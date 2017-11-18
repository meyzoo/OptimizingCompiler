## Восстановление кода из SSA-формы

### Постановка задачи

#### Теоретическая сводка

Если некоторая переменная имеет N использований и M определений, для представления du- и ud- цепочек понадобится порядка M×N элементов.
Для того, чтобы уменьшить расходы на представление цепочек, можно использовать **SSA (Static Single Assignment form)** — _промежуточное представление, используемое компиляторами, в котором каждой переменной значение присваивается лишь единожды._
Помимо уменьшения затрат на представление цепочек, эта форма имеет и другие преимущества:

• Алгоритмы оптимизации могут быть проще в случае, если переменная имеет только одно определение.

• Для большинства практических программ количество _ϕ_-функций (речь о которых пойдет ниже) растет линейно в зависимости от исходной
программы.

• Несвязанные использования одной переменной (такой, как, например, счетчик двух независимых циклов) получат разные имена в SSA-форме.
Для того, чтобы понять, как выглядит программа в представлении SSA, рассмотрим один базовый блок _B<SUB>i</SUB>_. Пусть блок _B<SUB>i</SUB>_ содержит инструкции, приведенные в левом столбце:

<img src="https://pp.userapi.com/c834100/v834100400/249f2/KmhkAVFX30o.jpg" alt="">

В правом столбце приведено соответствующее им SSA-представление. Рассмотренный пример показывает, что каждое новое присваивание значения переменной на самом деле присваивает значение очередному **поколению** (_generation_). Поколения одной и той же переменной рассматриваются как независимые друг от друга переменные. Описанное преобразование, проведенное в пределах одного базового блока, называют **нумерацией** значений (_value numbering_).

#### Входные данные

1. Cfg
2. SSA-граф

#### Выходные данные

1. SSA-граф
2. Cfg

_1_ — построение SSA-формы, _2_ — восстановление из SSA

### Описание реализации

#### Построение SSA-формы

Если инструкции базовых блоков _B<SUB>1</SUB>,...,B<SUB>n</SUB>_ выполняются строго последовательно, то такие блоки можно рассматривать как один большой базовый блок _B_ и применять к нему описанное выше преобразование. Если же есть базовый блок, у которого более одного предка, то становится непонятно, какое поколение переменной необходимо использовать. Чтобы решить проблему, вводится специальная нотация _ϕ_-функций (функций слияния). Необходимо расставить _ϕ_-функции там, где несколько потоков управления сливаются в один. Точнее, пусть у базового блока _B<SUB>i</SUB>_ есть k непосредственных предшественников. Тогда _ϕ_-функция, которая будет размещена в самом начале блока _B<SUB>i</SUB>_, будет иметь _k_ аргументов, причем _m_-ый аргумент будет соответствовать значению переменной, пришедшему по ветви из _m_-того предшественника.

Представление _ϕ_-функций в [трехадресном коде](https://github.com/meyzoo/OptimizingCompiler/blob/my-fork/docs/src/03-three-address-code.md) выполнено следующим образом:
```c sharp
 case Operation.Phi:
       body = $"{Destination} = {LeftOperand} IF WENT FROM: {RightOperand}";
       break;
```
В начале базового блока соответствующая _ϕ_-функция присваивается новой переменной.

Перед вставкой _ϕ_-функций необходимо создать коллекцию уникальных переменных входного графа потока управления:
```c sharp 
private HashSet<IdentificatorValue> GetAllVars(CFGraph inputGraph)
{
    HashSet<IdentificatorValue> variables = new HashSet<IdentificatorValue>();
    foreach (var block in inputGraph.Blocks)
        foreach (var line in block.Enumerate())
            if (LinearHelper.AsDefinition(line) != null && !AdditionalMethods.IsPhiId(line.LeftOperand.Value as IdentificatorValue))
               variables.Add(line.Destination as IdentificatorValue);
    return variables;
} 
``` 

Вставка _ϕ_-функций:
```c sharp
private CFGraph InsertPhi(CFGraph inputGraph)
{
 CFGraph ssaGraph = inputGraph;
 foreach (var variable in vars)
  foreach (var node in inputGraph.graph.Vertices)
   if (node.ParentsNodes.Count >= 2)
   {
      IValue phiLabel = new IdentificatorValue("phi" + counterPhi);
      var newAssign = new LinearRepresentation(Operation.Assign, variable, phiLabel, null);
      node.Value.NewAppend(newAssign);
      foreach (var parentNode in node.ParentsNodes)
      {
          IValue phiLabel = new IdentificatorValue("phi" + counterPhi);
          var newAssign = new LinearRepresentation(Operation.Assign, variable, phiLabel, null);
          node.Value.InsertAfter(newAssign, phiFunc);
      }
      counterPhi++;
   }
  return ssaGraph;
}
```

После того, как _ϕ_-функции вставлены, нужно переименовать различные определения каждой переменной _a_ в _a<SUB>1</SUB>,...,a<SUB>m</SUB>_. Необходимо переименовывать каждое использование переменной _a_, чтобы использовать ближайшее определение _d_ переменной _a_, которое находится над _a_ в [дереве доминирования](25-DominanceFrontier.md) графа потока управления. Индексы, необходимые для переименования, накапливаются в стеках.

<img src="https://pp.userapi.com/c639127/v639127394/5bf0b/pzIC8lqMimE.jpg" alt="">

#### Восстановление из SSA-формы

Преобразование SSA-формы обратно в трехадресный код является элементарным и выполняется [при доказательстве корректности алгоритма](http://ssabook.gforge.inria.fr/latest/book.pdf). Для обратного перевода необходимо выполнить устранение мертвого кода – удалить все _ϕ_-функции и декрементировать счетчики-стеки для каждой переменной, участвующей в преобразовании. 

Для избавления от _ϕ_-функций необходимо удалить всю цепочку присваиваний:

```c sharp
setTAC = new HashSet<IThreeAddressCode>();
foreach (var block in ssaGraph.Blocks)
{
       foreach (var instr in block.Enumerate())
           if (AdditionalMethods.AssignPhi(instr))
               setTAC.Add(instr);
       var phiInstrs = block.Enumerate().Select(x => x).Where(instr => instr.Operation == Operation.Phi);
       for (int i = phiInstrs.Count() - 1; i >= 0; --i)
           block.Remove(phiInstrs.ElementAt(i));
       for (int i = setTAC.Count() - 1; i >= 0; --i)
           block.Remove(setTAC.ElementAt(i));
}
```

Процесс обнуления счетчика для каждой переменной итеративен: 

<img src="https://pp.userapi.com/c834204/v834204814/29656/CHkdSmZANCk.jpg" alt="">   

Обратное переименование переменных использует работу со строками, полученными из значений операндов.

### Тест

```c sharp
[TestMethod]
public void SsaRemovingTest()
{
    var root = Parser.ParseString(Samples.SampleProgramText.ssaSample);
    var code = ProgramTreeToLinear.Build(root);
    var blocks = LinearToBaseBlock.Build(code);
    // Построение CFG-графа из блоков
    var ctrlFlowGraph = new CFGraph(blocks);
    Console.WriteLine("------------ Граф потока управления: ------------");
    Console.WriteLine(ctrlFlowGraph.ToString());
    // Построение SSA-формы по CFG-графу
    SsaBuilding ssa = new SsaBuilding(ctrlFlowGraph);
    CFGraph ssaGraph = ssa.SSAForm;
    Console.WriteLine("------------ SSA-форма для графа: ------------");
    Console.WriteLine(ssaGraph.ToString());
    // Восстановление из SSA-формы
    SsaRemoving ssaRmv = new SsaRemoving(ssaGraph);
    Console.WriteLine("------------ Восстановление из SSA-формы: ------------");
    Console.WriteLine(ssaRmv.RemoveSSA());
}
```

Пример входных данных:

```c sharp
public static readonly string ssaSample = "x = 10;" +
                                          "y = 34;" +
                                          "y = y;" +
                                          "x = x + 1;" +
                                          "if 13 {" +
                                          "y = x / 4;" +
                                          "u = y; }" +
                                          "else {" +
                                          "y = x + 5;" +
                                          "u = x - y; }" +
                                          "v = u;";
```

Результаты:
```
------------ Граф потока управления: ------------
digraph G {
0 [label="
%ulabel391: x := 10
%ulabel392: y := 34
%ulabel393: y := y
%ulabel394: x := x + 1
%ulabel395: IF 13 THEN GOTO %label0
"];
1 [label="
%ulabel396: y := x + 5
%ulabel397: u := x - y
%ulabel398: GOTO %label1
"];
2 [label="
%label0: NOP
%ulabel399: y := x / 4
%ulabel400: u := y
"];
3 [label="
%label1: NOP
%ulabel401: v := u
"];
0 -> 1 [];
0 -> 2 [];
1 -> 3 [];
2 -> 3 [];
}
------------ SSA-форма для графа: ------------
digraph G {
0 [label="
%ulabel391: x0 := 10
%ulabel392: y0 := 34
%ulabel393: y1 := y0
%ulabel394: x1 := x0 + 1
%ulabel395: IF 13 THEN GOTO %label0
"];
1 [label="
%ulabel396: y2 := x1 + 5
%ulabel397: u0 := x1 - y2
%ulabel398: GOTO %label1
"];
2 [label="
%label0: NOP
%ulabel399: y4 := x1 / 4
%ulabel400: u2 := y4
"];
3 [label="
%ulabel411: v0 := phi3
%ulabel413: phi3 = v0 IF WENT FROM: %ulabel400
%ulabel412: phi3 = v0 IF WENT FROM: %ulabel398
%ulabel408: u1 := phi2
%ulabel410: phi2 = u2 IF WENT FROM: %ulabel400
%ulabel409: phi2 = u0 IF WENT FROM: %ulabel398
%ulabel405: y3 := phi1
%ulabel407: phi1 = y4 IF WENT FROM: %ulabel400
%ulabel406: phi1 = y2 IF WENT FROM: %ulabel398
%ulabel402: x2 := phi0
%ulabel404: phi0 = x1 IF WENT FROM: %ulabel400
%ulabel403: phi0 = x1 IF WENT FROM: %ulabel398
%label1: NOP
%ulabel401: v1 := u1
"];
0 -> 1 [];
0 -> 2 [];
1 -> 3 [];
2 -> 3 [];
}
------------ Восстановление из SSA-формы: ------------
digraph G {
0 [label="
%ulabel391: x := 10
%ulabel392: y := 34
%ulabel393: y := y
%ulabel394: x := x + 1
%ulabel395: IF 13 THEN GOTO %label0
"];
1 [label="
%ulabel396: y := x + 5
%ulabel397: u := x - y
%ulabel398: GOTO %label1
"];
2 [label="
%label0: NOP
%ulabel399: y := x / 4
%ulabel400: u := y
"];
3 [label="
%label1: NOP
%ulabel401: v := u
"];
0 -> 1 [];
0 -> 2 [];
1 -> 3 [];
2 -> 3 [];
}
```
