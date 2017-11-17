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

1. Cfg-граф
2. SSA-граф

#### Выходные данные

1. SSA-граф
2. Cfg-граф

_1_ — построение SSA-формы, _2_ — восстановление из SSA

### Описание реализации

#### Построение SSA-формы

Если инструкции базовых блоков _B<SUB>1</SUB>,...,B<SUB>n</SUB>_ выполняются строго последовательно, то такие блоки можно рассматривать как один большой базовый блок _B_ и применять к нему описанное выше преобразование. Если же есть базовый блок, у которого более одного предка, то становится непонятно, какое поколение переменной необходимо использовать. Чтобы решить проблему, вводится специальная нотация _ϕ_-функций (функций слияния). Необходимо расставить _ϕ_-функции там, где несколько потоков управления сливаются в один. Точнее, пусть у базового блока _B<SUB>i</SUB>_ есть k непосредственных предшественников. Тогда _ϕ_-функция, которая будет размещена в самом начале блока _B<SUB>i</SUB>_, будет иметь _k_ аргументов, причем _m_-ый аргумент будет соответствовать значению переменной, пришедшему по ветви из _m_-того предшественника.

Представление _ϕ_-функций в трехадресном коде выполнено следующим образом:
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

```


