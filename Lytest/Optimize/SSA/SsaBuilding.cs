using System.Collections.Generic;
using System.Linq;
using LYtest.CFG;
using LYtest.LinearRepr;
using LYtest.LinearRepr.Values;

namespace LYtest.Optimize.SSA
{
    public class SsaBuilding
    {
        public CFGraph SSAForm => ssaForm;
        CFGraph ssaForm;
        private CFGraph cfGraph;
        private int counterPhi = 0;
        private Dictionary<IdentificatorValue, Stack<int>> varsDict;
        private Dictionary<IdentificatorValue, int> varsCounter;
        private HashSet<IdentificatorValue> vars;
        private List<CFGNode> visitedNodes = new List<CFGNode>();

        public SsaBuilding(CFGraph inputGraph)
        {
            vars = GetAllVars(inputGraph);
            var insertPhiGraph = InsertPhi(inputGraph);
            ssaForm = RenamingVars(insertPhiGraph);
        }
 
        private HashSet<IdentificatorValue> GetAllVars(CFGraph inputGraph)
        {
            HashSet<IdentificatorValue> variables = new HashSet<IdentificatorValue>();
            foreach (var block in inputGraph.Blocks)
                foreach (var line in block.Enumerate())
                    if (LinearHelper.AsDefinition(line) != null &&
                        !AdditionalMethods.IsPhiId(line.LeftOperand.Value as IdentificatorValue))
                        variables.Add(line.Destination as IdentificatorValue);
            return variables;
        }

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
                            var phiFunc = new LinearRepresentation(Operation.Phi, phiLabel as StringValue
                                , variable, parentNode.Value.Enumerate().Last().Label);
                            node.Value.InsertAfter(newAssign, phiFunc);
                        }
                        counterPhi++;
                    }
            return ssaGraph;
        }

        public static void RenamingAllVars(CFGNode currentNode, List<CFGNode> visitedNodes,
            Dictionary<IdentificatorValue, Stack<int>> varsDictionary, Dictionary<IdentificatorValue, int> varsCounter, bool intoSSA)
        {
            if (visitedNodes.Contains(currentNode)) return;
            foreach (var str in currentNode.Value.Enumerate())
            {
                if (AdditionalMethods.AssignPhi(str))
                {
                    IdentificatorValue curVar = str.Destination as IdentificatorValue;
                    AdditionalMethods.SetNewName(varsDictionary, varsCounter, curVar, intoSSA);
                    int varCounter = varsDictionary[curVar].Peek();
                    string renamed = AdditionalMethods.Rename(str.Destination.Value, varCounter.ToString(), intoSSA);
                    str.Destination = new IdentificatorValue(renamed);
                }
                if (!AdditionalMethods.IsPhiId(str.LeftOperand as IdentificatorValue) && str.Operation != Operation.Phi)
                {
                    if (str.RightOperand is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.RightOperand as IdentificatorValue;
                        int varCounter = varsDictionary[curVar].Peek();
                        string renamed = AdditionalMethods.Rename(str.RightOperand.Value.ToString(), varCounter.ToString(), intoSSA);
                        str.RightOperand = new IdentificatorValue(renamed);
                    }
                    if (str.LeftOperand is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.LeftOperand as IdentificatorValue;
                        int varCounter = varsDictionary[curVar].Peek();
                        string renamed = AdditionalMethods.Rename(str.LeftOperand.Value.ToString(), varCounter.ToString(), intoSSA);
                        str.LeftOperand = new IdentificatorValue(renamed);
                    }
                    if (str.Destination is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.Destination as IdentificatorValue;
                        AdditionalMethods.SetNewName(varsDictionary, varsCounter, curVar, intoSSA);
                        int varCounter = varsDictionary[curVar].Peek();
                        string renamed = AdditionalMethods.Rename(str.Destination.Value, varCounter.ToString(), intoSSA);
                        str.Destination = new IdentificatorValue(renamed);
                    }
                }
            }
            var children = new List<CFGNode>() { currentNode.directChild, currentNode.gotoNode };
            foreach (var child in children)
            {
                if (child == null)
                    continue;
                foreach (var s in child.Value.Enumerate())
                    if (AdditionalMethods.AssignPhi(s))
                    {
                        foreach (var line in child.Value.Enumerate()
                            .Select(str => str).Where(str => str.Operation == Operation.Phi && str.Destination == s.LeftOperand))
                        {
                            if (line.RightOperand == currentNode.Value.Enumerate().Last().Label)
                            {
                                IdentificatorValue curVar = line.LeftOperand as IdentificatorValue;
                                int varCounter = varsDictionary[curVar].Peek();
                                string renamed = AdditionalMethods.Rename(line.LeftOperand.Value.ToString(), varCounter.ToString(), intoSSA);
                                line.LeftOperand = new IdentificatorValue(renamed);
                            }
                        }
                    }
            }
            if (!visitedNodes.Contains(currentNode))
                visitedNodes.Add(currentNode);
            foreach (var child in children)
                if (child != null) RenamingAllVars(child, visitedNodes, varsDictionary, varsCounter, intoSSA);
            foreach (var str in currentNode.Value.Enumerate())
                if (str.LeftOperand is IdentificatorValue)
                {
                    IdentificatorValue curVar = str.LeftOperand as IdentificatorValue;
                    if (varsDictionary.Keys.Contains(curVar))
                        varsDictionary[curVar].Pop();
                }
        }

        private CFGraph RenamingVars(CFGraph inputGraph)
        {
            cfGraph = inputGraph;
            varsDict = new Dictionary<IdentificatorValue, Stack<int>>();
            varsCounter = new Dictionary<IdentificatorValue, int>();
            var allVars = GetAllVars(cfGraph);
            foreach (var v in allVars)
            {
                var stack = new Stack<int>();
                stack.Push(0);
                varsDict.Add(v, stack);
                varsCounter.Add(v, 0);
            }
            RenamingAllVars(cfGraph.GetRoot(), visitedNodes, varsDict, varsCounter, true);
            return cfGraph;
        }
    }

    public class AdditionalMethods
    {
        public static bool AssignPhi(IThreeAddressCode line)
        {
            return IsPhiId(line.LeftOperand as IdentificatorValue) && line.Operation == Operation.Assign;
        }

        public static bool IsPhiId(IdentificatorValue idCheck)
        {
            return idCheck != null && idCheck.Value.Count() >= 3 && idCheck.Value.Substring(0, 3) == "phi";
        }

        public static void SetNewName(Dictionary<IdentificatorValue, Stack<int>> dict1,
    Dictionary<IdentificatorValue, int> dict2, IdentificatorValue v, bool intoSsa)
        {
            if (dict1[v] == null) dict1[v] = new Stack<int>();
            var i = dict2[v];
            dict1[v].Push(i);
            dict2[v] = intoSsa ? i + 1 : i - 1;
        }

        public static string Rename(string s1, string s2, bool intoSsa)
        {
            return intoSsa ? s1 + s2 : s1.Remove(s1.Length - s2.Length, s2.Length);
        }
    } 
}
