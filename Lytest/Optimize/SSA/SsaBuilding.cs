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
        private Dictionary<IdentificatorValue, Stack<int>> varsDictionary;
        private Dictionary<IdentificatorValue, int> varsCounter;
        private HashSet<IdentificatorValue> vars;
        private List<CFGNode> visitedNodes = new List<CFGNode>();

        public SsaBuilding(CFGraph inputGraph)
        {
            vars = GetAllVars(inputGraph);
            var insertPhiGraph = InsertPhiFuncs(inputGraph);
            ssaForm = RenamingVars(insertPhiGraph);
        }

        private HashSet<IdentificatorValue> GetAllVars(CFGraph inputGraph)
        {
            HashSet<IdentificatorValue> variables = new HashSet<IdentificatorValue>();
            foreach (var block in inputGraph.Blocks)
            {
                foreach (var line in block.Enumerate())
                {
                    if (LinearHelper.AsDefinition(line) != null &&
                !SsaRemoving.IsPhiId(line.LeftOperand.Value as IdentificatorValue))
                        variables.Add(line.Destination as IdentificatorValue);
                }
            }
            return variables;
        }

        private CFGraph InsertPhiFuncs(CFGraph inputGraph)
        {
            CFGraph ssaGraph = inputGraph;
            foreach (var variable in vars)
            {
                foreach (var node in inputGraph.graph.Vertices)
                {
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
                }
            }
            return ssaGraph;
        }

        private void SetNewName(IdentificatorValue v)
        {
            if (varsDictionary[v] == null) varsDictionary[v] = new Stack<int>();
            var i = varsCounter[v];
            varsDictionary[v].Push(i);
            varsCounter[v] = i + 1;
        }

        private void RenamingAllVars(CFGNode currentNode)
        {
            if (visitedNodes.Contains(currentNode))
                return;
            foreach (var str in currentNode.Value.Enumerate())
            {
                if (SsaRemoving.AssignPhi(str))
                {
                    IdentificatorValue curVar = str.Destination as IdentificatorValue;
                    SetNewName(curVar);
                    int varCounter = varsDictionary[curVar].Peek();
                    str.Destination = new IdentificatorValue(str.Destination.Value + varCounter.ToString());
                }
                if (!SsaRemoving.IsPhiId(str.LeftOperand as IdentificatorValue) && str.Operation != Operation.Phi)
                {
                    if (str.RightOperand is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.RightOperand as IdentificatorValue;
                        int varCounter = varsDictionary[curVar].Peek();
                        str.RightOperand = new IdentificatorValue(str.RightOperand.Value + varCounter.ToString());
                    }
                    if (str.LeftOperand is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.LeftOperand as IdentificatorValue;
                        int varCounter = varsDictionary[curVar].Peek();
                        str.LeftOperand = new IdentificatorValue(str.LeftOperand.Value + varCounter.ToString());
                    }
                    if (str.Destination is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.Destination as IdentificatorValue;
                        SetNewName(curVar);
                        int varCounter = varsDictionary[curVar].Peek();
                        str.Destination = new IdentificatorValue(str.Destination.Value + varCounter.ToString());
                    }
                }
            }
            var children = new List<CFGNode>() { currentNode.directChild, currentNode.gotoNode };
            foreach (var child in children)
            {
                if (child == null)
                    continue;
                foreach (var s in child.Value.Enumerate())
                    if (SsaRemoving.AssignPhi(s))
                    {
                        foreach (var line in child.Value.Enumerate()
                            .Select(str => str).Where(str => str.Operation == Operation.Phi && str.Destination == s.LeftOperand))
                        {
                            if (line.RightOperand == currentNode.Value.Enumerate().Last().Label)
                            {
                                IdentificatorValue curVar = line.LeftOperand as IdentificatorValue;
                                int varCounter = varsDictionary[curVar].Peek();
                                line.LeftOperand = new IdentificatorValue(line.LeftOperand.Value + varCounter.ToString());
                            }
                        }
                    }
            }
            if (!visitedNodes.Contains(currentNode))
                visitedNodes.Add(currentNode);
            foreach (var child in children)
                if (child != null) RenamingAllVars(child);
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
            varsDictionary = new Dictionary<IdentificatorValue, Stack<int>>();
            varsCounter = new Dictionary<IdentificatorValue, int>();
            var allVars = GetAllVars(cfGraph);
            foreach (var v in allVars)
            {
                var stack = new Stack<int>();
                stack.Push(0);
                varsDictionary.Add(v, stack);
                varsCounter.Add(v, 0);
            }
            RenamingAllVars(cfGraph.GetRoot());
            return cfGraph;
        }

    }
}
