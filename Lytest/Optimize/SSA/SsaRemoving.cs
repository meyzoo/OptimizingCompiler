using System.Collections.Generic;
using System.Linq;
using LYtest.CFG;
using LYtest.LinearRepr;
using LYtest.LinearRepr.Values;

namespace LYtest.Optimize.SSA
{
    public class SsaRemoving
    {
        private CFGraph cfGraph;
        private HashSet<IThreeAddressCode> setTAC;
        private Dictionary<IdentificatorValue, Stack<int>> varsDict;
        private Dictionary<IdentificatorValue, int> counters;
        private List<CFGNode> visitedNodes = new List<CFGNode>();

        public SsaRemoving(CFGraph cfg)
        {
            cfGraph = cfg;
            setTAC = new HashSet<IThreeAddressCode>();
            foreach (var block in cfGraph.Blocks)
            {
                foreach (var instr in block.Enumerate())
                    if (AssignPhi(instr))
                        setTAC.Add(instr);
                var phiInstrs = block.Enumerate().Select(x => x).Where(instr => instr.Operation == Operation.Phi);
                for (int i = phiInstrs.Count() - 1; i >= 0; --i)
                    block.Remove(phiInstrs.ElementAt(i));
                for (int i = setTAC.Count() - 1; i >= 0; --i)
                    block.Remove(setTAC.ElementAt(i));
            }
            varsDict = new Dictionary<IdentificatorValue, Stack<int>>();
            counters = new Dictionary<IdentificatorValue, int>();
            var allVariables = GetAllVariables(cfGraph);
            foreach (var v in allVariables)
            {
                var stack = new Stack<int>();
                stack.Push(0);
                varsDict.Add(v, stack);
                counters.Add(v, 0);
            }
        }

        private void SetNewName(IdentificatorValue v)
        {
            if (varsDict[v] == null) varsDict[v] = new Stack<int>();
            var i = counters[v];
            varsDict[v].Push(i);
            counters[v] = i + 1;
        }

        private HashSet<IdentificatorValue> GetAllVariables(CFGraph inputGraph)
        {
            HashSet<IdentificatorValue> variables = new HashSet<IdentificatorValue>();
            foreach (var block in inputGraph.Blocks)
                foreach (var line in block.Enumerate())
                    if (LinearHelper.AsDefinition(line) != null && !IsPhiId(line.LeftOperand.Value as IdentificatorValue))
                    {
                        if (line.LeftOperand is IdentificatorValue)
                            variables.Add(line.LeftOperand as IdentificatorValue);
                        if (line.RightOperand is IdentificatorValue)
                            variables.Add(line.RightOperand as IdentificatorValue);
                        if (line.Destination is IdentificatorValue)
                            variables.Add(line.Destination as IdentificatorValue);
                    }
            return variables;
        }

        private void RenameVarsBack(CFGNode currentNode)
        {
            if (visitedNodes.Contains(currentNode))
                return;
            foreach (var str in currentNode.Value.Enumerate())
            {
                if (AssignPhi(str))
                {
                    IdentificatorValue curVar = str.Destination as IdentificatorValue;
                    SetNewName(curVar);
                    int varCounter = varsDict[curVar].Peek();
                    str.Destination = new IdentificatorValue
                        (str.Destination.Value.Remove(str.Destination.Value.Length - varCounter.ToString().Length, varCounter.ToString().Length));
                }
                if (!IsPhiId(str.LeftOperand as IdentificatorValue) && str.Operation != Operation.Phi)
                {
                    if (str.RightOperand is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.RightOperand as IdentificatorValue;
                        int varCounter = varsDict[curVar].Peek();
                        str.RightOperand = new IdentificatorValue(str.RightOperand.Value.ToString().Remove
                            (str.RightOperand.Value.ToString().Length - varCounter.ToString().Length, varCounter.ToString().Length));
                    }
                    if (str.LeftOperand is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.LeftOperand as IdentificatorValue;
                        int varCounter = varsDict[curVar].Peek();
                        str.LeftOperand = new IdentificatorValue(str.LeftOperand.Value.ToString().Remove
                            (str.LeftOperand.Value.ToString().Length - varCounter.ToString().Length, varCounter.ToString().Length));
                    }
                    if (str.Destination is IdentificatorValue)
                    {
                        IdentificatorValue curVar = str.Destination as IdentificatorValue;
                        SetNewName(curVar);
                        int varCounter = varsDict[curVar].Peek();
                        str.Destination = new IdentificatorValue
                            (str.Destination.Value.Remove(str.Destination.Value.Length - varCounter.ToString().Length, varCounter.ToString().Length));
                    }
                }
            }
            var children = new List<CFGNode>() { currentNode.directChild, currentNode.gotoNode };
            foreach (var child in children)
            {
                if (child == null)
                    continue;
                foreach (var s in child.Value.Enumerate())
                    if (AssignPhi(s))
                    {
                        foreach (var line in child.Value.Enumerate()
                            .Select(str => str).Where(str => str.Operation == Operation.Phi && str.Destination == s.LeftOperand))
                        {
                            if (line.RightOperand == currentNode.Value.Enumerate().Last().Label)
                            {
                                IdentificatorValue curVar = line.LeftOperand as IdentificatorValue;
                                int varCounter = varsDict[curVar].Peek();
                                line.LeftOperand = new IdentificatorValue(line.LeftOperand.Value.ToString().Remove
                                    (line.LeftOperand.Value.ToString().Length - varCounter.ToString().Length, varCounter.ToString().Length));
                            }
                        }
                    }
            }
            if (!visitedNodes.Contains(currentNode))
                visitedNodes.Add(currentNode);
            foreach (var child in children)
                if (child != null)
                    RenameVarsBack(child);
            foreach (var str in currentNode.Value.Enumerate())
                if (str.LeftOperand is IdentificatorValue)
                {
                    IdentificatorValue curVar = str.LeftOperand as IdentificatorValue;
                    if (varsDict.Keys.Contains(curVar)) varsDict[curVar].Pop();
                }
        }

        public CFGraph RemoveSSA()
        {
            RenameVarsBack(cfGraph.GetRoot());
            return cfGraph;
        }

        public static bool AssignPhi(IThreeAddressCode line)
        {
            return IsPhiId(line.LeftOperand as IdentificatorValue) && line.Operation == Operation.Assign;
        }

        public static bool IsPhiId(IdentificatorValue idCheck)
        {
            return idCheck != null && idCheck.Value.Count() >= 3  && idCheck.Value.Substring(0, 3) == "phi";
        }
    }
}