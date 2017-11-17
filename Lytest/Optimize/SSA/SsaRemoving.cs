using System.Collections.Generic;
using System.Linq;
using LYtest.CFG;
using LYtest.LinearRepr;
using LYtest.LinearRepr.Values;

namespace LYtest.Optimize.SSA
{
    public class SsaRemoving
    {
        private CFGraph ssaGraph;
        private HashSet<IThreeAddressCode> setTAC;
        private Dictionary<IdentificatorValue, Stack<int>> varsDict;
        private Dictionary<IdentificatorValue, int> varsCounter;
        private List<CFGNode> visitedNodes = new List<CFGNode>();

        public SsaRemoving(CFGraph ssa)
        {
            ssaGraph = ssa;
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
            varsDict = new Dictionary<IdentificatorValue, Stack<int>>();
            varsCounter = new Dictionary<IdentificatorValue, int>();
            var allVariables = GetAllVariables(ssaGraph);
            foreach (var v in allVariables)
            {
                var stack = new Stack<int>();
                stack.Push(0);
                varsDict.Add(v, stack);
                varsCounter.Add(v, 0);
            }
        }

        private HashSet<IdentificatorValue> GetAllVariables(CFGraph inputGraph)
        {
            HashSet<IdentificatorValue> variables = new HashSet<IdentificatorValue>();
            foreach (var block in inputGraph.Blocks)
                foreach (var line in block.Enumerate())
                    if (LinearHelper.AsDefinition(line) != null && 
                        !AdditionalMethods.IsPhiId(line.LeftOperand.Value as IdentificatorValue))
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

        public CFGraph RemoveSSA()
        {
            SsaBuilding.RenamingAllVars(ssaGraph.GetRoot(), visitedNodes, varsDict, varsCounter, false);
            return ssaGraph;
        }

    }
}