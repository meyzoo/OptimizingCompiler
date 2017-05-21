﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using LYtest.BaseBlocks;
using QuickGraph;
using QuickGraph.Graphviz;

namespace LYtest.CFG
{
    public class DepthSpanningTree
    {
        // Verteces numeration
        public Dictionary<CFGNode, int> Numbers { get; }

        // Tree
        public BidirectionalGraph<CFGNode, Edge<CFGNode>> Tree { get; }

        // visited verteces array
        private HashSet<CFGNode> visited = null;

        // Constructor from CFGraph
        public DepthSpanningTree(CFGraph cfg)
        {
            visited = new HashSet<CFGNode>();
            Tree = new BidirectionalGraph<CFGNode, Edge<CFGNode>>();
            Numbers = new Dictionary<CFGNode, int>();

            var root = cfg.GetRoot();
            int start = 0;
            BuildTree(root, ref start);
        }

        // Build tree
        private void BuildTree(CFGNode node, ref int currentNumber)
        {
            if (node == null)
                return;
            visited.Add(node);
            Numbers[node] = currentNumber;

            if (node.directChild == null && node.gotoNode == null)
            {
                return;
            }

            var children = new List<CFGNode>();
            if (node.directChild != null)
            {
                children.Add(node.directChild);
            }
            if (node.gotoNode != null)
            {
                children.Add(node.gotoNode);
            }


            if (!Tree.Vertices.Contains(node))
                Tree.AddVertex(node);
            foreach (var child in children)
            {
                if (!visited.Contains(child))
                {
                    if (!Tree.Vertices.Contains(child))
                        Tree.AddVertex(child);
                    Tree.AddEdge(new Edge<CFGNode>(node, child));

                    currentNumber += 1;
                    //Console.WriteLine(currentNumber);
                    BuildTree(child, ref currentNumber);
                }
            }
        }

        // Finds back path from source to target, true if it is.
        public bool FindBackwardPath(CFGNode source, CFGNode target)
        {
            var result = false;
            List<Edge<CFGNode>> incomingEdges = new List<Edge<CFGNode>>();
            try
            {
                incomingEdges = Tree.InEdges(source).ToList();
            }
            catch (KeyNotFoundException exc)
            {
                Console.WriteLine(exc.ToString());
            }

            while (incomingEdges.Count() > 0)
            {
                var edge = incomingEdges.First();
                if (edge.Source.Equals(target))
                {
                    result = true;
                    break;
                }
                else
                {
                    incomingEdges = Tree.InEdges(edge.Source).ToList();
                }
            }

            return result;
        }

        public override string ToString()
        {
            var graphviz = new GraphvizAlgorithm<CFGNode, Edge<CFGNode>>(Tree);
            return graphviz.Generate();
        }
    }
}
