﻿using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using ProgramTree;
using LYtest.Visitors;
using LYtest.BaseBlocks;
using LYtest.CFG;
using QuickGraph;

namespace LYtest
{
    class Program
    {
        static void Main(string[] args)
        {
            string inp = "i= m -1;" +
                        "j = n;" +
                        "a = u1;" +

                        "while 1 {" +
                        " i = i +1;" +
                        "j = j -1;" +

                        "if 5 { a = u2; }" +
                        "i = u3;" +
                        "}";
//            var root = Parser.ParseString(inp);

            var text = File.ReadAllText("a.txt");
            var root = Parser.ParseString(text);

            if (root == null)
            {
                Console.WriteLine("Error");
                return;
            }

            // Генерация и получение трёхзначного кода
            var linearCode = new LinearCodeVisitor();
            root.AcceptVisit(linearCode);
            var code = linearCode.code;

            
            // Get blocks and print it
            var blocks = LinearToBaseBlock.Build(code);
            foreach (var block in blocks)
            {
                Console.WriteLine(block.ToString());
            }

            // Get graph and made DepthSpanningTree
            var cfg = new CFGraph(blocks);

            var dst = new DepthSpanningTree(cfg);
            string dst_viz = dst.ToString();
            Console.WriteLine(dst_viz);

            Console.WriteLine("");

            Console.WriteLine(cfg.EdgeTypes.ToString());


            var f = cfg.allRetreatingEdgesAreBackwards();
            var r = cfg.getNaturalCyclesForBackwardEdges();
            Console.ReadLine();
        }

    }
}
