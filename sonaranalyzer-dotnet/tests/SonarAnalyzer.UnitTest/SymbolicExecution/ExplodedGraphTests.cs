/*
* SonarAnalyzer for .NET
* Copyright (C) 2015-2019 SonarSource SA
* mailto: contact AT sonarsource DOT com
*
* This program is free software; you can redistribute it and/or
* modify it under the terms of the GNU Lesser General Public
* License as published by the Free Software Foundation; either
* version 3 of the License, or (at your option) any later version.
*
* This program is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
* Lesser General Public License for more details.
*
* You should have received a copy of the GNU Lesser General Public License
* along with this program; if not, write to the Free Software Foundation,
* Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
*/

extern alias csharp;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using csharp::SonarAnalyzer.LiveVariableAnalysis.CSharp;
using FluentAssertions;
using FluentAssertions.Execution;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using SonarAnalyzer.ControlFlowGraph;
using SonarAnalyzer.ControlFlowGraph.CSharp;
using SonarAnalyzer.LiveVariableAnalysis;
using SonarAnalyzer.SymbolicExecution;
using SonarAnalyzer.SymbolicExecution.Constraints;
using SonarAnalyzer.UnitTest.Helpers;

namespace SonarAnalyzer.UnitTest.SymbolicExecution
{
    [TestClass]
    public class ExplodedGraphTests
    {
        private const string TestInput = @"
namespace NS
{{
  public class Foo
  {{
    private bool Property {{ get; set; }}
    public void Main(bool inParameter, out bool outParameter)
    {{
      {0}
    }}
  }}
}}";

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_SequentialInput()
        {
            var testInput = "var a = true; var b = false; b = !b; a = (b);";
            var context = new ExplodedGraphContext(testInput);
            var varDeclarators = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>();
            var aSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "a"));
            var bSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "b"));
            var numberOfProcessedInstructions = 0;
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "a = true")
                    {
                        args.ProgramState.GetSymbolValue(aSymbol).Should().Be(SymbolicValue.True);
                    }
                    if (args.Instruction.ToString() == "b = false")
                    {
                        args.ProgramState.GetSymbolValue(bSymbol).Should().Be(SymbolicValue.False);
                    }
                    if (args.Instruction.ToString() == "b = !b")
                    {
                        args.ProgramState.GetSymbolValue(bSymbol).Should().NotBe(SymbolicValue.False);
                        args.ProgramState.GetSymbolValue(bSymbol).Should().NotBe(SymbolicValue.True);
                    }
                    if (args.Instruction.ToString() == "a = (b)")
                    {
                        args.ProgramState.GetSymbolValue(bSymbol)
                            .Should().Be(args.ProgramState.GetSymbolValue(aSymbol));
                    }
                };

            context.Walk();

            numberOfProcessedInstructions.Should().Be(9);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_SequentialInput_OutParameter()
        {
            var testInput = "outParameter = true;";
            var context = new ExplodedGraphContext(testInput);
            var parameters = context.MainMethod.DescendantNodes().OfType<ParameterSyntax>();
            var outParameterSymbol = context.SemanticModel.GetDeclaredSymbol(parameters.First(d => d.Identifier.ToString() == "outParameter"));
            var numberOfProcessedInstructions = 0;
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "outParameter = true")
                    {
                        args.ProgramState.GetSymbolValue(outParameterSymbol)
                            .Should().Be(SymbolicValue.True);
                    }
                };

            context.Walk();

            numberOfProcessedInstructions.Should().Be(2);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_SequentialInput_Max()
        {
            var inputBuilder = new StringBuilder();
            for (var i = 0; i < CSharpExplodedGraph.MaxStepCount / 2 + 1; i++)
            {
                inputBuilder.AppendLine($"var x{i} = true;");
            }
            var testInput = inputBuilder.ToString();
            var context = new ExplodedGraphContext(testInput);

            var numberOfExitBlockReached = 0;
            context.EG.ExitBlockReached += (sender, args) => { numberOfExitBlockReached++; };

            context.EG.Walk();  // Special case with manual checks

            context.ExplorationEnded.Should().Be(false);
            context.NumberOfExitBlockReached.Should().Be(0);
            context.MaxStepCountReached.Should().Be(true);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_SingleBranchVisited_If()
        {
            var testInput = "var a = false; bool b; if (a) { b = true; } else { b = false; } a = b;";
            var context = new ExplodedGraphContext(testInput);
            var varDeclarators = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>();
            var aSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "a"));
            var bSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "b"));
            var numberOfLastInstructionVisits = 0;
            var numberOfProcessedInstructions = 0;
            var numberOfExitBlockReached = 0;
            context.EG.ExitBlockReached += (sender, args) => { numberOfExitBlockReached++; };
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "a = false")
                    {
                        args.ProgramState.GetSymbolValue(aSymbol).Should().Be(SymbolicValue.False);
                    }
                    if (args.Instruction.ToString() == "b = true")
                    {
                        Execute.Assertion.FailWith("We should never get into this branch");
                    }
                    if (args.Instruction.ToString() == "b = false")
                    {
                        args.ProgramState.GetSymbolValue(bSymbol).Should().Be(SymbolicValue.False);
                        args.ProgramState.GetSymbolValue(aSymbol)
                            .Should().BeNull("a is dead, so there should be no associated value to it.");
                    }
                    if (args.Instruction.ToString() == "a = b")
                    {
                        numberOfLastInstructionVisits++;
                    }
                };

            context.Walk();

            numberOfProcessedInstructions.Should().Be(8);
            numberOfExitBlockReached.Should().Be(1);
            numberOfLastInstructionVisits.Should().Be(1);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_SingleBranchVisited_And()
        {
            var testInput = "var a = false; if (a && !a) { a = true; }";
            var context = new ExplodedGraphContext(testInput);
            var varDeclarators = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>();
            var aSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "a"));
            var numberOfProcessedInstructions = 0;
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "a = !true")
                    {
                        args.ProgramState.GetSymbolValue(aSymbol).Should().Be(SymbolicValue.False); // Roslyn is clever !true has const value.
                    }
                    if (args.Instruction.ToString() == "!a")
                    {
                        Execute.Assertion.FailWith("We should never get into this branch");
                    }
                };

            context.Walk(); // Only EG final status check
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_BothBranchesVisited()
        {
            var testInput = "var a = false; bool b; if (inParameter) { b = inParameter; } else { b = !inParameter; } a = b;";
            var context = new ExplodedGraphContext(testInput);
            var varDeclarators = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>();
            var aSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "a"));
            var bSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "b"));
            var parameters = context.MainMethod.DescendantNodes().OfType<ParameterSyntax>();
            var inParameterSymbol = context.SemanticModel.GetDeclaredSymbol(parameters.First(d => d.Identifier.ToString() == "inParameter"));
            var numberOfLastInstructionVisits = 0;
            var numberOfProcessedInstructions = 0;
            var visitedBlocks = new HashSet<Block>();
            var branchesVisited = 0;
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    visitedBlocks.Add(args.ProgramPoint.Block);

                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "a = false")
                    {
                        branchesVisited++;

                        args.ProgramState.GetSymbolValue(aSymbol).Should().Be(SymbolicValue.False); // Roslyn is clever !true has const value.
                    }
                    if (args.Instruction.ToString() == "b = inParameter")
                    {
                        branchesVisited++;

                        bSymbol.HasConstraint(BoolConstraint.True, args.ProgramState).Should().BeTrue();
                        inParameterSymbol.HasConstraint(BoolConstraint.True, args.ProgramState).Should().BeTrue();
                    }
                    if (args.Instruction.ToString() == "b = !inParameter")
                    {
                        branchesVisited++;

                        // b has value, but not true or false
                        args.ProgramState.GetSymbolValue(bSymbol).Should().NotBeNull();
                        bSymbol.HasConstraint(BoolConstraint.False, args.ProgramState).Should().BeFalse();
                        bSymbol.HasConstraint(BoolConstraint.True, args.ProgramState).Should().BeFalse();

                        inParameterSymbol.HasConstraint(BoolConstraint.False, args.ProgramState).Should().BeTrue();
                    }
                    if (args.Instruction.ToString() == "a = b")
                    {
                        branchesVisited++;

                        args.ProgramState.GetSymbolValue(inParameterSymbol).Should().BeNull(); // not out/ref parameter and LVA says dead
                        numberOfLastInstructionVisits++;
                    }
                };

            // Number of Exit blocks:
            // All variables are dead at the ExitBlock, so whenever we get there,
            // the ExplodedGraph nodes should be the same, and thus should be processed only once.
            context.Walk();

            branchesVisited.Should().Be(4 + 1);
            numberOfLastInstructionVisits.Should().Be(2);
            visitedBlocks.Should().HaveCount(context.CFG.Blocks.Count() - 1 /* Exit block*/);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_BothBranchesVisited_StateMerge()
        {
            var testInput = "var a = !true; bool b; if (inParameter) { b = false; } else { b = false; } a = b;";
            var context = new ExplodedGraphContext(testInput);
            var varDeclarators = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>();
            var aSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "a"));
            var numberOfLastInstructionVisits = 0;
            var numberOfProcessedInstructions = 0;
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "a = b")
                    {
                        args.ProgramState.GetSymbolValue(aSymbol).Should().Be(SymbolicValue.False);
                        numberOfLastInstructionVisits++;
                    }
                };

            context.Walk();

            numberOfLastInstructionVisits.Should().Be(1);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_BothBranchesVisited_NonCondition()
        {
            var testInput = "var str = this?.ToString();";
            var context = new ExplodedGraphContext(testInput);
            var visitedBlocks = new HashSet<Block>();
            var countConditionEvaluated = 0;
            context.EG.ConditionEvaluated += (sender, args) => { countConditionEvaluated++; };
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    visitedBlocks.Add(args.ProgramPoint.Block);
                };

            context.Walk();

            visitedBlocks.Should().HaveCount(context.CFG.Blocks.Count() - 1 /* Exit block */);
            countConditionEvaluated.Should().Be(0);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_AllBranchesVisited()
        {
            var testInput = "int i = 1; switch (i) { case 1: default: cw1(); break; case 2: cw2(); break; }";
            var context = new ExplodedGraphContext(testInput);
            var numberOfCw1InstructionVisits = 0;
            var numberOfCw2InstructionVisits = 0;
            var numberOfProcessedInstructions = 0;
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "cw1()")
                    {
                        numberOfCw1InstructionVisits++;
                    }
                    if (args.Instruction.ToString() == "cw2()")
                    {
                        numberOfCw2InstructionVisits++;
                    }
                };

            context.Walk();

            numberOfCw1InstructionVisits.Should().Be(2);
            numberOfCw2InstructionVisits.Should().Be(1);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_NonDecisionMakingAssignments()
        {
            var testInput = "var a = true; a |= false; var b = 42; b++; ++b;";
            var context = new ExplodedGraphContext(testInput);
            var varDeclarators = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>();
            var aSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "a"));
            var bSymbol = context.SemanticModel.GetDeclaredSymbol(varDeclarators.First(d => d.Identifier.ToString() == "b"));
            var numberOfProcessedInstructions = 0;
            var branchesVisited = 0;
            SymbolicValue sv = null;
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "a = true")
                    {
                        branchesVisited++;
                        args.ProgramState.GetSymbolValue(aSymbol).Should().Be(SymbolicValue.True);
                    }
                    if (args.Instruction.ToString() == "a |= false")
                    {
                        branchesVisited++;
                        args.ProgramState.GetSymbolValue(aSymbol).Should().NotBeNull();
                        args.ProgramState.GetSymbolValue(aSymbol).Should().NotBe(SymbolicValue.False);
                        args.ProgramState.GetSymbolValue(aSymbol).Should().NotBe(SymbolicValue.True);
                    }
                    if (args.Instruction.ToString() == "b = 42")
                    {
                        branchesVisited++;
                        sv = args.ProgramState.GetSymbolValue(bSymbol);
                        sv.Should().NotBeNull();
                    }
                    if (args.Instruction.ToString() == "b++")
                    {
                        branchesVisited++;
                        var svNew = args.ProgramState.GetSymbolValue(bSymbol);
                        svNew.Should().NotBeNull();
                        svNew.Should().NotBe(sv);
                    }
                    if (args.Instruction.ToString() == "++b")
                    {
                        branchesVisited++;
                        var svNew = args.ProgramState.GetSymbolValue(bSymbol);
                        svNew.Should().NotBeNull();
                        svNew.Should().NotBe(sv);
                    }
                };

            context.Walk();

            numberOfProcessedInstructions.Should().Be(11);
            branchesVisited.Should().Be(5);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_NonLocalNorFieldSymbolBranching()
        {
            var testInput = "if (Property) { cw(); }";
            var context = new ExplodedGraphContext(testInput);
            var numberOfProcessedInstructions = 0;
            var propertySymbol = context.SemanticModel.GetSymbolInfo(context.MainMethod.DescendantNodes()
                .OfType<IdentifierNameSyntax>().First(d => d.Identifier.ToString() == "Property")).Symbol;
            propertySymbol.Should().NotBeNull();
            context.EG.InstructionProcessed +=
                (sender, args) =>
                {
                    numberOfProcessedInstructions++;
                    if (args.Instruction.ToString() == "Property")
                    {
                        args.ProgramState.GetSymbolValue(propertySymbol).Should().BeNull();
                    }
                };

            context.Walk();     // Only EG final status check
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_LoopExploration()
        {
            var testInput = "var i = 0; while (i < 1) { i = i + 1; }";
            var context = new ExplodedGraphContext(testInput);
            var exceeded = 0;
            context.EG.ProgramPointVisitCountExceedLimit += (sender, args) =>
            {
                exceeded++;
                args.ProgramPoint.Block.Instructions.Should().Contain(i => i.ToString() == "i < 1");
            };

            context.EG.Walk();

            exceeded.Should().Be(1);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_InternalStateCount_MaxReached()
        {
            if (TestContextHelper.IsAzureDevOpsContext) // ToDo: test throws OutOfMemory on Azure DevOps
            {
                return;
            }

            var testInput = @"
using System;

namespace TesteAnalyzer
{
    class Program
    {
        static bool GetBool() { return bool.Parse(""True""); }

        static void Main(string[] args)
        {
            bool corrupted = false;
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();
            corrupted |= !GetBool();

            if (!corrupted)
            {
                Console.Out.WriteLine();
            }
        }
    }
}
";
            var context = new ExplodedGraphContext(TestHelper.Compile(testInput));
            var maxInternalStateCountReached = false;
            context.EG.MaxInternalStateCountReached += (sender, args) => { maxInternalStateCountReached = true; };

            context.EG.Walk();  // Special case, walk and check everythink manually

            maxInternalStateCountReached.Should().BeTrue();
            context.NumberOfExitBlockReached.Should().Be(0);
            context.ExplorationEnded.Should().BeFalse();
            context.MaxStepCountReached.Should().BeFalse();
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_CoalesceAssignment()
        {
            var testInput = @"string s = null; s ??= ""Empty""; s.ToString();";
            var context = new ExplodedGraphContext(testInput);
            var sSyntax = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>().Single(d => d.Identifier.ToString() == "s");
            var sSymbol = context.SemanticModel.GetDeclaredSymbol(sSyntax);
            var numberOfValidatedInstructions = 0;
            context.EG.InstructionProcessed += (sender, args) =>
                {
                    if(args.Instruction.ToString() == "s.ToString()")
                    {
                        numberOfValidatedInstructions++;
                        args.ProgramState.HasConstraint(args.ProgramState.GetSymbolValue(sSymbol), ObjectConstraint.NotNull).Should().BeTrue();
                    }
                };

            context.Walk();

            numberOfValidatedInstructions.Should().Be(1);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_SwitchExpression_SimpleExpression()
        {
            var testInput = @"string s = null; s = (s == null) switch { true => ""Value"", _ => s}; s.ToString();";
            var context = new ExplodedGraphContext(testInput);
            var sSyntax = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>().Single(d => d.Identifier.ToString() == "s");
            var sSymbol = context.SemanticModel.GetDeclaredSymbol(sSyntax);
            var numberOfValidatedInstructions = 0;
            context.EG.InstructionProcessed += (sender, args) =>
            {
                if (args.Instruction.ToString() == "s.ToString()")
                {
                    numberOfValidatedInstructions++;
                    args.ProgramState.HasConstraint(args.ProgramState.GetSymbolValue(sSymbol), ObjectConstraint.NotNull).Should().BeTrue();
                }
            };

            context.Walk();

            numberOfValidatedInstructions.Should().Be(1);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_SwitchStatement()
        {
            var testInput = @"string s=null; switch(s==null) {case true: s=""Value""; break; default : break;}; s.ToString();";
            var context = new ExplodedGraphContext(testInput);
            var sSyntax = context.MainMethod.DescendantNodes().OfType<VariableDeclaratorSyntax>().Single(d => d.Identifier.ToString() == "s");
            var sSymbol = context.SemanticModel.GetDeclaredSymbol(sSyntax);
            var numberOfValidatedInstructions = 0;
            context.EG.InstructionProcessed += (sender, args) =>
            {
                if (args.Instruction.ToString() == "s.ToString()")
                {
                    numberOfValidatedInstructions++;
                    args.ProgramState.HasConstraint(args.ProgramState.GetSymbolValue(sSymbol), ObjectConstraint.NotNull).Should().BeTrue();
                }
            };

            context.Walk();

            numberOfValidatedInstructions.Should().Be(1);
        }

        [TestMethod]
        [TestCategory("Symbolic execution")]
        public void ExplodedGraph_StaticLocalFunctions()
        {
            var testInput = @"static string Local(object o) {return o.ToString()} Local(null);";
            var context = new ExplodedGraphContext(testInput);
            var numberOfValidatedInstructions = 0;
            context.EG.InstructionProcessed += (sender, args) =>
            {
                if (args.Instruction.ToString() == "o.ToString()")
                {
                    numberOfValidatedInstructions++;
                }
            };

            context.Walk();

            numberOfValidatedInstructions.Should().Be(0);   // Local functions are not supported by CFG (yet)
        }

        private class ExplodedGraphContext
        {
            public readonly SemanticModel SemanticModel;
            public readonly MethodDeclarationSyntax MainMethod;
            public readonly IMethodSymbol MainMethodSymbol;
            public readonly AbstractLiveVariableAnalysis LVA;
            public readonly IControlFlowGraph CFG;
            public readonly CSharpExplodedGraph EG;

            public bool ExplorationEnded;
            public bool MaxStepCountReached;
            public int NumberOfExitBlockReached;

            public ExplodedGraphContext(string methodBody)
                : this(ControlFlowGraphTest.CompileWithMethodBody(string.Format(TestInput, methodBody), "Main", out var semanticModel), semanticModel)
            { }

            public ExplodedGraphContext((SyntaxTree tree, SemanticModel semanticModel) compilation)
                : this(compilation.tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>().Single(m => m.Identifier.ValueText == "Main"), compilation.semanticModel)
            { }

            public ExplodedGraphContext(SyntaxTree tree, SemanticModel semanticModel)
                : this(tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>().Single(m => m.Identifier.ValueText == "Main"), semanticModel)
            {}

            private ExplodedGraphContext(MethodDeclarationSyntax mainMethod, SemanticModel semanticModel)
            {
                this.MainMethod = mainMethod;
                this.SemanticModel = semanticModel;
                this.MainMethodSymbol = semanticModel.GetDeclaredSymbol(this.MainMethod) as IMethodSymbol;
                this.CFG = CSharpControlFlowGraph.Create(this.MainMethod.Body, semanticModel);
                this.LVA = CSharpLiveVariableAnalysis.Analyze(this.CFG, this.MainMethodSymbol, semanticModel);
                this.EG = new CSharpExplodedGraph(this.CFG, this.MainMethodSymbol, semanticModel, this.LVA);
                this.EG.ExplorationEnded += (sender, args) => { this.ExplorationEnded = true; };
                this.EG.MaxStepCountReached += (sender, args) => { this.MaxStepCountReached = true; };
                this.EG.ExitBlockReached += (sender, args) => { this.NumberOfExitBlockReached++; };
            }

            public void Walk()
            {
                this.EG.Walk();
                this.ExplorationEnded.Should().Be(true);
                this.NumberOfExitBlockReached.Should().Be(1);
                this.MaxStepCountReached.Should().Be(false);
            }
        }

    }
}
