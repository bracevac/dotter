import edot.Interpolation._
import edot.FileOps._
import edot.NbE._
import fastparse.Parsed.{Success, Failure}
import ammonite.ops._
import edot.Syntax._
import edot.Syntax.Sugar._

def help() = {
  println("Interpolators")
  println("=============\n")
  println("To parse a string as a type or expression, use the interpolator \"p\"")
  println("    > p\"{x => x}\"")
  println("    > res0: Exp = λ(♯0)\n")
  println("Interpolators support splicing in AST values (of type Exp), e.g.,")
  println("    > val id : Exp = p\"{x => x}\"")
  println("    > p\"{y => ${id} y }\"")
  println("    > res0: Exp = λ(λ(♯0) ꞏ ♯0)\n")
  println("Other possible interpolators are \"e\" (parse as expression) or \"t\" (parse as type).\n ")
  println("Normalization by Evaluation")
  println("===========================\n")
  println("To normalize and read-back an Exp Ast, invoke nf { <type AST> } { <exp AST> }, like so:")
  println("    > nf { p\"Set 0\" } { p\"( { x => { Type = x.Type } } {Type = Nat} ).Type\" }")
  println("    > res0: Exp = ℕ\n")
  println("File I/O")
  println("========\n")
  println("The \"p\", \"e\", and \"t\" are overloaded, accepting paths to files containing larger expressions:")
  println("    > p(pwd/'foo) //read and parse contents of file foo in pwd\n")
  println("Please refer to the Ammonite-Ops library docs to learn more about paths and file I/O.\n")
  println("Type \"help\" to show this message again.\n\n")
}

repl.prompt() = "> "
repl.pprinter() = edot.Syntax.Printer

help()
