package edot

import edot.Parser._
import Syntax.Printer.pprintln
import edot.Syntax._
import Sugar._
import fastparse._
import fastparse.Parsed.{Failure, Success}
import org.scalatest.funsuite.AnyFunSuite


class ParserTest extends AnyFunSuite {
  def testP[A](p : P[_] => P[A])(input : String)(expected : A): Unit = {
    val Success(value, _) = parse(input , p)
    assert(value == expected)
    pprintln(value)
  }
  def testExp(input : String)(expected : Exp)(implicit scope: Scope = Scope()): Unit = {
    testP(toplevel(_,scope))(input)(expected)
  }
  def testType(input : String)(expected : Exp)(implicit scope: Scope = Scope()): Unit = {
    testP(typ(_,scope))(input)(expected)
  }
  def failP[A](p : P[_] => P[A])(input : String): Unit = {
    val Failure(_,_,_) = parse(input , p)
    ()
  }
  def failExp(input : String)(implicit scope: Scope = Scope()): Unit = {
    failP(toplevel(_,scope))(input)
  }
  def failType(input : String)(implicit scope: Scope = Scope()): Unit = {
    failP(typ(_,scope))(input)
  }

  test("Curried lambdas") {
    testExp { "{x y _ z => z x y }" }
            { λ(λ(λ(λ(♯(0) ꞏ ♯(3) ꞏ ♯(2))))) }
  }
  test("Primes and non-dependent function types") {
    testExp { "{x' x'' _ x''' => x''' x' x'' } {Type = ((Nat => Top) => Nat => {Type : Nat .. Top}) } " }
            { λ(λ(λ(λ(♯(0) ꞏ ♯(3) ꞏ ♯(2))))) ꞏ Type(Π(Π(ℕ, λ(⊤)), λ(Π(ℕ, λ(Type(ℕ ꞏꞏ ⊤)))))) }
  }
  test("Function type 1") {
    testType { "(((_ : Nat) => Top) => Nat => {Type : Nat .. Top})  " }
             { Π(Π(ℕ, λ(⊤)), λ(Π(ℕ, λ(Type(ℕ ꞏꞏ ⊤))))) }
  }
  test("Function type 2.1") {
    testType { "Nat => /*yay!*/ Top //with comments! " }
             { Π(ℕ, λ(⊤)) }
  }
  test("Function type 2.2") {
    testType { "(x : Nat) => /*yay!*/ Top //with comments! "  }
             { Π(ℕ, λ(⊤)) }
  }
  test("Function type 2.3") {
    testType { "(_ : Nat) => /*yay!*/        Top //with comments! "  }
             { Π(ℕ, λ(⊤)) }
  }
  test("Function type 3") {
    implicit val scope : Scope = Scope("Vec")
    testType { "Pi Nat {n => (Vec n).Type}"  }
             { Π(ℕ, λ((♯(1) ꞏ ♯(0)).Type)) }
  }
  test("Function type 4") {
    testType { "Π ℕ {x => x.Type } "  }
             { Π(ℕ, λ(♯(0).Type)) }
  }
  test("Function type 4.1") {
    testType { "(x : ℕ) => x.Type "  }
             { Π(ℕ, λ(♯(0).Type)) }
  }
  test("Function type 5 (illegal)") {
    failType { "Π ℕ (f (Set 1)) " }
  }
  test("Function type 6 (multi-binders)") {
    testType { "(x y z _ : ℕ) => {Type : x.Type .. z.Type} " }
             { Π(ℕ, λ(Π(ℕ, λ(Π(ℕ, λ(Π(ℕ, λ(Type(♯(3).Type ꞏꞏ ♯(1).Type))))))))) }
  }
  test("Function type 7") {
    testType { "(x : {Type : Nat .. Top}) => x.Type " }
             { Π(Type(ℕ ꞏꞏ ⊤), λ(♯(0).Type)) }
  }
  test("Abstract type") {
    testType { "{Type : Nat .. Top}" }
             { Type(ℕ ꞏꞏ ⊤) }
  }
  test("Nested abstract type") {
    testType { "{Type : {Type : Nat .. Top} .. {Type :  {Type : Nat .. Bot}.. Top}}  " }
             { Type(Type(ℕ ꞏꞏ ⊤) ꞏꞏ Type(Type(ℕ ꞏꞏ ⊥) ꞏꞏ ⊤)) }
  }
  test("\"Type\" is not an identifier") {
    failP(ident(_))("Type")
  }

}
