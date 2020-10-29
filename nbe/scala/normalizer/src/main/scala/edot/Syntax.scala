package edot

import pprint.PPrinter

object Syntax {

  sealed trait Exp
  case class Num(i: Int) extends Exp {
    override def toString: String = i.toString
  }
  case class ♯(index: Int) extends Exp {
    assert (index >= 0)
    var name : String = ""
    override def toString: String = s"♯${index}"
  }//deBruijn *index*
  object ♯ {
    def apply(index : Int, name : String) : ♯ = {
      val v = ♯(index)
      v.name = name
      v
    }
  }
  case class Lam(body: Exp) extends Exp {
    override def toString: String = s"λ{$body}"
  }

  case class App(fun: Exp, arg: Exp) extends Exp {
    override def toString: String = s"(${fun} ꞏ ${arg})"
  }
  case class TypeVal(typ: Exp) extends Exp {
    override def toString: String = s"{Type = ${typ}}"
  }

  case class Π(dom: Exp, cod: Exp) extends Exp
  case class TSel(t: Exp) extends Exp {
    override def toString: String = s"($t).Type"
  }
  case class AbsType(lb: Exp, ub: Exp) extends Exp {
    override def toString: String = s"{Type : ${lb} .. ${ub}}"
  }

  case class Set(level : Int) extends Exp {
    assert (level >= 0)
  }
  case object Nat extends Exp {
    override def toString: String = "ℕ"
  }

  case object Top extends Exp {
    override def toString: String = "⊤"
  }

  case object Bot extends Exp {
    override def toString: String = "⊥"
  }

  object Sugar {
    implicit class ExpSugar(val e : Exp) extends AnyVal {
      def ꞏ(that: Exp): App = App(e, that)
      def ꞏꞏ(that : Exp): (Exp, Exp) = (e, that)
      def Type : TSel = TSel(e)
    }
    val ⊥ = Bot
    val ⊤ = Top
    val ℕ = Nat

    object λ {
      def apply(body : Exp): Lam = Lam(body)
    }

    object Type {
      def apply(e : Exp): Syntax.TypeVal = Syntax.TypeVal(e)
      def apply(p: (Exp, Exp)): Syntax.AbsType = Syntax.AbsType(p._1, p._2)
    }
  }

  //TODO predicates for normal forms and neutral terms

  val Printer : PPrinter = pprint.copy(additionalHandlers = {
    case Num(i)       => pprint.Tree.Literal(i.toString)
    case ♯(index)     => pprint.Tree.Literal(s"♯${index}")
    case Lam(e)       => pprint.Tree.Apply("λ", Iterator(e).map(Printer.treeify(_)))
    case App(e1, e2)  => pprint.Tree.Infix(Printer.treeify(e1), "ꞏ", Printer.treeify(e2))
    case AbsType(e1,e2) => pprint.Tree.Apply("Type", Iterator(pprint.Tree.Infix(Printer.treeify(e1), "..", Printer.treeify(e2))))
    case TypeVal(e)   => pprint.Tree.Apply("", Iterator(pprint.Tree.Infix(pprint.Tree.Literal("Type"), "=", Printer.treeify(e))))
    case Top          => pprint.Tree.Literal(Top.toString)
    case Bot          => pprint.Tree.Literal(Bot.toString)
    case Nat          => pprint.Tree.Literal(Nat.toString)
  })
}



