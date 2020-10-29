package edot

import edot.Syntax.{Exp, ♯}

object Domain {

  sealed trait Val

  sealed trait NfVal
  case class Reify(typ : Val, value : Val) extends NfVal

  sealed trait NeVal

  type Env = List[Val]

  case class VLam(body: Exp, env: Env) extends Val
  case class VNum(i : Int) extends Val
  case class VType(typ : Val) extends Val
  case class Reflect(typ : Val, ne : NeVal) extends Val
  case class VΠ(dom : Val, cod : Val) extends Val
  case class VTType(lb : Val, ub : Val) extends Val
  case class VSet(level : Int) extends Val //{ assert (level >= 0) }
  case object VNat extends Val
  case object VTop extends Val
  case object VBot extends Val

  case class $(level : Int) extends NeVal {
    assert (level >= 0)
  }
  case class NeApp(fun : NeVal, arg : NfVal) extends NeVal
  case class NeTSel(typ : NeVal) extends NeVal

  object Sugar {

    implicit class ValOps(val v: Val) extends AnyVal {
      def ⭡(that: NeVal): Reflect = Reflect(v, that)

      def ⭣(that: Val): Reify = Reify(v, that)

      def ⟶(that: Val): VΠ = VΠ(v, VLam(♯(1), List(that)))
    }

    object ⭡ {
      def unapply(v: Val): Option[(Val, NeVal)] = v match {
        case Reflect(typ, ne) => Some((typ, ne))
        case _ => None
      }
    }

    object ⭣ {
      def unapply(v: NfVal): Option[(Val, Val)] = v match {
        case Reify(typ, v) => Some((typ, v))
        case _ => None
      }
    }

    object ⟶ {
      def unapply(v: Val): Option[(Val, Val)] = v match {
        case VΠ(v, VLam(♯(1), env)) if env.isDefinedAt(0) => Some((v, env.head))
        case _ => None
      }
    }

  }

  object BaseType {
    import Sugar._
    def apply(v : Val) : Boolean = v match {
      case VBot | VTop | VNat | VSet(_) | (VSet(_) ⭡ _) => true
      case _ => false
    }
    def unapply(v : Val) : Option[Val] = Option.when(apply(v))(v)
  }
}