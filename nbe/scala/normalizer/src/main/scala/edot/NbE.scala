package edot

import edot.Domain._
import edot.Syntax._
import Domain.Sugar._

object NbE {
  def app(v1 : Val, v2 : Val): Val = (v1, v2) match {
    case (VLam(body, env), v) => eval(body)(v :: env)
    case (VΠ(t, u) ⭡ ne , v) => (app(u, v) ⭡ NeApp(ne, t ⭣ v))
  }

  def tsel(v : Val): Val = v match {
    case VType(t) => t
    case VTType(_, _) ⭡ ne =>
      VSet(-1) ⭡ NeTSel(ne)
  }

  implicit class ValApp(val v : Val) extends AnyVal {
    def ꞏ(that : Val): Val = app(v, that)
    def Type : Val = tsel(v)
  }

  def eval(exp : Exp)(implicit env : Env) : Val = exp match {
    case Num(i)        => VNum(i)
    case ♯(index)      => env(index)
    case Lam(body)     => VLam(body, env)
    case App(fun, arg) => eval(fun) ꞏ eval(arg)
    case TypeVal(typ)  => VType(eval(typ))
    case Π(dom, cod)   =>
      val vcod@VLam(_,_) = eval(cod)
      VΠ(eval(dom), vcod)
    case TSel(t)       => eval(t).Type
    case AbsType(lb, ub) => VTType(eval(lb), eval(ub))
    case Nat           => VNat
    case Set(k)        => VSet(k)
    case Top           => VTop
    case Bot           => VBot
  }

  def quote(nf : NfVal)(implicit n : Int) : Exp = nf match {
    case VSet(k)        ⭣ VΠ(s, t)       => Π(quote(VSet(k) ⭣ s), quote((s ⟶ VSet(k)) ⭣ t))
    case VΠ(s, t)       ⭣ f              => val x = s ⭡ $(n+1)
                                            Lam(quote((t ꞏ x) ⭣ (f ꞏ x) )(n+1))
    case VSet(_)        ⭣ VNat           => Nat
    case VNat           ⭣ VNum(i)        => Num(i)
    /**
       TODO following Abel's observations, it does not seem necessary
       to have any kind of side conditions, such as ensuring the proper
       universe levels. If all we ever care about are well-typed terms, then
       it is a priori clear that the levels check out
     */
    case VSet(_)        ⭣ VSet(l)        => Set(l)
    case VSet(k)        ⭣ VTType(lb, ub) => AbsType(quote(VSet(k-1) ⭣ lb), quote(VSet(k-1) ⭣ ub))
    case VTType(t1, t2) ⭣ VType(t3)      => TypeVal(quote(VSet(-1) ⭣ t3))
    case VSet(_)        ⭣ VTop           => Top
    case VTop           ⭣ v              => ??? //TODO we're missing smth here
    case VSet(_)        ⭣ VBot           => Bot
    //case VBot           ⭣ v              => ??? // TODO I believe this case should not be possible
    case BaseType(_)    ⭣ (BaseType(_) ⭡ ne)      => quote(ne)
  }

  implicit class TruncSubtract(val x : Int) extends AnyVal {
    def ∸(y : Int) : Int = {
      assert(x >= 0)
      assert(y >= 0)
      if (y > x) 0 else x - y
    }
  }

  def quote(ne : NeVal)(implicit n : Int) : Exp = ne match {
    case $(level)        => ♯(n  ∸ (level + 1))
    case NeApp(fun, arg) => App(quote(fun), quote(arg))
    case NeTSel(typ)     => TSel(quote(typ))
  }

  def nf(typ: Exp)(exp: Exp)(implicit env: Env = List()): Exp = {
    implicit val n = env.length
    quote { eval(typ) ⭣ eval(exp) }
  }
}
