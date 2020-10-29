package edot

import fastparse._
import ScalaWhitespace._
import Syntax._
import CharPredicates._
import edot.Parser.anything
import fastparse.Parsed.Success
import fastparse.internal.Logger
import pprint.PPrinter

object Parser {
  val logged = collection.mutable.Buffer.empty[String]
  implicit val logger = Logger(logged.append(_))

  type Id = String
  /** we convert variable names on the fly to deBruijn indices, by threading an implicit scope through the parser */
  case class Scope(vars : List[Id] = List(), //for deBruijn conversion
                   splices : Array[Exp] = Array()) { // for splicing abstract syntax into expressions
    override def toString: String = {
      List(vars.toString(), splices.mkString("Array(", ", ", ")")).mkString("Scope(", ", ", ")")
    }
  }
  object Scope {
    def apply(xs : String*) : Scope = new Scope(xs.toList, Array())
  }

  /** retrieve deBruijn index for a give variable name in scope */
  def lookup(x: Id)(implicit scope : Scope) : Int = {
    val res = scope.vars.indexOf(x)
    assert(res >= 0, s"unbound variable : ${x}")
    res
  }
  /** retrieve the i-th exp for splicing into the i-th hole */
  def splice(i : Int)(implicit scope : Scope) : Exp = scope.splices(i)


  implicit class ListOps(val xs : List[Id]) extends AnyVal {
    def +++(that: Scope) : Scope = Scope(xs ++ that.vars, that.splices)
  }

  def keyword[_ : P] = P { StringIn("Top", "⊤",  "Bot", "⊥", "Nat", "ℕ", "Type", "Set", "Pi", "Π") }
  def `=>`[_ : P] = P {StringIn("=>", "⇒")}
  def `.`[_ : P] = P {"."}
  def `..`[_ : P] = P {".."}
  def `<:`[_ : P] = P {"<:"}
  def `:>`[_ : P] = P {":>"}
  def ident[_ : P] = P {
    !keyword ~ CharPred(isLetter).repX(1) ~~ CharPred(c => isLetter(c) || isDigit(c) || c == '-').repX ~~ "'".repX
  }
  def variable[_ : P](implicit scope : Scope = Scope()) : P[♯] = P { ident.! map { x => ♯(lookup(x),x) } }
  def hole[_ : P](implicit scope : Scope = Scope()) : P[Exp] = P { "?" ~~ CharIn("0-9").repX(1).! map { x => splice(x.toInt)  } }
  def number[_ : P] : P[Num] = P { CharIn("0-9").repX(1).! map { x => Num(x.toInt)} }
  def parens[_ : P,A](p : => P[A]): P[A] = P { "(" ~ p ~ ")" }
  def braces[_ : P,A](p : => P[A]): P[A] = P { "{" ~ p ~ "}" }
  def set[_ : P] : P[Set] = P { (StringIn("Set") ~ number) map { case Num(i) => Set(i) }  }
  def nat[_ : P] : P[Nat.type] = P {  StringIn("Nat", "ℕ") map { _ => Nat }  }
  def top[_ : P] : P[Top.type] = P {  StringIn("Top", "⊤") map { _ => Top }  }
  def bot[_ : P] : P[Bot.type] = P {  StringIn("Bot", "⊥") map { _ => Bot }  }
  def tsel[_ : P](implicit scope : Scope = Scope()) : P[TSel] = P { (exp ~ `.` ~ StringIn("Type")) map TSel }
  def typeval[_ : P](implicit scope : Scope = Scope()) : P[TypeVal] = P { ("{" ~ "Type" ~ "=" ~ typ ~ "}") map TypeVal }

  def abstype[_ : P](implicit scope : Scope = Scope()) : P[AbsType] = {
    def full = P { "{" ~ "Type" ~ ":" ~ typ ~ `..` ~ typ ~ "}" }
    def upper = P { ("{" ~ "Type" ~ `<:` ~ typ ~ "}").map( (Bot,_) ) }
    def lower = P { ("{" ~ "Type" ~ `:>` ~ typ ~ "}").map( (_,Top) ) }
    P { ( upper | lower | full ) map { case (e1, e2) => AbsType(e1, e2) }}
  }

  def binders[_:P] : P[List[Id]] = P { (ident | "_").!.rep(1).map(_.toList.reverse) }
  def funtype[_ : P](implicit scope : Scope = Scope()) : P[Π] = {
    def pitype = P { StringIn("Pi", "Π") ~ typ ~ typ_lam } map { case (e1 , e2) => Π(e1, e2) }
    def depfun = for {
      xs  <- "(" ~ binders ~ ":"
      e1 <- typ ~ ")" ~ `=>`
      e2 <- typ(implicitly, xs +++ scope)
    } yield xs.tail.foldRight(Π(e1,Lam(e2))) { (_, e) => Π(e1,Lam(e)) }
    def nondep = P { (typ1 ~ `=>` ~ typ) map {case (e1, e2) => Π(e1, Lam(e2))}}
    P { pitype | depfun | nondep }
  }

  def lam[_ : P](sort : Scope => P[Exp])(implicit scope : Scope = Scope()) : P[Lam] = {
    def body : P[Lam] = for {
      args <- binders ~ `=>`
      e <- sort(args +++ scope)
    } yield args.tail.foldRight(Lam(e)) {case (_,l) => Lam(l)}
    braces(body)
  }

  def typ_lam[_ : P](implicit scope : Scope = Scope()): P[Lam] = lam(typ(implicitly,_))
  def exp_lam[_ : P](implicit scope : Scope = Scope()): P[Lam] = lam(exp(implicitly,_))

  def typ1[_ : P](implicit scope : Scope = Scope()) : P[Exp] = P {
    set | top | bot | nat | abstype | tsel | hole | parens(typ)
  }

  def typ[_ : P](implicit scope : Scope = Scope()) : P[Exp] = P {
    funtype | typ1
  }

  def exp1[_ : P](implicit scope : Scope = Scope()) : P[Exp] = P {
    number | variable | hole | exp_lam | typeval | parens(exp)
  }

  def exp[_ : P](implicit scope : Scope = Scope()) : P[Exp] = P {
    exp1.rep(1).map(_.reduceLeft(App))
  }

  def toplevel[_ : P](implicit scope : Scope = Scope()) : P[Exp] = P { exp ~ End }

  //TODO support global and local decls
  //would be nice if we could read files with sequences of decls and have these be bound
  //by their assigned name in the repl

  def anything[_ : P](implicit scope : Scope = Scope()) : P[Exp] = P { (typ | exp) ~ End}

}

object Interpolation {
  import fastparse.Parsed
  import fastparse.Parsed.Success
  implicit class ParseHelper(val sc : StringContext) extends AnyVal {
    private def join() : String = {
      var i = 0
      sc.parts.reduceLeft { (a, b) =>
        val y = i
        i = i + 1
        a ++ s"?$y" ++ b
      }
    }
    def e(es : Exp*) : Parsed[Exp] = {
      val scope : Parser.Scope = Parser.Scope(List(), es.to(Array))
      parse(join(), Parser.exp(_,scope))
    }
    def t(es : Exp*) : Parsed[Exp] = {
      val scope : Parser.Scope = Parser.Scope(List(), es.to(Array))
      parse(join(), Parser.typ(_,scope))
    }
    def p(es : Exp*) : Exp = {
      val scope : Parser.Scope = Parser.Scope(List(), es.to(Array))
      val Success(e, _) = parse(join(), Parser.anything(_,scope))
      e
    }
    //TODO have interpolators that perform normalization and read-back, that would require a type checker
  }
}

object FileOps {
  import ammonite.ops._
  def p(path : Path) : Exp = {
    val Success(exp, _) = parse(read! path, Parser.anything(_))
    exp
  }
  def e(path : Path) : Exp = {
    val Success(exp, _) = parse(read! path, Parser.exp(_))
    exp
  }
  def t(path : Path) : Exp = {
    val Success(exp, _) = parse(read! path, Parser.typ(_))
    exp
  }
}
//TODO use cuts/NoCut where appropriate
//TODO lambdas and applications at type level?

