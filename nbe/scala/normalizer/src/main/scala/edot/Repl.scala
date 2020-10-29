package edot
import ammonite.ops._

object Repl {
  def main(args : Array[String]): Unit = {
    ammonite.Main(predefFile = Some(pwd/"predef.sc"), welcomeBanner = Some("edot REPL") ).run()
  }
}
