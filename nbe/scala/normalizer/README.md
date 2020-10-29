# Scala NbE Implementation of DSubE/EDOT

Implements NbE that largely follows Andreas Abel's habil thesis.

## Running

Integrates the [Ammonite REPL](https://ammonite.io) for quick experimentation.
To start just execute

    sbt run

or

    ./repl.sh

## Interpolators

To parse a string as a type or expression, use the [interpolator](https://docs.scala-lang.org/overviews/core/string-interpolation.html) `p`

```scala
    > p"{x => x}"
    > res0: Exp = λ(♯0)
```

Interpolators support splicing in AST values (of type `edot.Syntax.Exp`), e.g.,

```scala
    > val id : Exp = p"{x => x}"
    > p"{y => ${id} y }"
    > res0: Exp = λ(λ(♯0) ꞏ ♯0)
```

Other possible interpolators are `e` (parse as expression) or `t` (parse as type).

## Normalization by Evaluation

To normalize and read-back an Exp Ast, invoke `nf { <type AST> } { <exp AST> }`, like so:

```scala
    > nf { p"Set 0" } { p"( { x => { Type = x.Type } } {Type = Nat} ).Type" }
    > res0: Exp = ℕ
```

## File I/O

The `p`, `e`, and `t` are overloaded, accepting paths to files containing larger expressions:

```scala
    > p(pwd/'foo) //read and parse contents of file foo in pwd
```

Please refer to the [Ammonite-Ops](https://ammonite.io/#Ammonite-Ops)
documentation to learn more about paths and file I/O.

## TODOs

* Implement a bidirectional type checker

## References

**Normalization by Evaluation - Dependent Types and Impredicativity** (Habilitationsschrift 2013) by Andreas Abel ([pdf](http://www2.tcs.ifi.lmu.de/~abel/habil.pdf))
