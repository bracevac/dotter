# Normalization by Evaluation (NbE)

We approach DOT from the perspective of predicative (Martin-Löf) type theory.
This is work in progress.

* Go beyond Scala/DOT. Generalize from path-dependent to full dependent types.
  * Path expressions become just a special case of full dependent types.
  * NbE for deciding equality.
* Model abstract types as forms of Sigma types/existentials.
* Combine predicative universe hierarchy, cumulativity, and subtyping with top types.
* Normalization by evaluation and its metatheory, following techniques by Andreas Abel.
* Agda formalization in the `agda/` folder. Currently working on completeness and strong normalization.
* Scala implementation in the `scala/` folder.

## References

**Normalization by Evaluation - Dependent Types and Impredicativity** (Habilitationsschrift 2013) by Andreas Abel ([pdf](http://www2.tcs.ifi.lmu.de/~abel/habil.pdf))
