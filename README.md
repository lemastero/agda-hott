# agda-hott

Notes in Agda about
* Homotopy Type Theory (based on
  * [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/) by Martín Hötzel Escardó, ([arxiv 1911.00580](https://arxiv.org/abs/1911.00580)),
  * [Introduction to Homotopy Type Theory](https://arxiv.org/abs/2212.11082) by Egbert Rijke)
* Category Theory (based on
  * CS410 Advanced Functional Programming at the University of Strathclyde by Conor McBride ([videos](https://www.youtube.com/playlist?list=PLqggUNm8QSqmeTg5n37oxBif-PInUfTJ2)), ([GH repo with code](https://github.com/pigworker/CS410-17)), ([lecture notes](https://github.com/pigworker/CS410-15/blob/master/CS410-notes.pdf)), ([GH 2018](https://github.com/pigworker/CS410-18)) [agda-categories](https://github.com/agda/agda-categories))
* Patterns of Functional Programming (inspired by category theory that can be found in Haskell, Scala, PureScript, Idris)

Patters of FP can be seen as continuation of [scala_typeclassopedia](https://github.com/lemastero/scala_typeclassopedia) - this time in Agda).

Section zio-prelude aims at formally verifying encoding from Scala library [zio-prelude](https://zio.dev/zio-prelude/) (that improve usuall encoding of FP abstractions e.g. by adding Zivariant, introducing novel definitions like ZRerf that is a generalization of optics).

Category theory definitions are strict - use equality (agda-categories are parametrized by equivalence relation).
