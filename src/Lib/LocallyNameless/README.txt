The code in this folder was adapted for Cubical Agda from the
code accompanying the paper

Andrew M. Pitts, "Locally Nameless Sets", POPL 2023

Below follows the original README.txt of that development.


Locally Nameless Sets (Agda code)

(UPDATED VERSION 2023-02-18)

© 2023 Andrew Pitts, University of Cambridge

Agda (version 2.6.3) was used to develop the theory of locally
nameless sets and to check some of the proofs in the paper

Andrew M. Pitts, "Locally Nameless Sets", POPL 2023

The root is the file

Everything.agda

(for browsable code start at html/Everything.html).

The code mainly targets proofs that involve equational reasoning
combined with the use of atoms and indices that are sufficiently fresh
(via cofinite quantification). Some of these proofs involve a lot of
nested case analysis on elements of sets with decidable equality
(atoms and indices); some of the equational axioms are
unfamiliar-looking and combinatorially complicated; and it is easy to
forget to check necessary freshness conditions are satisfied when
doing informal proofs. For all these reasons the use of an interactive
theorem prover to produce machine-checked proofs was essential to gain
assurance that the results in the paper are correct. The Agda code is
stand-alone: some standard definitions (that might otherwise be called
from Agda's Standard Library) are collected in the file Prelude.agda.
The last part of the development requires function extensionality,
which we postulate in the file FunExt.agda.
