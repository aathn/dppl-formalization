# Agda Formalization for Jacana: Sound Composition of Differentiation, ODE Solving, and Stochastic Processes

This is the Agda code accompanying the paper "Jacana: Sound Composition of Differentiation, ODE Solving, and Stochastic Processes".

The code is primarily meant to be typechecked to check its correctness; this can be done using the command

```
agda src/Everything.agda
```

The file `Everything.agda` also contains an overview of the different modules in the repository.

For main points of interest, see the following table.
The abbreviation DPPL is short for Differential (Probabilistic) Programming Language.

| File                                  | Content                         |
|---------------------------------------|---------------------------------|
| src/DPPL/Syntax.agda                  | Abstract syntax                 |
| src/DPPL/Typing.agda                  | Typing relation                 |
| src/DPPL/SmallStep.agda               | Operational semantics           |
| src/DPPL/Denotations/Model.agda       | Abstract denotational semantics |
| src/DPPL/Denotations/Domain.agda      | Semantic domain                 |
| src/DPPL/Denotations/Denotations.agda | Instantiation of the semantics  |
| src/DPPL/Properties/Progress.agda     | Proof of progress               |
| src/DPPL/Properties/Preservation.agda | Proof of preservation           |
| src/DPPL/Properties/Determinism.agda  | Proof of determinism            |

The code was developed using a bleeding-edge version of Agda 2.8, along with the 1lab library for cubical Agda.
You may need to match the commit hashes below to be able to check the proofs.

TODO: Update these! (especially fix/list the dependency on my own fork of 1lab)
Commits:
- agda: 0feec2519d580aaf8cc18b791c16790ca738bfd1
- 1lab: e51776c97deb6faffa48b8d74e1542e43f1d8a42

The proofs are based on an axiomatisation of the real numbers (in `src/Lib/Algebra/Reals.agda`) as well as an axiomatisation of regularity properties such as continuity and piecewise analyticity under analytic partitioning (PAP) (in `src/DPPL/Denotations/Regularity.agda`).
Furthermore, the denotational semantics rely on some regularity properties of operations like differentiation, which were only proven on paper (listed in `src/DPPL/Denotations/Denotations.agda`).
Similarly, the operational semantics and its soundness proof rely on abstract implementations of automatic differentiation and ODE solving (specified in `src/DPPL/SmallStep.agda`) which are assumed to be type-preserving (see `src/DPPL/Properties/Preservation.agda`).
Wherever such axiomatisations or assumptions are used, they are passed explicitly as parameters, no postulates are introduced.
Each such parameter is named using the scheme `XXXXAssumptions` (e.g., `EvalAssumptions` in `src/DPPL/SmallStep.agda`).
