# Agda Formalization for Jacana: Sound Composition of Differentiation, ODE Solving, and Probabilistic Programming

This is the Agda code accompanying the paper "Jacana: Sound Composition of Differentiation, ODE Solving, and Probabilistic Programming".

The code is primarily meant to be typechecked to check its correctness; this can be done using the command

```
agda src/Everything.agda
```

The file `Everything.agda` also contains an overview of the different modules in the repository.

For main points of interest, see the following table.
The abbreviation DPPL is short for Differential Probabilistic Programming Language.

| File                                  | Content                |
|---------------------------------------|------------------------|
| src/DPPL/Syntax.agda                  | Abstract syntax        |
| src/DPPL/Typing.agda                  | Typing relation        |
| src/DPPL/SmallStep.agda               | Operational semantics  |
| src/DPPL/Denotations.agda             | Denotational semantics |
| src/DPPL/Properties/Progress.agda     | Proof of progress      |
| src/DPPL/Properties/Preservation.agda | Proof of preservation  |
| src/DPPL/Properties/Determinism.agda  | Proof of determinism   |

The code was developed using a bleeding-edge version of Agda 2.8, along with the 1lab library for cubical Agda.
You may need to match the commit hashes below to be able to check the proofs.

Commits:
- agda: 0feec2519d580aaf8cc18b791c16790ca738bfd1
- 1lab: e51776c97deb6faffa48b8d74e1542e43f1d8a42

A couple of lemmas were left unproven due to time constraints; these are passed explicitly as parameters wherever used, no postulates are introduced.
Such lemmas are introduced in record types named `TempAssumptions`, there is one in `src/DPPL/Denotations.agda` and one in `src/DPPL/Properties/Typing.agda`.
