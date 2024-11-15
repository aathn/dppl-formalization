# Agda Formalization for A Differential Probabilistic Programming Language

This is the Agda code accompanying the paper "A Differential Probabilistic Programming Language".

The code is primarily meant to be typechecked to check its correctness; this can be done using the command

```
agda src/Everything.agda
```

For main points of interest, see the following table:

| File                             | Content               |
|----------------------------------|-----------------------|
| src/Examples.agda                | Simple examples       |
| src/Syntax.agda                  | Abstract syntax       |
| src/Typing.agda                  | Typing relation       |
| src/SmallStep.agda               | Operational semantics |
| src/Properties/Progress.agda     | Proof of progress     |
| src/Properties/Preservation.agda | Proof of preservation |
| src/Properties/Determinism.agda  | Proof of determinism  |

The code was developed using Agda 2.7.0.1 and agda-stdlib 2.1.
