# Open influence diagrams: Lean 4

The Lean project of `CategoricalInfluenceDiagrams.jl` (ADR 0018, decision 5). It requires
two existing proof projects by relative path:

- `CategoricalBayesianNetworks.jl/proofs`, the typed open-network syntax category and its
  FinStoch interpretation (ADR 0010, namespace `OpenNet`);
- `InfluenceDiagrams.jl/proofs`, the finite influence-diagram model with instantiation,
  expected utility and optimisation (namespace `InfluenceDiagramsProofs`).

Through them it also requires the `BayesianNetworks.jl` and `FiniteKernels.jl` proof
projects. Lean, Mathlib and mdgen are pinned to **4.30.0**, and the Lake manifest shares
`../../.lake-packages` with the rest of the workspace.

## What is stated so far

`CategoricalInfluenceDiagramsProofs/Basic.lean` states the structure that open influence
diagrams add to the boundary of an open network, with no claim about composition:

| Declaration | Content |
|---|---|
| `OpenInfluence.Observability` | The flag of a boundary variable: `observed` or `hidden` |
| `OpenInfluence.ObservedInterface` | An `OpenNet.Interface` with a flag on every port |
| `ObservedInterface.sum`, `empty` | The tensor of interfaces with flags, and its unit |
| `ObservedInterface.sum_flag_inl`, `sum_flag_inr` | The tensor keeps each side's flags |
| `OpenInfluence.InformationLocal` | Rule 3: no decision reads a boundary variable flagged hidden |
| `informationLocal_of_no_hidden` | A boundary that hides nothing is information-local |
| `InformationLocal.of_reveal` | Revealing boundary variables preserves information locality |

The theorems ADR 0018 plans (decision and utility generators on the typed syntax, the
expectation-semiring kernel category with its monoidal structure, functoriality of the
fixed-strategy interpretation under composition and tensor, the contextual identity, and the
isolated-optimisation obstruction) are milestone M4 and are not stated here yet.

## Build and inspect

```sh
lake build --wfail
make audit
make docs
```

`make audit` kernel-checks every declaration listed in `Audit.lean`, uses
`assert_no_sorry`, and fails unless every printed axiom belongs to
`{propext, Classical.choice, Quot.sound}`. It rejects an empty inventory, scans every Lean
source for escape hatches (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`,
`implemented_by`, `extern`, `#eval`), and then runs the driver's synthetic guard
regressions. `make docs` generates the Markdown (mdgen), HTML (pandoc) and PDF (pandoc and
LuaLaTeX, with the workspace's JuliaMono fonts) from the checked Lean source. The Lean CI
workflow checks out the four sibling repositories beside this one, because Lake path
dependencies need them.
