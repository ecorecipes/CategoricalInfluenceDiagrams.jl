# CategoricalInfluenceDiagrams.jl

[![Build Status](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/actions/workflows/CI.yml)
[![Lean](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/actions/workflows/lean.yml/badge.svg)](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/actions/workflows/lean.yml)
[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://ecorecipes.github.io/CategoricalInfluenceDiagrams.jl/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Open influence diagrams as structured cospans: influence diagrams with typed boundaries, and
their composition.

Part of the ecorecipes compositional Bayesian-network ecosystem. This package is the
decision-layer analogue of `CategoricalBayesianNetworks.jl` (open Bayesian networks) and
builds on it and on `InfluenceDiagrams.jl` (decisions, utilities, policies and solvers),
which stays free of Catlab. The design is the workspace's ADR 0018,
[`docs/adr/0018-open-influence-diagrams.md`](docs/adr/0018-open-influence-diagrams.md).

## Features

- `OpenInfluenceDiagram`: a Catlab structured cospan with an `InfluenceDiagram` apex and
  `VariableSpace` feet, the same feet as an open Bayesian network, built with
  `Open(id; inputs, outputs, observed)`.
- Observability on the boundary: every interface variable is `:observed` (remembered
  information a later decision may read) or `:hidden`, and is hidden unless declared
  observed. Interfaces that differ only in observability do not match.
- The typed-interface rule of open networks, extended to decisions and utilities: at most
  one generator per variable, no generator on an input, decisions read only internal or
  observed inputs, utilities may read anything in the apex, the causal-plus-information
  graph is acyclic, and composition preserves no-forgetting (checked on every composite).
- `compose`, `glue`, `otimes` and `oapply` over undirected wiring diagrams, each a pushout
  or coproduct of ACSets with the rule checked again on the result.
- Open Bayesian networks embed with every boundary variable hidden, and convert back.
- `RewardKernel(K, W)`: the semantics of an open diagram under a fixed strategy, a
  `FiniteKernel` `K` from the inputs to the outputs with a table `W` of the
  probability-weighted reward earned on the way. Reward kernels compose by
  `(K₁K₂, W₁K₂ + K₁W₂)` and tensor by `(K₁⊗K₂, W₁⊗K₂ + K₁⊗W₂)`, with identity, copy,
  discard and swap lifted from `FiniteKernels.jl` with zero reward.
- `interpret(o, kernels, utilities, σ)` (or `interpret(o, model, σ)`) maps an open diagram
  and a deterministic strategy to its reward kernel; `merge_strategies` forms the strategy
  of a composite. On a closed composite it gives `(1, EU)`, and the test suite checks it
  against `expected_utility` of the closed composite under `compose`, `glue`, `otimes` and
  `oapply`, on the umbrella, oil-wildcatter and grazing examples and on random diagrams.
- Optimisation is contextual, never isolated. `optimize(o, kernels, utilities)` solves a
  closed composite with the solvers of `InfluenceDiagrams.jl`. `contextual_value` scores an
  open component under a fixed strategy against an explicit prior on its inputs and an
  explicit continuation value on its outputs, and `contextual_optimize` maximises that over
  its legal deterministic strategies. `continuation_value` (the suffix's value function)
  and `boundary_law` (the law the prefix induces on the boundary) give the contexts of a
  serial composite, for which the contextual identity holds; the test suite checks it
  against `expected_utility` of the closed composite. There is no "optimise each component,
  then compose" operation: the test suite reproduces the research bundle's Lean
  counterexample, where components optimised in isolation compose to the value 1 and the
  composite attains 4.
- Every name of `CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl` is re-exported.

Not yet here: the Lean proofs of the semantics and the optimisation results, and the
vignettes. They are later milestones of ADR 0018's plan. The laws of `RewardKernel`, the
functoriality of `interpret`, the contextual identity and the isolated-optimisation
counterexample are checked numerically, not proved. Randomised (behavioural) policies and
evidence across a boundary are outside the first release.
The Lean project in [`proofs/`](proofs/) so far states boundary observability and
information locality over the two parent proof projects; it proves no theorem about
composition yet.

## Installation

The ecosystem packages are not registered. Install this package and its ecosystem
dependencies by URL, in dependency order:

```julia
using Pkg
Pkg.add(url="https://github.com/ecorecipes/FiniteKernels.jl")
Pkg.add(url="https://github.com/ecorecipes/MarkovCategories.jl")
Pkg.add(url="https://github.com/ecorecipes/BayesianNetworkFormats.jl")
Pkg.add(url="https://github.com/ecorecipes/BayesianNetworks.jl")
Pkg.add(url="https://github.com/ecorecipes/BayesianNetworkInference.jl")
Pkg.add(url="https://github.com/ecorecipes/InfluenceDiagrams.jl")
Pkg.add(url="https://github.com/ecorecipes/CategoricalBayesianNetworks.jl")
Pkg.add(url="https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl")
```

Requires Julia ≥ 1.12.

## Quick Start

Split the umbrella problem into a chance component, which exports the weather (hidden) and
the forecast (observed), and a decision component, which imports both; then compose them
back:

```julia
using CategoricalInfluenceDiagrams

chance = Open(influence_diagram(:Weather => [:sunny, :rainy],
                                :Forecast => [:sunny, :cloudy, :rainy];
                                mechanisms = [:Weather => (), :Forecast => :Weather],
                                closed = false);
              outputs = [:Weather, :Forecast], observed = [:Forecast])

decide = Open(influence_diagram(:Weather => [:sunny, :rainy],
                                :Forecast => [:sunny, :cloudy, :rainy],
                                :Umbrella => [:take, :leave];
                                decisions = [:Umbrella => :Forecast],
                                utilities = [:U => (:Weather, :Umbrella)], closed = false);
              inputs = [:Weather, :Forecast], observed = [:Forecast])

whole = compose(chance, decide)
is_isomorphic(apex(whole), umbrella_diagram())   # true
```

Declaring the forecast hidden instead makes `decide` invalid: its decision would read a
variable that the boundary hides (`DiagramInterfaceError`, rule 3).

With numbers bound, each component denotes a reward kernel for a fixed strategy, and the
composite's is their composite:

```julia
m = umbrella_model()
ks = Dict(x => kernel(m, x) for x in (:Weather, :Forecast))
σ = Strategy(:Umbrella => deterministic_policy(m, :Umbrella, [:leave, :leave, :take]))
r = compose(interpret(chance, ks, bound_utilities(m), Strategy()),
            interpret(decide, ks, bound_utilities(m), σ))
r ≈ interpret(whole, ks, bound_utilities(m), σ)   # true
reward(r)[] ≈ 77                                   # true: the expected utility
```

The closed composite is solved by the solvers of `InfluenceDiagrams.jl`, and the open
decision component reaches the same optimum against the law the chance component induces
on the boundary:

```julia
optimize(whole, ks, bound_utilities(m)).expected_utility ≈ 77         # true
ν = boundary_law(chance, ks, bound_utilities(m), Strategy())
contextual_optimize(decide, ks, bound_utilities(m); prior = ν).expected_utility ≈ 77   # true
```

## Vignettes

Rendered vignettes will live in [`vignettes/`](vignettes/) and be published in the
[documentation](https://ecorecipes.github.io/CategoricalInfluenceDiagrams.jl/).
