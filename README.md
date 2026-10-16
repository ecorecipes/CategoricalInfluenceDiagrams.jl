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
- Every name of `CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl` is re-exported.

Not yet here: the compositional semantics of fixed strategies (`RewardKernel`, `interpret`),
contextual optimisation, their Lean proofs, and the vignettes. They are later milestones of
ADR 0018's plan. The Lean project in [`proofs/`](proofs/) so far states boundary
observability and information locality over the two parent proof projects; it proves no
theorem about composition yet.

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

## Vignettes

Rendered vignettes will live in [`vignettes/`](vignettes/) and be published in the
[documentation](https://ecorecipes.github.io/CategoricalInfluenceDiagrams.jl/).
