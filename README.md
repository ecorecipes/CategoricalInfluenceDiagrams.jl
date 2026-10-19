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
  observed. `observed = [...]` flags a name on every foot it is on, and
  `observed = (inputs = [...], outputs = [...])` flags each foot separately, so a
  pass-through variable can be read inside a component and forgotten at its output, or
  revealed at its output without its own decisions reading it. Interfaces that differ only
  in observability do not match.
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
  its legal deterministic strategies, by handing the component to the exhaustive policy
  search of `InfluenceDiagrams.jl` with the prior and the continuation as a
  `DecisionContext` (and, with `brute_force = true`, by scoring every strategy through
  `interpret` instead). `continuation_value` (the suffix's value function)
  and `boundary_law` (the law the prefix induces on the boundary) give the contexts of a
  serial composite, for which the contextual identity holds; the test suite checks it
  against `expected_utility` of the closed composite. There is no "optimise each component,
  then compose" operation: the test suite reproduces the research bundle's Lean
  counterexample, where components optimised in isolation compose to the value 1 and the
  composite attains 4.
- Reward certificates (ADR 0019): `export_reward_certificate` writes a diagram, its
  observability flags and tables, a deterministic strategy and the reward kernel that
  `interpret` computed for it as an `OpenInfluence.RewardCertificate/v1` record, which the
  Lean checker in `proofs/` (`lake exe check_certificate`) decodes and checks against the
  exact semantics. Exact rational companions certify models whose binary64 tables do not
  sum to exactly one.
- Lenses and equilibria (ADR 0020): along a chain of components `f₁ ⋅ … ⋅ fₙ`,
  `component_contexts` computes the prior and the continuation each component receives
  (the forward and backward passes of the reward kernels' lenses), `regrets` and
  `is_equilibrium` test whether every component's strategy is a best response in its
  context, and `best_response_dynamics` improves one component at a time until none can
  gain. An equilibrium is what composes; it can be worth less than the optimum, which
  `optimize` on the closed composite finds.
- Every name of `CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl` is re-exported.

Randomised (behavioural) policies and evidence across a boundary are outside the first
release.

## Proofs

The Lean project in [`proofs/`](proofs/) builds on the proof projects of
`CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl`. Among its results:

- Reward kernels form a category: serial composition `(K₁, W₁) ; (K₂, W₂) = (K₁K₂, W₁K₂ + K₁W₂)` is associative and has the identity `(id, 0)` as a unit on both sides.
- For a fixed deterministic strategy, the interpretation of open influence diagrams sends serial composition to composition of reward kernels, identities to `(id, 0)`, and tensor to the tensor of reward kernels.
- For reward kernels whose suffix has a normalised probability component, and so for all open influence diagrams under a fixed strategy, `EU_{f;g}(μ, c) = EU_f(μ, c_g) = L_f + EU_g(ν_f, c)`.
- In the bundle's witness, every pair of separately optimal components composes to expected utility 1, while the joint optimum is 4.
- If the reward-certificate checker accepts a decoded certificate at tolerance `τ`, its network is valid, no decision of the decoded open influence diagram reads an input flagged hidden, and for every pair of boundary assignments `(x, y)` the recorded `K` and `W` cells at the flat index of `(x, y)`, which is a bijection onto the cells of `K`, are within `τ` of `interpret σ f` at `(x, y)`, for the decoded diagram `f` and strategy `σ`.
- The lens of a reward kernel, with the boundary law as its forward map and the value function as its backward map, sends serial composition with a normalised suffix to composition of lenses and the identity to the identity lens.
- For two decision games, a pair of strategies is an equilibrium of their serial composite exactly when neither component can raise the composite's expected utility by changing its own strategy alone.
- Every strategy that maximises expected utility in a context is an equilibrium there, for every game built from decision games and identities by serial composition.
- An equilibrium need not be optimal: in a witness of two decisions that must agree, the later not observing the earlier, an equilibrium is worth 1 where the optimum is 2.

The certificate result is about reward certificates (ADR 0019): `lake exe check_certificate`
decodes a certificate written by `export_reward_certificate` and checks it, so Julia's
numbers for a recorded diagram are checked against the Lean semantics. The last four are
about lenses and open games (ADR 0020), over the reward-kernel semantics; the tensor of games
is not defined. The syntax is not
quotiented by isomorphism, the semantics does not read observability flags, and nothing is
proved about arbitrary gluing, evidence, or whether a Julia composite is the Lean composite
of its parts; [`proofs/README.md`](proofs/README.md) lists every theorem and these
restrictions.
Each sentence above is checked against its Lean statement by the workspace's SA-Pass
harness. The Julia test suite checks the same laws numerically.

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

| # | Vignette | Description |
|---|---|---|
| 1 | [Open influence diagrams and composition](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/blob/main/vignettes/01_open_influence_diagrams/01_open_influence_diagrams.md) | Observability flags, the typed-interface rule and its typed errors, splitting the umbrella problem and composing it back with `compose`, `glue`, `otimes` and `oapply`, and reward kernels checked against the expected utility of the closed composite |
| 2 | [Composing a management decision with a zoo network](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/blob/main/vignettes/02_management_decision_with_zoo_network/02_management_decision_with_zoo_network.md) | The zoo's reference habitat network opened at a boundary, a grazing decision and a valuation attached as components, the closed composite optimised, and the decision component optimised against the network's boundary law and value function |
| 3 | [Why optimisation does not compose](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/blob/main/vignettes/03_why_optimisation_does_not_compose/03_why_optimisation_does_not_compose.md) | The isolated-optimisation counterexample (1 < 4), why it fails, the contextual repair, and why pointwise maximisation over hidden boundary states is refused by rule 3 |

Each vignette is also published as a tutorial in the [documentation](https://ecorecipes.github.io/CategoricalInfluenceDiagrams.jl/);
the sources are the `.qmd` files in [`vignettes/`](vignettes/).
