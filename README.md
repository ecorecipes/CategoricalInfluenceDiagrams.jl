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
- Evidence across a boundary (ADR 0021): `interpret(...; evidence)` conditions a component
  on hard evidence or on likelihood (virtual) evidence, which gives a substochastic reward kernel that composes as any other.
  The contexts then carry the evidence mass: `boundary_state` pushes forward a state (the
  unnormalised law and the reward earned so far), `continuation_effect` pulls back an
  effect (the probability of the evidence still to come and the value downstream), and
  `evidence_mass` and `conditional_value` (the expected utility given the evidence) are the
  same at every cut of a chain. `contextual_optimize`, `optimize` on a closed composite and
  the equilibrium functions take `evidence` and maximise the conditional value; a mass
  below binary64's normal range is resolved exactly, as ADR 0014 requires. Normalising each
  component on its own evidence is not sound, and the test suite reproduces the Lean
  witness.
- Behavioural strategies (ADR 0022): a `StochasticPolicy` draws a decision's action from a
  table given its information; `interpret` and every function built on it take them.
  `contextual_optimize` searches deterministic strategies, which suffice when every decision
  has its own policy (Kuhn's theorem, proved in Lean for open influence diagrams, with and
  without evidence); decisions that share a name share a policy, and then randomising can
  help (the absent-minded driver), so `contextual_optimize` refuses shared names.
- Shared policies (ADR 0024): along a chain, `shared` ties decisions of different components
  to one policy. `policy_regrets` and `is_policy_equilibrium` test the first-order condition
  that holds at every optimum of the shared policies (the multi-self consistency of
  Piccione and Rubinstein: changing a policy's uses one at a time, the gains sum to at most
  zero; given evidence, the first-order changes of the conditional value), and
  `shared_policy_search` searches behavioural strategies on a grid, since the optimum of a
  shared policy can be randomised.
- Composition certificates (ADR 0023): `export_composition_certificate(A, B, ...)` writes the
  reward certificates of two parts and of their composite, and `lake exe check_composition`
  checks each and that the composite's recorded reward kernel is the composite of the parts'
  within the tolerance, which ties Julia's composite to the Lean composite of its parts,
  cell by cell. `export_tensor_certificate` does the same for `otimes`.
- Colimit certificates (ADR 0025): `export_colimit_certificate` records the parts and the
  composite of `compose`, `otimes`, `glue` or `oapply` with Catlab's cocone maps, and
  `lake exe check_composition` checks that the maps are a colimit witness (generators and
  utilities matched one to one, labels, tables, parents and scopes kept, only boundary
  variables joined); the composite's semantics is then exactly the junction sum of the
  parts', with no tolerance: the structure of Julia's composite is checked, not only its
  numbers.
- Every name of `CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl` is re-exported.


## Proofs

The Lean project in [`proofs/`](proofs/) builds on the proof projects of
`CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl`. Among its results:

- Reward kernels form a category: serial composition `(K₁, W₁) ; (K₂, W₂) = (K₁K₂, W₁K₂ + K₁W₂)` is associative and has the identity `(id, 0)` as a unit on both sides.
- For a fixed deterministic strategy, the interpretation of open influence diagrams sends serial composition to composition of reward kernels, identities to `(id, 0)`, and tensor to the tensor of reward kernels.
- For reward kernels whose suffix has a normalised probability component, and so for all open influence diagrams under a fixed strategy, `EU_{f;g}(μ, c) = EU_f(μ, c_g) = L_f + EU_g(ν_f, c)`.
- In the bundle's witness, every pair of separately optimal components composes to expected utility 1, while the joint optimum is 4.
- If the reward-certificate checker accepts a decoded certificate at tolerance `τ`, its network is valid, no decision of the decoded open influence diagram reads an input flagged hidden, and for every pair of boundary assignments `(x, y)` the recorded `K` and `W` cells at the flat index of `(x, y)`, which is a bijection onto the cells of `K`, are within `τ` of `interpret σ f` at `(x, y)`, for the decoded diagram `f` and strategy `σ`.
- If the composition checker accepts a composition certificate at tolerance `τ`, its parts' interfaces line up and, for every input coordinate `x` of the left part and output coordinate `z` of the right part, the decoded composite's exact probability and reward at `(x, z)` are within an explicit bound, computed from `τ` and the recorded cells, of the composite in the category of reward kernels of the decoded parts' exact tables.
- If the tensor checker accepts a tensor certificate at tolerance `τ`, the composite's interfaces are the parts' side by side and, for all coordinates of the two parts, the decoded composite's exact probability and reward at the joined coordinates are within an explicit bound, computed from `τ` and the recorded cells, of the tensor in the category of reward kernels of the decoded parts' exact tables.
- The lens of a reward kernel, with the boundary law as its forward map and the value function as its backward map, sends serial composition with a normalised suffix to composition of lenses and the identity to the identity lens.
- For two decision games, a pair of strategies is an equilibrium of their serial composite exactly when neither component can raise the composite's expected utility by changing its own strategy alone.
- Every strategy that maximises expected utility in a context is an equilibrium there, for every game built from decision games and identities by serial composition.
- An equilibrium need not be optimal: in a witness of two decisions that must agree, the later not observing the earlier, an equilibrium is worth 1 where the optimum is 2.
- For two decision games and a prior that is a product of probability vectors, a pair of strategies is an equilibrium of their tensor exactly when neither factor can raise the composite's expected utility by changing its own strategy alone.
- A strategy that maximises the value from every input state is a best response under every nonnegative prior, and a strategy of two such perfect games in series is an equilibrium exactly when, by backward induction, the suffix is perfect against the continuation and the prefix against the suffix's value function.
- Evidence composes: weighting the fixed-strategy interpretation of open influence diagrams by a likelihood on the values of the generators sends serial composition to composition of reward kernels and tensor to the tensor of reward kernels, and the likelihood one gives back the unweighted interpretation.
- Carrying the evidence mass, the backward action of reward kernels on effects and the forward action on states are functorial with no normalisation hypothesis, and the evidence mass and the evidence-weighted value of a state against an effect are the same on either side of a reward kernel.
- Normalising each component on its own evidence before composing is not sound: with a uniform binary state worth 1 when true and evidence nine times likelier when it is true, the conditional value is 9/10, while the components normalised one by one give 1/2.
- For a behavioural strategy, which gives every decision a table of action probabilities, the interpretation of open influence diagrams sends serial composition to composition of reward kernels, identities to `(id, 0)` and tensor to the tensor of reward kernels, and a deterministic strategy has the interpretation of its point masses.
- A mixture of reward kernels with nonnegative weights summing to one has expected utility at most that of one of its components, and, when masses are nonnegative and a component of zero mass has zero evidence-weighted value, conditional value at most that of one of its components of positive mass.
- Every stochastic kernel between finite spaces is the mixture of the deterministic kernels of its rules, each weighted by the probability of drawing it, so one randomised decision placed in a serial context, beside other wires, has expected utility at most that of some deterministic rule in its place.
- When two decisions share a policy, randomising can help: in the absent-minded driver, continuing with probability 2/3 at both junctions is worth 4/3, while either deterministic policy is worth at most 1; with a policy each, the deterministic pair that continues and then exits is worth 4 and no pair of probabilities does better.
- When no two decision generators of an open influence diagram share a label, every behavioural strategy is matched by a deterministic one: for every prior and continuation some deterministic strategy has at least its expected utility, and, with nonnegative likelihoods, a state whose reward vanishes where its mass does and an effect whose value vanishes where its likelihood does, if the evidence has positive mass some deterministic strategy gives it positive mass and at least the same conditional value.
- Isomorphic open influence diagrams have the same semantics under every behavioural strategy, and so under every deterministic one, and the semantics is a functor to `FinRew` from the category of typed interfaces and open influence diagrams up to isomorphism under serial composition.
- At an optimum of a policy shared by two uses in series, separated by any fixed kernels, the gain from changing the first use alone towards another policy plus the gain from changing the second use alone is at most zero.
- In the absent-minded driver, at the shared optimum of continuing with probability 2/3, continuing for sure at the first junction alone gains 2/3 and at the second junction alone loses 2/3.
- If the colimit checker accepts a colimit certificate, then for all input and output coordinates of the composite, exactly, its decoded probability is the sum, over the boundary coordinates of the parts consistent with them, of the product of the parts' decoded probabilities, and its decoded reward is the corresponding sum of each part's reward times the other parts' probabilities.
- Open influence diagrams up to isomorphism, with serial composition and the tensor, form a symmetric monoidal category, and for every behavioural strategy the semantics is a braided strong monoidal functor from it to `FinRew`.
- Given evidence of positive mass, at an optimum of the conditional value of a policy shared by two uses in series, the first-order changes in conditional value from changing each use alone towards another policy sum to at most zero.

The three certificate results are about reward certificates (ADR 0019) and composition and
tensor certificates (ADR 0023): `lake exe check_certificate` checks Julia's numbers for a
recorded diagram against the Lean semantics, and `lake exe check_composition` checks that a
recorded composite's semantics is the composite (or tensor) of its parts', which ties Julia's composite to the
Lean composite of its parts for the semantics, though not for the syntax. The next six are
about lenses and open games (ADR 0020), over the reward-kernel semantics: equilibria, the
tensor of games (exact for product priors; for correlated priors no context of one factor
suffices) and perfect equilibria. The three after them are about evidence (ADR 0021): the
evidence-weighted interpretation is proved functorial for serial composition and tensor,
and the binary64 rules of `conditional_value` are Julia's. The last four are about
behavioural strategies (ADR 0022). Of the last seven, the first is Kuhn's theorem for the
syntax (ADR 0022), the second makes the semantics a functor on diagrams up to isomorphism
(ADR 0025), the next two are about shared policies (ADR 0024), the fifth is about colimit
certificates (ADR 0025), which check the composite's structure as Catlab's cocone and give
its semantics exactly, the sixth makes the semantics a symmetric monoidal functor (ADR 0025),
and the last is the shared-policy condition given evidence (ADR 0024). The semantics does not
read observability flags, and the colimit certificates check structure on the decoded
records rather than as an isomorphism of `IDNet`s;
[`proofs/README.md`](proofs/README.md) lists every theorem and these restrictions.
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
| 4 | [Two agencies: equilibria of a monitoring and a management decision](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/blob/main/vignettes/04_equilibria_of_two_agencies/04_equilibria_of_two_agencies.md) | A survey component inserted into the zoo network: the joint optimum surveys, the status quo of no survey is also an equilibrium, and which one separate revision reaches depends on who revises first (ADR 0020) |
| 5 | [Evidence across a boundary](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/blob/main/vignettes/05_evidence_across_a_boundary/05_evidence_across_a_boundary.md) | Evidence held by one component of the zoo network's management chain: a wet year at the site changes the managers' best action, an absence found by the survey moves belief about the site's soil moisture, normalising a component on its own evidence loses it, and every cut gives the same conditional value (ADR 0021) |
| 6 | [Shared policies and colimit certificates](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/blob/main/vignettes/06_shared_policies_and_colimit_certificates/06_shared_policies_and_colimit_certificates.md) | A prescribed-burning rule applied in two seasons by managers who keep no record: the best shared rule burns with probability 4/7, the first-order test of `policy_regrets` holds there while each season alone would change, and a colimit certificate of the two-season composite is checked by the Lean checker (ADRs 0024 and 0025) |
| 7 | [Two tree diseases, one causal core](https://github.com/ecorecipes/CategoricalInfluenceDiagrams.jl/blob/main/vignettes/07_oak_mildew_and_ash_dieback/07_oak_mildew_and_ash_dieback.md) | Oak powdery mildew and ash dieback built from one shape of seasonal component (persistence, exposure, infection, then a persistence branch and a damage branch): the best oak planting stock depends on the inoculum context, and for ash a healthy crown says little about colonisation, so unconditional litter removal beats a symptom-triggered rule (illustrative tables) |

Each vignette is also published as a tutorial in the [documentation](https://ecorecipes.github.io/CategoricalInfluenceDiagrams.jl/);
the sources are the `.qmd` files in [`vignettes/`](vignettes/).
