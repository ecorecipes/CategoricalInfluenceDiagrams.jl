# CategoricalInfluenceDiagrams.jl

Open influence diagrams as structured cospans, following ADR 0018 of the ecosystem. The
package is the decision-layer analogue of `CategoricalBayesianNetworks.jl`: it gives the
influence diagrams of `InfluenceDiagrams.jl` open boundaries and composes them, keeping
Catlab out of the model layer (ADR 0009).

## What is here

- **Open influence diagrams.** An [`OpenInfluenceDiagram`](@ref) is a Catlab structured
  cospan whose apex is an `InfluenceDiagram` and whose feet are `VariableSpace`s, the same
  feet as those of an open Bayesian network. Build one with
  [`Open`](@ref Open(::InfluenceDiagram)).
- **Observability.** Every interface variable is `:observed`, remembered information that a
  later decision may read, or `:hidden`. The flags sit beside the cospan, one per interface
  position, rather than in the feet, so that the feet stay interchangeable with those of
  `CategoricalBayesianNetworks.jl`. Everything is hidden unless declared observed. Two
  interfaces that agree on variables and states but not on flags do not match
  ([`ObservabilityMismatchError`](@ref)).
- **The typed-interface rule**, checked by
  [`validation_errors`](@ref validation_errors(::OpenInfluenceDiagram)) and on construction:
  1. every variable has at most one generator, a chance mechanism or a decision;
  2. an input-foot variable has no generator in the apex;
  3. a decision reads only internal variables and *observed* input-foot variables;
  4. a utility scope may read any apex variable, inputs included;
  5. the causal-plus-information graph is acyclic;
  6. composition preserves no-forgetting when the components have it: checked on every
     composite, reported as a [`NoForgettingError`](@ref) naming the decision and the
     missing information arc.
- **Composition.** [`compose`](@ref compose(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)),
  [`glue`](@ref glue(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)),
  [`otimes`](@ref otimes(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)) and
  [`oapply`](@ref oapply(::UndirectedWiringDiagram, ::AbstractVector{<:OpenInfluenceDiagram}))
  are pushouts or coproducts of ACSets, with the rule checked again on the composite.
  Decisions and utilities stay inside their components; only variables cross a boundary.
- **Open Bayesian networks embed** with every interface variable hidden:
  `OpenInfluenceDiagram(o::OpenBayesNet)`, inverted by `OpenBayesNet(d)`.

- **Semantics for a fixed strategy.** A [`RewardKernel`](@ref) `(K, W)` pairs a
  `FiniteKernel` `K` from the input interface to the output interface with a table `W` of
  the same shape: the probability-weighted reward earned on the way. Reward kernels compose
  by `(K₁, W₁) ; (K₂, W₂) = (K₁K₂, W₁K₂ + K₁W₂)` and tensor by
  `(K₁ ⊗ K₂, W₁ ⊗ K₂ + K₁ ⊗ W₂)`, with identities, copies, discards and swaps lifted from
  `FiniteKernels.jl` with zero reward
  ([`compose`](@ref compose(::RewardKernel, ::RewardKernel)),
  [`otimes`](@ref otimes(::RewardKernel, ::RewardKernel)),
  [`identity_reward_kernel`](@ref), [`copy_reward_kernel`](@ref),
  [`discard_reward_kernel`](@ref), [`swap_reward_kernel`](@ref)). Discard is not natural:
  dropping an output keeps the reward earned on the way to it.
- **Interpretation.**
  [`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy))
  maps an open influence diagram and a deterministic strategy to its reward kernel, in the
  layout `CategoricalBayesianNetworks.jl` uses for open networks. The strategy of a
  composite is the disjoint union of its components' strategies
  ([`merge_strategies`](@ref)). On a closed composite the result is `(1, EU)`, with `EU`
  the expected utility that `InfluenceDiagrams.jl` computes, and the test suite checks
  `interpret` against that oracle under `compose`, `glue`, `otimes` and `oapply`, on every
  strategy of the umbrella and oil-wildcatter splits, on the SPEC §46 grazing diagram at
  two boundaries, and on random small diagrams.

A composite is an ordinary `InfluenceDiagram`, so the solvers of `InfluenceDiagrams.jl`
(`instantiate`, `expected_utility`, `optimize`) apply to it once it is closed.

## Not yet here

ADR 0018 also plans contextual optimisation (optimising a component against an explicit
boundary prior and continuation value), the Lean proofs of the semantics and of the
optimisation results, and vignettes. They are later milestones. The functoriality of
`interpret` is checked numerically, not proved. The Lean project in `proofs/` builds on the
proof projects of `CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl` and so far
states only boundary observability and information locality.

## Example

```@meta
DocTestSetup = :(using CategoricalInfluenceDiagrams)
```

```jldoctest umbrella
julia> chance = Open(influence_diagram(:Weather => [:sunny, :rainy],
                                       :Forecast => [:sunny, :cloudy, :rainy];
                                       mechanisms = [:Weather => (), :Forecast => :Weather],
                                       closed = false);
                     outputs = [:Weather, :Forecast], observed = [:Forecast]);

julia> decide = Open(influence_diagram(:Weather => [:sunny, :rainy],
                                       :Forecast => [:sunny, :cloudy, :rainy],
                                       :Umbrella => [:take, :leave];
                                       decisions = [:Umbrella => :Forecast],
                                       utilities = [:U => (:Weather, :Umbrella)],
                                       closed = false);
                     inputs = [:Weather, :Forecast], observed = [:Forecast]);

julia> is_isomorphic(apex(compose(chance, decide)), umbrella_diagram())
true
```

With the numbers of `umbrella_model`, the chance component's reward kernel composed with
the decision component's equals the composite's, whose reward is the expected utility:

```jldoctest umbrella
julia> m = umbrella_model();

julia> ks = Dict(x => kernel(m, x) for x in (:Weather, :Forecast));

julia> σ = Strategy(:Umbrella => deterministic_policy(m, :Umbrella, [:leave, :leave, :take]));

julia> r = compose(interpret(chance, ks, bound_utilities(m), Strategy()),
                   interpret(decide, ks, bound_utilities(m), σ));

julia> r ≈ interpret(compose(chance, decide), ks, bound_utilities(m), σ)
true

julia> reward(r)[] ≈ expected_utility(m, σ) ≈ 77
true
```

See the API Reference for the docstrings.
