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
  `CategoricalBayesianNetworks.jl`. Everything is hidden unless declared observed, by name
  on every foot (`observed = [...]`) or foot by foot
  (`observed = (inputs = [...], outputs = [...])`). A pass-through variable observed on the
  input foot and hidden on the output foot is forgotten at the boundary; hidden on the
  input foot and observed on the output foot, it is revealed by the component, whose own
  decisions still may not read it. Two
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
- **Optimisation, contextual and never isolated.** A composite is an ordinary
  `InfluenceDiagram`, and
  [`optimize`](@ref optimize(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict))
  hands a closed composite to the solvers of `InfluenceDiagrams.jl`. An open component
  `f : X → Y` has no expected utility of its own: [`contextual_value`](@ref) scores it
  under a fixed strategy against an explicit prior `μ` on its joint input states and an
  explicit continuation `c` on its joint output states, `Σ_x μ(x) Σ_y (W(y, x) + K(y | x) c(y))`,
  and [`contextual_optimize`](@ref) maximises that over the legal deterministic strategies,
  by handing the component to the `ExhaustivePolicySearch` of `InfluenceDiagrams.jl` with
  the prior over its input variables and the continuation over its output variables as a
  `DecisionContext` (its brute-force path, through `interpret`, is the cross-check).
  For a serial composite `f ⋅ g` the contexts are the suffix's value function
  ([`continuation_value`](@ref)) and the prefix's boundary law ([`boundary_law`](@ref)),
  and the contextual identity `EU_{f;g}(σ, τ; μ, c) = EU_f(σ; μ, c_τ) = L_σ + EU_g(τ; ν_σ, c)`
  holds; the test suite checks it against the closed-composite oracle, and checks that
  both orders of contextual maximisation reach the optimum the solvers find.
  There is deliberately no "optimise each component, then compose" operation. The test
  suite reproduces the counterexample of the research bundle's Lean track: a fair hidden
  bit, an early action with utility `-[A]`, a late action that observes only `A` with
  utilities `4[A]` and `2[B = H]`. Each component optimised in isolation (zero
  continuation, actual induced prior) composes to the value `1`, while the composite
  attains `4`. Maximising separately at each hidden boundary state would need a policy that
  reads the hidden input, which rule 3 rejects.

## Not yet here

ADR 0018 also plans the Lean proofs of the semantics and of the optimisation results, and
vignettes. They are later milestones. The functoriality of `interpret`, the contextual
identity and the counterexample are checked numerically, not proved. Randomised
(behavioural) policies and evidence across a boundary are outside the first release. The
Lean project in `proofs/` builds on the proof projects of `CategoricalBayesianNetworks.jl`
and `InfluenceDiagrams.jl` and so far states only boundary observability and information
locality.

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

The closed composite is solved by `InfluenceDiagrams.jl`'s solvers; the open decision
component reaches the same optimum when it is optimised against the law the chance
component induces on the boundary:

```jldoctest umbrella
julia> optimize(compose(chance, decide), ks, bound_utilities(m)).expected_utility ≈ 77
true

julia> ν = boundary_law(chance, ks, bound_utilities(m), Strategy());

julia> contextual_optimize(decide, ks, bound_utilities(m); prior = ν).expected_utility ≈ 77
true
```

See the API Reference for the docstrings.
