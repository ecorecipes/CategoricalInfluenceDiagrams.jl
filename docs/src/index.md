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
- **Lenses and equilibria** (ADR 0020). Along a chain of components,
  [`component_contexts`](@ref) gives each component the prior and continuation the rest of
  the chain induces, [`regrets`](@ref) and [`is_equilibrium`](@ref) test whether any one
  component could gain alone, and [`best_response_dynamics`](@ref) revises one component at
  a time until none can. An equilibrium can be worth less than the optimum; see
  [Lenses and equilibria](games.md).
- **Evidence across a boundary** (ADR 0021). `interpret` takes hard `evidence`, which
  makes a component's reward kernel substochastic; [`boundary_state`](@ref) and
  [`continuation_effect`](@ref) carry the evidence mass across a boundary, and
  [`evidence_mass`](@ref) and [`conditional_value`](@ref), the expected utility given the
  evidence, are the same at every cut. Normalising each component on its own evidence is
  not sound; see [Evidence across a boundary](evidence.md).
- **Reward certificates** (ADR 0019). [`export_reward_certificate`](@ref) writes a
  diagram, its flags and tables, a deterministic strategy and the reward kernel
  `interpret` computed for it as an `OpenInfluence.RewardCertificate/v1` record, for the
  Lean checker in `proofs/` (`lake exe check_certificate`). See
  [Reward certificates](certificates.md).

## Proofs, and what is not here

The Lean project in `proofs/` builds on the proof projects of
`CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl`. It proves the
reward-kernel category and its symmetric monoidal structure, the functoriality of the
fixed-strategy interpretation under serial composition and tensor, the contextual
identity, the two obstructions of the research bundle, lenses and open-game equilibria
(ADR 0020), and the composition of evidence (ADR 0021). Its checker for reward
certificates ties Julia's `interpret` of a recorded diagram to that interpretation, cell
by cell (ADR 0019). `proofs/README.md` lists the theorems and their restrictions; the
test suite checks the same laws numerically.

Randomised (behavioural) policies are outside the first release. That a Julia composite is the Lean composite of its parts is not proved: a
certificate checks the diagram it records, not the operation that built it.
