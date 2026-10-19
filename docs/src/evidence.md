# Evidence across a boundary

An observation made in one component of a composite can change what is believed in every
other: a sighting downstream is evidence about the habitat upstream, and a survey reading
upstream changes the value of a decision downstream. ADR 0021 says how evidence crosses a
boundary between open influence diagrams, and what has to be carried with it.

## A component with evidence

[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy))
takes hard evidence on any variable of a component's apex, its inputs and outputs included:

```julia
r = interpret(o, kernels, utilities, σ; evidence = [:Sighting => :seen])
```

Evidence may also be soft: a likelihood vector, `:Weather => [0.2, 0.9]`, one entry in
`[0, 1]` per state, the probability of an observation given each state. It acts as the hard
observation of a virtual child variable with that likelihood would.

The result is still a [`RewardKernel`](@ref) `(K, W)`, but `K(y | x)` is now the probability
of reaching the output state `y` *and* seeing the evidence, and `W` the reward earned on
those paths. `K` is substochastic: its column sums are the probability of the evidence given
each input state. Nothing is normalised. Reward kernels with evidence compose exactly as
others do, and the evidence of a composite is the union of its components' evidence; evidence
on a variable of the shared boundary may be given to either side or to both, since an
indicator is idempotent.

## Why the mass must cross the boundary

Normalising each component on its own evidence before composing is not sound. Take a
uniform binary state worth `1` when it is true, and a sighting nine times likelier when the
state is true. Given the sighting the state is true with probability `9/10`, and that is the
value. Normalised on its own, the component holding the sighting has the evidence with
probability one from either state, and composing it with the prior gives `1/2`: the
likelihood of the evidence as a function of the boundary state is exactly what normalising
discards. The Lean module `Evidence` proves this witness
(`local_normalisation_obstruction`), and the test suite reproduces it.

## States, effects and the conditional value

The contexts of ADR 0018 and the lenses of ADR 0020 assume that what follows a component
has total probability one. With evidence they carry the mass:

- a **state** on a component's inputs, a reward kernel `I → X`, pairs the unnormalised law
  `ν(x)` of reaching `x` with the evidence seen so far and the reward-weighted law `ρ(x)`
  earned so far; [`boundary_state`](@ref) pushes it forward through a component;
- an **effect** on a component's outputs, a reward kernel `Y → I`, pairs the probability
  `m(y)` of the evidence still to come and the evidence-weighted value `c(y)` of what
  follows; [`continuation_effect`](@ref) pulls it back through a component.

A plain prior is the state `(μ, 0)` and a plain continuation the effect `(1, c)`, so every
function that takes a `prior` or a `continuation` also takes a state or an effect. Against
a state and an effect, a component has

- an [`evidence_mass`](@ref) `Σ_x ν(x) m'(x)`,
- an evidence-weighted value, [`contextual_value`](@ref), `Σ_x (ρ(x) m'(x) + ν(x) c'(x))`,
- and a [`conditional_value`](@ref), their ratio: the expected utility given all of the
  evidence,

where `(m', c')` is the effect pulled back through the component. Both pairings are the
same at every cut of a chain (the Lean theorems `mass_push` and `value_push`), so the
conditional value of a composite can be computed at any boundary from the two contexts
there:

```julia
s = boundary_state(prefix, kernels, utilities, σ)                     # forward
e = continuation_effect(suffix, kernels, utilities, τ;
                        evidence = [:Sighting => :seen])              # backward
conditional_value(middle, kernels, utilities, ρ; prior = s, continuation = e)
# == conditional_value(prefix ⋅ middle ⋅ suffix, kernels, utilities, σ ∪ ρ ∪ τ;
#                      evidence = [:Sighting => :seen])
```

Without evidence the mass is one, the state's probability row is [`boundary_law`](@ref),
the effect's reward row is [`continuation_value`](@ref), and the conditional value is the
contextual value.

## Optimisation and equilibria given evidence

[`contextual_optimize`](@ref) takes `evidence`, and a state or an effect as its context, and
then maximises the conditional value over the legal strategies, from value tables built in
one pass over the component's joint states, skipping strategies under which the evidence is
impossible, as `InfluenceDiagrams`' exhaustive search does on a closed
model with evidence. On a closed composite, `optimize(o, kernels, utilities; evidence)`
records the evidence on the model and calls `InfluenceDiagrams`' solvers. When the evidence
lies downstream of a decision, its probability depends on the strategy, and the conditional
value is not the evidence-weighted value up to a constant.

The chain functions of [Lenses and equilibria](games.md), [`component_contexts`](@ref),
[`regrets`](@ref), [`is_equilibrium`](@ref) and [`best_response_dynamics`](@ref), take
`evidence` on the variables of the chain. The contexts are then states and effects, each
component's conditional value in its context is the whole chain's, and every regret is the
gain in the chain's conditional value from one component's change alone.

## Rare and impossible evidence

[`conditional_value`](@ref) follows ADR 0014. A binary64 run is trusted when its evidence
mass is finite and at least `floatmin(Float64)` and none of its products of nonzero operands
fell below `floatmin`. Otherwise the value is recomputed exactly in
`Rational{BigInt}` and rounded correctly, so a mass that only underflowed gives the right
answer; only a mass that is exactly zero raises `ImpossibleEvidenceError`. The diagram forms
recompute from the model's tables; the reward-kernel form has only its tables, and decides
on them. A model with tolerated negative entries raises `IndeterminatePosteriorError` when
the mass is within the tolerance budget of zero. [`evidence_mass`](@ref) is an unnormalised
quantity and is returned as computed.

## What is proved

The Lean module `Evidence` proves, over arbitrary real tables, that the actions on states and
effects are functorial with no normalisation hypothesis, that the evidence mass and the
evidence-weighted value are the same on either side of a reward kernel, that the
contextual identity holds without normalisation once the mass is carried, that hard evidence
on a boundary is idempotent and commutes, and the local-normalisation witness. For the
syntax, it proves that weighting the interpretation by a likelihood on the generators' values
is functorial under serial composition and tensor. The binary64 rules above are not proved; the test suite checks the Julia functions against
`InfluenceDiagrams`' `expected_utility` of the closed composite with the evidence observed.
