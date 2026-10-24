# Lenses and equilibria

Optimisation of open influence diagrams is contextual (ADR 0018): a component `f : X → Y`
is valued against a prior `μ` on its inputs and a continuation `c` on its outputs, and the
optimum of a composite is not the composite of the components' optima. ADR 0020 adds the
solution concept that *does* compose, equilibrium in the sense of open games, and the
lenses that carry the contexts it needs.

## The lens of a component

Under a fixed strategy a component is a reward kernel `(K, W)`. It transports a context in
two directions:

- forward, a prior `μ` on its inputs becomes the law `ν = μ K` on its outputs
  ([`boundary_law`](@ref));
- backward, a continuation `c` on its outputs becomes the value function
  `x ↦ Σ_y (W(y, x) + K(y | x) c(y))` on its inputs ([`continuation_value`](@ref)).

The pair is a lens. For a chain `f₁ ⋅ f₂ ⋅ … ⋅ fₙ` under a strategy `σ`, the forward pass
gives each component the law on its inputs and the backward pass the value of its outputs.
[`component_contexts`](@ref) returns these contexts `(μᵢ, cᵢ)`. By the contextual identity,
component `i`'s value in its context is the value of the whole chain less the reward of the
components before it, which `i`'s own strategy cannot change. The Lean module `Lens` proves
that the lens of a serial composite is the composite of the lenses (`lens_comp`), so the
contexts do not depend on how the chain is bracketed.

## Equilibria

A strategy of the chain is an *equilibrium* when every component's part of it is a best
response in that component's context: no component can raise the value of the whole chain
by changing its own strategy alone. [`regrets`](@ref) returns, for each component, what it
would gain by its best response ([`contextual_optimize`](@ref) in its context);
[`is_equilibrium`](@ref) checks that every regret is at most a tolerance.

```julia
chain = [early, late]                 # e.g. the components of the third vignette
σ = merge_strategies(Strategy(:A => ConstantPolicy(:no)), Strategy(:B => ConstantPolicy(:no)))
component_contexts(chain, kernels, utilities, σ)   # [(prior, continuation), ...]
regrets(chain, kernels, utilities, σ)              # [3.0, 0.0]: the early component gains 3
is_equilibrium(chain, kernels, utilities, σ)       # false
```

[`best_response_dynamics`](@ref) replaces one component's strategy at a time by a best
response in its current context, while that strictly improves it, and stops at an
equilibrium. The value of the chain never decreases.

## What an equilibrium is not

An equilibrium is a person-by-person optimum: each component is optimal given the others.
The global optimum of the closed composite is always an equilibrium (`seq_sound`), but an
equilibrium can be worth less. Two decisions that must agree, where the later does not
observe the earlier, have an equilibrium in which neither acts, worth 1, and one in which
both act, worth 2 (`coordination_equilibrium_not_optimal`). Best-response dynamics started
from "neither acts" stays there. This is the local optimality of single policy updating in
limited-memory influence diagrams (Lauritzen and Nilsson, 2001), at the level of components.

So:

- use `optimize` on the closed composite for the optimum;
- use `component_contexts` to see what each component is optimised against, and `regrets`
  to check whether a proposed strategy can be improved by any one component on its own;
- use `best_response_dynamics` when components are owned or revised separately and the
  question is where separate revision settles, not what is best overall.

In the third vignette's counterexample, where components optimised in isolation compose to
1 against an optimum of 4, the equilibria are exactly the strategies that take the early
action, and they attain 4: optimising each component against the context its neighbours
induce repairs that example, though not every example.

Limited-memory chains, where the later decisions do not remember the earlier ones, are
composed with `no_forgetting = false`, a keyword all four functions accept and pass to
[`compose`](@ref). Behavioural strategies are covered by ADR 0022: a chain may start from
one, and best responses are deterministic. The tensor of games is proved in Lean (exact for
product priors, not expressible through one factor's context for correlated ones); the
Julia chain functions are serial.

## Perfect equilibria

An equilibrium can rest on a choice at a state it never reaches. A later component's policy
there is a best response whatever it is, because the state has probability zero, and it can
still deter an earlier component. `regrets(...; perfect = true)` and
`is_equilibrium(...; perfect = true)` ask more: every component optimal from every one of its
input states, against its continuation. This is subgame perfection, found by backward
induction. The Lean module `Perfection` proves that perfection refines equilibrium, and gives
the threat witness: not acting against an untested refusal is an equilibrium worth 1, while
the perfect equilibria act and cooperate, worth the optimum 4. Perfection is meaningful when
a component's decisions observe its inputs.

## Shared policies

Several components may have to use one policy: a rule applied every year, or decisions that
cannot be told apart, as in the absent-minded driver. `compose` refuses two decisions of one
name, so sharing is declared: `shared = [[:D1, :D2]]` ties `D2` to the policy of `D1`, which
the strategy gives (position by position; the information states and actions must agree in
size). The three functions of ADR 0024 take it.

The optimum of a shared policy can be randomised. In the absent-minded driver, continuing
with probability `2/3` at both junctions is worth `4/3`, and each deterministic policy is
worth at most `1`. At that optimum each junction on its own would still change: continuing
for sure at the first junction alone gains `2/3`. So the equilibria above, where each
component best responds on its own, are the wrong notion. What holds at an optimum is the
first-order condition of Piccione and Rubinstein's multi-self consistency. Change the policy
towards another one, value each use's change alone in its own context, and the gains sum to
at most zero. The Lean module `SharedPolicy` proves it (`shared_optimum_first_order`), from a
product rule for serial composites, and gives the driver's per-use gains `2/3` and `-2/3`.

- [`policy_regrets`](@ref) returns, for every policy, shared or not, the largest sum of
  per-use gains over deterministic replacements: the first-order gain. For a policy used
  once it is exactly the gain of changing that decision alone.
- [`is_policy_equilibrium`](@ref) tests that every such regret is at most `tol`.
- Given `evidence` (or a chain context that carries it), the value is the chain's
  conditional value `V = N / Z`, and a use's gain is the first-order change of the ratio,
  `(N_u - V Z_u) / Z` (`first_order_conditional` in Lean).
- [`shared_policy_search`](@ref) searches behavioural strategies whose probabilities are
  multiples of `1 / grid`, valuing each on the composite; the grid contains the deterministic
  strategies and, for a suitable `grid`, the randomised optimum.

```julia
s = shared_policy_search(chain, kernels, utilities; shared = [[:X1, :X2]], grid = 3)
policy_regrets(chain, kernels, utilities, s.strategy; shared = [[:X1, :X2]])
```

The first-order condition is necessary at an optimum, not sufficient. When every decision has
its own policy, deterministic strategies suffice (Kuhn's theorem, proved in the Lean module
`Kuhn` for open influence diagrams), and `optimize` on the closed composite finds the optimum.
