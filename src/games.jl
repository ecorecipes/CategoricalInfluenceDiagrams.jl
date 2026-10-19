"""
Lenses and open-game equilibria for chains of open influence diagrams (ADR 0020).

A reward kernel `f : X → Y` is a lens: forward it carries a prior `μ` on `X` to the boundary
law `ν = μ K` on `Y` ([`boundary_law`](@ref)); backward it carries a continuation `c` on `Y`
to the value function on `X` ([`continuation_value`](@ref)). Along a chain
`f₁ ⋅ f₂ ⋅ … ⋅ fₙ` under a strategy `σ`, the forward pass gives each component the law on its
inputs and the backward pass the value of its outputs: the context `(μᵢ, cᵢ)` in which the
contextual identity makes `fᵢ`'s value the value of the whole chain, up to terms that `fᵢ`'s
strategy does not change.

A strategy of the chain is an *equilibrium* (in the sense of open games) when every
component's part of it is a best response in that component's context. This is weaker than
optimality: a global optimum is an equilibrium, but an equilibrium can be worth less (the Lean
module `Lens` proves both). It is the solution concept that composes. This file provides
[`component_contexts`](@ref), [`regrets`](@ref), [`is_equilibrium`](@ref) and
[`best_response_dynamics`](@ref); `optimize` on the closed composite remains the way to find
the optimum.

With evidence (ADR 0021) the lens passes carry the evidence mass: forward, states
([`boundary_state`](@ref)); backward, effects ([`continuation_effect`](@ref)). Each
component's context then gives exactly the whole chain's evidence mass and
evidence-weighted value, and its conditional value is the chain's expected utility given
all of the evidence ([`conditional_value`](@ref)), which every component maximises.
"""

# The components' decision names, checked to be owned by one component each.
function _component_decisions(components::AbstractVector{<:OpenInfluenceDiagram})
    names = [unique(decision_names(apex(o))) for o in components]
    seen = Dict{Symbol,Int}()
    for (i, ds) in enumerate(names), d in ds
        haskey(seen, d) &&
            throw(ArgumentError("decision :$d is in components $(seen[d]) and $i; each decision must belong to one component of the chain"))
        seen[d] = i
    end
    return names
end

# The composite of the chain, by `compose` (which validates, and checks rule 6 unless
# `no_forgetting = false`).
function _chain_composite(components::AbstractVector{<:OpenInfluenceDiagram},
                          no_forgetting::Bool)
    isempty(components) && throw(ArgumentError("the chain has no components"))
    return foldl((f, g) -> compose(f, g; no_forgetting=no_forgetting), components)
end

# The chain checked: nonempty, composable, decisions owned once.
function _check_chain(components::AbstractVector{<:OpenInfluenceDiagram},
                      no_forgetting::Bool)
    _chain_composite(components, no_forgetting)
    return _component_decisions(components)
end

# The policies of `σ` for the decision names `ds`; a missing one is left to `interpret`.
function _restrict(σ::Strategy, ds::AbstractVector{Symbol})
    return Strategy(Dict{Symbol,AbstractPolicy}(d => σ[d] for d in ds if haskey(σ, d)))
end

# The evidence of a chain split by component: the part of `ev` on each component's apex.
# Evidence on a shared boundary variable goes to both sides, which changes nothing, since an
# indicator is idempotent. A name on no component raises `UnknownVariableError`.
function _component_evidence(components::AbstractVector{<:OpenInfluenceDiagram}, evidence)
    evidence === nothing && return [nothing for _ in components]
    ev = _evidence(_chain_composite(components, false), evidence)
    return [Dict{Symbol,Symbol}(x => s for (x, s) in ev if has_variable(apex(o), x))
            for o in components]
end

# Whether the chain is valued given evidence: evidence in a component or a context that
# carries evidence mass (a state prior or an effect continuation).
_conditional_mode(evidence, prior, continuation) = (evidence !== nothing &&
                                                    !isempty(evidence)) ||
                                                   prior isa RewardKernel ||
                                                   continuation isa RewardKernel

# A prior or state on `X` as a state reward kernel `I → X`, an effect or continuation on `Y`
# as an effect reward kernel `Y → I`.
function _as_state(prior, X::FiniteSpace, atol::Real)
    ν, ρ = _state_vectors(prior, X, atol)
    return RewardKernel(FiniteKernel(FiniteSpace(), X, reshape(ν, size(X)); check=false),
                        reshape(ρ === nothing ? zeros(length(ν)) : ρ, size(X)))
end
function _as_effect(continuation, Y::FiniteSpace, atol::Real)
    m, c = _effect_vectors(continuation, Y, atol)
    return RewardKernel(FiniteKernel(Y, FiniteSpace(),
                                     reshape(m === nothing ? ones(length(c)) : m, size(Y));
                                     check=false), reshape(c, size(Y)))
end

# The contexts of the reward kernels `rs` of a chain given evidence: the forward pass of
# states and the backward pass of effects.
function _chain_states_effects(rs::AbstractVector{<:RewardKernel}, prior, continuation,
                               atol::Real)
    n = length(rs)
    ss = Vector{RewardKernel}(undef, n)
    es = Vector{RewardKernel}(undef, n)
    ss[1] = _as_state(prior, dom(rs[1]), atol)
    for i in 1:(n - 1)
        ss[i + 1] = boundary_state(rs[i]; prior=ss[i], atol=atol)
    end
    es[n] = _as_effect(continuation, codom(rs[n]), atol)
    for i in n:-1:2
        es[i - 1] = continuation_effect(rs[i]; continuation=es[i], atol=atol)
    end
    return [(prior=ss[i], continuation=es[i]) for i in 1:n]
end

# The contexts of the reward kernels `rs` of a chain: the forward pass of boundary laws and
# the backward pass of value functions; given evidence, of states and effects.
function _chain_contexts(rs::AbstractVector{<:RewardKernel}, prior, continuation, atol::Real;
                         conditional::Bool=false)
    conditional && return _chain_states_effects(rs, prior, continuation, atol)
    n = length(rs)
    μs = Vector{Vector{Float64}}(undef, n)
    cs = Vector{Vector{Float64}}(undef, n)
    μs[1] = _prior_vector(prior, dom(rs[1]), atol)
    for i in 1:(n - 1)
        μs[i + 1] = boundary_law(rs[i]; prior=μs[i], atol=atol)
    end
    cs[n] = _continuation_vector(continuation, codom(rs[n]))
    for i in n:-1:2
        cs[i - 1] = continuation_value(rs[i]; continuation=cs[i])
    end
    return [(prior=μs[i], continuation=cs[i]) for i in 1:n]
end

"""
    component_contexts(components, kernels, utilities, σ::Strategy; prior = nothing,
                       continuation = nothing, evidence = nothing, no_forgetting = true,
                       max_states, atol) -> Vector{NamedTuple}

The context `(prior = μᵢ, continuation = cᵢ)` of each component of the chain
`components[1] ⋅ components[2] ⋅ … ⋅ components[n]` under the strategy `σ` of the whole chain
(ADR 0020). `prior` and `continuation` are the chain's own context, given as for
[`contextual_value`](@ref) on the composite; they may be left out for an empty interface.

The contexts are the lens passes: `μ₁` is the chain's prior and `μᵢ₊₁` the
[`boundary_law`](@ref) of component `i` from `μᵢ`; `cₙ` is the chain's continuation and
`cᵢ₋₁` the [`continuation_value`](@ref) of component `i` from `cᵢ`. Each `μᵢ` is a vector
over the joint input states of component `i` and each `cᵢ` over its joint output states, in
`joint_states` order; an empty interface has one joint state. By the contextual identity,
`contextual_value(components[i], …, σ; prior = μᵢ, continuation = cᵢ)` differs from the
value of the whole chain by the reward of the components before `i`, which `i`'s strategy
does not change.

The chain must compose (each component's outputs match the next one's inputs, as for
[`compose`](@ref), which checks rule 6 unless `no_forgetting = false`, the option for a
limited-memory chain) and each decision name must belong to one component (`ArgumentError`
otherwise). `σ` is restricted to each component's decisions and interpreted with
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy)),
whose keywords and errors apply.

With `evidence` (ADR 0021: hard evidence on variables of the chain, split among the
components whose apex has them, so evidence on a shared boundary variable goes to both
sides), or with a chain context that carries evidence (a [`RewardKernel`](@ref) state
`prior` or effect `continuation`), the contexts are reward kernels: `μᵢ` the state
`I → inputs` of [`boundary_state`](@ref), which carries the evidence and the reward
upstream, and `cᵢ` the effect `outputs → I` of [`continuation_effect`](@ref), which
carries the evidence and the value downstream. Then
`conditional_value(components[i], …, σ; prior = μᵢ, continuation = cᵢ, evidence = eᵢ)` is
exactly the whole chain's expected utility given all of the evidence, for every `i`. A
variable of the evidence on no component raises `UnknownVariableError`.
"""
function component_contexts(components::AbstractVector{<:OpenInfluenceDiagram},
                            kernels::AbstractDict, utilities::AbstractDict, σ::Strategy;
                            prior=nothing, continuation=nothing, evidence=nothing,
                            no_forgetting::Bool=true, atol::Real=DEFAULT_ATOL, kw...)
    names = _check_chain(components, no_forgetting)
    evs = _component_evidence(components, evidence)
    rs = [interpret(o, kernels, utilities, _restrict(σ, ds); evidence=e, atol=atol, kw...)
          for (o, ds, e) in zip(components, names, evs)]
    return _chain_contexts(rs, prior, continuation, atol;
                           conditional=_conditional_mode(evidence, prior, continuation))
end

"""
    regrets(components, kernels, utilities, σ::Strategy; prior = nothing,
            continuation = nothing, evidence = nothing, no_forgetting = true,
            max_policies = 1_000_000, max_states, atol) -> Vector{Float64}

For each component of the chain, how much more it could earn in its context
([`component_contexts`](@ref)) by changing its own part of `σ` alone: the optimum of
[`contextual_optimize`](@ref) in that context minus the component's
[`contextual_value`](@ref) there. Each regret is the gain in the value of the whole chain
from that unilateral change, by the contextual identity, and is zero (up to rounding) for
every component exactly when `σ` is an equilibrium. A component without decisions has
regret zero.

The search for each component is `contextual_optimize`'s, with its `max_policies` limit and
its `PolicySearchTooLargeError`; the other keywords and errors are those of
[`component_contexts`](@ref).

Given evidence (`evidence`, or a chain context that carries it), values are conditional
values ([`conditional_value`](@ref)), the expected utility given all of the evidence, and
each regret is the gain in the whole chain's conditional value from the component's
unilateral change. A strategy under which the evidence is impossible has no conditional
value (`ImpossibleEvidenceError`).
"""
function regrets(components::AbstractVector{<:OpenInfluenceDiagram}, kernels::AbstractDict,
                 utilities::AbstractDict, σ::Strategy; prior=nothing, continuation=nothing,
                 evidence=nothing, no_forgetting::Bool=true,
                 max_policies::Integer=1_000_000, atol::Real=DEFAULT_ATOL,
                 max_states::Integer=DEFAULT_MAX_STATES)
    names = _check_chain(components, no_forgetting)
    evs = _component_evidence(components, evidence)
    conditional = _conditional_mode(evidence, prior, continuation)
    rs = [interpret(o, kernels, utilities, _restrict(σ, ds); evidence=e, atol=atol,
                    max_states=max_states)
          for (o, ds, e) in zip(components, names, evs)]
    ctx = _chain_contexts(rs, prior, continuation, atol; conditional=conditional)
    return [isempty(names[i]) ? 0.0 :
            _best_response(components[i], kernels, utilities, ctx[i], evs[i];
                           max_policies=max_policies, atol=atol,
                           max_states=max_states).expected_utility -
            _context_value(rs[i], ctx[i], conditional, atol)
            for i in eachindex(components)]
end

# A component's value in its context: the conditional value given evidence, the
# contextual value otherwise.
function _context_value(r::RewardKernel, ctx, conditional::Bool, atol::Real)
    f = conditional ? conditional_value : contextual_value
    return f(r; prior=ctx.prior, continuation=ctx.continuation, atol=atol)
end

function _best_response(o::OpenInfluenceDiagram, kernels::AbstractDict,
                        utilities::AbstractDict, ctx, ev; kw...)
    return contextual_optimize(o, kernels, utilities; prior=ctx.prior,
                               continuation=ctx.continuation, evidence=ev, kw...)
end

"""
    is_equilibrium(components, kernels, utilities, σ::Strategy; tol = 1e-9, kwargs...) -> Bool

Whether `σ` is an equilibrium of the chain (ADR 0020): every component's part of `σ` is a
best response in its context, that is every one of [`regrets`](@ref) is at most `tol`. The
other keywords are those of `regrets`.

An equilibrium need not be optimal: two components can each be best responding to the other
while a joint change would do better. The global optimum of the closed composite, from
`optimize`, is always an equilibrium.
"""
function is_equilibrium(components::AbstractVector{<:OpenInfluenceDiagram},
                        kernels::AbstractDict, utilities::AbstractDict, σ::Strategy;
                        tol::Real=1e-9, kw...)
    tol >= 0 || throw(ArgumentError("tol must be nonnegative, got $tol"))
    return all(<=(tol), regrets(components, kernels, utilities, σ; kw...))
end

"""
    best_response_dynamics(components, kernels, utilities, σ::Strategy; prior = nothing,
                           continuation = nothing, evidence = nothing,
                           no_forgetting = true, tol = 1e-9, max_rounds = 100,
                           max_policies = 1_000_000, max_states, atol) -> NamedTuple

Starting from the strategy `σ` of the whole chain, visit the components in order, replacing
a component's part of the strategy by a best response in its current context
([`contextual_optimize`](@ref)) whenever that raises the component's value by more than
`tol`, and repeat until a full round changes nothing. The result is an equilibrium
([`is_equilibrium`](@ref)), and the value of the whole chain never decreases, so the
procedure ends; `max_rounds` bounds the rounds (`converged = false` when it is reached).

It returns `(strategy, value, rounds, converged, values, changed)`: the final strategy, the
chain's value under it ([`contextual_value`](@ref) of the composite in the chain's context),
the number of rounds, whether the last round changed nothing, the chain's value before the
first and after every change, and the index of the component changed at each change.

This is single policy updating at the level of components (Lauritzen and Nilsson's local
optimisation for limited-memory influence diagrams). It finds an equilibrium, which can be
worse than the optimum; which one depends on `σ` and on the order of the components. To find
the optimum, use `optimize` on the closed composite.

Given evidence (`evidence`, or a chain context that carries it), every value is the
conditional value of the whole chain given all of the evidence
([`conditional_value`](@ref)), which each best response maximises and which therefore never
decreases.
"""
function best_response_dynamics(components::AbstractVector{<:OpenInfluenceDiagram},
                                kernels::AbstractDict, utilities::AbstractDict, σ::Strategy;
                                prior=nothing, continuation=nothing, evidence=nothing,
                                no_forgetting::Bool=true, tol::Real=1e-9,
                                max_rounds::Integer=100, max_policies::Integer=1_000_000,
                                atol::Real=DEFAULT_ATOL,
                                max_states::Integer=DEFAULT_MAX_STATES)
    tol >= 0 || throw(ArgumentError("tol must be nonnegative, got $tol"))
    max_rounds >= 1 || throw(ArgumentError("max_rounds must be positive, got $max_rounds"))
    names = _check_chain(components, no_forgetting)
    whole = _chain_composite(components, no_forgetting)
    evs = _component_evidence(components, evidence)
    conditional = _conditional_mode(evidence, prior, continuation)
    value(σ) = (conditional ? conditional_value : contextual_value)(whole, kernels, utilities,
                                                                    σ; prior=prior,
                                                                    continuation=continuation,
                                                                    evidence=evidence,
                                                                    atol=atol,
                                                                    max_states=max_states)
    interpret_all(σ) = [interpret(o, kernels, utilities, _restrict(σ, ds); evidence=e,
                                  atol=atol, max_states=max_states)
                        for (o, ds, e) in zip(components, names, evs)]
    values = [value(σ)]
    changed = Int[]
    rounds, converged = 0, false
    while rounds < max_rounds
        rounds += 1
        any_change = false
        for i in eachindex(components)
            isempty(names[i]) && continue
            rs = interpret_all(σ)
            ctx = _chain_contexts(rs, prior, continuation, atol; conditional=conditional)[i]
            current = _context_value(rs[i], ctx, conditional, atol)
            best = _best_response(components[i], kernels, utilities, ctx, evs[i];
                                  max_policies=max_policies, atol=atol, max_states=max_states)
            best.expected_utility > current + tol || continue
            others = [d for d in keys(σ) if !(d in names[i])]
            σ = merge_strategies(_restrict(σ, others), _restrict(best.strategy, names[i]))
            push!(values, value(σ))
            push!(changed, i)
            any_change = true
        end
        if !any_change
            converged = true
            break
        end
    end
    return (strategy=σ, value=last(values), rounds=rounds, converged=converged,
            values=values, changed=changed)
end
