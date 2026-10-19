"""
Optimisation of open influence diagrams (ADR 0018, decision 4): contextual, never isolated.
The bundle `docs/categorical-extensions-2026-09-12/influence/` refutes "optimise each
component on its own, then compose" (`INF-ISOLATED-OBSTRUCTION`), so this file offers no
such operation. It offers

- [`optimize`](@ref optimize(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict)) on a
  closed composite, which hands the instantiated composite to `InfluenceDiagrams`' solvers;
- [`contextual_value`](@ref) and [`contextual_optimize`](@ref), which value and optimise an
  open component `f : X → Y` against an explicit prior `μ` on the joint input states and an
  explicit continuation `c` on the joint output states (the downstream value function);
- [`continuation_value`](@ref) and [`boundary_law`](@ref), the two contexts a serial
  composite `f ; g` induces: the suffix's value function `c_τ` and the prefix's boundary law
  `ν_σ`. With them the contextual identity of the bundle (`INF-FIXED-CONTEXT`) reads
  `EU_{f;g}(σ, τ; μ, c) = EU_f(σ; μ, c_τ) = L_σ + EU_g(τ; ν_σ, c)`, where `L_σ` is the
  value of `f` with zero continuation;
- with evidence (ADR 0021), contexts that carry the evidence mass: a state
  ([`boundary_state`](@ref)) on the inputs and an effect ([`continuation_effect`](@ref)) on
  the outputs, with [`evidence_mass`](@ref) and [`conditional_value`](@ref), the expected
  utility given the evidence, which [`contextual_optimize`](@ref) maximises.

The strategies searched are deterministic. A behavioural (stochastic) strategy is interpreted
and valued like any other (ADR 0022), but it is never better than the best deterministic one
when every decision has its own policy: `InfluenceDiagrams`' Lean theorem
`exists_deterministic_optimal_all` for expected utility, and this package's
`conditionalValue_mix_le` for the conditional value given evidence. Decisions that share a
name share a policy, and then randomising can help (the absent-minded driver,
`AbsentMinded.randomising_helps`); `contextual_optimize` refuses shared names.
"""

# Closed composites
###################

# The apex of `o` as an `InfluenceDiagramModel` with the tables of `kernels` and `utilities`
# bound, resolved through the apex's references as `interpret` resolves them. The input
# variables of an open `o` have no mechanism and stay without one: they are the model's
# exogenous variables, whose law a `DecisionContext` supplies.
function _bound_model(o::OpenInfluenceDiagram, kernels::AbstractDict,
                      utilities::AbstractDict; atol::Real=DEFAULT_ATOL)
    id = apex(o)
    m = InfluenceDiagramModel(id)
    for mech in mechanisms(id)
        kernel_ref(id, mech) isa PointMassRef && continue
        x = variable_name(id, target(id, mech))
        k = resolve_kernel(id, mech, kernels)
        k === nothing && throw(MissingKernelError(x, kernel_ref(id, mech)))
        m = bind_kernel(m, x => k; atol=atol)
    end
    for u in parts(id, :Utility)
        util = _lookup_utility(id, u, utilities)
        if util === nothing
            ref = subpart(id, u, :utility_ref)
            throw(MissingUtilityError(utility_name(id, u),
                                      ref isa KernelRef ? ref : NoRef()))
        end
        m = bind_utility(m, utility_name(id, u) => util)
    end
    return m
end

# The closed composite `o` as a bound `InfluenceDiagramModel`.
function _closed_model(o::OpenInfluenceDiagram, kernels::AbstractDict,
                       utilities::AbstractDict; atol::Real=DEFAULT_ATOL)
    isempty(inputs(o)) && isempty(outputs(o)) ||
        throw(ArgumentError("optimize: the diagram has inputs $(inputs(o)) and outputs $(outputs(o)); only a closed composite is optimised as a whole (optimise an open component with contextual_optimize, against an explicit prior and continuation)"))
    validate(o)
    return _bound_model(o, kernels, utilities; atol=atol)
end

"""
    optimize(o::OpenInfluenceDiagram, kernels, utilities; evidence = nothing,
             backend = DecisionVariableElimination(), atol = DEFAULT_ATOL, kwargs...) -> DecisionSolution
    optimize(o::OpenInfluenceDiagram, m::InfluenceDiagramModel; kwargs...)

Solve a closed composite (ADR 0018, decision 4): `o` must have no inputs and no outputs,
as `compose(f, g)` of an `f : I → Y` and a `g : Y → I` has. Its apex is instantiated with
the tables of `kernels` and `utilities` (keyed as for
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy)):
by `KernelRef` or target variable name, and by utility name or `utility_ref`), and
`InfluenceDiagrams`' `optimize` solves it with `backend`, a `DecisionBackend`
(`DecisionVariableElimination` or `ExhaustivePolicySearch`). The result is that function's
`DecisionSolution`: the maximal expected utility and a deterministic strategy for every
decision of the composite. The keywords are passed on (`atol`, `max_states`).

An open `o` raises `ArgumentError`: a component with a boundary has no expected utility of
its own until a prior and a continuation are given, which is what
[`contextual_optimize`](@ref) takes. There is deliberately no operation that optimises the
components of a composite one by one and composes the results; that is not sound (the
bundle's `INF-ISOLATED-OBSTRUCTION`).

`evidence` (ADR 0021) is hard evidence on the composite's variables (likelihood evidence
raises `ArgumentError`: an `InfluenceDiagrams` model observes states only, and
[`contextual_optimize`](@ref) takes it), checked as for
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy))
and recorded on the model with `observe`; the solver then maximises the expected utility
given the evidence, with `InfluenceDiagrams`' rules (decision variable elimination needs
evidence without an action among its causal ancestors; `ExhaustivePolicySearch` takes any,
skipping strategies under which it is impossible). The model form reads `kernels(m)`,
`bound_utilities(m)` and the model's evidence, joined with the keyword's. `o` is
validated first. A missing table raises `MissingKernelError` or `MissingUtilityError`;
the solver's own errors pass through, among them `IrregularDiagramError` from decision
variable elimination on a composite without no-forgetting (built with
`no_forgetting = false`; `ExhaustivePolicySearch` solves those) and
`PolicySearchTooLargeError`.
"""
function optimize(o::OpenInfluenceDiagram, kernels::AbstractDict, utilities::AbstractDict;
                  evidence=nothing, backend::DecisionBackend=DecisionVariableElimination(),
                  atol::Real=DEFAULT_ATOL, kw...)
    m = _closed_model(o, kernels, utilities; atol=atol)
    ev = _evidence(o, evidence)
    all(s -> s isa Symbol, values(ev)) ||
        throw(ArgumentError("optimize: likelihood evidence on $(sort!([x for (x, s) in ev if !(s isa Symbol)])) cannot be recorded on an InfluenceDiagrams model, which observes states only; optimise the closed composite with contextual_optimize, which takes it"))
    isempty(ev) || (m = observe(m, sort!([x => s for (x, s) in ev]; by=first)))
    return optimize(m, backend; atol=atol, kw...)
end

function optimize(o::OpenInfluenceDiagram, m::InfluenceDiagramModel; evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return optimize(o, ks, us; evidence=ev, kw...)
end

# Contexts
##########

# The prior over the joint input states of `X`, in `joint_states` order, checked as
# `InfluenceDiagrams`' `DecisionContext` checks a prior: finite, nonnegative entries (no
# tolerance below zero) summing to one within `atol` (`|Σ - 1| <= atol`, the
# kernel-normalisation convention). It is never renormalised.
function _prior_vector(prior, X::FiniteSpace, atol::Real)
    if prior === nothing
        isempty(X) ||
            throw(ArgumentError("the inputs $(axis_names(X)) need an explicit prior on their joint states"))
        return [1.0]
    end
    if prior isa FiniteKernel
        isempty(prior.dom) && prior.codom == X ||
            throw(ArgumentError("a prior kernel must be a state I → $(axis_names(X)), not $(axis_names(prior.dom)) → $(axis_names(prior.codom))"))
        prior = vec(prior.table)
    end
    prior isa AbstractVector{<:Real} ||
        throw(ArgumentError("a prior must be a real vector over the joint input states or a state kernel, not a $(typeof(prior))"))
    length(prior) == length(X) ||
        throw(ArgumentError("the prior has $(length(prior)) entries but the inputs $(axis_names(X)) have $(length(X)) joint states"))
    all(isfinite, prior) ||
        throw(ArgumentError("the prior has an entry that is not finite"))
    all(>=(0), prior) || throw(ArgumentError("the prior has a negative entry"))
    abs(sum(prior) - 1) <= atol ||
        throw(ArgumentError("the prior sums to $(sum(prior)), not to one within atol = $atol"))
    return convert(Vector{Float64}, collect(prior))
end

# The continuation over the joint output states of `Y`, in `joint_states` order, checked.
function _continuation_vector(continuation, Y::FiniteSpace)
    if continuation === nothing
        isempty(Y) ||
            throw(ArgumentError("the outputs $(axis_names(Y)) need an explicit continuation value on their joint states"))
        return [0.0]
    end
    continuation isa AbstractVector{<:Real} ||
        throw(ArgumentError("a continuation must be a real vector over the joint output states or a reward kernel to I, not a $(typeof(continuation))"))
    length(continuation) == length(Y) ||
        throw(ArgumentError("the continuation has $(length(continuation)) entries but the outputs $(axis_names(Y)) have $(length(Y)) joint states"))
    all(isfinite, continuation) ||
        throw(ArgumentError("the continuation has an entry that is not finite"))
    return convert(Vector{Float64}, collect(continuation))
end

# A context on the input side as `(ν, ρ)` (ADR 0021). A prior (a vector or a state kernel)
# gives `(μ, nothing)`: no reward has been earned before it. A state reward kernel `I → X`
# gives its probability row `ν`, the probability of reaching each input state with the
# evidence seen upstream (of mass at most one), and its reward row `ρ`, the reward earned
# upstream on those paths.
function _state_vectors(prior, X::FiniteSpace, atol::Real)
    prior isa RewardKernel || return _prior_vector(prior, X, atol), nothing
    isempty(dom(prior)) && codom(prior) == X ||
        throw(ArgumentError("a prior reward kernel must be a state I → $(axis_names(X)), not $(axis_names(dom(prior))) → $(axis_names(codom(prior))); pass boundary_state(f; prior = μ) for an f with inputs"))
    ν = vec(kernel(prior).table)
    all(isfinite, ν) ||
        throw(ArgumentError("the prior state has a probability entry that is not finite"))
    all(>=(-atol), ν) ||
        throw(ArgumentError("the prior state has a probability entry below -atol = $atol"))
    sum(ν) <= 1 + atol ||
        throw(ArgumentError("the prior state has mass $(sum(ν)), more than one within atol = $atol"))
    return convert(Vector{Float64}, ν), vec(reward(prior))
end

# A context on the output side as `(m, c)` (ADR 0021). A continuation vector gives
# `(nothing, c)`: no evidence is still to come. An effect reward kernel `Y → I` gives its
# probability row `m`, the probability of the evidence downstream from each output state,
# and its reward row `c`, the value downstream on those paths.
function _effect_vectors(continuation, Y::FiniteSpace, atol::Real)
    continuation isa RewardKernel || return nothing, _continuation_vector(continuation, Y)
    dom(continuation) == Y && isempty(codom(continuation)) ||
        throw(ArgumentError("a continuation reward kernel must be $(axis_names(Y)) → I, not $(axis_names(dom(continuation))) → $(axis_names(codom(continuation))); pass continuation_effect(g; continuation = c) for a g with outputs"))
    m = vec(kernel(continuation).table)
    all(isfinite, m) ||
        throw(ArgumentError("the continuation effect has a probability entry that is not finite"))
    all(>=(-atol), m) ||
        throw(ArgumentError("the continuation effect has a probability entry below -atol = $atol"))
    return convert(Vector{Float64}, m), vec(reward(continuation))
end

_colsum(A::AbstractMatrix) = vec(sum(A; dims=1))

# The backward action of `r` on the effect `(m, c)`: `(Kᵀ m, Wᵀ m + Kᵀ c)`, the column sums
# standing for `Kᵀ 1` and `Wᵀ 1` when `m` is `nothing`.
function _pull(r::RewardKernel, m, c::Vector{Float64})
    K, W = kernel_matrix(kernel(r)), reward_matrix(r)
    mp = m === nothing ? _colsum(K) : transpose(K) * m
    cp = (m === nothing ? _colsum(W) : transpose(W) * m) .+ transpose(K) * c
    return mp, cp
end

# The pairing of the state `(ν, ρ)` with the effect `(m, c)` on one space: the evidence mass
# `Σ ν m` and the evidence-weighted value `Σ (ρ m + ν c)`.
_pairing_value(ν, ρ, m, c) = (ρ === nothing ? 0.0 : sum(ρ .* m)) + sum(ν .* c)
_pairing_mass(ν, m) = sum(ν .* m)

# The evidence mass and evidence-weighted value of `r` between a state and an effect.
function _mass_and_value(r::RewardKernel, ν, ρ, m, c)
    mp, cp = _pull(r, m, c)
    return _pairing_mass(ν, mp), _pairing_value(ν, ρ, mp, cp)
end

"""
    contextual_value(r::RewardKernel; prior = nothing, continuation = nothing, atol = DEFAULT_ATOL) -> Float64
    contextual_value(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; prior, continuation, evidence, kwargs...)
    contextual_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ = strategy(m); kwargs...)

The expected utility `EU_f(σ; μ, c)` of an open component `f : X → Y` under the fixed
strategy `σ`, in the context of a prior `μ` on its inputs and a continuation `c` on its
outputs (ADR 0018, decision 4; the bundle's `Score`):

    EU_f(σ; μ, c) = Σ_x μ(x) Σ_y (W(y, x) + K(y | x) c(y)),

where `(K, W)` is the reward kernel of `f` under `σ`. The diagram forms compute it with
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy)),
whose arguments and keywords (`evidence`, `max_states`, `atol`) they take.

- `prior` is a real vector over the joint input states, in `joint_states` order of
  `dom(r)` (the first input varies fastest), with nonnegative entries summing to one
  within `atol` (`|Σ μ - 1| <= atol`, as `InfluenceDiagrams`' `DecisionContext` requires;
  it is never renormalised), or a `FiniteKernel` state `I → dom(r)`. It is the joint law of the hidden
  state and the remembered information at the boundary; no independence is assumed. It may
  be left out only when `f` has no inputs. It may also be a [`RewardKernel`](@ref) state
  `I → dom(r)`, which carries evidence seen upstream ([`boundary_state`](@ref)).
- `continuation` is a real (signed) vector over the joint output states, in `joint_states`
  order of `codom(r)`: the value the rest of the problem earns from each boundary state.
  It may also be a [`RewardKernel`](@ref) effect `codom(r) → I`, such as the
  [`continuation_effect`](@ref) of a suffix or the reward kernel of a closed suffix, which
  also carries the probability of evidence downstream. It may be left out only when `f`
  has no outputs. A zero continuation scores `f`'s own reward only.

With evidence (ADR 0021) anywhere, in `f` (the `evidence` keyword of the diagram forms), in
a state prior or in an effect continuation, the result is the *evidence-weighted* value
`E[U · 1(evidence)]`, with the state `(ν, ρ)` and the effect `(m, c)`:

    Σ_x (ρ(x) m'(x) + ν(x) c'(x)),   m' = Kᵀ m,   c' = Wᵀ m + Kᵀ c,

which composes linearly; [`conditional_value`](@ref) divides it by the
[`evidence_mass`](@ref) `Σ_x ν(x) m'(x)` to give the expected utility given the evidence.
Without evidence the mass is one and the two agree.

A wrong length, a non-finite entry, a negative or unnormalised prior, a state of mass above
one or with a probability entry below `-atol`, or a context left out for a nonempty
interface raises `ArgumentError`. On a closed composite, with both left out, the value is
the expected utility.

For a serial composite the contextual identity holds (the bundle's `INF-FIXED-CONTEXT`,
checked numerically by the test suite):

    contextual_value(f ⋅ g; prior = μ, continuation = c)
      == contextual_value(f; prior = μ, continuation = continuation_value(g; continuation = c))
      == contextual_value(f; prior = μ, continuation = 0)
         + contextual_value(g; prior = boundary_law(f; prior = μ), continuation = c)

With evidence in `g` the first equation needs the effect, which carries `g`'s evidence
mass: `contextual_value(f; prior = μ, continuation = continuation_effect(g; continuation =
c))`; and the second the state, which carries `f`'s: `contextual_value(g; prior =
boundary_state(f; prior = μ), continuation = c)`.
"""
function contextual_value(r::RewardKernel; prior=nothing, continuation=nothing,
                          atol::Real=DEFAULT_ATOL)
    ν, ρ = _state_vectors(prior, dom(r), atol)
    m, c = _effect_vectors(continuation, codom(r), atol)
    mp, cp = _pull(r, m, c)
    return _pairing_value(ν, ρ, mp, cp)
end

function contextual_value(o::OpenInfluenceDiagram, kernels::AbstractDict,
                          utilities::AbstractDict, σ::Strategy; prior=nothing,
                          continuation=nothing, atol::Real=DEFAULT_ATOL, kw...)
    r = interpret(o, kernels, utilities, σ; atol=atol, kw...)
    return contextual_value(r; prior=prior, continuation=continuation, atol=atol)
end

function contextual_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                          σ::Strategy=strategy(m); evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return contextual_value(o, ks, us, σ; evidence=ev, kw...)
end

"""
    continuation_value(r::RewardKernel; continuation = nothing) -> Vector{Float64}
    continuation_value(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; continuation, kwargs...)
    continuation_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ = strategy(m); kwargs...)

The value function `c_τ` of a suffix `g : Y → Z` under the fixed strategy `τ`, over the
joint input states `y` of `g` in `joint_states` order:

    c_τ(y) = Σ_z (W_g(z, y) + K_g(z | y) c(z)),

the expected reward `g` earns from the boundary state `y` plus the continuation `c` (the
argument `continuation`, as in [`contextual_value`](@ref)) of what follows `g`. When `g` is
closed on the right (no outputs) `continuation` may be left out and `c_τ(y)` is the
expected reward of `g` from `y`. It is the continuation to pass to
[`contextual_value`](@ref) or [`contextual_optimize`](@ref) for the prefix `f` of
`f ⋅ g`: `EU_{f;g}(σ, τ; μ, c) = EU_f(σ; μ, c_τ)`.

`c_τ` is the analyst's value function: it may depend on hidden boundary state, but the
policies of `τ` still read only their declared information. The diagram forms interpret
`o` first, with `interpret`'s arguments and keywords.

With evidence in `g` (or a `continuation` effect carrying evidence), `c_τ(y)` is the
evidence-weighted value from `y`, and the prefix's context also needs the probability of
that evidence from each `y`: pass [`continuation_effect`](@ref), which holds both, rather
than this vector (ADR 0021).
"""
function continuation_value(r::RewardKernel; continuation=nothing,
                            atol::Real=DEFAULT_ATOL)
    m, c = _effect_vectors(continuation, codom(r), atol)
    return _pull(r, m, c)[2]
end

function continuation_value(o::OpenInfluenceDiagram, kernels::AbstractDict,
                            utilities::AbstractDict, σ::Strategy; continuation=nothing,
                            atol::Real=DEFAULT_ATOL, kw...)
    return continuation_value(interpret(o, kernels, utilities, σ; atol=atol, kw...);
                              continuation=continuation, atol=atol)
end

function continuation_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                            σ::Strategy=strategy(m); evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return continuation_value(o, ks, us, σ; evidence=ev, kw...)
end

"""
    boundary_law(r::RewardKernel; prior = nothing, atol = DEFAULT_ATOL) -> Vector{Float64}
    boundary_law(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; prior, kwargs...)
    boundary_law(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ = strategy(m); kwargs...)

The law `ν_σ = μ K_f` that a prefix `f : X → Y` under the fixed strategy `σ` induces on its
joint output states, in `joint_states` order: `ν_σ(y) = Σ_x μ(x) K_f(y | x)`, with the
prior `μ` given as in [`contextual_value`](@ref) (left out when `f` has no inputs). It is
the joint law of the hidden state and the remembered information at the boundary, not a
product of marginals. It is the prior to pass to [`contextual_value`](@ref) or
[`contextual_optimize`](@ref) for the suffix `g` of `f ⋅ g`:
`EU_{f;g}(σ, τ; μ, c) = L_σ + EU_g(τ; ν_σ, c)`, where
`L_σ = contextual_value(f; prior = μ, continuation = 0)` is the reward the prefix earns.

With evidence in `f` (or a state `prior` carrying evidence) the law is unnormalised: its
mass is the probability of the evidence so far, and it is not a prior for the suffix. Pass
[`boundary_state`](@ref) instead, or divide by the mass for the posterior law of the
boundary given that evidence (ADR 0021).

The diagram forms interpret `o` first, with `interpret`'s arguments and keywords.
"""
function boundary_law(r::RewardKernel; prior=nothing, atol::Real=DEFAULT_ATOL)
    ν, _ = _state_vectors(prior, dom(r), atol)
    return kernel_matrix(kernel(r)) * ν
end

function boundary_law(o::OpenInfluenceDiagram, kernels::AbstractDict,
                      utilities::AbstractDict, σ::Strategy; prior=nothing,
                      atol::Real=DEFAULT_ATOL, kw...)
    r = interpret(o, kernels, utilities, σ; atol=atol, kw...)
    return boundary_law(r; prior=prior, atol=atol)
end

function boundary_law(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                      σ::Strategy=strategy(m); evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return boundary_law(o, ks, us, σ; evidence=ev, kw...)
end

# Contexts with evidence (ADR 0021)
###################################

"""
    boundary_state(r::RewardKernel; prior = nothing, atol = DEFAULT_ATOL) -> RewardKernel
    boundary_state(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; prior, kwargs...)
    boundary_state(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ = strategy(m); kwargs...)

The forward context that a prefix `f : X → Y` under the fixed strategy `σ` hands its
suffix when there is evidence (ADR 0021): a reward kernel state `I → Y` whose probability
row is the unnormalised boundary law `ν'(y) = Σ_x ν(x) K_f(y | x)`, the probability of
reaching `y` with the evidence seen so far, and whose reward row is
`ρ'(y) = Σ_x (ρ(x) K_f(y | x) + ν(x) W_f(y, x))`, the reward earned so far on those paths.
`prior` is given as in [`contextual_value`](@ref), a plain prior being the state `(μ, 0)`;
a state can be passed on, so a chain is pushed forward one component at a time.

It is the prior to pass to [`contextual_value`](@ref), [`conditional_value`](@ref) or
[`contextual_optimize`](@ref) for the suffix `g` of `f ⋅ g`, which then sees the whole
chain's evidence-weighted value: `contextual_value(g; prior = boundary_state(f; prior = μ),
continuation = c) == contextual_value(f ⋅ g; prior = μ, continuation = c)`, with no
normalisation needed. Its probability row is [`boundary_law`](@ref).

The diagram forms interpret `o` first, with `interpret`'s arguments and keywords
(`evidence` among them).
"""
function boundary_state(r::RewardKernel; prior=nothing, atol::Real=DEFAULT_ATOL)
    ν, ρ = _state_vectors(prior, dom(r), atol)
    K, W = kernel_matrix(kernel(r)), reward_matrix(r)
    νp = K * ν
    ρp = ρ === nothing ? W * ν : K * ρ .+ W * ν
    Y = codom(r)
    return RewardKernel(FiniteKernel(FiniteSpace(), Y, reshape(νp, size(Y)); check=false),
                        reshape(ρp, size(Y)))
end

function boundary_state(o::OpenInfluenceDiagram, kernels::AbstractDict,
                        utilities::AbstractDict, σ::Strategy; prior=nothing,
                        atol::Real=DEFAULT_ATOL, kw...)
    r = interpret(o, kernels, utilities, σ; atol=atol, kw...)
    return boundary_state(r; prior=prior, atol=atol)
end

function boundary_state(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                        σ::Strategy=strategy(m); evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return boundary_state(o, ks, us, σ; evidence=ev, kw...)
end

"""
    continuation_effect(r::RewardKernel; continuation = nothing, atol = DEFAULT_ATOL) -> RewardKernel
    continuation_effect(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; continuation, kwargs...)
    continuation_effect(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ = strategy(m); kwargs...)

The backward context that a suffix `g : Y → Z` under the fixed strategy `τ` hands its
prefix when there is evidence (ADR 0021): a reward kernel effect `Y → I` whose probability
row is `m'(y) = Σ_z K_g(z | y) m(z)`, the probability of the evidence from `y` on, and
whose reward row is `c'(y) = Σ_z (W_g(z, y) m(z) + K_g(z | y) c(z))`, the
evidence-weighted value from `y` on, which is [`continuation_value`](@ref). `continuation`
is given as in [`contextual_value`](@ref), a plain continuation being the effect `(1, c)`;
an effect can be passed on, so a chain is pulled back one component at a time.

It is the continuation to pass to [`contextual_value`](@ref), [`conditional_value`](@ref)
or [`contextual_optimize`](@ref) for the prefix `f` of `f ⋅ g`:
`contextual_value(f; prior = μ, continuation = continuation_effect(g; continuation = c))
== contextual_value(f ⋅ g; prior = μ, continuation = c)`, with no normalisation needed.
Without evidence its probability row is one (within the kernels' tolerance) and it carries
the same information as `continuation_value`. The evidence mass is the same at every cut:
the [`evidence_mass`](@ref) of a state against an effect does not depend on where the
chain is split.

The diagram forms interpret `o` first, with `interpret`'s arguments and keywords
(`evidence` among them).
"""
function continuation_effect(r::RewardKernel; continuation=nothing,
                             atol::Real=DEFAULT_ATOL)
    m, c = _effect_vectors(continuation, codom(r), atol)
    mp, cp = _pull(r, m, c)
    X = dom(r)
    return RewardKernel(FiniteKernel(X, FiniteSpace(), reshape(mp, size(X)); check=false),
                        reshape(cp, size(X)))
end

function continuation_effect(o::OpenInfluenceDiagram, kernels::AbstractDict,
                             utilities::AbstractDict, σ::Strategy; continuation=nothing,
                             atol::Real=DEFAULT_ATOL, kw...)
    r = interpret(o, kernels, utilities, σ; atol=atol, kw...)
    return continuation_effect(r; continuation=continuation, atol=atol)
end

function continuation_effect(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                             σ::Strategy=strategy(m); evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return continuation_effect(o, ks, us, σ; evidence=ev, kw...)
end

"""
    evidence_mass(r::RewardKernel; prior = nothing, continuation = nothing, atol = DEFAULT_ATOL) -> Float64
    evidence_mass(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; prior, continuation, kwargs...)
    evidence_mass(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ = strategy(m); kwargs...)

The probability of the evidence (ADR 0021) of an open component `f : X → Y` under the
fixed strategy `σ`, in the context of `prior` and `continuation` given as in
[`contextual_value`](@ref): `Σ_x ν(x) Σ_y K_f(y | x) m(y)`, with `(ν, ρ)` the state of
the prior and `(m, c)` the effect of the continuation. The evidence counted is that of `f`
itself (the `evidence` keyword of the diagram forms), of a state prior (upstream) and of an
effect continuation (downstream). For a serial composite it is the pairing, at the
boundary, of the prefix's unnormalised boundary law with the suffix's likelihood, and it
is the same at every cut:
`evidence_mass(f ⋅ g; prior = μ, continuation = c) == evidence_mass(f; prior = μ,
continuation = continuation_effect(g; continuation = c)) == evidence_mass(g; prior =
boundary_state(f; prior = μ), continuation = c)`.

It is an unnormalised quantity, returned as computed in binary64, and may be zero or
subnormal; [`conditional_value`](@ref) is the entry point that decides impossibility.
Without evidence it is one, up to the kernels' tolerance.
"""
function evidence_mass(r::RewardKernel; prior=nothing, continuation=nothing,
                       atol::Real=DEFAULT_ATOL)
    ν, _ = _state_vectors(prior, dom(r), atol)
    m, c = _effect_vectors(continuation, codom(r), atol)
    return _pairing_mass(ν, _pull(r, m, c)[1])
end

function evidence_mass(o::OpenInfluenceDiagram, kernels::AbstractDict,
                       utilities::AbstractDict, σ::Strategy; prior=nothing,
                       continuation=nothing, atol::Real=DEFAULT_ATOL, kw...)
    r = interpret(o, kernels, utilities, σ; atol=atol, kw...)
    return evidence_mass(r; prior=prior, continuation=continuation, atol=atol)
end

function evidence_mass(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                       σ::Strategy=strategy(m); evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return evidence_mass(o, ks, us, σ; evidence=ev, kw...)
end

# A binary64 evidence mass decides nothing unless it is finite and at least `floatmin`
# (ADR 0014, decision 2).
_trusted_mass(Z::Float64) = isfinite(Z) && Z >= floatmin(Float64)

# The smallest nonzero magnitude among the entries of `vs` (`Inf` if there is none).
function _min_nonzero(vs...)
    m = Inf
    for v in vs, x in v
        iszero(x) || (m = min(m, abs(x)))
    end
    return m
end

# Whether pairing the state `(ν, ρ)`, the reward kernel `r` and the effect `(m, c)` may form
# a product of nonzero operands below `floatmin`, which ADR 0014's shared trust rule does not
# trust. Every term is a product of one entry of each of the three, so it suffices that the
# smallest nonzero magnitudes, and their partial products, are normal.
function _pairing_underflows(r::RewardKernel, ν, ρ, m, c)
    a = _min_nonzero(ν, ρ === nothing ? () : ρ)
    b = _min_nonzero(kernel(r).table, reward(r))
    e = _min_nonzero(m === nothing ? (1.0,) : m, c)
    return any(<(floatmin(Float64)), (a, b, e, a * b, b * e, a * e, a * b * e))
end

# The conditional value recomputed exactly from the tables `K` and `W` (outputs first, in
# any arithmetic whose entries convert exactly to `Rational{BigInt}`) between the state
# `(ν, ρ)` and the effect `(m, c)`, rounded correctly to binary64 (ADR 0016).
function _exact_conditional(K::AbstractArray, W::AbstractArray, X::FiniteSpace,
                            Y::FiniteSpace, ν, ρ, m, c, ev::AbstractDict)
    Q = Rational{BigInt}
    # `vec` first: broadcasting over a zero-dimensional table would give a scalar.
    Kq = reshape(Q.(vec(K)), length(Y), length(X))
    Wq = reshape(Q.(vec(W)), length(Y), length(X))
    mq = m === nothing ? ones(Q, length(Y)) : Q.(m)
    mp = transpose(Kq) * mq
    cp = transpose(Wq) * mq .+ transpose(Kq) * Q.(c)
    νq = Q.(ν)
    Z = sum(νq .* mp)
    N = (ρ === nothing ? zero(Q) : sum(Q.(ρ) .* mp)) + sum(νq .* cp)
    iszero(Z) && throw(ImpossibleEvidenceError(_hard(ev)))
    Z < 0 &&
        throw(IndeterminatePosteriorError(_hard(ev),
                                          "the evidence mass is negative: a tolerated negative entry gives the evidence a negative probability"))
    return _nearest_binary64(N / Z)
end

"""
    conditional_value(r::RewardKernel; prior = nothing, continuation = nothing, atol = DEFAULT_ATOL) -> Float64
    conditional_value(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; prior, continuation, evidence, max_states, atol)
    conditional_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ = strategy(m); kwargs...)

The expected utility given the evidence (ADR 0021) of an open component `f : X → Y` under
the fixed strategy `σ`, in the context of `prior` and `continuation` given as in
[`contextual_value`](@ref): the evidence-weighted value divided by the
[`evidence_mass`](@ref),

    E[U | evidence] = Σ_x (ρ(x) m'(x) + ν(x) c'(x)) / Σ_x ν(x) m'(x),

with `m' = Kᵀ m` and `c' = Wᵀ m + Kᵀ c`. The evidence is that of `f` (the `evidence`
keyword of the diagram forms, checked as for
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy))),
of a state prior ([`boundary_state`](@ref)) and of an effect continuation
([`continuation_effect`](@ref)). Since the numerator and the mass are both pairings that
are the same at every cut of a chain, the conditional value of a composite is computed at
any boundary from the two contexts there; on a closed composite it is `InfluenceDiagrams`'
`expected_utility` of the model with the evidence observed. Normalising each component on
its own evidence before composing is not sound (the Lean module `Evidence`,
`local_normalisation_obstruction`): the evidence mass has to cross the boundary. Without
evidence the result is [`contextual_value`](@ref).

Evidence mass follows ADR 0014. A binary64 run is trusted when its mass is finite and at
least `floatmin` and none of its products of nonzero operands fell below `floatmin` (the
reward-kernel form checks this conservatively, from the smallest nonzero entries of the
state, the kernel and the effect). Otherwise the value is recomputed exactly in
`Rational{BigInt}` and rounded
correctly: the diagram forms recompute the reward kernel from the tables, so a mass that
only underflowed is resolved, and the reward-kernel form, which has only its tables,
recomputes the pairing from them. A mass that is exactly zero raises
`ImpossibleEvidenceError`. When `f`'s tables hold tolerated negative entries (in
`[-atol, 0)`) and there is evidence, the diagram forms raise `IndeterminatePosteriorError`
if the mass is not larger than the budget `(1 + atol)^n - 1`, `n` the number of variables
with a mechanism or a policy, or if the exact fallback would be needed; a mass that comes
out negative raises it in every form.

The diagram forms take [`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy))'s
arguments and errors; the model form also uses the model's evidence.
"""
function conditional_value(r::RewardKernel; prior=nothing, continuation=nothing,
                           atol::Real=DEFAULT_ATOL)
    ν, ρ = _state_vectors(prior, dom(r), atol)
    m, c = _effect_vectors(continuation, codom(r), atol)
    Z, N = _mass_and_value(r, ν, ρ, m, c)
    _trusted_mass(Z) && !_pairing_underflows(r, ν, ρ, m, c) && return N / Z
    return _exact_conditional(kernel(r).table, reward(r), dom(r), codom(r), ν, ρ, m, c,
                              _Evidence())
end

# The conditional value of the validated `o` under the checked evidence `ev`, between the
# checked state `(ν, ρ)` and effect `(m, c)`, with ADR 0014's rules.
function _conditional_value(o::OpenInfluenceDiagram, kernels::AbstractDict,
                            utilities::AbstractDict, σ::Strategy, ev::AbstractDict,
                            ν, ρ, m, c; max_states::Integer, atol::Real)
    t = _interpret_tables(o, kernels, utilities, σ, ev, identity; max_states=max_states,
                          atol=atol)
    r = RewardKernel(FiniteKernel(t.X, t.Y, t.K; check=false), t.W)
    Z, N = _mass_and_value(r, ν, ρ, m, c)
    track = t.negative && !isempty(ev)
    if track
        budget = _joint_atol(atol, t.nfactors)
        Z <= budget &&
            throw(IndeterminatePosteriorError(_hard(ev),
                                              "the evidence mass $(Z) is within the tolerance budget $(budget) of zero"))
    end
    trusted = _trusted_mass(Z) && !t.underflow && !_pairing_underflows(r, ν, ρ, m, c)
    trusted && return N / Z
    track &&
        throw(IndeterminatePosteriorError(_hard(ev),
                                          "the evidence mass $(Z) or a product forming it is below binary64's normal range, and the exact fallback does not accept tolerated negative entries"))
    q = _interpret_tables(o, kernels, utilities, σ, ev, Rational{BigInt};
                          max_states=max_states, atol=atol)
    return _exact_conditional(q.K, q.W, q.X, q.Y, ν, ρ, m, c, ev)
end

function conditional_value(o::OpenInfluenceDiagram, kernels::AbstractDict,
                           utilities::AbstractDict, σ::Strategy; prior=nothing,
                           continuation=nothing, evidence=nothing,
                           max_states::Integer=DEFAULT_MAX_STATES, atol::Real=DEFAULT_ATOL)
    validate(o)
    ev = _evidence(o, evidence)
    ν, ρ = _state_vectors(prior, _space(o, input_variables(o)), atol)
    m, c = _effect_vectors(continuation, _space(o, output_variables(o)), atol)
    return _conditional_value(o, kernels, utilities, σ, ev, ν, ρ, m, c;
                              max_states=max_states, atol=atol)
end

function conditional_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                           σ::Strategy=strategy(m); evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return conditional_value(o, ks, us, σ; evidence=ev, kw...)
end

# The joint space of the apex variables `vs`, in order.
_space(o::OpenInfluenceDiagram, vs) = FiniteSpace(FiniteAxis[axis(apex(o), v) for v in vs])

# Contextual optimisation
#########################

# Optimisation keys policies, tables and the context by name, so the apex of a component
# to optimise must have unique variable, decision and utility names. `interpret` and
# `contextual_value` work part by part and keep supporting repeated names (equally named
# decisions then share one policy).
function _require_unique_names(id::AbstractInfluenceDiagram)
    repeated(xs) = sort!(unique(x for x in xs if count(==(x), xs) > 1))
    found = [(what, repeated(Symbol[subpart(id, p, attr) for p in parts(id, ob)]))
             for (what, ob, attr) in (("decision", :Decision, :decision_name),
                                      ("variable", :Variable, :variable_name),
                                      ("utility", :Utility, :utility_name))]
    filter!(x -> !isempty(last(x)), found)
    isempty(found) ||
        throw(ArgumentError("contextual_optimize: names must be unique for optimisation, but the diagram repeats the " *
                            join(["$what names $(names_)" for (what, names_) in found],
                                 ", the ") *
                            " (as a diagram tensored with itself does); rename them, or value a fixed strategy with contextual_value"))
    return nothing
end

# A boundary context as `vars => table` for `InfluenceDiagrams`' `DecisionContext`: the
# vector `v` over the joint states of the apex variables `vs`, in `joint_states` order (the
# first variable fastest), reshaped to one axis per position of `vs`. A repeated variable
# repeats its name, as `DecisionContext` reads a repeated terminal variable on the
# diagonal. An empty `vs` gives a 0-dimensional table: the one-entry continuation of a
# component without outputs is a constant, which still counts.
function _boundary_table(id::AbstractInfluenceDiagram, vs::AbstractVector{<:Integer},
                         v::Vector{Float64})
    return Symbol[variable_name(id, x) for x in vs] => reshape(v,
                                                               Tuple(nstates(id, x)
                                                                     for x in vs))
end

"""
    contextual_optimize(o::OpenInfluenceDiagram, kernels, utilities; prior = nothing,
                        continuation = nothing, evidence = nothing,
                        max_policies = 1_000_000, brute_force = false, max_states,
                        atol) -> DecisionSolution
    contextual_optimize(o::OpenInfluenceDiagram, m::InfluenceDiagramModel; kwargs...)

Maximise [`contextual_value`](@ref) over the deterministic strategies of the decisions of
the open component `o : X → Y`, in the explicit context of a prior `μ` on its joint input
states and a continuation `c` on its joint output states, given as for
[`contextual_value`](@ref) (ADR 0018, decision 4). The result is `InfluenceDiagrams`'
`DecisionSolution`: the best value `EU_o(σ*; μ, c)`, a best strategy `σ*` with a
`DeterministicPolicy` for every decision name of `o`, and diagnostics that include
`nstrategies` and `method`.

Only legal strategies are searched: each policy is a function of its decision's declared
information set, which by rule 3 holds internal and *observed* input variables only. A
hidden input is never read, so no strategy can maximise separately at each hidden boundary
state; the bundle shows that doing so changes the problem (`INF-HIDDEN-OBSTRUCTION`).

By default the search is `InfluenceDiagrams`' own: the apex of `o` is bound to the tables
of `kernels` and `utilities` as an `InfluenceDiagramModel` whose input variables keep no
mechanism (they are its exogenous variables), the context becomes a `DecisionContext` with
`μ` as the prior over the input variables and `c` as the terminal utility over the output
variables (a repeated output repeats its name and is read on the diagonal; a pass-through
variable is both), and `optimize(m, ExhaustivePolicySearch(; max_policies); context,
max_states, atol)` solves it. The result and its diagnostics are that function's
(`(nstrategies, method = :value_table)`, with `exact_fallback = true` when its value table
falls back to scoring strategy by strategy). It enumerates the strategies in the order of
`all_deterministic_strategies(apex(o))` (`all_deterministic_policies` for each decision, in
`decision_order`, the first decision fastest) and returns the first one attaining the
maximum. More than `max_policies` strategies raise `PolicySearchTooLargeError`. Decision
variable elimination is never used, since it takes no context.

With `brute_force = true` every strategy, in the same order, is scored by
[`contextual_value`](@ref) through `interpret` instead, an independent path that is slower
and is the oracle the test suite compares with; its diagnostics are
`(nstrategies, method = :brute_force)`.

With evidence (ADR 0021), in `o` (the `evidence` keyword, checked as for
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy)))
or carried by the context (a state `prior` from [`boundary_state`](@ref), an effect
`continuation` from [`continuation_effect`](@ref)), the objective is the
[`conditional_value`](@ref), the expected utility given all of the evidence, as
`InfluenceDiagrams`' `ExhaustivePolicySearch` maximises it on a closed model with
evidence. By default one pass over the apex's joint states, with the decisions left free,
builds value tables: for each joint state of the decisions' information and action
variables, the evidence mass and the evidence-weighted value a strategy selecting it
contributes, the state and the effect folded in as factors on the inputs and outputs. Each
strategy, in the same order, is then scored by summing the cells it selects
(`method = :conditional_value_table`). A strategy whose summed mass is below binary64's
normal range is scored by `conditional_value` instead, with its exact fallback (ADR 0014),
and if the pass computed a product of nonzero operands below `floatmin`, or met a
tolerated negative entry with evidence, every strategy is (`exact_fallback = true`). With
`brute_force = true` every strategy is scored by `conditional_value` through `interpret`
(`method = :conditional`), the independent path the tests compare with. Strategies under
which the evidence has probability exactly zero are skipped, and if every strategy is,
`ImpossibleEvidenceError` is raised. When the evidence lies downstream
of a decision, its probability depends on the strategy, and the conditional value is not
the evidence-weighted value up to a constant. A state prior with zero reward and mass one
within `atol`, or an effect continuation whose probability row is one within `atol`, counts
as a plain prior or continuation.

The context is what makes the result meaningful. With `continuation` the
[`continuation_value`](@ref) of a suffix `g` under `τ`, the optimum is the best prefix
strategy against that suffix; maximising that over `τ` gives the optimum of `o ⋅ g`, and so
does maximising `L_σ + contextual_optimize(g; prior = boundary_law(o, σ))` over `σ`. A
component optimised against a context other than the one its neighbours induce (a zero
continuation, say) can choose a strategy that composes badly: the bundle's Lean witness
composes isolated optima to `1` where the composite attains `4`
(`INF-ISOLATED-OBSTRUCTION`). There is no operation that optimises components one by one
and composes them.

Arguments are checked as for `interpret` and [`contextual_value`](@ref): `o` is validated,
the prior and continuation are checked as there (a prior's entries nonnegative and summing
to one within `atol`, as `DecisionContext` requires), at most `max_states` joint states of
the apex are enumerated (`ModelTooLargeError`), and missing tables raise
`MissingKernelError` or `MissingUtilityError`. The apex's variable, decision and utility
names must be unique, since the search keys policies and tables by name: equally named
decisions (a diagram tensored with itself, say) raise `ArgumentError` on both paths, while
`interpret` and [`contextual_value`](@ref) still accept them. The model form reads
`kernels(m)`, `bound_utilities(m)` and the model's evidence, joined with the keyword's.
"""
function contextual_optimize(o::OpenInfluenceDiagram, kernels::AbstractDict,
                             utilities::AbstractDict; prior=nothing, continuation=nothing,
                             evidence=nothing, max_policies::Integer=1_000_000,
                             brute_force::Bool=false,
                             max_states::Integer=DEFAULT_MAX_STATES,
                             atol::Real=DEFAULT_ATOL)
    validate(o)
    id = apex(o)
    _require_unique_names(id)
    ev = _evidence(o, evidence)
    in_ids, out_ids = input_variables(o), output_variables(o)
    X = FiniteSpace(FiniteAxis[axis(id, v) for v in in_ids])
    Y = FiniteSpace(FiniteAxis[axis(id, v) for v in out_ids])
    ν, ρ = _state_vectors(prior, X, atol)
    m, c = _effect_vectors(continuation, Y, atol)
    # A state with no reward and mass one is a prior, an effect with probability one a
    # continuation: without evidence they take the plain path.
    ρ !== nothing && all(iszero, ρ) && abs(sum(ν) - 1) <= atol && (ρ = nothing)
    m !== nothing && all(x -> abs(x - 1) <= atol, m) && (m = nothing)
    if !isempty(ev) || ρ !== nothing || m !== nothing
        search = brute_force ? _conditional_search : _value_table_search
        return search(o, kernels, utilities, ev, ν, ρ, m, c; max_policies=max_policies,
                      max_states=max_states, atol=atol)
    end
    μ = ν
    if brute_force
        total = n_deterministic_strategies(id)
        total <= max_policies || throw(PolicySearchTooLargeError(total, max_policies))
        best, best_strategy = -Inf, Strategy()
        for σ in all_deterministic_strategies(id)
            v = contextual_value(o, kernels, utilities, σ; prior=μ, continuation=c,
                                 max_states=max_states, atol=atol)
            v > best && ((best, best_strategy) = (v, σ))
        end
        return DecisionSolution(best, best_strategy,
                                (nstrategies=Int(total), method=:brute_force))
    end
    m = _bound_model(o, kernels, utilities; atol=atol)
    # Without inputs there are no exogenous variables, so no prior (the one-entry `μ` is
    # one within `atol`); a zero continuation adds nothing, so it is left out, and a closed
    # composite is solved exactly as `optimize` solves it.
    context = DecisionContext(;
                              prior=isempty(in_ids) ? nothing :
                                    _boundary_table(id, in_ids, μ),
                              terminal=all(iszero, c) ? nothing :
                                       _boundary_table(id, out_ids, c))
    return optimize(m, ExhaustivePolicySearch(; max_policies=max_policies); context=context,
                    max_states=max_states, atol=atol)
end

function contextual_optimize(o::OpenInfluenceDiagram, m::InfluenceDiagramModel;
                             evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return contextual_optimize(o, ks, us; evidence=ev, kw...)
end

# The value tables of the validated `o` under the checked evidence `ev`, between the checked
# state `(ν, ρ)` and effect `(m, c)` (`nothing` for no reward upstream and mass one
# downstream), for the conditional search (ADR 0021): one pass over the apex's joint states
# with the decisions left free, accumulating into the joint state of the decisions'
# information and action variables (`keep`, each once) the evidence mass `Z` and the
# evidence-weighted value `N` of every apex state. Also whether a product of nonzero operands
# fell below `floatmin` (`underflow`) and whether a mechanism table has a negative entry.
function _conditional_tables(o::OpenInfluenceDiagram, kernels::AbstractDict,
                             utilities::AbstractDict, ev::AbstractDict, ν, ρ, m, c;
                             max_states::Integer, atol::Real)
    id = apex(o)
    in_ids, out_ids = input_variables(o), output_variables(o)
    ids = collect(parts(id, :Variable))
    n = prod(BigInt[nstates(id, v) for v in ids]; init=big(1))
    n <= max_states || throw(ModelTooLargeError(Int(min(n, typemax(Int))), max_states))
    pos = Dict{Int,Int}(v => i for (i, v) in enumerate(ids))
    dims = Tuple(nstates(id, v) for v in ids)
    factors = _factors(id, kernels, pos; atol=atol)
    negative = any(f -> any(<(0), f.table), factors)
    for v in ids
        s = get(ev, variable_name(id, v), nothing)
        s === nothing && continue
        push!(factors, _Factor(_evidence_table(id, v, s), Int[pos[v]]))
    end
    us = _utility_factors(id, utilities, pos)
    keep = Int[]
    for d in parts(id, :Decision), v in vcat(decision_information(id, d),
                                             decision_variable(id, d))
        v in keep || push!(keep, v)
    end
    Z = zeros(Float64, Tuple(nstates(id, v) for v in keep))
    N = zeros(Float64, size(Z))
    in_lin = LinearIndices(Tuple(nstates(id, v) for v in in_ids))
    out_lin = LinearIndices(Tuple(nstates(id, v) for v in out_ids))
    underflow = false
    # A product of nonzero operands below `floatmin` is not trusted (ADR 0014).
    function mul(a, b)
        r = a * b
        !iszero(a) && !iszero(b) && (iszero(r) || abs(r) < floatmin(Float64)) &&
            (underflow = true)
        return r
    end
    for ci in CartesianIndices(dims)
        p = _product(factors, ci)
        if p == 0
            underflow |= all(f -> !iszero(_value(f, ci)), factors)
            continue
        end
        underflow |= abs(p) < floatmin(Float64)
        x = in_lin[ntuple(j -> ci[pos[in_ids[j]]], length(in_ids))...]
        y = out_lin[ntuple(j -> ci[pos[out_ids[j]]], length(out_ids))...]
        u = 0.0
        for f in us
            u += _value(f, ci)
        end
        my = m === nothing ? 1.0 : m[y]
        pν = mul(p, ν[x])
        k = ntuple(j -> ci[pos[keep[j]]], length(keep))
        Z[k...] += mul(pν, my)
        N[k...] += (ρ === nothing ? 0.0 : mul(mul(p, ρ[x]), my)) +
                   mul(pν, mul(u, my) + c[y])
    end
    return (Z=Z, N=N, keep=keep, underflow=underflow, negative=negative)
end

# The conditional search by value tables (ADR 0021): each strategy, in the order of
# `all_deterministic_strategies`, scored by the cells of `_conditional_tables` it selects.
function _value_table_search(o::OpenInfluenceDiagram, kernels::AbstractDict,
                             utilities::AbstractDict, ev::AbstractDict, ν, ρ, m, c;
                             max_policies::Integer, max_states::Integer, atol::Real)
    id = apex(o)
    total = n_deterministic_strategies(id)
    total <= max_policies || throw(PolicySearchTooLargeError(total, max_policies))
    t = _conditional_tables(o, kernels, utilities, ev, ν, ρ, m, c; max_states=max_states,
                            atol=atol)
    if t.underflow || (t.negative && !isempty(ev))
        sol = _conditional_search(o, kernels, utilities, ev, ν, ρ, m, c;
                                  max_policies=max_policies, max_states=max_states,
                                  atol=atol)
        return DecisionSolution(sol.expected_utility, sol.strategy,
                                merge(sol.diagnostics, (exact_fallback=true,)))
    end
    kpos = Dict{Int,Int}(v => i for (i, v) in enumerate(t.keep))
    decisions = collect(parts(id, :Decision))
    info_pos = [Int[kpos[v] for v in decision_information(id, d)] for d in decisions]
    act_pos = [kpos[decision_variable(id, d)] for d in decisions]
    act_index = [Dict(l => i for (i, l) in enumerate(axis(id, decision_variable(id, d)).labels))
                 for d in decisions]
    best, best_strategy = -Inf, nothing
    for σ in all_deterministic_strategies(id)
        tabs = [map(a -> act_index[i][a], policy_table(σ[decision_name(id, d)]))
                for (i, d) in enumerate(decisions)]
        Zs = Ns = 0.0
        for k in CartesianIndices(t.Z)
            ok = true
            for i in eachindex(decisions)
                if tabs[i][ntuple(j -> k[info_pos[i][j]], length(info_pos[i]))...] !=
                   k[act_pos[i]]
                    ok = false
                    break
                end
            end
            ok || continue
            Zs += t.Z[k]
            Ns += t.N[k]
        end
        iszero(Zs) && continue
        v = _trusted_mass(Zs) ? Ns / Zs :
            try
                _conditional_value(o, kernels, utilities, σ, ev, ν, ρ, m, c;
                                   max_states=max_states, atol=atol)
            catch e
                e isa ImpossibleEvidenceError || rethrow()
                continue
            end
        if best_strategy === nothing || v > best
            best, best_strategy = v, σ
        end
    end
    best_strategy === nothing && throw(ImpossibleEvidenceError(_hard(ev)))
    return DecisionSolution(best, best_strategy,
                            (nstrategies=Int(total), method=:conditional_value_table))
end

# The strategy of the validated `o` with the best conditional value between the checked
# state `(ν, ρ)` and effect `(m, c)`, under the checked evidence `ev`: each strategy in the
# order of `all_deterministic_strategies`, the first maximum, strategies of exactly zero
# evidence mass skipped (ADR 0021).
function _conditional_search(o::OpenInfluenceDiagram, kernels::AbstractDict,
                             utilities::AbstractDict, ev::AbstractDict, ν, ρ, m, c;
                             max_policies::Integer, max_states::Integer, atol::Real)
    id = apex(o)
    total = n_deterministic_strategies(id)
    total <= max_policies || throw(PolicySearchTooLargeError(total, max_policies))
    best, best_strategy = -Inf, nothing
    for σ in all_deterministic_strategies(id)
        v = try
            _conditional_value(o, kernels, utilities, σ, ev, ν, ρ, m, c;
                               max_states=max_states, atol=atol)
        catch e
            e isa ImpossibleEvidenceError || rethrow()
            continue
        end
        if best_strategy === nothing || v > best
            best, best_strategy = v, σ
        end
    end
    best_strategy === nothing && throw(ImpossibleEvidenceError(_hard(ev)))
    return DecisionSolution(best, best_strategy,
                            (nstrategies=Int(total), method=:conditional))
end
