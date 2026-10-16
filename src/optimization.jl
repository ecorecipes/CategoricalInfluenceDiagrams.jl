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
  value of `f` with zero continuation.

Strategies are deterministic, as in the semantics: ADR 0018 keeps behavioural policies out of
the first release.
"""

# Closed composites
###################

# The tables of a model, refusing evidence (outside ADR 0018's first release).
function _model_tables(m::InfluenceDiagramModel, f::AbstractString)
    isempty(evidence(m)) ||
        throw(ArgumentError("$f: the model has evidence on $(sort!(collect(keys(evidence(m))))); evidence composition is outside ADR 0018's first release"))
    return kernels(m), bound_utilities(m)
end

# The closed composite `o` as an `InfluenceDiagramModel` with the tables of `kernels` and
# `utilities` bound, resolved through the apex's references as `interpret` resolves them.
function _closed_model(o::OpenInfluenceDiagram, kernels::AbstractDict,
                       utilities::AbstractDict; atol::Real=DEFAULT_ATOL)
    isempty(inputs(o)) && isempty(outputs(o)) ||
        throw(ArgumentError("optimize: the diagram has inputs $(inputs(o)) and outputs $(outputs(o)); only a closed composite is optimised as a whole (optimise an open component with contextual_optimize, against an explicit prior and continuation)"))
    validate(o)
    id = apex(o)
    m = InfluenceDiagramModel(id)
    for mech in mechanisms(id)
        kernel_ref(id, mech) isa PointMassRef && continue
        x = variable_name(id, target(id, mech))
        k = _resolve_kernel(id, mech, kernels)
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

"""
    optimize(o::OpenInfluenceDiagram, kernels, utilities;
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

The model form reads `kernels(m)` and `bound_utilities(m)`; a model with evidence raises
`ArgumentError` (evidence composition is outside ADR 0018's first release). `o` is
validated first. A missing table raises `MissingKernelError` or `MissingUtilityError`;
the solver's own errors pass through, among them `IrregularDiagramError` from decision
variable elimination on a composite without no-forgetting (built with
`no_forgetting = false`; `ExhaustivePolicySearch` solves those) and
`PolicySearchTooLargeError`.
"""
function optimize(o::OpenInfluenceDiagram, kernels::AbstractDict, utilities::AbstractDict;
                  backend::DecisionBackend=DecisionVariableElimination(),
                  atol::Real=DEFAULT_ATOL, kw...)
    return optimize(_closed_model(o, kernels, utilities; atol=atol), backend; atol=atol,
                    kw...)
end

function optimize(o::OpenInfluenceDiagram, m::InfluenceDiagramModel; kw...)
    ks, us = _model_tables(m, "optimize")
    return optimize(o, ks, us; kw...)
end

# Contexts
##########

# The prior over the joint input states of `X`, in `joint_states` order, checked.
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
    all(>=(-atol), prior) || throw(ArgumentError("the prior has a negative entry"))
    abs(sum(prior) - 1) <= atol * length(prior) ||
        throw(ArgumentError("the prior sums to $(sum(prior)), not one"))
    return convert(Vector{Float64}, collect(prior))
end

# The continuation over the joint output states of `Y`, in `joint_states` order, checked.
function _continuation_vector(continuation, Y::FiniteSpace)
    if continuation === nothing
        isempty(Y) ||
            throw(ArgumentError("the outputs $(axis_names(Y)) need an explicit continuation value on their joint states"))
        return [0.0]
    end
    if continuation isa RewardKernel
        dom(continuation) == Y && isempty(codom(continuation)) ||
            throw(ArgumentError("a continuation reward kernel must be $(axis_names(Y)) → I, not $(axis_names(dom(continuation))) → $(axis_names(codom(continuation))); pass continuation_value(g; continuation = c) for a g with outputs"))
        return vec(reward_matrix(continuation))
    end
    continuation isa AbstractVector{<:Real} ||
        throw(ArgumentError("a continuation must be a real vector over the joint output states or a reward kernel to I, not a $(typeof(continuation))"))
    length(continuation) == length(Y) ||
        throw(ArgumentError("the continuation has $(length(continuation)) entries but the outputs $(axis_names(Y)) have $(length(Y)) joint states"))
    all(isfinite, continuation) ||
        throw(ArgumentError("the continuation has an entry that is not finite"))
    return convert(Vector{Float64}, collect(continuation))
end

"""
    contextual_value(r::RewardKernel; prior = nothing, continuation = nothing, atol = DEFAULT_ATOL) -> Float64
    contextual_value(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; prior, continuation, kwargs...)
    contextual_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ = strategy(m); kwargs...)

The expected utility `EU_f(σ; μ, c)` of an open component `f : X → Y` under the fixed
strategy `σ`, in the context of a prior `μ` on its inputs and a continuation `c` on its
outputs (ADR 0018, decision 4; the bundle's `Score`):

    EU_f(σ; μ, c) = Σ_x μ(x) Σ_y (W(y, x) + K(y | x) c(y)),

where `(K, W)` is the reward kernel of `f` under `σ`. The diagram forms compute it with
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy)),
whose arguments and keywords (`max_states`, `atol`) they take.

- `prior` is a real vector over the joint input states, in `joint_states` order of
  `dom(r)` (the first input varies fastest), nonnegative and summing to one (within `atol`
  per entry), or a `FiniteKernel` state `I → dom(r)`. It is the joint law of the hidden
  state and the remembered information at the boundary; no independence is assumed. It may
  be left out only when `f` has no inputs.
- `continuation` is a real (signed) vector over the joint output states, in `joint_states`
  order of `codom(r)`: the value the rest of the problem earns from each boundary state.
  It may also be a [`RewardKernel`](@ref) `codom(r) → I`, whose reward row is the
  continuation (the [`continuation_value`](@ref) of a closed suffix). It may be left out
  only when `f` has no outputs. A zero continuation scores `f`'s own reward only.

A wrong length, a non-finite entry, a negative or unnormalised prior, or a context left out
for a nonempty interface raises `ArgumentError`. On a closed composite, with both left
out, the value is the expected utility.

For a serial composite the contextual identity holds (the bundle's `INF-FIXED-CONTEXT`,
checked numerically by the test suite):

    contextual_value(f ⋅ g; prior = μ, continuation = c)
      == contextual_value(f; prior = μ, continuation = continuation_value(g; continuation = c))
      == contextual_value(f; prior = μ, continuation = 0)
         + contextual_value(g; prior = boundary_law(f; prior = μ), continuation = c)
"""
function contextual_value(r::RewardKernel; prior=nothing, continuation=nothing,
                          atol::Real=DEFAULT_ATOL)
    μ = _prior_vector(prior, dom(r), atol)
    return sum(μ .* continuation_value(r; continuation=continuation))
end

function contextual_value(o::OpenInfluenceDiagram, kernels::AbstractDict,
                          utilities::AbstractDict, σ::Strategy; prior=nothing,
                          continuation=nothing, atol::Real=DEFAULT_ATOL, kw...)
    r = interpret(o, kernels, utilities, σ; atol=atol, kw...)
    return contextual_value(r; prior=prior, continuation=continuation, atol=atol)
end

function contextual_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                          σ::Strategy=strategy(m); kw...)
    ks, us = _model_tables(m, "contextual_value")
    return contextual_value(o, ks, us, σ; kw...)
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
"""
function continuation_value(r::RewardKernel; continuation=nothing)
    c = _continuation_vector(continuation, codom(r))
    return vec(sum(reward_matrix(r); dims=1)) .+ transpose(kernel_matrix(kernel(r))) * c
end

function continuation_value(o::OpenInfluenceDiagram, kernels::AbstractDict,
                            utilities::AbstractDict, σ::Strategy; continuation=nothing,
                            kw...)
    return continuation_value(interpret(o, kernels, utilities, σ; kw...);
                              continuation=continuation)
end

function continuation_value(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                            σ::Strategy=strategy(m); kw...)
    ks, us = _model_tables(m, "continuation_value")
    return continuation_value(o, ks, us, σ; kw...)
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

The diagram forms interpret `o` first, with `interpret`'s arguments and keywords.
"""
function boundary_law(r::RewardKernel; prior=nothing, atol::Real=DEFAULT_ATOL)
    μ = _prior_vector(prior, dom(r), atol)
    return kernel_matrix(kernel(r)) * μ
end

function boundary_law(o::OpenInfluenceDiagram, kernels::AbstractDict,
                      utilities::AbstractDict, σ::Strategy; prior=nothing,
                      atol::Real=DEFAULT_ATOL, kw...)
    r = interpret(o, kernels, utilities, σ; atol=atol, kw...)
    return boundary_law(r; prior=prior, atol=atol)
end

function boundary_law(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                      σ::Strategy=strategy(m); kw...)
    ks, us = _model_tables(m, "boundary_law")
    return boundary_law(o, ks, us, σ; kw...)
end

# Contextual optimisation
#########################

# The linear index, in `joint_states` order, of the joint state that `ci` gives the
# variables at the positions `sel`, whose numbers of states are `sz`.
@inline function _joint_index(ci::CartesianIndex, sel::Vector{Int}, sz::Vector{Int})
    idx, stride = 1, 1
    @inbounds for j in eachindex(sel)
        idx += stride * (ci[sel[j]] - 1)
        stride *= sz[j]
    end
    return idx
end

"""
    contextual_optimize(o::OpenInfluenceDiagram, kernels, utilities; prior = nothing,
                        continuation = nothing, max_policies = 1_000_000,
                        brute_force = false, max_states, atol) -> DecisionSolution
    contextual_optimize(o::OpenInfluenceDiagram, m::InfluenceDiagramModel; kwargs...)

Maximise [`contextual_value`](@ref) over the deterministic strategies of the decisions of
the open component `o : X → Y`, in the explicit context of a prior `μ` on its joint input
states and a continuation `c` on its joint output states, given as for
[`contextual_value`](@ref) (ADR 0018, decision 4). The result is `InfluenceDiagrams`'
`DecisionSolution`: the best value `EU_o(σ*; μ, c)`, a best strategy `σ*` with a
`DeterministicPolicy` for every decision name of `o`, and the diagnostics
`(nstrategies, method)`.

Only legal strategies are searched: each policy is a function of its decision's declared
information set, which by rule 3 holds internal and *observed* input variables only. A
hidden input is never read, so no strategy can maximise separately at each hidden boundary
state; the bundle shows that doing so changes the problem (`INF-HIDDEN-OBSTRUCTION`).

The search enumerates every deterministic strategy (`all_deterministic_policies` for each
decision name, in `decision_order`, the first decision fastest) and returns the first one
attaining the maximum, as `ExhaustivePolicySearch` does. More than `max_policies`
strategies raise `PolicySearchTooLargeError`. By default each strategy is scored from one
value table, computed by enumerating the joint states of the apex with the actions left
free: `Σ μ(x) P_chance (U + c(y))` accumulated over the information and action variables.
With `brute_force = true` every strategy is scored by [`contextual_value`](@ref) through
`interpret` instead, which is slower and is the oracle the test suite compares with.

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
at most `max_states` joint states of the apex are enumerated (`ModelTooLargeError`), and
missing tables raise `MissingKernelError` or `MissingUtilityError`. Equally named decisions
share one policy, which must fit each of them (`PolicySignatureError`). The model form reads
`kernels(m)` and `bound_utilities(m)` and refuses evidence (`ArgumentError`).
"""
function contextual_optimize(o::OpenInfluenceDiagram, kernels::AbstractDict,
                             utilities::AbstractDict; prior=nothing, continuation=nothing,
                             max_policies::Integer=1_000_000, brute_force::Bool=false,
                             max_states::Integer=DEFAULT_MAX_STATES,
                             atol::Real=DEFAULT_ATOL)
    validate(o)
    id = apex(o)
    in_ids, out_ids = input_variables(o), output_variables(o)
    X = FiniteSpace(FiniteAxis[axis(id, v) for v in in_ids])
    Y = FiniteSpace(FiniteAxis[axis(id, v) for v in out_ids])
    μ = _prior_vector(prior, X, atol)
    c = _continuation_vector(continuation, Y)
    # The decision parts in decision order, and their distinct names: equally named
    # decisions share one policy.
    ds = decision_order(id)
    dnames = Symbol[decision_name(id, d) for d in ds]
    names_ = unique(dnames)
    first_of = Dict(n => ds[findfirst(==(n), dnames)] for n in names_)
    info_axes(d) = FiniteAxis[axis(id, v) for v in decision_information(id, d)]
    action_axis(d) = axis(id, decision_variable(id, d))
    total = prod(BigInt[n_deterministic_policies(info_axes(first_of[n]),
                                                 action_axis(first_of[n]))
                        for n in names_]; init=BigInt(1))
    total <= max_policies || throw(PolicySearchTooLargeError(total, max_policies))
    per = [all_deterministic_policies(n, info_axes(first_of[n]), action_axis(first_of[n]))
           for n in names_]
    for (i, d) in enumerate(ds)
        validate_policy(dnames[i], info_axes(d), action_axis(d),
                        first(per[findfirst(==(dnames[i]), names_)]))
    end
    function strategy_of(choice)
        return Strategy(Dict{Symbol,AbstractPolicy}(names_[j] => per[j][choice[j]]
                                                    for j in eachindex(names_)))
    end
    best, best_choice = -Inf, nothing
    if brute_force
        for choice in Iterators.product(eachindex.(per)...)
            v = contextual_value(o, kernels, utilities, strategy_of(choice); prior=μ,
                                 continuation=c, max_states=max_states, atol=atol)
            v > best && ((best, best_choice) = (v, choice))
        end
        return DecisionSolution(best, strategy_of(best_choice),
                                (nstrategies=Int(total), method=:brute_force))
    end
    # The value table over the information and action variables of the decisions.
    ids = collect(parts(id, :Variable))
    n = prod(BigInt[nstates(id, v) for v in ids]; init=big(1))
    n <= max_states || throw(ModelTooLargeError(Int(min(n, typemax(Int))), max_states))
    pos = Dict{Int,Int}(v => i for (i, v) in enumerate(ids))
    dims = Tuple(nstates(id, v) for v in ids)
    factors = _factors(id, kernels, pos; atol=atol)
    us = _utility_factors(id, utilities, pos)
    keep = Int[]
    for d in ds, v in vcat(decision_information(id, d), decision_variable(id, d))
        pos[v] in keep || push!(keep, pos[v])
    end
    N = zeros(Float64, Tuple(dims[k] for k in keep))
    in_sel, out_sel = Int[pos[v] for v in in_ids], Int[pos[v] for v in out_ids]
    in_sz, out_sz = Int[nstates(id, v) for v in in_ids],
                    Int[nstates(id, v) for v in out_ids]
    for ci in CartesianIndices(dims)
        w = μ[_joint_index(ci, in_sel, in_sz)]
        w == 0 && continue
        p = _product(factors, ci)
        p == 0 && continue
        u = c[_joint_index(ci, out_sel, out_sz)]
        for f in us
            u += _value(f, ci)
        end
        N[CartesianIndex(ntuple(j -> ci[keep[j]], length(keep)))] += w * p * u
    end
    # Each policy as a table of action indices; each decision part as the positions, in
    # the value table, of its information and its action.
    kpos = Dict{Int,Int}(k => j for (j, k) in enumerate(keep))
    tables = [[map(a -> findfirst(==(a), p.action.labels), p.table) for p in per[j]]
              for j in eachindex(names_)]
    which = Int[findfirst(==(dn), names_) for dn in dnames]
    info_k = [Int[kpos[pos[v]] for v in decision_information(id, d)] for d in ds]
    act_k = Int[kpos[pos[decision_variable(id, d)]] for d in ds]
    for choice in Iterators.product(eachindex.(per)...)
        v = 0.0
        for k in CartesianIndices(N)
            ok = true
            for i in eachindex(ds)
                t = tables[which[i]][choice[which[i]]]
                ik = info_k[i]
                if t[ntuple(j -> k[ik[j]], length(ik))...] != k[act_k[i]]
                    ok = false
                    break
                end
            end
            ok && (v += N[k])
        end
        v > best && ((best, best_choice) = (v, choice))
    end
    return DecisionSolution(best, strategy_of(best_choice),
                            (nstrategies=Int(total), method=:value_table))
end

function contextual_optimize(o::OpenInfluenceDiagram, m::InfluenceDiagramModel; kw...)
    ks, us = _model_tables(m, "contextual_optimize")
    return contextual_optimize(o, ks, us; kw...)
end
