"""
The semantics of open influence diagrams for a fixed strategy (ADR 0018, decision 3): the
expectation-semiring kernel category. A morphism `X → Y` is a [`RewardKernel`](@ref)
`(K, W)`: `K` is a `FiniteKernel` from the input interface to the output interface, and
`W` a real table of the same shape holding the probability-weighted reward earned on the
way. Composition and tensor are those of `FiniteKernels.jl` lifted to the expectation
semiring `(p, r)·(q, s) = (pq, ps + rq)`; `W` is carried through `compose_kernel` and
`tensor_kernel` as an unchecked `FiniteKernel`, so no kernel arithmetic is reimplemented
here. [`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy))
maps an open influence diagram and a deterministic strategy to its reward kernel, in the
layout of `CategoricalBayesianNetworks`' `interpret` for open networks.
"""

# Reward kernels
################

"""
    RewardKernel(K::FiniteKernel, W::AbstractArray{<:Real})
    RewardKernel(K::FiniteKernel)

A morphism of the expectation-semiring kernel category (ADR 0018, decision 3): the
semantics of an open influence diagram `X → Y` under a fixed strategy.

- `K` is a `FiniteKernel` `X → Y`: `K(y | x)` is the probability of reaching the output
  state `y` from the input state `x`.
- `W` is a real table of exactly the shape of `K`'s table, outputs first:
  `W[y..., x...]` is the expectation, given `x`, of the reward earned on the way times
  the indicator that the output state is `y`. It may be signed. Summed over the outputs it
  is the expected reward given `x`.

Without `W` the reward is zero: this lifts a kernel such as an identity, a copy, a discard
or a swap into the category. A `W` of another shape, or with an entry that is not finite,
raises `ArgumentError`.

Read the parts with `kernel(r)` and [`reward`](@ref), the spaces with `dom(r)` and
`codom(r)`. Combine with [`compose`](@ref compose(::RewardKernel, ::RewardKernel)) and
[`otimes`](@ref otimes(::RewardKernel, ::RewardKernel)); the structure maps are
[`identity_reward_kernel`](@ref), [`copy_reward_kernel`](@ref),
[`discard_reward_kernel`](@ref) and [`swap_reward_kernel`](@ref). Joint states are
ordered as `FiniteKernels`' `joint_states` (the first variable varies fastest), so
[`reward_matrix`](@ref) and `kernel_matrix(kernel(r))` share their rows and columns.
"""
struct RewardKernel
    kernel::FiniteKernel
    reward::Array{Float64}
    function RewardKernel(K::FiniteKernel, W::AbstractArray{<:Real})
        size(W) == size(K.table) ||
            throw(ArgumentError("RewardKernel: the reward table has size $(size(W)) but the kernel $(K.dom) → $(K.codom) has a table of size $(size(K.table))"))
        all(isfinite, W) ||
            throw(ArgumentError("RewardKernel: the reward table has an entry that is not finite"))
        return new(K, convert(Array{Float64}, collect(W)))
    end
end

RewardKernel(K::FiniteKernel) = RewardKernel(K, zeros(Float64, size(K.table)))

"""
    kernel(r::RewardKernel) -> FiniteKernel

The probability part `K` of the reward kernel `r`.
"""
kernel(r::RewardKernel) = r.kernel

"""
    reward(r::RewardKernel) -> Array{Float64}

The reward part `W` of `r`, laid out as the table of `kernel(r)` (output axes first,
then input axes).
"""
reward(r::RewardKernel) = r.reward

"""
    reward_matrix(r::RewardKernel) -> Matrix{Float64}

The reward table of `r` as a `length(codom) × length(dom)` matrix, with rows and columns
ordered as `kernel_matrix(kernel(r))`. Its column sums are the expected rewards given each
input state.
"""
reward_matrix(r::RewardKernel) = reshape(r.reward, length(r.kernel.codom),
                                         length(r.kernel.dom))

"""
    dom(r::RewardKernel) -> FiniteSpace
    codom(r::RewardKernel) -> FiniteSpace

The input and output space of `r`, those of `kernel(r)`.
"""
dom(r::RewardKernel) = r.kernel.dom
codom(r::RewardKernel) = r.kernel.codom

function Base.:(==)(a::RewardKernel, b::RewardKernel)
    return a.kernel == b.kernel && a.reward == b.reward
end
Base.hash(r::RewardKernel, h::UInt) = hash(r.reward, hash(r.kernel, hash(:RewardKernel, h)))

"""
    isapprox(a::RewardKernel, b::RewardKernel; kwargs...) -> Bool

Whether `a` and `b` have the same spaces and approximately equal kernels and reward
tables; the keywords (`atol`, `rtol`) are passed to both comparisons.
"""
function Base.isapprox(a::RewardKernel, b::RewardKernel; kwargs...)
    return isapprox(a.kernel, b.kernel; kwargs...) && size(a.reward) == size(b.reward) &&
           isapprox(a.reward, b.reward; kwargs...)
end

function Base.show(io::IO, r::RewardKernel)
    return print(io, "RewardKernel(", axis_names(dom(r)), " → ", axis_names(codom(r)), ")")
end

# The reward table as an unchecked `FiniteKernel`, so that `compose_kernel` and
# `tensor_kernel` do its linear algebra.
_reward_kernel(r::RewardKernel) = FiniteKernel(dom(r), codom(r), r.reward; check=false)

"""
    compose(a::RewardKernel, b::RewardKernel, cs::RewardKernel...) -> RewardKernel
    a ⋅ b

Sequential composition in diagrammatic order (first `a`, then `b`):
`(K₁, W₁) ; (K₂, W₂) = (K₁K₂, W₁K₂ + K₁W₂)`, where `K₁K₂` is `FiniteKernels`'
`compose_kernel`. The reward earned in `a` is carried through `b`'s kernel and the reward
earned in `b` is weighted by the probability of reaching each of its inputs. Further
reward kernels are folded on from the left. `codom(a)` must equal `dom(b)` (`FiniteKernels`'
`SpaceMismatchError`).
"""
function compose(a::RewardKernel, b::RewardKernel)
    K = compose_kernel(a.kernel, b.kernel)
    W = compose_kernel(_reward_kernel(a), b.kernel).table +
        compose_kernel(a.kernel, _reward_kernel(b)).table
    return RewardKernel(K, W)
end
function compose(a::RewardKernel, b::RewardKernel, c::RewardKernel, cs::RewardKernel...)
    return foldl(compose, (c, cs...); init=compose(a, b))
end

⋅(a::RewardKernel, b::RewardKernel) = compose(a, b)

"""
    otimes(a::RewardKernel, b::RewardKernel, cs::RewardKernel...) -> RewardKernel
    a ⊗ b

The tensor `(K₁ ⊗ K₂, W₁ ⊗ K₂ + K₁ ⊗ W₂)` on `dom(a) ⊗ dom(b) → codom(a) ⊗ codom(b)`, where
`⊗` of kernels is `FiniteKernels`' `tensor_kernel`: the two run independently and their
rewards add. Further reward kernels are folded on from the left.
"""
function otimes(a::RewardKernel, b::RewardKernel)
    K = tensor_kernel(a.kernel, b.kernel)
    W = tensor_kernel(_reward_kernel(a), b.kernel).table +
        tensor_kernel(a.kernel, _reward_kernel(b)).table
    return RewardKernel(K, W)
end
function otimes(a::RewardKernel, b::RewardKernel, c::RewardKernel, cs::RewardKernel...)
    return foldl(otimes, (c, cs...); init=otimes(a, b))
end

⊗(a::RewardKernel, b::RewardKernel) = otimes(a, b)

"""
    identity_reward_kernel(X::FiniteSpace) -> RewardKernel

The identity `(id_X, 0)`.
"""
identity_reward_kernel(X::FiniteSpace) = RewardKernel(identity_kernel(X))

"""
    copy_reward_kernel(X::FiniteSpace) -> RewardKernel

The copy map `X → X ⊗ X` of `FiniteKernels`, with zero reward.
"""
copy_reward_kernel(X::FiniteSpace) = RewardKernel(copy_kernel(X))

"""
    discard_reward_kernel(X::FiniteSpace) -> RewardKernel

The discard map `X → I` of `FiniteKernels`, with zero reward. Discard is not natural in
this category: `f ; discard` keeps the expected reward of `f` given each input, so it
equals `discard` only when that reward is zero. Discarding an output does not discard the
reward earned on the way to it.
"""
discard_reward_kernel(X::FiniteSpace) = RewardKernel(discard_kernel(X))

"""
    swap_reward_kernel(X::FiniteSpace, Y::FiniteSpace) -> RewardKernel

The symmetry `X ⊗ Y → Y ⊗ X` of `FiniteKernels`, with zero reward.
"""
swap_reward_kernel(X::FiniteSpace, Y::FiniteSpace) = RewardKernel(swap_kernel(X, Y))

# Strategies
############

"""
    merge_strategies(σs::Strategy...) -> Strategy

The strategy of a composite: the disjoint union of the components' strategies (ADR 0018,
decision 3). A decision name with a policy in two of them raises
[`DuplicatePolicyError`](@ref), even when the two policies are equal: the components of a
composite built by `compose` or `glue` have distinct decision names, and a strategy names
each decision once.
"""
function merge_strategies(σs::Strategy...)
    out = Dict{Symbol,AbstractPolicy}()
    for σ in σs, d in sort!(collect(keys(σ)))
        haskey(out, d) && throw(DuplicatePolicyError(d))
        out[d] = σ[d]
    end
    return Strategy(out)
end

# Interpretation
################

# The utility bound to utility node `u`, from a dictionary keyed by utility name or by
# `utility_ref` (as InfluenceDiagrams' `bound_utilities` and the kernels of a model are);
# `nothing` when it does not resolve. A `NoRef` or unset reference never resolves by
# reference.
function _lookup_utility(id::AbstractInfluenceDiagram, u::Integer, us::AbstractDict{Symbol})
    return get(us, utility_name(id, u), nothing)
end
function _lookup_utility(id::AbstractInfluenceDiagram, u::Integer,
                         us::AbstractDict{<:KernelRef})
    ref = subpart(id, u, :utility_ref)
    return ref isa KernelRef && !(ref isa NoRef) ? get(us, ref, nothing) : nothing
end

# The value of the factor `f` (a table indexed by the variables at `f.axes`) at the joint
# assignment `ci`.
@inline function _value(f::_Factor, ci::CartesianIndex)
    idx = 1
    @inbounds for j in eachindex(f.axes)
        idx += f.strides[j] * (ci[f.axes[j]] - 1)
    end
    return @inbounds f.table[idx]
end

# The policy factors of `id` under `σ`: for each decision, the one-hot kernel of its policy
# on (action, information...) at the positions `pos`.
function _policy_factors(id::AbstractInfluenceDiagram, σ::Strategy,
                         pos::AbstractDict{Int,Int})
    missing = missing_policies(σ, id)
    isempty(missing) || throw(IncompleteStrategyError(missing))
    out = _Factor[]
    for d in parts(id, :Decision)
        name = decision_name(id, d)
        p = σ[name]
        p isa Union{DeterministicPolicy,ConstantPolicy} ||
            throw(ArgumentError("interpret: the policy of decision :$name is a $(nameof(typeof(p))); the first release interprets deterministic policies only (ADR 0018, decision 4)"))
        info = decision_information(id, d)
        a = decision_variable(id, d)
        info_axes = FiniteAxis[axis(id, v) for v in info]
        validate_policy(name, info_axes, axis(id, a), p)
        k = policy_kernel(p, FiniteSpace(info_axes), FiniteSpace(axis(id, a)))
        push!(out, _Factor(k.table, Int[pos[a]; Int[pos[v] for v in info]]))
    end
    return out
end

# The utility factors of `id`, each on its scope at the positions `pos`.
function _utility_factors(id::AbstractInfluenceDiagram, utilities::AbstractDict,
                          pos::AbstractDict{Int,Int})
    out = _Factor[]
    for u in parts(id, :Utility)
        name = utility_name(id, u)
        util = _lookup_utility(id, u, utilities)
        if util === nothing
            ref = subpart(id, u, :utility_ref)
            throw(MissingUtilityError(name, ref isa KernelRef ? ref : NoRef()))
        end
        sc = utility_scope(id, u)
        table = utility_table(util, FiniteAxis[axis(id, v) for v in sc])
        all(isfinite, table) ||
            throw(UtilityScopeError(name, :value, "finite utility entries", table))
        push!(out, _Factor(table, Int[pos[v] for v in sc]))
    end
    return out
end

# Evidence (ADR 0021)
#####################

# The evidence `ev` on the apex of `o` as a dictionary from variable name to state: `nothing`,
# a pair, a vector of pairs or a dictionary. Every name must be an apex variable
# (`UnknownVariableError`), every state one of its states (`UnknownStateError`), and no
# evidence may be on a decision's action (`EvidenceOnActionError`: an action is chosen, not
# observed). A name shared by several apex variables (a diagram tensored with itself)
# observes all of them.
function _evidence(o::OpenInfluenceDiagram, ev)
    ev === nothing && return Dict{Symbol,Symbol}()
    ev isa Union{Pair,AbstractVector,AbstractDict} ||
        throw(ArgumentError("evidence must be a pair, a vector of pairs or a dictionary of variable name => state, not a $(typeof(ev))"))
    pairs_ = ev isa Pair ? [ev] : collect(ev)
    all(p -> p isa Pair{Symbol,Symbol}, pairs_) ||
        throw(ArgumentError("evidence must map variable names (Symbols) to states (Symbols)"))
    d = Dict{Symbol,Symbol}()
    for (x, s) in pairs_
        haskey(d, x) && d[x] !== s &&
            throw(ArgumentError("the evidence gives :$x two states, :$(d[x]) and :$s"))
        d[x] = s
    end
    id = apex(o)
    for x in sort!(collect(keys(d)))
        vs = [v for v in parts(id, :Variable) if variable_name(id, v) === x]
        isempty(vs) && throw(UnknownVariableError(x))
        for v in vs
            d[x] in axis(id, v).labels || throw(UnknownStateError(x, d[x]))
            dec = InfluenceDiagrams.decision_of(id, v)
            dec === nothing ||
                throw(EvidenceOnActionError(x, decision_name(id, dec), d[x]))
        end
    end
    return d
end

# The tables of `⟦o⟧_σ` under the evidence `ev` (checked by `_evidence`), in the arithmetic
# that `conv` maps each Float64 table entry into: `identity` for the binary64 run,
# `Rational{BigInt}` for an exact one. `o` must be validated. Evidence is one indicator factor
# per observed apex variable, inputs and outputs included, so `T` is the probability of
# reaching each output with the evidence and `W` the reward on those paths. Also returns
# whether a mechanism table has a (tolerated) negative entry, the number of mechanism and
# policy factors (one per variable that is not an input), the `n` of ADR 0014's budget, and
# whether the binary64 run computed a product of nonzero operands below `floatmin` (ADR
# 0014's shared trust rule: such a run decides nothing about the evidence mass).
function _interpret_tables(o::OpenInfluenceDiagram, kernels::AbstractDict,
                           utilities::AbstractDict, σ::Strategy, ev::Dict{Symbol,Symbol},
                           conv; max_states::Integer=DEFAULT_MAX_STATES,
                           atol::Real=DEFAULT_ATOL)
    id = apex(o)
    in_ids, out_ids = input_variables(o), output_variables(o)
    ids = collect(parts(id, :Variable))
    n = prod(BigInt[nstates(id, v) for v in ids]; init=big(1))
    n <= max_states || throw(ModelTooLargeError(Int(min(n, typemax(Int))), max_states))
    pos = Dict{Int,Int}(v => i for (i, v) in enumerate(ids))
    dims = Tuple(nstates(id, v) for v in ids)
    factors = _factors(id, kernels, pos; atol=atol)
    negative = any(f -> any(<(0), f.table), factors)
    append!(factors, _policy_factors(id, σ, pos))
    nfactors = length(factors)
    for v in ids
        s = get(ev, variable_name(id, v), nothing)
        s === nothing && continue
        push!(factors, _Factor(Float64[l === s for l in axis(id, v).labels], Int[pos[v]]))
    end
    us = _utility_factors(id, utilities, pos)
    X = FiniteSpace(FiniteAxis[axis(id, v) for v in in_ids])
    Y = FiniteSpace(FiniteAxis[axis(id, v) for v in out_ids])
    R = typeof(conv(0.0))
    T = zeros(R, (size(Y)..., size(X)...))
    W = zeros(R, size(T))
    sel = Int[pos[v] for v in vcat(out_ids, in_ids)]
    underflow = false
    tiny(x) = !iszero(x) && abs(x) < floatmin(Float64)
    for ci in CartesianIndices(dims)
        if R === Float64
            p = _product(factors, ci)
            if p == 0
                underflow |= all(f -> !iszero(_value(f, ci)), factors)
                continue
            end
            underflow |= tiny(p)
        else
            p = one(R)
            for f in factors
                x = _value(f, ci)
                if iszero(x)
                    p = zero(R)
                    break
                end
                p *= conv(x)
            end
            iszero(p) && continue
        end
        u = zero(R)
        for f in us
            u += conv(_value(f, ci))
        end
        idx = ntuple(j -> ci[sel[j]], length(sel))
        T[idx...] += p
        pu = p * u
        R === Float64 && !iszero(u) && (underflow |= iszero(pu) || tiny(pu))
        W[idx...] += pu
    end
    return (X=X, Y=Y, K=T, W=W, negative=negative, nfactors=nfactors, underflow=underflow)
end

"""
    interpret(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy; evidence = nothing,
              max_states = 1_000_000, atol = DEFAULT_ATOL) -> RewardKernel
    interpret(o::OpenInfluenceDiagram, m::InfluenceDiagramModel, σ::Strategy = strategy(m); kwargs...)

The semantics `⟦o⟧_σ : ⊗ inputs → ⊗ outputs` of an open influence diagram under the fixed
deterministic strategy `σ` (ADR 0018, decision 3), as a [`RewardKernel`](@ref) `(K, W)`.
For each joint input state `x`, `K(y | x)` is the probability that the outputs take the
joint state `y`, and `W[y..., x...]` the expectation of the total (additive) utility of the
apex times the indicator that the outputs are `y`. The inputs have no mechanism, so the
apex is conditioned on them: the product of the chance kernels and the policy kernels is
summed over every apex variable that is not an output, with the inputs held at `x`.

The layout is that of `CategoricalBayesianNetworks`' `interpret` for an open network: the
input and output spaces have one axis per interface variable, in interface order (an
output listed twice is copied, an input that is also an output passes through), and the
joint states are enumerated with the first variable fastest. On a closed composite (no
inputs, no outputs) the result is the `1 × 1` reward kernel with `K = 1` and `W` the
expected utility that `InfluenceDiagrams`' `expected_utility` computes on the instantiated
diagram.

`evidence` (ADR 0021) is hard evidence on apex variables: a pair `:X => :x`, a vector of
pairs or a dictionary. Each observed variable contributes the indicator of its observed
state, inputs and outputs included, so `K(y | x)` becomes the probability of reaching `y`
*and* seeing the evidence, and `W` the reward earned on those paths. `K` is then
substochastic: it is built unchecked, and its column sums are the probability of the
evidence given each input state. Nothing is normalised, since the evidence mass must cross
the boundary to the rest of the problem (normalising each component on its own evidence
is not sound; see [`conditional_value`](@ref)). Reward kernels with evidence compose as any
others: `interpret(compose(A, B), merge_strategies(σ, τ); evidence = e)` is
`compose(interpret(A, σ; evidence = e_A), interpret(B, τ; evidence = e_B))`, where `e_A`
and `e_B` are the parts of `e` on each apex; evidence on a variable of the shared boundary
may be given to either or both, since an indicator is idempotent. An unknown variable
raises `UnknownVariableError`, an unknown state `UnknownStateError`, evidence on a
decision's action `EvidenceOnActionError` (an action is chosen, not observed), and two
states for one variable `ArgumentError`.

The tables come from the apex's references, as `instantiate` reads them:

- `kernels` is a dictionary keyed by `KernelRef` or by target variable name, exactly as
  for `CategoricalBayesianNetworks`' `interpret` (`MissingKernelError`,
  `KernelBindingError`);
- `utilities` a dictionary of `AbstractUtility`s keyed by utility name (as
  `bound_utilities` of a model) or by `utility_ref` (`MissingUtilityError` when one does
  not resolve, `UtilityScopeError` when one does not fit its scope);
- a model `m` supplies `kernels(m)` and `bound_utilities(m)`, and `σ` defaults to its
  strategy. Its evidence is used as the evidence, together with the `evidence` keyword
  (a variable given different states by the two raises `ArgumentError`).

`σ` needs a `DeterministicPolicy` or `ConstantPolicy` for every decision name of the apex
(`IncompleteStrategyError`; a `StochasticPolicy` raises `ArgumentError`), checked against
the decision's information and action axes (`PolicySignatureError`); policies for other
decisions are ignored, as `instantiate` ignores them, and decisions that share a name share
their policy. A decision that reads an observed input reads that input's state directly:
the policy is evaluated at the input state `x`, which is what rule 3 makes legal. Build the
strategy of a composite with [`merge_strategies`](@ref).

`o` is validated first. At most `max_states` joint states of the apex are enumerated
(`ModelTooLargeError`); `atol` is the normalisation tolerance of the kernels.

Functoriality, checked numerically by the test suite against the closed-composite oracle:
`interpret(compose(A, B), merge_strategies(σ, τ)) ≈ compose(interpret(A, σ),
interpret(B, τ))`, and likewise for `otimes`, with and without evidence.
"""
function interpret(o::OpenInfluenceDiagram, kernels::AbstractDict,
                   utilities::AbstractDict, σ::Strategy; evidence=nothing,
                   max_states::Integer=DEFAULT_MAX_STATES, atol::Real=DEFAULT_ATOL)
    validate(o)
    ev = _evidence(o, evidence)
    t = _interpret_tables(o, kernels, utilities, σ, ev, identity; max_states=max_states,
                          atol=atol)
    K = isempty(ev) ? FiniteKernel(t.X, t.Y, t.K; atol=_joint_atol(atol, t.nfactors)) :
        FiniteKernel(t.X, t.Y, t.K; check=false)
    return RewardKernel(K, t.W)
end

# The kernels, utilities and evidence of a model, its own evidence joined with `extra`.
function _model_tables(m::InfluenceDiagramModel, extra=nothing)
    ev = Dict{Symbol,Symbol}(BayesianNetworks.evidence(m))
    if extra !== nothing
        extra isa Union{Pair,AbstractVector,AbstractDict} ||
            throw(ArgumentError("evidence must be a pair, a vector of pairs or a dictionary of variable name => state, not a $(typeof(extra))"))
        for (x, s) in (extra isa Pair ? [extra] : collect(extra))
            haskey(ev, x) && ev[x] !== s &&
                throw(ArgumentError("the model observes :$x in state :$(ev[x]), but the evidence keyword gives :$s"))
            ev[x] = s
        end
    end
    return kernels(m), bound_utilities(m), ev
end

function interpret(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                   σ::Strategy=strategy(m); evidence=nothing, kw...)
    ks, us, ev = _model_tables(m, evidence)
    return interpret(o, ks, us, σ; evidence=ev, kw...)
end
