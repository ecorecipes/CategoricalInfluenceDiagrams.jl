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

"""
    interpret(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy;
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

The tables come from the apex's references, as `instantiate` reads them:

- `kernels` is a dictionary keyed by `KernelRef` or by target variable name, exactly as
  for `CategoricalBayesianNetworks`' `interpret` (`MissingKernelError`,
  `KernelBindingError`);
- `utilities` a dictionary of `AbstractUtility`s keyed by utility name (as
  `bound_utilities` of a model) or by `utility_ref` (`MissingUtilityError` when one does
  not resolve, `UtilityScopeError` when one does not fit its scope);
- a model `m` supplies `kernels(m)` and `bound_utilities(m)`, and `σ` defaults to its
  strategy. A model with evidence raises `ArgumentError`: evidence composition is outside
  ADR 0018's first release.

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
interpret(B, τ))`, and likewise for `otimes`.
"""
function interpret(o::OpenInfluenceDiagram, kernels::AbstractDict,
                   utilities::AbstractDict, σ::Strategy;
                   max_states::Integer=DEFAULT_MAX_STATES, atol::Real=DEFAULT_ATOL)
    validate(o)
    id = apex(o)
    in_ids, out_ids = input_variables(o), output_variables(o)
    ids = collect(parts(id, :Variable))
    n = prod(BigInt[nstates(id, v) for v in ids]; init=big(1))
    n <= max_states || throw(ModelTooLargeError(Int(min(n, typemax(Int))), max_states))
    pos = Dict{Int,Int}(v => i for (i, v) in enumerate(ids))
    dims = Tuple(nstates(id, v) for v in ids)
    factors = _factors(id, kernels, pos; atol=atol)
    append!(factors, _policy_factors(id, σ, pos))
    us = _utility_factors(id, utilities, pos)
    X = FiniteSpace(FiniteAxis[axis(id, v) for v in in_ids])
    Y = FiniteSpace(FiniteAxis[axis(id, v) for v in out_ids])
    T = zeros(Float64, (size(Y)..., size(X)...))
    W = zeros(Float64, size(T))
    sel = Int[pos[v] for v in vcat(out_ids, in_ids)]
    for ci in CartesianIndices(dims)
        p = _product(factors, ci)
        p == 0 && continue
        u = 0.0
        for f in us
            u += _value(f, ci)
        end
        idx = ntuple(j -> ci[sel[j]], length(sel))
        T[idx...] += p
        W[idx...] += p * u
    end
    K = FiniteKernel(X, Y, T; atol=_joint_atol(atol, length(factors)))
    return RewardKernel(K, W)
end

function interpret(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                   σ::Strategy=strategy(m); kw...)
    isempty(evidence(m)) ||
        throw(ArgumentError("interpret: the model has evidence on $(sort!(collect(keys(evidence(m))))); evidence composition is outside ADR 0018's first release"))
    return interpret(o, kernels(m), bound_utilities(m), σ; kw...)
end
