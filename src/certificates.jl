# Reward certificates (ADR 0019): `export_reward_certificate` writes an open influence
# diagram, its observability flags, its tables, one deterministic strategy and the reward
# kernel `interpret` computed for that strategy as an `OpenInfluence.RewardCertificate/v1`
# record, which the Lean checker `lake exe check_certificate` in `proofs/` reads. The format
# is specified in the workspace plan `docs/REWARD-CERTIFICATES-PLAN-2026-10-17.md` ("The
# format") and described by `docs/src/reward-certificate-v1.schema.json`; the exporter and
# the checker change together.

const _REWARD_CERTIFICATE_FORMAT = "OpenInfluence.RewardCertificate/v1"
const _NUMERIC_MODES = (:binary64_exact, :rational_exact)

function _reward_error(code::Symbol, path, message)
    return throw(RewardCertificateError(code, String(path),
                                        String(message)))
end

# The IEEE binary64 bit word of `x`: 16 lowercase hexadecimal digits, exactly as
# InfluenceDiagrams' `_dve_float_bits` writes a certificate cell.
_binary64_word(x::Float64) = string(reinterpret(UInt64, x); base=16, pad=16)

# The cells of a table with axis lengths `dims` in the certificate's order: lexicographic,
# the last axis fastest. Each coordinate is a 1-based tuple; no axes give one cell, `()`.
# The result is a flat vector, so that the comprehensions over it are flat lists too.
function _cell_order(dims::Tuple)
    return vec([reverse(Tuple(c)) for c in CartesianIndices(reverse(dims))])
end

# References, with the tags of CategoricalBayesianNetworks' `OpenNet.RawCertificate/v1`
# (`_certificate_ref` there). `what` names the part for the message.
function _reward_ref(ref, path::AbstractString, what::AbstractString)
    ref isa NoRef && return (tag="noRef",)
    ref isa NamedRef && return (tag="named", id=ref.id)
    ref isa PointMassRef && return (tag="pointMass", state=String(ref.state))
    ref isa PolicyRef && return (tag="policy", decision=String(ref.decision))
    ref isa KernelRef &&
        _reward_error(:unsupported_reference, path,
                      "$what has a reference of type $(typeof(ref)), for which $_REWARD_CERTIFICATE_FORMAT has no tag")
    return _reward_error(:unset_reference, path,
                         "$what has no reference value; $_REWARD_CERTIFICATE_FORMAT records every reference (NoRef() records none)")
end

# The 0-based rank of every variable part: its position in a topological order of the
# causal-plus-information graph (one arc per `Input` occurrence, parent to target, and one
# per `InformationInput`, information variable to action), by Kahn's algorithm with the
# smallest part id first. The diagram is valid, so the graph is acyclic (rule 5).
function _reward_ranks(id::AbstractInfluenceDiagram)
    n = nparts(id, :Variable)
    succ = [Int[] for _ in 1:n]
    indegree = zeros(Int, n)
    arc!(s, t) = (push!(succ[s], t); indegree[t] += 1)
    for i in parts(id, :Input)
        arc!(subpart(id, i, :input_variable), target(id, subpart(id, i, :input_mechanism)))
    end
    for i in parts(id, :InformationInput)
        arc!(subpart(id, i, :information_variable),
             decision_variable(id, subpart(id, i, :information_decision)))
    end
    ready = sort!(findall(iszero, indegree); rev=true)
    rank = Dict{Int,Int}()
    while !isempty(ready)
        v = pop!(ready)
        rank[v] = length(rank)
        for t in succ[v]
            indegree[t] -= 1
            if indegree[t] == 0
                push!(ready, t)
                sort!(ready; rev=true)
            end
        end
    end
    length(rank) == n ||
        throw(ArgumentError("export_reward_certificate: the causal-plus-information graph has a cycle"))
    return rank
end

# Boundary rows, as CategoricalBayesianNetworks' `_certificate_boundary`: one per foot
# variable, in foot order, with the apex variable it maps to and the foot's own attributes.
function _reward_boundary(foot::AbstractVariableSpace, mapping::AbstractVector{<:Integer},
                          dense::AbstractDict{Int,Int}, side::AbstractString)
    return [(varId=dense[mapping[i]],
             attrs=(name=String(variable_name(foot, v)),
                    spaceRef=_reward_ref(subpart(foot, v, :space_ref),
                                         "network.$side[$(i - 1)].attrs.spaceRef",
                                         "$side foot variable $(variable_name(foot, v))"),
                    states=String.(states(foot, v))))
            for (i, v) in enumerate(parts(foot, :Variable))]
end

# The `network` object: the body of `OpenNet.RawCertificate/v1`, chance mechanisms first
# (in `Mechanism` part order), then decisions (in `Decision` part order) as mechanism
# records with a policy reference and their information inputs as input rows.
function _reward_network(o::OpenInfluenceDiagram, dense::AbstractDict{Int,Int})
    id = apex(o)
    rank = _reward_ranks(id)
    variable_data = [(name=String(variable_name(id, v)),
                      spaceRef=_reward_ref(subpart(id, v, :space_ref),
                                           "network.variableData[$(dense[v])].spaceRef",
                                           "variable $(variable_name(id, v)) (part $v)"),
                      stateRows=[(name=String(subpart(id, s, :state_name)),
                                  position=subpart(id, s, :state_position))
                                 for s in incident(id, v, :state_variable)],
                      rank=rank[v]) for v in parts(id, :Variable)]
    records = Any[]
    for m in parts(id, :Mechanism)
        g = length(records)
        path = "network.mechanisms[$g].kernelRef"
        what = "mechanism $(mechanism_name(id, m)) (part $m)"
        ref = _reward_ref(subpart(id, m, :kernel_ref), path, what)
        ref.tag == "policy" &&
            _reward_error(:policy_reference_on_chance, path,
                          "$what is a chance mechanism with the policy reference PolicyRef(:$(ref.decision)); $_REWARD_CERTIFICATE_FORMAT reserves policy references for decisions")
        push!(records,
              (name=String(mechanism_name(id, m)), kernelRef=ref,
               target=dense[target(id, m)],
               inputRows=[(varId=dense[subpart(id, i, :input_variable)],
                           position=subpart(id, i, :input_position))
                          for i in incident(id, m, :input_mechanism)]))
    end
    for d in parts(id, :Decision)
        name = String(decision_name(id, d))
        push!(records,
              (name=name, kernelRef=(tag="policy", decision=name),
               target=dense[decision_variable(id, d)],
               inputRows=[(varId=dense[subpart(id, i, :information_variable)],
                           position=subpart(id, i, :information_position))
                          for i in incident(id, d, :information_decision)]))
    end
    return (variableCount=length(variable_data), variableData=variable_data,
            mechanisms=records,
            inputs=_reward_boundary(input_space(o), input_variables(o), dense, "inputs"),
            outputs=_reward_boundary(output_space(o), output_variables(o), dense,
                                     "outputs"))
end

# The first decision part of each distinct decision name, in order of first appearance
# among the decision generators. Equally named decisions share one policy, so they must
# agree in information axis lengths and action state count.
function _reward_decisions(id::AbstractInfluenceDiagram, ndecisions_before::Integer)
    shape(x) = (Int[nstates(id, v) for v in decision_information(id, x)],
                nstates(id, decision_variable(id, x)))
    firsts = Pair{Symbol,Int}[]
    for (j, d) in enumerate(parts(id, :Decision))
        name = decision_name(id, d)
        k = findfirst(p -> first(p) == name, firsts)
        if k === nothing
            push!(firsts, name => d)
            continue
        end
        d0 = last(firsts[k])
        shape(d) == shape(d0) ||
            _reward_error(:inconsistent_decision,
                          "network.mechanisms[$(ndecisions_before + j - 1)]",
                          "decisions :$name (parts $d0 and $d) share one policy but differ in shape: information axis lengths $(shape(d0)[1]) and $(shape(d)[1]), action state counts $(shape(d0)[2]) and $(shape(d)[2])")
    end
    return firsts
end

# Every cell the certificate would hold, counted from the structure alone.
function _reward_budget(o::OpenInfluenceDiagram, firsts, max_entries::Integer)
    id = apex(o)
    card(vs) = prod(BigInt[nstates(id, v) for v in vs]; init=big(1))
    total = big(0)
    for m in parts(id, :Mechanism)
        total += card(vcat(inputs(id, m), target(id, m)))
    end
    for u in parts(id, :Utility)
        total += card(utility_scope(id, u))
    end
    for (_, d) in firsts
        total += card(decision_information(id, d))
    end
    total += 2 * card(input_variables(o)) * card(output_variables(o))
    total <= max_entries ||
        _reward_error(:too_many_entries, "",
                      "the certificate needs $total cells (chance tables, utilities, strategy, K and W) and max_entries is $max_entries")
    return nothing
end

# Exact companions (`rational_exact`): the caller's dictionary with canonical keys
# `(tag, part id, zero-based coordinates)` and `Rational{BigInt}` values. Malformed keys
# and values are invalid keyword values.
function _reward_companions(numeric_mode::Symbol, exact_tables)
    if numeric_mode === :binary64_exact
        exact_tables === nothing ||
            throw(ArgumentError("export_reward_certificate: exact_tables requires numeric_mode = :rational_exact"))
        return nothing
    end
    exact_tables isa AbstractDict ||
        throw(ArgumentError("export_reward_certificate: numeric_mode = :rational_exact requires exact_tables, a dictionary of exact companions for every chance and utility cell; rationals are never inferred from Float64 cells"))
    integer(x) = x isa Integer && !(x isa Bool)
    out = Dict{Tuple{Symbol,Int,Tuple{Vararg{Int}}},Rational{BigInt}}()
    for (key, value) in exact_tables
        key isa Tuple && length(key) == 3 && key[1] in (:chance, :utility) &&
        integer(key[2]) && key[3] isa Tuple && all(integer, key[3]) ||
            throw(ArgumentError("export_reward_certificate: exact_tables key $(repr(key)) is not (:chance, mechanism part id, coordinates) or (:utility, utility part id, coordinates), with zero-based integer coordinates"))
        q = if integer(value)
            Rational{BigInt}(BigInt(value))
        elseif value isa Rational && !iszero(denominator(value))
            Rational{BigInt}(BigInt(numerator(value)), BigInt(denominator(value)))
        else
            throw(ArgumentError("export_reward_certificate: the companion for $(repr(key)) is $(repr(value)); companions must be finite exact integers or rationals"))
        end
        canonical = (key[1], Int(key[2]), Tuple(Int(i) for i in key[3]))
        haskey(out, canonical) &&
            throw(ArgumentError("export_reward_certificate: exact_tables has two entries for $(repr(canonical))"))
        out[canonical] = q
    end
    return out
end

# One number cell: `{f64}`, or `{q, f64}` with the companion under `key`, which must round
# to the cell (to nearest, ties to even, by BayesianNetworks' `_nearest_binary64`).
function _reward_cell(x::Real, key, path::AbstractString, companions, used)
    y = Float64(x)
    isfinite(x) && isfinite(y) ||
        _reward_error(:non_finite, path,
                      "the cell is $x, and $_REWARD_CERTIFICATE_FORMAT records finite binary64 words only")
    word = _binary64_word(y)
    companions === nothing && return (f64=word,)
    q = get(companions, key, nothing)
    q === nothing &&
        _reward_error(:missing_companion, path,
                      "exact_tables has no companion for $(repr(key)), the cell $y")
    push!(used, key)
    _nearest_binary64(q) == y ||
        _reward_error(:companion_rounding, path,
                      "the companion $(numerator(q))//$(denominator(q)) for $(repr(key)) rounds to $(_nearest_binary64(q)), not to the cell $y")
    return (q=(num=string(numerator(q)), den=string(denominator(q))), f64=word)
end

# The cells of `table`, whose Julia axes are `perm(coordinate)` of the certificate axes.
function _reward_cells(table, dims::Tuple, index, tag::Symbol, part::Integer,
                       path::AbstractString, companions, used)
    return [_reward_cell(table[index(c)...], (tag, Int(part), Tuple(c .- 1)),
                         "$path[$(j - 1)]", companions, used)
            for (j, c) in enumerate(_cell_order(dims))]
end

# The utility tables, one record per `Utility` part.
function _reward_utilities(id::AbstractInfluenceDiagram, utilities::AbstractDict,
                           dense::AbstractDict{Int,Int}, companions, used)
    out = Any[]
    for (k, u) in enumerate(parts(id, :Utility))
        name = utility_name(id, u)
        util = _lookup_utility(id, u, utilities)
        if util === nothing
            ref = subpart(id, u, :utility_ref)
            throw(MissingUtilityError(name, ref isa KernelRef ? ref : NoRef()))
        end
        sc = utility_scope(id, u)
        table = utility_table(util, FiniteAxis[axis(id, v) for v in sc])
        dims = Tuple(nstates(id, v) for v in sc)
        cells = _reward_cells(table, dims, identity, :utility, u,
                              "utilities[$(k - 1)].cells", companions, used)
        push!(out,
              (name=String(name),
               scopeRows=[(varId=dense[subpart(id, i, :utility_variable)],
                           position=subpart(id, i, :utility_position))
                          for i in incident(id, u, :utility_node)], cells=cells))
    end
    return out
end

# The chance tables, one record per chance mechanism: axes the parents in input-position
# order, then the child. A `FiniteKernel`'s table is outputs first, so the cell at
# `(parents..., child)` is `table[child, parents...]`.
function _reward_chance_tables(id::AbstractInfluenceDiagram, kernels::AbstractDict,
                               companions, used)
    out = Any[]
    for (k, m) in enumerate(parts(id, :Mechanism))
        g = k - 1
        kern = resolve_kernel(id, m, kernels)
        kern === nothing &&
            throw(MissingKernelError(variable_name(id, target(id, m)), kernel_ref(id, m)))
        axes_ = vcat(inputs(id, m), target(id, m))
        dims = Tuple(nstates(id, v) for v in axes_)
        cells = _reward_cells(kern.table, dims, c -> (c[end], c[1:(end - 1)]...), :chance,
                              m, "chance_tables[$g].cells", companions, used)
        push!(out, (mechanism=g, cells=cells))
    end
    return out
end

# The strategy, one record per distinct decision name: the 1-based state position of the
# action the policy picks at each cell of the first such decision's information axes.
function _reward_strategy(id::AbstractInfluenceDiagram, σ::Strategy, firsts)
    out = Any[]
    for (name, d) in firsts
        info = decision_information(id, d)
        a = decision_variable(id, d)
        k = policy_kernel(σ[name], FiniteSpace(FiniteAxis[axis(id, v) for v in info]),
                          FiniteSpace(axis(id, a)))
        positions = [subpart(id, s, :state_position) for s in state_ids(id, a)]
        dims = Tuple(nstates(id, v) for v in info)
        actions = [positions[findfirst(i -> k.table[i, c...] == 1, eachindex(positions))]
                   for c in _cell_order(dims)]
        push!(out, (decision=String(name), actions=actions))
    end
    return out
end

# `K` and `W` with the axes the input rows, then the output rows; a `RewardKernel`'s tables
# are outputs first, so the cell at `(x..., y...)` is `table[y..., x...]`.
function _reward_result(r::RewardKernel, nin::Integer)
    T, W = kernel(r).table, reward(r)
    nout = ndims(T) - nin
    dims = (size(T)[(nout + 1):end]..., size(T)[1:nout]...)
    index(c) = (c[(nin + 1):end]..., c[1:nin]...)
    cells(table, key) = [_reward_cell(table[index(c)...], nothing, "result.$key[$(j - 1)]",
                                      nothing, nothing)
                         for (j, c) in enumerate(_cell_order(dims))]
    return (arithmetic="binary64", K=cells(T, "K"), W=cells(W, "W"))
end

"""
    export_reward_certificate(o::OpenInfluenceDiagram, kernels, utilities, σ::Strategy;
                              numeric_mode = :binary64_exact, exact_tables = nothing,
                              description = "", max_entries = 1_000_000)
        -> OrderedDict{String,Any}
    export_reward_certificate(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                              σ::Strategy = strategy(m); kwargs...)

The `OpenInfluence.RewardCertificate/v1` record of the open influence diagram `o` under
the deterministic strategy `σ` (ADR 0019): its structure, observability flags, chance and
utility tables, the strategy, and the reward kernel `(K, W)` that
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy))
computes for them. The Lean checker in `proofs/`, `lake exe
check_certificate`, reads it. The arguments are those of `interpret`, dictionary and model
forms alike (a model with evidence raises `ArgumentError`).

The result is JSON-compatible data: an `OrderedDict` (OrderedCollections' type, the one
`BayesianNetworks` and `InfluenceDiagrams` return for their documents) whose keys, and the
fields of every named tuple inside it, are in the format's order, so `JSON3.write` emits
the same bytes on every Julia version. Its keys are `format`, `numeric_mode`, `metadata`
(producer, producer version, Julia version and `description`), `network`,
`observability`, `chance_tables`, `utilities`, `strategy` and `result`:

- `network` is the body of `CategoricalBayesianNetworks`' `OpenNet.RawCertificate/v1`
  (`open_network_certificate`): dense 0-based variable indices in part order, ranks (the
  0-based positions in a topological order of the causal-plus-information graph), state
  and input rows with their 1-based positions, and attributed boundary rows. The chance
  mechanisms come first, then each decision as a mechanism record whose reference is
  `policy(name)` and whose input rows are its information inputs.
- `observability` holds one flag per boundary row.
- Every table is a flat list of cells in lexicographic order of its axes, the last axis
  fastest, each axis over its variable's states in position order. Chance tables have the
  parents in input-position order, then the child; utilities their scope in position
  order; each distinct decision name has one policy, over its first decision's
  information inputs, whose cells are 1-based action state positions; `K` and `W` have
  the input rows, then the output rows. They are converted from the outputs-first,
  first-variable-fastest layout of the [`RewardKernel`](@ref).

With `numeric_mode = :binary64_exact` a number cell is `(f64 = word)`, the 16 lowercase
hexadecimal digits of the cell's IEEE binary64 bit word, as in `InfluenceDiagrams`'
`export_dve_certificate`. With `numeric_mode = :rational_exact` every chance and utility
cell also carries an exact companion `(q = (num, den), f64 = word)`, taken from
`exact_tables`, a dictionary keyed by `(:chance, mechanism_part_id, coordinates)` and
`(:utility, utility_part_id, coordinates)`, with zero-based coordinate tuples in the
table's axis order, to exact integers or rationals. It must cover every chance and utility
cell and nothing else, and each companion must round, to nearest with ties to even, to its
`Float64` cell. The result cells stay binary64 words. No rational is inferred from a
`Float64`, and no table is renormalised.

Errors:

- invalid keyword values (an unknown `numeric_mode`, `exact_tables` in binary64 mode or
  missing in rational mode, a malformed companion key or value, a `description` that is
  not a string, a negative `max_entries`) raise `ArgumentError`;
- `o` is validated first and keeps the errors of
  [`validate`](@ref validate(::OpenInfluenceDiagram)); the tables and the strategy keep
  those of `interpret`
  (among them `MissingKernelError`, `KernelBindingError`, `MissingUtilityError`,
  `UtilityScopeError`, `IncompleteStrategyError`, `PolicySignatureError`,
  `ModelTooLargeError`), and a `StochasticPolicy` raises `ArgumentError`, since the format
  records deterministic policies;
- what the format cannot record raises [`RewardCertificateError`](@ref) with a code:
  `:unset_reference`, `:unsupported_reference`, `:policy_reference_on_chance`,
  `:inconsistent_decision`, `:too_many_entries` (more than `max_entries` cells in all,
  counted from the structure before any table is read or `interpret` runs), `:non_finite`,
  `:missing_companion`, `:extra_companion` and `:companion_rounding`.

The certificate records the diagram as Julia holds it, not the operations that built it;
JSON parsing, this exporter, Catlab's colimits and Julia's `Float64` arithmetic are
trusted (ADR 0019). See the manual page "Reward certificates".
"""
function export_reward_certificate(o::OpenInfluenceDiagram, kernels::AbstractDict,
                                   utilities::AbstractDict, σ::Strategy;
                                   numeric_mode=:binary64_exact, exact_tables=nothing,
                                   description="", max_entries=1_000_000)
    numeric_mode isa Symbol && numeric_mode in _NUMERIC_MODES ||
        throw(ArgumentError("export_reward_certificate: numeric_mode must be :binary64_exact or :rational_exact, not $(repr(numeric_mode))"))
    description isa AbstractString ||
        throw(ArgumentError("export_reward_certificate: description must be a string, not a $(typeof(description))"))
    max_entries isa Integer && !(max_entries isa Bool) && max_entries >= 0 ||
        throw(ArgumentError("export_reward_certificate: max_entries must be a nonnegative integer, not $(repr(max_entries))"))
    companions = _reward_companions(numeric_mode, exact_tables)
    validate(o)
    id = apex(o)
    dense = Dict{Int,Int}(v => i - 1 for (i, v) in enumerate(parts(id, :Variable)))
    network = _reward_network(o, dense)
    firsts = _reward_decisions(id, nparts(id, :Mechanism))
    _reward_budget(o, firsts, max_entries)
    used = Set{Tuple{Symbol,Int,Tuple{Vararg{Int}}}}()
    utility_records = _reward_utilities(id, utilities, dense, companions, used)
    # The format records deterministic policies; a behavioural one (ADR 0022) is refused.
    for d in unique(decision_names(apex(o)))
        haskey(σ, d) && σ[d] isa StochasticPolicy &&
            throw(ArgumentError("export_reward_certificate: the policy of decision :$d is a StochasticPolicy; reward certificates record deterministic policies only"))
    end
    r = interpret(o, kernels, utilities, σ)
    chance_tables = _reward_chance_tables(id, kernels, companions, used)
    if companions !== nothing
        extra = sort!(collect(setdiff(keys(companions), used)))
        isempty(extra) ||
            _reward_error(:extra_companion, "exact_tables",
                          "exact_tables has $(length(extra)) companion(s) that match no chance or utility cell, the first $(repr(first(extra)))")
    end
    return OrderedDict{String,Any}("format" => _REWARD_CERTIFICATE_FORMAT,
                                   "numeric_mode" => String(numeric_mode),
                                   "metadata" =>
                                       (producer="CategoricalInfluenceDiagrams.jl",
                                        producer_version=string(pkgversion(@__MODULE__)),
                                        julia_version=string(VERSION),
                                        description=String(description)),
                                   "network" => network,
                                   "observability" =>
                                       (inputs=String.(input_observability(o)),
                                        outputs=String.(output_observability(o))),
                                   "chance_tables" => chance_tables,
                                   "utilities" => utility_records,
                                   "strategy" => _reward_strategy(id, σ, firsts),
                                   "result" =>
                                       _reward_result(r, length(input_variables(o))))
end

function export_reward_certificate(o::OpenInfluenceDiagram, m::InfluenceDiagramModel,
                                   σ::Strategy=strategy(m); kw...)
    isempty(evidence(m)) ||
        throw(ArgumentError("export_reward_certificate: the model has evidence on $(sort!(collect(keys(evidence(m))))); evidence composition is outside ADR 0018's first release"))
    return export_reward_certificate(o, kernels(m), bound_utilities(m), σ; kw...)
end

# Composition certificates (ADR 0023)
#####################################

const _COMPOSITION_CERTIFICATE_FORMAT = "OpenInfluence.CompositionCertificate/v1"
const _TENSOR_CERTIFICATE_FORMAT = "OpenInfluence.TensorCertificate/v1"

# The companions argument of an operation certificate, checked.
function _operation_tables(f, exact_tables)
    exact_tables === nothing && return (left=nothing, right=nothing, composite=nothing)
    exact_tables isa NamedTuple &&
    sort!(collect(keys(exact_tables))) == [:composite, :left, :right] ||
        throw(ArgumentError("$f: exact_tables must be a named tuple (left = ..., right = ..., composite = ...) of companions"))
    return exact_tables
end

"""
    export_composition_certificate(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram, kernels,
                                   utilities, σ::Strategy; numeric_mode = :binary64_exact,
                                   exact_tables = nothing, no_forgetting = true,
                                   description = "", max_entries = 1_000_000)
        -> OrderedDict{String,Any}

The `OpenInfluence.CompositionCertificate/v1` record of the serial composite `A ⋅ B` (ADR
0023): three reward certificates ([`export_reward_certificate`](@ref)), under `"left"` for
`A`, `"right"` for `B` and `"composite"` for `compose(A, B; no_forgetting)`, each under the
strategy `σ` (policies for decisions a diagram does not have are ignored). The Lean checker
`lake exe check_composition` accepts it when each certificate is accepted, the interfaces line
up, and every recorded cell of the composite's reward kernel is within the tolerance of the
composite, in the expectation semiring, of the parts' recorded cells. Its soundness theorems
then bound, cell by cell, the gap between the decoded composite's exact semantics and the
composite of the decoded parts', which is what ties Julia's composite to the Lean composite
of its parts.

`numeric_mode`, `description` and `max_entries` are passed to each certificate (the
description gaining the part's name). In `:rational_exact` mode `exact_tables` is a named
tuple `(left = ..., right = ..., composite = ...)` of the three certificates' companions, each
keyed by its own diagram's part ids, as `export_reward_certificate` wants them; anything else
raises `ArgumentError`. The errors of `compose` and of `export_reward_certificate` pass
through.
"""
function export_composition_certificate(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram,
                                        kernels::AbstractDict, utilities::AbstractDict,
                                        σ::Strategy; numeric_mode=:binary64_exact,
                                        exact_tables=nothing, no_forgetting::Bool=true,
                                        description="", max_entries=1_000_000)
    tables = _operation_tables("export_composition_certificate", exact_tables)
    description isa AbstractString ||
        throw(ArgumentError("export_composition_certificate: description must be a string, not a $(typeof(description))"))
    C = compose(A, B; no_forgetting=no_forgetting)
    return _operation_certificate(_COMPOSITION_CERTIFICATE_FORMAT, A, B, C, kernels, utilities,
                                  σ, tables, numeric_mode, description, max_entries)
end

# The three reward certificates of an operation's parts and result, under `format`.
function _operation_certificate(format, A, B, C, kernels, utilities, σ, tables, numeric_mode,
                                description, max_entries)
    function part(o, t, name)
        text = isempty(description) ? name : "$(description) ($(name))"
        return export_reward_certificate(o, kernels, utilities, σ; numeric_mode=numeric_mode,
                                         exact_tables=t, description=text,
                                         max_entries=max_entries)
    end
    return OrderedDict{String,Any}("format" => format,
                                   "left" => part(A, tables.left, "left"),
                                   "right" => part(B, tables.right, "right"),
                                   "composite" => part(C, tables.composite, "composite"))
end

"""
    export_tensor_certificate(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram, kernels,
                              utilities, σ::Strategy; numeric_mode = :binary64_exact,
                              exact_tables = nothing, no_forgetting = true,
                              description = "", max_entries = 1_000_000)
        -> OrderedDict{String,Any}

The `OpenInfluence.TensorCertificate/v1` record of `A ⊗ B` (ADR 0023): the reward
certificates of `A`, `B` and `otimes(A, B; no_forgetting)` under `"left"`, `"right"` and
`"composite"`, as [`export_composition_certificate`](@ref) writes them for `compose`. `lake
exe check_composition` reads either kind by its format string; for a tensor it checks that the
composite's interfaces are the parts' side by side, `A`'s first, and that every recorded cell
of the composite is within the tolerance of the product of the parts' cells (`K_A ⊗ K_B`, and
`W_A ⊗ K_B + K_A ⊗ W_B` for the reward), and its soundness theorems bound the gap between the
decoded composite's exact semantics and the tensor of the decoded parts'. The arguments and
errors are those of `export_composition_certificate`, with `otimes`'s errors passing through.
"""
function export_tensor_certificate(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram,
                                   kernels::AbstractDict, utilities::AbstractDict,
                                   σ::Strategy; numeric_mode=:binary64_exact,
                                   exact_tables=nothing, no_forgetting::Bool=true,
                                   description="", max_entries=1_000_000)
    tables = _operation_tables("export_tensor_certificate", exact_tables)
    description isa AbstractString ||
        throw(ArgumentError("export_tensor_certificate: description must be a string, not a $(typeof(description))"))
    C = otimes(A, B; no_forgetting=no_forgetting)
    return _operation_certificate(_TENSOR_CERTIFICATE_FORMAT, A, B, C, kernels, utilities, σ,
                                  tables, numeric_mode, description, max_entries)
end


# Colimit certificates (ADR 0025)
#################################

const _COLIMIT_CERTIFICATE_FORMAT = "OpenInfluence.ColimitCertificate/v1"

"""
    export_colimit_certificate(op::Symbol, A::OpenInfluenceDiagram, B::OpenInfluenceDiagram,
                               kernels, utilities, σ::Strategy; along = nothing,
                               no_forgetting = true, numeric_mode = :binary64_exact,
                               exact_tables = nothing, description = "",
                               max_entries = 1_000_000) -> OrderedDict{String,Any}
    export_colimit_certificate(uwd::UndirectedWiringDiagram, diagrams, kernels, utilities,
                               σ::Strategy; kwargs...) -> OrderedDict{String,Any}

The `OpenInfluence.ColimitCertificate/v1` record of a composite (ADR 0025): the reward
certificates ([`export_reward_certificate`](@ref)) of the parts under `"parts"` and of the
composite under `"composite"`, all under the strategy `σ`, with the operation's name under
`"operation"` and Catlab's cocone under `"legs"`: for each part, the 0-based index in the
composite's certificate of each of its variables, generators (chance mechanisms, then
decisions, as the reward certificate numbers them) and utilities. `op` is `:compose`,
`:otimes` or `:glue` (which needs `along`, as for `glue`); the second form is `oapply` on the
undirected wiring diagram `uwd`. For `glue` the second part is recorded as glued: its glued
inputs carry the names of their partners in `A`, as in the composite.

`lake exe check_composition` accepts the certificate when every reward certificate is
accepted and the legs are a colimit witness: bijective on generators and utilities,
preserving attributes, labels, targets, parents, tables, policies and scopes, identifying
only boundary variables, and covering the composite's outputs. Its soundness theorems then
give, exactly and with no tolerance, the composite's semantics as the junction sum of the
parts' in the expectation semiring: the structure of the composite, not only its numbers,
is checked.

In `:rational_exact` mode `exact_tables` is a named tuple `(parts = [...], composite = ...)`
of companions, one per part and one for the composite, each keyed by its own diagram's part
ids; anything else raises `ArgumentError`, as does an unknown `op` or `along` given to any
operation but `:glue`. The errors of the operation and of `export_reward_certificate` pass
through.
"""
function export_colimit_certificate(op::Symbol, A::OpenInfluenceDiagram,
                                    B::OpenInfluenceDiagram, kernels::AbstractDict,
                                    utilities::AbstractDict, σ::Strategy; along=nothing,
                                    no_forgetting::Bool=true, kw...)
    op === :glue || along === nothing ||
        throw(ArgumentError("export_colimit_certificate: along is for :glue only, not :$op"))
    if op === :compose
        C, cocone = _compose_cocone(A, B; no_forgetting=no_forgetting)
        pieces = [A, B]
    elseif op === :otimes
        C, cocone = _otimes_cocone(A, B; no_forgetting=no_forgetting)
        pieces = [A, B]
    elseif op === :glue
        along === nothing &&
            throw(ArgumentError("export_colimit_certificate: :glue needs along"))
        C, cocone, pieces = _glue_cocone(A, B; along=along, no_forgetting=no_forgetting)
    else
        throw(ArgumentError("export_colimit_certificate: op must be :compose, :otimes or :glue, not :$op"))
    end
    return _colimit_certificate(String(op), pieces, C, cocone, kernels, utilities, σ; kw...)
end

function export_colimit_certificate(uwd::UndirectedWiringDiagram,
                                    diagrams::AbstractVector{<:OpenInfluenceDiagram},
                                    kernels::AbstractDict, utilities::AbstractDict,
                                    σ::Strategy; no_forgetting::Bool=true, kw...)
    C, cocone = _oapply_cocone(uwd, diagrams; no_forgetting=no_forgetting)
    return _colimit_certificate("oapply", collect(diagrams), C, cocone, kernels, utilities, σ;
                                kw...)
end

# The leg record of the cocone map `f` from the apex of `piece` into the apex `P` of the
# composite, in the reward certificates' numbering.
function _colimit_leg(piece::OpenInfluenceDiagram, f, P)
    id = apex(piece)
    nm = nparts(P, :Mechanism)
    return (variables=[f.Variable[v] - 1 for v in parts(id, :Variable)],
            generators=vcat([f.Mechanism[m] - 1 for m in parts(id, :Mechanism)],
                            [nm + f.Decision[d] - 1 for d in parts(id, :Decision)]),
            utilities=[f.Utility[u] - 1 for u in parts(id, :Utility)])
end

function _colimit_certificate(op::String, pieces, C, cocone, kernels, utilities, σ;
                              numeric_mode=:binary64_exact, exact_tables=nothing,
                              description="", max_entries=1_000_000)
    description isa AbstractString ||
        throw(ArgumentError("export_colimit_certificate: description must be a string, not a $(typeof(description))"))
    if exact_tables === nothing
        tables = (parts=fill(nothing, length(pieces)), composite=nothing)
    else
        exact_tables isa NamedTuple &&
        sort!(collect(keys(exact_tables))) == [:composite, :parts] &&
        length(exact_tables.parts) == length(pieces) ||
            throw(ArgumentError("export_colimit_certificate: exact_tables must be a named tuple (parts = [...], composite = ...) with one companion table per part"))
        tables = exact_tables
    end
    function certificate(o, t, name)
        text = isempty(description) ? name : "$(description) ($(name))"
        return export_reward_certificate(o, kernels, utilities, σ; numeric_mode=numeric_mode,
                                         exact_tables=t, description=text,
                                         max_entries=max_entries)
    end
    return OrderedDict{String,Any}("format" => _COLIMIT_CERTIFICATE_FORMAT,
                                   "operation" => op,
                                   "parts" => [certificate(o, t, "part $k")
                                               for (k, (o, t)) in
                                               enumerate(zip(pieces, tables.parts))],
                                   "composite" => certificate(C, tables.composite,
                                                              "composite"),
                                   "legs" => [_colimit_leg(o, f, apex(C))
                                              for (o, f) in zip(pieces, cocone)])
end
