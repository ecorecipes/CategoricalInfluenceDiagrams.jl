"""
Composition of open influence diagrams (ADR 0018, decision 2): strict sequential `compose`,
the convenient `glue`, the tensor `otimes` and `oapply` over undirected wiring diagrams,
mirroring `CategoricalBayesianNetworks.jl`. Every operation is a pushout or coproduct of
`InfluenceDiagram` ACSets computed by Catlab. The interfaces are compared first, names,
states, references and observability, and the composite is re-wrapped and validated:
rules 1 to 5 of the typed-interface rule on the composite, then rule 6, that composition
preserves no-forgetting.
"""

# Unset references in colimits
##############################

# `CategoricalBayesianNetworks`' `_with_unset_refs_held` runs a colimit on copies whose unset
# references (`space_ref`, `kernel_ref` and, in an influence diagram, `utility_ref`) hold a
# placeholder, and clears the placeholders from what it returns. It finds the ACSets of a
# value through `_acsets`, which needs to know the values of this package.
_acsets(o::OpenInfluenceDiagram) = _acsets(o.cospan)
_acsets(X::OpenInfluenceDiagramOb) = (X.space,)
_acsets(X::InfluenceDiagramCospanOb) = (X.ob,)

# Interface comparison
######################

"""
    interface_matches(X::OpenInfluenceDiagramOb, Y::OpenInfluenceDiagramOb) -> Bool

Whether two interfaces of open influence diagrams agree exactly: their spaces match in the
sense of `CategoricalBayesianNetworks`' `interface_matches` (the same variables, states with
positions, and references, position by position), and their [`OBSERVABILITY`](@ref) flags
are equal. This is the condition under which
[`compose`](@ref compose(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)) glues
`codom(A)` to `dom(B)`.
"""
function interface_matches(X::OpenInfluenceDiagramOb, Y::OpenInfluenceDiagramOb)
    return _interface_difference(X.space, Y.space) === nothing &&
           X.observability == Y.observability
end

# Throw the first difference between two interfaces with flags, names and states first.
function _check_interfaces(a::AbstractVariableSpace, fa::AbstractVector{Symbol},
                           b::AbstractVariableSpace, fb::AbstractVector{Symbol},
                           context::AbstractString)
    d = _interface_difference(a, b)
    d === nothing || throw(InterfaceMismatchError(d..., context))
    for (i, (x, y)) in enumerate(zip(fa, fb))
        x === y ||
            throw(ObservabilityMismatchError(variable_name(a, i), i, x, y, context))
    end
    return nothing
end

# Pushouts
##########

# Pushout of `a` and `b` along the variable space on the variables `ids_a` of `a`, whose
# matches in `b` are `ids_b` (states agreeing position by position).
function _pushout_along_maps(a::InfluenceDiagram, ids_a::AbstractVector{<:Integer},
                             b::InfluenceDiagram, ids_b::AbstractVector{<:Integer})
    S, va, sa = _foot(a, ids_a)
    _, vb, sb = _foot(b, ids_b)
    length(sa) == length(sb) ||
        throw(InterfaceMismatchError(:states, 0, sa, sb, "pushout: state counts differ"))
    LS = InfluenceDiagram()
    copy_parts!(LS, S)
    fa = ACSetTransformation((Variable=va, State=sa), LS, a)
    fb = ACSetTransformation((Variable=vb, State=sb), LS, b)
    po = pushout[infer_acset_cat(a)](fa, fb)
    ia, ib = legs(po)
    return apex(po), ia, ib
end

# No-forgetting (rule 6)
########################

# Successor lists of the information graph of `id`: causal inputs, information inputs and
# explicit precedence, on variable ids.
function _successors(id::AbstractInfluenceDiagram)
    succ = [Int[] for _ in parts(id, :Variable)]
    for i in parts(id, :Input)
        push!(succ[subpart(id, i, :input_variable)],
              subpart(id, subpart(id, i, :input_mechanism), :target))
    end
    for i in parts(id, :InformationInput)
        push!(succ[subpart(id, i, :information_variable)],
              decision_variable(id, subpart(id, i, :information_decision)))
    end
    for p in parts(id, :DecisionPrecedence)
        push!(succ[decision_variable(id, subpart(id, p, :earlier))],
              decision_variable(id, subpart(id, p, :later)))
    end
    return succ
end

function _descendants(succ, start::Int)
    seen = falses(length(succ))
    stack = [start]
    while !isempty(stack)
        for t in succ[pop!(stack)]
            seen[t] && continue
            seen[t] = true
            push!(stack, t)
        end
    end
    return seen
end

# The no-forgetting violations of a valid diagram, as `NoForgettingError`s: decision `D_l`
# forgets when some decision `D_k` precedes it (a directed path from the action of `D_k` to
# the action of `D_l` in the information graph) and the information set of `D_l` lacks a
# variable of the information set of `D_k`, or the action of `D_k`. The order is the
# decision order of `InfluenceDiagrams`, then information-set order. On a diagram whose
# decisions are totally ordered by such paths this is that package's `no_forgetting_arcs`;
# decisions that no path orders, such as those of two diagrams side by side, owe each
# other nothing, which is what lets `otimes` preserve no-forgetting.
function _forgetting(id::AbstractInfluenceDiagram)
    ds = decision_order(id)
    succ = _successors(id)
    reach = Dict(d => _descendants(succ, decision_variable(id, d)) for d in ds)
    out = NoForgettingError[]
    for l in ds
        have = Set(decision_information(id, l))
        al = decision_variable(id, l)
        for k in ds
            k == l && continue
            reach[k][al] || continue
            for v in vcat(decision_information(id, k), decision_variable(id, k))
                v in have && continue
                push!(have, v)
                push!(out,
                      NoForgettingError(decision_name(id, l), variable_name(id, v),
                                        decision_name(id, k)))
            end
        end
    end
    return out
end

_has_no_forgetting(id::AbstractInfluenceDiagram) = isempty(_forgetting(id))

# Composite validation
######################

function _unique_named(id::AbstractInfluenceDiagram)
    return allunique(variable_names(id)) && allunique(mechanism_names(id)) &&
           allunique(decision_names(id)) && allunique(utility_names(id))
end

# Validate a composite of the diagrams `pieces`: rules 1 to 5, then rule 6. With
# `unique = true` names must be unique when every piece had unique names, so that a
# composite of `compose` or `glue` never silently carries two variables, mechanisms,
# decisions or utilities of one name; `otimes` and `oapply` keep repeated names, as they do
# for open networks.
function _validate_composite(o::OpenInfluenceDiagram, pieces; unique::Bool=true,
                             no_forgetting::Bool=true)
    validate(o; unique_names=unique && all(p -> _unique_named(apex(p)), pieces))
    no_forgetting || return nothing
    all(p -> _has_no_forgetting(apex(p)), pieces) || return nothing
    errs = _forgetting(apex(o))
    isempty(errs) || throw(first(errs))
    return nothing
end

# Sequential composition
########################

"""
    compose(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram; no_forgetting = true) -> OpenInfluenceDiagram
    A ⋅ B

Strict sequential composition. The output interface of `A` must equal the input interface
of `B` position by position: names, states with positions and references
(BayesianNetworks' `InterfaceMismatchError` names the first difference), then observability
([`ObservabilityMismatchError`](@ref)). Both diagrams are validated first. The result is a
Catlab pushout of the two apexes along the shared foot, with the inputs of `A` and the
outputs of `B` and their flags.

The composite is validated (see
[`validation_errors`](@ref validation_errors(::OpenInfluenceDiagram)); with unique names
when both pieces had them), then **rule 6**: when both components have no-forgetting, so
must the composite, or a [`NoForgettingError`](@ref) names the first decision that forgets
and the missing information arc. A decision of `B` that comes after a decision of `A` has to
know what that decision knew and did, and it can only learn it through observed interface
variables. Here, decision `D_k` precedes `D_l` when a directed path of causal, information or
precedence arcs runs from the action of `D_k` to the action of `D_l`, and no-forgetting asks
that the information set of `D_l` contain that of `D_k` and its action. For decisions that
such paths order totally this is `InfluenceDiagrams`' `is_no_forgetting`. With
`no_forgetting = false` rule 6 is skipped, and the result may be a limited-memory diagram,
which `ExhaustivePolicySearch` solves on the closed composite.

Unset references, `utility_ref` included, survive the pushout unchanged.
"""
function compose(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram;
                 no_forgetting::Bool=true)
    return first(_compose_cocone(A, B; no_forgetting=no_forgetting))
end

# `compose` with the cocone of its pushout: the composite and, for each operand, the map of
# its apex into the composite's (`_cocone_leg`), the witness of a colimit certificate.
function _compose_cocone(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram;
                         no_forgetting::Bool=true)
    validate(A)
    validate(B)
    _check_interfaces(output_space(A), A.output_observability, input_space(B),
                      B.input_observability, "compose: outputs(A) vs inputs(B)")
    cocone = Ref{Any}(nothing)
    C = _with_unset_refs_held(A.cospan, B.cospan) do a, b
        P, ia, ib = _pushout_along_maps(apex(a), _variable_component(right(a)), apex(b),
                                        _variable_component(left(b)))
        cocone[] = (ia, ib)
        cat = infer_acset_cat(P)
        cospan = Cospan(P, compose[cat](left(a), ia), compose[cat](right(b), ib))
        return force(_IDCospan(cospan, dom(a), codom(b)))
    end
    o = OpenInfluenceDiagram(C, A.input_observability, B.output_observability)
    _validate_composite(o, (A, B); no_forgetting=no_forgetting)
    return o, [_cocone_leg(f) for f in cocone[]]
end

# The components of a cocone map on the parts that carry a semantics.
function _cocone_leg(f)
    c = components(f)
    part(x) = Vector{Int}(collect(c[x]))
    return (Variable=part(:Variable), Mechanism=part(:Mechanism),
            Decision=part(:Decision), Utility=part(:Utility))
end

⋅(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram) = compose(A, B)

# Gluing
########

"""
    glue(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram; along, no_forgetting = true) -> OpenInfluenceDiagram

Glue selected outputs of `A` to selected inputs of `B`: each `a => b` in
`along::Vector{Pair{Symbol,Symbol}}` names an output variable of `A` and an input variable
of `B`, which must carry the same states (positions included), reference and observability,
but may differ in name (the glued variable keeps its name in `A`). BayesianNetworks'
`InterfaceMismatchError` reports a name that is not in the relevant interface, a variable
glued twice, or the first pair whose states or references differ, and
[`ObservabilityMismatchError`](@ref) a pair whose flags differ. A rename whose new name is
already taken in `apex(B)` is refused with BayesianNetworks' `NameClashError`.

The result has inputs `inputs(A)` followed by the unglued inputs of `B`, and outputs the
unglued outputs of `A` followed by `outputs(B)`, each with its flag. It is validated as a
composite, rule 6 included, exactly as for
[`compose`](@ref compose(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)). Both operands
are validated first, as `compose` validates them. Unlike the open-network `glue` this
matters: rule 3 concerns a component's own input foot, and gluing turns a glued input into
an internal variable, so a decision that reads a hidden input of `B` would otherwise pass
on the composite.
"""
function glue(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram;
              along::AbstractVector{<:Pair{Symbol,Symbol}}, no_forgetting::Bool=true)
    return first(_glue_cocone(A, B; along=along, no_forgetting=no_forgetting))
end

# `glue` with the cocone of its pushout and the operands as glued: `B` with its glued inputs
# renamed after their partners in `A` (`B` itself when nothing is renamed), whose apex the
# second map leaves.
function _glue_cocone(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram;
                      along::AbstractVector{<:Pair{Symbol,Symbol}}, no_forgetting::Bool=true)
    validate(A)
    validate(B)
    foreach(_require_attributes, (output_space(A), input_space(B)))
    outA, inB = outputs(A), inputs(B)
    ia, ib = Int[], Int[]
    for (k, (a, b)) in enumerate(along)
        i = findall(==(a), outA)
        isempty(i) &&
            throw(InterfaceMismatchError(:missing_output, k, a, nothing,
                                         "glue: $a is not an output of A"))
        length(i) > 1 && throw(DuplicateNameError(:Variable, a, i))
        j = findall(==(b), inB)
        isempty(j) &&
            throw(InterfaceMismatchError(:missing_input, k, nothing, b,
                                         "glue: $b is not an input of B"))
        length(j) > 1 && throw(DuplicateNameError(:Variable, b, j))
        only(i) in ia &&
            throw(InterfaceMismatchError(:duplicate, k, a, b,
                                         "glue: output $a of A is glued more than once"))
        only(j) in ib &&
            throw(InterfaceMismatchError(:duplicate, k, a, b,
                                         "glue: input $b of B is glued more than once"))
        d = _variable_difference(output_space(A), only(i), input_space(B), only(j);
                                 names=false)
        d === nothing ||
            throw(InterfaceMismatchError(d[1], k, d[2], d[3], "glue: along[$k] = $a => $b"))
        fa, fb = A.output_observability[only(i)], B.input_observability[only(j)]
        fa === fb ||
            throw(ObservabilityMismatchError(a, k, fa, fb, "glue: along[$k] = $a => $b"))
        push!(ia, only(i))
        push!(ib, only(j))
    end
    VA_out, VB_in = output_variables(A), input_variables(B)
    # A pushout cannot merge variables whose names differ, so the glued variables of B
    # take the names of their partners in A first, unless that name is taken in B.
    apB = apex(B)
    if any(a != b for (a, b) in along)
        renamed = copy(variable_names(apB))
        for ((a, _), j) in zip(along, ib)
            renamed[VB_in[j]] = a
        end
        for ((a, b), j) in zip(along, ib)
            a == b && continue
            count(==(a), renamed) == 1 ||
                throw(NameClashError(:Variable, a, b, "glue: along $a => $b"))
        end
        apB = deepcopy(apB)
        for (v, name) in zip(parts(apB, :Variable), renamed)
            set_subpart!(apB, v, :variable_name, name)
        end
    end
    cocone = Ref{Any}(nothing)
    P, mapA, mapB = _with_unset_refs_held(apex(A), apB) do a, b
        P, fa, fb = _pushout_along_maps(a, VA_out[ia], b, VB_in[ib])
        cocone[] = (fa, fb)
        return P, _variable_component(fa), _variable_component(fb)
    end
    B′ = apB === apex(B) ? B :
         OpenInfluenceDiagram(_cospan(apB, input_variables(B), output_variables(B)),
                              B.input_observability, B.output_observability)
    keep_a = setdiff(eachindex(outA), ia)
    keep_b = setdiff(eachindex(inB), ib)
    in_ids = vcat(mapA[input_variables(A)], mapB[VB_in[keep_b]])
    out_ids = vcat(mapA[VA_out[keep_a]], mapB[output_variables(B)])
    o = OpenInfluenceDiagram(_cospan(P, in_ids, out_ids),
                             vcat(A.input_observability, B.input_observability[keep_b]),
                             vcat(A.output_observability[keep_a], B.output_observability))
    _validate_composite(o, (A, B); no_forgetting=no_forgetting)
    return o, [_cocone_leg(f) for f in cocone[]], [A, B′]
end

# Tensor
########

"""
    otimes(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram; no_forgetting = true) -> OpenInfluenceDiagram
    A ⊗ B

Place two open influence diagrams side by side: the apex is the coproduct (disjoint union)
of the apexes, and the interfaces and their flags are concatenated, `A`'s first. Names are
kept, so tensoring a diagram with itself repeats them; the result is validated with
`unique_names = false`. Rule 6 always holds here: no path orders a decision of `A` against
one of `B`, so neither has anything to remember of the other.
"""
function otimes(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram; no_forgetting::Bool=true)
    return first(_otimes_cocone(A, B; no_forgetting=no_forgetting))
end

# `otimes` with the cocone of its coproduct.
function _otimes_cocone(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram;
                        no_forgetting::Bool=true)
    validate(A)
    validate(B)
    cocone = Ref{Any}(nothing)
    C = _with_unset_refs_held(A.cospan, B.cospan) do a, b
        cat = infer_acset_cat(apex(a))
        cp = coproduct[cat](apex(a), apex(b))
        ia, ib = legs(cp)
        cocone[] = (ia, ib)
        input_sum = coproduct[cat](dom(left(a)), dom(left(b)))
        output_sum = coproduct[cat](dom(right(a)), dom(right(b)))
        input_leg = copair[cat](input_sum, compose[cat](left(a), ia),
                                compose[cat](left(b), ib))
        output_leg = copair[cat](output_sum, compose[cat](right(a), ia),
                                 compose[cat](right(b), ib))
        return force(_IDCospan(Cospan(apex(cp), input_leg, output_leg),
                               otimes(dom(a), dom(b)), otimes(codom(a), codom(b))))
    end
    o = OpenInfluenceDiagram(C, vcat(A.input_observability, B.input_observability),
                             vcat(A.output_observability, B.output_observability))
    _validate_composite(o, (A, B); unique=false, no_forgetting=no_forgetting)
    return o, [_cocone_leg(f) for f in cocone[]]
end

⊗(A::OpenInfluenceDiagram, B::OpenInfluenceDiagram) = otimes(A, B)

"""
    otimes(X::OpenInfluenceDiagramOb, Y::OpenInfluenceDiagramOb) -> OpenInfluenceDiagramOb
    X ⊗ Y

The tensor of two interfaces: the variables of `X` followed by those of `Y`, with their
flags.
"""
function otimes(X::OpenInfluenceDiagramOb, Y::OpenInfluenceDiagramOb)
    vs = deepcopy(X.space)
    copy_parts!(vs, Y.space)
    return OpenInfluenceDiagramOb(vs, vcat(X.observability, Y.observability))
end

⊗(X::OpenInfluenceDiagramOb, Y::OpenInfluenceDiagramOb) = otimes(X, Y)

"""
    munit(::Type{OpenInfluenceDiagramOb}) -> OpenInfluenceDiagramOb

The monoidal unit: the empty interface.
"""
munit(::Type{OpenInfluenceDiagramOb}) = OpenInfluenceDiagramOb(VariableSpace(), Symbol[])

"""
    id(X::OpenInfluenceDiagramOb) -> OpenInfluenceDiagram

The identity on the interface `X`: an apex holding the variables of `X` and nothing else,
with both legs the identity and both feet flagged as in `X`. Composing with it changes a
diagram only up to isomorphism.
"""
function id(X::OpenInfluenceDiagramOb)
    ap = InfluenceDiagram()
    copy_parts!(ap, X.space)
    function leg()
        return OpenACSetLeg(X.space; Variable=collect(parts(X.space, :Variable)),
                            State=collect(parts(X.space, :State)))
    end
    o = OpenInfluenceDiagram(InfluenceDiagramCospan(ap, leg(), leg()), X.observability,
                             X.observability)
    validate(o)
    return o
end

# Undirected wiring diagrams
############################

# One leg per interface variable, inputs first, so that the diagram can sit in a box of an
# undirected wiring diagram; with the flag of each leg.
function _unbundle(o::OpenInfluenceDiagram)
    id = apex(o)
    ids = vcat(input_variables(o), output_variables(o))
    flags = vcat(o.input_observability, o.output_observability)
    return InfluenceDiagramCospan(id, (_leg(id, [v]) for v in ids)...), flags
end

"""
    oapply(uwd::UndirectedWiringDiagram, diagrams::Vector{<:OpenInfluenceDiagram};
           validate = true, no_forgetting = true) -> OpenInfluenceDiagram
    oapply(uwd::UndirectedWiringDiagram, diagrams::Dict{Symbol,<:OpenInfluenceDiagram}; kw...)

Compose open influence diagrams along an undirected wiring diagram (for example one written
with `@relation`). Box `i` receives `diagrams[i]` (or, for the dictionary form, the diagram
named like the box); its ports are the interface variables of the diagram, inputs first,
then outputs. Diagrams whose ports meet at a junction must agree there in variable, states
and reference (BayesianNetworks' `InterfaceMismatchError`, naming the junction) and in
observability ([`ObservabilityMismatchError`](@ref)). An outer port on a junction that no
box touches is refused with `InterfaceMismatchError(:missing_junction, ...)`. A box count
that differs from the number of diagrams raises `ArgumentError`.

Each junction carries one flag, and each port the flag of its variable on its foot. A
pass-through variable, one on both feet of a diagram, has two ports, an input port and an
output port, whose flags differ when the diagram flags the variable differently on its two
feet (see [`Open`](@ref Open(::InfluenceDiagram))). Wired to the same junction, the two
ports must agree like any two ports there, so different flags raise
[`ObservabilityMismatchError`](@ref). Wired to two junctions, each junction keeps its own
flag; the colimit joins them into one variable, since both ports name it, and an outer port
on either junction carries that junction's flag. Whether a decision may read the variable
is then decided on the composite by rule 3, and rule 6 is checked as for `compose`.

The apex is the colimit computed by Catlab's `oapply` for structured multicospans. The
inputs of the result are the outer-port variables without a generator (a mechanism or a
decision) and its outputs the others, in outer-port order, each with its junction's flag.
Undirected diagrams cannot express the typed-interface rule, so with `validate = true` each
diagram is validated first and the composite afterwards, as for
[`compose`](@ref compose(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)) but without
demanding unique names, rule 6 included unless `no_forgetting = false`. A junction that
receives two generated variables gives BayesianNetworks' `DuplicateGeneratorError` or
InfluenceDiagrams' `DecisionUniquenessError`, and a cycle `CyclicBayesNetError` or, through
an information arc, InfluenceDiagrams' `InvalidInformationSetError`.
"""
function oapply(uwd::UndirectedWiringDiagram,
                diagrams::AbstractVector{<:OpenInfluenceDiagram};
                validate::Bool=true, no_forgetting::Bool=true)
    return first(_oapply_cocone(uwd, diagrams; validate=validate,
                                no_forgetting=no_forgetting))
end

# `oapply` with the cocone of Catlab's colimit: the map of each box's apex into the
# composite's.
function _oapply_cocone(uwd::UndirectedWiringDiagram,
                        diagrams::AbstractVector{<:OpenInfluenceDiagram};
                        validate::Bool=true, no_forgetting::Bool=true)
    nboxes(uwd) == length(diagrams) ||
        throw(ArgumentError("oapply: the diagram has $(nboxes(uwd)) boxes but $(length(diagrams)) influence diagrams were given"))
    # The keyword `validate` shadows the function. Each diagram is validated as `compose`
    # validates its operands: rule 3 concerns a box's own input foot, which the colimit
    # may turn into internal variables that the composite no longer flags.
    validate && foreach(BayesianNetworks.validate, diagrams)
    foreach(d -> _require_attributes(apex(d)), diagrams)
    unbundled = map(_unbundle, diagrams)
    junction_feet = Dict{Int,VariableSpace}()
    junction_flags = Dict{Int,Symbol}()
    for (b, (m, flags)) in zip(boxes(uwd), unbundled)
        ps = ports(uwd, b)
        length(ps) == length(feet(m)) ||
            throw(InterfaceMismatchError(:length, b, length(feet(m)), length(ps),
                                         "oapply: interface variables of diagram $b vs ports of box $b"))
        for (p, f, fl) in zip(ps, feet(m), flags)
            j = junction(uwd, p)
            context = "oapply: junction $j (box $b, port $p)"
            if haskey(junction_feet, j)
                d = _interface_difference(junction_feet[j], f)
                d === nothing || throw(InterfaceMismatchError(d[1], j, d[3], d[4], context))
                junction_flags[j] === fl ||
                    throw(ObservabilityMismatchError(variable_name(f, 1), j,
                                                     junction_flags[j], fl, context))
            else
                junction_feet[j] = f
                junction_flags[j] = fl
            end
        end
    end
    outer_flags = Symbol[]
    for p in parts(uwd, :OuterPort)
        j = junction(uwd, p; outer=true)
        haskey(junction_feet, j) ||
            throw(InterfaceMismatchError(:missing_junction, j, _junction_name(uwd, j),
                                         nothing,
                                         "oapply: outer port $p is wired to junction $j$(_junction_suffix(uwd, j)), which no box touches"))
        push!(outer_flags, junction_flags[j])
    end
    cocone = Ref{Any}(nothing)
    R = _with_unset_refs_held(map(first, unbundled)) do us
        R, colim = oapply(uwd, us, nothing; return_colimit=true)
        cocone[] = legs(colim)[1:nboxes(uwd)]
        return R
    end
    P = apex(R)
    outer = Int[only(_variable_component(leg)) for leg in legs(R)]
    is_input = [!_has_generator(P, v) for v in outer]
    o = OpenInfluenceDiagram(_cospan(P, outer[is_input], outer[.!is_input]),
                             outer_flags[is_input], outer_flags[.!is_input])
    validate && _validate_composite(o, diagrams; unique=false, no_forgetting=no_forgetting)
    return o, [_cocone_leg(f) for f in cocone[]]
end

function oapply(uwd::UndirectedWiringDiagram,
                diagrams::AbstractDict{Symbol,<:OpenInfluenceDiagram}; kw...)
    names = Symbol.(subpart(uwd, :name))
    ordered = [haskey(diagrams, n) ? diagrams[n] :
               throw(ArgumentError("oapply: no influence diagram for box :$n"))
               for n in names]
    return oapply(uwd, ordered; kw...)
end

"""
    validate_composition(o::OpenInfluenceDiagram) -> Nothing

Post-hoc validation of a composite built without the typed-interface rule, such as the
result of [`oapply`](@ref oapply(::UndirectedWiringDiagram, ::AbstractVector{<:OpenInfluenceDiagram}))
with `validate = false`: the checks of
[`validate`](@ref validate(::OpenInfluenceDiagram)). Rule 6 needs the components, so only
the operations that receive them check it.
"""
validate_composition(o::OpenInfluenceDiagram) = validate(o)
