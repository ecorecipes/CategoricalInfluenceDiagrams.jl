"""
Open influence diagrams as structured cospans (ADR 0018, decision 2). The apex is an
`InfluenceDiagram` and the two feet are `VariableSpace`s, the same feet as those of an
`OpenBayesNet`. Catlab's `OpenACSetTypes` applies to `SchInfluenceDiagram` unchanged,
because every hom it adds to `SchBayesNet` points into `Variable`, `Decision` or `Utility`
and none leaves `Variable` or `State`.

Observability is stored beside the cospan, one flag per interface position, and not in the
feet: a foot is a `VariableSpace`, and adding an attribute to its schema would break the
interoperation with `CategoricalBayesianNetworks.jl`, whose feet are the same ACSets.
"""

const InfluenceDiagramCospanObUntyped, InfluenceDiagramCospanUntyped = OpenACSetTypes(InfluenceDiagramUntyped,
                                                                                      VariableSpaceUntyped)

@doc """
    InfluenceDiagramCospanObUntyped{Label, Position, Ref}

Object type of the structured cospans under an open influence diagram, with attribute types
left open (a Catlab `StructuredCospanOb` wrapping a `VariableSpaceUntyped`). See
[`InfluenceDiagramCospanOb`](@ref).
""" InfluenceDiagramCospanObUntyped

@doc """
    InfluenceDiagramCospanUntyped{Label, Position, Ref}

Morphism type of the structured cospans under an open influence diagram, with attribute
types left open (a Catlab `StructuredMulticospan` with an `InfluenceDiagramUntyped` apex).
See [`InfluenceDiagramCospan`](@ref).
""" InfluenceDiagramCospanUntyped

"""
    InfluenceDiagramCospanOb

`InfluenceDiagramCospanObUntyped{Symbol, Int, KernelRef}`: a `VariableSpace` wrapped as a
Catlab `StructuredCospanOb`, the interface object of the cospan that an
[`OpenInfluenceDiagram`](@ref) carries. It has no observability; the object of the category
of open influence diagrams is [`OpenInfluenceDiagramOb`](@ref).
"""
const InfluenceDiagramCospanOb = InfluenceDiagramCospanObUntyped{Symbol,Int,KernelRef}

"""
    InfluenceDiagramCospan

`InfluenceDiagramCospanUntyped{Symbol, Int, KernelRef}`: a Catlab structured (multi)cospan
whose apex is an `InfluenceDiagram` and whose feet are `VariableSpace`s, the analogue of
`OpenBayesNet`. [`structured_cospan`](@ref) returns the one an
[`OpenInfluenceDiagram`](@ref) carries.
"""
const InfluenceDiagramCospan = InfluenceDiagramCospanUntyped{Symbol,Int,KernelRef}

_discrete_functor(::Type{StructuredMulticospan{L}}) where {L} = L

# The functor L: VariableSpace -> InfluenceDiagram behind `InfluenceDiagramCospan`, and the
# two-footed subtype that an open influence diagram carries.
const _IDL = _discrete_functor(InfluenceDiagramCospan)
const _IDCospan = StructuredCospan{_IDL}

"""
    OBSERVABILITY

The two observability flags of an interface variable (ADR 0018, decision 2): `:observed`,
remembered information that a later decision may read, and `:hidden`, state that crosses
the boundary but that no decision on the far side may read.
"""
const OBSERVABILITY = (:observed, :hidden)

function _check_flags(flags::AbstractVector{Symbol}, n::Integer, side::AbstractString)
    length(flags) == n ||
        throw(ArgumentError("the $side foot has $n variables but $(length(flags)) observability flags"))
    for f in flags
        f in OBSERVABILITY ||
            throw(ArgumentError("observability flag :$f on the $side foot is neither :observed nor :hidden"))
    end
    return nothing
end

"""
    OpenInfluenceDiagramOb(space::VariableSpace, observability::Vector{Symbol})

An object of the category of open influence diagrams: an interface, that is a
`VariableSpace` together with one [`OBSERVABILITY`](@ref) flag per variable, in interface
order. `dom(o)` and `codom(o)` of an [`OpenInfluenceDiagram`](@ref) return one; its fields
`space` and `observability` are the interface and its flags. Two objects are equal when
their spaces and flags are. Building one with a flag that is not `:observed` or `:hidden`,
or with a number of flags other than the number of variables, raises `ArgumentError`.
"""
struct OpenInfluenceDiagramOb
    space::VariableSpace
    observability::Vector{Symbol}
    function OpenInfluenceDiagramOb(space::VariableSpace,
                                    observability::AbstractVector{Symbol})
        _check_flags(observability, nparts(space, :Variable), "interface")
        return new(space, collect(Symbol, observability))
    end
end

function Base.:(==)(a::OpenInfluenceDiagramOb, b::OpenInfluenceDiagramOb)
    return a.space == b.space && a.observability == b.observability
end

# Hashes the names and flags only, which equal interfaces share, so that `hash` agrees with
# `==` whatever the ACSet's own hash.
function Base.hash(a::OpenInfluenceDiagramOb, h::UInt)
    return hash((variable_names(a.space), a.observability),
                hash(:OpenInfluenceDiagramOb, h))
end

"""
    observability(X::OpenInfluenceDiagramOb) -> Vector{Symbol}

The [`OBSERVABILITY`](@ref) flags of the interface `X`, in interface order.
"""
observability(X::OpenInfluenceDiagramOb) = X.observability

"""
    OpenInfluenceDiagram

An open influence diagram (ADR 0018, decision 2): a Catlab structured cospan
([`InfluenceDiagramCospan`](@ref)) whose apex is an `InfluenceDiagram` and whose two feet
are `VariableSpace`s, together with an [`OBSERVABILITY`](@ref) flag for every variable of
each foot. Build one with [`Open`](@ref Open(::InfluenceDiagram)), or embed an
`OpenBayesNet` with `OpenInfluenceDiagram(o::OpenBayesNet)`; combine with
[`compose`](@ref compose(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)),
[`glue`](@ref glue(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)),
[`otimes`](@ref otimes(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)) and
[`oapply`](@ref oapply(::UndirectedWiringDiagram, ::AbstractVector{<:OpenInfluenceDiagram})).
Inspect with `apex`, `legs`, `feet`, `dom`, `codom`, `inputs`, `outputs`, `input_space`,
`output_space`, `input_variables`, `output_variables`, `left_leg`, `right_leg`,
[`input_observability`](@ref), [`output_observability`](@ref), [`observed_inputs`](@ref),
[`observed_outputs`](@ref) and [`structured_cospan`](@ref).

Only variables cross the boundary: decisions and utilities stay inside their component.

The inner constructor `OpenInfluenceDiagram(cospan, input_observability,
output_observability)` checks only that there is one flag per foot variable and that each
is `:observed` or `:hidden` (`ArgumentError` otherwise); it does not check the
typed-interface rule, which [`validate`](@ref validate(::OpenInfluenceDiagram)) does.
"""
struct OpenInfluenceDiagram{C<:_IDCospan}
    cospan::C
    input_observability::Vector{Symbol}
    output_observability::Vector{Symbol}
    function OpenInfluenceDiagram(cospan::C, input_observability::AbstractVector{Symbol},
                                  output_observability::AbstractVector{Symbol}) where {C<:_IDCospan}
        fin, fout = feet(cospan)
        _check_flags(input_observability, nparts(fin, :Variable), "input")
        _check_flags(output_observability, nparts(fout, :Variable), "output")
        return new{C}(cospan, collect(Symbol, input_observability),
                      collect(Symbol, output_observability))
    end
end

function Base.:(==)(a::OpenInfluenceDiagram, b::OpenInfluenceDiagram)
    return a.cospan == b.cospan && a.input_observability == b.input_observability &&
           a.output_observability == b.output_observability
end

# Equal diagrams have equal interface names and flags; hashing those keeps `hash` consistent
# with `==` without relying on a structural hash of Catlab's cospans.
function Base.hash(a::OpenInfluenceDiagram, h::UInt)
    return hash((inputs(a), outputs(a), a.input_observability, a.output_observability),
                hash(:OpenInfluenceDiagram, h))
end

# Construction
##############

# The structured cospan with feet on the apex variables `in_ids` and `out_ids`, in R-form.
function _cospan(id::InfluenceDiagram, in_ids::AbstractVector{<:Integer},
                 out_ids::AbstractVector{<:Integer})
    return InfluenceDiagramCospan(id, _leg(id, in_ids), _leg(id, out_ids))
end

"""
    Open(id::InfluenceDiagram; inputs = Symbol[], outputs = Symbol[], observed = Symbol[],
         validate = true) -> OpenInfluenceDiagram
    Open(id::InfluenceDiagram, inputs, outputs; observed = Symbol[], validate = true)

Make `id` an open influence diagram with the named variables as input and output
interfaces, in the given order. Each foot is a `VariableSpace` copying the variables' names,
references and states (with positions), exactly as for an `OpenBayesNet`. Names may repeat
in `outputs` (an implicit copy) but not in `inputs`.

`observed` names the interface variables that are `:observed`: remembered information that
a decision may read. Every other interface variable is `:hidden`. It takes two forms.

- A vector of names. A name in it is observed on every foot it appears on, and a name that
  is on neither foot raises `ArgumentError`.
- A named tuple `(inputs = [...], outputs = [...])`, either field optional (default
  empty), which flags each foot separately: the names in `observed.inputs` are observed on
  the input foot, those in `observed.outputs` on the output foot. A name in
  `observed.inputs` that is not an input, or in `observed.outputs` that is not an output,
  raises `ArgumentError` naming them, as does any other field or an entry that is not a
  `Symbol`. The vector `[n...]` is the named tuple that lists each `n` on every foot it is
  on.

**The default is that everything is hidden.** It is the conservative choice: a decision may
never read a hidden input (rule 3), so an interface carries information only where it says
so, and an `OpenBayesNet` embeds with every variable hidden.

Per-foot flags matter for a pass-through variable, one on both feet:

- *observed on the input foot, hidden on the output foot*: the boundary forgets the
  variable. The component's decisions may read it, but a decision downstream cannot, since
  the next component must take it hidden to match (or [`ObservabilityMismatchError`](@ref))
  and rule 3 then forbids reading it. If such a decision comes after one that read the
  variable, the composite fails rule 6 ([`NoForgettingError`](@ref)).
- *hidden on the input foot, observed on the output foot*: the component reveals the
  variable, as a perfect observation made inside the component, and a downstream decision
  may read it. The component's own decisions still may not, since rule 3 is about inputs.
  Composites are validated again, so a decision downstream still cannot read the variable
  when a composite's input foot hides it: `compose(R, B)`, with `R` revealing `X` to a
  decision of `B` that reads it, fails rule 3 on the composite, because `X` is a hidden
  input of `R ⋅ B`; composed after a component that generates `X`, it is internal and
  legal.

With `validate = true` the typed-interface rule is checked (see
[`validate`](@ref validate(::OpenInfluenceDiagram))) and the first violation thrown. An
unknown name raises BayesianNetworks' `UnknownVariableError`.

# Example

```jldoctest
julia> id = influence_diagram(:Weather => [:sunny, :rainy],
                              :Forecast => [:sunny, :cloudy, :rainy],
                              :Umbrella => [:take, :leave];
                              decisions = [:Umbrella => :Forecast],
                              utilities = [:U => (:Weather, :Umbrella)], closed = false);

julia> B = Open(id; inputs = [:Weather, :Forecast], observed = [:Forecast]);

julia> inputs(B), input_observability(B)
([:Weather, :Forecast], [:hidden, :observed])

julia> R = Open(influence_diagram(:X => [:a, :b]; closed = false);
                inputs = [:X], outputs = [:X], observed = (outputs = [:X],));

julia> input_observability(R), output_observability(R)
([:hidden], [:observed])
```
"""
function Open(id::InfluenceDiagram; inputs::AbstractVector{Symbol}=Symbol[],
              outputs::AbstractVector{Symbol}=Symbol[],
              observed::Union{AbstractVector{Symbol},NamedTuple}=Symbol[],
              validate::Bool=true)
    in_flags, out_flags = _observed_flags(observed, inputs, outputs)
    in_ids = [variable_id(id, n) for n in inputs]
    out_ids = [variable_id(id, n) for n in outputs]
    o = OpenInfluenceDiagram(_cospan(id, in_ids, out_ids), in_flags, out_flags)
    validate && _validate_open(o)
    return o
end

# The flags of the two feet that `Open`'s `observed` declares. A vector observes a name on
# every foot it is on; a named tuple `(inputs = ..., outputs = ...)` names the observed
# variables of each foot separately.
function _observed_flags(observed::AbstractVector{Symbol}, inputs, outputs)
    for n in observed
        (n in inputs || n in outputs) ||
            throw(ArgumentError("Open: observed variable :$n is neither an input nor an output"))
    end
    flag(n) = n in observed ? :observed : :hidden
    return map(flag, inputs), map(flag, outputs)
end

function _observed_flags(observed::NamedTuple, inputs, outputs)
    extra = [k for k in keys(observed) if !(k in (:inputs, :outputs))]
    isempty(extra) ||
        throw(ArgumentError("Open: observed has the fields $extra; a named tuple takes only `inputs` and `outputs`"))
    return (_foot_flags(get(observed, :inputs, Symbol[]), inputs, :inputs, "an input"),
            _foot_flags(get(observed, :outputs, Symbol[]), outputs, :outputs, "an output"))
end

# The flags of one foot whose observed variables are `names`.
function _foot_flags(names, foot::AbstractVector{Symbol}, side::Symbol,
                     what::AbstractString)
    (names isa AbstractVector && all(n -> n isa Symbol, names)) ||
        throw(ArgumentError("Open: observed.$side must be a vector of variable names, got $(repr(names))"))
    stray = Symbol[n for n in names if !(n in foot)]
    isempty(stray) ||
        throw(ArgumentError("Open: observed.$side names $stray, each of which is not $what"))
    return [n in names ? :observed : :hidden for n in foot]
end

function Open(id::InfluenceDiagram, inputs::AbstractVector{Symbol},
              outputs::AbstractVector{Symbol}; kw...)
    return Open(id; inputs=inputs, outputs=outputs, kw...)
end

# Accessors
###########

"""
    structured_cospan(o::OpenInfluenceDiagram) -> InfluenceDiagramCospan

The Catlab structured cospan of `o`, without its observability flags.
"""
structured_cospan(o::OpenInfluenceDiagram) = o.cospan

"""
    apex(o::OpenInfluenceDiagram) -> InfluenceDiagram

The apex of `o`: the influence diagram whose variables the feet name.
"""
apex(o::OpenInfluenceDiagram) = apex(o.cospan)

"""
    legs(o::OpenInfluenceDiagram)

The two legs of `o`, input first: Catlab `ACSetTransformation`s from the (L-form) feet into
the apex.
"""
legs(o::OpenInfluenceDiagram) = legs(o.cospan)

"""
    feet(o::OpenInfluenceDiagram)

The two feet of `o`, input first, as `VariableSpace`s.
"""
feet(o::OpenInfluenceDiagram) = feet(o.cospan)

"""
    dom(o::OpenInfluenceDiagram) -> OpenInfluenceDiagramOb
    codom(o::OpenInfluenceDiagram) -> OpenInfluenceDiagramOb

The input (`dom`) and output (`codom`) interface of `o`, with its observability flags.
"""
dom(o::OpenInfluenceDiagram) = OpenInfluenceDiagramOb(input_space(o), o.input_observability)
function codom(o::OpenInfluenceDiagram)
    return OpenInfluenceDiagramOb(output_space(o), o.output_observability)
end

"""
    input_space(o::OpenInfluenceDiagram) -> VariableSpace
    output_space(o::OpenInfluenceDiagram) -> VariableSpace

The input (left) and output (right) foot of `o`.
"""
input_space(o::OpenInfluenceDiagram) = first(feet(o))
output_space(o::OpenInfluenceDiagram) = last(feet(o))

"""
    inputs(o::OpenInfluenceDiagram) -> Vector{Symbol}
    outputs(o::OpenInfluenceDiagram) -> Vector{Symbol}

Names of the input and output variables of `o`, in interface order.
"""
inputs(o::OpenInfluenceDiagram) = variable_names(input_space(o))
outputs(o::OpenInfluenceDiagram) = variable_names(output_space(o))

"""
    left_leg(o::OpenInfluenceDiagram)
    right_leg(o::OpenInfluenceDiagram)

The legs embedding the input and output foot into the apex (Catlab's `left` and `right`).
"""
left_leg(o::OpenInfluenceDiagram) = left(o.cospan)
right_leg(o::OpenInfluenceDiagram) = right(o.cospan)

"""
    input_variables(o::OpenInfluenceDiagram) -> Vector{Int}
    output_variables(o::OpenInfluenceDiagram) -> Vector{Int}

Apex part ids of the input and output variables, in interface order.
"""
input_variables(o::OpenInfluenceDiagram) = _variable_component(left(o.cospan))
output_variables(o::OpenInfluenceDiagram) = _variable_component(right(o.cospan))

"""
    input_observability(o::OpenInfluenceDiagram) -> Vector{Symbol}

The [`OBSERVABILITY`](@ref) flag of each input variable of `o`, in interface order.
"""
input_observability(o::OpenInfluenceDiagram) = o.input_observability

"""
    output_observability(o::OpenInfluenceDiagram) -> Vector{Symbol}

The [`OBSERVABILITY`](@ref) flag of each output variable of `o`, in interface order.
"""
output_observability(o::OpenInfluenceDiagram) = o.output_observability

"""
    observed_inputs(o::OpenInfluenceDiagram) -> Vector{Symbol}

Names of the input variables of `o` that are `:observed`, in interface order: the inputs a
decision of `o` may read.
"""
function observed_inputs(o::OpenInfluenceDiagram)
    return [n for (n, f) in zip(inputs(o), o.input_observability) if f === :observed]
end

"""
    observed_outputs(o::OpenInfluenceDiagram) -> Vector{Symbol}

Names of the output variables of `o` that are `:observed`, in interface order: the outputs
a decision downstream of `o` may read.
"""
function observed_outputs(o::OpenInfluenceDiagram)
    return [n for (n, f) in zip(outputs(o), o.output_observability) if f === :observed]
end

function Base.show(io::IO, o::OpenInfluenceDiagram)
    id = apex(o)
    flagged(ns, fs) = [f === :observed ? Symbol(n, "!") : n for (n, f) in zip(ns, fs)]
    return print(io, "OpenInfluenceDiagram(", nparts(id, :Variable), " variables, ",
                 nparts(id, :Mechanism), " mechanisms, ", nparts(id, :Decision),
                 " decisions, ", nparts(id, :Utility), " utilities; ",
                 flagged(inputs(o), o.input_observability), " -> ",
                 flagged(outputs(o), o.output_observability), ")")
end

# Embedding of open Bayesian networks
#####################################

# The leg, in R-form, from `foot` into an apex whose parts have the ids they have in the
# codomain of `l`: the embedding and its inverse keep every part id.
function _copy_leg(l, foot::VariableSpace)
    return OpenACSetLeg(foot; Variable=_variable_component(l), State=_state_component(l))
end

"""
    OpenInfluenceDiagram(o::OpenBayesNet; validate = true) -> OpenInfluenceDiagram

The open Bayesian network `o` as an open influence diagram with no decisions and no
utilities, and with every interface variable `:hidden` (ADR 0018, Consequences). The apex
is `InfluenceDiagram(apex(o))`, whose parts keep their ids, and the feet are those of `o`.
`OpenBayesNet` of the result gives back `o`. With `validate = true` the typed-interface rule
is checked.
"""
function OpenInfluenceDiagram(o::OpenBayesNetCospan; validate::Bool=true)
    id = InfluenceDiagram(apex(o))
    fin, fout = feet(o)
    c = InfluenceDiagramCospan(id, _copy_leg(left(o), fin), _copy_leg(right(o), fout))
    d = OpenInfluenceDiagram(c, fill(:hidden, nparts(fin, :Variable)),
                             fill(:hidden, nparts(fout, :Variable)))
    validate && _validate_open(d)
    return d
end

"""
    OpenBayesNet(o::OpenInfluenceDiagram) -> OpenBayesNet

The open Bayesian network underlying `o`, which must have no decisions, utilities or
precedence rows (`ArgumentError` otherwise, naming them): the apex is `BayesNet(apex(o))`,
whose parts keep their ids, and the feet are those of `o`. Observability flags are dropped;
in a diagram without decisions no variable is read as information. This inverts
[`OpenInfluenceDiagram(o::OpenBayesNet)`](@ref OpenInfluenceDiagram(::CategoricalBayesianNetworks.OpenBayesNetCospan)).
"""
function OpenBayesNet(o::OpenInfluenceDiagram)
    id = apex(o)
    nparts(id, :Decision) == 0 ||
        throw(ArgumentError("OpenBayesNet: the diagram has decisions $(decision_names(id))"))
    nparts(id, :Utility) == 0 ||
        throw(ArgumentError("OpenBayesNet: the diagram has utilities $(utility_names(id))"))
    nparts(id, :DecisionPrecedence) == 0 ||
        throw(ArgumentError("OpenBayesNet: the diagram has decision precedence rows"))
    bn = BayesNet(id)
    fin, fout = feet(o)
    return OpenBayesNet(bn, _copy_leg(left_leg(o), fin), _copy_leg(right_leg(o), fout))
end

# Typed-interface rule
######################

# Whether variable `v` of `id` has a generator: a chance mechanism or a decision.
function _has_generator(id::AbstractInfluenceDiagram, v::Integer)
    return !isempty(incident(id, v, :target)) ||
           !isempty(incident(id, v, :decision_variable))
end

# The interface rules of an open influence diagram whose apex has passed its structural
# checks, appended to `errs` in this order: the legs are natural and attribute-preserving
# (`InterfaceError` 5, as for an open network); the input leg is injective
# (`InterfaceError` 2); rule 2 (no input has a generator); every generator-free variable is
# an input (`InterfaceError` 3); rule 3 (no decision reads a hidden input). The last three
# are checked only when the legs are natural.
function _check_interface!(errs, o::OpenInfluenceDiagram)
    id = apex(o)
    natural = true
    for (leg, foot) in ((left_leg(o), input_space(o)), (right_leg(o), output_space(o)))
        bad = _leg_mismatches(leg, foot, id)
        if !isempty(bad) || !_leg_is_natural(leg, foot)
            isempty(bad) && (bad = collect(parts(foot, :Variable)))
            push!(errs, InterfaceError(5, variable_name.(Ref(foot), bad), bad))
            natural = false
        end
    end
    natural || return errs
    in_ids = input_variables(o)
    seen = Dict{Int,Int}()
    dup = Int[]
    for (i, w) in enumerate(in_ids)
        haskey(seen, w) ? push!(dup, i) : (seen[w] = i)
    end
    isempty(dup) ||
        push!(errs, InterfaceError(2, variable_name.(Ref(input_space(o)), dup), dup))
    for w in unique(in_ids)
        for m in incident(id, w, :target)
            push!(errs,
                  DiagramInterfaceError(2, variable_name(id, w), mechanism_name(id, m),
                                        :mechanism))
        end
        for d in incident(id, w, :decision_variable)
            push!(errs,
                  DiagramInterfaceError(2, variable_name(id, w), decision_name(id, d),
                                        :decision))
        end
    end
    free = filter(v -> !haskey(seen, v) && !_has_generator(id, v), parts(id, :Variable))
    isempty(free) || push!(errs, InterfaceError(3, variable_name.(Ref(id), free), free))
    hidden = Set(w for (w, f) in zip(in_ids, o.input_observability) if f === :hidden)
    for d in parts(id, :Decision), v in decision_information(id, d)
        v in hidden &&
            push!(errs,
                  DiagramInterfaceError(3, variable_name(id, v), decision_name(id, d),
                                        :hidden_input))
    end
    return errs
end

"""
    validation_errors(o::OpenInfluenceDiagram; unique_names = false) -> Vector{Exception}

All problems of the open influence diagram `o` under the typed-interface rule of ADR 0018
(decision 2), without stopping at the first. The structural checks of the apex come first
(`InfluenceDiagrams`' `validation_errors`, always with `closed = false`, since an input has
no generator); they cover rules 1, 4 and 5:

1. every variable has at most one generator, a chance mechanism or a decision
   (`DuplicateGeneratorError`, `DecisionUniquenessError`);
4. a utility scope may read any apex variable, inputs included; it may not read a variable
   that is not in the apex (`DanglingReferenceError`);
5. the causal-plus-information graph is acyclic (`CyclicBayesNetError`,
   `InvalidInformationSetError` with reason `:downstream`, `DecisionPrecedenceCycleError`).

Then the interface checks, which are skipped when the apex has a `DanglingReferenceError`
or a `MissingAttributeError`. The legs must be natural and preserve names, references and
states (`InterfaceError` 5), and the input leg injective (`InterfaceError` 2), as for an
open Bayesian network. Then

2. an input-foot variable has no generator in the apex ([`DiagramInterfaceError`](@ref)
   with rule 2);
   - and every variable without a generator is an input (`InterfaceError` 3, as for an
     open network: an action variable has a generator, its decision);
3. a decision's information inputs are internal variables or *observed* input-foot
   variables ([`DiagramInterfaceError`](@ref) with rule 3).

Rule 6, that composition preserves no-forgetting, concerns a composite and its components,
not one diagram, and is checked by the operations that build composites (see
[`compose`](@ref compose(::OpenInfluenceDiagram, ::OpenInfluenceDiagram))). An output
variable may be declared observed or hidden freely: whether a later decision may read it is
decided by the flag, not by where it came from.
"""
function validation_errors(o::OpenInfluenceDiagram; unique_names::Bool=false)
    errs = validation_errors(apex(o); closed=false, unique_names=unique_names)
    any(e -> e isa Union{DanglingReferenceError,MissingAttributeError}, errs) &&
        return errs
    _check_interface!(errs, o)
    return errs
end

"""
    validate(o::OpenInfluenceDiagram; unique_names = false) -> Nothing

Throw the first entry of
[`validation_errors`](@ref validation_errors(::OpenInfluenceDiagram)), if any.
"""
function validate(o::OpenInfluenceDiagram; kw...)
    errs = validation_errors(o; kw...)
    isempty(errs) || throw(first(errs))
    return nothing
end

_validate_open(o::OpenInfluenceDiagram) = validate(o)

"""
    isvalid(o::OpenInfluenceDiagram; unique_names = false) -> Bool

Whether [`validation_errors`](@ref validation_errors(::OpenInfluenceDiagram)) is empty.
"""
Base.isvalid(o::OpenInfluenceDiagram; kw...) = isempty(validation_errors(o; kw...))
