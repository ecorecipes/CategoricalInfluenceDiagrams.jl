"""
    CategoricalInfluenceDiagrams

Open influence diagrams as structured cospans (ADR 0018). This is the decision-layer
analogue of `CategoricalBayesianNetworks.jl`: it adds to `InfluenceDiagrams.jl`, which stays
Catlab-free (ADR 0009), the open-system machinery of the categorical layer.

  - **Open diagrams** (`src/open.jl`): [`OpenInfluenceDiagram`](@ref), a Catlab structured
    cospan with an `InfluenceDiagram` apex and `VariableSpace` feet, the feet being the same
    type as those of an open Bayesian network. Every interface variable is also declared
    `:observed` (remembered information a later decision may read) or `:hidden`. The
    typed-interface rule of open Bayesian networks is extended to decisions and utilities
    and checked by [`validation_errors`](@ref validation_errors(::OpenInfluenceDiagram)).
    An `OpenBayesNet` embeds with every interface variable `:hidden`.
  - **Composition** (`src/composition.jl`):
    [`compose`](@ref compose(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)),
    [`glue`](@ref glue(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)),
    [`otimes`](@ref otimes(::OpenInfluenceDiagram, ::OpenInfluenceDiagram)) and
    [`oapply`](@ref oapply(::UndirectedWiringDiagram, ::AbstractVector{<:OpenInfluenceDiagram})),
    each a pushout or coproduct of ACSets, with the rule (including its no-forgetting
    clause) checked again on the composite.

Every exported name of `CategoricalBayesianNetworks` and `InfluenceDiagrams` is re-exported,
so `using CategoricalInfluenceDiagrams` is a superset of using both.

Part of the ecorecipes compositional Bayesian-network ecosystem.
"""
module CategoricalInfluenceDiagrams

using Catlab.CategoricalAlgebra: StructuredCospan, StructuredMulticospan,
                                 StructuredCospanOb, OpenACSetTypes, OpenACSetLeg, left,
                                 right, force, components, infer_acset_cat, pushout,
                                 Cospan, coproduct, copair, ACSetTransformation
using Catlab.WiringDiagrams: UndirectedWiringDiagram, nboxes, boxes, ports, junction
using ACSets
using BayesianNetworks
using BayesianNetworks: AbstractVariableSpace, BayesNetUntyped, VariableSpace,
                        VariableSpaceUntyped, BayesNetError, InterfaceError,
                        InterfaceMismatchError, NameClashError, DuplicateNameError,
                        DanglingReferenceError, MissingAttributeError
using CategoricalBayesianNetworks
using InfluenceDiagrams
# Imported by name: the internals of `CategoricalBayesianNetworks.jl` that this package
# builds on, as that package builds on `BayesianNetworks`' internals. They are the foot and
# leg builders, the leg checks of its typed-interface rule, the interface comparison and the
# handling of unset references in colimits. None is part of that package's public
# interface; a change on either side has to be made on both (see CLAUDE.md).
using CategoricalBayesianNetworks: OpenBayesNetCospan, _foot, _leg, _leg_mismatches,
                                   _leg_is_natural, _variable_component, _state_component,
                                   _require_attributes, _with_unset_refs_held,
                                   _interface_difference, _variable_difference,
                                   _junction_name, _junction_suffix

import Catlab.Theories: compose, otimes, munit, dom, codom, id, ⋅, ⊗
import Catlab.CategoricalAlgebra: apex, legs, feet
import Catlab.WiringDiagrams: oapply
import BayesianNetworks: validate, validation_errors, inputs
import CategoricalBayesianNetworks: Open, OpenBayesNet, outputs, input_space, output_space,
                                    input_variables, output_variables, left_leg, right_leg,
                                    glue, interface_matches, validate_composition, _acsets

# Re-exported names of the two parent packages, so that `using CategoricalInfluenceDiagrams`
# is a superset of `using CategoricalBayesianNetworks` and `using InfluenceDiagrams`. The two
# export no name with different bindings, and every exception type keeps its owner's
# binding: `ImpossibleEvidenceError`, `IrregularDiagramError` and `ScopeError` print
# unqualified, as the frozen checkers need (ADR 0013).
for M in (CategoricalBayesianNetworks, InfluenceDiagrams)
    for name in setdiff(names(M), [nameof(M)])
        @eval export $name
    end
end

# errors.jl
export OpenInfluenceDiagramError, ObservabilityMismatchError, DiagramInterfaceError,
       NoForgettingError
# open.jl
export InfluenceDiagramCospanObUntyped, InfluenceDiagramCospanUntyped,
       InfluenceDiagramCospanOb, InfluenceDiagramCospan, OpenInfluenceDiagramOb,
       OpenInfluenceDiagram, OBSERVABILITY, structured_cospan, observability,
       input_observability, output_observability, observed_inputs, observed_outputs

include("errors.jl")
include("open.jl")
include("composition.jl")

end # module
