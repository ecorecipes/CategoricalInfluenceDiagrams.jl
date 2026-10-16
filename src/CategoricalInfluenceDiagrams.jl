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
  - **Semantics for a fixed strategy** (`src/semantics.jl`): [`RewardKernel`](@ref), the
    expectation-semiring kernel category over `FiniteKernels.jl`, and
    [`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy)),
    which maps an open influence diagram and a deterministic strategy to its reward
    kernel, functorially for `compose` and `otimes`.
  - **Optimisation, contextual and never isolated** (`src/optimization.jl`):
    [`optimize`](@ref optimize(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict))
    on a closed composite, and [`contextual_value`](@ref) and
    [`contextual_optimize`](@ref) on an open component against an explicit boundary prior
    and continuation value, with [`continuation_value`](@ref) and
    [`boundary_law`](@ref) the contexts a serial composite induces.

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
# The brute-force factor machinery that `CategoricalBayesianNetworks`' `interpret` uses,
# shared with it (see CLAUDE.md): none of it is `BayesianNetworks`' public interface.
using BayesianNetworks: DEFAULT_MAX_STATES, _Factor, _factors, _product, _joint_atol,
                        _resolve_kernel
using FiniteKernels: compose_kernel, tensor_kernel, identity_kernel, copy_kernel,
                     discard_kernel, swap_kernel, axis_names
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
import BayesianNetworks: validate, validation_errors, inputs, kernel
import InfluenceDiagrams: optimize
import CategoricalBayesianNetworks: Open, OpenBayesNet, outputs, input_space, output_space,
                                    input_variables, output_variables, left_leg, right_leg,
                                    glue, interface_matches, validate_composition, _acsets,
                                    interpret

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
       NoForgettingError, DuplicatePolicyError
# open.jl
export InfluenceDiagramCospanObUntyped, InfluenceDiagramCospanUntyped,
       InfluenceDiagramCospanOb, InfluenceDiagramCospan, OpenInfluenceDiagramOb,
       OpenInfluenceDiagram, OBSERVABILITY, structured_cospan, observability,
       input_observability, output_observability, observed_inputs, observed_outputs
# semantics.jl
export RewardKernel, reward, reward_matrix, identity_reward_kernel, copy_reward_kernel,
       discard_reward_kernel, swap_reward_kernel, merge_strategies
# optimization.jl
export contextual_value, contextual_optimize, continuation_value, boundary_law

include("errors.jl")
include("open.jl")
include("composition.jl")
include("semantics.jl")
include("optimization.jl")

end # module
