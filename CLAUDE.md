# CategoricalInfluenceDiagrams.jl

Open influence diagrams as structured cospans: influence diagrams with typed, observability-
flagged boundaries, and their composition (ADR 0018).

## Place in the ecosystem

Dependency order (arrows = depends on):
EcologicalBayesianNetworks → InfluenceDiagrams → BayesianNetworkInference → BayesianNetworks →
FiniteKernels, and BayesianNetworks → BayesianNetworkFormats (all Catlab-free);
CategoricalBayesianNetworks → BayesianNetworks, MarkovCategories (the Catlab layer).
This package sits on top of both halves: it depends on CategoricalBayesianNetworks (open
networks, Catlab) and InfluenceDiagrams (schema, policies, solvers), with Catlab and ACSets
directly, and nothing depends on it. It is the decision-layer analogue of
CategoricalBayesianNetworks: by ADR 0009 a module that needs Catlab lives in a categorical
package, so InfluenceDiagrams stays Catlab-free and CategoricalBayesianNetworks does not
take on the decision stack. Sibling packages are expected at `../<Name>.jl` (see `[sources]`
in Project.toml; the transitive siblings are listed too, because none is registered). Do not
edit them from here; record API gaps instead.

Every exported name of CategoricalBayesianNetworks and of InfluenceDiagrams is re-exported (a
loop over both `names` in the module). The two export no name with different bindings
(checked when the loop was written), so `using CategoricalInfluenceDiagrams` is a superset of
using both. Do not `using Catlab` wholesale in the module: Catlab and BayesianNetworks both
export `is_isomorphic`, `validate` and `to_graphviz`, and the parents' bindings must win.

## ADR 0018 invariants that must not be broken

- Structural syntax (ACSets) and numerical semantics (kernels, policies, utilities) stay
  separate; tables are never ACSet attributes. The semantics (`src/semantics.jl`) reads
  the tables through the apex's references, as `instantiate` does.
- Only variables cross a boundary. Decisions and utilities stay inside their component;
  reward crosses only through the semantics, as the `W` of a `RewardKernel`.
- The semantics for a fixed strategy (ADR 0018, decision 3) is the expectation-semiring
  kernel category: `RewardKernel(K, W)` with `K` a `FiniteKernel` and `W` a `Float64`
  table of exactly `K`'s shape (outputs first, then inputs). Composition is
  `(K₁K₂, W₁K₂ + K₁W₂)` and tensor `(K₁⊗K₂, W₁⊗K₂ + K₁⊗W₂)`; both are computed by
  `FiniteKernels`' `compose_kernel` and `tensor_kernel`, with `W` passed as an unchecked
  `FiniteKernel`. Never reimplement kernel arithmetic here. Identity, copy, discard and
  swap are lifted with zero reward; discard is not natural (`f ; discard` keeps `f`'s
  expected reward), which is the semantics, not a bug.
- `interpret(o, kernels, utilities, σ)` follows `CategoricalBayesianNetworks`'
  `interpret(::OpenBayesNet, kernels)` exactly: one axis per interface variable in
  interface order, outputs first, joint states with the first variable fastest, apex
  variables enumerated by part id, inputs held fixed (they have no mechanism). Kernels are
  keyed by `KernelRef` or target name as there; utilities by utility name or `utility_ref`.
  Policies are matched by decision name (equally named decisions share one), must be
  `DeterministicPolicy` or `ConstantPolicy` (a `StochasticPolicy` is an `ArgumentError`:
  ADR 0018 decision 4 keeps behavioural policies out of the first release), and a decision
  reading an observed input reads the input's state directly. A model's evidence is an
  `ArgumentError` (evidence composition is out of scope). `merge_strategies` is the
  disjoint union and raises `DuplicatePolicyError` on a name in two strategies.
- The feet are `VariableSpace`s, the same ACSets as CategoricalBayesianNetworks' feet. Never
  add observability to the feet schema: it lives beside the cospan in `OpenInfluenceDiagram`
  (`input_observability`, `output_observability`, one flag per interface position) and in
  `OpenInfluenceDiagramOb` (`observability`). Flags are `:observed` or `:hidden`; anything
  else is an `ArgumentError`. `Open` defaults to everything hidden, and an `OpenBayesNet`
  embeds all hidden. Glued interface variables must agree on flags
  (`ObservabilityMismatchError`), after names, states and references
  (BayesianNetworks' `InterfaceMismatchError`).
- The typed-interface rule (ADR 0018, decision 2), numbered as in the ADR:
  1. at most one generator (mechanism or decision) per variable: InfluenceDiagrams'
     validation (`DuplicateGeneratorError`, `DecisionUniquenessError`);
  2. no input has a generator: `DiagramInterfaceError(2, ...)`, kind `:mechanism` or
     `:decision`;
  3. a decision reads only internal or observed-input variables:
     `DiagramInterfaceError(3, ...)`, kind `:hidden_input`;
  4. utilities may read any apex variable (only a dangling reference fails,
     `DanglingReferenceError`);
  5. the causal-plus-information graph is acyclic: InfluenceDiagrams' validation
     (`CyclicBayesNetError`, `InvalidInformationSetError(:downstream)`,
     `DecisionPrecedenceCycleError`);
  6. composition preserves no-forgetting when the components have it: checked by every
     operation that builds a composite (`NoForgettingError(decision, variable, earlier)`),
     not by `validation_errors` of one diagram, since it concerns the components.
     `no_forgetting = false` opts out and yields a limited-memory composite.

  The open-network conditions that do not change keep CategoricalBayesianNetworks' errors:
  natural, attribute-preserving legs (`InterfaceError` 5), an injective input leg
  (`InterfaceError` 2), and every generator-free variable an input (`InterfaceError` 3).
- No-forgetting in rule 6 is read along the *precedence partial order*: `D_k` precedes `D_l`
  when a directed path of causal, information or precedence arcs runs from the action of
  `D_k` to the action of `D_l` (`_forgetting` in `src/composition.jl`). InfluenceDiagrams'
  `is_no_forgetting` linearises the decisions by `decision_order`, so two decisions no path
  orders count as forgetting there; under the partial order they owe each other nothing,
  which is what lets `otimes` preserve no-forgetting. The two agree when paths order the
  decisions totally. Decision variable elimination on a closed composite still needs the
  linear notion; `with_no_forgetting` or `ExhaustivePolicySearch` handle the rest.
- Nothing may construct an `OpenInfluenceDiagram` that bypasses `validate` except
  deliberately (`Open(...; validate = false)`, the inner constructor, or
  `oapply(...; validate = false)`), and every composite is validated again.
- Every operation takes its colimit with unset `Ref` attributes held by CategoricalBayesianNetworks'
  `_with_unset_refs_held`: `space_ref`, `kernel_ref` and, in an influence diagram,
  `utility_ref`. An unset reference is structurally valid and must stay unset.
- Every law of the semantics, and every optimised path, is checked against the
  closed-composite oracle (`instantiate` then `expected_utility`): `interpret` of a closed
  composite is `(1, EU)`. Keep `interpret` an independent brute-force enumeration; never
  short-cut it to `expected_utility`.
- Optimisation is contextual, never isolated (ADR 0018, decision 4). Never add an operation
  that optimises the components of a composite one by one and composes the results: the
  bundle refutes it (`INF-ISOLATED-OBSTRUCTION`), and `test_optimization.jl` reproduces the
  Lean witness (`1 < 4`). What exists: `optimize(o, kernels, utilities)` on a *closed*
  composite only (an open `o` is an `ArgumentError`), which binds the apex's tables into an
  `InfluenceDiagramModel` (`_closed_model`, resolving kernels with `BayesianNetworks`'
  `_resolve_kernel` and utilities with `_lookup_utility`) and calls `InfluenceDiagrams`'
  `optimize`; `contextual_value(o, ..., σ; prior, continuation)`,
  `EU_f(σ; μ, c) = Σ_x μ(x) Σ_y (W(y, x) + K(y | x) c(y))`; `contextual_optimize`; and the
  two contexts of a serial composite, `continuation_value` (`c_τ`, over `dom`) and
  `boundary_law` (`ν_σ = K μ`, over `codom`). Contexts are explicit: `prior` (a vector in
  `joint_states` order, nonnegative, summing to one within `atol` per entry, or a state
  kernel `I → X`) and `continuation` (a signed vector in `joint_states` order, or a
  `RewardKernel` `Y → I`) may be left out only for an empty interface, never defaulted to
  something else. `contextual_optimize` enumerates the legal deterministic strategies only
  (policies over each decision's declared information, so never a hidden input), in
  `decision_order` with the first decision fastest, and returns the first maximum as an
  `InfluenceDiagrams` `DecisionSolution` with diagnostics `(nstrategies, method)`; more
  than `max_policies` strategies raise `PolicySearchTooLargeError`, as in
  `ExhaustivePolicySearch`. Its default value table (`Σ μ(x) P_chance (U + c(y))` over the
  information and action variables) is checked against `brute_force = true`, which scores
  each strategy with `contextual_value` through `interpret`. Model forms read
  `kernels(m)`/`bound_utilities(m)` through the apex's references (so they need a diagram
  whose references are bound) and refuse evidence.

## Commands

```sh
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'   # the test suite
julia --project=docs docs/make.jl --no-deploy                     # build docs locally (strict)
cd vignettes && quarto render                                     # render vignettes (render each .qmd on its own to re-execute)
julia scripts/sync_vignettes.jl [--check]                         # copy vignettes into docs/src/tutorials
cd proofs && lake build --wfail && make audit && make docs        # the Lean project
```

Precompiling the package takes several minutes (Catlab's open-ACSet types over the
influence-diagram schema); later loads are fast.

## Layout

- `src/CategoricalInfluenceDiagrams.jl`: the module; the Catlab imports (by name), the
  re-export loop over both parents, and the `using CategoricalBayesianNetworks: ...` list of
  that package's internals this one builds on: `OpenBayesNetCospan`, `_foot`, `_leg`,
  `_leg_mismatches`, `_leg_is_natural`, `_variable_component`, `_state_component`,
  `_require_attributes`, `_with_unset_refs_held`, `_acsets` (extended here with methods for
  this package's types), `_interface_difference`, `_variable_difference`, `_junction_name`
  and `_junction_suffix`. They are not CategoricalBayesianNetworks' public interface; a
  change on either side has to be made on both. Likewise `BayesianNetworks`' brute-force
  factor machinery, which `CategoricalBayesianNetworks`' `interpret` also uses:
  `DEFAULT_MAX_STATES`, `_Factor` (whose fields `table`, `axes` and `strides` `_value`
  reads), `_factors`, `_product` and `_joint_atol`; and `_resolve_kernel`, the kernel
  lookup through a mechanism's reference that `optimize` uses to bind a closed composite's
  tables.
- `src/errors.jl`: `OpenInfluenceDiagramError <: BayesNetError` (ADR 0013, since the package
  defines several types) and its subtypes `ObservabilityMismatchError`,
  `DiagramInterfaceError`, `NoForgettingError` and `DuplicatePolicyError`, with
  `showerror` methods that name the variables and decisions; included first.
- `src/open.jl`: `InfluenceDiagramCospan(Ob)(Untyped)` from
  `OpenACSetTypes(InfluenceDiagramUntyped, VariableSpaceUntyped)`; `OBSERVABILITY`;
  `OpenInfluenceDiagramOb` (space plus flags); `OpenInfluenceDiagram{C}` (a two-footed
  `StructuredCospan` plus the flags of each foot); `Open(id; inputs, outputs, observed,
  validate)`; accessors (methods on Catlab's `apex`, `legs`, `feet`, `dom`, `codom` and on
  CategoricalBayesianNetworks' `inputs`, `outputs`, `input_space`, ...); the embedding
  `OpenInfluenceDiagram(::OpenBayesNet)` and its inverse `OpenBayesNet(::OpenInfluenceDiagram)`;
  and the typed-interface rule (`validation_errors`, `validate`, `isvalid`).
- `src/composition.jl`: `interface_matches` on interfaces with flags; the influence-diagram
  pushout `_pushout_along_maps`; rule 6 (`_forgetting`, `_validate_composite`); `compose`
  (`⋅`), `glue`, `otimes` (`⊗`, also on interfaces), `munit`, `id`, `oapply` (vector and
  dictionary forms) and `validate_composition`. `compose` and `glue` demand unique names
  when both pieces had them; `otimes` and `oapply` do not, as in CategoricalBayesianNetworks.
- `src/semantics.jl`: `RewardKernel` (accessors `kernel`, `reward`, `reward_matrix`,
  `dom`, `codom`; `==`, `hash`, `isapprox`), `compose` (`⋅`) and `otimes` (`⊗`) on reward
  kernels, `identity_reward_kernel`, `copy_reward_kernel`, `discard_reward_kernel`,
  `swap_reward_kernel`, `merge_strategies`, and `interpret` on an open influence diagram
  (dictionary and model forms). Tensoring two kernels `I → I` relies on `FiniteKernels`'
  `tensor_kernel` returning a rank-0 array (fixed there in `e78404a`).
- `src/optimization.jl`: `optimize` on a closed composite (dictionary and model forms;
  imported from `InfluenceDiagrams` and extended), `contextual_value`,
  `continuation_value` and `boundary_law` (each on a `RewardKernel` and, through
  `interpret`, on a diagram, dictionary and model forms), and `contextual_optimize`
  (value table or brute force).
- `test/runtests.jl`: `test_open.jl` (construction, accessors, flags, one failing case per
  rule, the Bayesian-network embedding; defines the umbrella split `umbrella_chance` and
  `umbrella_decision`), `test_composition.jl` (every operation; the umbrella, the SPEC §46
  grazing diagram at two boundaries and the two-stage diagram split and composed back to
  isomorphic diagrams; rules 1, 5 and 6 across boundaries; unset references),
  `test_semantics.jl` (the reward-kernel laws on random reward kernels; `interpret` against
  the closed-composite oracle under `compose`, `glue`, `otimes` and `oapply` on every
  strategy of the umbrella and two-stage oil-wildcatter splits, on the grazing splits and on
  seeded random diagrams cut into two and three pieces and placed side by side; identities,
  associativity, interchange, copy and discard through the syntax; defines
  `random_spec` and `random_pieces`), `test_optimization.jl` (the contextual identity in
  both forms on the umbrella, oil-wildcatter and grazing splits and on seeded random splits
  of two and three pieces; `optimize` on closed composites; `contextual_optimize` against
  brute force and the solvers, in both contextual orders; the bundle's Lean witness of
  `INF-ISOLATED-OBSTRUCTION`, `lean_early` and `lean_late`, giving `1 < 4`, and of
  `INF-HIDDEN-OBSTRUCTION`, where the pointwise value 2 needs a policy reading the hidden
  input and rule 3 rejects it), `test_errors.jl` (hierarchy, re-exports, frozen names,
  messages) and `test_docstrings.jl`.
- `proofs/`: the Lean project (see below).
- `vignettes/`: the quarto project: 01 open influence diagrams and composition, 02 a management decision composed with the zoo's `reference_habitat_bn` (MIT, built in), 03 why optimisation does not compose.

## Proofs

`proofs/` is a Lean/Mathlib/mdgen 4.30.0 project that requires the
`CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl` proof projects by relative path
(and through them the BayesianNetworks and FiniteKernels ones), sharing the workspace's
`../../.lake-packages`. `lake-manifest.json` was written by hand from the siblings' pins,
because the sandbox has no network; keep its revisions equal to theirs. Namespace
`OpenInfluence`, modules `Basic` (observability, information locality), `RewardKernel`,
`Category` (`FinRew` with Mathlib's symmetric monoidal copy-discard instances; discard is
not natural), `Context` (the contextual identity; its first equation needs the suffix
normalised), `Syntax` (`IDNet`: ADR 0010's open nets with decision labels and utility
generators), `Interpretation` (`interpret_comp`, `interpret_identity`, `interpret_tensor`)
and `Obstruction` (the isolated and hidden-input witnesses, as reward-kernel tables). The
restrictions in `proofs/README.md` ("Scope and restrictions") are part of every claim:
`IDNet` is not quotiented by isomorphism, so functoriality is equations on
representatives; the semantics does not read observability flags; nothing about arbitrary
gluing, evidence or the Julia-to-Lean refinement is proved. Every theorem sentence in
`proofs/README.md` is an SA-Pass claim (`cid.*` in the workspace
`conformance/sapass/claims.toml`, shadows in `CategoricalInfluenceDiagramsProofs/Shadows/`,
a `lean_lib` outside `defaultTargets`); change a sentence and its claim together. `make audit` checks every
`#print axioms` line of `Audit.lean` against `propext`, `Classical.choice` and `Quot.sound`,
scans the sources for escape hatches and runs the driver's guard regressions. The Lean CI
workflow checks out the four sibling repositories beside this one.

## Files not to edit by hand

- `docs/src/tutorials/` is generated by `scripts/sync_vignettes.jl`.
- `vignettes/*/*.md`, `*.html`, `*.pdf` and `*_files/` are quarto output; edit the `.qmd`.
- `docs/adr/` is copied from the workspace `docs/adr/` by `scripts/sync_adrs.jl`; edit the workspace copy.
- `proofs/CategoricalInfluenceDiagramsProofs.{md,html,pdf}` are generated from the Lean
  source by `make docs`.

## Style

JuliaFormatter `yas`; docstrings on every exported name, which `test/test_docstrings.jl` enforces; the docs
build is strict (no `warnonly`), so a docstring left out of the manual or a broken `@ref` fails it; typed
exceptions with variable names in the message, following ADR 0013 and ADR 0015: they live in `src/errors.jl` and
subtype `OpenInfluenceDiagramError <: BayesNetError`, invalid arguments and keywords raise `ArgumentError`,
typed errors from a lower package pass through unchanged and documented, and another package's type is named
as a code span, never with `@ref`; no emojis in code or docs.
