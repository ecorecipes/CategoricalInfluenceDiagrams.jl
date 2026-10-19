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
  embeds all hidden. `Open`'s `observed` is a vector (a name is observed on every foot it
  is on; this meaning is fixed) or a named tuple `(inputs = [...], outputs = [...])`, either
  field optional, flagging each foot separately (a name in `observed.inputs` that is not an
  input, or in `observed.outputs` that is not an output, is an `ArgumentError` naming
  them; so is any other field). Never add keywords `observed_inputs`/`observed_outputs`:
  those are exported accessors. For a pass-through variable: observed on input and hidden
  on output, the boundary forgets it (a later decision cannot read it, and rule 6 catches
  a decision that should remember it); hidden on input and observed on output, the
  component reveals it as a perfect observation inside the component, but its own
  decisions still may not read it (rule 3 is about inputs); composites are re-validated,
  so a decision cannot read a variable that the composite's input foot hides. Glued
  interface variables must agree on flags (`ObservabilityMismatchError`), after names,
  states and references (BayesianNetworks' `InterfaceMismatchError`). In `oapply` each
  junction has one flag and each port the flag of its foot: a pass-through variable's two
  ports on one junction with different flags are an `ObservabilityMismatchError`; on two
  junctions, each keeps its flag (the colimit joins them into one variable) and an outer
  port takes its own junction's flag.
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
  `resolve_kernel` and utilities with `_lookup_utility`) and calls `InfluenceDiagrams`'
  `optimize`; `contextual_value(o, ..., σ; prior, continuation)`,
  `EU_f(σ; μ, c) = Σ_x μ(x) Σ_y (W(y, x) + K(y | x) c(y))`; `contextual_optimize`; and the
  two contexts of a serial composite, `continuation_value` (`c_τ`, over `dom`) and
  `boundary_law` (`ν_σ = K μ`, over `codom`). Contexts are explicit: `prior` (a vector in
  `joint_states` order, nonnegative, summing to one within `atol`, or a state
  kernel `I → X`) and `continuation` (a signed vector in `joint_states` order, or a
  `RewardKernel` `Y → I`) may be left out only for an empty interface, never defaulted to
  something else. `contextual_optimize` delegates to `InfluenceDiagrams`: `_bound_model`
  (which `_closed_model` also uses, after its closedness check) binds the apex's tables
  into an `InfluenceDiagramModel` whose input variables keep no mechanism (they are its
  exogenous variables: rule 2 and `InterfaceError` 3 make the inputs exactly the
  generator-free variables), `_boundary_table` reshapes the prior (over the input
  variables, which never repeat) and the continuation (over the output variables, a
  repeated output repeating its name, read on the diagonal) into a `DecisionContext`, and
  `optimize(m, ExhaustivePolicySearch(; max_policies); context, max_states, atol)` solves
  it. Its `DecisionSolution` and diagnostics (`(nstrategies, method = :value_table)`,
  possibly `exact_fallback`) are returned as they are. The order of the strategies, the
  first maximum and `PolicySearchTooLargeError` are that search's. Decision variable
  elimination and evidence are never reached (no backend keyword; the model forms refuse
  evidence, as a context does). `brute_force = true` keeps the independent path, scoring
  each strategy of `all_deterministic_strategies(apex(o))` with `contextual_value` through
  `interpret`; the tests check that the two agree in value and strategy. The search keys
  policies, tables and the context by name, so `contextual_optimize` raises
  `ArgumentError` (`_require_unique_names`, on both paths) when the apex repeats a decision,
  variable or utility name (a diagram tensored with itself); `interpret` and
  `contextual_value` still accept repeated names, equally named decisions sharing one
  policy. The prior rule (`_prior_vector`, shared by `contextual_value`, `boundary_law` and
  `contextual_optimize`) is `DecisionContext`'s: entries nonnegative with no slack and
  `|Σ - 1| <= atol`. Model forms read
  `kernels(m)`/`bound_utilities(m)` through the apex's references (so they need a diagram
  whose references are bound) and refuse evidence.

## Commands

```sh
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'   # the test suite
julia --project=docs docs/make.jl --no-deploy                     # build docs locally (strict)
cd vignettes && quarto render                                     # render vignettes (render each .qmd on its own to re-execute)
julia scripts/sync_vignettes.jl [--check]                         # copy vignettes into docs/src/tutorials
julia --project scripts/write_certificate_fixtures.jl [--check]   # write the reward-certificate fixtures
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
  reads), `_factors`, `_product` and `_joint_atol`. The kernel lookup through a
  mechanism's reference that `optimize` and `contextual_optimize` use to bind an apex's tables is
  `BayesianNetworks`' public `resolve_kernel`, no longer an internal. For the reward
  certificates, two more `BayesianNetworks` internals: `OrderedDict` (the binding it
  imports from OrderedCollections, taken from there, as InfluenceDiagrams does, so that no
  dependency is added) and `_nearest_binary64` (ADR 0016's correct rounding, which checks
  exact companions); and `scripts/write_certificate_fixtures.jl` (hence the tests) writes
  JSON with `InfluenceDiagrams.JSON3`, the JSON3 that InfluenceDiagrams writes its own
  certificates with, so JSON3 is in neither `[deps]` nor `[extras]`. Keep these in step.
- `src/errors.jl`: `OpenInfluenceDiagramError <: BayesNetError` (ADR 0013, since the package
  defines several types) and its subtypes `ObservabilityMismatchError`,
  `DiagramInterfaceError`, `NoForgettingError`, `DuplicatePolicyError` and
  `RewardCertificateError(code, path, message)`, with `showerror` methods that name the
  variables and decisions; included first.
- `src/open.jl`: `InfluenceDiagramCospan(Ob)(Untyped)` from
  `OpenACSetTypes(InfluenceDiagramUntyped, VariableSpaceUntyped)`; `OBSERVABILITY`;
  `OpenInfluenceDiagramOb` (space plus flags); `OpenInfluenceDiagram{C}` (a two-footed
  `StructuredCospan` plus the flags of each foot); `Open(id; inputs, outputs, observed,
  validate)` (`_observed_flags` and `_foot_flags` turn either form of `observed` into the
  flags of each foot); accessors (methods on Catlab's `apex`, `legs`, `feet`, `dom`, `codom` and on
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
  (`InfluenceDiagrams`' exhaustive search with a `DecisionContext`, or brute force).
- `src/games.jl` (ADR 0020): lenses and open-game equilibria for a chain of components
  composed with `compose` (`no_forgetting` passed through; limited-memory chains need
  `false`). `component_contexts` runs the lens passes (`boundary_law` forward from the
  chain's prior, `continuation_value` backward from its continuation) over the reward
  kernels of the components under the restricted strategy; `regrets` compares each
  component's `contextual_optimize` in its context with its `contextual_value` there;
  `is_equilibrium` thresholds the regrets; `best_response_dynamics` replaces one
  component's policies at a time by a best response while that gains more than `tol`, and
  stops at an equilibrium. A decision name in two components is an `ArgumentError`. This
  is not the forbidden "optimise each component in isolation and compose": every best
  response is taken in the context the rest of the chain induces, and the result is
  documented as an equilibrium, which can be worse than `optimize`'s optimum (the Lean
  coordination witness, 1 < 2).
- `src/certificates.jl` (ADR 0019): `export_reward_certificate(o, kernels, utilities, σ;
  numeric_mode, exact_tables, description, max_entries)` and the model form, writing
  `OpenInfluence.RewardCertificate/v1`. The format section of the workspace plan
  `docs/REWARD-CERTIFICATES-PLAN-2026-10-17.md` is a contract with the Lean checker
  (`lake exe check_certificate` in `proofs/`), mirrored by
  `docs/src/reward-certificate-v1.schema.json`: change the exporter, the schema and the
  checker together. The result is an `OrderedDict{String,Any}` whose keys, and every named
  tuple's fields, are in the format's order (the tests check it against the schema's
  property order). `network` mirrors CategoricalBayesianNetworks' `open_network_certificate`
  (dense 0-based ids in part order, rows in part order with their actual positions,
  boundary attributes read from the feet), with the reference tags reimplemented in
  `_reward_ref` so that they raise `RewardCertificateError`; chance mechanisms come first,
  then decisions as `policy(name)` generators whose input rows are the information inputs
  (`position` = `information_position`); ranks are a Kahn order of the
  causal-plus-information graph. Every table is flat, lexicographic, last axis fastest
  (`_cell_order`); `K` and `W` are converted from the reward kernel's outputs-first layout.
  Order of work: keywords (`ArgumentError`), `validate`, the network (reference codes),
  equally named decisions (`:inconsistent_decision`), the cell budget (`:too_many_entries`,
  from the structure alone), the utility tables (so a non-finite utility is `:non_finite`),
  `interpret` (whose errors pass through), the chance tables, unused companions, the
  strategy and the result. Binary64 words are those of InfluenceDiagrams'
  `_dve_float_bits`; companions are keyed `(:chance | :utility, part id, zero-based
  coordinates)` and must round to their cell by `_nearest_binary64`.
- `scripts/write_certificate_fixtures.jl`: `certificate_fixtures()` builds the eight
  fixtures of the plan, `write_certificate_fixtures` writes them into
  `proofs/certificate-fixtures/` (compact `JSON3.write` plus a newline; `--check` compares
  instead). It writes only those eight files: the `hand-*.json` and `*.bad.json` fixtures
  beside them are written by `proofs/scripts/hand_fixtures.py`, and
  `proofs/certificate-fixtures/EXPECTED.md` lists the checker's expected outcome for every
  fixture (`make check-certificates` fails on an unlisted one). `test/test_certificates.jl` includes the script and
  compares the fixtures byte for byte, apart from `metadata.julia_version`. Rerun the
  script after a deliberate change to the format or to a fixture's model, and keep the
  Lean checker's expectations in step.
- `test/runtests.jl`: `test_open.jl` (construction, accessors, flags, per-foot flags and
  their errors, one failing case per rule, the Bayesian-network embedding; defines the umbrella split `umbrella_chance` and
  `umbrella_decision`), `test_composition.jl` (every operation; the umbrella, the SPEC §46
  grazing diagram at two boundaries and the two-stage diagram split and composed back to
  isomorphic diagrams; rules 1, 5 and 6 across boundaries; per-foot flags on a
  pass-through relay of the two-stage split, forgetting and revealing, under `compose`,
  `glue`, `otimes`, `id` and `oapply` on one junction and on two; unset references),
  `test_semantics.jl` (the reward-kernel laws on random reward kernels; `interpret` against
  the closed-composite oracle under `compose`, `glue`, `otimes` and `oapply` on every
  strategy of the umbrella and two-stage oil-wildcatter splits, on the grazing splits and on
  seeded random diagrams cut into two and three pieces and placed side by side; identities,
  associativity, interchange, copy and discard through the syntax; defines
  `random_spec` and `random_pieces`), `test_optimization.jl` (the contextual identity in
  both forms on the umbrella, oil-wildcatter and grazing splits and on seeded random splits
  of two and three pieces; `optimize` on closed composites; `contextual_optimize` against
  brute force and the solvers, in both contextual orders; the delegation to a
  `DecisionContext`: a non-product joint prior over two inputs, a repeated output and a
  pass-through variable in the continuation, the shared-name `ArgumentError`, evidence and
  decision variable elimination unreachable; the bundle's Lean witness of
  `INF-ISOLATED-OBSTRUCTION`, `lean_early` and `lean_late`, giving `1 < 4`, and of
  `INF-HIDDEN-OBSTRUCTION`, where the pointwise value 2 needs a policy reading the hidden
  input and rule 3 rejects it), `test_games.jl` (ADR 0020: contexts against `boundary_law`/`continuation_value`; the Lean
  obstruction and coordination witnesses; on seeded random three-piece chains composed with
  `no_forgetting = false`, the contextual identity along the chain, bracketing-independent
  contexts, regrets equal to unilateral gains found by brute force on the closed composite,
  best-response dynamics monotone and ending at an equilibrium, and brute-force optima being
  equilibria), `test_certificates.jl` (reward certificates: the umbrella
  split's cells by hand; every cell re-derived from `cpt`, `utility_value`, the policies
  and `kernel_matrix`/`reward_matrix` on the fixtures, the oil wildcatter's strategies and
  seeded random pieces; the model form; rational companions and their rounding; every
  error code; the schema's key order; the committed fixtures), `test_errors.jl`
  (hierarchy, re-exports, frozen names, messages) and `test_docstrings.jl`.
- `proofs/`: the Lean project (see below). `proofs/certificate-fixtures/*.json` is written by
  `scripts/write_certificate_fixtures.jl` (other than `hand-*.json` and `*.bad.json`, written
  by `proofs/scripts/hand_fixtures.py`); do not edit it by hand.
- `vignettes/`: the quarto project: 01 open influence diagrams and composition, 02 a management decision composed with the zoo's `reference_habitat_bn` (MIT, built in), 03 why optimisation does not compose, 04 equilibria of a monitoring and a management agency (ADR 0020: `component_contexts`, `regrets`, `best_response_dynamics` on the zoo network with a survey component).

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
generators), `Interpretation` (`interpret_comp`, `interpret_identity`, `interpret_tensor`),
`Obstruction` (the isolated and hidden-input witnesses, as reward-kernel tables) and
`Lens` (ADR 0020: the lens of a reward kernel, open games with decision, identity and
serial composition, equilibria compositional, optima equilibria, the coordination witness). The
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
- `proofs/certificate-fixtures/*.json` are written by
  `julia --project scripts/write_certificate_fixtures.jl`, except `hand-*.json` and
  `*.bad.json`, which `python3 proofs/scripts/hand_fixtures.py` writes.

## Style

JuliaFormatter `yas`; docstrings on every exported name, which `test/test_docstrings.jl` enforces; the docs
build is strict (no `warnonly`), so a docstring left out of the manual or a broken `@ref` fails it; typed
exceptions with variable names in the message, following ADR 0013 and ADR 0015: they live in `src/errors.jl` and
subtype `OpenInfluenceDiagramError <: BayesNetError`, invalid arguments and keywords raise `ArgumentError`,
typed errors from a lower package pass through unchanged and documented, and another package's type is named
as a code span, never with `@ref`; no emojis in code or docs.
