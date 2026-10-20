# Reward certificates

[`export_reward_certificate`](@ref) writes an open influence diagram, a deterministic
strategy for it and the reward kernel `(K, W)` that
[`interpret`](@ref interpret(::OpenInfluenceDiagram, ::AbstractDict, ::AbstractDict, ::Strategy))
computed for that strategy as an `OpenInfluence.RewardCertificate/v1` record (ADR 0019).
The Lean project in `proofs/` checks such a record with `lake exe check_certificate`. The
record ties the numbers Julia computed for one concrete diagram to the definition of the
semantics the Lean theorems are stated for, cell by cell, with the error stated.

```julia
using CategoricalInfluenceDiagrams

m = umbrella_model()
chance = Open(influence_diagram(:Weather => [:sunny, :rainy],
                                :Forecast => [:sunny, :cloudy, :rainy];
                                mechanisms=[:Weather => (), :Forecast => :Weather],
                                closed=false);
              outputs=[:Weather, :Forecast], observed=[:Forecast])
decide = Open(influence_diagram(:Weather => [:sunny, :rainy],
                                :Forecast => [:sunny, :cloudy, :rainy],
                                :Umbrella => [:take, :leave];
                                decisions=[:Umbrella => :Forecast],
                                utilities=[:U => (:Weather, :Umbrella)], closed=false);
              inputs=[:Weather, :Forecast], observed=[:Forecast])
σ = Strategy(:Umbrella => deterministic_policy(m, :Umbrella, [:leave, :leave, :take]))
kernels = Dict{Symbol,FiniteKernel}(x => kernel(m, x) for x in chance_names(syntax(m)))

certificate = export_reward_certificate(decide, kernels, bound_utilities(m), σ)
closed = export_reward_certificate(compose(chance, decide), kernels, bound_utilities(m), σ)
```

The arguments are those of `interpret`. The model form
`export_reward_certificate(o, m, σ = strategy(m))` reads `kernels(m)` and
`bound_utilities(m)` through the apex's references, and refuses a model with evidence.

The result is JSON-compatible data, an `OrderedDict{String,Any}` whose keys, and the
fields of every named tuple inside it, are in the format's order. JSON3, or another
writer that keeps insertion order, therefore writes the same bytes on every Julia version:

```julia
using JSON3
write("umbrella-decision.json", JSON3.write(certificate) * "\n")
```

## What a certificate records

| Key | Content |
|---|---|
| `format` | `"OpenInfluence.RewardCertificate/v1"` |
| `numeric_mode` | `"binary64_exact"` or `"rational_exact"` |
| `metadata` | `producer`, `producer_version`, `julia_version` and the caller's `description` |
| `network` | the structure: variables, generators and boundary rows |
| `observability` | one flag, `"observed"` or `"hidden"`, per input row and per output row |
| `chance_tables` | one table per chance mechanism |
| `utilities` | one record per utility: its name, positioned scope rows and table |
| `strategy` | one policy per distinct decision name |
| `result` | `{"arithmetic": "binary64", "K": [...], "W": [...]}` |

The [JSON Schema](reward-certificate-v1.schema.json) (draft 2020-12) gives the shape of
each field. Its property order is the key order of the certificate. Cross-field
conditions are for the checker: cell counts, positions, ranks, flag counts, information
locality, row sums and the result.

### The network

`network` has exactly the keys of the body of CategoricalBayesianNetworks'
`OpenNet.RawCertificate/v1` (`open_network_certificate`): `variableCount`,
`variableData`, `mechanisms`, `inputs` and `outputs`, with the same record shapes and
reference tags (`noRef`, `named`, `pointMass` and `policy`).

- Variable indices are dense and 0-based, in the apex's `Variable` part order. Positions
  (of states, inputs and scope) are the actual 1-based `*_position` attributes, and rows
  are written in part order with those positions, not sorted.
- Each variable's `rank` is its 0-based position in a topological order of the
  causal-plus-information graph, so ranks increase along every generator's input rows.
- The generators are the chance mechanisms, in `Mechanism` part order, then the
  decisions, in `Decision` part order. A decision is a mechanism record whose `name` is
  its decision name, whose `kernelRef` is `{"tag": "policy", "decision": name}`, whose
  `target` is its action variable and whose `inputRows` are its information inputs, each
  with its `information_position`. Generator indices are 0-based positions in this list.
- Boundary rows hold the apex variable each foot variable maps to and the attributes read
  from the foot itself. A copied output is two rows on one variable, and a pass-through
  variable is a row on each foot.

Decision precedence rows are not recorded, and neither is no-forgetting: the semantics
for a fixed strategy reads neither.

### Cell layout

Every table is a flat list of cells in lexicographic order of its axes, the last axis
varying fastest, each axis running over its variable's states in position order. A table
with no axes has one cell. The axes are:

- a chance table: the parents in input-position order, then the child. A repeated parent
  is a repeated axis. The record is `{"mechanism": g, "cells": [...]}`, with `g` the
  generator index.
- a utility: its scope rows in position order, a repeated variable being a repeated axis.
- a policy: the information inputs, in position order, of the first decision generator
  with that name. Each cell is the 1-based state position of the chosen action. A
  `ConstantPolicy` is written as its table. Equally named decisions share one policy
  (ADR 0018), so they must agree in information axis lengths and action state count.
- `K` and `W`: the input rows, in row order, then the output rows, in row order.

A [`RewardKernel`](@ref) holds its tables outputs first, with joint states enumerated
first variable fastest (FiniteKernels' `joint_states`). The exporter converts them: the
certificate cell at input state `x` and output state `y` is `kernel(r).table[y..., x...]`
and `reward(r)[y..., x...]`. In the decision half of the umbrella above, the inputs are
`(Weather, Forecast)` and there are no outputs, so `W` lists the expected utility for
`(sunny, sunny)`, `(sunny, cloudy)`, `(sunny, rainy)`, `(rainy, sunny)`, and so on:
`100, 100, 20, 0, 0, 70`.

## Numeric modes

A number cell is an InfluenceDiagrams certificate value (as `export_dve_certificate`
writes it), so the Lean side reuses that project's value decoder:

- `{"f64": word}`: `word` is 16 lowercase hexadecimal digits, the IEEE binary64 bit
  pattern. Its exact value is the dyadic rational the bits denote. Non-finite values are
  never written.
- `{"q": {"num": "...", "den": "..."}, "f64": word}`: an exact rational companion and the
  binary64 word, where `f64` is the nearest-even rounding of `q`. The exact value of the
  cell is `q`.

In `binary64_exact` mode (the default) every cell is `{"f64"}`. A runtime acceptance of a
kernel within `atol` does not make its binary64 rows sum to exactly one, and the checker
makes no semantic claim when they do not. It reports the largest row deviation instead.
Tables whose cells are dyadic (`1/2`, `1/4`, `3/8`, ...) are exact in binary64; the
fixture `dyadic.json` is such a model.

In `rational_exact` mode every chance and utility cell is `{"q", "f64"}`, and the result
cells stay `{"f64"}`. The companions come from `exact_tables`, a dictionary keyed like
InfluenceDiagrams' companions, with zero-based coordinates in the table's axis order:

```text
(:chance, mechanism_part_id, Tuple(zero_based_coordinates)) => exact integer or rational
(:utility, utility_part_id, Tuple(zero_based_coordinates))  => exact integer or rational
```

It must cover every chance and utility cell and nothing else. Each companion is checked
to round, to nearest with ties to even, to the `Float64` cell it accompanies, by
BayesianNetworks' correctly rounded `_nearest_binary64` (ADR 0016); a zero companion
matches either signed zero. No rational is inferred from a `Float64` and no table is
renormalised. This mode is the way to certify a model such as the umbrella, whose
decimal tables (`0.7`, `0.15`, ...) are not dyadic.

## Limits and errors

`max_entries` (default `1_000_000`) bounds the total number of cells: the chance tables,
utilities, policies, `K` and `W`. It is checked from the structure alone, before any
table is read and before `interpret` runs.

Invalid keyword values raise `ArgumentError`: an unknown `numeric_mode`, `exact_tables`
in `binary64_exact` mode or missing in `rational_exact` mode, a companion key that is not
of the form above (or two keys naming one cell) or a companion that is not an exact
integer or rational, a `description` that is not a string, and a `max_entries` that is
not a nonnegative integer.

The diagram is validated first, and keeps the errors of
[`validate`](@ref validate(::OpenInfluenceDiagram)). The tables and the strategy keep
those of `interpret`: `MissingKernelError`, `KernelBindingError`, `MissingUtilityError`,
`UtilityScopeError`, `IncompleteStrategyError`, `PolicySignatureError`,
`ModelTooLargeError`, and `ArgumentError` for a `StochasticPolicy`.

What the format cannot record raises [`RewardCertificateError`](@ref), whose `code`,
`path` and `message` say what and where:

| Code | Condition |
|---|---|
| `:unset_reference` | a `space_ref` or `kernel_ref` has no value |
| `:unsupported_reference` | a reference of a type the format has no tag for |
| `:policy_reference_on_chance` | a chance mechanism carries a `PolicyRef` |
| `:inconsistent_decision` | equally named decisions of different shapes |
| `:too_many_entries` | more than `max_entries` cells |
| `:non_finite` | a cell that is not finite |
| `:missing_companion` | a chance or utility cell without an exact companion |
| `:extra_companion` | a companion that matches no cell |
| `:companion_rounding` | a companion that does not round to its cell |

## Fixtures

`scripts/write_certificate_fixtures.jl` writes the fixtures the Lean checker reads into
`proofs/certificate-fixtures/`, as compact JSON with a trailing newline:

| File | Content |
|---|---|
| `umbrella-decision.json` | the decision half of the umbrella split, with `Forecast` observed on input |
| `umbrella-closed.json` | the umbrella split composed back: empty interfaces, `K = [1]`, `W = [EU]` |
| `two-stage-composite.json` | the oil wildcatter composed from its test and drill pieces |
| `relay.json` | a pass-through variable and a copied output |
| `dyadic.json` | dyadic chance tables, so that binary64 rows sum to exactly one |
| `umbrella-rational.json` | the closed umbrella in `rational_exact` mode |

The test suite builds them with the same code and compares them with the committed
files byte for byte, apart from `metadata.julia_version`, which names the Julia that ran
the exporter. Run `julia --project scripts/write_certificate_fixtures.jl --check` to
check them, and without `--check` to rewrite them after a deliberate change to the
format, which has to be made in the Lean checker too.

## Trust boundary

A checker that accepts a certificate has checked the record, not the program that
produced it (ADR 0019). These steps are trusted, not proved:

- JSON parsing;
- this exporter;
- Catlab's colimits, which built the composite;
- Julia's `Float64` arithmetic in `interpret`.

A certificate certifies the diagram it records, not the operations that built it. A
certificate of a composite shows that Julia's numbers match the Lean semantics for the
composite as recorded; on its own it does not show that Julia's composite is the Lean
composite of its parts. Composition certificates, below, add that, for the semantics.
Contextual values and contextual optimisation are not covered by version 1.

## Composition certificates

[`export_composition_certificate`](@ref) writes an `OpenInfluence.CompositionCertificate/v1`
record (ADR 0023): the reward certificates of two parts `A` and `B` and of
`compose(A, B)`, under one strategy. `lake exe check_composition` accepts it when

1. each of the three is accepted, as `check_certificate` would accept it;
2. the interfaces line up: `A`'s output rows have the attributes of `B`'s input rows, the
   composite's input rows those of `A`'s and its output rows those of `B`'s;
3. every recorded cell of the composite is within the tolerance of the composite of the
   parts' recorded cells: `K_C(x, z)` of `Σ_y K_A(x, y) K_B(y, z)` and `W_C(x, z)` of
   `Σ_y (W_A(x, y) K_B(y, z) + K_A(x, y) W_B(y, z))`.

The Lean theorems `composition_sound_K` and `composition_sound_W` then bound, at every
`(x, z)`, the gap between the decoded composite's exact reward kernel and the composite of
the decoded parts' exact reward kernels, by `2τ` plus `τ` times sums of recorded cells.
Since each certificate's exact tables are the `interpret` of its decoded diagram, this ties
Julia's composite to the Lean composite of its parts, for the semantics. The syntax of the
composite, its net up to isomorphism, is not checked.

```julia
cc = export_composition_certificate(chance, decide, kernels(m), bound_utilities(m), σ)
```

In `:rational_exact` mode `exact_tables` is a named tuple `(left = ..., right = ...,
composite = ...)`, each keyed by its own diagram's part ids. The fixtures in
`proofs/composition-fixtures/` (written by `scripts/write_certificate_fixtures.jl`, checked
by `make check-compositions`) hold two accepted compositions and three rejected at the
part, alignment and composition stages.
