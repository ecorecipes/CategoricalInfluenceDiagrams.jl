# Expected checker outcomes

`make check-certificates` runs `lake exe check_certificate` (default tolerance `1e-12`) on
every `*.json` file of this directory and compares the outcome with this table
(`scripts/check_certificates.py` reads it). A fixture missing from the table, or a listed
fixture that is missing, fails the target. For a rejection, the stage is the beginning of
the reason the checker prints after `rejected:`.

The Julia fixtures are written by `scripts/write_certificate_fixtures.jl` of the package;
the `hand-*.json` and `*.bad.json` fixtures by `scripts/hand_fixtures.py` here. Each
`*.bad.json` is `hand-mixed.json` with the one corruption named in its description.
Binary64 fixtures whose chance rows do not sum to exactly one are outside the exact
semantics (ADR 0019, decision 4) and are expected to be rejected at `exact row sums`; the
checker still reports their largest row deviation and result errors.

| Fixture | Outcome | Stage |
|---|---|---|
| `umbrella-decision.json` | accepted | |
| `umbrella-closed.json` | rejected | exact row sums |
| `two-stage-composite.json` | rejected | exact row sums |
| `relay.json` | rejected | exact row sums |
| `dyadic.json` | accepted | |
| `umbrella-rational.json` | accepted | |
| `two-stage-rational.json` | accepted | |
| `relay-rational.json` | accepted | |
| `hand-mixed.json` | accepted | |
| `hand-closed.json` | accepted | |
| `hand-rational.json` | accepted | |
| `hand-inexact.json` | rejected | exact row sums |
| `hidden-input.bad.json` | rejected | information locality |
| `cell-count.bad.json` | rejected | cell counts |
| `negative-cell.bad.json` | rejected | chance nonnegativity |
| `action-range.bad.json` | rejected | actions in range |
| `k-cell.bad.json` | rejected | result K |
| `w-cell.bad.json` | rejected | result W |
| `flag-count.bad.json` | rejected | flag counts |
