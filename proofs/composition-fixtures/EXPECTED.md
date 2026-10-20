# Expected composition-checker outcomes

`make check-compositions` runs `lake exe check_composition` (default tolerance `1e-12`) on
every `*.json` file of this directory and compares the outcome with this table
(`scripts/check_certificates.py composition-fixtures check_composition` reads it). A fixture
missing from the table, or a listed fixture that is missing, fails the target. For a
rejection, the stage is the beginning of the reason the checker prints after `rejected:`.

All five are written by `scripts/write_certificate_fixtures.jl` of the package
(`composition_fixtures`). `swapped.bad.json` is `umbrella-rational.json` with its two parts
exchanged; `strategy.bad.json` is it with the composite recorded under another strategy.

| Fixture | Outcome | Stage |
|---|---|---|
| `umbrella-rational.json` | accepted | |
| `two-stage-rational.json` | accepted | |
| `umbrella-binary64.json` | rejected | left: exact row sums |
| `swapped.bad.json` | rejected | alignment |
| `strategy.bad.json` | rejected | composition W |
