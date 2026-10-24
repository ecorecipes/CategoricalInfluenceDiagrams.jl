# Expected composition-checker outcomes

`make check-compositions` runs `lake exe check_composition` (default tolerance `1e-12`) on
every `*.json` file of this directory and compares the outcome with this table
(`scripts/check_certificates.py composition-fixtures check_composition` reads it). A fixture
missing from the table, or a listed fixture that is missing, fails the target. For a
rejection, the stage is the beginning of the reason the checker prints after `rejected:`.

All are written by `scripts/write_certificate_fixtures.jl` of the package
(`composition_fixtures`). `swapped.bad.json` is `umbrella-rational.json` with its two parts
exchanged; `strategy.bad.json` is it with the composite recorded under another strategy. The
`tensor-*` fixtures are tensor certificates (`OpenInfluence.TensorCertificate/v1`) of the
umbrella's decision part beside the relay, corrupted in the same two ways. The `colimit-*`
fixtures are colimit certificates (`OpenInfluence.ColimitCertificate/v1`, ADR 0025, written by
`colimit_fixtures`): the umbrella split under `compose`, `glue` and `oapply` and the decision
part beside the relay under `otimes`; the `compose` one with a leg sending a generator to the
wrong generator (`legs.bad`), with its composite under another strategy (`policy.bad`, whose
recorded policy no longer matches the part's) and in binary64.

| Fixture | Outcome | Stage |
|---|---|---|
| `umbrella-rational.json` | accepted | |
| `two-stage-rational.json` | accepted | |
| `umbrella-binary64.json` | rejected | left: exact row sums |
| `swapped.bad.json` | rejected | alignment |
| `strategy.bad.json` | rejected | composition W |
| `tensor-rational.json` | accepted | |
| `tensor-swapped.bad.json` | rejected | alignment |
| `tensor-strategy.bad.json` | rejected | tensor W |
| `colimit-compose.json` | accepted | |
| `colimit-glue.json` | accepted | |
| `colimit-oapply.json` | accepted | |
| `colimit-otimes.json` | accepted | |
| `colimit-legs.bad.json` | rejected | structure |
| `colimit-policy.bad.json` | rejected | structure |
| `colimit-binary64.json` | rejected | part 0: exact row sums |
