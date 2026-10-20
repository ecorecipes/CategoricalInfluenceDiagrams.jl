# Write the reward-certificate fixtures (ADR 0019) into proofs/certificate-fixtures/, where
# the Lean checker (`lake exe check_certificate`, `make check-certificates`) reads them.
#
#   julia --project scripts/write_certificate_fixtures.jl          # write
#   julia --project scripts/write_certificate_fixtures.jl --check  # exit 1 if one is stale
#
# The test suite includes this file and compares `certificate_fixture_bytes` with the
# committed files, so the script and the tests build the fixtures with the same code. Only
# the fixtures listed in `certificate_fixtures` are written; the hand-made negative
# fixtures (`*.bad.json`) beside them are not touched.
#
# The JSON writer is the JSON3 that InfluenceDiagrams writes its own certificates with
# (`InfluenceDiagrams.JSON3`), so that this package adds no dependency (see CLAUDE.md).
# Output is deterministic: every object is an `OrderedDict` or a named tuple in the
# format's key order, written compactly with a trailing newline.

using CategoricalInfluenceDiagrams
using InfluenceDiagrams: InfluenceDiagrams

const CERTIFICATE_FIXTURE_DIR = normpath(joinpath(@__DIR__, "..", "proofs",
                                                  "certificate-fixtures"))
const COMPOSITION_FIXTURE_DIR = normpath(joinpath(@__DIR__, "..", "proofs",
                                                  "composition-fixtures"))

# Chance kernels keyed by target variable name, so that one table source serves the pieces
# of a split and the composite.
function certificate_kernels(m)
    return Dict{Symbol,FiniteKernel}(x => kernel(m, x) for x in chance_names(syntax(m)))
end

# The umbrella problem of `InfluenceDiagrams.umbrella_model` split at {Weather, Forecast}:
# the chance half exports the weather (hidden) and the forecast (observed), and the
# decision half imports both.
function certificate_umbrella_chance()
    id = influence_diagram(:Weather => [:sunny, :rainy],
                           :Forecast => [:sunny, :cloudy, :rainy];
                           mechanisms=[:Weather => (), :Forecast => :Weather], closed=false)
    return Open(id; outputs=[:Weather, :Forecast], observed=[:Forecast])
end

function certificate_umbrella_decision()
    id = influence_diagram(:Weather => [:sunny, :rainy],
                           :Forecast => [:sunny, :cloudy, :rainy],
                           :Umbrella => [:take, :leave];
                           decisions=[:Umbrella => :Forecast],
                           utilities=[:U => (:Weather, :Umbrella)], closed=false)
    return Open(id; inputs=[:Weather, :Forecast], observed=[:Forecast])
end

# Leave the umbrella unless the forecast is rain.
function certificate_umbrella_strategy()
    forecast = FiniteAxis(:Forecast, [:sunny, :cloudy, :rainy])
    umbrella = FiniteAxis(:Umbrella, [:take, :leave])
    return Strategy(:Umbrella => DeterministicPolicy(:Umbrella, [forecast], umbrella,
                                                     [:leave, :leave, :take]))
end

# The umbrella's exact tables, keyed as `exact_tables` wants them: chance cells by
# mechanism part id and utility cells by utility part id of the closed composite `c`, with
# zero-based coordinates (parents, then the child; the utility's scope).
function certificate_umbrella_companions(c)
    id = apex(c)
    mech(x) = only(incident(id, variable_id(id, x), :target))
    exact = Dict{Any,Rational{Int}}()
    for (s, q) in enumerate((7 // 10, 3 // 10))
        exact[(:chance, mech(:Weather), (s - 1,))] = q
    end
    forecast = [7//10 1//5 1//10; 3//20 1//4 3//5]
    for w in 1:2, f in 1:3
        exact[(:chance, mech(:Forecast), (w - 1, f - 1))] = forecast[w, f]
    end
    u = only(parts(id, :Utility))
    utility = [20 100; 70 0]
    for w in 1:2, a in 1:2
        exact[(:utility, u, (w - 1, a - 1))] = utility[w, a]
    end
    return exact
end

# `InfluenceDiagrams.two_stage_diagram` (test, then drill) split after the test result.
function certificate_two_stage_test()
    id = influence_diagram(:Oil => [:dry, :wet], :Test => [:test, :skip],
                           :Result => [:pos, :neg, :none];
                           mechanisms=[:Oil => (), :Result => (:Oil, :Test)],
                           decisions=[:Test => Symbol[]], utilities=[:TestCost => :Test],
                           closed=false)
    return Open(id; outputs=[:Oil, :Test, :Result], observed=[:Test, :Result])
end

function certificate_two_stage_drill()
    id = influence_diagram(:Oil => [:dry, :wet], :Test => [:test, :skip],
                           :Result => [:pos, :neg, :none], :Drill => [:drill, :dont];
                           decisions=[:Drill => (:Test, :Result)],
                           utilities=[:Payoff => (:Oil, :Drill)], closed=false)
    return Open(id; inputs=[:Oil, :Test, :Result], observed=[:Test, :Result])
end

# The optimal strategy (expected utility 21): test, and drill exactly on a positive result.
function certificate_two_stage_strategy()
    test = FiniteAxis(:Test, [:test, :skip])
    result = FiniteAxis(:Result, [:pos, :neg, :none])
    drill = FiniteAxis(:Drill, [:drill, :dont])
    return Strategy(:Test => ConstantPolicy(:test),
                    :Drill => DeterministicPolicy(:Drill, [test, result], drill,
                                                  [:drill :dont :dont; :dont :dont :drill]))
end

# The two-stage composite's exact tables, keyed as `exact_tables` wants them (see
# `certificate_umbrella_companions`): the decimal model `two_stage_model` rounds.
function certificate_two_stage_companions(c)
    id = apex(c)
    mech(x) = only(incident(id, variable_id(id, x), :target))
    util(x) = only(u for u in parts(id, :Utility) if utility_name(id, u) == x)
    exact = Dict{Any,Rational{Int}}()
    for s in 0:1
        exact[(:chance, mech(:Oil), (s,))] = 1 // 2
    end
    # (Oil, Test, Result): a test reports the oil, no test reports nothing.
    result = Dict((0, 0) => (3 // 10, 7 // 10, 0 // 1), (1, 0) => (4 // 5, 1 // 5, 0 // 1),
                  (0, 1) => (0 // 1, 0 // 1, 1 // 1), (1, 1) => (0 // 1, 0 // 1, 1 // 1))
    for ((o, t), row) in result, (r, q) in enumerate(row)
        exact[(:chance, mech(:Result), (o, t, r - 1))] = q
    end
    payoff = [-60 0; 100 0]
    for o in 1:2, d in 1:2
        exact[(:utility, util(:Payoff), (o - 1, d - 1))] = payoff[o, d]
    end
    for (t, q) in enumerate((-10, 0))
        exact[(:utility, util(:TestCost), (t - 1,))] = q
    end
    return exact
end

# A relay: the oil passes through (observed on input, hidden on output), a report of it is
# written twice (a copied output), and an action reads the report and is scored on the oil.
function certificate_relay()
    id = influence_diagram(:Oil => [:dry, :wet], :Report => [:good, :bad],
                           :Act => [:go, :stop];
                           mechanisms=[:Report => :Oil], decisions=[:Act => :Report],
                           utilities=[:Gain => (:Oil, :Act)], closed=false)
    o = Open(id; inputs=[:Oil], outputs=[:Oil, :Report, :Report],
             observed=(inputs=[:Oil], outputs=[:Report]))
    oil, report = FiniteAxis(:Oil, [:dry, :wet]), FiniteAxis(:Report, [:good, :bad])
    act = FiniteAxis(:Act, [:go, :stop])
    kernels = Dict{Symbol,FiniteKernel}(:Report => FiniteKernel(FiniteSpace(oil),
                                                                FiniteSpace(report),
                                                                [0.2 0.9; 0.8 0.1]))
    utilities = Dict{Symbol,AbstractUtility}(:Gain => TabularUtility([oil, act],
                                                                     [-5.0 0.0; 12.0 0.0]))
    σ = Strategy(:Act => DeterministicPolicy(:Act, [report], act, [:go, :stop]))
    return o, kernels, utilities, σ
end

# The relay's exact tables: the decimal report kernel and the integer gain.
function certificate_relay_companions(o)
    id = apex(o)
    mech = only(incident(id, variable_id(id, :Report), :target))
    gain = only(parts(id, :Utility))
    exact = Dict{Any,Rational{Int}}()
    # (Oil, Report): P(good | dry) = 1/5, P(good | wet) = 9/10.
    report = [1//5 4//5; 9//10 1//10]
    for oil in 1:2, r in 1:2
        exact[(:chance, mech, (oil - 1, r - 1))] = report[oil, r]
    end
    table = [-5 0; 12 0]
    for oil in 1:2, a in 1:2
        exact[(:utility, gain, (oil - 1, a - 1))] = table[oil, a]
    end
    return exact
end

# A dyadic diagram: the forecast half of the umbrella with every chance cell a dyadic
# rational, so that binary64 rows sum to exactly one, and integer utilities, so that K and W
# are exact too. The weather is a hidden input and the forecast an observed output.
function certificate_dyadic()
    id = influence_diagram(:Weather => [:sunny, :rainy],
                           :Forecast => [:sunny, :cloudy, :rainy],
                           :Umbrella => [:take, :leave];
                           mechanisms=[:Forecast => :Weather],
                           decisions=[:Umbrella => :Forecast],
                           utilities=[:U => (:Weather, :Umbrella)], closed=false)
    o = Open(id; inputs=[:Weather], outputs=[:Forecast], observed=[:Forecast])
    weather = FiniteAxis(:Weather, [:sunny, :rainy])
    forecast = FiniteAxis(:Forecast, [:sunny, :cloudy, :rainy])
    umbrella = FiniteAxis(:Umbrella, [:take, :leave])
    # Outputs first: column w is P(Forecast | Weather = w).
    table = [1/2 1/8; 1/4 1/4; 1/4 5/8]
    kernels = Dict{Symbol,FiniteKernel}(:Forecast => FiniteKernel(FiniteSpace(weather),
                                                                  FiniteSpace(forecast),
                                                                  table))
    utilities = Dict{Symbol,AbstractUtility}(:U => TabularUtility([weather, umbrella],
                                                                  [20.0 100.0; 70.0 0.0]))
    σ = Strategy(:Umbrella => DeterministicPolicy(:Umbrella, [forecast], umbrella,
                                                  [:leave, :take, :take]))
    return o, kernels, utilities, σ
end

"""
    certificate_fixtures() -> Vector{Pair{String,OrderedDict{String,Any}}}

The reward certificates written to `proofs/certificate-fixtures/`, by file name.
"""
function certificate_fixtures()
    um = InfluenceDiagrams.umbrella_model()
    uk, uu = certificate_kernels(um), bound_utilities(um)
    closed = compose(certificate_umbrella_chance(), certificate_umbrella_decision())
    om = InfluenceDiagrams.two_stage_model()
    two = compose(certificate_two_stage_test(), certificate_two_stage_drill())
    return ["umbrella-decision.json" =>
                export_reward_certificate(certificate_umbrella_decision(),
                                          uk, uu,
                                          certificate_umbrella_strategy();
                                          description="the decision half of the umbrella split, with Forecast observed on input"),
            "umbrella-closed.json" => export_reward_certificate(closed, uk, uu,
                                                                certificate_umbrella_strategy();
                                                                description="the umbrella split composed back: empty interfaces, K = [1], W = [EU]"),
            "two-stage-composite.json" => export_reward_certificate(two,
                                                                    certificate_kernels(om),
                                                                    bound_utilities(om),
                                                                    certificate_two_stage_strategy();
                                                                    description="the oil wildcatter composed from its test and drill pieces, under the optimal strategy"),
            "relay.json" => export_reward_certificate(certificate_relay()...;
                                                      description="a pass-through variable and a copied output"),
            "dyadic.json" => export_reward_certificate(certificate_dyadic()...;
                                                       description="dyadic chance tables: binary64 rows sum to exactly one"),
            "umbrella-rational.json" => export_reward_certificate(closed, uk, uu,
                                                                  certificate_umbrella_strategy();
                                                                  numeric_mode=:rational_exact,
                                                                  exact_tables=certificate_umbrella_companions(closed),
                                                                  description="the closed umbrella with exact rational companions"),
            "two-stage-rational.json" => export_reward_certificate(two,
                                                                   certificate_kernels(om),
                                                                   bound_utilities(om),
                                                                   certificate_two_stage_strategy();
                                                                   numeric_mode=:rational_exact,
                                                                   exact_tables=certificate_two_stage_companions(two),
                                                                   description="the oil wildcatter composite with exact rational companions"),
            "relay-rational.json" => let (o, k, u, σ) = certificate_relay()
                export_reward_certificate(o, k, u, σ; numeric_mode=:rational_exact,
                                          exact_tables=certificate_relay_companions(o),
                                          description="the relay with exact rational companions")
            end]
end

# The companions `exact` of the diagram `from` (keyed by its part ids), restricted and rekeyed
# to the diagram `to` by mechanism target and utility name: the companions of a part, or of a
# composite, from those of another diagram with the same tables.
function remap_companions(exact, from::OpenInfluenceDiagram, to::OpenInfluenceDiagram)
    fid, tid = apex(from), apex(to)
    name(id, kind, p) = kind === :chance ? variable_name(id, subpart(id, p, :target)) :
                        utility_name(id, p)
    function find(id, kind, nm)
        ps = kind === :chance ? parts(id, :Mechanism) : parts(id, :Utility)
        return [p for p in ps if name(id, kind, p) === nm]
    end
    out = Dict{Any,Rational{Int}}()
    for ((kind, p, coords), q) in exact
        hit = find(tid, kind, name(fid, kind, p))
        isempty(hit) || (out[(kind, only(hit), coords)] = q)
    end
    return out
end

# Three rational companions for a composition of `A` and `B`, from those of the composite.
function composition_companions(A, B, exact_composite)
    C = compose(A, B)
    return (left=remap_companions(exact_composite, C, A),
            right=remap_companions(exact_composite, C, B), composite=exact_composite)
end

"""
    composition_fixtures() -> Vector{Pair{String,OrderedDict{String,Any}}}

The composition certificates written to `proofs/composition-fixtures/`, by file name: the
umbrella and oil-wildcatter splits with exact companions (accepted), the umbrella in binary64
(rejected: its decimal rows are not exact), its parts swapped (rejected: alignment) and its
composite recorded under another strategy (rejected: composition W).
"""
function composition_fixtures()
    um = InfluenceDiagrams.umbrella_model()
    uk, uu = certificate_kernels(um), bound_utilities(um)
    A, B = certificate_umbrella_chance(), certificate_umbrella_decision()
    closed = compose(A, B)
    umbrella_exact = composition_companions(A, B, certificate_umbrella_companions(closed))
    om = InfluenceDiagrams.two_stage_model()
    T, D = certificate_two_stage_test(), certificate_two_stage_drill()
    two_exact = composition_companions(T, D, certificate_two_stage_companions(compose(T, D)))
    umbrella = export_composition_certificate(A, B, uk, uu, certificate_umbrella_strategy();
                                              numeric_mode=:rational_exact,
                                              exact_tables=umbrella_exact,
                                              description="the umbrella split")
    swapped = CategoricalInfluenceDiagrams.OrderedDict{String,Any}("format" => umbrella["format"],
                                      "left" => umbrella["right"],
                                      "right" => umbrella["left"],
                                      "composite" => umbrella["composite"])
    take = Strategy(:Umbrella => ConstantPolicy(:take))
    other = export_reward_certificate(closed, uk, uu, take; numeric_mode=:rational_exact,
                                      exact_tables=umbrella_exact.composite,
                                      description="the umbrella split (composite, other strategy)")
    mismatched = CategoricalInfluenceDiagrams.OrderedDict{String,Any}("format" => umbrella["format"],
                                         "left" => umbrella["left"],
                                         "right" => umbrella["right"],
                                         "composite" => other)
    return ["umbrella-rational.json" => umbrella,
            "two-stage-rational.json" => export_composition_certificate(T, D,
                                                                       certificate_kernels(om),
                                                                       bound_utilities(om),
                                                                       certificate_two_stage_strategy();
                                                                       numeric_mode=:rational_exact,
                                                                       exact_tables=two_exact,
                                                                       description="the oil wildcatter split"),
            "umbrella-binary64.json" => export_composition_certificate(A, B, uk, uu,
                                                                      certificate_umbrella_strategy();
                                                                      description="the umbrella split in binary64"),
            "swapped.bad.json" => swapped,
            "strategy.bad.json" => mismatched]
end

"""
    certificate_fixture_bytes(certificate) -> String

The bytes of a fixture file: compact JSON in the certificate's key order and a newline.
"""
certificate_fixture_bytes(certificate) = InfluenceDiagrams.JSON3.write(certificate) * "\n"

"""
    certificate_fixture_comparable(text) -> String

`text` with the recorded Julia version blanked: the fixtures are compared byte for byte
up to `metadata.julia_version`, which records the Julia that ran the exporter.
"""
function certificate_fixture_comparable(text::AbstractString)
    return replace(text, r"\"julia_version\":\"[^\"]*\"" => "\"julia_version\":\"\"")
end

function write_certificate_fixtures(; check::Bool=false)
    mkpath(CERTIFICATE_FIXTURE_DIR)
    mkpath(COMPOSITION_FIXTURE_DIR)
    stale = String[]
    for (dir, (name, certificate)) in vcat([CERTIFICATE_FIXTURE_DIR => f
                                            for f in certificate_fixtures()],
                                           [COMPOSITION_FIXTURE_DIR => f
                                            for f in composition_fixtures()])
        path = joinpath(dir, name)
        bytes = certificate_fixture_bytes(certificate)
        if check
            isfile(path) &&
            certificate_fixture_comparable(read(path, String)) ==
            certificate_fixture_comparable(bytes) ||
                push!(stale, name)
        else
            write(path, bytes)
            println("wrote ", relpath(path, normpath(joinpath(@__DIR__, ".."))))
        end
    end
    if !isempty(stale)
        println("stale certificate fixtures: ", join(stale, ", "))
        exit(1)
    end
    return nothing
end

if abspath(PROGRAM_FILE) == @__FILE__
    write_certificate_fixtures(; check="--check" in ARGS)
end
