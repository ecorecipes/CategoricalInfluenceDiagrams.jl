# Reward certificates (ADR 0019): `export_reward_certificate` against hand-computed cells,
# against `interpret` and the tables it was given (re-derived independently of the
# exporter's own cell order), every error code, the rational companions, the key order of
# the JSON Schema, and the committed fixtures byte for byte. The fixtures are built by
# `scripts/write_certificate_fixtures.jl`, included here so that the script and the tests
# share one builder.
include(joinpath(@__DIR__, "..", "scripts", "write_certificate_fixtures.jl"))

using BayesianNetworks: _nearest_binary64
using CategoricalInfluenceDiagrams: OrderedDict

const CertJSON3 = InfluenceDiagrams.JSON3

# A reference type the format has no tag for.
struct RewardCertificateTestRef <: KernelRef end

# The value of a binary64 cell.
cell_f64(c) = reinterpret(Float64, parse(UInt64, c.f64; base=16))
cell_q(c) = Rational{BigInt}(parse(BigInt, c.q.num), parse(BigInt, c.q.den))

# The 1-based coordinate of the 0-based cell index `j` of a table with axis lengths `dims`
# in lexicographic order, the last axis fastest: written out by mixed-radix division, apart
# from the exporter's `_cell_order`.
function lex_coordinate(j::Integer, dims)
    c = zeros(Int, length(dims))
    for k in length(dims):-1:1
        c[k] = j % dims[k] + 1
        j ÷= dims[k]
    end
    return c
end

# The column-major (first axis fastest) linear index of `c` among `dims`, which is the
# order of `joint_states` and so of the rows and columns of `kernel_matrix`.
function first_fastest_index(c, dims)
    idx, stride = 1, 1
    for k in eachindex(dims)
        idx += (c[k] - 1) * stride
        stride *= dims[k]
    end
    return idx
end

# The certificate `cert` of `o` under `σ` records exactly the tables it was given and the
# reward kernel `interpret` computes: every cell re-derived from `cpt`, `utility_value`,
# the policy and `kernel_matrix`/`reward_matrix`.
function certificate_matches(cert, o, ks, us, σ)
    id = apex(o)
    ok = true
    for t in cert["chance_tables"]
        m = parts(id, :Mechanism)[t.mechanism + 1]
        table = cpt(resolve_kernel(id, m, ks))
        dims = size(table)
        ok &= length(t.cells) == prod(dims; init=1)
        for (j, c) in enumerate(t.cells)
            ok &= cell_f64(c) === Float64(table[lex_coordinate(j - 1, dims)...])
        end
    end
    for (k, u) in enumerate(parts(id, :Utility))
        rec = cert["utilities"][k]
        sc = utility_scope(id, u)
        dims = Tuple(nstates(id, v) for v in sc)
        ok &= rec.name == String(utility_name(id, u)) &&
              length(rec.cells) == prod(dims; init=1)
        util = us[utility_name(id, u)]
        for (j, c) in enumerate(rec.cells)
            x = lex_coordinate(j - 1, dims)
            labels = [states(id, sc[i])[x[i]] for i in eachindex(sc)]
            ok &= cell_f64(c) === utility_value(util, labels...)
        end
    end
    for rec in cert["strategy"]
        d = first(d
                  for d in parts(id, :Decision)
                  if String(decision_name(id, d)) == rec.decision)
        info = decision_information(id, d)
        dims = Tuple(nstates(id, v) for v in info)
        actions = states(id, decision_variable(id, d))
        p = σ[Symbol(rec.decision)]
        ok &= length(rec.actions) == prod(dims; init=1)
        for (j, a) in enumerate(rec.actions)
            x = lex_coordinate(j - 1, dims)
            chosen = p isa ConstantPolicy ? p.action :
                     p([states(id, info[i])[x[i]] for i in eachindex(info)]...)
            ok &= a == findfirst(==(chosen), actions)
        end
    end
    r = interpret(o, ks, us, σ)
    din, dout = Tuple(size(dom(r))), Tuple(size(codom(r)))
    K, W = kernel_matrix(kernel(r)), reward_matrix(r)
    nin = length(din)
    for (key, M) in (("K", K), ("W", W))
        cells = getproperty(cert["result"], Symbol(key))
        ok &= length(cells) == length(M)
        for (j, c) in enumerate(cells)
            x = lex_coordinate(j - 1, (din..., dout...))
            ok &= cell_f64(c) ===
                  M[first_fastest_index(x[(nin + 1):end], dout),
                    first_fastest_index(x[1:nin], din)]
        end
    end
    return ok
end

# Whether every object in the JSON value `x` has its keys in the order of the matching
# schema's `properties` (following `$ref` and `oneOf`).
function schema_key_order(x, s, defs)
    ref = get(s, Symbol("\$ref"), nothing)
    ref === nothing || return schema_key_order(x, defs[Symbol(last(split(ref, "/")))], defs)
    haskey(s, :oneOf) && return any(t -> schema_key_order(x, t, defs), s[:oneOf])
    if x isa CertJSON3.Object
        haskey(s, :properties) || return false
        collect(keys(x)) == collect(keys(s[:properties])) || return false
        return all(schema_key_order(x[k], s[:properties][k], defs) for k in keys(x))
    elseif x isa CertJSON3.Array
        return !haskey(s, :items) || all(schema_key_order(y, s[:items], defs) for y in x)
    end
    return true
end

# The code of the `RewardCertificateError` `f()` raises, and its path.
function certificate_error(f)
    e = try
        f()
        nothing
    catch err
        err
    end
    e isa RewardCertificateError ||
        error("expected a RewardCertificateError, got $(repr(e))")
    return e
end

@testset "Reward certificates" begin
    m = umbrella_model()
    ks, us = kernels_by_name(m), bound_utilities(m)
    A, B = umbrella_chance(), umbrella_decision()
    C = compose(A, B)
    σ = certificate_umbrella_strategy()

    @testset "layout on the umbrella split, against hand-computed cells" begin
        # The chance half: two chance tables, an observed and a hidden output, no reward.
        cA = export_reward_certificate(A, ks, us, Strategy())
        @test cA isa OrderedDict{String,Any}
        @test all(x -> x isa Vector, (cA["chance_tables"][1].cells, cA["result"].K))
        @test collect(keys(cA)) ==
              ["format", "numeric_mode", "metadata", "network", "observability",
               "chance_tables", "utilities", "strategy", "result"]
        @test cA["format"] == "OpenInfluence.RewardCertificate/v1"
        @test cA["numeric_mode"] == "binary64_exact"
        @test cA["metadata"] ==
              (producer="CategoricalInfluenceDiagrams.jl",
               producer_version=string(pkgversion(CategoricalInfluenceDiagrams)),
               julia_version=string(VERSION), description="")
        net = cA["network"]
        @test keys(net) == (:variableCount, :variableData, :mechanisms, :inputs, :outputs)
        @test net.variableCount == 2
        @test [v.name for v in net.variableData] == ["Weather", "Forecast"]
        @test [v.rank for v in net.variableData] == [0, 1]
        @test net.variableData[2].stateRows ==
              [(name="sunny", position=1), (name="cloudy", position=2),
               (name="rainy", position=3)]
        @test [g.name for g in net.mechanisms] ==
              ["Weather_mechanism", "Forecast_mechanism"]
        @test [g.target for g in net.mechanisms] == [0, 1]
        @test net.mechanisms[2].inputRows == [(varId=0, position=1)]
        @test all(g.kernelRef == (tag="noRef",) for g in net.mechanisms)
        @test isempty(net.inputs) && [b.varId for b in net.outputs] == [0, 1]
        @test net.outputs[2].attrs ==
              (name="Forecast", spaceRef=(tag="noRef",),
               states=["sunny", "cloudy", "rainy"])
        @test cA["observability"] == (inputs=String[], outputs=["hidden", "observed"])
        @test [t.mechanism for t in cA["chance_tables"]] == [0, 1]
        @test cell_f64.(cA["chance_tables"][1].cells) == [0.7, 0.3]
        # (Weather, Forecast), the forecast fastest.
        @test cell_f64.(cA["chance_tables"][2].cells) == [0.7, 0.2, 0.1, 0.15, 0.25, 0.6]
        @test isempty(cA["utilities"]) && isempty(cA["strategy"])
        @test cA["result"].arithmetic == "binary64"
        @test cell_f64.(cA["result"].K) ≈
              [0.7 * 0.7, 0.7 * 0.2, 0.7 * 0.1, 0.3 * 0.15, 0.3 * 0.25, 0.3 * 0.6]
        @test all(iszero, cell_f64.(cA["result"].W))

        # The decision half: the decision is a generator with a policy reference reading
        # the observed input, and W is the utility of the weather and the chosen action.
        cB = export_reward_certificate(B, ks, us, σ; description="decision half")
        @test cB["metadata"].description == "decision half"
        g = only(cB["network"].mechanisms)
        @test g == (name="Umbrella", kernelRef=(tag="policy", decision="Umbrella"),
                    target=2, inputRows=[(varId=1, position=1)])
        @test [v.rank for v in cB["network"].variableData] == [0, 1, 2]
        @test [b.varId for b in cB["network"].inputs] == [0, 1]
        @test cB["observability"] == (inputs=["hidden", "observed"], outputs=String[])
        @test isempty(cB["chance_tables"])
        u = only(cB["utilities"])
        @test u.name == "U" &&
              u.scopeRows == [(varId=0, position=1), (varId=2, position=2)]
        # (Weather, Umbrella): sunny-take, sunny-leave, rainy-take, rainy-leave.
        @test cell_f64.(u.cells) == [20.0, 100.0, 70.0, 0.0]
        # Leave unless rain is forecast; actions are 1-based state positions.
        @test only(cB["strategy"]) == (decision="Umbrella", actions=[2, 2, 1])
        # (Weather, Forecast), the forecast fastest.
        @test cell_f64.(cB["result"].K) == ones(6)
        @test cell_f64.(cB["result"].W) == [100.0, 100.0, 20.0, 0.0, 0.0, 70.0]
        @test u.cells[1] == (f64="4034000000000000",)
        @test cB["result"].W[end] == (f64="4051800000000000",)

        # The composite: chance mechanisms first, then the decision; K = [1], W = [EU].
        cC = export_reward_certificate(C, ks, us, σ)
        @test [g.kernelRef.tag for g in cC["network"].mechanisms] ==
              ["noRef", "noRef", "policy"]
        @test cell_f64.(cC["result"].K) == [1.0]
        @test cell_f64(only(cC["result"].W)) == reward(interpret(C, ks, us, σ))[] ≈ 77
        @test cC["observability"] == (inputs=String[], outputs=String[])
    end

    @testset "cells are the tables given and interpret's reward kernel" begin
        for (o, ks_, us_, σ_) in
            ((A, ks, us, Strategy()), (B, ks, us, σ), (C, ks, us, σ),
             (B, ks, us, Strategy(:Umbrella => ConstantPolicy(:take))),
             certificate_relay(), certificate_dyadic())
            @test certificate_matches(export_reward_certificate(o, ks_, us_, σ_), o, ks_,
                                      us_, σ_)
        end
        mo = two_stage_model()
        two = compose(two_stage_test(), two_stage_drill())
        kso, uso = kernels_by_name(mo), bound_utilities(mo)
        for σ_ in (certificate_two_stage_strategy(),
                   collect(all_deterministic_strategies(apex(two)))[1:5:end]...)
            @test certificate_matches(export_reward_certificate(two, kso, uso, σ_), two,
                                      kso, uso, σ_)
        end
        # Seeded random diagrams cut into pieces with inputs, outputs and decisions.
        for seed in 1:6
            rng = Xoshiro(100 + seed)
            spec = random_spec(rng)
            n = length(spec.vars)
            for piece in random_pieces(spec, [rand(rng, 2:n)])
                σ_ = random_strategy(rng, apex(piece))
                c = export_reward_certificate(piece, spec.kernels, spec.utilities, σ_)
                @test certificate_matches(c, piece, spec.kernels, spec.utilities, σ_)
                # Ranks increase along every generator's input rows, and every variable
                # with a generator is a target exactly once.
                net = c["network"]
                @test all(net.variableData[r.varId + 1].rank <
                          net.variableData[g.target + 1].rank
                          for g in net.mechanisms for r in g.inputRows)
                @test sort!([v.rank for v in net.variableData]) == 0:(net.variableCount - 1)
                nchance = length(c["chance_tables"])
                @test all(g.kernelRef.tag == "policy"
                          for g in net.mechanisms[(nchance + 1):end])
            end
        end
    end

    @testset "the model form" begin
        mσ = set_policy(m, :Umbrella, σ[:Umbrella])
        whole = Open(syntax(mσ))
        c = export_reward_certificate(whole, mσ)
        @test c == export_reward_certificate(whole, kernels(mσ), bound_utilities(mσ), σ)
        @test c == export_reward_certificate(whole, m, σ)
        @test [g.kernelRef.tag for g in c["network"].mechanisms] ==
              ["named", "named", "policy"]
        @test certificate_matches(c, whole, kernels(mσ), bound_utilities(mσ), σ)
        @test_throws ArgumentError export_reward_certificate(whole,
                                                             observe(mσ,
                                                                     :Forecast => :rainy))
    end

    @testset "rational companions" begin
        exact = certificate_umbrella_companions(C)
        q = export_reward_certificate(C, ks, us, σ; numeric_mode=:rational_exact,
                                      exact_tables=exact)
        b = export_reward_certificate(C, ks, us, σ)
        @test q["numeric_mode"] == "rational_exact"
        id = apex(C)
        ms = collect(parts(id, :Mechanism))
        for (t, tb) in zip(q["chance_tables"], b["chance_tables"])
            dims = Tuple(nstates(id, v)
                         for v in vcat(inputs(id, ms[t.mechanism + 1]),
                                       target(id, ms[t.mechanism + 1])))
            for (j, (c, cb)) in enumerate(zip(t.cells, tb.cells))
                @test keys(c) == (:q, :f64) && keys(c.q) == (:num, :den)
                @test c.f64 == cb.f64
                @test _nearest_binary64(cell_q(c)) === cell_f64(c)
                key = (:chance, ms[t.mechanism + 1],
                       Tuple(lex_coordinate(j - 1, dims) .- 1))
                @test cell_q(c) == exact[key]
            end
        end
        for c in only(q["utilities"]).cells
            @test _nearest_binary64(cell_q(c)) === cell_f64(c) &&
                  denominator(cell_q(c)) == 1
        end
        @test only(q["chance_tables"][1].cells[1:1]).q == (num="7", den="10")
        # The result stays binary64 and equal to binary64 mode's.
        @test q["result"] == b["result"]
        @test all(keys(c) == (:f64,) for c in q["result"].W)
        # Integers, `Rational{Int}` and `Rational{BigInt}` are all exact companions.
        big_exact = Dict{Any,Any}(k => Rational{BigInt}(v) for (k, v) in exact)
        @test export_reward_certificate(C, ks, us, σ; numeric_mode=:rational_exact,
                                        exact_tables=big_exact) == q
        # 7/10 is not a binary64 number: its word is the nearest one, which the
        # companion check accepts, and 7/10 + 2^-60 rounds to the same word.
        wkey = (:chance, ms[1], (0,))
        near = merge(exact, Dict(wkey => 7 // 10 + 1 // big(2)^60))
        @test cell_q(export_reward_certificate(C, ks, us, σ; numeric_mode=:rational_exact,
                                               exact_tables=near)["chance_tables"][1].cells[1]) ==
              7 // 10 + 1 // big(2)^60
    end

    @testset "error codes" begin
        exact = certificate_umbrella_companions(C)
        rational(tables) = () -> export_reward_certificate(C, ks, us, σ;
                                                           numeric_mode=:rational_exact,
                                                           exact_tables=tables)
        id = apex(C)
        ms = collect(parts(id, :Mechanism))

        # An internal variable: a boundary variable's reference is also on its foot.
        unset = deepcopy(B)
        set_subpart!(apex(unset), 3, :space_ref, nothing)
        e = certificate_error(() -> export_reward_certificate(unset, ks, us, σ))
        @test e.code === :unset_reference && e.path == "network.variableData[2].spaceRef"
        unset = deepcopy(A)
        set_subpart!(apex(unset), 2, :kernel_ref, nothing)
        e = certificate_error(() -> export_reward_certificate(unset, ks, us, Strategy()))
        @test e.code === :unset_reference && e.path == "network.mechanisms[1].kernelRef"

        odd = deepcopy(A)
        set_subpart!(apex(odd), 1, :kernel_ref, RewardCertificateTestRef())
        e = certificate_error(() -> export_reward_certificate(odd, ks, us, Strategy()))
        @test e.code === :unsupported_reference &&
              e.path == "network.mechanisms[0].kernelRef"
        @test occursin("RewardCertificateTestRef", e.message)

        policy = deepcopy(A)
        set_subpart!(apex(policy), 2, :kernel_ref, PolicyRef(:Umbrella))
        e = certificate_error(() -> export_reward_certificate(policy, ks, us, Strategy()))
        @test e.code === :policy_reference_on_chance &&
              e.path == "network.mechanisms[1].kernelRef"
        @test occursin("Forecast_mechanism", e.message)

        # Two decisions named :D, which share a policy, on information of different sizes.
        d1 = influence_diagram(:X => [:a, :b], :D => [:u, :v]; mechanisms=[:X => ()],
                               decisions=[:D => :X], closed=false)
        d2 = influence_diagram(:Y => [:a, :b, :c], :D => [:u, :v]; mechanisms=[:Y => ()],
                               decisions=[:D => :Y], closed=false)
        twice = otimes(Open(d1), Open(d2))
        e = certificate_error(() -> export_reward_certificate(twice,
                                                              Dict{Symbol,FiniteKernel}(),
                                                              Dict{Symbol,AbstractUtility}(),
                                                              Strategy(:D =>
                                                                           ConstantPolicy(:u))))
        @test e.code === :inconsistent_decision && e.path == "network.mechanisms[3]"
        @test occursin(":D", e.message)
        # Equally named decisions of one shape share their policy.
        same = otimes(Open(d1), Open(d1))
        X = FiniteSpace(:X, [:a, :b])
        ks2 = Dict{Symbol,FiniteKernel}(:X => FiniteKernel(FiniteSpace(FiniteAxis[]), X,
                                                           [0.25, 0.75]))
        c2 = export_reward_certificate(same, ks2, Dict{Symbol,AbstractUtility}(),
                                       Strategy(:D => ConstantPolicy(:v)))
        @test only(c2["strategy"]) == (decision="D", actions=[2, 2])
        @test [g.name for g in c2["network"].mechanisms] == ["X_mechanism", "X_mechanism",
                                                             "D", "D"]

        # B holds 4 utility cells, a policy of 3 and K and W of 6 each: 19 in all.
        @test export_reward_certificate(B, ks, us, σ; max_entries=19) isa OrderedDict
        e = certificate_error(() -> export_reward_certificate(B, ks, us, σ; max_entries=18))
        @test e.code === :too_many_entries && occursin("19", e.message)

        weather = FiniteAxis(:Weather, [:sunny, :rainy])
        umbrella = FiniteAxis(:Umbrella, [:take, :leave])
        inf = Dict{Symbol,AbstractUtility}(:U => TabularUtility([weather, umbrella],
                                                                [0.0 Inf; 0.0 0.0]))
        e = certificate_error(() -> export_reward_certificate(B, ks, inf, σ))
        @test e.code === :non_finite && e.path == "utilities[0].cells[1]"

        e = certificate_error(rational(delete!(copy(exact), (:chance, ms[2], (1, 2)))))
        @test e.code === :missing_companion && e.path == "chance_tables[1].cells[5]"
        e = certificate_error(rational(merge(exact, Dict((:chance, ms[2], (2, 0)) => 0))))
        @test e.code === :extra_companion && e.path == "exact_tables"
        e = certificate_error(rational(merge(exact, Dict((:utility, 7, (0, 0)) => 0))))
        @test e.code === :extra_companion
        e = certificate_error(rational(merge(exact,
                                             Dict((:chance, ms[1], (0,)) => 71 // 100))))
        @test e.code === :companion_rounding && e.path == "chance_tables[0].cells[0]"
        e = certificate_error(rational(merge(exact,
                                             Dict((:utility, 1, (0, 1)) => 100 + 1 // 2^40))))
        @test e.code === :companion_rounding && e.path == "utilities[0].cells[1]"

        msg = sprint(showerror, e)
        @test occursin("RewardCertificateError: :companion_rounding at utilities[0].cells[1]",
                       msg)
        @test RewardCertificateError(:x, "", "m") == RewardCertificateError(:x, "", "m")
        @test sprint(showerror, RewardCertificateError(:too_many_entries, "", "no room")) ==
              "RewardCertificateError: :too_many_entries: no room"
    end

    @testset "argument errors and errors that pass through" begin
        exact = certificate_umbrella_companions(C)
        export_(; kw...) = export_reward_certificate(C, ks, us, σ; kw...)
        @test_throws ArgumentError export_(; numeric_mode=:decimal)
        @test_throws ArgumentError export_(; numeric_mode="binary64_exact")
        @test_throws ArgumentError export_(; exact_tables=exact)
        @test_throws ArgumentError export_(; numeric_mode=:rational_exact)
        @test_throws ArgumentError export_(; numeric_mode=:rational_exact,
                                           exact_tables=[1 // 2])
        for (key, value) in (((:cpt, 1, (0,)), 1), ((:chance, 1, [0]), 1),
                             ((:chance, true, (0,)), 1), ((:chance, 1, (0,), 0), 1),
                             ((:chance, 1, (0,)), 0.7), ((:chance, 1, (0,)), 1 // 0),
                             ((:chance, 1, (0,)), true))
            @test_throws ArgumentError export_(; numeric_mode=:rational_exact,
                                               exact_tables=merge(Dict{Any,Any}(exact),
                                                                  Dict{Any,Any}(key =>
                                                                                    value)))
        end
        # Two keys that name one cell (a `Dict` would merge them; an `IdDict` does not).
        dup = IdDict{Any,Any}(exact)
        dup[(:chance, Int32(1), (0,))] = 7 // 10
        @test_throws ArgumentError export_(; numeric_mode=:rational_exact, exact_tables=dup)
        @test_throws ArgumentError export_(; description=:umbrella)
        @test_throws ArgumentError export_(; max_entries=-1)
        @test_throws ArgumentError export_(; max_entries=true)
        @test_throws ArgumentError export_(; max_entries=1.5e6)
        # interpret's errors pass through unchanged.
        stoch = StochasticPolicy(:Umbrella,
                                 random_kernel(Xoshiro(3), FiniteSpace(axis(apex(B), 2)),
                                               FiniteSpace(axis(apex(B), 3))))
        @test_throws ArgumentError export_reward_certificate(B, ks, us,
                                                             Strategy(:Umbrella => stoch))
        @test_throws IncompleteStrategyError export_reward_certificate(B, ks, us,
                                                                       Strategy())
        @test_throws MissingKernelError export_reward_certificate(A,
                                                                  Dict{Symbol,FiniteKernel}(),
                                                                  us, Strategy())
        @test_throws MissingUtilityError export_reward_certificate(B, ks,
                                                                   Dict{Symbol,
                                                                        AbstractUtility}(),
                                                                   σ)
        # validate's errors pass through unchanged.
        hidden = umbrella_decision(; observed=Symbol[], validate=false)
        @test_throws DiagramInterfaceError export_reward_certificate(hidden, ks, us, σ)
    end

    @testset "key order of the JSON Schema" begin
        docs = joinpath(@__DIR__, "..", "docs", "src")
        schema = CertJSON3.read(read(joinpath(docs, "reward-certificate-v1.schema.json"),
                                     String))
        defs = schema[Symbol("\$defs")]
        @test schema[Symbol("\$schema")] == "https://json-schema.org/draft/2020-12/schema"
        for (name, cert) in certificate_fixtures()
            @test schema_key_order(CertJSON3.read(certificate_fixture_bytes(cert)), schema,
                                   defs)
        end
        # The check sees a swap at the top level and one inside a rational companion.
        text = certificate_fixture_bytes(Dict(certificate_fixtures())["umbrella-rational.json"])
        top = replace(text,
                      "{\"format\":\"OpenInfluence.RewardCertificate/v1\",\"numeric_mode\":\"rational_exact\"," => "{\"numeric_mode\":\"rational_exact\",\"format\":\"OpenInfluence.RewardCertificate/v1\",")
        nested = replace(text,
                         "\"q\":{\"num\":\"7\",\"den\":\"10\"}" => "\"q\":{\"den\":\"10\",\"num\":\"7\"}";
                         count=1)
        for swapped in (top, nested)
            @test swapped != text
            @test !schema_key_order(CertJSON3.read(swapped), schema, defs)
        end
    end

    @testset "the committed fixtures, byte for byte" begin
        fixtures = certificate_fixtures()
        @test first.(fixtures) ==
              ["umbrella-decision.json", "umbrella-closed.json", "two-stage-composite.json",
               "relay.json", "dyadic.json", "umbrella-rational.json",
               "two-stage-rational.json", "relay-rational.json"]
        for (name, cert) in fixtures
            path = joinpath(CERTIFICATE_FIXTURE_DIR, name)
            @test isfile(path)
            bytes = certificate_fixture_bytes(cert)
            @test endswith(bytes, "}\n") && count('\n', bytes) == 1
            # Up to the recorded Julia version, which names the Julia that ran the exporter.
            @test certificate_fixture_comparable(read(path, String)) ==
                  certificate_fixture_comparable(bytes)
            @test certificate_fixture_bytes(cert) == bytes
        end
        # The fixtures say what the plan says they hold.
        byname = Dict(fixtures)
        closed = byname["umbrella-closed.json"]
        @test isempty(closed["network"].inputs) && isempty(closed["network"].outputs)
        @test cell_f64.(closed["result"].K) == [1.0]
        @test cell_f64(only(closed["result"].W)) ≈ expected_utility(m, σ)
        dec = byname["umbrella-decision.json"]
        @test dec["observability"].inputs == ["hidden", "observed"]
        @test cell_f64(only(byname["two-stage-composite.json"]["result"].W)) ≈ 21
        relay = byname["relay.json"]
        @test [r.varId for r in relay["network"].outputs] == [0, 1, 1]
        @test only(relay["network"].inputs).varId == 0
        @test byname["umbrella-rational.json"]["numeric_mode"] == "rational_exact"
        # Dyadic rows sum to exactly one, as do the rows of K.
        dy = byname["dyadic.json"]
        rowsum(cells, n) = [sum(Rational{BigInt}(cell_f64(c)) for c in cells[i:(i + n - 1)])
                            for i in 1:n:length(cells)]
        @test all(==(1), rowsum(only(dy["chance_tables"]).cells, 3))
        @test all(==(1), rowsum(dy["result"].K, 3))
        @test !all(==(1),
                   rowsum(last(byname["umbrella-closed.json"]["chance_tables"]).cells,
                          3))
    end
end
