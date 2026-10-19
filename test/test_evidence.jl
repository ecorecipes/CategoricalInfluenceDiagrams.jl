# Evidence across a boundary (ADR 0021), checked against the closed-composite oracle: the
# reward kernel of a diagram with evidence is substochastic and composes as any other; the
# evidence mass and the evidence-weighted value are pairings of a state and an effect, the
# same at every cut; the conditional value of a closed composite is `InfluenceDiagrams`'
# `expected_utility` of the model with the evidence observed; normalising each component
# on its own evidence is not sound (the Lean witness of `local_normalisation_obstruction`).

# Up to two pieces of random hard evidence on the chance variables of `spec`.
function random_evidence(rng, spec)
    chance = [v for v in spec.vars if v.kind === :chance]
    picks = Random.shuffle(rng, chance)[1:rand(rng, 1:min(2, length(chance)))]
    return Dict{Symbol,Symbol}(v.name => rand(rng, v.labels) for v in picks)
end

# The part of the evidence `ev` on the apex of `o`.
function evidence_on(o::OpenInfluenceDiagram, ev)
    return Dict{Symbol,Symbol}(x => s for (x, s) in ev if has_variable(apex(o), x))
end

# The oracle's value given the evidence, or `nothing` when it is impossible under `σ`.
function oracle_given(c::OpenInfluenceDiagram, ks, us, σ, ev)
    m = observe(oracle_model(apex(c), ks, us), sort!(collect(ev); by=first))
    return try
        expected_utility(m, σ)
    catch e
        e isa ImpossibleEvidenceError || rethrow()
        nothing
    end
end

# The prefix and suffix of the Lean witness: a uniform binary state worth 1 when true, and
# a sighting nine times likelier when it is true.
function sighting_chain()
    prefix = Open(influence_diagram(:State => LEAN_BOOL; mechanisms=[:State => ()],
                                    utilities=[:Worth => :State], closed=false);
                  outputs=[:State])
    suffix = Open(influence_diagram(:State => LEAN_BOOL, :Sighting => [:seen, :unseen];
                                    mechanisms=[:Sighting => :State], closed=false);
                  inputs=[:State])
    ax = FiniteAxis(:State, LEAN_BOOL)
    ks = Dict{Symbol,FiniteKernel}(:State => state(FiniteSpace(ax), [0.5, 0.5]),
                                   :Sighting => FiniteKernel(FiniteSpace(ax),
                                                             FiniteSpace(:Sighting,
                                                                         [:seen, :unseen]),
                                                             [0.1 0.9; 0.9 0.1]))
    us = Dict{Symbol,AbstractUtility}(:Worth => TabularUtility([ax], [0.0, 1.0]))
    return prefix, suffix, ks, us
end

@testset "evidence" begin
    m = umbrella_model()
    ks, us = kernels_by_name(m), bound_utilities(m)
    A, B = umbrella_chance(), umbrella_decision()
    whole = compose(A, B)
    weather, forecast = [:sunny, :rainy], [:sunny, :cloudy, :rainy]

    @testset "interpret with evidence: the oracle and functoriality" begin
        for σ in all_deterministic_strategies(apex(B))
            for ev in vcat([Dict(:Weather => w) for w in weather],
                           [Dict(:Forecast => f) for f in forecast],
                           [Dict(:Weather => :rainy, :Forecast => :cloudy)])
                r = interpret(whole, ks, us, σ; evidence=ev)
                mo = observe(m, sort!(collect(ev); by=first))
                @test kernel(r).table[] ≈ evidence_mass(r)
                @test conditional_value(r) ≈ expected_utility(mo, σ)
                @test conditional_value(whole, ks, us, σ; evidence=ev) ≈
                      expected_utility(mo, σ)
                @test contextual_value(r) ≈ reward(r)[]
                # Evidence on the shared boundary may go to either side, or both.
                for (ea, eb) in ((ev, Dict{Symbol,Symbol}()), (Dict{Symbol,Symbol}(), ev),
                                 (ev, ev))
                    @test compose(interpret(A, ks, us, Strategy(); evidence=ea),
                                  interpret(B, ks, us, σ; evidence=eb)) ≈ r
                end
            end
            # The probability of the evidence, against the oracle's marginal.
            P = marginal(instantiate(m, σ), [:Forecast])
            for (i, f) in enumerate(forecast)
                @test evidence_mass(whole, ks, us, σ; evidence=:Forecast => f) ≈
                      P.table[i]
            end
        end
        # An open component with evidence on an input conditions that input.
        σ = Strategy(:Umbrella => ConstantPolicy(:take))
        rb = interpret(B, ks, us, σ; evidence=:Weather => :rainy)
        plain = interpret(B, ks, us, σ)
        mask = [w === :rainy for w in weather, _ in forecast]
        @test vec(kernel(rb).table) ≈ vec(kernel(plain).table) .* vec(mask)
        @test vec(reward(rb)) ≈ vec(reward(plain)) .* vec(mask)
        # Without evidence nothing changes.
        @test interpret(B, ks, us, σ; evidence=Dict{Symbol,Symbol}()) == plain
        @test interpret(B, ks, us, σ; evidence=nothing) == plain
    end

    @testset "contexts with evidence: states, effects and every cut" begin
        σ = Strategy(:Umbrella => ConstantPolicy(:leave))
        rA = interpret(A, ks, us, Strategy())
        rB = interpret(B, ks, us, σ)
        # Without evidence, the state is the boundary law with the prefix's reward, the
        # effect has mass one and the value function, and the two values agree.
        s = boundary_state(rA)
        @test vec(kernel(s).table) ≈ boundary_law(rA)
        @test vec(reward(s)) ≈ zeros(6)
        e = continuation_effect(rB)
        @test vec(kernel(e).table) ≈ ones(6)
        @test vec(reward(e)) ≈ continuation_value(rB)
        @test conditional_value(rB; prior=s) ≈ contextual_value(rB; prior=s) ≈
              contextual_value(whole, ks, us, σ)
        @test contextual_value(rA; continuation=e) ≈ contextual_value(whole, ks, us, σ)
        # With evidence on each side, every cut gives the same mass, value and conditional
        # value, and that of the composite.
        for ea in (Dict{Symbol,Symbol}(), Dict(:Forecast => :cloudy)),
            eb in (Dict{Symbol,Symbol}(), Dict(:Weather => :rainy))

            rA = interpret(A, ks, us, Strategy(); evidence=ea)
            rB = interpret(B, ks, us, σ; evidence=eb)
            ev = merge(ea, eb)
            c = conditional_value(whole, ks, us, σ; evidence=ev)
            @test conditional_value(rA; continuation=continuation_effect(rB)) ≈ c
            @test conditional_value(rB; prior=boundary_state(rA)) ≈ c
            @test conditional_value(compose(rA, rB)) ≈ c
            Z = evidence_mass(whole, ks, us, σ; evidence=ev)
            @test evidence_mass(rA; continuation=continuation_effect(rB)) ≈ Z
            @test evidence_mass(rB; prior=boundary_state(rA)) ≈ Z
            @test sum(boundary_law(rA) .* vec(kernel(continuation_effect(rB)).table)) ≈ Z
            V = contextual_value(whole, ks, us, σ; evidence=ev)
            @test contextual_value(rA; continuation=continuation_effect(rB)) ≈ V
            @test contextual_value(rB; prior=boundary_state(rA)) ≈ V
            @test V ≈ c * Z
        end
    end

    @testset "random splits with evidence" begin
        rng = Xoshiro(20261020)
        tested = 0
        for trial in 1:10
            spec = random_spec(rng)
            n = length(spec.vars)
            n >= 3 || continue
            k1 = rand(rng, 2:(n - 1))
            P, M, S = random_pieces(spec, [k1, rand(rng, (k1 + 1):n)])
            lim = (; no_forgetting=false)
            whole3 = foldl((f, g) -> compose(f, g; lim...), [P, M, S])
            ks3, us3 = spec.kernels, spec.utilities
            ev = random_evidence(rng, spec)
            for σ in some_strategies(rng, apex(whole3); n=4)
                rs = [interpret(o, ks3, us3, restrict(σ, o); evidence=evidence_on(o, ev))
                      for o in (P, M, S)]
                r = interpret(whole3, ks3, us3, σ; evidence=ev)
                # Functoriality with evidence, under either bracketing.
                @test compose(rs...) ≈ r
                PM = compose(P, M; lim...)
                MS = compose(M, S; lim...)
                @test compose(interpret(PM, ks3, us3, restrict(σ, PM);
                                        evidence=evidence_on(PM, ev)), rs[3]) ≈ r
                @test compose(rs[1],
                              interpret(MS, ks3, us3, restrict(σ, MS);
                                        evidence=evidence_on(MS, ev))) ≈ r
                truth = oracle_given(whole3, ks3, us3, σ, ev)
                if truth === nothing
                    @test evidence_mass(r) == 0
                    @test_throws ImpossibleEvidenceError conditional_value(whole3, ks3, us3,
                                                                           σ; evidence=ev)
                    continue
                end
                tested += 1
                @test conditional_value(whole3, ks3, us3, σ; evidence=ev) ≈ truth
                # The middle component in its context gives the whole conditional value.
                s = boundary_state(rs[1])
                e = continuation_effect(rs[3])
                @test conditional_value(rs[2]; prior=s, continuation=e) ≈ truth
                @test conditional_value(M, ks3, us3, restrict(σ, M); prior=s,
                                        continuation=e, evidence=evidence_on(M, ev)) ≈ truth
            end
            # The best strategy of the middle component in its context is the best
            # unilateral change of the whole, by brute force on the closed composite.
            σ = first(some_strategies(rng, apex(whole3); n=1))
            s = boundary_state(interpret(P, ks3, us3, restrict(σ, P);
                                         evidence=evidence_on(P, ev)))
            e = continuation_effect(interpret(S, ks3, us3, restrict(σ, S);
                                              evidence=evidence_on(S, ev)))
            others = Strategy(Dict{Symbol,AbstractPolicy}(d => σ[d] for d in keys(σ)
                                                          if !(d in decision_names(apex(M)))))
            values = Float64[]
            for τ in all_deterministic_strategies(apex(M))
                v = oracle_given(whole3, ks3, us3, merge_strategies(others, τ), ev)
                v === nothing || push!(values, v)
            end
            if isempty(values)
                @test_throws ImpossibleEvidenceError contextual_optimize(M, ks3, us3;
                                                                         prior=s,
                                                                         continuation=e,
                                                                         evidence=evidence_on(M,
                                                                                              ev))
            else
                sol = contextual_optimize(M, ks3, us3; prior=s, continuation=e,
                                          evidence=evidence_on(M, ev))
                @test sol.expected_utility ≈ maximum(values)
                @test sol.diagnostics.method === :conditional
            end
            # The optimum of the closed composite given the evidence, against the search on
            # the model.
            if n_deterministic_strategies(apex(whole3)) <= 4096
                mo = observe(oracle_model(apex(whole3), ks3, us3),
                             sort!(collect(ev); by=first))
                best = try
                    optimize(mo; backend=ExhaustivePolicySearch()).expected_utility
                catch err
                    err isa ImpossibleEvidenceError || rethrow()
                    nothing
                end
                best === nothing ||
                    @test contextual_optimize(whole3, ks3, us3;
                                              evidence=ev).expected_utility ≈ best
                best === nothing ||
                    @test optimize(whole3, ks3, us3; evidence=ev,
                                   backend=ExhaustivePolicySearch()).expected_utility ≈ best
            end
        end
        @test tested > 0
    end

    @testset "equilibria given evidence" begin
        rng = Xoshiro(20261021)
        checked = 0
        for trial in 1:8
            spec = random_spec(rng)
            n = length(spec.vars)
            n >= 3 || continue
            k1 = rand(rng, 2:(n - 1))
            chain = random_pieces(spec, [k1, rand(rng, (k1 + 1):n)])
            ks3, us3 = spec.kernels, spec.utilities
            lim = (; no_forgetting=false)
            whole3 = foldl((f, g) -> compose(f, g; lim...), chain)
            ev = random_evidence(rng, spec)
            for σ in some_strategies(rng, apex(whole3); n=3)
                truth = oracle_given(whole3, ks3, us3, σ, ev)
                truth === nothing && continue
                checked += 1
                ctx = component_contexts(chain, ks3, us3, σ; evidence=ev, lim...)
                for i in 1:3
                    @test ctx[i].prior isa RewardKernel && ctx[i].continuation isa RewardKernel
                    @test conditional_value(chain[i], ks3, us3, restrict(σ, chain[i]);
                                            prior=ctx[i].prior,
                                            continuation=ctx[i].continuation,
                                            evidence=evidence_on(chain[i], ev)) ≈ truth
                end
                # Regrets are the unilateral gains in the conditional value of the whole,
                # among strategies that keep the evidence possible.
                gains = map(1:3) do i
                    mine = Set(decision_names(apex(chain[i])))
                    isempty(mine) && return 0.0
                    others = Strategy(Dict{Symbol,AbstractPolicy}(d => σ[d] for d in keys(σ)
                                                                  if !(d in mine)))
                    vs = [oracle_given(whole3, ks3, us3, merge_strategies(others, τ), ev)
                          for τ in all_deterministic_strategies(apex(chain[i]))]
                    return maximum(v for v in vs if v !== nothing) - truth
                end
                @test regrets(chain, ks3, us3, σ; evidence=ev, lim...) ≈ gains atol = 1e-9
                brd = best_response_dynamics(chain, ks3, us3, σ; evidence=ev, lim...)
                @test brd.converged
                @test all(diff(brd.values) .> 0)
                @test brd.value ≈ oracle_given(whole3, ks3, us3, brd.strategy, ev)
                @test is_equilibrium(chain, ks3, us3, brd.strategy; evidence=ev, lim...)
            end
        end
        @test checked > 0
    end

    @testset "local normalisation is not sound (the Lean witness)" begin
        prefix, suffix, ksl, usl = sighting_chain()
        closed = compose(prefix, suffix)
        seen = :Sighting => :seen
        @test conditional_value(closed, ksl, usl, Strategy(); evidence=seen) ≈ 0.9
        # Normalising each component on its own evidence: the suffix's evidence has
        # probability one given its input once normalised, so the prefix keeps its prior.
        rp = interpret(prefix, ksl, usl, Strategy())
        rs = interpret(suffix, ksl, usl, Strategy(); evidence=seen)
        mass = vec(sum(kernel_matrix(kernel(rs)); dims=1))
        Kn = reshape(vec(kernel_matrix(kernel(rs))) ./ mass, size(kernel(rs).table))
        Wn = reshape(vec(reward_matrix(rs)) ./ mass, size(reward(rs)))
        normalised = RewardKernel(FiniteKernel(dom(rs), codom(rs), Kn), Wn)
        @test conditional_value(compose(rp, normalised)) ≈ 0.5
        # Carrying the mass across the boundary gives the composite's value.
        @test conditional_value(rp; continuation=continuation_effect(rs)) ≈ 0.9
        @test conditional_value(rs; prior=boundary_state(rp)) ≈ 0.9
    end

    @testset "ADR 0014: rare and impossible evidence" begin
        ax = FiniteAxis(:Rare, [:a, :b])
        rare = Open(influence_diagram(:Rare => [:a, :b], :Echo => [:e, :f];
                                      mechanisms=[:Rare => (), :Echo => :Rare],
                                      utilities=[:V => :Rare], closed=false))
        usr = Dict{Symbol,AbstractUtility}(:V => TabularUtility([ax], [1.0, 0.0]))
        tables(pb) = Dict{Symbol,FiniteKernel}(:Rare => state(FiniteSpace(ax), [1e-200, 1.0]),
                                               :Echo => FiniteKernel(FiniteSpace(ax),
                                                                     FiniteSpace(:Echo,
                                                                                 [:e, :f]),
                                                                     [1e-200 pb; 1.0 1.0-pb]))
        # The mass 1e-400 underflows; the exact fallback resolves it.
        ksr = tables(0.0)
        @test evidence_mass(rare, ksr, usr, Strategy(); evidence=:Echo => :e) == 0
        @test conditional_value(rare, ksr, usr, Strategy(); evidence=:Echo => :e) == 1.0
        # The reward-kernel form has only the underflowed tables, exactly zero.
        @test_throws ImpossibleEvidenceError conditional_value(interpret(rare, ksr, usr,
                                                                         Strategy();
                                                                         evidence=:Echo => :e))
        # Exactly impossible evidence.
        ksz = Dict{Symbol,FiniteKernel}(:Rare => state(FiniteSpace(ax), [0.5, 0.5]),
                                        :Echo => FiniteKernel(FiniteSpace(ax),
                                                              FiniteSpace(:Echo, [:e, :f]),
                                                              [0.0 0.0; 1.0 1.0]))
        @test_throws ImpossibleEvidenceError conditional_value(rare, ksz, usr, Strategy();
                                                               evidence=:Echo => :e)
        @test_throws ImpossibleEvidenceError contextual_optimize(rare, ksz, usr;
                                                                 evidence=:Echo => :e)
        # The mixed case: both terms of the mass below floatmin, the answer exact.
        ksm = tables(1e-300)
        exact = big(1e-200)^2 / (big(1e-200)^2 + big(1e-300))
        @test conditional_value(rare, ksm, usr, Strategy(); evidence=:Echo => :e) ≈
              Float64(exact)
    end

    @testset "errors" begin
        σ = Strategy(:Umbrella => ConstantPolicy(:take))
        @test_throws UnknownVariableError interpret(B, ks, us, σ; evidence=:Rain => :yes)
        @test_throws UnknownStateError interpret(B, ks, us, σ; evidence=:Weather => :snowy)
        @test_throws EvidenceOnActionError interpret(B, ks, us, σ;
                                                     evidence=:Umbrella => :take)
        @test_throws ArgumentError interpret(B, ks, us, σ;
                                             evidence=[:Weather => :sunny,
                                                       :Weather => :rainy])
        @test_throws ArgumentError interpret(B, ks, us, σ; evidence=42)
        @test_throws ArgumentError interpret(B, ks, us, σ; evidence=["Weather" => "sunny"])
        @test_throws ArgumentError interpret(B, ks, us, σ; evidence=[:Weather => :sunny, 1])
        rA = interpret(A, ks, us, Strategy())
        rB = interpret(B, ks, us, σ)
        # Contexts of the wrong shape, or a state of mass above one.
        @test_throws ArgumentError contextual_value(rB; prior=continuation_effect(rB))
        @test_throws ArgumentError contextual_value(rA; continuation=boundary_state(rA))
        heavy = RewardKernel(FiniteKernel(FiniteSpace(), codom(rA),
                                          fill(0.5, size(codom(rA))); check=false))
        @test_throws ArgumentError conditional_value(rB; prior=heavy)
        # Evidence on a chain must name a variable of some component.
        @test_throws UnknownVariableError component_contexts([A, B], ks, us, σ;
                                                             evidence=:Rain => :yes)
        @test_throws EvidenceOnActionError regrets([A, B], ks, us, σ;
                                                   evidence=:Umbrella => :take)
    end
end
