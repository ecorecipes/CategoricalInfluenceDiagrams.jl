# Behavioural (stochastic) strategies (ADR 0022), checked against the closed-composite
# oracle: `interpret` of a behavioural strategy is `InfluenceDiagrams`' expected utility of
# the instantiated composite, it is functorial, and it never beats the best deterministic
# strategy when every decision has its own policy (with or without evidence), as the Lean
# module `Behaviour` and `InfluenceDiagrams`' `exists_deterministic_optimal_all` prove.

# A behavioural strategy of `id`: every decision draws its action from a random table.
function random_behaviour(rng, id)
    ps = Dict{Symbol,AbstractPolicy}()
    for d in parts(id, :Decision)
        name = decision_name(id, d)
        haskey(ps, name) && continue
        ps[name] = StochasticPolicy(name,
                                    random_kernel(rng, FiniteSpace(info_axes(id, d)),
                                                  FiniteSpace(action_axis(id, d))))
    end
    return Strategy(ps)
end

@testset "behavioural strategies" begin
    m = umbrella_model()
    ks, us = kernels_by_name(m), bound_utilities(m)
    A, B = umbrella_chance(), umbrella_decision()
    whole = compose(A, B)

    @testset "the umbrella problem" begin
        rng = Xoshiro(22)
        for _ in 1:5
            β = random_behaviour(rng, apex(B))
            r = interpret(whole, ks, us, β)
            @test closed_ok(r, oracle(whole, ks, us, β))
            @test compose(interpret(A, ks, us, Strategy()), interpret(B, ks, us, β)) ≈ r
            # Never better than the deterministic optimum, with or without evidence.
            @test contextual_value(r) <=
                  optimize(whole, ks, us; backend=ExhaustivePolicySearch()).expected_utility +
                  1e-9
            for ev in (:Weather => :rainy, :Forecast => :cloudy)
                @test conditional_value(whole, ks, us, β; evidence=ev) <=
                      contextual_optimize(whole, ks, us; evidence=ev).expected_utility + 1e-9
            end
        end
        # A deterministic policy as a point-mass table is the deterministic policy.
        id = apex(B)
        d = only(parts(id, :Decision))
        σ = Strategy(:Umbrella => DeterministicPolicy(:Umbrella, info_axes(id, d),
                                                      action_axis(id, d),
                                                      [:leave, :take, :take]))
        point = Strategy(:Umbrella => StochasticPolicy(:Umbrella, policy_kernel(σ[:Umbrella])))
        @test interpret(B, ks, us, point) ≈ interpret(B, ks, us, σ)
    end

    @testset "random splits: oracle, functoriality, sufficiency, equilibria" begin
        rng = Xoshiro(20261022)
        checked = 0
        for trial in 1:8
            spec = random_spec(rng)
            n = length(spec.vars)
            n >= 3 || continue
            k1 = rand(rng, 2:(n - 1))
            P, M, S = random_pieces(spec, [k1, rand(rng, (k1 + 1):n)])
            lim = (; no_forgetting=false)
            whole3 = foldl((f, g) -> compose(f, g; lim...), [P, M, S])
            ks3, us3 = spec.kernels, spec.utilities
            β = random_behaviour(rng, apex(whole3))
            r = interpret(whole3, ks3, us3, β)
            @test closed_ok(r, oracle(whole3, ks3, us3, β))
            @test compose(interpret(P, ks3, us3, β), interpret(M, ks3, us3, β),
                          interpret(S, ks3, us3, β)) ≈ r
            # The middle component in context: a behavioural policy is never better than
            # the deterministic best response.
            ctx = component_contexts([P, M, S], ks3, us3, β; lim...)
            @test contextual_value(M, ks3, us3, β; prior=ctx[2].prior,
                                   continuation=ctx[2].continuation) <=
                  contextual_optimize(M, ks3, us3; prior=ctx[2].prior,
                                      continuation=ctx[2].continuation).expected_utility +
                  1e-9
            # Regrets of a behavioural strategy are nonnegative, and best responses lead to
            # a deterministic equilibrium.
            @test all(>=(-1e-9), regrets([P, M, S], ks3, us3, β; lim...))
            brd = best_response_dynamics([P, M, S], ks3, us3, β; lim...)
            @test brd.converged && all(diff(brd.values) .> 0)
            @test is_equilibrium([P, M, S], ks3, us3, brd.strategy; lim...)
            checked += 1
        end
        @test checked > 0
    end
end
