# Shared policies (ADR 0024): chains whose components share a policy, the multi-self
# regrets of `policy_regrets` (the first-order condition of the Lean module `SharedPolicy`)
# and the grid search over behavioural strategies, on the absent-minded driver of the Lean
# module `Behaviour` and on random chains against finite differences.

using Random: Xoshiro

const DRIVE = [:exit, :cont]

# The absent-minded driver as a chain: the first junction's decision `X1`, then the second
# junction's decision `X2`, which does not observe `X1`. Exiting first pays 0, exiting second
# 4, continuing at both 1.
function driver_chain()
    first = Open(influence_diagram(:X1 => DRIVE; decisions=[:X1 => Symbol[]], closed=false);
                 outputs=[:X1])
    second = Open(influence_diagram(:X1 => DRIVE, :X2 => DRIVE; decisions=[:X2 => Symbol[]],
                                    utilities=[:Pay => (:X1, :X2)], closed=false);
                  inputs=[:X1])
    ax(x) = FiniteAxis(x, DRIVE)
    us = Dict{Symbol,AbstractUtility}(:Pay => TabularUtility([ax(:X1), ax(:X2)], [0 0; 4 1]))
    return [first, second], Dict{Symbol,FiniteKernel}(), us
end

# A behavioural policy for `d` on its spaces in component `o`, from its action columns.
function columns_policy(o, d, table)
    id = apex(o)
    k = first(x for x in parts(id, :Decision) if decision_name(id, x) == d)
    I = FiniteSpace(FiniteAxis[axis(id, v) for v in decision_information(id, k)])
    A = FiniteSpace(axis(id, decision_variable(id, k)))
    return StochasticPolicy(d, FiniteKernel(I, A, reshape(table, size(A)..., size(I)...)))
end

continue_with(chain, p) = Strategy(:X1 => columns_policy(chain[1], :X1, [1 - p, p]))

# The value of the tied chain, the derivative of the driver's value `4p - 3p²` towards
# continuing and towards exiting, and the regret they give.
drive_value(chain, ks, us, σ) =
    contextual_value(compose(chain...), ks, us,
                     Strategy(:X1 => σ[:X1],
                              :X2 => StochasticPolicy(:X2,
                                                      FiniteKernel(FiniteSpace(),
                                                                   FiniteSpace(:X2, DRIVE),
                                                                   policy_kernel(σ[:X1]).table))))
drive_regret(p) = max((1 - p) * (4 - 6p), -p * (4 - 6p))

@testset "shared policies" begin
    chain, ks, us = driver_chain()
    tie = [[:X1, :X2]]

    @testset "the absent-minded driver" begin
        for p in (0.0, 0.25, 0.5, 2 / 3, 0.9, 1.0)
            σ = continue_with(chain, p)
            @test drive_value(chain, ks, us, σ) ≈ 4p - 3p^2 atol = 1e-12
            r = policy_regrets(chain, ks, us, σ; shared=tie)
            @test collect(keys(r)) == [:X1]
            @test r[:X1] ≈ drive_regret(p) atol = 1e-12
            @test is_policy_equilibrium(chain, ks, us, σ; shared=tie) == (p ≈ 2 / 3)
        end
        # The grid search finds the randomised optimum, which is worth 4/3 against at most 1
        # for either deterministic policy.
        s = shared_policy_search(chain, ks, us; shared=tie, grid=3)
        @test s.nstrategies == 4
        @test s.value ≈ 4 / 3 atol = 1e-12
        @test vec(policy_kernel(s.strategy[:X1]).table) ≈ [1 / 3, 2 / 3] atol = 1e-12
        @test collect(keys(policies(s.strategy))) == [:X1]
        @test is_policy_equilibrium(chain, ks, us, s.strategy; shared=tie)
        @test shared_policy_search(chain, ks, us; shared=tie, grid=1).value ≈ 1 atol = 1e-12
        # At the shared optimum each junction alone would still change: the regrets of the
        # untied decisions are positive (the Lean `per_use_gains`: 2/3 at the first).
        untied = Strategy(:X1 => s.strategy[:X1],
                          :X2 => columns_policy(chain[2], :X2, [1 / 3, 2 / 3]))
        r = policy_regrets(chain, ks, us, untied)
        @test r[:X1] ≈ 2 / 3 atol = 1e-12
        @test r[:X2] ≈ 4 / 3 atol = 1e-12
        # With a policy each, the deterministic pair (continue, exit) is optimal at 4.
        free = shared_policy_search(chain, ks, us; grid=2)
        @test free.value ≈ 4 atol = 1e-12
        @test vec(policy_kernel(free.strategy[:X1]).table) ≈ [0, 1]
        @test vec(policy_kernel(free.strategy[:X2]).table) ≈ [1, 0]
        @test all(v -> abs(v) < 1e-12, values(policy_regrets(chain, ks, us, free.strategy)))
    end

    @testset "regrets are derivatives on random chains" begin
        rng = Xoshiro(240)
        ax(x) = FiniteAxis(x, [:a, :b])
        first_part = Open(influence_diagram(:H => [:a, :b], :D1 => [:a, :b];
                                            mechanisms=[:H => ()],
                                            decisions=[:D1 => [:H]],
                                            utilities=[:U1 => (:H, :D1)], closed=false);
                          outputs=[:H, :D1], observed=[:H])
        second_part = Open(influence_diagram(:H => [:a, :b], :D1 => [:a, :b],
                                             :D2 => [:a, :b, :c]; decisions=[:D2 => [:H]],
                                             utilities=[:U2 => (:H, :D1, :D2)],
                                             closed=false); inputs=[:H, :D1], observed=[:H])
        @test_throws ArgumentError policy_regrets([first_part, second_part],
                                                  Dict{Symbol,FiniteKernel}(),
                                                  Dict{Symbol,AbstractUtility}(),
                                                  Strategy(); shared=[[:D1, :D2]])
        third_part = Open(influence_diagram(:H => [:a, :b], :D1 => [:a, :b],
                                            :D2 => [:a, :b]; decisions=[:D2 => [:H]],
                                            utilities=[:U2 => (:H, :D1, :D2)],
                                            closed=false); inputs=[:H, :D1], observed=[:H])
        rchain = [first_part, third_part]
        for _ in 1:5
            p = rand(rng)
            rks = Dict{Symbol,FiniteKernel}(:H => state(FiniteSpace(:H, [:a, :b]), [p, 1 - p]))
            rus = Dict{Symbol,AbstractUtility}(:U1 => TabularUtility([ax(:H), ax(:D1)],
                                                                     randn(rng, 2, 2)),
                                               :U2 => TabularUtility([ax(:H), ax(:D1),
                                                                      ax(:D2)],
                                                                     randn(rng, 2, 2, 2)))
            q = rand(rng, 2)
            head(t) = Strategy(:D1 => columns_policy(rchain[1], :D1, t))
            tied(t) = Strategy(:D1 => columns_policy(rchain[1], :D1, t),
                               :D2 => columns_policy(rchain[2], :D2, t))
            whole = compose(rchain...)
            t0 = [q[1] 1-q[2]; 1-q[1] q[2]]
            σ = head(t0)
            r = policy_regrets(rchain, rks, rus, σ; shared=[[:D1, :D2]])
            # The regret is the largest derivative towards a deterministic policy, by finite
            # differences on the tied chain.
            h = 1e-6
            base = contextual_value(whole, rks, rus, tied(t0))
            derivs = map(Iterators.product(1:2, 1:2)) do (a1, a2)
                π = zeros(2, 2)
                π[a1, 1] = 1
                π[a2, 2] = 1
                (contextual_value(whole, rks, rus, tied((1 - h) .* t0 .+ h .* π)) - base) / h
            end
            @test r[:D1] ≈ maximum(derivs) atol = 1e-4
            # Untied, each regret is the exact gain of changing that decision alone.
            untied = tied(t0)
            ru = policy_regrets(rchain, rks, rus, untied)
            for (d, part) in ((:D1, 1), (:D2, 2))
                others = Strategy(Dict{Symbol,AbstractPolicy}(k => untied[k]
                                                              for k in keys(untied)
                                                              if k != d))
                gain = maximum(contextual_value(whole, rks, rus, merge_strategies(others, τ))
                               for τ in all_deterministic_strategies(apex(rchain[part]))) -
                       base
                @test ru[d] ≈ gain atol = 1e-12
            end
        end
    end

    @testset "errors" begin
        σ = continue_with(chain, 0.5)
        @test_throws ArgumentError policy_regrets(chain, ks, us, σ; shared=[[:X1, :Z]])
        @test_throws ArgumentError policy_regrets(chain, ks, us, σ; shared=[[:X1, :X1]])
        @test_throws ArgumentError policy_regrets(chain, ks, us, σ; shared=[Symbol[]])
        both = Strategy(:X1 => σ[:X1], :X2 => columns_policy(chain[2], :X2, [0.5, 0.5]))
        @test_throws ArgumentError policy_regrets(chain, ks, us, both; shared=tie)
        @test_throws ArgumentError is_policy_equilibrium(chain, ks, us, σ; shared=tie, tol=-1)
        @test_throws ArgumentError shared_policy_search(chain, ks, us; shared=tie, grid=0)
        @test_throws PolicySearchTooLargeError shared_policy_search(chain, ks, us; grid=10,
                                                                    max_strategies=10)
    end
end
