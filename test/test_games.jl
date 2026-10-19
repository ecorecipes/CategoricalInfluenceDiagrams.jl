# Lenses and open-game equilibria (ADR 0020), checked against the closed composite: the
# contexts of a chain are the lens passes, a component's regret is the gain in the whole
# chain's value from its best unilateral change (found by brute force over that component's
# strategies), optima are equilibria, and best-response dynamics ends at an equilibrium
# without lowering the value. The two witnesses are those of the Lean module `Lens`.

# The best unilateral gain of component `i` of the chain under `σ`, by brute force on the
# closed composite.
function unilateral_gain(chain, ks, us, σ, i)
    whole = foldl((f, g) -> compose(f, g; no_forgetting=false), chain)
    base = contextual_value(whole, ks, us, σ)
    mine = Set(decision_names(apex(chain[i])))
    isempty(mine) && return 0.0
    others = Strategy(Dict{Symbol,AbstractPolicy}(d => σ[d] for d in keys(σ) if !(d in mine)))
    return maximum(contextual_value(whole, ks, us, merge_strategies(others, τ))
                   for τ in all_deterministic_strategies(apex(chain[i]))) - base
end

# The two decisions of the Lean coordination witness: `A` then `B`, `B` not observing `A`,
# paying 2 when both are taken and 1 when neither is.
function coordination_chain()
    first = Open(influence_diagram(:A => LEAN_BOOL; decisions=[:A => Symbol[]],
                                   closed=false); outputs=[:A])
    second = Open(influence_diagram(:A => LEAN_BOOL, :B => LEAN_BOOL;
                                    decisions=[:B => Symbol[]],
                                    utilities=[:Payoff => (:A, :B)], closed=false);
                  inputs=[:A])
    ax(x) = FiniteAxis(x, LEAN_BOOL)
    us = Dict{Symbol,AbstractUtility}(:Payoff => TabularUtility([ax(:A), ax(:B)],
                                                                [1 0; 0 2]))
    return [first, second], Dict{Symbol,FiniteKernel}(), us
end

@testset "games" begin
    @testset "the contexts are the lens passes" begin
        chain = [lean_early(), lean_late()]
        ks, us = lean_tables()
        for σ in all_deterministic_strategies(apex(compose(chain...)))
            ctx = component_contexts(chain, ks, us, σ)
            @test length(ctx) == 2
            @test ctx[1].prior == [1.0]
            @test ctx[1].continuation ≈
                  continuation_value(chain[2], ks, us, restrict(σ, chain[2]))
            @test ctx[2].prior ≈ boundary_law(chain[1], ks, us, restrict(σ, chain[1]))
            @test ctx[2].continuation == [0.0]
        end
    end

    @testset "the obstruction witness: equilibria take the early action" begin
        chain = [lean_early(), lean_late()]
        ks, us = lean_tables()
        for a in LEAN_BOOL, τ in all_deterministic_strategies(apex(chain[2]))
            σ = merge_strategies(constant(:A, a), τ)
            r = regrets(chain, ks, us, σ)
            @test r ≈ [a === :no ? 3.0 : 0.0, 0.0] atol = 1e-12
            @test is_equilibrium(chain, ks, us, σ) == (a === :yes)
            @test r ≈ [unilateral_gain(chain, ks, us, σ, i) for i in 1:2] atol = 1e-12
        end
        start = merge_strategies(constant(:A, :no), constant(:B, :no))
        brd = best_response_dynamics(chain, ks, us, start)
        @test brd.converged && brd.rounds == 2
        @test brd.values ≈ [1.0, 4.0] && brd.changed == [1] && brd.value ≈ 4.0
        @test only(policy_table(brd.strategy[:A])) === :yes
        @test is_equilibrium(chain, ks, us, brd.strategy)
    end

    @testset "the coordination witness: an equilibrium need not be optimal" begin
        chain, ks, us = coordination_chain()
        whole = compose(chain...)
        values = Dict((a, b) => contextual_value(whole, ks, us,
                                                 merge_strategies(constant(:A, a),
                                                                  constant(:B, b)))
                      for a in LEAN_BOOL, b in LEAN_BOOL)
        @test values[(:no, :no)] ≈ 1 && values[(:yes, :yes)] ≈ 2
        for a in LEAN_BOOL, b in LEAN_BOOL
            σ = merge_strategies(constant(:A, a), constant(:B, b))
            @test is_equilibrium(chain, ks, us, σ) == (a === b)
        end
        best = optimize(whole, ks, us; backend=ExhaustivePolicySearch())
        @test best.expected_utility ≈ 2
        @test is_equilibrium(chain, ks, us, best.strategy)
        stuck = best_response_dynamics(chain, ks, us,
                                       merge_strategies(constant(:A, :no), constant(:B, :no)))
        @test stuck.converged && stuck.rounds == 1 && stuck.values ≈ [1.0]
        @test stuck.value < best.expected_utility
        moved = best_response_dynamics(chain, ks, us,
                                       merge_strategies(constant(:A, :no), constant(:B, :yes)))
        @test moved.values ≈ [0.0, 2.0] && moved.changed == [1]
    end

    @testset "random chains of three pieces" begin
        rng = Xoshiro(20261019)
        checked_optimum = 0
        for trial in 1:8
            spec = random_spec(rng)
            n = length(spec.vars)
            n >= 3 || continue
            k1 = rand(rng, 2:(n - 1))
            P, M, S = random_pieces(spec, [k1, rand(rng, (k1 + 1):n)])
            chain = [P, M, S]
            ks, us = spec.kernels, spec.utilities
            # Random splits are limited-memory composites in general (rule 6 off).
            whole = foldl((f, g) -> compose(f, g; no_forgetting=false), chain)
            lim = (; no_forgetting=false)
            for σ in some_strategies(rng, apex(whole); n=3)
                ctx = component_contexts(chain, ks, us, σ; lim...)
                # The contextual identity along the chain: each component's value in its
                # context is the chain's value less the reward of the components before it.
                total = contextual_value(whole, ks, us, σ)
                earlier = 0.0
                for i in 1:3
                    r = interpret(chain[i], ks, us, restrict(σ, chain[i]))
                    @test contextual_value(r; prior=ctx[i].prior,
                                           continuation=ctx[i].continuation) + earlier ≈
                          total atol = 1e-9
                    earlier += contextual_value(r; prior=ctx[i].prior,
                                                continuation=zeros(length(ctx[i].continuation)))
                end
                # The lens laws: bracketing the chain differently gives the same contexts.
                left = component_contexts([P, compose(M, S; lim...)], ks, us, σ; lim...)
                right = component_contexts([compose(P, M; lim...), S], ks, us, σ; lim...)
                @test left[1].continuation ≈ ctx[1].continuation
                @test left[2].prior ≈ ctx[2].prior
                @test right[1].continuation ≈ ctx[2].continuation
                @test right[2].prior ≈ ctx[3].prior
                # Regrets are unilateral gains on the closed composite.
                @test regrets(chain, ks, us, σ; lim...) ≈
                      [unilateral_gain(chain, ks, us, σ, i) for i in 1:3] atol = 1e-9
                # Best-response dynamics never lowers the value and ends at an equilibrium.
                brd = best_response_dynamics(chain, ks, us, σ; lim...)
                @test brd.converged
                @test all(diff(brd.values) .> 0)
                @test brd.value ≈ contextual_value(whole, ks, us, brd.strategy)
                @test is_equilibrium(chain, ks, us, brd.strategy; lim...)
            end
            # A global optimum, by brute force, is an equilibrium.
            if n_deterministic_strategies(apex(whole)) <= 4096
                best = argmax(σ -> contextual_value(whole, ks, us, σ),
                              collect(all_deterministic_strategies(apex(whole))))
                @test is_equilibrium(chain, ks, us, best; lim...)
                checked_optimum += 1
            end
        end
        @test checked_optimum > 0
    end

    @testset "perfect equilibria: the Lean threat witness" begin
        ax(x) = FiniteAxis(x, LEAN_BOOL)
        first = Open(influence_diagram(:Act => LEAN_BOOL; decisions=[:Act => Symbol[]],
                                       closed=false); outputs=[:Act], observed=[:Act])
        second = Open(influence_diagram(:Act => LEAN_BOOL, :Cooperate => LEAN_BOOL;
                                        decisions=[:Cooperate => (:Act,)],
                                        utilities=[:Payoff => (:Act, :Cooperate)],
                                        closed=false); inputs=[:Act], observed=[:Act])
        chain = [first, second]
        ks = Dict{Symbol,FiniteKernel}()
        us = Dict{Symbol,AbstractUtility}(:Payoff => TabularUtility([ax(:Act), ax(:Cooperate)],
                                                                    [1 1; 0 4]))
        respond(t) = Strategy(:Cooperate => DeterministicPolicy(:Cooperate, [ax(:Act)],
                                                                ax(:Cooperate), t))
        # Not acting, against a refusal that is never tested, is an equilibrium worth 1.
        threat = merge_strategies(constant(:Act, :no), respond([:no, :no]))
        @test is_equilibrium(chain, ks, us, threat)
        @test contextual_value(compose(chain...), ks, us, threat) ≈ 1
        # It is not perfect: from the unreached state the second component gains 4.
        @test regrets(chain, ks, us, threat; perfect=true) ≈ [0.0, 4.0]
        @test !is_equilibrium(chain, ks, us, threat; perfect=true)
        # The perfect equilibria act and cooperate, worth the optimum 4.
        for t in ([:no, :yes], [:yes, :yes])
            σ = merge_strategies(constant(:Act, :yes), respond(t))
            @test is_equilibrium(chain, ks, us, σ; perfect=true)
            @test is_equilibrium(chain, ks, us, σ)
            @test contextual_value(compose(chain...), ks, us, σ) ≈ 4
        end
        @test !is_equilibrium(chain, ks, us,
                              merge_strategies(constant(:Act, :no), respond([:no, :yes]));
                              perfect=true)
        @test_throws ArgumentError regrets(chain, ks, us, threat; perfect=true,
                                           evidence=:Act => :no)
    end

    @testset "errors" begin
        chain = [lean_early(), lean_late()]
        ks, us = lean_tables()
        σ = merge_strategies(constant(:A, :no), constant(:B, :no))
        @test_throws ArgumentError component_contexts(OpenInfluenceDiagram[], ks, us, σ)
        @test_throws InterfaceMismatchError regrets([lean_early(), lean_early()], ks, us, σ)
        @test_throws ArgumentError is_equilibrium(chain, ks, us, σ; tol=-1)
        @test_throws ArgumentError best_response_dynamics(chain, ks, us, σ; tol=-1)
        @test_throws ArgumentError best_response_dynamics(chain, ks, us, σ; max_rounds=0)
        capped = best_response_dynamics(chain, ks, us, σ; max_rounds=1)
        @test !capped.converged && capped.rounds == 1
    end
end
