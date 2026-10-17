# Optimisation of open influence diagrams (ADR 0018, decision 4): the contextual identity
# against the closed-composite oracle, contextual optimisation against brute force and the
# existing solvers, and the bundle's two obstructions: isolated optimisation
# (`INF-ISOLATED-OBSTRUCTION`, the Lean witness) and hidden-input pointwise maximisation
# (`INF-HIDDEN-OBSTRUCTION`). Uses the fixtures and helpers of `test_open.jl`,
# `test_composition.jl` and `test_semantics.jl`.

# The contextual identity for `f ⋅ g` under `σ` and `τ`, prior `μ` on `f`'s inputs and
# continuation `c` on `g`'s outputs, in both forms; returns the three values.
function contextual_forms(f, g, ks, us, σ, τ; μ=nothing, c=nothing)
    rf, rg = interpret(f, ks, us, σ), interpret(g, ks, us, τ)
    whole = contextual_value(compose(f, g; no_forgetting=false), ks, us,
                             merge_strategies(σ, τ); prior=μ, continuation=c)
    via_suffix = contextual_value(rf; prior=μ,
                                  continuation=continuation_value(rg; continuation=c))
    L = contextual_value(rf; prior=μ, continuation=zeros(length(codom(rf))))
    via_prefix = L + contextual_value(rg; prior=boundary_law(rf; prior=μ), continuation=c)
    return whole, via_suffix, via_prefix
end

function identity_holds(f, g, ks, us, σ, τ; μ=nothing, c=nothing, eu=nothing)
    whole, s, p = contextual_forms(f, g, ks, us, σ, τ; μ=μ, c=c)
    return whole ≈ s ≈ p && (eu === nothing || whole ≈ eu)
end

# A random probability vector of length `n`.
random_prior(rng, n) = (v = rand(rng, n) .+ 0.01; v ./ sum(v))

# The best composite value of `f ⋅ g` by brute force: the maximum over the strategies of
# `f` and of `g` of the oracle's expected utility.
function brute_force_optimum(f, g, ks, us)
    C = compose(f, g; no_forgetting=false)
    return maximum(oracle(C, ks, us, merge_strategies(σ, τ))
                   for σ in all_deterministic_strategies(apex(f)),
                       τ in all_deterministic_strategies(apex(g)))
end

# The two contextual forms of the optimum of `f ⋅ g` (the bundle's `INF-ATTAINMENT`):
# suffix table first (Lean) and prefix policy first (Rocq and HOL4).
function suffix_first(f, g, ks, us; kw...)
    return maximum(contextual_optimize(f, ks, us;
                                       continuation=continuation_value(g, ks, us, τ),
                                       kw...).expected_utility
                   for τ in all_deterministic_strategies(apex(g)))
end
function prefix_first(f, g, ks, us; kw...)
    return maximum(begin
                       rf = interpret(f, ks, us, σ)
                       L = contextual_value(rf; continuation=zeros(length(codom(rf))))
                       L +
                       contextual_optimize(g, ks, us; prior=boundary_law(rf),
                                           kw...).expected_utility
                   end
                   for σ in all_deterministic_strategies(apex(f)))
end

# The Lean witness of `INF-ISOLATED-OBSTRUCTION` (`SerialInfluence.Witness` in the sealed
# bundle) as two open influence diagrams. A fair hidden bit `H`; the early action `A`
# observes nothing and costs `-[A]`; the late action `B` observes only `A`, and the late
# utilities are `4[A]` and `2[B = H]`. The boundary carries `H` hidden and `A` observed.
# Labels are ordered false first, as Lean's `Bool`.
const LEAN_BOOL = [:no, :yes]

function lean_early()
    id = influence_diagram(:H => LEAN_BOOL, :A => LEAN_BOOL; mechanisms=[:H => ()],
                           decisions=[:A => Symbol[]], utilities=[:EarlyCost => :A],
                           closed=false)
    return Open(id; outputs=[:H, :A], observed=[:A])
end

function lean_late(; information=(:A,), observed=[:A])
    id = influence_diagram(:H => LEAN_BOOL, :A => LEAN_BOOL, :B => LEAN_BOOL;
                           decisions=[:B => information],
                           utilities=[:LateBenefit => :A, :HiddenMatch => (:H, :B)],
                           closed=false)
    return Open(id; inputs=[:H, :A], observed=observed)
end

function lean_tables()
    ax(x) = FiniteAxis(x, LEAN_BOOL)
    ks = Dict{Symbol,FiniteKernel}(:H => state(FiniteSpace(:H, LEAN_BOOL), [0.5, 0.5]))
    us = Dict{Symbol,AbstractUtility}(:EarlyCost => TabularUtility([ax(:A)], [0, -1]),
                                      :LateBenefit => TabularUtility([ax(:A)], [0, 4]),
                                      :HiddenMatch => TabularUtility([ax(:H), ax(:B)],
                                                                     [2 0; 0 2]))
    return ks, us
end

constant(d, a) = Strategy(d => ConstantPolicy(a))

@testset "Optimisation" begin
    m = umbrella_model()
    ks, us = kernels_by_name(m), bound_utilities(m)
    A, B = umbrella_chance(), umbrella_decision()

    @testset "contextual value of a reward kernel" begin
        rng = Xoshiro(30)
        X = tensor_space(FiniteSpace(:X1, [:a, :b]), FiniteSpace(:X2, [:p, :q, :r]))
        Y = FiniteSpace(:Y, [:u, :v])
        r = random_reward_kernel(rng, X, Y)
        μ, c = random_prior(rng, length(X)), randn(rng, length(Y))
        Km, Wm = kernel_matrix(kernel(r)), reward_matrix(r)
        expected = sum(μ[x] * (Wm[y, x] + Km[y, x] * c[y]) for x in 1:6, y in 1:2)
        @test contextual_value(r; prior=μ, continuation=c) ≈ expected
        @test continuation_value(r; continuation=c) ≈
              [sum(Wm[y, x] + Km[y, x] * c[y] for y in 1:2) for x in 1:6]
        @test boundary_law(r; prior=μ) ≈ Km * μ && sum(boundary_law(r; prior=μ)) ≈ 1
        # A prior given as a state kernel, and a continuation as a reward kernel to I.
        @test contextual_value(r; prior=state(X, reshape(μ, size(X))), continuation=c) ≈
              expected
        g = RewardKernel(discard_kernel(Y), c)
        @test contextual_value(r; prior=μ, continuation=g) ≈ expected
        @test continuation_value(g) == c
        # Composition: the identity on reward kernels.
        h = random_reward_kernel(rng, Y, FiniteSpace(:Z, [:s, :t, :w]))
        cz = randn(rng, 3)
        @test contextual_value(compose(r, h); prior=μ, continuation=cz) ≈
              contextual_value(r; prior=μ,
                               continuation=continuation_value(h; continuation=cz)) ≈
              contextual_value(r; prior=μ, continuation=zeros(2)) +
              contextual_value(h; prior=boundary_law(r; prior=μ), continuation=cz)
        # The context must be given for a nonempty interface, and well formed.
        @test_throws ArgumentError contextual_value(r; continuation=c)
        @test_throws ArgumentError contextual_value(r; prior=μ)
        @test_throws ArgumentError contextual_value(r; prior=μ[1:5], continuation=c)
        @test_throws ArgumentError contextual_value(r; prior=2 .* μ, continuation=c)
        bad = copy(μ)
        bad[1:2] .= (bad[1] + bad[2] + 0.5, -0.5)
        @test_throws ArgumentError contextual_value(r; prior=bad, continuation=c)
        @test_throws ArgumentError contextual_value(r; prior=fill(NaN, 6), continuation=c)
        @test_throws ArgumentError contextual_value(r; prior=μ, continuation=[1.0, Inf])
        @test_throws ArgumentError contextual_value(r; prior=μ, continuation=ones(3))
        @test_throws ArgumentError contextual_value(r; prior=μ, continuation=h)
        @test_throws ArgumentError contextual_value(r; prior=state(Y, [0.5, 0.5]),
                                                    continuation=c)
        @test_throws ArgumentError contextual_value(r; prior="uniform", continuation=c)
        # A closed reward kernel needs no context: its value is its reward.
        closed = RewardKernel(state(FiniteSpace(), [1.0]), fill(7.5))
        @test contextual_value(closed) == 7.5
    end

    @testset "the contextual identity on the umbrella split, every strategy" begin
        for τ in all_deterministic_strategies(apex(B))
            eu = expected_utility(m, τ)
            @test identity_holds(A, B, ks, us, Strategy(), τ; eu=eu)
            # The suffix's value function from each boundary state, and the prefix's law.
            c = continuation_value(B, ks, us, τ)
            @test length(c) == 6
            @test contextual_value(A, ks, us, Strategy(); continuation=c) ≈ eu
            ν = boundary_law(A, ks, us, Strategy())
            @test contextual_value(B, ks, us, τ; prior=ν) ≈ eu
            @test contextual_value(compose(A, B), ks, us, τ) ≈ eu
        end
        # The model forms read the tables through the apex's references, so they need a
        # diagram whose references are bound, such as the model's own syntax.
        whole = Open(syntax(m))
        τ = constant(:Umbrella, :take)
        @test contextual_value(whole, m, τ) ≈ expected_utility(m, τ)
        @test continuation_value(whole, m, τ) ≈ [expected_utility(m, τ)]
        @test boundary_law(whole, m, τ) ≈ [1.0]
        @test_throws MissingKernelError contextual_value(compose(A, B), m, τ)
        @test_throws ArgumentError contextual_value(whole, observe(m, :Forecast => :rainy),
                                                    τ)
    end

    @testset "the contextual identity on the oil wildcatter split, every strategy" begin
        mo = two_stage_model()
        kso, uso = kernels_by_name(mo), bound_utilities(mo)
        P, Q = two_stage_test(), two_stage_drill()
        C = compose(P, Q)
        for σ in all_deterministic_strategies(apex(C))
            @test identity_holds(P, Q, kso, uso, restrict(σ, P), restrict(σ, Q);
                                 eu=oracle(C, kso, uso, σ))
        end
    end

    @testset "the contextual identity on the grazing splits" begin
        mg = reference_grazing_model()
        ksg, usg = kernels_by_name(mg), bound_utilities(mg)
        id = reference_grazing_diagram()
        rng = Xoshiro(47)
        σs = vcat([constant(:GrazingManagement, a)
                   for a in [:exclude, :reduce, :maintain]],
                  [random_strategy(rng, id) for _ in 1:3])
        M, H = grazing_management(), grazing_habitat()
        E, D = grazing_environment(), grazing_decision()
        for σ in σs
            eu = expected_utility(mg, σ)
            @test identity_holds(M, H, ksg, usg, σ, Strategy(); eu=eu)
            @test identity_holds(E, D, ksg, usg, Strategy(), σ; eu=eu)
        end
    end

    @testset "the contextual identity on random splits" begin
        for seed in 1:8
            rng = Xoshiro(100 + seed)
            spec = random_spec(rng)
            ks_, us_ = spec.kernels, spec.utilities
            n = length(spec.vars)
            P, S = random_pieces(spec, [rand(rng, 2:n)])
            C = compose(P, S; no_forgetting=false)
            for σ in some_strategies(rng, apex(C))
                @test identity_holds(P, S, ks_, us_, restrict(σ, P), restrict(σ, S);
                                     eu=oracle(C, ks_, us_, σ))
            end
            # Three pieces: an open prefix with an arbitrary continuation, and an open
            # suffix with an arbitrary prior.
            k1 = rand(rng, 2:(n - 1))
            P3, M3, S3 = random_pieces(spec, [k1, rand(rng, (k1 + 1):n)])
            σ = random_strategy(rng, apex(C))
            σP, σM, σS = (restrict(σ, o) for o in (P3, M3, S3))
            ny = length(codom(interpret(M3, ks_, us_, σM)))
            nx = length(dom(interpret(M3, ks_, us_, σM)))
            @test identity_holds(P3, M3, ks_, us_, σP, σM; c=randn(rng, ny))
            @test identity_holds(M3, S3, ks_, us_, σM, σS; μ=random_prior(rng, nx))
            @test identity_holds(P3, compose(M3, S3; no_forgetting=false), ks_, us_, σP,
                                 merge_strategies(σM, σS); eu=oracle(C, ks_, us_, σ))
        end
    end

    @testset "optimize on closed composites" begin
        C = compose(A, B)
        sol = optimize(C, ks, us)
        @test sol isa DecisionSolution && sol.expected_utility ≈ 77
        @test optimize(C, ks, us; backend=ExhaustivePolicySearch()).expected_utility ≈ 77
        @test optimize(Open(syntax(m)), m).expected_utility ≈ optimize(m).expected_utility
        @test contextual_value(C, ks, us, sol.strategy) ≈ 77
        @test maximum(oracle(C, ks, us, τ) for τ in all_deterministic_strategies(apex(C))) ≈
              77
        # Kernels and utilities keyed by reference, as `interpret` takes them.
        whole = Open(syntax(m))
        @test optimize(whole, kernels(m), Dict(NamedRef("U") => us[:U])).expected_utility ≈
              77
        # Only a closed composite has an expected utility of its own.
        @test_throws ArgumentError optimize(A, ks, us)
        @test_throws ArgumentError optimize(B, ks, us)
        @test_throws ArgumentError optimize(Open(syntax(m)),
                                            observe(m, :Forecast => :rainy))
        @test_throws MissingKernelError optimize(C, Dict{Symbol,FiniteKernel}(), us)
        @test_throws MissingUtilityError optimize(C, ks, Dict{Symbol,AbstractUtility}())
        # The oil wildcatter: both backends agree with brute force.
        mo = two_stage_model()
        kso, uso = kernels_by_name(mo), bound_utilities(mo)
        Co = compose(two_stage_test(), two_stage_drill())
        @test optimize(Co, kso, uso).expected_utility ≈ 21
        @test optimize(Co, kso, uso; backend=ExhaustivePolicySearch()).expected_utility ≈ 21
    end

    @testset "contextual optimisation attains the composite optimum" begin
        # The umbrella: the decision downstream, against the law the chance part induces.
        ν = boundary_law(A, ks, us, Strategy())
        sol = contextual_optimize(B, ks, us; prior=ν)
        @test sol isa DecisionSolution && sol.expected_utility ≈ 77
        @test sol.diagnostics.nstrategies == 8 && sol.diagnostics.method === :value_table
        @test expected_utility(m, sol.strategy) ≈ 77
        @test contextual_optimize(Open(syntax(m)), m).strategy == sol.strategy
        bf = contextual_optimize(B, ks, us; prior=ν, brute_force=true)
        @test bf.expected_utility ≈ sol.expected_utility && bf.strategy == sol.strategy
        @test bf.diagnostics.method === :brute_force
        @test contextual_optimize(compose(A, B), ks, us).expected_utility ≈ 77
        @test_throws PolicySearchTooLargeError contextual_optimize(B, ks, us; prior=ν,
                                                                   max_policies=7)
        @test_throws ArgumentError contextual_optimize(B, ks, us)
        @test_throws ModelTooLargeError contextual_optimize(B, ks, us; prior=ν,
                                                            max_states=2)
        # A component without decisions has one strategy, the empty one.
        none = contextual_optimize(A, ks, us;
                                   continuation=continuation_value(B, ks, us,
                                                                   sol.strategy))
        @test none.strategy == Strategy() && none.expected_utility ≈ 77
        # The oil wildcatter: both contextual forms and brute force agree with the solvers,
        # and the prefix optimised against the optimal suffix's value function attains it.
        mo = two_stage_model()
        kso, uso = kernels_by_name(mo), bound_utilities(mo)
        P, Q = two_stage_test(), two_stage_drill()
        global_ = optimize(compose(P, Q), kso, uso)
        @test global_.expected_utility ≈ 21
        @test brute_force_optimum(P, Q, kso, uso) ≈ 21
        @test suffix_first(P, Q, kso, uso) ≈ 21 && prefix_first(P, Q, kso, uso) ≈ 21
        τstar = restrict(global_.strategy, Q)
        sP = contextual_optimize(P, kso, uso;
                                 continuation=continuation_value(Q, kso, uso, τstar))
        @test sP.expected_utility ≈ 21
        @test expected_utility(mo, merge_strategies(sP.strategy, τstar)) ≈ 21
        σstar = restrict(global_.strategy, P)
        sQ = contextual_optimize(Q, kso, uso; prior=boundary_law(P, kso, uso, σstar))
        Lstar = contextual_value(P, kso, uso, σstar; continuation=zeros(12))
        @test Lstar + sQ.expected_utility ≈ 21
        bQ = contextual_optimize(Q, kso, uso; prior=boundary_law(P, kso, uso, σstar),
                                 brute_force=true)
        @test bQ.expected_utility ≈ sQ.expected_utility && bQ.strategy == sQ.strategy
        @test sQ.diagnostics.nstrategies == 64
        # The grazing diagram at both boundaries: the decision upstream against the
        # habitat's value function, and downstream against the environment's law.
        mg = reference_grazing_model()
        ksg, usg = kernels_by_name(mg), bound_utilities(mg)
        M, H = grazing_management(), grazing_habitat()
        E, D = grazing_environment(), grazing_decision()
        best = optimize(compose(E, D), ksg, usg).expected_utility
        @test best ≈ optimize(mg).expected_utility
        @test optimize(compose(M, H), ksg, usg;
                       backend=ExhaustivePolicySearch()).expected_utility ≈
              best
        sM = contextual_optimize(M, ksg, usg;
                                 continuation=continuation_value(H, ksg, usg, Strategy()))
        @test sM.expected_utility ≈ best && expected_utility(mg, sM.strategy) ≈ best
        sD = contextual_optimize(D, ksg, usg; prior=boundary_law(E, ksg, usg, Strategy()))
        @test sD.expected_utility ≈ best && expected_utility(mg, sD.strategy) ≈ best
        @test sD.diagnostics.nstrategies == 3^9
    end

    @testset "contextual optimisation on random splits against brute force" begin
        checked = 0
        for seed in 1:40
            checked == 6 && break
            rng = Xoshiro(200 + seed)
            spec = random_spec(rng)
            ks_, us_ = spec.kernels, spec.utilities
            P, S = random_pieces(spec, [rand(rng, 2:length(spec.vars))])
            C = compose(P, S; no_forgetting=false)
            # Brute force enumerates every strategy pair: only small searches.
            n_deterministic_strategies(apex(P)) <= 64 &&
                n_deterministic_strategies(apex(S)) <= 64 || continue
            checked += 1
            best = optimize(C, ks_, us_; backend=ExhaustivePolicySearch()).expected_utility
            @test brute_force_optimum(P, S, ks_, us_) ≈ best
            @test suffix_first(P, S, ks_, us_) ≈ best
            @test prefix_first(P, S, ks_, us_) ≈ best
            # The value table agrees with brute force strategy by strategy, on an open
            # component with an arbitrary context.
            ny = length(codom(interpret(P, ks_, us_, random_strategy(rng, apex(P)))))
            c = randn(rng, ny)
            vt = contextual_optimize(P, ks_, us_; continuation=c)
            bf = contextual_optimize(P, ks_, us_; continuation=c, brute_force=true)
            @test vt.expected_utility ≈ bf.expected_utility
            @test contextual_value(P, ks_, us_, vt.strategy; continuation=c) ≈
                  vt.expected_utility
        end
        @test checked == 6
    end

    @testset "isolated optimisation does not compose (INF-ISOLATED-OBSTRUCTION)" begin
        ksl, usl = lean_tables()
        early, late = lean_early(), lean_late()
        whole = compose(early, late)
        @test isvalid(whole) && inputs(whole) == outputs(whole) == Symbol[]
        # The closed objective is 1 + 3p, p the early probability of `A`: 1 or 4 for the two
        # early actions, whatever the late policy (`whole_pure_early`).
        for a in LEAN_BOOL, τ in all_deterministic_strategies(apex(late))
            σ = merge_strategies(constant(:A, a), τ)
            @test oracle(whole, ksl, usl, σ) == contextual_value(whole, ksl, usl, σ) ==
                  (a === :yes ? 4.0 : 1.0)
        end
        # Isolated optimisation, as the bundle defines it: each component optimal under the
        # actual induced prior with a zero continuation. The early component (whose prior
        # is the fair bit it generates) chooses `A = no`, value 0 against -1
        # (`early_isolated_optimal`).
        iso_early = contextual_optimize(early, ksl, usl; continuation=zeros(4))
        @test iso_early.strategy[:A].table[] === :no && iso_early.expected_utility == 0
        @test contextual_value(early, ksl, usl, constant(:A, :yes);
                               continuation=zeros(4)) ==
              -1
        # The late component under the boundary law that choice induces: every legal policy
        # is worth 1 (`late_isolated`), and the search returns the first, `B = no`.
        ν = boundary_law(early, ksl, usl, iso_early.strategy)
        @test ν == [0.5, 0.5, 0.0, 0.0]
        for τ in all_deterministic_strategies(apex(late))
            @test contextual_value(late, ksl, usl, τ; prior=ν) == 1
        end
        iso_late = contextual_optimize(late, ksl, usl; prior=ν)
        @test iso_late.expected_utility == 1 && all(==(:no), iso_late.strategy[:B].table)
        # Composed, the isolated choices are worth 1; the composite attains 4.
        isolated = contextual_value(whole, ksl, usl,
                                    merge_strategies(iso_early.strategy, iso_late.strategy))
        @test isolated ==
              oracle(whole, ksl, usl,
                     merge_strategies(iso_early.strategy, iso_late.strategy)) ==
              1
        opt = optimize(whole, ksl, usl)
        @test opt.expected_utility == 4 && opt.strategy[:A].table[] === :yes
        @test optimize(whole, ksl, usl;
                       backend=ExhaustivePolicySearch()).expected_utility ==
              4
        @test isolated < opt.expected_utility
        @test (isolated, opt.expected_utility) == (1.0, 4.0)
        # The contextual repair: optimised against the late component's value function,
        # the early component chooses `A = yes` and attains 4, in both contextual forms.
        cτ = continuation_value(late, ksl, usl, iso_late.strategy)
        repaired = contextual_optimize(early, ksl, usl; continuation=cτ)
        @test repaired.strategy[:A].table[] === :yes && repaired.expected_utility == 4
        @test suffix_first(early, late, ksl, usl) == 4
        @test prefix_first(early, late, ksl, usl) == 4
    end

    @testset "hidden-input pointwise maximisation is illegal (INF-HIDDEN-OBSTRUCTION)" begin
        ksl, usl = lean_tables()
        early, late = lean_early(), lean_late()
        ν = boundary_law(early, ksl, usl, constant(:A, :no))
        # The legal late optimum under the induced law is 1: `B` reads only `A`.
        legal = contextual_optimize(late, ksl, usl; prior=ν)
        @test legal.expected_utility == 1
        @test legal.strategy[:B].information == [FiniteAxis(:A, LEAN_BOOL)]
        @test legal.diagnostics.nstrategies == 2^2
        # Maximising separately at each boundary state (h, a) instead: the value of each
        # action from each state, and the pointwise maximum, which is worth 2.
        cs = [continuation_value(late, ksl, usl, constant(:B, b)) for b in LEAN_BOOL]
        pointwise = sum(ν .* max.(cs...))
        @test pointwise == 2 && legal.expected_utility < pointwise
        # The pointwise maximiser picks `B = H`: it differs between the states (no, no) and
        # (yes, no), which agree on `A`, so it is not a function of `B`'s information.
        argmaxes = [LEAN_BOOL[argmax([cs[1][j], cs[2][j]])] for j in 1:4]
        @test argmaxes[1:2] == [:no, :yes]
        # As a policy it would read the hidden input `H`, which rule 3 forbids.
        e = try
            lean_late(; information=(:H, :A))
        catch err
            err
        end
        @test e isa DiagramInterfaceError
        @test (e.rule, e.variable, e.by, e.kind) == (3, :H, :B, :hidden_input)
        # Declaring `H` observed makes such a policy legal, with value 2, but it changes the
        # problem: the early component hides `H`, so the two no longer compose.
        peek = lean_late(; information=(:H, :A), observed=[:H, :A])
        @test contextual_optimize(peek, ksl, usl; prior=ν).expected_utility == 2
        @test_throws ObservabilityMismatchError compose(early, peek)
    end
end
