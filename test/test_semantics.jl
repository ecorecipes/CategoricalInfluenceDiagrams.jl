using Random: Random, Xoshiro, AbstractRNG
using FiniteKernels: compose_kernel, tensor_kernel, identity_kernel, discard_kernel,
                     SpaceMismatchError, factors

# The semantics of ADR 0018, decision 3, checked against the closed-composite oracle: for a
# closed composite `c`, `interpret(c, σ)` is the 1×1 reward kernel `(1, EU)`, where `EU` is
# `expected_utility` of the instantiated diagram. Kernels are keyed by target variable name
# and utilities by utility name, so that one table source serves the pieces of a split and
# the composite.

# Chance kernels of a model, keyed by target variable name.
function kernels_by_name(m)
    return Dict{Symbol,FiniteKernel}(x => kernel(m, x)
                                     for x in chance_names(syntax(m)))
end

# The closed composite `id` as a model with the given tables: the oracle's input.
function oracle_model(id, ks, us)
    m = InfluenceDiagramModel(id)
    m = bind_kernel(m, [x => ks[x] for x in chance_names(id)])
    return bind_utility(m, [u => us[u] for u in utility_names(id)])
end

function oracle(c::OpenInfluenceDiagram, ks, us, σ)
    return expected_utility(oracle_model(apex(c), ks, us), σ)
end

# The axes of the information set and the action of decision `d` of `id`.
info_axes(id, d) = FiniteAxis[axis(id, v) for v in decision_information(id, d)]
action_axis(id, d) = axis(id, decision_variable(id, d))

# A deterministic strategy of `id` with every action drawn at random.
function random_strategy(rng::AbstractRNG, id)
    ps = Dict{Symbol,AbstractPolicy}()
    for d in parts(id, :Decision)
        ia, a = info_axes(id, d), action_axis(id, d)
        table = [rand(rng, a.labels) for _ in CartesianIndices(Tuple(length.(ia)))]
        ps[decision_name(id, d)] = DeterministicPolicy(decision_name(id, d), ia, a, table)
    end
    return Strategy(ps)
end

# The policies of `σ` for the decisions of `o`.
function restrict(σ::Strategy, o::OpenInfluenceDiagram)
    return Strategy(Dict{Symbol,AbstractPolicy}(d => σ[d] for d in decision_names(apex(o))))
end

# Up to `n` strategies of `id`: all of them when there are few, else a seeded sample.
function some_strategies(rng, id; n=12)
    n_deterministic_strategies(id) <= n && return collect(all_deterministic_strategies(id))
    return [random_strategy(rng, id) for _ in 1:n]
end

# A closed composite agrees with the oracle: `(1, EU)`.
function closed_ok(r::RewardKernel, eu)
    return size(kernel(r).table) == () && kernel(r).table[] ≈ 1 && reward(r)[] ≈ eu
end

function random_reward_kernel(rng, X, Y)
    K = random_kernel(rng, X, Y)
    return RewardKernel(K, randn(rng, size(K.table)))
end

# Random small influence diagrams
#################################

# A random diagram in a fixed variable order: `nchance` chance variables and `ndec`
# decisions, each reading at most two earlier variables, and `nutil` utilities over one or
# two variables. Names start with `prefix`, so that two diagrams can sit side by side.
function random_spec(rng; prefix="", nchance=4, ndec=rand(rng, 1:2), nutil=2)
    kinds = vcat(:chance,
                 Random.shuffle(rng,
                                vcat(fill(:chance, nchance - 1),
                                     fill(:decision, ndec))))
    vars = NamedTuple[]
    nc = nd = 0
    for (i, k) in enumerate(kinds)
        name = k === :chance ? Symbol(prefix, "X", nc += 1) : Symbol(prefix, "D", nd += 1)
        labels = k === :chance ? [:s1, :s2, :s3][1:rand(rng, 2:3)] : [:a1, :a2]
        earlier = Symbol[v.name for v in vars]
        reads = isempty(earlier) ? Symbol[] :
                Random.shuffle(rng, earlier)[1:rand(rng, 0:min(2, length(earlier)))]
        push!(vars, (name=name, labels=labels, kind=k, reads=reads))
    end
    names = Symbol[v.name for v in vars]
    utils = [(name=Symbol(prefix, "U", j),
              scope=Random.shuffle(rng, names)[1:rand(rng, 1:2)]) for j in 1:nutil]
    axes = Dict(v.name => FiniteAxis(v.name, v.labels) for v in vars)
    space_of(xs) = FiniteSpace(FiniteAxis[axes[x] for x in xs])
    ks = Dict{Symbol,FiniteKernel}()
    for v in vars
        v.kind === :chance || continue
        ks[v.name] = random_kernel(rng, space_of(v.reads), space_of([v.name]))
    end
    us = Dict{Symbol,AbstractUtility}()
    for u in utils
        sc = space_of(u.scope)
        us[u.name] = TabularUtility(factors(sc), 10 .* randn(rng, size(sc)))
    end
    observed = Set{Symbol}(r for v in vars if v.kind === :decision for r in v.reads)
    for v in vars
        rand(rng) < 0.3 && push!(observed, v.name)
    end
    return (vars=vars, utils=utils, kernels=ks, utilities=us, observed=observed)
end

# The pieces of `spec` cut before each position in `cuts`: piece `j` owns the variables of
# its segment and the utilities whose last scope variable is there, imports the earlier
# variables it or a later piece reads, and exports the variables a later piece reads.
function random_pieces(spec, cuts)
    vars = spec.vars
    n = length(vars)
    bounds = vcat(1, cuts, n + 1)
    seg = zeros(Int, n)
    for j in 1:(length(bounds) - 1), i in bounds[j]:(bounds[j + 1] - 1)
        seg[i] = j
    end
    at = Dict(v.name => i for (i, v) in enumerate(vars))
    useg(u) = maximum(seg[at[x]] for x in u.scope)
    function reads(j)
        return union(Symbol[r for (i, v) in enumerate(vars) if seg[i] == j for r in v.reads],
                     Symbol[x for u in spec.utils if useg(u) == j for x in u.scope])
    end
    nseg = length(bounds) - 1
    # The interface after segment j: variables of segments 1..j read by a later segment.
    function iface(j)
        return j == 0 || j == nseg ? Symbol[] :
               sort!(collect(Symbol,
                             filter(x -> seg[at[x]] <= j,
                                    union((reads(k) for k in (j + 1):nseg)...)));
                     by=x -> at[x])
    end
    pieces = OpenInfluenceDiagram[]
    for j in 1:nseg
        ins, outs = iface(j - 1), iface(j)
        own = Symbol[v.name for (i, v) in enumerate(vars) if seg[i] == j]
        names = sort!(union(ins, own); by=x -> at[x])
        vs = [vars[at[x]] for x in names]
        id = influence_diagram((v.name => v.labels for v in vs)...;
                               mechanisms=Pair{Symbol,Any}[v.name => Tuple(v.reads)
                                                           for v in vs
                                                           if v.kind === :chance &&
                                                              v.name in own],
                               decisions=Pair{Symbol,Any}[v.name => Tuple(v.reads)
                                                          for v in vs
                                                          if v.kind === :decision &&
                                                             v.name in own],
                               utilities=Pair{Symbol,Any}[u.name => Tuple(u.scope)
                                                          for u in spec.utils
                                                          if useg(u) == j],
                               closed=false)
        obs = Symbol[x for x in union(ins, outs) if x in spec.observed]
        push!(pieces, Open(id; inputs=ins, outputs=outs, observed=obs))
    end
    return pieces
end

@testset "Semantics" begin
    @testset "reward kernels: construction and accessors" begin
        X = FiniteSpace(:X, [:a, :b])
        Y = FiniteSpace(:Y, [:u, :v, :w])
        rng = Xoshiro(1)
        K = random_kernel(rng, X, Y)
        r = RewardKernel(K)
        @test kernel(r) === K && reward(r) == zeros(3, 2)
        @test dom(r) == X && codom(r) == Y
        W = randn(rng, 3, 2)
        s = RewardKernel(K, W)
        @test reward(s) == W && reward_matrix(s) == W
        @test s == RewardKernel(K, copy(W)) && hash(s) == hash(RewardKernel(K, copy(W)))
        @test s ≈ RewardKernel(K, W .+ 1e-12) && !(s ≈ r)
        @test sprint(show, s) == "RewardKernel([:X] → [:Y])"
        @test_throws ArgumentError RewardKernel(K, zeros(2, 3))
        @test_throws ArgumentError RewardKernel(K, fill(NaN, 3, 2))
        Z = tensor_space(X, X)
        @test size(reward_matrix(RewardKernel(random_kernel(rng, Z, Y)))) == (3, 4)
        @test_throws SpaceMismatchError compose(s, s)
        # Two closed reward kernels side by side: the probabilities multiply and the
        # rewards add.
        one_ = state(FiniteSpace(), [1.0])
        t = otimes(RewardKernel(one_, fill(2.0)), RewardKernel(one_, fill(3.0)))
        @test kernel(t).table[] == 1 && reward(t)[] == 5
    end

    @testset "reward kernels: the category laws" begin
        rng = Xoshiro(2)
        X = FiniteSpace(:X, [:a, :b])
        Y = FiniteSpace(:Y, [:u, :v, :w])
        Z = FiniteSpace(:Z, [:p, :q])
        V = FiniteSpace(:V, [:m, :n])
        I = FiniteSpace()
        f, g, h = random_reward_kernel(rng, X, Y), random_reward_kernel(rng, Y, Z),
                  random_reward_kernel(rng, Z, V)
        k = random_reward_kernel(rng, V, X)
        # Identities and associativity.
        @test compose(identity_reward_kernel(X), f) ≈ f
        @test compose(f, identity_reward_kernel(Y)) ≈ f
        @test compose(compose(f, g), h) ≈ compose(f, compose(g, h)) ≈ compose(f, g, h)
        @test f ⋅ g ≈ compose(f, g)
        # The monoidal unit and associativity of the tensor.
        idI = identity_reward_kernel(I)
        @test otimes(idI, f) ≈ f && otimes(f, idI) ≈ f
        @test otimes(otimes(f, g), h) ≈ otimes(f, otimes(g, h)) ≈ otimes(f, g, h)
        @test f ⊗ g ≈ otimes(f, g)
        @test otimes(identity_reward_kernel(X), identity_reward_kernel(Y)) ≈
              identity_reward_kernel(tensor_space(X, Y))
        # The interchange law.
        @test compose(otimes(f, h), otimes(g, k)) ≈ otimes(compose(f, g), compose(h, k))
        # Symmetry: involutive and natural.
        @test compose(swap_reward_kernel(X, Y), swap_reward_kernel(Y, X)) ≈
              identity_reward_kernel(tensor_space(X, Y))
        @test compose(otimes(f, h), swap_reward_kernel(Y, V)) ≈
              compose(swap_reward_kernel(X, Z), otimes(h, f))
        # Copy and discard form a commutative comonoid.
        cp, dc = copy_reward_kernel(X), discard_reward_kernel(X)
        idX = identity_reward_kernel(X)
        @test compose(cp, otimes(idX, dc)) ≈ idX && compose(cp, otimes(dc, idX)) ≈ idX
        @test compose(cp, swap_reward_kernel(X, X)) ≈ cp
        @test compose(cp, otimes(cp, idX)) ≈ compose(cp, otimes(idX, cp))
        @test reward(cp) == zeros(size(kernel(cp).table)) && iszero(reward(dc))
        # Lifting with zero reward is a monoidal functor from kernels.
        a, b = random_kernel(rng, X, Y), random_kernel(rng, Y, Z)
        @test compose(RewardKernel(a), RewardKernel(b)) ≈ RewardKernel(compose_kernel(a, b))
        @test otimes(RewardKernel(a), RewardKernel(b)) ≈ RewardKernel(tensor_kernel(a, b))
        # Discard is not natural: discarding the output keeps the expected reward earned
        # on the way, so `f ; discard` is discard only when that reward is zero.
        fd = compose(f, discard_reward_kernel(Y))
        @test kernel(fd) ≈ discard_kernel(X)
        @test vec(reward(fd)) ≈ vec(sum(reward_matrix(f); dims=1))
        @test !(fd ≈ discard_reward_kernel(X))
        @test compose(RewardKernel(kernel(f)), discard_reward_kernel(Y)) ≈
              discard_reward_kernel(X)
    end

    @testset "merge_strategies" begin
        σ = Strategy(:A => ConstantPolicy(:x))
        τ = Strategy(:B => ConstantPolicy(:y), :C => ConstantPolicy(:z))
        @test merge_strategies(σ, τ) ==
              Strategy(:A => ConstantPolicy(:x), :B => ConstantPolicy(:y),
                       :C => ConstantPolicy(:z))
        @test merge_strategies() == Strategy() && merge_strategies(σ) == σ
        e = try
            merge_strategies(σ, τ, σ)
        catch err
            err
        end
        @test e == DuplicatePolicyError(:A)
        @test occursin(":A", sprint(showerror, e))
        @test_throws DuplicatePolicyError merge_strategies(σ, σ)
    end

    m = umbrella_model()
    ks, us = kernels_by_name(m), bound_utilities(m)
    A, B = umbrella_chance(), umbrella_decision()

    @testset "interpret: layout and conventions" begin
        σ = Strategy(:Umbrella => deterministic_policy(m, :Umbrella,
                                                       [:leave, :leave, :take]))
        rA = interpret(A, ks, us, Strategy())
        rB = interpret(B, ks, us, σ)
        # A diagram without decisions or utilities has zero reward and the kernel that
        # `CategoricalBayesianNetworks` gives the same open network: the same axes, in
        # interface order, and the same enumeration of joint states.
        @test reward(rA) == zeros(size(kernel(rA).table))
        @test kernel(rA) ≈ interpret(OpenBayesNet(A), ks)
        @test axis_names(codom(rA)) == [:Weather, :Forecast]
        @test axis_names(dom(rB)) == [:Weather, :Forecast] && isempty(codom(rB))
        # The decision reads the observed input directly: on every joint input state the
        # reward is the utility of the weather and of the action the policy picks for the
        # forecast, with the joint states in `joint_states` order.
        for (j, (w, f)) in enumerate(joint_states(dom(rB)))
            @test reward_matrix(rB)[1, j] == utility_value(us[:U], w, σ[:Umbrella](f))
        end
        @test kernel(rB) ≈ discard_kernel(dom(rB))
        # The model form reads `kernels(m)` and `bound_utilities(m)` through references.
        whole = Open(syntax(m))
        @test closed_ok(interpret(whole, m, σ), expected_utility(m, σ))
        @test interpret(whole, m, σ) ≈
              interpret(whole, kernels(m), Dict(NamedRef("U") => us[:U]), σ)
        @test interpret(whole, set_policy(m, :Umbrella, σ[:Umbrella])) ≈
              interpret(whole, m, σ)
    end

    @testset "interpret: argument errors" begin
        σ = Strategy(:Umbrella => ConstantPolicy(:take))
        @test_throws IncompleteStrategyError interpret(B, ks, us, Strategy())
        stoch = StochasticPolicy(:Umbrella,
                                 random_kernel(Xoshiro(3), FiniteSpace(axis(apex(B), 2)),
                                               FiniteSpace(axis(apex(B), 3))))
        @test_throws ArgumentError interpret(B, ks, us, Strategy(:Umbrella => stoch))
        wrong = DeterministicPolicy(:Umbrella, FiniteAxis[axis(apex(B), 1)],
                                    axis(apex(B), 3), [:take, :leave])
        @test_throws PolicySignatureError interpret(B, ks, us,
                                                    Strategy(:Umbrella => wrong))
        @test_throws PolicySignatureError interpret(B, ks, us,
                                                    Strategy(:Umbrella => ConstantPolicy(:nope)))
        @test_throws MissingUtilityError interpret(B, ks, Dict{Symbol,AbstractUtility}(), σ)
        @test_throws MissingKernelError interpret(A, Dict{Symbol,FiniteKernel}(), us,
                                                  Strategy())
        @test_throws ModelTooLargeError interpret(B, ks, us, σ; max_states=2)
        whole = Open(syntax(m))
        @test_throws ArgumentError interpret(whole, observe(m, :Forecast => :rainy), σ)
        # Policies for decisions that are not in the apex are ignored, as `instantiate`
        # ignores them.
        @test interpret(A, ks, us, σ) ≈ interpret(A, ks, us, Strategy())
    end

    @testset "functoriality on the umbrella split, every strategy" begin
        rA = interpret(A, ks, us, Strategy())
        C = compose(A, B)
        G = glue(A, B; along=[:Weather => :Weather, :Forecast => :Forecast])
        uwd = @relation () begin
            chance(weather, forecast)
            decide(weather, forecast)
        end
        O = oapply(uwd, [A, B])
        σs = all_deterministic_strategies(apex(B))
        @test length(σs) == 8
        for σ in σs
            rB = interpret(B, ks, us, σ)
            rC = interpret(C, ks, us, merge_strategies(Strategy(), σ))
            @test rC ≈ compose(rA, rB)
            @test closed_ok(rC, oracle(C, ks, us, σ))
            @test reward(rC)[] ≈ expected_utility(m, σ)
            @test interpret(G, ks, us, σ) ≈ rC
            @test interpret(O, ks, us, σ) ≈ rC
        end
        # The best of them is the forecast's value, 77 (`umbrella_model`).
        @test maximum(reward(interpret(C, ks, us, σ))[] for σ in σs) ≈ 77
    end

    @testset "identities, associativity, tensor, copy and discard on diagrams" begin
        σ = Strategy(:Umbrella => deterministic_policy(m, :Umbrella, [:leave, :take, :take]))
        rA, rB = interpret(A, ks, us, Strategy()), interpret(B, ks, us, σ)
        # Identities.
        X = codom(A)
        @test interpret(id(X), ks, us, Strategy()) ≈ identity_reward_kernel(codom(rA))
        @test interpret(compose(A, id(X)), ks, us, Strategy()) ≈ rA
        @test interpret(compose(id(dom(B)), B), ks, us, σ) ≈ rB
        unit = interpret(id(munit(OpenInfluenceDiagramOb)), ks, us, Strategy())
        @test closed_ok(unit, 0.0)
        # A three-piece split: the weather, the forecast (passing the weather through)
        # and the decision; both bracketings of the composite and the composite of the
        # interpretations agree.
        W = Open(influence_diagram(:Weather => [:sunny, :rainy];
                                   mechanisms=[:Weather => ()], closed=false);
                 outputs=[:Weather])
        F = Open(influence_diagram(:Weather => [:sunny, :rainy],
                                   :Forecast => [:sunny, :cloudy, :rainy];
                                   mechanisms=[:Forecast => :Weather], closed=false);
                 inputs=[:Weather], outputs=[:Weather, :Forecast], observed=[:Forecast])
        rW, rF = interpret(W, ks, us, Strategy()), interpret(F, ks, us, Strategy())
        left = interpret(compose(compose(W, F), B), ks, us, σ)
        right = interpret(compose(W, compose(F, B)), ks, us, σ)
        @test left ≈ right ≈ compose(rW, rF, rB) ≈ compose(rW, compose(rF, rB))
        @test interpret(compose(F, B), ks, us, σ) ≈ compose(rF, rB)
        @test closed_ok(left, expected_utility(m, σ))
        # Tensor, and the interchange law through the syntax: two copies side by side
        # share their kernels, utilities and the policy of their equally named decisions.
        @test interpret(otimes(A, B), ks, us, σ) ≈ otimes(rA, rB)
        AA, BB = otimes(A, A), otimes(B, B)
        @test interpret(BB, ks, us, σ) ≈ otimes(rB, rB)
        both = interpret(compose(AA, BB), ks, us, σ)
        @test both ≈ compose(otimes(rA, rA), otimes(rB, rB)) ≈
              otimes(compose(rA, rB), compose(rA, rB))
        @test closed_ok(both, 2 * expected_utility(m, σ))
        # A copied output is the output followed by copy.
        Acopy = Open(umbrella_chance_diagram(); outputs=[:Weather, :Forecast, :Forecast],
                     observed=[:Forecast])
        Fsp = FiniteSpace(axis(apex(A), 2))
        @test interpret(Acopy, ks, us, Strategy()) ≈
              compose(rA,
                      otimes(identity_reward_kernel(FiniteSpace(axis(apex(A), 1))),
                             copy_reward_kernel(Fsp)))
        # Dropping an output is discard, and the reward survives it.
        Bout = Open(umbrella_decision_diagram(); inputs=[:Weather, :Forecast],
                    outputs=[:Umbrella], observed=[:Forecast])
        rBout = interpret(Bout, ks, us, σ)
        @test compose(rBout, discard_reward_kernel(codom(rBout))) ≈ rB
        @test sum(reward(rBout)) ≈ sum(reward(rB))
    end

    @testset "the oil wildcatter split where the test result is observed" begin
        mo = two_stage_model()
        kso, uso = kernels_by_name(mo), bound_utilities(mo)
        P, Q = two_stage_test(), two_stage_drill()
        @test observed_outputs(P) == [:Test, :Result]
        C = compose(P, Q)
        G = glue(P, Q; along=[:Oil => :Oil, :Test => :Test, :Result => :Result])
        σs = all_deterministic_strategies(apex(C))
        @test length(σs) == 2 * 2^6
        best = -Inf
        for σ in σs
            σP, σQ = restrict(σ, P), restrict(σ, Q)
            @test merge_strategies(σP, σQ) == σ
            rC = interpret(C, kso, uso, σ)
            @test rC ≈ compose(interpret(P, kso, uso, σP), interpret(Q, kso, uso, σQ))
            @test closed_ok(rC, oracle(C, kso, uso, σ))
            @test reward(rC)[] ≈ expected_utility(mo, σ)
            @test interpret(G, kso, uso, σ) ≈ rC
            best = max(best, reward(rC)[])
        end
        @test best ≈ 21
    end

    @testset "the SPEC §46 grazing diagram at two boundaries" begin
        mg = reference_grazing_model()
        ksg, usg = kernels_by_name(mg), bound_utilities(mg)
        id = reference_grazing_diagram()
        d = decision_id(id, :GrazingManagement)
        rng = Xoshiro(46)
        σs = vcat([Strategy(:GrazingManagement => ConstantPolicy(a))
                   for a in action_axis(id, d).labels],
                  [random_strategy(rng, id) for _ in 1:4])
        M, H = grazing_management(), grazing_habitat()
        E, D = grazing_environment(), grazing_decision()
        CM, CE = compose(M, H), compose(E, D)
        uwd = @relation () begin
            management(soil, pressure, vegetation)
            habitat(soil, pressure, vegetation)
        end
        OM = oapply(uwd, [M, H])
        rE = interpret(E, ksg, usg, Strategy())
        rH = interpret(H, ksg, usg, Strategy())
        @test reward(rE) == zeros(size(kernel(rE).table))
        for σ in σs
            eu = expected_utility(mg, σ)
            # The decision upstream of the boundary, all hidden.
            rCM = interpret(CM, ksg, usg, σ)
            @test rCM ≈ compose(interpret(M, ksg, usg, σ), rH)
            @test closed_ok(rCM, oracle(CM, ksg, usg, σ)) && reward(rCM)[] ≈ eu
            @test interpret(OM, ksg, usg, σ) ≈ rCM
            # The decision downstream, reading the observed forecast and vegetation.
            rCE = interpret(CE, ksg, usg, σ)
            @test rCE ≈ compose(rE, interpret(D, ksg, usg, σ))
            @test closed_ok(rCE, oracle(CE, ksg, usg, σ)) && reward(rCE)[] ≈ eu
        end
    end

    @testset "random small diagrams" begin
        for seed in 1:8
            rng = Xoshiro(seed)
            spec = random_spec(rng)
            ks_, us_ = spec.kernels, spec.utilities
            n = length(spec.vars)
            k = rand(rng, 2:n)
            P, S = random_pieces(spec, [k])
            C = compose(P, S; no_forgetting=false)
            G = glue(P, S; along=[x => x for x in outputs(P)], no_forgetting=false)
            @test inputs(C) == outputs(C) == Symbol[]
            for σ in some_strategies(rng, apex(C))
                σP, σS = restrict(σ, P), restrict(σ, S)
                rC = interpret(C, ks_, us_, σ)
                @test rC ≈ compose(interpret(P, ks_, us_, σP), interpret(S, ks_, us_, σS))
                @test closed_ok(rC, oracle(C, ks_, us_, σ))
                @test interpret(G, ks_, us_, σ) ≈ rC
            end
            # Three pieces: associativity, and an open composite with inputs.
            k1 = rand(rng, 2:(n - 1))
            k2 = rand(rng, (k1 + 1):n)
            P3, M3, S3 = random_pieces(spec, [k1, k2])
            σ = random_strategy(rng, apex(C))
            r1, r2, r3 = (interpret(o, ks_, us_, restrict(σ, o)) for o in (P3, M3, S3))
            MS = compose(M3, S3; no_forgetting=false)
            @test interpret(MS, ks_, us_, restrict(σ, MS)) ≈ compose(r2, r3)
            left = interpret(compose(compose(P3, M3; no_forgetting=false), S3;
                                     no_forgetting=false), ks_, us_, σ)
            right = interpret(compose(P3, MS; no_forgetting=false), ks_, us_, σ)
            @test left ≈ right ≈ compose(r1, r2, r3)
            @test closed_ok(left, oracle(C, ks_, us_, σ))
        end
    end

    @testset "random small diagrams side by side: tensor and interchange" begin
        for seed in 11:16
            rng = Xoshiro(seed)
            a, b = random_spec(rng; prefix="a"), random_spec(rng; prefix="b")
            ks_ = merge(a.kernels, b.kernels)
            us_ = merge(a.utilities, b.utilities)
            Pa, Sa = random_pieces(a, [rand(rng, 2:length(a.vars))])
            Pb, Sb = random_pieces(b, [rand(rng, 2:length(b.vars))])
            Ca = compose(Pa, Sa; no_forgetting=false)
            Cb = compose(Pb, Sb; no_forgetting=false)
            σa, σb = random_strategy(rng, apex(Ca)), random_strategy(rng, apex(Cb))
            σ = merge_strategies(σa, σb)
            rPa, rSa = interpret(Pa, ks_, us_, σa), interpret(Sa, ks_, us_, σa)
            rPb, rSb = interpret(Pb, ks_, us_, σb), interpret(Sb, ks_, us_, σb)
            @test interpret(otimes(Pa, Pb), ks_, us_, σ) ≈ otimes(rPa, rPb)
            @test interpret(otimes(Sa, Sb), ks_, us_, σ) ≈ otimes(rSa, rSb)
            X = compose(otimes(Pa, Pb), otimes(Sa, Sb); no_forgetting=false)
            Y = otimes(Ca, Cb)
            rX = interpret(X, ks_, us_, σ)
            @test rX ≈ compose(otimes(rPa, rPb), otimes(rSa, rSb)) ≈
                  otimes(compose(rPa, rSa), compose(rPb, rSb))
            @test interpret(Y, ks_, us_, σ) ≈ rX
            @test closed_ok(rX, oracle(X, ks_, us_, σ))
            @test reward(rX)[] ≈ oracle(Ca, ks_, us_, σa) + oracle(Cb, ks_, us_, σb)
        end
    end
end
