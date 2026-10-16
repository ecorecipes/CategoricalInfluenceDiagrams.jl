# The SPEC section 46 grazing diagram (`InfluenceDiagrams.reference_grazing_diagram`) split
# at two boundaries. In the first the management component holds the decision and exports
# the state the habitat component needs, all hidden. In the second the decision sits
# downstream and reads the forecast and the current vegetation through observed inputs.
const GRAZING_STATES = (:Climate => [:dry, :normal, :wet],
                        :ClimateForecast => [:dry, :normal, :wet],
                        :SoilMoisture => [:low, :medium, :high],
                        :CurrentVegetation => [:sparse, :moderate, :dense],
                        :GrazingManagement => [:exclude, :reduce, :maintain],
                        :GrazingPressure => [:low, :high],
                        :Vegetation => [:sparse, :moderate, :dense],
                        :HabitatQuality => [:poor, :good],
                        :Occupancy => [:absent, :present],
                        :Biodiversity => [:low, :high])

grazing_states(names...) = [n => Dict(GRAZING_STATES)[n] for n in names]

function grazing_management()
    id = influence_diagram(grazing_states(:Climate, :ClimateForecast, :SoilMoisture,
                                          :CurrentVegetation, :GrazingManagement,
                                          :GrazingPressure)...;
                           mechanisms=[:Climate => (), :ClimateForecast => :Climate,
                                       :SoilMoisture => :Climate, :CurrentVegetation => (),
                                       :GrazingPressure => :GrazingManagement],
                           decisions=[:GrazingManagement => (:ClimateForecast,
                                                             :CurrentVegetation)],
                           utilities=[:ManagementCost => :GrazingManagement], closed=false)
    return Open(id; outputs=[:SoilMoisture, :GrazingPressure, :CurrentVegetation])
end

function grazing_habitat()
    id = influence_diagram(grazing_states(:SoilMoisture, :GrazingPressure,
                                          :CurrentVegetation, :Vegetation, :HabitatQuality,
                                          :Occupancy, :Biodiversity)...;
                           mechanisms=[:Vegetation => (:SoilMoisture, :GrazingPressure,
                                                       :CurrentVegetation),
                                       :HabitatQuality => :Vegetation,
                                       :Occupancy => :HabitatQuality,
                                       :Biodiversity => :Occupancy],
                           utilities=[:ConservationBenefit => :Biodiversity], closed=false)
    return Open(id; inputs=[:SoilMoisture, :GrazingPressure, :CurrentVegetation])
end

function grazing_environment(; observed=[:ClimateForecast, :CurrentVegetation])
    id = influence_diagram(grazing_states(:Climate, :ClimateForecast, :SoilMoisture,
                                          :CurrentVegetation)...;
                           mechanisms=[:Climate => (), :ClimateForecast => :Climate,
                                       :SoilMoisture => :Climate, :CurrentVegetation => ()],
                           closed=false)
    return Open(id; outputs=[:ClimateForecast, :SoilMoisture, :CurrentVegetation],
                observed=observed)
end

function grazing_decision(; observed=[:ClimateForecast, :CurrentVegetation])
    id = influence_diagram(grazing_states(:ClimateForecast, :SoilMoisture,
                                          :CurrentVegetation, :GrazingManagement,
                                          :GrazingPressure, :Vegetation, :HabitatQuality,
                                          :Occupancy, :Biodiversity)...;
                           mechanisms=[:GrazingPressure => :GrazingManagement,
                                       :Vegetation => (:SoilMoisture, :GrazingPressure,
                                                       :CurrentVegetation),
                                       :HabitatQuality => :Vegetation,
                                       :Occupancy => :HabitatQuality,
                                       :Biodiversity => :Occupancy],
                           decisions=[:GrazingManagement => (:ClimateForecast,
                                                             :CurrentVegetation)],
                           utilities=[:ConservationBenefit => :Biodiversity,
                                      :ManagementCost => :GrazingManagement],
                           closed=false)
    return Open(id; inputs=[:ClimateForecast, :SoilMoisture, :CurrentVegetation],
                observed=observed)
end

# `InfluenceDiagrams.two_stage_diagram` (test, then drill) split after the test: the first
# component holds the test decision and the test result; the second the drilling decision,
# which reads the test and its result through observed inputs.
function two_stage_test(; observed=[:Test, :Result])
    id = influence_diagram(:Oil => [:dry, :wet], :Test => [:test, :skip],
                           :Result => [:pos, :neg, :none];
                           mechanisms=[:Oil => (), :Result => (:Oil, :Test)],
                           decisions=[:Test => Symbol[]], utilities=[:TestCost => :Test],
                           closed=false)
    return Open(id; outputs=[:Oil, :Test, :Result], observed=observed)
end

function two_stage_drill(; information=(:Test, :Result), observed=[:Test, :Result])
    id = influence_diagram(:Oil => [:dry, :wet], :Test => [:test, :skip],
                           :Result => [:pos, :neg, :none], :Drill => [:drill, :dont];
                           decisions=[:Drill => information],
                           utilities=[:Payoff => (:Oil, :Drill)], closed=false)
    return Open(id; inputs=[:Oil, :Test, :Result], observed=observed)
end

@testset "Composition" begin
    A = umbrella_chance()
    B = umbrella_decision()

    @testset "compose: the umbrella split and composed back" begin
        C = compose(A, B)
        @test C isa OpenInfluenceDiagram && isvalid(C)
        @test inputs(C) == outputs(C) == Symbol[]
        @test is_isomorphic(apex(C), umbrella_diagram())
        @test A ⋅ B == C
        # The composite is an ordinary closed diagram: the existing solvers apply.
        @test isvalid(apex(C); closed=true)
        # The operands are left alone.
        @test A == umbrella_chance() && B == umbrella_decision()
    end

    @testset "compose: interface mismatches" begin
        e = try
            compose(umbrella_chance(; observed=Symbol[]), B)
        catch err
            err
        end
        @test e == ObservabilityMismatchError(:Forecast, 2, :hidden, :observed,
                                              "compose: outputs(A) vs inputs(B)")
        @test occursin(":Forecast", sprint(showerror, e))
        other = Open(umbrella_chance_diagram(); outputs=[:Forecast, :Weather])
        @test_throws InterfaceMismatchError compose(other, B)
        # Operands are validated first.
        @test_throws DiagramInterfaceError compose(A,
                                                   umbrella_decision(; observed=Symbol[],
                                                                     validate=false))
    end

    @testset "compose with an identity" begin
        I = id(codom(A))
        @test is_isomorphic(apex(compose(A, I)), apex(A))
        @test codom(compose(A, I)) == codom(A)
        @test is_isomorphic(apex(compose(id(dom(B)), B)), apex(B))
    end

    @testset "glue" begin
        G = glue(A, B; along=[:Weather => :Weather, :Forecast => :Forecast])
        @test isvalid(G) && is_isomorphic(apex(G), umbrella_diagram())
        # Gluing only the forecast leaves two variables named `Weather`, which the name-safe
        # `glue` refuses, as for open networks; with the decision component's weather renamed
        # it leaves one input and one output.
        @test_throws DuplicateNameError glue(A, B; along=[:Forecast => :Forecast])
        Bw = Open(rename_variable(umbrella_decision_diagram(), :Weather => :Season);
                  inputs=[:Season, :Forecast], observed=[:Forecast])
        H = glue(A, Bw; along=[:Forecast => :Forecast])
        @test isvalid(H)
        @test inputs(H) == [:Season] && input_observability(H) == [:hidden]
        @test outputs(H) == [:Weather] && output_observability(H) == [:hidden]
        e = try
            glue(umbrella_chance(; observed=Symbol[]), B;
                 along=[:Forecast => :Forecast])
        catch err
            err
        end
        @test e isa ObservabilityMismatchError && e.variable == :Forecast &&
              e.left == :hidden && e.right == :observed
        @test_throws InterfaceMismatchError glue(A, B; along=[:Nope => :Forecast])
        @test_throws InterfaceMismatchError glue(A, B; along=[:Weather => :Forecast])
        # A rename: the glued variable keeps its name in A.
        renamed = rename_variable(umbrella_decision_diagram(), :Forecast => :Signal)
        Br = Open(renamed; inputs=[:Weather, :Signal], observed=[:Signal])
        Gr = glue(A, Br; along=[:Weather => :Weather, :Forecast => :Signal])
        @test is_isomorphic(apex(Gr), umbrella_diagram())
        # The new name may not be taken in B: here the action is called `Forecast`.
        clash = rename_variable(renamed, :Umbrella => :Forecast)
        Bc = Open(clash; inputs=[:Weather, :Signal], observed=[:Signal])
        @test_throws NameClashError glue(A, Bc; along=[:Forecast => :Signal])
    end

    @testset "otimes" begin
        T = A ⊗ B
        @test T == otimes(A, B) && isvalid(T)
        @test inputs(T) == [:Weather, :Forecast]
        @test outputs(T) == [:Weather, :Forecast]
        @test input_observability(T) == [:hidden, :observed]
        @test output_observability(T) == [:hidden, :observed]
        @test dom(T) == dom(A) ⊗ dom(B) && codom(T) == codom(A) ⊗ codom(B)
        # Two decisions side by side owe each other nothing (rule 6 holds).
        BB = otimes(B, B)
        @test nparts(apex(BB), :Decision) == 2 && isvalid(BB)
    end

    @testset "oapply" begin
        uwd = @relation () begin
            chance(weather, forecast)
            decide(weather, forecast)
        end
        O = oapply(uwd, [A, B])
        @test isvalid(O) && is_isomorphic(apex(O), umbrella_diagram())
        @test oapply(uwd, Dict(:chance => A, :decide => B)) == O
        open_uwd = @relation (forecast,) begin
            chance(weather, forecast)
            decide(weather, forecast)
        end
        Of = oapply(open_uwd, [A, B])
        @test outputs(Of) == [:Forecast] && output_observability(Of) == [:observed]
        e = try
            oapply(uwd, [umbrella_chance(; observed=Symbol[]), B])
        catch err
            err
        end
        @test e isa ObservabilityMismatchError && e.variable == :Forecast
        @test_throws ArgumentError oapply(uwd, [A])
        @test_throws ArgumentError oapply(uwd, Dict(:chance => A))
        # A junction that receives two generated variables breaks rule 1.
        twice = @relation () begin
            chance(weather, forecast)
            again(weather, forecast)
        end
        @test_throws DuplicateGeneratorError oapply(twice, [A, A])
    end

    @testset "rule 5 across a boundary" begin
        # A decision that reads Z, and a mechanism Z <- D in another component: wired
        # together the information arc runs from the decision's own consequence.
        dec = Open(influence_diagram(:Z => [:a, :b], :D => [:yes, :no];
                                     decisions=[:D => :Z], closed=false);
                   inputs=[:Z], outputs=[:D], observed=[:Z])
        mech = Open(influence_diagram(:D => [:yes, :no], :Z => [:a, :b];
                                      mechanisms=[:Z => :D], closed=false);
                    inputs=[:D], outputs=[:Z], observed=[:Z])
        loop = @relation () begin
            decide(z, d)
            respond(d, z)
        end
        e = try
            oapply(loop, [dec, mech])
        catch err
            err
        end
        @test e isa InvalidInformationSetError && e.decision == :D &&
              e.reason == :downstream
        # A causal loop is a cycle of the network part.
        f = Open(influence_diagram(:X => [:a, :b], :Y => [:c, :d]; mechanisms=[:Y => :X],
                                   closed=false); inputs=[:X], outputs=[:Y])
        g = Open(influence_diagram(:Y => [:c, :d], :X => [:a, :b]; mechanisms=[:X => :Y],
                                   closed=false); inputs=[:Y], outputs=[:X])
        cyc = @relation () begin
            f(x, y)
            g(y, x)
        end
        @test_throws CyclicBayesNetError oapply(cyc, [f, g])
    end

    @testset "rule 6: composition preserves no-forgetting" begin
        P, Q = two_stage_test(), two_stage_drill()
        C = compose(P, Q)
        @test isvalid(C) && is_isomorphic(apex(C), two_stage_diagram())
        @test is_no_forgetting(apex(C))
        # The drilling decision forgets the test: both components have no-forgetting, but
        # the composite does not.
        forgetful = two_stage_drill(; information=(:Result,))
        e = try
            compose(P, forgetful)
        catch err
            err
        end
        @test e == NoForgettingError(:Drill, :Test, :Test)
        msg = sprint(showerror, e)
        @test occursin(":Drill", msg) && occursin(":Test -> :Drill", msg)
        @test_throws NoForgettingError glue(P, forgetful;
                                            along=[:Oil => :Oil, :Test => :Test,
                                                   :Result => :Result])
        wire = @relation () begin
            test(oil, t, result)
            drill(oil, t, result)
        end
        @test_throws NoForgettingError oapply(wire, [P, forgetful])
        # Opting out gives the limited-memory composite, which InfluenceDiagrams reports.
        L = compose(P, forgetful; no_forgetting=false)
        @test isvalid(L) && no_forgetting_arcs(apex(L)) == [:Drill => :Test]
        @test oapply(wire, [P, forgetful]; no_forgetting=false) isa OpenInfluenceDiagram
        # Hiding the test at the boundary takes the information away: the drilling
        # decision may no longer read it (rule 3), so the forgetting cannot be repaired
        # downstream.
        @test_throws DiagramInterfaceError two_stage_drill(; observed=[:Result])
        # A component that already forgets is not owed no-forgetting by the composite.
        lim = Open(syntax(without_information(two_stage_model(), :Drill, :Test)))
        @test !is_no_forgetting(apex(lim))
        @test isvalid(compose(lim, id(munit(OpenInfluenceDiagramOb))))
    end

    @testset "the grazing diagram split and composed back" begin
        M, H = grazing_management(), grazing_habitat()
        C = compose(M, H)
        @test isvalid(C) && is_isomorphic(apex(C), reference_grazing_diagram())
        E, D = grazing_environment(), grazing_decision()
        C2 = compose(E, D)
        @test isvalid(C2) && is_isomorphic(apex(C2), reference_grazing_diagram())
        @test is_isomorphic(apex(glue(E, D;
                                      along=[:ClimateForecast => :ClimateForecast,
                                             :SoilMoisture => :SoilMoisture,
                                             :CurrentVegetation => :CurrentVegetation])),
                            reference_grazing_diagram())
        # The decision may not read the current vegetation if the boundary hides it.
        e = try
            grazing_decision(; observed=[:ClimateForecast])
        catch err
            err
        end
        @test e == DiagramInterfaceError(3, :CurrentVegetation, :GrazingManagement,
                                         :hidden_input)
        # The same split wired by an undirected wiring diagram.
        uwd = @relation () begin
            management(soil, pressure, vegetation)
            habitat(soil, pressure, vegetation)
        end
        @test is_isomorphic(apex(oapply(uwd, [M, H])), reference_grazing_diagram())
    end

    @testset "unset references survive every composition" begin
        # `utility_ref` is a `Ref` attribute: an unset one is structurally valid, and
        # Catlab's colimits cannot read it, so they run with it held by a placeholder.
        refs(acs) = [subpart(acs, p, attr)
                     for (attr, ob, T) in attrs(acset_schema(acs)) if T === :Ref
                     for p in parts(acs, ob)]
        unset(acs) = count(isnothing, refs(acs))
        held(o) = any(r -> r isa CategoricalBayesianNetworks._UnsetRef, refs(apex(o)))
        id = umbrella_decision_diagram()
        u = add_part!(id, :Utility; utility_name=:Extra)
        add_part!(id, :UtilityInput; utility_node=u, utility_variable=1,
                  utility_position=1)
        @test subpart(id, u, :utility_ref) === nothing
        Bu = Open(id; inputs=[:Weather, :Forecast], observed=[:Forecast])
        before = deepcopy(Bu)
        @test isvalid(Bu)
        uwd = @relation () begin
            chance(weather, forecast)
            decide(weather, forecast)
        end
        for (C, n) in ((compose(A, Bu), 1),
                       (glue(A, Bu; along=[:Weather => :Weather, :Forecast => :Forecast]), 1),
                       (otimes(Bu, Bu), 2), (oapply(uwd, [A, Bu]), 1))
            @test isvalid(C) && unset(apex(C)) == n && !held(C)
        end
        @test Bu == before
    end
end
