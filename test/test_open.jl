using Catlab.CategoricalAlgebra: OpenACSetLeg

const CID = CategoricalInfluenceDiagrams

# The umbrella problem of `InfluenceDiagrams.umbrella_diagram` split at the boundary
# {Weather, Forecast}: a chance component that exports the weather (hidden) and the forecast
# (observed), and a decision component that imports both.
function umbrella_chance_diagram()
    return influence_diagram(:Weather => [:sunny, :rainy],
                             :Forecast => [:sunny, :cloudy, :rainy];
                             mechanisms=[:Weather => (), :Forecast => :Weather],
                             closed=false)
end

function umbrella_decision_diagram()
    return influence_diagram(:Weather => [:sunny, :rainy],
                             :Forecast => [:sunny, :cloudy, :rainy],
                             :Umbrella => [:take, :leave];
                             decisions=[:Umbrella => :Forecast],
                             utilities=[:U => (:Weather, :Umbrella)], closed=false)
end

function umbrella_chance(; observed=[:Forecast])
    return Open(umbrella_chance_diagram(); outputs=[:Weather, :Forecast], observed=observed)
end

function umbrella_decision(; observed=[:Forecast], validate=true)
    return Open(umbrella_decision_diagram(); inputs=[:Weather, :Forecast],
                observed=observed, validate=validate)
end

@testset "Open influence diagrams" begin
    A = umbrella_chance()
    B = umbrella_decision()

    @testset "construction and accessors" begin
        @test A isa OpenInfluenceDiagram
        @test structured_cospan(B) isa InfluenceDiagramCospan
        @test inputs(A) == Symbol[]
        @test outputs(A) == [:Weather, :Forecast]
        @test inputs(B) == [:Weather, :Forecast]
        @test outputs(B) == Symbol[]
        @test apex(B) == umbrella_decision_diagram()
        @test input_space(B) isa VariableSpace
        @test states(input_space(B), :Forecast) == [:sunny, :cloudy, :rainy]
        @test input_variables(B) == [variable_id(apex(B), :Weather),
                                     variable_id(apex(B), :Forecast)]
        @test output_variables(A) == [1, 2]
        @test feet(B) == [input_space(B), output_space(B)]
        @test length(legs(B)) == 2
        @test left_leg(B) === legs(B)[1]
        @test right_leg(B) === legs(B)[2]
        @test input_observability(B) == [:hidden, :observed]
        @test output_observability(A) == [:hidden, :observed]
        @test observed_inputs(B) == [:Forecast]
        @test observed_outputs(A) == [:Forecast]
        @test observed_outputs(B) == Symbol[]
        @test dom(B) isa OpenInfluenceDiagramOb
        @test dom(B).space == input_space(B)
        @test observability(dom(B)) == [:hidden, :observed]
        @test codom(A) == OpenInfluenceDiagramOb(output_space(A), [:hidden, :observed])
        @test interface_matches(codom(A), dom(B))
        @test !interface_matches(codom(umbrella_chance(; observed=Symbol[])), dom(B))
        @test validate(B) === nothing
        @test isvalid(B) && isempty(validation_errors(B))
        @test Open(umbrella_decision_diagram(), [:Weather, :Forecast], Symbol[];
                   observed=[:Forecast]) == B
        @test hash(umbrella_decision()) == hash(B)
        @test hash(dom(umbrella_decision())) == hash(dom(B))
        @test occursin("[:Weather, :Forecast!] -> Symbol[]", sprint(show, B))
        @test_throws UnknownVariableError Open(umbrella_decision_diagram(); inputs=[:Nope])
    end

    @testset "observability defaults to hidden" begin
        o = Open(umbrella_chance_diagram(); outputs=[:Weather, :Forecast])
        @test output_observability(o) == [:hidden, :hidden]
        # A name observed on both feet of a pass-through is observed on each.
        id = influence_diagram(:X => [:a, :b]; closed=false)
        p = Open(id; inputs=[:X], outputs=[:X, :X], observed=[:X])
        @test input_observability(p) == [:observed]
        @test output_observability(p) == [:observed, :observed]
    end

    @testset "invalid observability is an ArgumentError" begin
        @test_throws ArgumentError Open(umbrella_chance_diagram(); outputs=[:Weather],
                                        observed=[:Forecast])
        c = structured_cospan(A)
        @test_throws ArgumentError OpenInfluenceDiagram(c, Symbol[], [:hidden])
        @test_throws ArgumentError OpenInfluenceDiagram(c, Symbol[], [:hidden, :maybe])
        @test_throws ArgumentError OpenInfluenceDiagramOb(VariableSpace(), [:hidden])
        @test OpenInfluenceDiagram(c, Symbol[], [:observed, :hidden]) isa
              OpenInfluenceDiagram
    end

    @testset "monoidal structure" begin
        u = munit(OpenInfluenceDiagramOb)
        @test nparts(u.space, :Variable) == 0 && isempty(observability(u))
        X = dom(B)
        @test otimes(u, X) == X
        @test otimes(X, u) == X
        XX = X ⊗ X
        @test variable_names(XX.space) == [:Weather, :Forecast, :Weather, :Forecast]
        @test observability(XX) == [:hidden, :observed, :hidden, :observed]
        i = id(X)
        @test i isa OpenInfluenceDiagram && isvalid(i)
        @test dom(i) == X && codom(i) == X
        @test nparts(apex(i), :Mechanism) == nparts(apex(i), :Decision) == 0
    end

    @testset "rule 1: at most one generator per variable" begin
        id = umbrella_decision_diagram()
        add_mechanism!(id, :Umbrella; inputs=[:Forecast], name=:UmbrellaChance)
        o = Open(id; inputs=[:Weather, :Forecast], observed=[:Forecast], validate=false)
        e = first(validation_errors(o))
        @test e isa DecisionUniquenessError && e.variable == :Umbrella &&
              e.reason == :has_mechanism
        @test_throws DecisionUniquenessError validate(o)
        @test_throws DecisionUniquenessError Open(id; inputs=[:Weather, :Forecast],
                                                  observed=[:Forecast])
        two = umbrella_chance_diagram()
        add_mechanism!(two, :Forecast; name=:SecondForecast)
        @test_throws DuplicateGeneratorError Open(two; outputs=[:Forecast])
    end

    @testset "rule 2: an input has no generator" begin
        e = try
            Open(umbrella_chance_diagram(); inputs=[:Forecast])
        catch err
            err
        end
        @test e == DiagramInterfaceError(2, :Forecast, :Forecast_mechanism, :mechanism)
        @test occursin(":Forecast", sprint(showerror, e))
        id = umbrella_decision_diagram()
        o = Open(id; inputs=[:Weather, :Forecast, :Umbrella], observed=[:Forecast],
                 validate=false)
        @test validation_errors(o) ==
              [DiagramInterfaceError(2, :Umbrella, :Umbrella, :decision)]
        @test occursin("decision :Umbrella", sprint(showerror, first(validation_errors(o))))
        # The open-network conditions still hold: an injective input leg, and every variable
        # without a generator an input.
        o = Open(id; inputs=[:Weather, :Forecast, :Forecast], validate=false)
        @test any(e -> e isa InterfaceError && e.rule == 2, validation_errors(o))
        o = Open(id; inputs=[:Forecast], observed=[:Forecast], validate=false)
        @test validation_errors(o) == [InterfaceError(3, [:Weather], [1])]
    end

    @testset "rule 3: a decision reads only internal or observed inputs" begin
        e = try
            umbrella_decision(; observed=Symbol[])
        catch err
            err
        end
        @test e == DiagramInterfaceError(3, :Forecast, :Umbrella, :hidden_input)
        msg = sprint(showerror, e)
        @test occursin(":Umbrella", msg) && occursin(":Forecast", msg)
        # Reading an internal variable needs no flag: the same decision with the forecast
        # generated inside the component.
        whole = Open(umbrella_diagram())
        @test isvalid(whole)
        # A hidden input that no decision reads is fine (the weather).
        @test isvalid(umbrella_decision(; observed=[:Forecast]))
    end

    @testset "rule 4: a utility may read any apex variable" begin
        # `U` reads the hidden input `Weather`.
        @test :Weather in utility_scope_names(apex(B), :U)
        @test isvalid(B)
        id = umbrella_decision_diagram()
        # A utility input whose variable is not in the apex (left unset, so 0).
        add_part!(id, :UtilityInput; utility_node=1, utility_position=3)
        o = Open(id; inputs=[:Weather, :Forecast], observed=[:Forecast], validate=false)
        @test only(validation_errors(o)) isa DanglingReferenceError
        @test_throws DanglingReferenceError validate(o)
    end

    @testset "rule 5: the causal-plus-information graph is acyclic" begin
        id = influence_diagram(:X => [:a, :b], :D => [:yes, :no], :Y => [:c, :d];
                               mechanisms=[:Y => :D], decisions=[:D => :Y], closed=false)
        o = Open(id; inputs=[:X], validate=false)
        e = first(validation_errors(o))
        @test e isa InvalidInformationSetError && e.decision == :D && e.variable == :Y &&
              e.reason == :downstream
        cyc = influence_diagram(:X => [:a, :b], :Y => [:c, :d];
                                mechanisms=[:X => :Y, :Y => :X], closed=false)
        @test_throws CyclicBayesNetError Open(cyc; outputs=[:X])
    end

    @testset "legs must be natural" begin
        id = umbrella_decision_diagram()
        foot = VariableSpace()
        add_variable!(foot, :Weather; states=[:rainy, :sunny])
        bad = OpenInfluenceDiagram(InfluenceDiagramCospan(id,
                                                          OpenACSetLeg(foot; Variable=[1],
                                                                       State=[1, 2]),
                                                          CID._leg(id, Int[])),
                                   [:hidden], Symbol[])
        @test any(e -> e isa InterfaceError && e.rule == 5, validation_errors(bad))
    end

    @testset "embedding of open Bayesian networks" begin
        bn = bayesnet(:Climate => [:dry, :wet], :Irrigation => [:none, :high],
                      :SoilMoisture => [:low, :medium, :high];
                      mechanisms=[:SoilMoisture => (:Climate, :Irrigation)], closed=false)
        o = Open(bn; inputs=[:Climate, :Irrigation], outputs=[:SoilMoisture])
        e = OpenInfluenceDiagram(o)
        @test e isa OpenInfluenceDiagram && isvalid(e)
        @test inputs(e) == inputs(o) && outputs(e) == outputs(o)
        @test input_observability(e) == [:hidden, :hidden]
        @test output_observability(e) == [:hidden]
        @test input_space(e) == input_space(o) && output_space(e) == output_space(o)
        @test input_variables(e) == input_variables(o)
        @test BayesNet(apex(e)) == apex(o)
        @test nparts(apex(e), :Decision) == nparts(apex(e), :Utility) == 0
        back = OpenBayesNet(e)
        @test back == o
        @test OpenInfluenceDiagram(back) == e
        # A diagram with decisions or utilities is not a network.
        @test_throws ArgumentError OpenBayesNet(B)
        # Copied outputs survive the round trip.
        c = Open(bn; inputs=[:Climate, :Irrigation],
                 outputs=[:SoilMoisture, :SoilMoisture])
        @test OpenBayesNet(OpenInfluenceDiagram(c)) == c
        # The embedding composes as the network does.
        A = Open(bayesnet(:Climate => [:dry, :wet], :Irrigation => [:none, :high];
                          mechanisms=[:Climate => (), :Irrigation => ()]);
                 outputs=[:Climate, :Irrigation])
        C = compose(OpenInfluenceDiagram(A), e)
        @test is_isomorphic(apex(OpenBayesNet(C)), apex(compose(A, o)))
        @test outputs(C) == outputs(compose(A, o))
    end
end
