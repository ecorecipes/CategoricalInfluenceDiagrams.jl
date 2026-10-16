# The exception hierarchy of ADR 0013 and ADR 0015. The types this package introduces live in
# its own module under an abstract type of its own, which subtypes BayesianNetworks'
# `BayesNetError`; every exception type of the two parent packages is re-exported as the
# same binding.
function exported_exception_names(M)
    return filter(names(M)) do n
        T = getglobal(M, n)
        return T isa Type && T <: Exception
    end
end

@testset "errors" begin
    CID = CategoricalInfluenceDiagrams
    @test OpenInfluenceDiagramError <: BayesNetError
    @test isabstracttype(OpenInfluenceDiagramError)
    for T in (ObservabilityMismatchError, DiagramInterfaceError, NoForgettingError,
              DuplicatePolicyError)
        @test T <: OpenInfluenceDiagramError
        @test T <: AnyBayesNetError
        @test parentmodule(T) === CID
    end
    exported = names(CID)
    for M in (CategoricalBayesianNetworks, InfluenceDiagrams)
        for n in exported_exception_names(M)
            @test n in exported
            @test getglobal(CID, n) === getglobal(M, n)
        end
    end
    # The frozen names keep their owners' bindings and print unqualified.
    for (n, M) in ((:ImpossibleEvidenceError, BayesianNetworks),
                   (:IrregularDiagramError, InfluenceDiagrams),
                   (:ScopeError, BayesianNetworkInference))
        T = getglobal(CID, n)
        @test parentmodule(T) === M
        @test string(T) == string(n)
    end
    # Every message names the variables involved.
    for (e, needles) in
        ((ObservabilityMismatchError(:Forecast, 2, :observed, :hidden, "compose"),
          (":Forecast", ":observed", ":hidden")),
         (DiagramInterfaceError(2, :X, :X_mechanism, :mechanism), (":X", ":X_mechanism")),
         (DiagramInterfaceError(2, :A, :D, :decision), (":A", "decision :D")),
         (DiagramInterfaceError(3, :W, :D, :hidden_input), (":W", "decision :D")),
         (NoForgettingError(:Drill, :Test, :Test), (":Drill", ":Test -> :Drill")),
         (DuplicatePolicyError(:Drill), (":Drill",)))
        msg = sprint(showerror, e)
        @test all(occursin(n, msg) for n in needles)
    end
    @test NoForgettingError(:A, :B, :C) == NoForgettingError(:A, :B, :C)
end
