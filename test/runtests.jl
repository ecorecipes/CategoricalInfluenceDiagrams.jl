using Test
using CategoricalInfluenceDiagrams
using BayesianNetworks: BayesianNetworks, VariableSpace
using CategoricalBayesianNetworks: CategoricalBayesianNetworks
using InfluenceDiagrams: InfluenceDiagrams
using BayesianNetworkInference: BayesianNetworkInference
using ACSets: attrs, acset_schema

@testset "CategoricalInfluenceDiagrams" begin
    include("test_open.jl")
    include("test_composition.jl")
    include("test_semantics.jl")
    include("test_optimization.jl")
    include("test_games.jl")
    include("test_evidence.jl")
    include("test_behaviour.jl")
    include("test_shared.jl")
    include("test_certificates.jl")
    include("test_errors.jl")
    include("test_docstrings.jl")
end
