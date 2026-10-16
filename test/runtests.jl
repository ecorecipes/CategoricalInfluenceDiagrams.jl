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
    include("test_errors.jl")
    include("test_docstrings.jl")
end
