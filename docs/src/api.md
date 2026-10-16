# API Reference

Every exported name of `CategoricalBayesianNetworks.jl` and `InfluenceDiagrams.jl` is
re-exported, among them the Catlab names those packages re-export (`apex`, `legs`, `feet`,
`dom`, `codom`, `compose`, `otimes`, `munit`, `id`, `oapply`, `@relation`) and every exception
type of the lower packages, as the same bindings. Those names are documented by their
packages. This page documents the names this package defines, and the methods it adds to
the re-exported functions: among them `compose`, `otimes`, `dom`, `codom`, `isapprox` and
`kernel` on a [`RewardKernel`](@ref), `interpret` on an open influence diagram, and
`optimize` on a closed composite.

```@autodocs
Modules = [CategoricalInfluenceDiagrams]
```
