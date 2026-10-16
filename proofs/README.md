# Open influence diagrams: Lean 4

The Lean project of `CategoricalInfluenceDiagrams.jl` (ADR 0018, decision 5). It requires
two existing proof projects by relative path:

- `CategoricalBayesianNetworks.jl/proofs`, the typed open-network syntax category and its
  FinStoch interpretation (ADR 0010, namespace `OpenNet`);
- `InfluenceDiagrams.jl/proofs`, the finite influence-diagram model with instantiation,
  expected utility and optimisation (namespace `InfluenceDiagramsProofs`).

Through them it also requires the `BayesianNetworks.jl` and `FiniteKernels.jl` proof
projects. Lean, Mathlib and mdgen are pinned to **4.30.0**, and the Lake manifest shares
`../../.lake-packages` with the rest of the workspace. Everything is in the namespace
`OpenInfluence`. The sealed bundle `docs/categorical-extensions-2026-09-12/influence/` is
a guide and is cited by claim id; it is not imported.

## Main results

Each sentence below is registered as an SA-Pass claim in `conformance/sapass/claims.toml`
(ids `cid.*`), with a shadow module under `CategoricalInfluenceDiagramsProofs/Shadows/`.

1. Reward kernels form a category: serial composition `(K₁, W₁) ; (K₂, W₂) = (K₁K₂, W₁K₂ + K₁W₂)` is associative and has the identity `(id, 0)` as a unit on both sides.
   (`cid.serial-composition`)
2. The tensor `(K₁ ⊗ K₂, W₁ ⊗ K₂ + K₁ ⊗ W₂)` is a functor: it satisfies the interchange law `(f ⊗ g) ; (f' ⊗ g') = (f ; f') ⊗ (g ; g')` and sends a pair of identities to the identity.
   (`cid.tensor`)
3. Reward kernels with stochastic probability component form a symmetric monoidal copy-discard category, `FinRew`, with associator, unitors, symmetry, copy and discard lifted from `FinStoch` with zero reward.
   (`cid.finrew-instances`)
4. Discard, lifted with zero reward, is natural for exactly the reward kernels whose probability component is normalised and whose reward from every input sums to zero, so it is not natural in general (`FinRew.discard_not_natural`).
   (`cid.discard-not-natural`)
5. For a fixed deterministic strategy, the interpretation of open influence diagrams sends serial composition to composition of reward kernels, identities to `(id, 0)`, and tensor to the tensor of reward kernels.
   (`cid.functoriality`)
6. For reward kernels whose suffix has a normalised probability component, and so for all open influence diagrams under a fixed strategy, `EU_{f;g}(μ, c) = EU_f(μ, c_g) = L_f + EU_g(ν_f, c)`.
   (`cid.contextual-identity`)
7. In the bundle's witness, every pair of separately optimal components composes to expected utility 1, while the joint optimum is 4.
   (`cid.isolated-obstruction`)
8. Against the boundary law of the isolated-optimal prefix, every legal suffix policy has value 1, while maximising at each boundary state gives value 2 with a selector that reads the hidden variable and is not a legal policy.
   (`cid.hidden-obstruction`)

Here `EU_f(μ, c) = Σ_x μ x Σ_y (W x y + K x y · c y)` for a boundary prior `μ` and a terminal
continuation `c`; `c_g y = Σ_z (W_g y z + K_g y z · c z)` is the suffix's value function,
`ν_f y = Σ_x μ x K_f x y` the boundary law induced by the prefix and
`L_f = Σ_x μ x Σ_y W_f x y` the prefix's reward.

## Scope and restrictions

- **Syntax.** Open influence diagrams (`IDNet X Y`) are ADR 0010's typed open nets
  (`OpenNet.Net X Y`) in full generality, whose generators are chance mechanisms or
  decisions according to their label, together with utility generators that read an
  ordered, typed scope of the net's variables. They are **not quotiented** by structural
  isomorphism, so functoriality is a set of equations on representatives
  (`interpret_comp`, `interpret_identity`, `interpret_tensor`), not a Mathlib `Functor` out of
  a syntax category. The isomorphism invariance of `interpret` is not proved.
- **Strategies.** Policies are deterministic and keyed by decision label (decisions with
  equal labels share one), as in the Julia package; a policy is a function of the values on
  the decision's information ports (its ordered parents). Behavioural policies are out of
  scope (ADR 0018, decision 4).
- **Observability.** The fixed-strategy semantics does not read observability flags.
  Information locality (`InformationLocal`, rule 3) is a separate predicate on finite
  influence diagrams; the hidden-input obstruction states legality directly on its witness.
- **Contextual identity.** Its first equation needs the suffix's `K` to be normalised
  (`eu_comp_general` gives the defect, `eu_comp_needs_normalised` shows it can be nonzero);
  the second needs nothing (`eu_continuation`). For interpreted diagrams `K` is always
  stochastic, so no hypothesis remains.
- **Obstructions.** The two witnesses are stated in the reward-kernel semantics (explicit
  `K` and `W` tables for the bundle's two components), not built in the typed syntax. They
  follow the bundle's Lean witness; the bundle is not imported.
- **Not proved:** a category of open influence diagrams with arbitrary gluing, evidence
  composition, optimisation of composites beyond the contextual identity, and the
  Julia-to-Lean refinement (ADR 0018, decision 6).

## Theorems

| Declaration | Statement |
|---|---|
| `Observability`, `ObservedInterface`, `.sum`, `.empty` | Boundary flags `observed`/`hidden` on an `OpenNet.Interface`, and their tensor and unit |
| `InformationLocal`, `informationLocal_of_no_hidden`, `.of_reveal` | Rule 3: no decision reads a boundary variable flagged hidden; hiding nothing, or revealing, keeps it |
| `RewardKernel`, `.comp`, `.id`, `.tensor`, `.lift` | `(K, W)` with composition `(K₁K₂, W₁K₂ + K₁W₂)`, identity `(id, 0)`, tensor `(K₁⊗K₂, W₁⊗K₂ + K₁⊗W₂)`, zero-reward lift |
| `RewardKernel.id_comp`, `comp_id`, `comp_assoc` | The category laws, for arbitrary real tables |
| `RewardKernel.tensor_comp_tensor`, `tensor_id` | Interchange `(f ⊗ g) ; (f' ⊗ g') = (f ; f') ⊗ (g ; g')`, and `id ⊗ id = id` |
| `RewardKernel.tensor_assoc`, `tensor_unit_left`, `tensor_unit_right`, `tensor_swap` | Naturality of the associator, unitors and symmetry (lifted with zero reward) |
| `RewardKernel.copy_assoc`, `copy_discard_left`, `copy_discard_right`, `copy_swap` | Copy and discard, lifted with zero reward, form a commutative comonoid |
| `RewardKernel.comp_discard`, `comp_discard_eq_discard_iff` | `f ; discard` keeps the row sums of `W`; discard is natural for `f` iff `K` is normalised and every row of `W` sums to zero |
| `RewardKernel.Examples.discard_not_natural` | A stochastic reward kernel earning reward one is not discarded by discard |
| `RewardKernel.Stochastic.comp`, `.tensor`, `.id`, `.ofFun`, `.discard` | Stochasticity of `K` is preserved by composition and tensor |
| `FinRew`, `instCategory`, `instMonoidalCategory`, `instSymmetricCategory`, `instComonObj`, `instIsCommComonObj`, `instCopyDiscardCategory` | The Mathlib instances on reward kernels with stochastic `K` |
| `FinRew.comp_discard_eq_iff`, `FinRew.discard_not_natural` | In `FinRew`, `f ≫ ε = ε` iff every row of `W` sums to zero; it fails for `unitReward`, so there is no Markov instance |
| `FinRew.liftHom`, `liftHom_comp`, `liftHom_id`, `liftHom_tensor`, `liftHom_injective` | `FinStoch` embeds faithfully in `FinRew` with zero reward |
| `RewardKernel.eu`, `continuation`, `pushforward`, `prefixReward` | `EU_f(μ, c)`, the value function `c_g`, the boundary law `ν_f`, the prefix reward `L_f` |
| `RewardKernel.eu_comp_general` | `EU_{f;g}(μ, c) = EU_f(μ, c_g) + Σ_x μ x Σ_y W_f x y (Σ_z K_g y z − 1)` |
| `RewardKernel.eu_comp`, `eu_continuation`, `contextual_identity` | With `K_g` normalised, `EU_{f;g}(μ, c) = EU_f(μ, c_g)`; always `EU_f(μ, c_g) = L_f + EU_g(ν_f, c)` |
| `RewardKernel.eu_comp_needs_normalised` | Without normalisation the first equation can fail |
| `IDSignature`, `IDNet`, `.comp`, `.tensor`, `.identity`, `.ofNet` | Decision labels and utility labels on an `OpenNet` signature; open nets with utility generators, composed along the nets |
| `IDNet.generator`, `IDNet.utility`, `IDNet.IsDecision`, `IDNet.info` | One chance or decision generator on its inputs; one utility on a scope; decisions and their information ports |
| `IDInterpretation`, `Strategy`, `interp`, `reward`, `rewardTable`, `interpret` | State spaces, chance and utility tables, deterministic policies by label, and the fixed-strategy reward kernel `(K_f, W_f)` |
| `interp_weight_decision`, `interp_weight_chance`, `interpret_utility_K`, `interpret_utility_W` | A decision is the point mass of its policy; a utility generator passes its interface through and earns its utility on the diagonal |
| `interpret_stochastic`, `interpretHom` | `K_f` is stochastic, so `interpret` lands in `FinRew` |
| `reward_comp`, `reward_tensor` | The total utility of a composite (or tensor) splits over its components |
| `rewardTable_comp`, `interpret_comp`, `interpretHom_comp` | `interpret σ (f ; g) = interpret σ f ; interpret σ g` |
| `interpret_identity`, `interpretHom_identity` | `interpret σ (id X) = (id, 0)` |
| `rewardTable_tensor`, `interpret_tensor`, `interpret_tensor_natural` | `interpret σ (f ⊗ g)`, read through the bijection of assignments of `X ⊔ X'` with pairs, is `interpret σ f ⊗ interpret σ g` |
| `IDInterpretation.contextual_identity` | The contextual identity for interpreted open influence diagrams, with no hypothesis |
| `Obstruction.isolated_optimisation_fails` | `INF-ISOLATED-OBSTRUCTION`: every pair of isolated optima composes to `1`, the joint optimum is `4` |
| `Obstruction.early_isolatedOptimal_iff`, `late_isolatedOptimal`, `composite_eu` | The prefix is isolated-optimal iff `a = false`; every suffix is isolated-optimal; the composite value is `1 + 3[a]` |
| `Obstruction.hidden_input_obstruction`, `peek_pointwise_max`, `peek_not_legal` | `INF-HIDDEN-OBSTRUCTION`: legal suffixes have value `1`; the pointwise maximiser has value `2` and reads the hidden `H` |

## Build and inspect

```sh
lake build --wfail
make audit
make docs
python3 ../../conformance/sapass/run.py --claim cid.functoriality   # one SA-Pass claim
```

`make audit` kernel-checks every declaration listed in `Audit.lean`, uses
`assert_no_sorry`, and fails unless every printed axiom belongs to
`{propext, Classical.choice, Quot.sound}`. It rejects an empty inventory, scans every Lean
source for escape hatches (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`,
`implemented_by`, `extern`, `#eval`), and then runs the driver's synthetic guard
regressions. `make docs` generates the Markdown (mdgen), HTML (pandoc) and PDF (pandoc and
LuaLaTeX, with the workspace's JuliaMono fonts) from the checked Lean source. The SA-Pass
shadow modules form a second library, `Shadows`, outside the default target; the runner
builds them. The Lean CI workflow checks out the four sibling repositories beside this
one, because Lake path dependencies need them.
