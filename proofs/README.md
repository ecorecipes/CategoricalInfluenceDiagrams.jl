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
9. If the reward-certificate checker accepts a decoded certificate at tolerance `τ`, its network is valid, no decision of the decoded open influence diagram reads an input flagged hidden, and for every pair of boundary assignments `(x, y)` the recorded `K` and `W` cells at the flat index of `(x, y)`, which is a bijection onto the cells of `K`, are within `τ` of `interpret σ f` at `(x, y)`, for the decoded diagram `f` and strategy `σ`.
   (`cid.certificate-sound`)
10. `decodeCertificate_eq_ok` proves that the reward-certificate decoder succeeds on a parsed JSON value with a certificate `c` exactly when the value is `c`'s layout key for key, with exactly the nine top-level keys and with the network and the utility scope rows read by CategoricalBayesianNetworks' record readers.
    (`cid.certificate-decode`)
11. The lens of a reward kernel, with the boundary law as its forward map and the value function as its backward map, sends serial composition with a normalised suffix to composition of lenses and the identity to the identity lens.
    (`cid.lens-functor`)
12. Serial composition of open games is associative and unital on equilibria: a strategy of three games in series is an equilibrium, under either bracketing, exactly when each game's strategy is an equilibrium in the context that the lenses of the other two transport to it.
    (`cid.game-category`)
13. For two decision games, a pair of strategies is an equilibrium of their serial composite exactly when neither component can raise the composite's expected utility by changing its own strategy alone.
    (`cid.game-nash`)
14. Every strategy that maximises expected utility in a context is an equilibrium there, for every game built from decision games and identities by serial composition.
    (`cid.game-optimum`)
15. An equilibrium need not be optimal: in a witness of two decisions that must agree, the later not observing the earlier, an equilibrium is worth 1 where the optimum is 2.
    (`cid.game-coordination`)
16. In the bundle's witness, the equilibria are exactly the strategies that take the early action, and each of them attains the joint optimum 4.
    (`cid.obstruction-equilibria`)
17. Evidence composes: weighting the fixed-strategy interpretation of open influence diagrams by a likelihood on the values of the generators sends serial composition to composition of reward kernels and tensor to the tensor of reward kernels, and the likelihood one gives back the unweighted interpretation.
    (`cid.evidence-functor`)
18. Carrying the evidence mass, the backward action of reward kernels on effects and the forward action on states are functorial with no normalisation hypothesis, and the evidence mass and the evidence-weighted value of a state against an effect are the same on either side of a reward kernel.
    (`cid.evidence-lens`)
19. For any two reward kernels, normalised or not, the composite's expected utility is the prefix's value against the suffix's effect, and the composite's conditional value, the evidence-weighted value divided by the evidence mass, is the conditional value of the prefix's pushed-forward state against the suffix's pulled-back effect.
    (`cid.evidence-contextual`)
20. Hard evidence on a boundary, the diagonal indicator with zero reward, is idempotent and commutes with other hard evidence.
    (`cid.observe-idempotent`)
21. Normalising each component on its own evidence before composing is not sound: with a uniform binary state worth 1 when true and evidence nine times likelier when it is true, the conditional value is 9/10, while the components normalised one by one give 1/2.
    (`cid.local-normalisation`)
22. For a behavioural strategy, which gives every decision a table of action probabilities, the interpretation of open influence diagrams sends serial composition to composition of reward kernels, identities to `(id, 0)` and tensor to the tensor of reward kernels, and a deterministic strategy has the interpretation of its point masses.
    (`cid.behaviour-functor`)
23. A mixture of reward kernels with nonnegative weights summing to one has expected utility at most that of one of its components, and, when masses are nonnegative and a component of zero mass has zero evidence-weighted value, conditional value at most that of one of its components of positive mass.
    (`cid.mixture-sufficiency`)
24. When two decisions share a policy, randomising can help: in the absent-minded driver, continuing with probability 2/3 at both junctions is worth 4/3, while either deterministic policy is worth at most 1; with a policy each, the deterministic pair that continues and then exits is worth 4 and no pair of probabilities does better.
    (`cid.absent-minded`)
25. For two decision games and a prior that is a product of probability vectors, a pair of strategies is an equilibrium of their tensor exactly when neither factor can raise the composite's expected utility by changing its own strategy alone.
    (`cid.game-tensor`)
26. With a correlated prior no context of a factor alone is exact: in a witness with two equal binary inputs and a payoff for matching outputs, the first factor's best responses are exactly the policy that copies its input, but in no context of a probability vector on its input and a continuation on its output are its equilibria exactly that policy.
    (`cid.tensor-correlated`)
27. A strategy that maximises the value from every input state is a best response under every nonnegative prior, and a strategy of two such perfect games in series is an equilibrium exactly when, by backward induction, the suffix is perfect against the continuation and the prefix against the suffix's value function.
    (`cid.perfect-equilibrium`)
28. An equilibrium can rest on a choice at a state it never reaches: in a witness where acting first is worth 4 if the second decision cooperates, 0 if it does not and 1 without acting, not acting against a refusal is an equilibrium worth 1, while the perfect equilibria are exactly the strategies that act and cooperate, worth the optimum 4.
    (`cid.threat-witness`)
29. If the composition checker accepts a composition certificate at tolerance `τ`, its parts' interfaces line up and, for every input coordinate `x` of the left part and output coordinate `z` of the right part, the decoded composite's exact probability and reward at `(x, z)` are within an explicit bound, computed from `τ` and the recorded cells, of the composite in the category of reward kernels of the decoded parts' exact tables.
    (`cid.composition-certificate`)
30. If the tensor checker accepts a tensor certificate at tolerance `τ`, the composite's interfaces are the parts' side by side and, for all coordinates of the two parts, the decoded composite's exact probability and reward at the joined coordinates are within an explicit bound, computed from `τ` and the recorded cells, of the tensor in the category of reward kernels of the decoded parts' exact tables.
    (`cid.tensor-certificate`)
31. Every stochastic kernel between finite spaces is the mixture of the deterministic kernels of its rules, each weighted by the probability of drawing it, so one randomised decision placed in a serial context, beside other wires, has expected utility at most that of some deterministic rule in its place.
    (`cid.single-decision`)
32. When no two decision generators of an open influence diagram share a label, every behavioural strategy is matched by a deterministic one: for every prior and continuation some deterministic strategy has at least its expected utility, and, with nonnegative likelihoods, a state whose reward vanishes where its mass does and an effect whose value vanishes where its likelihood does, if the evidence has positive mass some deterministic strategy gives it positive mass and at least the same conditional value.
    (`cid.kuhn`)
33. Isomorphic open influence diagrams have the same semantics under every behavioural strategy, and so under every deterministic one, and the semantics is a functor to `FinRew` from the category of typed interfaces and open influence diagrams up to isomorphism under serial composition.
    (`cid.syntax-functor`)
34. At an optimum of a policy shared by two uses in series, separated by any fixed kernels, the gain from changing the first use alone towards another policy plus the gain from changing the second use alone is at most zero.
    (`cid.shared-first-order`)
35. In the absent-minded driver, at the shared optimum of continuing with probability 2/3, continuing for sure at the first junction alone gains 2/3 and at the second junction alone loses 2/3.
    (`cid.per-use-gains`)
36. If the colimit checker accepts a colimit certificate, then for all input and output coordinates of the composite, exactly, its decoded probability is the sum, over the boundary coordinates of the parts consistent with them, of the product of the parts' decoded probabilities, and its decoded reward is the corresponding sum of each part's reward times the other parts' probabilities.
    (`cid.colimit-certificate`)

Here `EU_f(μ, c) = Σ_x μ x Σ_y (W x y + K x y · c y)` for a boundary prior `μ` and a terminal
continuation `c`; `c_g y = Σ_z (W_g y z + K_g y z · c z)` is the suffix's value function,
`ν_f y = Σ_x μ x K_f x y` the boundary law induced by the prefix and
`L_f = Σ_x μ x Σ_y W_f x y` the prefix's reward. An effect `(m, c)` on `Y` is the
likelihood `m` of the evidence still to come and the evidence-weighted value `c` of what
follows, pulled back by `(K, W)` to `(K m, W m + K c)`; a state `(ν, ρ)` on `X` is the
unnormalised law `ν` of the evidence seen so far and the reward-weighted law `ρ`, pushed
forward to `(ν K, ρ K + ν W)`. Their evidence mass is `Σ ν m`, their evidence-weighted
value `Σ (ρ m + ν c)`, and the conditional value is the ratio.

## Scope and restrictions

- **Syntax.** Open influence diagrams (`IDNet X Y`) are ADR 0010's typed open nets
  (`OpenNet.Net X Y`) in full generality, whose generators are chance mechanisms or
  decisions according to their label, together with utility generators that read an
  ordered, typed scope of the net's variables. Module `SyntaxCategory` quotients them by
  isomorphism (`IDNet.Iso`: a bijection of generators and of utility generators preserving
  labels, ordered parents, outputs and scopes), proves `interpret` and `interpretB`
  invariant under it, and makes the semantics a Mathlib `Functor` from the resulting
  category `IDCat` to `FinRew` (`interpretFunctor`). Only serial composition is quotiented:
  the tensor (`interpret_tensor`) stays an equation on representatives, and the monoidal
  structure of the quotient is not developed.
- **Strategies.** Policies are keyed by decision label (decisions with equal labels share
  one), as in the Julia package. A deterministic policy is a function of the values on the
  decision's information ports (its ordered parents); a behavioural policy (module
  `Behaviour`, ADR 0022) is a table of probabilities given those values, normalised on
  correctly typed rows, drawn from independently at every use. Deterministic sufficiency
  is proved for mixtures of reward kernels (`eu_mix_le`, `conditionalValue_mix_le`), for one
  randomised decision in a serial context beside other wires
  (`single_decision_sufficiency`), and for every decision of an `IDNet` at once when no two
  decision generators share a label (module `Kuhn`: `kuhn_eu`, and `kuhn_conditional` given
  likelihood evidence and a state and an effect at the boundary), one row of the strategy at
  a time (`kernelAt_eq_mix`). It needs every decision's result type to be inhabited, as a
  deterministic strategy does. With shared labels it fails (`AbsentMinded`).
- **Shared policies** (ADR 0024; module `SharedPolicy`). The first-order condition at an
  optimum is proved for reward kernels: paths of reward kernels have first-order terms that
  obey the product rule under serial composition (`HasDeriv.comp`), so at an optimum of a
  policy shared by two uses the per-use gains sum to at most zero
  (`shared_optimum_first_order`). The theorem is stated for two uses; more uses follow by
  the same product rule, which is proved for any serial composite. That Julia's
  `policy_regrets` computes these per-use gains is checked by the test suite against finite
  differences, not proved.
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
- **Reward certificates** (ADR 0019; modules `Certificate/Record`, `Json`, `Exact`, `Check`,
  `Sound`). `lake exe check_certificate` decodes an `OpenInfluence.RewardCertificate/v1`
  file that `export_reward_certificate` wrote and decides `check τ c`. The theorems are
  about the decoded record. JSON parsing (CategoricalBayesianNetworks' strict parser), the
  Julia exporter, Catlab's colimits and Julia's `Float64` arithmetic are trusted, not proved
  (ADR 0019, decision 5). Acceptance requires every chance row to sum to exactly one over
  the rationals, because the decoded `IDInterpretation` must be normalised. Binary64 rows
  seldom do, so most `binary64_exact` certificates are rejected as outside the exact
  semantics, with their largest row deviation and result errors reported. The
  `rational_exact` mode, whose exact companions the checker also verifies to round to their
  words, is the way to certify such a model. State `k` of a variable (`Fin (dimension t)`) is
  read as the state of position `k + 1`; this is the format's convention, not a theorem. The
  checker also requires generators with equal labels to have equal tables, since the decoded
  signature keys tables by label. The exact reward kernel is computed by enumeration, one
  pass over the generator states per input state (`Certificate/Fast`, proved equal to the
  cell-by-cell sums), so checking costs about `|X| · |Z|` weight evaluations, for the input
  and generator state spaces, rather than `|X| · |Y| · |Z|`.
- **Lenses and games** (ADR 0020; module `Lens`). A reward kernel's lens is the pair
  (`pushforward`, `continuation`) on real functions; its laws need the later kernel
  normalised, as the contextual identity does. A `Game` has a type of strategies, a
  normalised play for each and an equilibrium predicate; decision games, identity games,
  serial composition and the tensor (module `GameTensor`) are defined. The tensor gives each
  factor the context of its marginal prior and the continuation the other factor induces; it
  is exact for product priors (`tensor_decision_eq_iff`), and no context of a factor alone is
  exact for correlated priors (`correlated_no_factor_context`), since the context a tensor
  factor needs depends on the other factor's input state. Equilibrium is a person-by-person optimum, not
  the optimum (`coordination_equilibrium_not_optimal`). The results are about the reward-kernel
  semantics, like the obstructions; that Julia's `component_contexts`, `regrets` and
  `best_response_dynamics` compute these contexts and equilibria is checked by the test
  suite, not proved.
- **Evidence** (ADR 0021; module `Evidence`). Hard evidence is the indicator likelihood
  of a general likelihood on the values of generators, keyed by label as strategies are
  (`IDInterpretation.Likelihood`); the evidence-weighted interpretation is not stochastic, so
  it is a reward kernel but not a morphism of `FinRew`. Its functoriality is proved for
  serial composition (`interpretE_comp`) and tensor (`interpretE_tensor`). Evidence on an input of the
  syntax, which has no generator, is the composition with `observe` on that boundary, so it is
  covered at the level of reward kernels only. The conditional value is a real quotient: it
  is `0` when the evidence mass is `0` (Lean's division), and nothing is claimed about that
  case; Julia raises `ImpossibleEvidenceError` instead. ADR 0014's binary64 rules (trusted
  masses, exact fallback, tolerated negative entries) are Julia's, not proved. That Julia's
  `boundary_state`, `continuation_effect`, `evidence_mass` and `conditional_value` compute
  these quantities is checked by the test suite against the closed-composite oracle.
- **Composition certificates** (ADR 0023; module `Certificate/Composition`). `lake exe
  check_composition` decodes three reward certificates, the two parts and their composite,
  checks each, checks that the interfaces line up by attributes, and checks every recorded
  cell of the composite against the composite of the parts' recorded cells. Soundness bounds
  the gap between the decoded composite's exact tables and the composite of the decoded
  parts' exact tables, cell by cell; with `interpret_K_eq` and `interpret_W_eq` these are the
  decoded diagrams' `interpret`. Tensor certificates do the same for `otimes`, the
  composite's cells against the products of the parts'. It ties semantics, not syntax.
- **Colimit certificates** (ADR 0025; module `Certificate/Colimit`). The same executable
  reads `OpenInfluence.ColimitCertificate/v1`: reward certificates of any number of parts and
  of their composite, and Catlab's cocone maps as legs. The checker verifies that the legs
  are a colimit witness on the decoded records (`Wired`), and soundness gives the
  composite's exact `K` and `W` as junction sums of the parts' (`colimit_exactK`,
  `colimit_exactW`), with no tolerance, for `compose`, `otimes`, `glue` and `oapply` alike.
  The witness is checked on the records; it is not turned into an `IDNet.Iso` between the
  decoded composite and `IDNet.comp` of the decoded parts, whose interfaces are distinct Lean
  terms.
- **Not proved:** a monoidal category of open influence diagrams up to isomorphism,
  gluing in the Lean syntax, and optimisation of composites beyond the contextual identity.
  Reward certificates check Julia's numbers for the diagram a certificate records against
  `interpret`; colimit certificates check, on the records, that Julia's composite is the
  colimit of its parts, and give its semantics exactly. The Julia operations themselves,
  Catlab's colimits and the exporter remain trusted: a certificate is checked for the
  composite it records.

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
| `RewardKernel.pushforward_comp`, `continuation_comp`, `pushforward_id`, `continuation_id`, `eu_eq_prefixReward_add` | The boundary law composes forward, the value function backward (suffix normalised); identities fix both; `EU_f(μ, c) = L_f(μ) + Σ_y ν_f y c y` |
| `Lens`, `Lens.comp`, `Lens.id`, `RewardKernel.lens`, `lens_comp`, `lens_id` | Lenses on real functions and the lens of a reward kernel, a functor on serial composites with a normalised suffix |
| `Game`, `Game.decision`, `Game.idGame`, `Game.seq` | Open games over reward kernels: strategies, a normalised play, equilibria in a context `(μ, c)`; decision games maximise, the composite asks each part to be an equilibrium in the context the other induces |
| `Game.seq_seq_eq_iff`, `seq_assoc_eq`, `seq_assoc_play`, `idGame_seq_eq`, `seq_idGame_eq` | Three games in series: each in equilibrium in its transported context; associativity and units on plays and equilibria |
| `Game.seq_decision_eq_iff` | Two decision games: an equilibrium is a pair from which neither gains alone, measured by the composite's expected utility |
| `Game.Sound`, `decision_sound`, `idGame_sound`, `seq_sound` | Maximisers are equilibria, for decision and identity games and serial composites of such games |
| `Coordination.first`, `second`, `payoff`, `game`, `composite_eu`, `game_eq_iff`, `coordination_equilibrium_not_optimal` | Two decisions that must agree, the later blind to the earlier: equilibria worth 1 and 2, optimum 2 |
| `Game.marg₁`, `marg₂`, `leftCont`, `rightCont`, `tensor`, `prodPrior`, `marg₁_prod`, `marg₂_prod`, `sum_comm4`, `tensor_eu_sum`, `tensor_eu_left`, `tensor_eu_right`, `tensor_decision_eq_iff` | The tensor of games; with a product prior a factor's context is exact, and an equilibrium of two decision games is a pair of mutual best responses |
| `CorrelatedTensor.copyPlay`, `first`, `prior`, `payoff`, `joint_eu`, `correlated_best_responses`, `first_eu`, `correlated_no_factor_context` | With equal inputs, the best response copies its input, and no context of the factor alone has exactly that equilibrium |
| `Game.perfect`, `perfect_eq_decision`, `seq_perfect_eq_iff` | Perfect decision games (optimal from every input state); perfection refines equilibrium for nonnegative priors; perfect equilibria of a series are found by backward induction |
| `Threat.first`, `second`, `payoff`, `composite_eu`, `first_value`, `second_value`, `threat`, `threat_equilibrium`, `threat_perfect_iff`, `threat_optimum` | An equilibrium worth 1 sustained by an untested refusal; the perfect equilibria act and cooperate, worth the optimum 4 |
| `Obstruction.early_normalised`, `Obstruction.game`, `obstruction_eq_iff` | In the obstruction witness the equilibria are exactly the strategies taking the early action |
| `RewardKernel.Effect`, `State`, `Effect.ofValue`, `State.ofPrior`, `pull`, `push`, `mass`, `value`, `conditionalValue` | Effects `(m, c)` and states `(ν, ρ)`, the backward and forward actions of a reward kernel, and the evidence mass, evidence-weighted value and conditional value of a state against an effect |
| `RewardKernel.pull_comp`, `push_comp`, `pull_id`, `push_id`, `mass_push`, `value_push` | Both actions are functorial with no normalisation hypothesis; the pairing is the same on either side of a reward kernel |
| `RewardKernel.mass_comp`, `conditionalValue_comp`, `value_ofPrior`, `pull_ofValue`, `eu_comp_pull` | The composite's evidence mass is the pairing of the prefix's boundary law with the suffix's likelihood; its conditional value is computed at the boundary; with mass one these are ADR 0018's expected utility and ADR 0020's value function; `EU_{f;g}(μ, c)` is the prefix's value against the suffix's effect, normalised or not |
| `RewardKernel.observe`, `observe_comp_observe`, `observe_idem`, `observe_comm` | Hard evidence on a boundary: two observations compose to their conjunction, so observing is idempotent and commutes |
| `LocalNormalisation.normalise`, `prior`, `evidence`, `composite_conditionalValue`, `normalised_conditionalValue`, `local_normalisation_obstruction` | Normalising each component on its own evidence gives `1/2` where the composite conditioned on all of it gives `9/10` |
| `IDInterpretation.Likelihood`, `lik`, `kernelE`, `rewardTableE`, `interpretE`, `lik_comp`, `kernelE_comp`, `rewardTableE_comp`, `interpretE_comp`, `lik_tensor`, `kernelE_tensor`, `rewardTableE_tensor`, `interpretE_tensor`, `interpretE_one` | The evidence-weighted interpretation of the syntax, functorial under serial composition and tensor; the likelihood one gives `interpret` |
| `IDInterpretation.Behaviour`, `interpB`, `pointMass`, `interpB_pointMass`, `rewardB`, `rewardTableB`, `interpretB`, `interpretB_stochastic` | Behavioural strategies and their semantics; the point masses of a deterministic strategy give `interp` |
| `rewardB_comp`, `rewardTableB_comp`, `interpretB_comp`, `interpretB_identity`, `rewardB_tensor`, `rewardTableB_tensor`, `kernel_tensor_joinB`, `interpretB_tensor`, `contextual_identityB`, `interpretB_pointMass` | Functoriality and the contextual identity for behavioural strategies |
| `RewardKernel.mix`, `mix_comp`, `comp_mix`, `eu_mix`, `eu_mix_le`, `mediant_le`, `pull_mix`, `mass_value_mix`, `conditionalValue_mix_le` | Mixtures compose affinely; their expected utility, and given evidence their conditional value, never exceed the best component's |
| `RewardKernel.ruleWeight`, `kernel_eq_mix_ofFun`, `ruleWeight_nonneg`, `sum_ruleWeight`, `lift_eq_mix`, `mix_tensor`, `single_decision_sufficiency` | A stochastic kernel is the mixture of its deterministic rules; one randomised decision in a serial context beside other wires is never better than the best deterministic rule |
| `AbsentMinded.first`, `second`, `drive_eu`, `randomising_helps`, `independent_deterministic_optimal` | The absent-minded driver: a shared policy is best randomised (`4/3 > 1`); separate policies are best deterministic (`4`) |
| `RewardCertificate.Certificate`, `Value`, `ChanceTable`, `Utility`, `Policy`, `Result`, `isPolicy` | The decoded record: CategoricalBayesianNetworks' raw network, flags, chance and utility tables, one policy per decision name, the recorded `K` and `W`; a generator is a decision when its reference is a `policy` reference |
| `Json.decodeCertificate`, `read`, `decodeCertificate_eq_ok`, `read_eq_ok`, `networkBody_fields` | The decoder succeeds with `c` exactly when the JSON is `c`'s layout key for key, reusing CategoricalBayesianNetworks' network readers and InfluenceDiagrams' value decoder |
| `Json.decodeFlag_eq_ok`, `decodeMode_eq_ok`, `decodeMetadata_eq_ok`, `decodeObservability_eq_ok`, `decodeChanceTable_eq_ok`, `decodeUtility_eq_ok`, `decodePolicy_eq_ok`, `decodeResult_eq_ok` | Each new record decodes exactly when the JSON has its layout |
| `flatIndex`, `flatIndex_lt`, `flatIndex_append`, `flatIndex_injective` | The lexicographic cell index, last axis fastest: in range, a chance table is a list of rows, distinct coordinates have distinct cells |
| `Certificate.exactK`, `exactW`, `resultIndex`, `resultCell_bijective` | The reward kernel of the certificate's numbers over `ℚ` by enumeration; the result layout is a bijection onto the cells |
| `Certificate.readOut?`, `reads_iff`, `outIndex`, `outIndex_injective`, `accRow`, `accRow_getD`, `kErrorFast`, `wErrorFast`, `kErrorFast_le_iff`, `wErrorFast_le_iff`, `kErrorFast_eq`, `wErrorFast_eq` | One pass over the generator states per input state gives the row of `K` and `W`; the fast errors are the errors, so the checker uses them |
| `Composition`, `rowAttrs`, `recoord`, `Composition.Aligned`, `inC`, `outC`, `mid`, `kHat`, `wHat`, `compKError`, `compWError`, `check`, `firstFailure`, `accepted_of_check` | Composition certificates (ADR 0023): three reward certificates, aligned interfaces, and the composite's recorded cells against the composite of the parts' |
| `tensorFormatName`, `joinCoord`, `Composition.TensorAligned`, `joinIn`, `joinOut`, `tensorKError`, `tensorWError`, `checkTensor`, `firstFailureTensor`, `tensor_sound_K`, `tensor_sound_W`, `Json.decodeTensor`, `Json.readOperation` | Tensor certificates: the composite's interfaces are the parts' side by side, and its exact tables are within an explicit bound of the tensor of the parts' |
| `Composition.abs_mul_sub_le`, `abs_sub_le_three`, `composition_sound_K`, `composition_sound_W`, `Json.decodeComposition`, `Json.readComposition` | On acceptance the decoded composite's exact `K` and `W` are within an explicit bound of the composite of the decoded parts' exact tables |
| `Certificate.check`, `stages`, `firstFailure`, `check_iff_firstFailure`, `Accepted`, `check_iff_accepted` | The checker as sixteen ordered stages; acceptance is their conjunction, and the reported stage is the first that fails |
| `Certificate.check_sound`, `InformationLocal` | Acceptance gives a valid network and information locality with the recorded flags |
| `sig`, `Certificate.model`, `strategyOf`, `diagram`, `chanceEntry_normalized` | The decoded signature, `IDInterpretation` (normalised by the exact row sums), strategy and `IDNet` |
| `Certificate.interpret_K_eq`, `interpret_W_eq` | `interpret σ f` at the boundary assignments of coordinates `x`, `y` is exactly `exactK x y`, `exactW x y` |
| `Certificate.reward_certificate_sound_K`, `reward_certificate_sound_W`, `boundaryIndex_bijective`, `diagram_informationLocal`, `semantics_stochastic` | On acceptance, every recorded cell is within `τ` of `interpret σ f` at the boundary assignment its flat index encodes, a bijection; no decision reads an input not flagged `observed` |
| `IDInterpretation.setRow`, `weight_setRow`, `recast`, `jointAt`, `likAt`, `kernelAt`, `kernelAt_congr`, `interpretBE`, `interpretBE_one`, `interpretBE_pointMass`, `kernelAt_recast` | One row of a behavioural strategy replaced by a point mass; the likelihood-weighted behavioural semantics, read on any interpretation's assignments; the likelihood one gives `interpretB`, point masses give `interpretE` |
| `IDInterpretation.DistinctDecisions`, `jointAt_affine`, `kernelAt_eq_mix`, `rows`, `DetAt`, `det_joint`, `kuhn_induction`, `kuhn_eu`, `kuhn_conditional` | Kuhn's theorem: with distinct decision labels the semantics is a mixture over each row read, so some deterministic strategy does as well, in expected utility and in conditional value given evidence |
| `RewardKernel.eu_reindex`, `mass_value_reindex`, `mass_pull_nonneg`, `value_pull_eq_zero` | Expected utility, mass and value are invariant under reindexing the boundaries; zero evidence mass means zero evidence-weighted value for nonnegative data |
| `IDNet.Iso`, `.refl`, `.trans`, `.symm`, `.comp`, `IDNet.setoid`, `id_comp_iso`, `comp_id_iso`, `assoc_iso` | Isomorphism of open influence diagrams, a congruence for serial composition, with the unit and associativity laws up to isomorphism |
| `IDInterpretation.rewardB_iso`, `interpretB_iso`, `interpret_iso`, `IDCat`, `IDHom`, `IDCat.category`, `interpretClass`, `interpretFunctor`, `interpretFunctor_map`, `interpretFunctor_pointMass` | The semantics is invariant under isomorphism and a functor from the category of diagrams up to isomorphism to `FinRew` |
| `RewardKernel.lin`, `lin_comp`, `comp_lin`, `eu_lin`, `HasDeriv`, `segment`, `hasDeriv_segment`, `hasDeriv_const`, `HasDeriv.comp`, `HasDeriv.eu`, `deriv_nonpos_of_le`, `first_order_optimum`, `shared_optimum_first_order` | Paths of reward kernels and their first-order terms; the product rule for serial composition; at an optimum of a shared policy the per-use gains sum to at most zero |
| `AbsentMinded.per_use_gains` | At the driver's shared optimum the first junction alone gains `2/3` and the second alone loses `2/3` |
| `Leg`, `Colimit`, `Certificate.IsBoundary`, `policyActions`, `Colimit.Wired`, `Ports`, `Row`, `Consistent`, `Colimit.check`, `firstFailure` | Colimit certificates (ADR 0025): parts, composite and Catlab's cocone; the colimit-witness conditions and the checker |
| `Colimit.split`, `split_bijective`, `valueP`, `weight_gm`, `joint_split`, `reward_split`, `consistent_tz_iff`, `ports_unique`, `sum_mul_prod_erase` | The composite's generator states split into the parts'; values, weights and rewards factor over the parts; the consistent boundary coordinates are unique |
| `Colimit.colimit_exactK`, `colimit_exactW`, `colimit_sound_K`, `colimit_sound_W`, `Json.decodeLeg`, `Json.decodeColimit`, `Json.readColimit` | On acceptance the composite's exact `K` and `W` are the junction sums of the parts', exactly |

## Build and inspect

```sh
lake build --wfail
make audit
make check-certificates
lake exe check_certificate PATH [--tol τ]                          # one reward certificate
make docs
python3 ../../conformance/sapass/run.py --claim cid.functoriality   # one SA-Pass claim
```

`lake exe check_certificate PATH [--tol τ]` decodes and checks one reward certificate. The
tolerance is a decimal such as `1e-12` (the default), parsed exactly to a rational. It prints
the counts, the largest chance-row deviation and the largest `K` and `W` errors, then
`accepted` (exit 0) or `rejected:` with the first failing stage (exit 1); a usage or file
error exits 2. `make check-certificates` builds it and runs it on every file in
`certificate-fixtures/`, comparing each outcome with `certificate-fixtures/EXPECTED.md`. The
Julia fixtures there are written by the package's `scripts/write_certificate_fixtures.jl`,
the `hand-*.json` and `*.bad.json` ones by `scripts/hand_fixtures.py`.

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
