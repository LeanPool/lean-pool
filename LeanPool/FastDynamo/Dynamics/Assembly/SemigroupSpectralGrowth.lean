/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.InductionSemigroupSpectrum

/-!
# Lemma A.1: semigroup generation and spectral growth

The paper's Lemma A.1 (`lem:semigroup-spectral-growth`), together with the facts about
`γ(u, ε)` that §1.1 states with it, as one statement: `SemigroupSpectralGrowth u hu hε`, proved
for every divergence-free velocity and every `ε > 0` by `semigroupSpectralGrowth_holds`.

For a divergence-free `u ∈ W^{1,∞}(T³; ℝ³)` and `ε > 0` the lemma says: `L_{ε,u}` with domain
`H² ∩ L²_σ` generates an analytic `C₀`-semigroup on `L²_σ`; its resolvent is compact; `e^{tL_{ε,u}}`
is compact for every `t > 0`; the spectral mapping `eq:compact-semigroup-spectral-mapping` holds for
`t > 0`; and `γ(u, ε) = max {Re λ : λ ∈ σ(L_{ε,u})}` (`eq:growth-rate-spectral-bound`), that is, the
supremum is attained.  §1.1 defines `γ(u, ε)` as the limit `eq:semigroup-growth-rate` and states
that the limit exists (the sentence after that display) and, after the definition of fast and slow
dynamos, that the supremum is attained at an eigenvalue.

The fields of `SemigroupSpectralGrowth`, in this order:

* `generator_eq`, `generator_curlForm`, `generator_unique`, `analytic` — generation;
* `resolventSet_nonempty`, `isCompactOperator_resolvent` — compact resolvent;
* `isCompactOperator_semigroup` — immediate compactness;
* `spectralMapping` — `eq:compact-semigroup-spectral-mapping`;
* `gamma_tendsto` — `γ(u, ε)` is the limit `eq:semigroup-growth-rate`;
* `gamma_eq_iSup` — `eq:growth-rate-spectral-bound`;
* `zero_mem_spectrum` — `0 ∈ σ(L_{ε,u})`, a step of the paper's proof;
* `exists_eigenvalue_re_eq_gamma` — attainment at an eigenvalue.

## How the Lean statement differs from the paper's

* **Model.**  The torus is the product model `T² × T` of `T³` (`ProductTorus3`), the state
  space is `productSolenoidalSubspace`, the Fourier-defined `L²_σ` of that model, and the velocity
  is an axially independent `TransverseRealW1Inf`, divergence-free in the sense
  `IsTransverseDivergenceFree`.  The semigroup is `solenoidalInductionSemigroup u hu hε`;
  `gamma u hu hε` is the growth bound of its isometric transport `literalInductionSemigroup` to
  the literal three-torus, which has the same operator norms
  (`StronglyContinuousSemigroup.norm_congr`) and the same growth bound
  (`growthBound_literalInductionSemigroup`).  The clauses are stated for the product semigroup
  and are not restated for the transported one.
* **The operator.**  The generator is `solenoidalInductionOperator u hu ε`: domain the
  divergence-free `H²` fields `solenoidalH2`, values the auxiliary transport–stretching action
  `productInductionAction u ε`.  On a divergence-free `H²` field this action is the paper's
  `curl(u × B) + εΔB` of `eq:physical-generator`: its embedding in the Fourier model of `H⁻²`
  is the curl form `productPhysicalInductionAction u ε B`
  (`productInductionAction_toHMinus2_eq_physical`), and that embedding is injective, so the curl
  form, computed in `H⁻²`, is the `L²` field `productInductionAction u ε B`.  The field
  `generator_curlForm` records this for the generator.
* **Generation.**  The paper perturbs `εΔ` on `L²_σ` (Engel–Nagel III.2.10).  Here the
  auxiliary operator generates a semigroup on all of `L²` by the Hille–Yosida theorem, its
  generator is identified (`HilleYosidaRay.generator_semigroup`), and the semigroup is restricted
  to the closed invariant subspace `L²_σ`, whose generator is the part of the generator in `L²_σ`
  (`generator_solenoidalInductionSemigroup`).  `generator_unique` states that the semigroup
  generated is unique, a standard fact that the paper uses without stating it.
* **Analyticity.**  The semigroup is proved analytic of angle `π/4`, in the sense
  `IsAnalyticSemigroup` (an extension to the open sector `|arg z| < π/4` that agrees with the
  semigroup on `[0, ∞)`, obeys the semigroup law, is holomorphic in the operator norm and tends
  strongly to the identity at `0` within every smaller sector, Engel–Nagel Definition II.4.5);
  the paper names no angle.  The proof passes a sector condition on the
  numerical range (`exists_productInduction_sectorial`) to the Yosida approximants in complex
  time (`HilleYosidaRay.isAnalyticSemigroup_of_sectorial`), not Engel–Nagel III.2.10.
* **Compactness.**  The resolvent factors through the compact embedding `H² → L²`
  (`isCompactOperator_productH2Embedding`), as in the paper; compactness of `e^{tL}` for `t > 0`
  is proved directly from analyticity (`IsAnalyticSemigroup.isCompactOperator`), where the paper
  cites Engel–Nagel II.4.29.
* **Spectral mapping and the spectral bound.**  The paper cites Engel–Nagel IV.3.11, IV.3.12 and
  V.3.2.  Here (`IsAnalyticSemigroup.spectrum_diff_zero`, `IsAnalyticSemigroup.growthBound_eq_iSup`)
  the non-zero spectrum of the compact operator `e^{tL}` consists of eigenvalues, each eigenspace
  is finite-dimensional and invariant under `L e^{tL}`, which therefore has an eigenvector; an
  eigenvector gives `‖e^{tL}‖ ≥ e^{t Re λ}`, so the growth bound `ω₀` is finite, and Gelfand's
  formula for `e^{L}` identifies `e^{ω₀}` with its spectral radius, attained at a point `e^{λ}`
  with `λ ∈ σ(L)`.  The unbounded spectrum is
  `LinearPMap.spectrum`, the complement of the set of `z` at which `z − L` has a bounded
  two-sided inverse.
* **The growth rate.**  `gamma` is defined as the growth bound, the `limsup` in `EReal` of
  `t⁻¹ log ‖e^{tL}‖`; `gamma_tendsto` states that it is a real number and a genuine limit, as the
  paper asserts after `eq:semigroup-growth-rate` (`gamma_eq_lim`, through
  `one_le_norm_solenoidalInductionSemigroup` and `tendsto_growthExponent`).  The paper's
  argument for the limit (subadditivity and local boundedness) is
  `StronglyContinuousSemigroup.growthBound_eq_iInf`.
* **`0 ∈ σ(L_{ε,u})`** is not a clause of the lemma; the paper derives it in the proof, from the
  vanishing mean of `L_{ε,u}B`, to make the supremum attained.  It is kept as a field because it
  makes the supremum in `gamma_eq_iSup` a supremum over a non-empty set.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Topology

/-- **Lemma A.1 of the paper** (`lem:semigroup-spectral-growth`, "Semigroup generation and
spectral growth"), with the facts on `γ(u, ε)` stated in §1.1, for one divergence-free velocity
`u` and one diffusivity `ε > 0`, about the induction semigroup
`e^{tL_{ε,u}} = solenoidalInductionSemigroup u hu hε` on `L²_σ` and its generator `L_{ε,u}`.
The module docstring lists how each clause differs from the paper's. -/
structure SemigroupSpectralGrowth (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    {ε : ℝ} (hε : 0 < ε) : Prop where
  /-- "The operator `L_{ε,u}`, with domain `H² ∩ L²_σ`, generates … a `C₀`-semigroup on `L²_σ`":
  the generator of `e^{tL_{ε,u}}` is the induction operator with domain the divergence-free `H²`
  fields. -/
  generator_eq : (solenoidalInductionSemigroup u hu hε).generator =
    (solenoidalInductionOperator u hu ε).toLinearPMap
  /-- The generator is the curl form `L_{ε,u} B = curl(u × B) + εΔB` of `eq:physical-generator`:
  at every point `x = B` of its domain (`B ∈ H²`), its value, embedded in the Fourier model of
  `H⁻²`, is `productPhysicalInductionAction u ε B`. -/
  generator_curlForm : ∀ (x : (solenoidalInductionSemigroup u hu hε).generator.domain)
    (B : ProductC3H2), productH2Embedding B = ((x : productSolenoidalSubspace) : ProductC3L2) →
      productL2ToHMinus2
          (((solenoidalInductionSemigroup u hu hε).generator x : productSolenoidalSubspace) :
            ProductC3L2) =
        productPhysicalInductionAction u ε B
  /-- The semigroup generated is unique: every `C₀`-semigroup on `L²_σ` whose generator is the
  induction operator with domain `H² ∩ L²_σ` is `e^{tL_{ε,u}}`. -/
  generator_unique : ∀ S : StronglyContinuousSemigroup productSolenoidalSubspace,
    S.generator = (solenoidalInductionOperator u hu ε).toLinearPMap →
      S = solenoidalInductionSemigroup u hu hε
  /-- "… generates an analytic `C₀`-semigroup": the semigroup is analytic, of angle `π/4`. -/
  analytic : IsAnalyticSemigroup (solenoidalInductionSemigroup u hu hε) (Real.pi / 4)
  /-- The resolvent set of `L_{ε,u}` is non-empty, so that the next clause is not vacuous. -/
  resolventSet_nonempty :
    (LinearPMap.resolventSet (solenoidalInductionSemigroup u hu hε).generator).Nonempty
  /-- "The resolvent of `L_{ε,u}` is compact": at every point `z` of the resolvent set. -/
  isCompactOperator_resolvent : ∀ (z : ℂ)
    (R : productSolenoidalSubspace →L[ℂ] productSolenoidalSubspace),
      LinearPMap.IsResolvent (solenoidalInductionSemigroup u hu hε).generator z R →
        IsCompactOperator R
  /-- "`e^{tL_{ε,u}}` is compact for every `t > 0`". -/
  isCompactOperator_semigroup : ∀ t : NNReal, 0 < t →
    IsCompactOperator ((solenoidalInductionSemigroup u hu hε).operator t)
  /-- `eq:compact-semigroup-spectral-mapping`:
  `σ(e^{tL_{ε,u}}) \ {0} = {e^{tλ} : λ ∈ σ(L_{ε,u})}` for `t > 0`. -/
  spectralMapping : ∀ t : NNReal, 0 < t →
    spectrum ℂ ((solenoidalInductionSemigroup u hu hε).operator t) \ {0} =
      (fun lam : ℂ ↦ Complex.exp (((t : ℝ) : ℂ) * lam)) ''
        LinearPMap.spectrum (solenoidalInductionSemigroup u hu hε).generator
  /-- `eq:semigroup-growth-rate` and the sentence after it: `t⁻¹ log ‖e^{tL_{ε,u}}‖` converges
  as `t → ∞`, to a real number, and `γ(u, ε)` is its limit. -/
  gamma_tendsto : ∃ L : ℝ, gamma u hu hε = (L : EReal) ∧
    Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log
      ‖(solenoidalInductionSemigroup u hu hε).operator (Real.toNNReal t)‖) atTop (𝓝 L)
  /-- `eq:growth-rate-spectral-bound`: `γ(u, ε) = sup {Re λ : λ ∈ σ(L_{ε,u})}`. -/
  gamma_eq_iSup : gamma u hu hε =
    ⨆ lam ∈ LinearPMap.spectrum (solenoidalInductionSemigroup u hu hε).generator,
      ((lam.re : ℝ) : EReal)
  /-- `0 ∈ σ(L_{ε,u})`, which the paper proves in the proof of the lemma (the mean of
  `L_{ε,u}B` vanishes, so `L_{ε,u}` is not surjective); in particular the supremum in
  `gamma_eq_iSup` is over a non-empty set. -/
  zero_mem_spectrum :
    (0 : ℂ) ∈ LinearPMap.spectrum (solenoidalInductionSemigroup u hu hε).generator
  /-- "The supremum is attained", at an eigenvalue (§1.1): some `λ ∈ σ(L_{ε,u})` with
  `Re λ = γ(u, ε)` has a non-zero eigenvector in `H² ∩ L²_σ`. -/
  exists_eigenvalue_re_eq_gamma :
    ∃ lam ∈ LinearPMap.spectrum (solenoidalInductionSemigroup u hu hε).generator,
      ((lam.re : ℝ) : EReal) = gamma u hu hε ∧
        ∃ x : (solenoidalInductionSemigroup u hu hε).generator.domain,
          (x : productSolenoidalSubspace) ≠ 0 ∧
            (solenoidalInductionSemigroup u hu hε).generator x =
              lam • (x : productSolenoidalSubspace)

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/-- **Lemma A.1 of the paper holds** (`lem:semigroup-spectral-growth`): for every
divergence-free axially independent velocity `u` and every `ε > 0`, every clause of
`SemigroupSpectralGrowth`.  The clauses are `generator_solenoidalInductionSemigroup`,
`productL2ToHMinus2_generator_solenoidalInductionSemigroup`,
`eq_solenoidalInductionSemigroup_of_generator_eq`,
`isAnalyticSemigroup_solenoidalInductionSemigroup`,
`exists_isResolvent_generator_solenoidalInductionSemigroup`,
`isCompactOperator_of_isResolvent_generator_solenoidalInductionSemigroup`,
`isCompactOperator_solenoidalInductionSemigroup`,
`spectrum_solenoidalInductionSemigroup_diff_zero`, `gamma_eq_lim`,
`gamma_eq_iSup_re_spectrum`, `zero_mem_spectrum_generator_solenoidalInductionSemigroup` and
`exists_eigenvalue_re_eq_gamma`. -/
theorem semigroupSpectralGrowth_holds : SemigroupSpectralGrowth u hu hε where
  generator_eq := generator_solenoidalInductionSemigroup u hu hε
  generator_curlForm := productL2ToHMinus2_generator_solenoidalInductionSemigroup u hu hε
  generator_unique := fun _ hS ↦ eq_solenoidalInductionSemigroup_of_generator_eq u hu hε hS
  analytic := isAnalyticSemigroup_solenoidalInductionSemigroup u hu hε
  resolventSet_nonempty := by
    obtain ⟨r, R, hR, -⟩ := exists_isResolvent_generator_solenoidalInductionSemigroup u hu hε
    exact ⟨_, R, hR⟩
  isCompactOperator_resolvent := fun _ _ hR ↦
    isCompactOperator_of_isResolvent_generator_solenoidalInductionSemigroup u hu hε hR
  isCompactOperator_semigroup := fun _ ht ↦
    isCompactOperator_solenoidalInductionSemigroup u hu hε ht
  spectralMapping := fun _ ht ↦ spectrum_solenoidalInductionSemigroup_diff_zero u hu hε ht
  gamma_tendsto := by
    obtain ⟨L, hL, -, -, hlim⟩ := gamma_eq_lim u hu hε
    refine ⟨L, hL, ?_⟩
    have hnorm : ∀ t : ℝ, ‖(literalInductionSemigroup u hu hε).operator (Real.toNNReal t)‖ =
        ‖(solenoidalInductionSemigroup u hu hε).operator (Real.toNNReal t)‖ := fun t ↦
      (solenoidalInductionSemigroup u hu hε).norm_congr solenoidalToLiteral _
    simpa only [hnorm] using hlim
  gamma_eq_iSup := gamma_eq_iSup_re_spectrum u hu hε
  zero_mem_spectrum := zero_mem_spectrum_generator_solenoidalInductionSemigroup u hu hε
  exists_eigenvalue_re_eq_gamma := exists_eigenvalue_re_eq_gamma u hu hε

end

end FastDynamo
