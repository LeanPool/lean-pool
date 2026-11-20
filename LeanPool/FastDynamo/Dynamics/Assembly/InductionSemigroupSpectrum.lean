/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Assembly.InductionMeanConservation
public import LeanPool.FastDynamo.Dynamics.Assembly.ProductInductionEnergy
public import LeanPool.FastDynamo.Dynamics.Assembly.SolenoidalGenerator
public import LeanPool.FastDynamo.Dynamics.HilleYosida.AnalyticGeneration
public import LeanPool.FastDynamo.Dynamics.SemigroupSpectralMapping
public import LeanPool.FastDynamo.Operator.ProductH2Compact

/-!
# Analyticity, compactness and spectrum of the induction semigroup

The analytic half of the paper's Lemma A.1 (`lem:semigroup-spectral-growth`) for
`solenoidalInductionSemigroup`, the semigroup `e^{tL_{ε,u}}` on `L²_σ` whose growth bound is
`gamma`:

* `isAnalyticSemigroup_solenoidalInductionSemigroup`: the semigroup is analytic of angle `π/4`.
  The product Hille–Yosida semigroup is analytic by the sector estimate
  `exists_productInduction_sectorial`, and analyticity passes to the closed invariant subspace
  `L²_σ`.
* `exists_isResolvent_generator_solenoidalInductionSemigroup`,
  `isCompactOperator_of_isResolvent_generator_solenoidalInductionSemigroup`: the generator has
  a compact resolvent, at every point of its resolvent set.  The resolvent on the real ray
  factors through the compact embedding `H² → L²`.
* `isCompactOperator_solenoidalInductionSemigroup`: `e^{tL_{ε,u}}` is compact for `t > 0`.
* `zero_mem_spectrum_generator_solenoidalInductionSemigroup`: `0 ∈ σ(L_{ε,u})`, by
  conservation of the mean.
* `spectrum_solenoidalInductionSemigroup_diff_zero`: the spectral mapping theorem
  `σ(e^{tL}) \ {0} = e^{tσ(L)}`.
* `gamma_eq_iSup_re_spectrum`, `exists_eigenvalue_re_eq_gamma`: `γ(u, ε)` is the spectral bound
  of `L_{ε,u}` and is attained at an eigenvalue.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/-- **Analyticity of the induction semigroup** (`lem:semigroup-spectral-growth`).  The semigroup
`solenoidalInductionSemigroup` is analytic of angle `π/4`: the Hille–Yosida semigroup of the
auxiliary induction operator on `L²` is analytic by the sector estimate on its numerical range
(`exists_productInduction_sectorial`), and an analytic semigroup restricts to an analytic
semigroup on a closed invariant subspace. -/
theorem isAnalyticSemigroup_solenoidalInductionSemigroup :
    IsAnalyticSemigroup (solenoidalInductionSemigroup u hu hε) (Real.pi / 4) := by
  obtain ⟨ω, hω⟩ := exists_productInduction_sectorial u hu hε
  exact (HilleYosidaRay.isAnalyticSemigroup_of_sectorial (productHilleYosidaRay u hu hε)
    (denseRange_productInductionOperator_embedding u ε) ω hω).restrict _
      isClosed_productSolenoidalSubspace _

/-- The generator of the induction semigroup on `L²_σ` has a compact resolvent on the real ray:
the resolvent of `exists_isResolvent_generator_solenoidalInductionSemigroup_eq` is the
restriction to `L²_σ` of the Hille–Yosida resolvent, which factors through the compact embedding
`H² → L²` (`isCompactOperator_productH2Embedding`). -/
theorem exists_isResolvent_generator_solenoidalInductionSemigroup :
    ∃ r : ℝ, ∃ R : productSolenoidalSubspace →L[ℂ] productSolenoidalSubspace,
      LinearPMap.IsResolvent (solenoidalInductionSemigroup u hu hε).generator r R ∧
        IsCompactOperator R := by
  obtain ⟨R, hR, hRx⟩ := exists_isResolvent_generator_solenoidalInductionSemigroup_eq u hu hε
    (‖transverseStretchingCoefficient u‖ + 1) (by linarith)
  refine ⟨_, R, hR, ?_⟩
  set hy := productHilleYosidaRay u hu hε
  set T := productH2Embedding.comp
    ((hy.resolvent.inv (((‖transverseStretchingCoefficient u‖ + 1 : ℝ)) : ℂ)).comp
      productSolenoidalSubspace.subtypeL)
  have hmem : ∀ x, T x ∈ productSolenoidalSubspace := fun x ↦
    stateResolvent_productHilleYosidaRay_mem_productSolenoidalSubspace u hu hε _
      (by linarith) x x.2
  have hfun : (R : productSolenoidalSubspace → productSolenoidalSubspace) =
      Set.codRestrict T productSolenoidalSubspace hmem :=
    funext fun x ↦ Subtype.ext (hRx x)
  rw [hfun]
  exact (isCompactOperator_productH2Embedding.comp_clm _).codRestrict hmem
    isClosed_productSolenoidalSubspace

/-- **The resolvent of the generator is compact at every resolvent point.**  A compact resolvent
at one point (`exists_isResolvent_generator_solenoidalInductionSemigroup`) makes every resolvent
compact, by the resolvent identity. -/
theorem isCompactOperator_of_isResolvent_generator_solenoidalInductionSemigroup {z : ℂ}
    {R : productSolenoidalSubspace →L[ℂ] productSolenoidalSubspace}
    (hR : LinearPMap.IsResolvent (solenoidalInductionSemigroup u hu hε).generator z R) :
    IsCompactOperator R := by
  obtain ⟨r, R₀, hR₀, hc⟩ := exists_isResolvent_generator_solenoidalInductionSemigroup u hu hε
  exact hR₀.isCompactOperator_of_isResolvent hc hR

/-- **Compactness of the semigroup** (`lem:semigroup-spectral-growth`): `e^{tL_{ε,u}}` is a
compact operator on `L²_σ` for every `t > 0`. -/
theorem isCompactOperator_solenoidalInductionSemigroup {t : NNReal} (ht : 0 < t) :
    IsCompactOperator ((solenoidalInductionSemigroup u hu hε).operator t) := by
  obtain ⟨r, R, hR, hc⟩ := exists_isResolvent_generator_solenoidalInductionSemigroup u hu hε
  exact (isAnalyticSemigroup_solenoidalInductionSemigroup u hu hε).isCompactOperator hR hc ht

/-- **`0 ∈ σ(L_{ε,u})`.**  Zero lies in the spectrum of the generator of the induction semigroup
on `L²_σ`: a resolvent at `0` would solve `-L y = c` for the solenoidal `H²` field `c` of unit
mean, whereas the induction action of a solenoidal `H²` field has zero mean
(`hasZeroMean_productInductionAction`). -/
theorem zero_mem_spectrum_generator_solenoidalInductionSemigroup :
    (0 : ℂ) ∈ LinearPMap.spectrum (solenoidalInductionSemigroup u hu hε).generator := by
  rintro ⟨R, hR⟩
  obtain ⟨c, hcdiv, hc1, -⟩ := exists_productSolenoidal_mean_eq_one
  have hx : productH2Embedding c ∈ productSolenoidalSubspace :=
    (productH2Embedding_mem_productSolenoidalSubspace_iff c).2 hcdiv
  obtain ⟨hdom, heq⟩ := hR.1 ⟨productH2Embedding c, hx⟩
  obtain ⟨B, hB⟩ := (mem_generator_solenoidalInductionSemigroup_domain_iff u hu hε _).1 hdom
  have hBdiv : productDivergenceFromH2 B = 0 :=
    (productH2Embedding_mem_productSolenoidalSubspace_iff B).1 (hB ▸ (R _).2)
  have hG := coe_generator_solenoidalInductionSemigroup u hu hε ⟨R ⟨productH2Embedding c, hx⟩, hdom⟩
    B hB
  have hmean := (hasZeroMean_iff _).1 (hasZeroMean_productInductionAction u hu ε B hBdiv) 0
  have h2 := congrArg (fun y : productSolenoidalSubspace ↦ (y : ProductC3L2)) heq
  simp only [zero_smul, zero_sub, Submodule.coe_neg] at h2
  have h3 := congrArg (productCoeffCLM 0 0 0) h2
  rw [hG, map_neg, hmean, neg_zero] at h3
  exact one_ne_zero (hc1.symm.trans h3.symm)

/-- **Spectral mapping theorem** (`eq:compact-semigroup-spectral-mapping`,
`lem:semigroup-spectral-growth`): for `t > 0`, the nonzero spectrum of `e^{tL_{ε,u}}` is
`e^{tσ(L_{ε,u})}`. -/
theorem spectrum_solenoidalInductionSemigroup_diff_zero {t : NNReal} (ht : 0 < t) :
    spectrum ℂ ((solenoidalInductionSemigroup u hu hε).operator t) \ {0} =
      (fun lam : ℂ ↦ Complex.exp (((t : ℝ) : ℂ) * lam)) ''
        LinearPMap.spectrum (solenoidalInductionSemigroup u hu hε).generator := by
  obtain ⟨r, R, hR, hc⟩ := exists_isResolvent_generator_solenoidalInductionSemigroup u hu hε
  exact (isAnalyticSemigroup_solenoidalInductionSemigroup u hu hε).spectrum_diff_zero hR hc ht

/-- **The growth rate is the spectral bound** (`eq:growth-rate-spectral-bound`,
`lem:semigroup-spectral-growth`): `γ(u, ε) = sup Re σ(L_{ε,u})`. -/
theorem gamma_eq_iSup_re_spectrum :
    gamma u hu hε = ⨆ lam ∈ LinearPMap.spectrum (solenoidalInductionSemigroup u hu hε).generator,
      ((lam.re : ℝ) : EReal) := by
  obtain ⟨r, R, hR, hc⟩ := exists_isResolvent_generator_solenoidalInductionSemigroup u hu hε
  rw [gamma, growthBound_literalInductionSemigroup]
  exact ((isAnalyticSemigroup_solenoidalInductionSemigroup u hu hε).growthBound_eq_iSup hR hc
    ⟨0, zero_mem_spectrum_generator_solenoidalInductionSemigroup u hu hε⟩).1

/-- **The growth rate is attained at an eigenvalue** (`lem:semigroup-spectral-growth`): some
eigenvalue `λ` of `L_{ε,u}` on `L²_σ` has `Re λ = γ(u, ε)`. -/
theorem exists_eigenvalue_re_eq_gamma :
    ∃ lam : ℂ, lam ∈ LinearPMap.spectrum (solenoidalInductionSemigroup u hu hε).generator ∧
      ((lam.re : ℝ) : EReal) = gamma u hu hε ∧
      ∃ x : (solenoidalInductionSemigroup u hu hε).generator.domain,
        (x : productSolenoidalSubspace) ≠ 0 ∧
        (solenoidalInductionSemigroup u hu hε).generator x =
          lam • (x : productSolenoidalSubspace) := by
  obtain ⟨r, R, hR, hc⟩ := exists_isResolvent_generator_solenoidalInductionSemigroup u hu hε
  rw [gamma, growthBound_literalInductionSemigroup]
  exact ((isAnalyticSemigroup_solenoidalInductionSemigroup u hu hε).growthBound_eq_iSup hR hc
    ⟨0, zero_mem_spectrum_generator_solenoidalInductionSemigroup u hu hε⟩).2

end

end FastDynamo
