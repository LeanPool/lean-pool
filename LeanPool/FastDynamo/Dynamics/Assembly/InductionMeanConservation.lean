/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRateLimit
public import LeanPool.FastDynamo.Finish.ZeroMean

/-!
# Conservation of the mean under the induction semigroup

The paper's growth rate `γ(u, ε)` (`eq:semigroup-growth-rate`) is the limit of
`t⁻¹ log ‖e^{t L_{ε,u}}‖`.  The spatial mean of a solenoidal field is conserved by the
induction equation, because the zeroth Fourier coefficient of `curl (u × B) + ε Δ B` vanishes
for every `B`; the semigroup on `L²_σ` therefore has norm at least one at every time, which makes
the growth rate a real number in `[0, ‖∇⊥ u‖_∞]`.

## Contents

* `hasZeroMean_productInductionAction`: the induction action of a solenoidal `H²` field has zero
  mean.
* `exists_productSolenoidal_mean_eq_one`: a solenoidal `H²` field of unit norm and unit mean.
* `one_le_norm_solenoidalInductionSemigroup`: `1 ≤ ‖e^{t L_{ε,u}}‖` for every `t`.
* `zero_le_gamma`, `gamma_eq_lim`: `γ(u, ε)` is a real number in `[0, ‖∇⊥ u‖_∞]` and the limit
  of `t⁻¹ log ‖e^{t L_{ε,u}}‖`, for every divergence-free `u` and every `ε > 0`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Topology

/-- The induction action of a solenoidal `H²` field has zero spatial mean: the zeroth Fourier
coefficient of the curl form `ε Δ B + curl (u × B)` vanishes, and on solenoidal fields the curl
form is the induction action (`productInductionAction_toHMinus2_eq_physical`). -/
theorem hasZeroMean_productInductionAction (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (ε : ℝ) (B : ProductC3H2)
    (hB : productDivergenceFromH2 B = 0) :
    HasZeroMean (productInductionAction u ε B) := by
  rw [hasZeroMean_iff]
  intro i
  have h := congrArg (fun F : ProductC3HMinus2 ↦ F i 0 0)
    (productInductionAction_toHMinus2_eq_physical u hu ε B hB)
  have hw : (productH2Weight 0 0 : ℂ) = 1 := by simp [productH2Weight]
  simp only [productL2ToHMinus2_apply, hw, div_one, productPhysicalInductionAction,
    add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, PiLp.add_apply, PiLp.smul_apply] at h
  rw [h]
  have hlap : productCoeffCLM 0 0 i (productLaplacianFromH2 B) = 0 := by
    rw [productCoeffCLM_productLaplacianFromH2]
    simp [productFrequencyEnergy]
  have e1 : productL2ToHMinus2 (productLaplacianFromH2 B) i 0 0 = 0 := by
    rw [productL2ToHMinus2_apply, hlap, zero_div]
  have e2 : productWeakCurl (productCrossWithVelocity u (productH2Embedding B)) i 0 0 = 0 := by
    fin_cases i <;> simp
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, e1, e2, smul_zero,
    add_zero]

/-- The constant field `e₀ = (1, 0, 0)` on the product torus. -/
private def constantField : ProductC3L2 :=
  Lp.const 2 productMeasure (EuclideanSpace.single (0 : Fin 3) (1 : ℂ))

/-- The zeroth Fourier monomial on the product torus is the constant function `1`. -/
private theorem productMonomialL2_zero_zero_ae :
    (productMonomialL2 0 0 : ProductTorus3 → ℂ) =ᵐ[productMeasure] fun _ ↦ 1 := by
  have hmono := scalarAxialLiftL2Fun_ae 0 (transverseMonomialL2 0)
  have htrans := (measurePreserving_fst
    (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving.ae_eq_comp
      (transverseMonomialL2_coe_ae 0)
  filter_upwards [hmono, htrans] with x hm ht
  change (scalarAxialLiftL2Fun 0 (transverseMonomialL2 0) : ProductTorus3 → ℂ) x = 1
  change (transverseMonomialL2 0 : TransverseTorus → ℂ) x.1 =
    UnitAddTorus.mFourier 0 x.1 at ht
  rw [hm, ht]
  simp [UnitAddTorus.mFourier_zero]

/-- The coordinates of the constant field `e₀` are the zeroth monomial and zero. -/
private theorem productCoordL2_constantField (i : Fin 3) :
    productCoordL2 i constantField = if i = 0 then productMonomialL2 0 0 else 0 := by
  apply Lp.ext
  have hcoord := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL constantField
  have hconst := Lp.coeFn_const (E := EuclideanSpace ℂ (Fin 3)) 2 productMeasure
    (EuclideanSpace.single (0 : Fin 3) (1 : ℂ))
  have hm := productMonomialL2_zero_zero_ae
  by_cases hi : i = 0
  · subst hi
    rw [ite_eq_left rfl]
    filter_upwards [hcoord, hconst, hm] with x hc hk hmx
    change ((EuclideanSpace.proj (𝕜 := ℂ) 0).compLpL 2 productMeasure constantField :
      ProductScalarL2) x = _
    rw [hc, hmx]
    have hk' : (constantField : ProductTorus3 → EuclideanSpace ℂ (Fin 3)) x =
        EuclideanSpace.single 0 1 := hk
    rw [hk']
    simp
  · rw [ite_eq_right hi]
    filter_upwards [hcoord, hconst, Lp.coeFn_zero (E := ℂ) 2 productMeasure] with x hc hk hz
    change ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 productMeasure constantField :
      ProductScalarL2) x = _
    rw [hc, hz]
    have hk' : (constantField : ProductTorus3 → EuclideanSpace ℂ (Fin 3)) x =
        EuclideanSpace.single 0 1 := hk
    rw [hk']
    simp [hi]

/-- The Fourier coefficients of `e₀` vanish except the zeroth coefficient of coordinate `0`. -/
private theorem productCoeffCLM_constantField (n : TransverseFrequency) (k : ℤ) (i : Fin 3) :
    productCoeffCLM n k i constantField = if n = 0 ∧ k = 0 ∧ i = 0 then 1 else 0 := by
  have h : productCoeffCLM n k i constantField =
      inner ℂ (productMonomialL2 n k) (productCoordL2 i constantField) := rfl
  rw [h, productCoordL2_constantField]
  by_cases hi : i = 0
  · rw [ite_eq_left hi]
    change inner ℂ (scalarAxialLiftL2 k (transverseMonomialL2 n))
      (scalarAxialLiftL2 0 (transverseMonomialL2 0)) = _
    rw [inner_scalarAxialLiftL2]
    have horth := (orthonormal_iff_ite.mp transverseScalarFourierBasis.orthonormal) n 0
    by_cases hk : k = 0 <;> by_cases hn : n = 0 <;> simp_all [transverseMonomialL2]
  · simp [hi]

/-- The constant field `e₀` has unit norm, the torus having unit volume. -/
private theorem norm_constantField : ‖constantField‖ = 1 := by
  have h := Lp.norm_const (p := 2) (μ := productMeasure)
    (EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) (by norm_num)
  rw [constantField, h]
  simp

/-- The pair `(e₀, Fourier coefficients of e₀)` is an element of the product `H²` graph. -/
private theorem constantField_mem : (constantField, productC3FourierAnalysis constantField) ∈
    productH2Submodule := by
  rw [mem_productH2Submodule_iff]
  intro n k i
  rw [productC3FourierAnalysis_apply, productCoeffCLM_constantField]
  by_cases h : n = 0 ∧ k = 0 ∧ i = 0
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp [productH2Weight]
  · simp [h]

/-- There is a solenoidal `H²` field of unit `L²` norm and unit mean: the constant field
`(1, 0, 0)` on the torus of unit volume, whose only non-zero Fourier coefficient is the zeroth
one. -/
theorem exists_productSolenoidal_mean_eq_one :
    ∃ c : ProductC3H2, productDivergenceFromH2 c = 0 ∧
      productCoeffCLM 0 0 0 (productH2Embedding c) = 1 ∧ ‖productH2Embedding c‖ = 1 := by
  refine ⟨⟨(constantField, productC3FourierAnalysis constantField), constantField_mem⟩, ?_,
    ?_, norm_constantField⟩
  · rw [productDivergenceFromH2_eq_zero_iff]
    intro n k
    simp only [productH2Embedding_apply, productCoeffCLM_constantField]
    by_cases h : n = 0 ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have hz : ∀ i : Fin 3, ¬ (n = 0 ∧ k = 0 ∧ i = 0) := fun i hi ↦ h ⟨hi.1, hi.2.1⟩
      simp only [hz, ite_false, mul_zero, Finset.sum_const_zero, add_zero]
  · simp [productCoeffCLM_constantField]

/-- The zeroth Fourier coefficient of the first coordinate is bounded by the `L²` norm. -/
private theorem norm_productCoeffCLM_zero_le (V : ProductC3L2) :
    ‖productCoeffCLM 0 0 0 V‖ ≤ ‖V‖ := by
  have hproj : ‖EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
      simpa using PiLp.norm_apply_le x 0
  have hcoord : ‖productCoordL2 (0 : Fin 3) V‖ ≤ ‖V‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        ((ContinuousLinearMap.norm_compLpL_le _).trans hproj) (norm_nonneg _))).trans_eq (one_mul _)
  have hmono : ‖productMonomialL2 0 0‖ = 1 := by
    change ‖scalarAxialLiftL2 0 (transverseMonomialL2 0)‖ = 1
    rw [LinearIsometry.norm_map]
    exact transverseScalarFourierBasis.orthonormal.1 0
  refine ((innerSL ℂ (productMonomialL2 0 0)).le_opNorm _).trans ?_
  rw [innerSL_apply_norm, hmono, one_mul]
  exact hcoord

section Semigroup

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/-- **The induction semigroup on `L²_σ` never contracts below one**: `1 ≤ ‖e^{t L_{ε,u}}‖`
for every `t ≥ 0`.  The spatial mean of a solenoidal field is conserved
(`hasZeroMean_productInductionAction`), so the orbit of the constant field `(1, 0, 0)`, of unit
norm and unit mean, keeps its mean, and a field of mean one has norm at least one. -/
theorem one_le_norm_solenoidalInductionSemigroup (t : NNReal) :
    1 ≤ ‖(solenoidalInductionSemigroup u hu hε).operator t‖ := by
  obtain ⟨c, hdiv, hmean, hnorm⟩ := exists_productSolenoidal_mean_eq_one
  have hmem : productH2Embedding c ∈ productSolenoidalSubspace :=
    (mem_productSolenoidalSubspace_iff _).2 ((productDivergenceFromH2_eq_zero_iff c).1 hdiv)
  set R := productInductionRealization u hu hε
  let g : ℝ → ℂ := fun s ↦
    productCoeffCLM 0 0 0 (productInductionSemigroup u hu hε (Real.toNNReal s)
      (productH2Embedding c))
  have hgcont : Continuous g :=
    (productCoeffCLM 0 0 0).continuous.comp
      (((productInductionSemigroup u hu hε).orbit_continuous _).comp continuous_real_toNNReal)
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) (t : ℝ), HasDerivWithinAt g 0 (Set.Ici s) s := by
    intro s hs
    have h0 : (0 : ℝ) ≤ s := hs.1
    have hs' := R.domainOrbit_isForwardStrongSolution c s h0
    have hd := (HasFDerivAt.comp_hasDerivWithinAt s
      (ContinuousLinearMap.hasFDerivAt ((productCoeffCLM 0 0 0).restrictScalars ℝ)) hs').mono
      (Set.Ici_subset_Ici.2 h0)
    have hz : productCoeffCLM 0 0 0
        ((productInductionOperator u ε).op (R.domainOrbit c s)) = 0 := by
      have hB : productDivergenceFromH2 (R.domainOrbit c s) = 0 :=
        (productDivergenceFromH2_eq_zero_iff _).2
          ((mem_productSolenoidalSubspace_iff _).1
            (productInductionRealization_domainOrbit_mem_productSolenoidalSubspace u hu hε c
              hmem h0))
      exact (hasZeroMean_iff _).1 (hasZeroMean_productInductionAction u hu ε _ hB) 0
    rw [← hz]
    refine hd.congr (fun y hy ↦ ?_) ?_
    · have hy0 : (0 : ℝ) ≤ y := h0.trans hy
      exact congrArg (productCoeffCLM 0 0 0) (R.semigroup_eq_embedding_domainOrbit c y hy0)
    · exact congrArg (productCoeffCLM 0 0 0) (R.semigroup_eq_embedding_domainOrbit c s h0)
  have hconst := constant_of_has_deriv_right_zero hgcont.continuousOn hderiv (t : ℝ)
    ⟨t.2, le_rfl⟩
  have hg0 : g 0 = 1 := by
    simp only [g, Real.toNNReal_zero, StronglyContinuousSemigroup.apply_zero]
    exact hmean
  have hgt : g (t : ℝ) = productCoeffCLM 0 0 0
      (productInductionSemigroup u hu hε t (productH2Embedding c)) := by
    simp only [g, Real.toNNReal_coe]
  have h1 : 1 ≤ ‖productInductionSemigroup u hu hε t (productH2Embedding c)‖ := by
    refine le_trans ?_ (norm_productCoeffCLM_zero_le _)
    rw [← hgt, hconst, hg0, norm_one]
  have hx : ‖(⟨productH2Embedding c, hmem⟩ : productSolenoidalSubspace)‖ = 1 := hnorm
  have h2 := ((solenoidalInductionSemigroup u hu hε).operator t).le_opNorm
    (⟨productH2Embedding c, hmem⟩ : productSolenoidalSubspace)
  rw [hx, mul_one] at h2
  exact h1.trans h2

/-- **The paper's growth rate is a real number in `[0, ‖∇⊥ u‖_∞]` and a limit**
(`eq:semigroup-growth-rate`), for every divergence-free velocity `u` and every `ε > 0`: there is
`L ∈ ℝ` with `0 ≤ L ≤ ‖∇⊥ u‖_∞`, `γ(u, ε) = L`, and
`t⁻¹ log ‖e^{t L_{ε,u}}‖ → L` as `t → ∞`.  The lower bound `1 ≤ ‖e^{tL}‖`
(`one_le_norm_solenoidalInductionSemigroup`) excludes the value `−∞` (`gamma_ne_bot_iff`), so
`gamma_tendsto_real` applies; the upper bound is `gamma_le_stretching`. -/
theorem gamma_eq_lim :
    ∃ L : ℝ, gamma u hu hε = (L : EReal) ∧ 0 ≤ L ∧ L ≤ ‖transverseStretchingCoefficient u‖ ∧
      Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log
        ‖(literalInductionSemigroup u hu hε).operator (Real.toNNReal t)‖) atTop (𝓝 L) := by
  have hone : ∀ t : NNReal, 1 ≤ ‖(literalInductionSemigroup u hu hε).operator t‖ := fun t ↦ by
    rw [literalInductionSemigroup,
      (solenoidalInductionSemigroup u hu hε).norm_congr solenoidalToLiteral t]
    exact one_le_norm_solenoidalInductionSemigroup u hu hε t
  have hne : gamma u hu hε ≠ ⊥ :=
    (gamma_ne_bot_iff u hu hε).2 ⟨0, fun t _ ↦ by simpa using hone t⟩
  obtain ⟨L, hgamma, hlim⟩ := gamma_tendsto_real u hu hε hne
  refine ⟨L, hgamma, ?_, ?_, hlim⟩
  · refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact mul_nonneg (inv_nonneg.2 ht) (Real.log_nonneg (hone _))
  · have h := gamma_le_stretching u hu hε
    rw [hgamma] at h
    exact EReal.coe_le_coe_iff.1 h

/-- **`0 ≤ γ(u, ε)`** for every divergence-free velocity `u` and every `ε > 0`: the induction
semigroup on `L²_σ` has norm at least one (`gamma_eq_lim`). -/
theorem zero_le_gamma : (0 : EReal) ≤ gamma u hu hε := by
  obtain ⟨L, hgamma, hL, -⟩ := gamma_eq_lim u hu hε
  rw [hgamma]
  exact_mod_cast hL

end Semigroup

end

end FastDynamo
