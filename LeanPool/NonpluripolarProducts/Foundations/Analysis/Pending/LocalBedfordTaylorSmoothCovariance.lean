/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity

/-!
# Covariance of smooth local products

Describes coordinate changes of Bedford–Taylor products for smooth potentials.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothCovariance

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalCurrentLebesgue ConstantFormProducts TopDegreeDensity ProductTestForms
  LocalBedfordTaylorSmoothDensity LocalBedfordTaylorSmoothProductDensity
  LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar

variable {n r k : ℕ} {A B : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}
variable (hdeg : r + k = n)

private def pairDensity (α : RealForm n (2 * k)) : formSpan n r →ₗ[ℝ] ℝ where
  toFun γ := topDensity (wedgeTo (by omega : 2 * r + 2 * k = 2 * n) γ α)
  map_add' γ γ' := by
    rw [Submodule.coe_add, wedgeTo_add_left]
    exact topDensity_add _ _
  map_smul' c γ := by
    rw [Submodule.coe_smul, wedgeTo_smul_left]
    exact topDensity_smul _ _

private theorem pairDensity_apply (α : RealForm n (2 * k)) (γ : formSpan n r) :
    pairDensity hdeg α γ =
      topDensity (wedgeTo (by omega : 2 * r + 2 * k = 2 * n) γ α) := rfl

private theorem pairDensity_nonneg {α : RealForm n (2 * k)} (hα : α ∈ spCone k)
    {γ : formSpan n r} (hγ : γ ∈ posCone n r) : 0 ≤ pairDensity hdeg α γ :=
  topDensity_nonneg_of_mem_spCone
    (wedgeTo_mem_spCone k r n hγ hα (by omega))

private theorem topDensity_wedgeTo_comp
    (L M : ComplexModel n →L[ℝ] ComplexModel n)
    (hML : M.comp L = ContinuousLinearMap.id ℝ _)
    (γ : RealForm n (2 * r)) (α : RealForm n (2 * k)) :
    topDensity (wedgeTo (by omega : 2 * r + 2 * k = 2 * n)
      γ (α.compContinuousLinearMap L)) =
      L.det * topDensity (wedgeTo (by omega : 2 * r + 2 * k = 2 * n)
        (γ.compContinuousLinearMap M) α) := by
  have hγ : γ = (γ.compContinuousLinearMap M).compContinuousLinearMap L := by
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← ContinuousLinearMap.comp_apply, hML, ContinuousLinearMap.id_apply]
  conv_lhs => rw [hγ]
  rw [← wedgeTo_compContinuousLinearMap]
  exact topDensity_compContinuousLinearMap _ L

private theorem continuousOn_pairDensity {α : ComplexModel n → RealForm n (2 * k)}
    (hαc : ContinuousOn α B) (γ : formSpan n r) :
    ContinuousOn (fun y => pairDensity hdeg (α y) γ) B := by
  have := ProductTestForms.realForm_finiteDimensional (n := n) (2 * k)
  exact ((topDensityLM n).comp
    (wedgeToBilin n (by omega : 2 * r + 2 * k = 2 * n)
      γ)).continuous_of_finiteDimensional.comp_continuousOn hαc

/-- The density `⟨γ ∧ α⟩⁺` on `B`, extended by `0`. -/
private def pairWeight (B : Opens (ComplexModel n)) (α : ComplexModel n → RealForm n (2 * k))
    (γ : formSpan n r) : ComplexModel n → ℝ≥0∞ :=
  (B : Set (ComplexModel n)).indicator fun y => ENNReal.ofReal (pairDensity hdeg (α y) γ)

private theorem measurable_pairWeight {α : ComplexModel n → RealForm n (2 * k)} (hαc :
    ContinuousOn α B)
    (γ : formSpan n r) : Measurable (pairWeight hdeg B α γ) := by
  have h := ENNReal.measurable_ofReal.comp
    (measurable_indicator_of_continuousOn (U := B) (continuousOn_pairDensity hdeg hαc γ))
  convert h using 1
  funext y
  by_cases hy : y ∈ (B : Set (ComplexModel n)) <;> simp [pairWeight, hy]

private theorem pairWeight_compl (α : ComplexModel n → RealForm n (2 * k)) (γ : formSpan n r) :
    volume.withDensity (pairWeight hdeg B α γ) ((B : Set (ComplexModel n))ᶜ) = 0 := by
  rw [withDensity_apply _ B.isOpen.measurableSet.compl]
  refine (setLIntegral_congr_fun B.isOpen.measurableSet.compl fun y hy => ?_).trans
    (lintegral_zero)
  exact indicator_of_notMem hy _

private theorem pairWeight_lt_top {α : ComplexModel n → RealForm n (2 * k)} (hαc : ContinuousOn α
    B)
    (γ : formSpan n r) (K : Set (ComplexModel n)) (hK : IsCompact K) (hKB : K ⊆ B) :
    volume.withDensity (pairWeight hdeg B α γ) K < ⊤ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((continuousOn_pairDensity hdeg hαc γ).mono
    hKB)
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ y in K, pairWeight hdeg B α γ y ≤ ∫⁻ _ in K, ENNReal.ofReal C :=
        setLIntegral_mono' hK.measurableSet fun y hy => by
          rw [pairWeight, indicator_of_mem (hKB hy)]
          have hyC : |pairDensity hdeg (α y) γ| ≤ C := by
            simpa only [Real.norm_eq_abs] using hC y hy
          exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hyC)
    _ = ENNReal.ofReal C * volume K := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

private theorem integral_pairWeight {α : ComplexModel n → RealForm n (2 * k)} (hαc : ContinuousOn
    α B)
    (hα : ∀ y ∈ B, α y ∈ spCone k) {γ : formSpan n r} (hγ : γ ∈ posCone n r)
    (φ : 𝓓(B, ℝ)) : ∫ y, φ y ∂volume.withDensity (pairWeight hdeg B α γ) = ∫ y,
      φ y * pairDensity hdeg (α y) γ := by
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_pairWeight hdeg hαc γ)
    (Eventually.of_forall fun y => by
      by_cases hy : y ∈ (B : Set (ComplexModel n))
      · rw [pairWeight, indicator_of_mem hy]; exact ENNReal.ofReal_lt_top
      · rw [pairWeight, indicator_of_notMem hy]; exact ENNReal.zero_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ (B : Set (ComplexModel n))
  · simp only [pairWeight, indicator_of_mem hy, ENNReal.toReal_ofReal (pairDensity_nonneg hdeg (hα
    y hy) hγ), smul_eq_mul]
    ring
  · simp [pairWeight, indicator_of_notMem hy, testFunction_eq_zero_of_notMem φ hy]

/-- **The pull-back of the current of a continuous semipositive `(1,1)`-form `α` is the current of
    `τ^* α`**:
if `T(γ)(φ) = ∫ φ ⟨γ ∧ α⟩ dλ` on `B`, then `(τ^* T)(γ)(φ) = ∫ φ(x) ⟨γ ∧ Dτ(x)^* α(τ x)⟩ dx`. -/
private theorem pullback_apply_of_positive_form (h : IsBiholomorphicPair A B τ σ)
    {T : LocalProductCurrent n B r}
    (hT : IsPositive T) {α : ComplexModel n → RealForm n (2 * k)} (hαc : ContinuousOn α B)
    (hα : ∀ y ∈ B, α y ∈ spCone k)
    (hTα : ∀ (γ : formSpan n r) (φ : 𝓓(B, ℝ)), T γ φ = ∫ y, φ y * pairDensity hdeg (α y) γ)
    (γ : formSpan n r) (φ : 𝓓(A, ℝ)) :
    pullback h hT γ φ =
      ∫ x, φ x * pairDensity hdeg ((α (τ x)).compContinuousLinearMap ((fderiv ℂ τ
        x).restrictScalars ℝ)) γ := by
  have hω : kahlerPower n r ∈ posCone n r :=
    formPower_mem_spCone isSemipositiveOneOne_kahlerForm r
  -- the trace measure is `⟨ω₀^r ∧ α⟩ λ|_B`
  have htr : hT.traceMeasure = volume.withDensity (pairWeight hdeg B α (kahlerPower n r)) :=
    eq_of_forall_testFunction_integral_eq hT.traceMeasure_compl (pairWeight_compl hdeg α _)
      (fun K hK hKB => hT.traceMeasure_lt_top hK hKB) (pairWeight_lt_top hdeg hαc _)
      fun φ => by rw [hT.integral_traceMeasure, hTα, integral_pairWeight hdeg hαc hα hω]
  -- the absolutely continuous density is `⟨· ∧ α⟩`
  have hac : ∀ᵐ y ∂(volume : Measure (ComplexModel n)), y ∈ B →
      ∀ γ, (acWeight hT y • densityForm hT y) γ = pairDensity hdeg (α y) γ := by
    refine ae_forall_eq_of_posCone (fun y => acWeight hT y • densityForm hT y) (fun y =>
      pairDensity hdeg (α y))
      fun γ hγ => ?_
    have hU := ae_eq_ofReal_acDensity hT hγ (measurable_pairWeight hdeg hαc γ) (pairWeight_compl
      hdeg α γ)
      (pairWeight_lt_top hdeg hαc γ) (fun φ => (integral_pairWeight hdeg hαc hα hγ φ).trans (hTα γ
        φ).symm)
      (Measure.MutuallySingular.zero_left) (zero_add _).symm
    filter_upwards [hU, ae_volume_acDensity_nonneg hT] with y h1 h2 hyB
    rw [pairWeight, indicator_of_mem hyB] at h1
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact ((ENNReal.ofReal_eq_ofReal_iff (pairDensity_nonneg hdeg (hα y hyB) hγ)
      (h2 γ hγ)).mp h1).symm
  have hrn : hT.traceMeasure.rnDeriv volume =ᵐ[volume] pairWeight hdeg B α (kahlerPower n r) := by
    rw [htr]
    exact Measure.rnDeriv_withDensity _ (measurable_pairWeight hdeg hαc _)
  -- the integral on `B`
  have step : ∫ y in B, φ (σ y) * densityForm hT y (pullSpan r (fderiv ℂ σ y) γ) ∂hT.traceMeasure =
      ∫ y in B, φ (σ y) * pairDensity hdeg (α y) (pullSpan r (fderiv ℂ σ y) γ) := by
    rw [htr, restrict_withDensity B.isOpen.measurableSet,
      integral_withDensity_eq_integral_toReal_smul (measurable_pairWeight hdeg hαc _)
        (Eventually.of_forall fun y => by
          by_cases hy : y ∈ (B : Set (ComplexModel n))
          · rw [pairWeight, indicator_of_mem hy]; exact ENNReal.ofReal_lt_top
          · rw [pairWeight, indicator_of_notMem hy]; exact ENNReal.zero_lt_top)]
    refine setIntegral_congr_ae B.isOpen.measurableSet ?_
    filter_upwards [hac, hrn] with y h1 h2 hyB
    have e := h1 hyB (pullSpan r (fderiv ℂ σ y) γ)
    simp only [LinearMap.smul_apply, smul_eq_mul] at e
    rw [← e, acWeight, h2, smul_eq_mul]
    ring
  -- the change of variables `y = τ x`
  have himg : τ '' (A : Set (ComplexModel n)) = B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact h.mapsTo hx
    · intro hy
      exact ⟨σ y, h.mapsTo_inv hy, h.right_inv y hy⟩
  have hderiv : ∀ x ∈ (A : Set (ComplexModel n)),
      HasFDerivWithinAt τ (fderiv ℝ τ x) (A : Set (ComplexModel n)) x := fun x hx =>
    (((differentiableAt_of_mem h hx).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  have hinj : InjOn τ (A : Set (ComplexModel n)) := fun x hx x' hx' hxx' => by
    rw [← h.left_inv x hx, ← h.left_inv x' hx', hxx']
  rw [pullback_apply h hT, step, ← himg,
    integral_image_eq_integral_abs_det_fderiv_smul volume A.isOpen.measurableSet hderiv hinj]
  conv_rhs => rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (A : Set (ComplexModel
    n)))
    (fun x hx => by rw [testFunction_eq_zero_of_notMem φ hx, zero_mul])]
  refine setIntegral_congr_fun A.isOpen.measurableSet fun x hx => ?_
  have hML : ((fderiv ℂ σ (τ x)).restrictScalars ℝ).comp ((fderiv ℂ τ x).restrictScalars ℝ) =
      ContinuousLinearMap.id ℝ _ := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact DFunLike.congr_fun (fderiv_inv_comp h hx) v
  simp only
  rw [h.left_inv x hx, pairDensity_apply hdeg, pairDensity_apply hdeg, coe_pullSpan,
    topDensity_wedgeTo_comp hdeg _ _ hML, fderiv_real_eq h hx, det_restrictScalars_eq_normSq,
    abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul]
  ring

/-- Full complementary-test covariance for a genuine smooth positive form. -/
theorem pullback_wedgeForm_apply (h : IsBiholomorphicPair A B τ σ)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α B)
    (hαp : ∀ y ∈ B, α y ∈ spCone k) (γ : formSpan n r) (φ : 𝓓(A, ℝ)) :
    pullback h (isPositive_wedgeForm hdeg isPositive_oneCurrent hα hαp) γ φ =
      ∫ x, φ x * topDensity (wedgeTo (by omega : 2 * r + 2 * k = 2 * n)
        γ ((α (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ))) := by
  exact pullback_apply_of_positive_form hdeg h _ hα.continuousOn hαp
    (wedgeForm_oneCurrent_apply hdeg hα
      (fun y hy => mem_formSpan_of_mem_spCone (hαp y hy))) γ φ

private theorem wedgeProd_positive : ∀ (q : ℕ) (β : Fin q → RealForm n 2),
    (∀ i, IsSemipositiveOneOne (β i)) → wedgeProd q β ∈ spCone q
  | 0, _, _ => unit_mem_spCone
  | q + 1, β, hβ => wedge_mem_spCone
      (wedgeProd_positive q (fun i => β i.castSucc) (fun i => hβ i.castSucc))
      (hβ (Fin.last q))

private theorem wedgeProd_comp (L : ComplexModel n →L[ℝ] ComplexModel n) :
    ∀ (q : ℕ) (β : Fin q → RealForm n 2),
      (wedgeProd q β).compContinuousLinearMap L =
        wedgeProd q (fun i => (β i).compContinuousLinearMap L)
  | 0, _ => by ext v; rfl
  | q + 1, β => by
    rw [wedgeProd_succ, wedgeProd_succ, coordinateWedge_compContinuousLinearMap,
      wedgeProd_comp L q]

variable {q : ℕ}

/-- The actual recursive smooth product is biholomorphically covariant in every degree. -/
theorem pullback_smooth_btProduct (hdegree : r + q = n)
    (h : IsBiholomorphicPair A B τ σ) {u : Fin q → ComplexModel n → ℝ}
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) B)
    (hup : ∀ i, PlurisubharmonicOn (fun z => (u i z : EReal)) B) :
    pullback h (isPositive_btProduct q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf hdegree) (isClosedAny_oneCurrentOf hdegree)
      (fun i => LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_of_isSmoothPshOn
        (isSmoothPshOn_of_psh (hu i) (hup i)))).1 =
      btProduct q r (fun i x => u i (τ x)) (oneCurrentOf (U := A) hdegree) := by
  have huA (i : Fin q) : ContDiffOn ℝ ∞ (fun x => u i (τ x)) A :=
    (hu i).comp (h.holo.restrict_scalars ℝ) h.mapsTo
  have hpA (i : Fin q) : PlurisubharmonicOn (fun x => (u i (τ x) : EReal)) A :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic A.isOpen
      (h.holo.differentiableOn (by simp)) h.mapsTo (hup i)
  have eB := btProduct_eq_wedgeForm q r u hu hup (oneCurrentOf hdegree)
    (isPositive_oneCurrentOf hdegree) (isClosedAny_oneCurrentOf hdegree)
  have eA := btProduct_eq_wedgeForm q r (fun i x => u i (τ x)) huA hpA
    (oneCurrentOf (U := A) hdegree) (isPositive_oneCurrentOf hdegree)
    (isClosedAny_oneCurrentOf hdegree)
  have eqw {U : Opens (ComplexModel n)}
      {α : ComplexModel n → RealForm n (2 * q)} (hα : ContDiffOn ℝ ∞ α U) :
      wedgeForm rfl (oneCurrentOf (U := U) hdegree) hα =
        wedgeForm hdegree (oneCurrent U) hα := by cases hdegree; rfl
  rw [eqw] at eB eA
  have hpos : ∀ y ∈ B, wedgeProd q (fun i => ddcForm (u i) y) ∈ spCone q :=
    fun y hy => wedgeProd_positive q _ (fun i =>
      isSemipositiveOneOne_smoothDDC (hu i) (hup i) hy)
  have ePB : pullback h (isPositive_btProduct q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf hdegree) (isClosedAny_oneCurrentOf hdegree)
      (fun i => LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_of_isSmoothPshOn
        (isSmoothPshOn_of_psh (hu i) (hup i)))).1 =
      pullback h (isPositive_wedgeForm hdegree isPositive_oneCurrent
        (contDiffOn_wedgeProd q (fun i => ddcForm (u i))
          (fun i => contDiffOn_ddcForm (hu i))) hpos) := by
    congr 1
  rw [ePB, eA]
  ext γ φ
  rw [pullback_wedgeForm_apply hdegree h _ hpos,
    wedgeForm_oneCurrent_apply hdegree
      (contDiffOn_wedgeProd q _ (fun i => contDiffOn_ddcForm (huA i)))
      (fun x hx => wedgeProd_mem_formSpan q _ (fun i =>
        ddcForm_mem_formSpan (huA i)
          (fun _ hz v => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn
            (huA i) (hpA i) hz v) x hx))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ A
  · rw [wedgeProd_comp]
    congr 3
    apply congrArg (wedgeProd q)
    funext i
    have ei := HolomorphicDDC.smoothDDC_comp A.isOpen B.isOpen h.holo (hu i)
      h.mapsTo hx
    rw [fderiv_real_eq h hx] at ei
    exact ei.symm
  · simp [LocalBedfordTaylorLocality.testFunction_eq_zero_of_notMem φ hx]

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothCovariance
