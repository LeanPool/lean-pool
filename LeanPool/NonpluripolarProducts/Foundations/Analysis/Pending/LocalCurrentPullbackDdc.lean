/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConstantFormProducts

/-!
# Naturality of `dd^c` under biholomorphisms: `τ^*(dd^c w) = dd^c(w ∘ τ)`

Blueprint `ana:current-pullback-ddc` (`blueprint/src/analytic.tex`; TN.5, toward
    `ana:volume-semicontinuity`, route item 2:
the chart readings of `θ + dd^c u` are related by the pull-back of
    `Pending.LocalCurrentPullback`). [Boucksom, Lemma 4.2](
https://arxiv.org/pdf/math/0201031#page=12) supplies context for transporting integrable
forms and the absolutely continuous part of a current. Smooth `dd^c` naturality is the
calculation preceding [Demailly, Theorem I.5.11](
https://www-fourier.univ-grenoble-alpes.fr/~demailly/source_files/analgeom/agbook.pdf#page=40).
The Lean proof passes from the smooth identity to locally bounded PSH potentials
under a biholomorphism using Bedford–Taylor convergence.

For `τ : A → B` biholomorphic with inverse `σ` (`BedfordTaylor.IsBiholomorphicPair A B τ σ`),
    `n = m + 1`:

* `ae_forall_eq_of_posCone`: two families of linear functionals on `Λ_q` agreeing a.e. on each
    strongly positive form agree
  a.e. on all of `Λ_q`;
* `formDensity`, **`ddcMul_oneCurrent_apply`**: for `g` smooth on `U`, `dd^c g = dd^c(g [1])` is
    the current of the form
  `dd^c g`, `(dd^c g)(γ)(φ) = ∫ φ ⟨γ ∧ dd^c g⟩ dλ` (TN3's `ddcMul_eq_ddcWedge`,
    `smoothDDC_eq_sum_hessFun`);
* **`pullback_apply_of_form`**: the pull-back of the current of a continuous semipositive
    `(1,1)`-form `α` on `B` is the current
  of `x ↦ Dτ(x)^* α(τ x)` (through `ae_eq_ofReal_acDensity`: the current is absolutely continuous
    with density `⟨· ∧ α⟩`,
  then the change of variables);
* **`pullback_ddcMul_of_isSmoothPshOn`**: `τ^*(dd^c g) = dd^c(g ∘ τ)` for `g` smooth psh on `B`
    (`smoothDDC_comp`);
* `preOpen`, `isBiholomorphicPair_preOpen`, **`pullback_restrict`** (pull-back commutes with
    restriction to `V ⊆ B`);
* `pbCoeffFun`, `pullback_apply_eq_sum_mulBorel` (`⟨τ^* T, φ γ⟩ = ∑ᵢ (a_i T)(b_i)(χ)` with
    continuous `a_i` on `B`),
  **`weakTendsto_pullback`** (the pull-back is weakly continuous, by TN3's `weakTendsto_mulBorel`);
* `weakTendsto_ddcMul_oneCurrent` (`dd^c f_j → dd^c w` weakly along decreasing locally bounded psh
    `f_j ↓ w`; dominated
  convergence), `isLocallyBoundedPshOn_comp`, `restrict_oneCurrent`;
* **`pullback_ddcMul`**: for `w` locally bounded psh on `B`, `τ^*(dd^c w) = dd^c(w ∘ τ)` (smooth
    decreasing approximation on
  a relatively compact `V ⊆ B` containing `τ(supp φ)`,
    `HolomorphicPullback.exists_decreasingMollifierApproximation`).

Not here: unbounded psh `w` (TN3's `ddcMul` is the Bedford--Taylor product of a locally bounded
    potential).

Sorry-free.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms TopDegreeDensity LocalProductCurrents
    LocalCurrentLebesgue
  LocalBedfordTaylorLocality LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
    LocalBedfordTaylorCollar
  LocalCurrentPullback BedfordTaylor
  ConstantFormProducts
    LocalBedfordTaylorContinuity

attribute [local instance] addCommGroupFormSpan

/-! ### Currents given by a continuous `(1,1)`-form, and `dd^c` of a smooth function -/

section FormCurrents

variable {m : ℕ}

/-- The pairing `γ ↦ ⟨γ ∧ α⟩` of `Λ_m` with a fixed two-form `α`, as a linear functional. -/
def formDensity (α : RealForm (m + 1) 2) : formSpan (m + 1) m →ₗ[ℝ] ℝ where
  toFun γ := topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α)
  map_add' γ γ' := by
    rw [Submodule.coe_add, coordinateWedge_add_left]
    exact topDensity_add _ _
  map_smul' c γ := by
    rw [Submodule.coe_smul, coordinateWedge_smul_left]
    exact topDensity_smul _ _

theorem formDensity_apply (α : RealForm (m + 1) 2) (γ : formSpan (m + 1) m) :
    formDensity α γ = topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α) :=
  rfl

theorem formDensity_nonneg {α : RealForm (m + 1) 2} (hα : IsSemipositiveOneOne α)
    {γ : formSpan (m + 1) m}
    (hγ : γ ∈ posCone (m + 1) m) : 0 ≤ formDensity α γ :=
  topDensity_nonneg_of_mem_spCone (wedge_mem_spCone hγ hα)

/-- **`dd^c g` for `g` smooth on `U` is the current of the form `dd^c g`**:
`(dd^c g)(γ)(φ) = ∫ φ ⟨γ ∧ dd^c g⟩ dλ`. -/
theorem ddcMul_oneCurrent_apply {U : Opens (ComplexModel (m + 1))} {g : ComplexModel (m + 1) → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) :
    ddcMul (oneCurrent U) g γ φ = ∫ x, φ x * formDensity (smoothDDC g x) γ := by
  have hc : IsClosedCurrent (oneCurrent U) := isClosedAny_oneCurrent (U := U)
  rw [ddcMul_eq_ddcWedge isPositive_oneCurrent hc hg, ddcWedge_apply]
  simp only [oneCurrent_apply, mulSmoothOnCLM_apply, coe_wedgeLM_apply]
  have hpt : ∀ x, φ x * formDensity (smoothDDC g x) γ = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      (topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) (coeffForm a b)) *
        (φ x * hessFun a b g x)) := by
    intro x
    by_cases hx : x ∈ U
    · rw [formDensity_apply, ← wedgeDensity_apply,
      smoothDDC_eq_sum_hessFun hg hx,
        map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, smul_eq_mul, wedgeDensity_apply]
      ring
    · simp [testFunction_eq_zero_of_notMem φ hx]
  simp_rw [hpt]
  have hint : ∀ a b, Integrable fun x => φ x * hessFun a b g x := fun a b =>
    (mulSmoothOnCLM (contDiffOn_hessFun hg a b) φ).continuous.integrable_of_hasCompactSupport
      (mulSmoothOnCLM (contDiffOn_hessFun hg a b) φ).hasCompactSupport
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ((hint a b).const_mul
    _).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => ((hint a b).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_const_mul]

end FormCurrents

/-! ### The pull-back of the current of a continuous semipositive form -/

section PullbackForm

variable {n r k : ℕ} {A B : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}
variable (hdeg : r + k = n)

/-- The top-degree density pairing of complementary forms. -/
def pairDensity (α : RealForm n (2 * k)) : formSpan n r →ₗ[ℝ] ℝ where
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

/-- **The pull-back of the current of a continuous strongly positive form `α` is the current of
    `τ^* α`**:
if `T(γ)(φ) = ∫ φ ⟨γ ∧ α⟩ dλ` on `B`, then `(τ^* T)(γ)(φ) = ∫ φ(x) ⟨γ ∧ Dτ(x)^* α(τ x)⟩ dx`. -/
theorem pullback_apply_of_positive_form (h : IsBiholomorphicPair A B τ σ)
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

end PullbackForm

section TwoForm

variable {m : ℕ} {A B : Opens (ComplexModel (m + 1))} {τ σ : ComplexModel (m + 1)
    → ComplexModel (m + 1)}

/-- **The pull-back of the current of a continuous semipositive `(1,1)`-form `α` is the current of
    `τ^* α`**:
if `T(γ)(φ) = ∫ φ ⟨γ ∧ α⟩ dλ` on `B`, then `(τ^* T)(γ)(φ) = ∫ φ(x) ⟨γ ∧ Dτ(x)^* α(τ x)⟩ dx`. -/
theorem pullback_apply_of_form (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent (m + 1)
    B m}
    (hT : IsPositive T) {α : ComplexModel (m + 1) → RealForm (m + 1) 2} (hαc : ContinuousOn α B)
    (hα : ∀ y ∈ B, IsSemipositiveOneOne (α y))
    (hTα : ∀ (γ : formSpan (m + 1) m) (φ : 𝓓(B, ℝ)), T γ φ = ∫ y, φ y * formDensity (α y) γ)
    (γ : formSpan (m + 1) m) (φ : 𝓓(A, ℝ)) :
    pullback h hT γ φ =
      ∫ x, φ x * formDensity ((α (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars
        ℝ)) γ := by
  exact pullback_apply_of_positive_form (k := 1) rfl h hT hαc
    (fun y hy ↦ mem_spCone_one (hα y hy)) hTα γ φ

end TwoForm

/-! ### Smooth psh functions -/

section Smooth

/-- A smooth psh function is locally bounded psh. -/
theorem isLocallyBoundedPshOn_of_isSmoothPshOn {n : ℕ} {U : Opens (ComplexModel n)} {g :
    ComplexModel n → ℝ}
    (hg : IsSmoothPshOn U g) : IsLocallyBoundedPshOn U g := by
  refine ⟨hg.2.1, fun z hz => ?_⟩
  obtain ⟨K, hK, hzK, hKU⟩ := exists_compact_subset U.isOpen hz
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.1.continuousOn.mono hKU)
  refine ⟨⟨interior K, isOpen_interior⟩, hzK, fun w hw => hKU (interior_subset hw), C,
    fun w hw => ?_⟩
  simpa [Real.norm_eq_abs] using hC w (interior_subset hw)

variable {m : ℕ} {A B : Opens (ComplexModel (m + 1))} {τ σ : ComplexModel (m + 1)
    → ComplexModel (m + 1)}

theorem isPositive_ddcMul_oneCurrent {U : Opens (ComplexModel (m + 1))} {g : ComplexModel (m + 1)
    → ℝ}
    (hg : IsLocallyBoundedPshOn U g) : IsPositive (ddcMul (oneCurrent U) g) :=
  (isPositive_ddcMul isPositive_oneCurrent (isClosedAny_oneCurrent (U := U)) hg).1

/-- **Naturality of `dd^c` for smooth psh functions**: `τ^*(dd^c g) = dd^c(g ∘ τ)`. -/
theorem pullback_ddcMul_of_isSmoothPshOn (h : IsBiholomorphicPair A B τ σ) {g : ComplexModel (m +
    1) → ℝ}
    (hg : IsSmoothPshOn B g) :
    pullback h (isPositive_ddcMul_oneCurrent (isLocallyBoundedPshOn_of_isSmoothPshOn hg)) =
      ddcMul (oneCurrent A) (fun x => g (τ x)) := by
  have hgA : ContDiffOn ℝ ∞ (fun x => g (τ x)) A := hg.1.comp (h.holo.restrict_scalars ℝ) h.mapsTo
  ext γ φ
  rw [pullback_apply_of_form h _ (contDiffOn_ddcForm hg.1).continuousOn
      (fun y hy => isSemipositiveOneOne_smoothDDC hg.1 hg.2.1 hy) (ddcMul_oneCurrent_apply hg.1),
    ddcMul_oneCurrent_apply hgA]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ (A : Set (ComplexModel (m + 1)))
  · simp only
    rw [HolomorphicDDC.smoothDDC_comp A.isOpen B.isOpen h.holo hg.1 h.mapsTo hx,
      fderiv_real_eq h hx]
  · simp [testFunction_eq_zero_of_notMem φ hx]

end Smooth

/-! ### Restriction and weak continuity of the pull-back -/

section Restrict

variable {n q : ℕ} {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}

/-- The part `A ∩ τ⁻¹(V)` of `A` mapped into an open set `V`. -/
def preOpen (h : IsBiholomorphicPair A B τ σ) (V : Opens (ComplexModel n)) : Opens (ComplexModel
    n) :=
  ⟨A ∩ τ ⁻¹' V, h.holo.continuousOn.isOpen_inter_preimage A.isOpen V.isOpen⟩

theorem preOpen_le (h : IsBiholomorphicPair A B τ σ) (V : Opens (ComplexModel n))
    : preOpen h V ≤ A :=
  fun _ hx => hx.1

theorem mem_preOpen (h : IsBiholomorphicPair A B τ σ) {V : Opens (ComplexModel n)} {x :
    ComplexModel n} :
    x ∈ preOpen h V ↔ x ∈ A ∧ τ x ∈ V :=
  Iff.rfl

/-- `τ : A ∩ τ⁻¹(V) → V` is again a biholomorphism, with inverse `σ`. -/
theorem isBiholomorphicPair_preOpen (h : IsBiholomorphicPair A B τ σ) {V : Opens (ComplexModel n)}
    (hVB : V ≤ B) :
    IsBiholomorphicPair (preOpen h V) V τ σ where
  holo := h.holo.mono inter_subset_left
  holo_inv := h.holo_inv.mono hVB
  mapsTo := fun _ hx => hx.2
  mapsTo_inv := fun y hy => ⟨h.mapsTo_inv (hVB hy), by
    change τ (σ y) ∈ V
    rw [h.right_inv y (hVB hy)]
    exact hy⟩
  left_inv := fun x hx => h.left_inv x hx.1
  right_inv := fun y hy => h.right_inv y (hVB hy)

variable {T : LocalProductCurrent n B q}

/-- **The pull-back commutes with restriction**: `τ'^*(T|_V) = (τ^* T)|_{A ∩ τ⁻¹(V)}`. -/
theorem pullback_restrict (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    {V : Opens (ComplexModel n)}
    (hVB : V ≤ B) :
    pullback (isBiholomorphicPair_preOpen h hVB) (isPositive_restrict hT hVB) =
      restrict (preOpen_le h V) (pullback h hT) := by
  ext γ φ
  rw [LocalBedfordTaylorLocality.restrict_apply, pullback_apply, pullback_apply,
    traceMeasure_restrict hT hVB,
    Measure.restrict_restrict_of_subset subset_rfl]
  have e1 : ∫ y in V, φ (σ y) * densityForm (isPositive_restrict hT hVB) y (pullSpan q (fderiv ℂ σ
    y) γ)
        ∂hT.traceMeasure =
      ∫ y in V, φ (σ y) * densityForm hT y (pullSpan q (fderiv ℂ σ y) γ) ∂hT.traceMeasure := by
    have h' := ae_densityForm_restrict_eq hT hVB
    rw [traceMeasure_restrict hT hVB] at h'
    refine integral_congr_ae ?_
    filter_upwards [h'] with y hy
    rw [hy]
  rw [e1]
  have hφ : (extTest (preOpen_le h V) φ : ComplexModel n → ℝ) = (φ : ComplexModel n → ℝ) :=
    funext (extTest_apply (preOpen_le h V) φ)
  rw [hφ]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero B.isOpen.measurableSet
    (hVB : (V : Set (ComplexModel n)) ⊆ B) fun y hy => ?_).symm
  have hσ : σ y ∉ preOpen h V := fun hm => hy.2 (by rw [← h.right_inv y hy.1]; exact hm.2)
  rw [testFunction_eq_zero_of_notMem φ hσ, zero_mul]

end Restrict

section Weak

variable {n q : ℕ} {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}

/-- A test function on `B` equal to `1` on a compact subset of `B`. -/
theorem exists_testFunction_eq_one {K : Set (ComplexModel n)} (hK : IsCompact K) (hKB : K ⊆ B) :
    ∃ χ : 𝓓(B, ℝ), ∀ x ∈ K, χ x = 1 := by
  obtain ⟨V, hVo, hKV, hVcl, hVc⟩ := exists_open_between_and_isCompact_closure hK B.isOpen hKB
  obtain ⟨χ, hχ, hχ1, hχV, -⟩ := LocalBedfordTaylorMass.exists_cutoff_unit hK hVo hKV
  have hχc : HasCompactSupport χ := hVc.of_isClosed_subset (isClosed_tsupport χ)
    (hχV.trans subset_closure)
  exact ⟨⟨χ, hχ, hχc, hχV.trans (subset_closure.trans hVcl)⟩, fun x hx => hχ1 x hx⟩

/-- The coefficient functions `y ↦ φ(σ y) (Dσ(y)^* γ)_i` of the pulled-back test form, on `B`,
    extended by `0`. -/
def pbCoeffFun (B : Opens (ComplexModel n)) (σ : ComplexModel n → ComplexModel n)
    (γ : formSpan n q)
    (φ : 𝓓(A, ℝ)) (i : Fin (Module.finrank ℝ (formSpan n q))) : ComplexModel n → ℝ :=
  (B : Set (ComplexModel n)).indicator fun y => φ (σ y) * (formBasis n q).repr (pullSpan q (fderiv
    ℂ σ y) γ) i

theorem continuousOn_pbCoeffFun (h : IsBiholomorphicPair A B τ σ) (γ : formSpan n q) (φ : 𝓓(A, ℝ))
    (i : Fin (Module.finrank ℝ (formSpan n q))) : ContinuousOn (pbCoeffFun B σ γ φ i) B := by
  have hd : ContinuousOn (fderiv ℂ σ) B :=
    h.holo_inv.continuousOn_fderiv_of_isOpen B.isOpen (ENat.natCast_le_of_coe_top_le_withTop
      le_rfl 1)
  refine ((φ.continuous.comp_continuousOn h.holo_inv.continuousOn).mul
    ((continuous_repr_pullSpan_apply γ i).comp_continuousOn hd)).congr fun y hy => ?_
  simp only [pbCoeffFun, indicator_of_mem hy, Pi.mul_apply, Function.comp_apply]

theorem measurable_pbCoeffFun (h : IsBiholomorphicPair A B τ σ) (γ : formSpan n q) (φ : 𝓓(A, ℝ))
    (i : Fin (Module.finrank ℝ (formSpan n q))) : Measurable (pbCoeffFun B σ γ φ i) := by
  have := measurable_indicator_of_continuousOn (U := B) (continuousOn_pbCoeffFun h γ φ i)
  convert this using 1
  funext y
  by_cases hy : y ∈ (B : Set (ComplexModel n)) <;> simp [pbCoeffFun, hy]

theorem isLocallyBoundedOn_pbCoeffFun (h : IsBiholomorphicPair A B τ σ) (γ : formSpan n q)
    (φ : 𝓓(A, ℝ))
    (i : Fin (Module.finrank ℝ (formSpan n q))) : IsLocallyBoundedOn (pbCoeffFun B σ γ φ i) B := by
  have := isLocallyBoundedOn_indicator_of_continuousOn (U := B) (continuousOn_pbCoeffFun h γ φ i)
  intro K hK hKB
  obtain ⟨M, hM⟩ := this K hK hKB
  exact ⟨M, fun x hx => by simpa [indicator_of_mem (hKB hx)] using hM x hx⟩

variable {T : LocalProductCurrent n B q}

/-- **The pull-back as a finite sum of values of `T`**: with a test function `χ` on `B` equal to
    `1` on `τ(supp φ)`,
`⟨τ^* T, φ γ⟩ = ∑ᵢ (a_i T)(b_i)(χ)`, `a_i(y) = φ(σ y) (Dσ(y)^* γ)_i`, `(b_i)` the basis of `Λ_q`.
-/
theorem pullback_apply_eq_sum_mulBorel (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q)
    (φ : 𝓓(A, ℝ)) {χ : 𝓓(B, ℝ)} (hχ : ∀ x ∈ τ '' tsupport φ, χ x = 1) :
    pullback h hT γ φ = ∑ i, mulBorel T (pbCoeffFun B σ γ φ i) (formBasis n q i) χ := by
  simp only [mulBorel_apply hT (measurable_pbCoeffFun h γ φ _) (isLocallyBoundedOn_pbCoeffFun h γ
    φ _)]
  rw [← integral_finsetSum _ fun i _ =>
    hT.integrable_mul_density (measurable_pbCoeffFun h γ φ i) (isLocallyBoundedOn_pbCoeffFun h γ φ
      i) _ χ,
    pullback_apply h hT, ← integral_indicator B.isOpen.measurableSet]
  refine integral_congr_ae ?_
  have hall := ae_all_iff.mpr fun i => densityForm_ae hT (formBasis n q i)
  filter_upwards [hall] with y hy
  by_cases hyB : y ∈ (B : Set (ComplexModel n))
  · rw [indicator_of_mem hyB]
    simp only [pbCoeffFun, indicator_of_mem hyB]
    have hsum : densityForm hT y (pullSpan q (fderiv ℂ σ y) γ) =
        ∑ i, (formBasis n q).repr (pullSpan q (fderiv ℂ σ y) γ) i * hT.density (formBasis n q i)
          y := by
      conv_lhs => rw [← (formBasis n q).sum_repr (pullSpan q (fderiv ℂ σ y) γ)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, hy i]
    rw [hsum, Finset.mul_sum]
    by_cases hφ : φ (σ y) = 0
    · simp [hφ]
    · have hmem : y ∈ τ '' tsupport φ := ⟨σ y, subset_tsupport φ hφ, h.right_inv y hyB⟩
      rw [hχ y hmem]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · rw [indicator_of_notMem hyB]
    simp [pbCoeffFun, indicator_of_notMem hyB]

theorem tendstoLocallyUniformlyOn_const_seq {f : ComplexModel n → ℝ} {s : Set (ComplexModel n)} :
    TendstoLocallyUniformlyOn (fun (_ : ℕ) => f) f atTop s :=
  fun _ hu _ _ => ⟨univ, univ_mem, Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩

/-- **The pull-back is weakly continuous** on positive currents. -/
theorem weakTendsto_pullback (h : IsBiholomorphicPair A B τ σ) {T : ℕ → LocalProductCurrent n B q}
    {T₀ : LocalProductCurrent n B q} (hT : ∀ k, IsPositive (T k)) (hT₀ : IsPositive T₀)
      (hconv : WeakTendsto T T₀) :
    WeakTendsto (fun k => pullback h (hT k)) (pullback h hT₀) := by
  intro γ φ
  have hK : IsCompact (τ '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn (h.holo.continuousOn.mono φ.tsupport_subset)
  obtain ⟨χ, hχ⟩ := exists_testFunction_eq_one hK
    (image_subset_iff.mpr fun x hx => h.mapsTo (φ.tsupport_subset hx))
  simp only [pullback_apply_eq_sum_mulBorel h _ γ φ hχ]
  refine tendsto_finsetSum _ fun i _ => ?_
  exact weakTendsto_mulBorel hT hconv (fun _ => measurable_pbCoeffFun h γ φ i)
    (fun _ => isLocallyBoundedOn_pbCoeffFun h γ φ i) (measurable_pbCoeffFun h γ φ i)
    (continuousOn_pbCoeffFun h γ φ i) tendstoLocallyUniformlyOn_const_seq (formBasis n q i) χ

end Weak

/-- A locally bounded psh function composed with `τ` is locally bounded psh on `A`. -/
theorem isLocallyBoundedPshOn_comp {n : ℕ} {A B : Opens (ComplexModel n)}
    {τ σ : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ σ)
    {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn B w) : IsLocallyBoundedPshOn A (fun x => w (τ x)) := by
  refine ⟨HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (u := fun z => (w z : EReal))
    A.isOpen
    (h.holo.differentiableOn (by simp)) h.mapsTo hw.1, fun z hz => ?_⟩
  obtain ⟨V, hzV, hVB, C, hC⟩ := hw.2 (τ z) (h.mapsTo hz)
  exact ⟨preOpen h V, ⟨hz, hzV⟩, preOpen_le h V, C, fun x hx => hC (τ x) hx.2⟩

/-! ### Decreasing approximation and the main theorem -/

section Naturality

variable {m : ℕ}

/-- **`dd^c` along decreasing sequences**: if locally bounded psh `f_j` decrease pointwise to a
    locally bounded psh `w` on
`U`, then `dd^c f_j → dd^c w` weakly (dominated convergence; one potential only). -/
theorem weakTendsto_ddcMul_oneCurrent {U : Opens (ComplexModel (m + 1))} {f : ℕ → ComplexModel (m
    + 1) → ℝ}
    {w : ComplexModel (m + 1) → ℝ} (hf : ∀ j, IsLocallyBoundedPshOn U (f j)) (hw :
      IsLocallyBoundedPshOn U w)
    (hanti : ∀ z ∈ U, Antitone fun j => f j z) (hlim : ∀ z ∈ U, Tendsto (fun j => f j z)
      atTop (𝓝 (w z))) :
    WeakTendsto (fun j => ddcMul (oneCurrent U) (f j)) (ddcMul (oneCurrent U) w) := by
  simp only [ddcMul]
  refine weakTendsto_ddc fun γ φ => ?_
  have hT := isPositive_oneCurrent (U := U)
  simp only [mulBorel_apply hT (measurable_indicator_of_isLocallyBoundedPshOn (hf _))
    (isLocallyBoundedOn_indicator (hf _)),
    mulBorel_apply hT (measurable_indicator_of_isLocallyBoundedPshOn hw)
      (isLocallyBoundedOn_indicator hw)]
  obtain ⟨M₀, hM₀⟩ := isLocallyBoundedOn_indicator (hf 0) _ φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨M₁, hM₁⟩ := isLocallyBoundedOn_indicator hw _ φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨C, -, hC⟩ := hT.exists_abs_density_le γ
  have hbd : ∀ j, ∀ x, |φ x * ((U : Set (ComplexModel (m + 1))).indicator (f j)
    x * hT.density γ x)| ≤
      |φ x| * (max M₀ M₁ * C) := by
    intro j x
    by_cases hx : x ∈ tsupport φ
    · have hxU : x ∈ (U : Set (ComplexModel (m + 1))) := φ.tsupport_subset hx
      have h1 : w x ≤ f j x := (hanti x hxU).le_of_tendsto (hlim x hxU) j
      have h2 : f j x ≤ f 0 x := hanti x hxU (Nat.zero_le j)
      have e0 := hM₀ x hx
      have e1 := hM₁ x hx
      rw [indicator_of_mem hxU] at e0 e1 ⊢
      have hfj : |f j x| ≤ max M₀ M₁ := by
        rw [abs_le] at e0 e1 ⊢
        constructor
        · linarith [le_max_right M₀ M₁]
        · linarith [le_max_left M₀ M₁]
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hfj (hC x) (abs_nonneg _)
        ((abs_nonneg _).trans hfj)) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hint : Integrable (fun x => |φ x| * (max M₀ M₁ * C)) hT.traceMeasure := by
    have := hT.integrable_mul_of_bounded (w := fun _ => (1 : ℝ)) φ.continuous φ.hasCompactSupport
      φ.tsupport_subset aestronglyMeasurable_const ⟨1, fun _ _ => by simp⟩
    simp only [mul_one] at this
    exact this.abs.mul_const _
  refine tendsto_integral_of_dominated_convergence _ (fun j => ?_) hint
    (fun j => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbd j x)
    (Eventually.of_forall fun x => ?_)
  · exact (φ.continuous.measurable.mul ((measurable_indicator_of_isLocallyBoundedPshOn (hf j)).mul
      (hT.measurable_density γ))).aestronglyMeasurable
  · by_cases hxU : x ∈ (U : Set (ComplexModel (m + 1)))
    · simp only [indicator_of_mem hxU]
      exact ((hlim x hxU).mul_const _).const_mul _
    · simp only [indicator_of_notMem hxU]
      exact tendsto_const_nhds

variable {A B : Opens (ComplexModel (m + 1))} {τ σ : ComplexModel (m + 1) → ComplexModel (m + 1)}

/-- **Naturality of `dd^c` under biholomorphisms**: for a locally bounded psh `w` on `B`,
`τ^*(dd^c w) = dd^c(w ∘ τ)` on `A`. -/
theorem pullback_ddcMul (h : IsBiholomorphicPair A B τ σ) {w : ComplexModel (m + 1) → ℝ}
    (hw : IsLocallyBoundedPshOn B w) :
    pullback h (isPositive_ddcMul_oneCurrent hw) = ddcMul (oneCurrent A) (fun x => w (τ x)) := by
  ext γ φ
  have hK : IsCompact (τ '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn (h.holo.continuousOn.mono φ.tsupport_subset)
  have hKB : τ '' tsupport φ ⊆ B := image_subset_iff.mpr fun x hx => h.mapsTo (φ.tsupport_subset
    hx)
  obtain ⟨V₀, hVo, hKV, hVcl, hVc⟩ := exists_open_between_and_isCompact_closure hK B.isOpen hKB
  set V : Opens (ComplexModel (m + 1)) := ⟨V₀, hVo⟩ with hVdef
  have hVB : V ≤ B := subset_closure.trans hVcl
  have hVrc : RelativelyCompactIn V B := ⟨hVc, hVcl⟩
  obtain ⟨f, hfs, hfa, hfl⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hw hVrc
  have h' := isBiholomorphicPair_preOpen h hVB
  have hφA' : tsupport φ ⊆ preOpen h V := fun x hx => ⟨φ.tsupport_subset hx, hKV ⟨x, hx, rfl⟩⟩
  let φ' : 𝓓(preOpen h V, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφA'⟩
  have hext : extTest (preOpen_le h V) φ' = φ := by
    ext x
    rw [extTest_apply]
    rfl
  have hwV : IsLocallyBoundedPshOn V w := isLocallyBoundedPshOn_mono hw hVB
  have hS : ∀ j, IsLocallyBoundedPshOn V (f j) := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn
    (hfs j)
  -- the left side, on `A ∩ τ⁻¹(V)`
  have e1 : pullback h (isPositive_ddcMul_oneCurrent hw) γ φ =
      pullback h' (isPositive_ddcMul_oneCurrent hwV) γ φ' := by
    rw [← hext, ← LocalBedfordTaylorLocality.restrict_apply, ← pullback_restrict h _ hVB]
    have e : LocalBedfordTaylorLocality.restrict hVB (ddcMul (oneCurrent B) w) = ddcMul
      (oneCurrent V) w := by
      rw [← ddcMul_restrict isPositive_oneCurrent hVB hw, restrict_oneCurrent]
    rw [pullback_congr h' _ (isPositive_ddcMul_oneCurrent hwV) e]
  -- the limits
  have hpb := weakTendsto_pullback h' (fun j => isPositive_ddcMul_oneCurrent (hS j))
    (isPositive_ddcMul_oneCurrent hwV) (weakTendsto_ddcMul_oneCurrent hS hwV hfa hfl) γ φ'
  have hsm : ∀ j, pullback h' (isPositive_ddcMul_oneCurrent (hS j)) =
      ddcMul (oneCurrent (preOpen h V)) (fun x => f j (τ x)) := fun j =>
    pullback_ddcMul_of_isSmoothPshOn h' (hfs j)
  have hconvA := weakTendsto_ddcMul_oneCurrent (fun j => isLocallyBoundedPshOn_comp h' (hS j))
    (isLocallyBoundedPshOn_comp h' hwV) (fun z hz => hfa (τ z) hz.2) (fun z hz => hfl (τ z) hz.2)
      γ φ'
  have e2 : pullback h' (isPositive_ddcMul_oneCurrent hwV) γ φ' =
      ddcMul (oneCurrent (preOpen h V)) (fun x => w (τ x)) γ φ' := by
    refine tendsto_nhds_unique hpb ?_
    simp only [hsm]
    exact hconvA
  -- the right side, back on `A`
  rw [e1, e2, ← restrict_oneCurrent (preOpen_le h V),
    ddcMul_restrict isPositive_oneCurrent (preOpen_le h V) (isLocallyBoundedPshOn_comp h hw),
    LocalBedfordTaylorLocality.restrict_apply, hext]

end Naturality

end SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
