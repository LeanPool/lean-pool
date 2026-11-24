/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentNonCharging
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorMass
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing

/-!
# The relative weighted Chern–Levine–Nirenberg inequality

Source: Xia, *Foundations of pluripotential theory*, `lem:relative-weighted-cln` and
`lem:bounded-product-preserves-nonpolar-current` (used by `chapter_npp.tex`, `prop:npp1` (3),
second sentence).

On an open `U ⊆ ℂⁿ`, for a closed positive current `S` of bidimension `(m+1, m+1)`
(`LocalProductCurrent n U (m + 1)`, any base current, not only `[U]`) and a locally bounded
psh `v`:

* `integral_cutoff_ddcMul_sub_eq` — **integration by parts against a smooth psh weight**: for
  locally bounded psh `g₁, g₂` agreeing where the defect tests of the cutoff `χ` live,
  `∫ χ W dd^c(g₁ S) ∧ ω^m - ∫ χ g₁ dd^c W ∧ S ∧ ω^m` is the same for `g₁` and `g₂`.
* `traceMeasure_ddcWedge_ballPot` — `dd^c(A(|z - z₀|² - R²)) ∧ S` has trace measure
  `(A/π) σ_S`.
* `exists_lintegral_neg_ddcMul_le_of_smooth`, **`exists_lintegral_neg_ddcMul_le`** — **the
  relative weighted CLN inequality** (FPT `lem:relative-weighted-cln`, in every bidimension
  `r = m + 1 ≥ 1`): for balls `B(z₀, R₁) ⋐ B(z₀, R) ⋐ U` and a bound `M` for `|v|` on
  `BBar(z₀, R)` there is `C` (depending only on `R₁, R, M`) such that for every closed positive `S`
  and every locally bounded psh `V ≤ 0` on `BBar(z₀,R)`,
  `∫_{B(z₀,R₁)} (-V) dd^c v ∧ S ∧ ω^m ≤ C ∫_{B(z₀,R)} (-V) S ∧ ω^{m+1}`.
  The proof uses the collar modification `max(v, A(|z - z₀|² - R²))` and one integration by parts
  (so no extra variable is needed for `r = 1`), then decreasing smooth approximation of `V`.
* **`doesNotChargePluripolarOn_ddcMul`** — FPT `lem:bounded-product-preserves-nonpolar-current`:
  if the trace measure of `S` charges no locally pluripolar set, neither does that of
  `dd^c v ∧ S`; `doesNotChargePluripolarOn_btProduct_base` — the same for every relative
  Bedford–Taylor product `dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ S`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.CoordinateWedgeAssoc
open SGPT.Foundations.Analysis.Pending.ConstantFormProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorMass

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

variable {U : Opens (ComplexModel n)} {m : ℕ}

/-! ### Integration by parts against a smooth psh weight -/

/-- **Integration by parts with a smooth psh weight `W`**: if `g₁ = g₂` wherever one of the defect
tests of the cutoff `χ` is nonzero, then
`∫ χ W dd^c(g₁ Q) ∧ ω^m - ∫ χ g₁ dd^c W ∧ Q ∧ ω^m`
`= ∫ χ W dd^c(g₂ Q) ∧ ω^m - ∫ χ g₂ dd^c W ∧ Q ∧ ω^m`
(the difference only involves the derivatives of `χ`). -/
theorem integral_cutoff_ddcMul_sub_eq {Q : LocalProductCurrent n U (m + 1)} (hQ : IsPositive Q)
    (hQc : IsClosedCurrent Q) {g₁ g₂ : (ComplexModel n) → ℝ} (hg₁ : IsLocallyBoundedPshOn U g₁)
    (hg₂ : IsLocallyBoundedPshOn U g₂) {W : (ComplexModel n) → ℝ} (hW : ContDiffOn ℝ ∞ W U)
    (hWl : ∀ x ∈ U, ∀ v, 0 ≤ leviForm W x v) (χ : 𝓓(U, ℝ))
    (hχ : ∀ a b x, defectTest hW a b χ x ≠ 0 → g₁ x = g₂ x) :
    (∫ x, χ x * W x ∂(isPositive_ddcMul hQ hQc hg₁).1.traceMeasure) -
        ∫ x, χ x * g₁ x ∂(isPositive_ddcWedge hQ hW hWl).traceMeasure =
      (∫ x, χ x * W x ∂(isPositive_ddcMul hQ hQc hg₂).1.traceMeasure) -
        ∫ x, χ x * g₂ x ∂(isPositive_ddcWedge hQ hW hWl).traceMeasure := by
  have key : ∀ {g : (ComplexModel n) → ℝ} (hg : IsLocallyBoundedPshOn U g),
      (∫ x, χ x * W x ∂(isPositive_ddcMul hQ hQc hg).1.traceMeasure) -
          ∫ x, χ x * g x ∂(isPositive_ddcWedge hQ hW hWl).traceMeasure =
        ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
          mulBorel Q ((U : Set (ComplexModel n)).indicator g)
            (wedgeLM m (isOneOne_coeffForm a b) (kahlerPower n m)) (defectTest hW a b χ) := by
    intro g hg
    have hS := (isPositive_ddcMul hQ hQc hg).1
    have hS' := isPositive_ddcWedge hQ hW hWl
    have hum := measurable_indicator_of_isLocallyBoundedPshOn hg
    have hub := isLocallyBoundedOn_indicator hg
    have e1 : ∫ x, χ x * W x ∂hS.traceMeasure =
        ddcMul Q g (kahlerPower n m) (mulSmoothOnCLM hW χ) := by
      rw [← hS.integral_traceMeasure]
      rfl
    have hd : IsLocalDensity (U := U) hS'.traceMeasure (fun _ => 1) :=
      ⟨hS'.traceMeasure_compl, fun K hK hKU => hS'.traceMeasure_lt_top hK hKU,
        measurable_const, fun K _ _ => ⟨1, fun _ _ => by simp⟩⟩
    have e2 : ∫ x, χ x * g x ∂hS'.traceMeasure =
        mulBorel (ddcWedge Q hW) ((U : Set (ComplexModel n)).indicator g) (kahlerPower n m) χ := by
      rw [mulBorel_apply_of_integral_eq hS' _ hd (fun ψ => by
        rw [← hS'.integral_traceMeasure]
        simp) hum hub χ]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_one]
      by_cases hx : x ∈ (U : Set (ComplexModel n))
      · rw [Set.indicator_of_mem hx]
      · rw [testFunction_eq_zero_of_notMem χ hx, zero_mul, zero_mul]
    rw [e1, e2, ddcWedge_eq_wedgeForm, mulBorel_wedgeForm rfl hQ _ (ddcForm_mem_spCone hW hWl) hum
      hub, ← ddcWedge_eq_wedgeForm]
    exact ddc_sub_ddcWedge _ hW _ χ
  rw [key hg₁, key hg₂]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  refine mulBorel_apply_eq_of_forall hQ (measurable_indicator_of_isLocallyBoundedPshOn hg₁)
    (isLocallyBoundedOn_indicator hg₁) (measurable_indicator_of_isLocallyBoundedPshOn hg₂)
    (isLocallyBoundedOn_indicator hg₂) _ _ fun x hx => ?_
  have hxU : x ∈ (U : Set (ComplexModel n)) := by
    by_contra hxU
    exact hx (testFunction_eq_zero_of_notMem _ hxU)
  rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, hχ a b x hx]

/-! ### The collar potential -/

theorem leviForm_ballPot_nonneg {A : ℝ} (hA : 0 ≤ A) (z₀ : (ComplexModel n)) (R : ℝ) :
    ∀ x ∈ U, ∀ v, 0 ≤ leviForm (ballPot A z₀ R) x v := fun x _ v => by
  rw [leviForm_ballPot]
  positivity

/-- `dd^c (A(|z - z₀|² - R²)) = (A/π) ω₀`. -/
theorem smoothDDC_ballPot (A : ℝ) (z₀ : (ComplexModel n)) (R : ℝ) (z : (ComplexModel n)) :
    smoothDDC (ballPot A z₀ R) z = (A / Real.pi) • kahlerForm n := by
  have e : ballPot A z₀ R = fun y => A • ((fun y => ‖y - z₀‖ ^ 2) y - (fun _ => R ^ 2) y) := by
    funext y
    simp [SmoothMax.quadraticCollar, smul_eq_mul]
  have h1 : ContDiffOn ℝ ∞ (fun y : (ComplexModel n) => ‖y - z₀‖ ^ 2) univ :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn
  rw [e, smoothDDC_smul isOpen_univ (h1.sub contDiffOn_const) A (mem_univ z),
    PositiveClasses.smoothDDC_sub isOpen_univ h1 contDiffOn_const (mem_univ z),
    smoothDDC_norm_sub_sq,
    GlobalPotentialTransforms.smoothDDC_const, sub_zero, smul_smul, div_eq_mul_inv]

/-- `ω₀^m ∧ ω₀ = ω₀^{m+1}`. -/
theorem wedgeSpan_kahlerPower_one (m : ℕ) :
    wedgeSpan n rfl (kahlerPower n m) (kahlerPower n 1) = kahlerPower n (m + 1) := by
  apply Subtype.ext
  rw [coe_wedgeSpan_apply rfl _ _ (by omega)]
  have h1 : ((kahlerPower n 1 : formSpan n 1) : RealForm n (2 * 1)) = kahlerForm n :=
    coordinateWedge_unit_eq _
  rw [h1]
  rfl

/-- **The trace measure of `dd^c(A(|z - z₀|² - R²)) ∧ S` is `(A/π) σ_S`.** -/
theorem traceMeasure_ddcWedge_ballPot {S : LocalProductCurrent n U (m + 1)} (hS : IsPositive S)
    {A : ℝ} (hA : 0 ≤ A) (z₀ : (ComplexModel n)) (R : ℝ) :
    (isPositive_ddcWedge hS (contDiff_ballPot A z₀ R).contDiffOn
      (leviForm_ballPot_nonneg hA z₀ R)).traceMeasure =
      ENNReal.ofReal (A / Real.pi) • hS.traceMeasure := by
  set hP := isPositive_ddcWedge hS (contDiff_ballPot A z₀ R).contDiffOn
    (leviForm_ballPot_nonneg hA z₀ R)
  refine eq_of_forall_testFunction_integral_eq (U := U) hP.traceMeasure_compl ?_
    (fun K hK hKU => hP.traceMeasure_lt_top hK hKU) ?_ fun φ => ?_
  · rw [smul_apply, hS.traceMeasure_compl, smul_zero]
  · intro K hK hKU
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hS.traceMeasure_lt_top hK hKU)
  · rw [hP.integral_traceMeasure, integral_smul_measure, hS.integral_traceMeasure,
      ENNReal.toReal_ofReal (by positivity), ddcWedge_eq_wedgeForm,
      wedgeForm_apply_eq rfl S (contDiffOn_ddcForm (contDiff_ballPot A z₀ R).contDiffOn)
        (ddcForm_mem_formSpan (contDiff_ballPot A z₀ R).contDiffOn
          (leviForm_ballPot_nonneg hA z₀ R)) (κ := Unit)
        (fun _ _ => A / Real.pi) (fun _ => contDiffOn_const) (fun _ => kahlerPower n 1)
        (fun x _ => ?_) (kahlerPower n m) φ]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
      have hφ : mulSmoothOnCLM (contDiffOn_const (c := A / Real.pi)) φ = (A / Real.pi) • φ := by
        ext x
        simp only [mulSmoothOnCLM_apply]
        change φ x * (A / Real.pi) = (A / Real.pi) * φ x
        ring
      rw [wedgeSpan_kahlerPower_one, hφ, map_smul, smul_eq_mul]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
      change smoothDDC (ballPot A z₀ R) x = _
      rw [smoothDDC_ballPot]
      congr 1
      exact (coordinateWedge_unit_eq _).symm

/-! ### The relative weighted CLN inequality on a ball -/

/-- The ball `B(z₀, R)` is relatively compact in `U` when `BBar(z₀, R) ⊆ U`. -/
theorem relativelyCompactIn_ballOpens {z₀ : (ComplexModel n)} {R : ℝ} (hR : 0 < R)
    (hBU : closedBall z₀ R ⊆ U) : RelativelyCompactIn ⟨ball z₀ R, isOpen_ball⟩ U :=
  LocalBedfordTaylorDecreasing.relativelyCompactIn_ball hR hBU

/-- A function continuous on `U`, vanishing off `B(z₀, R)`, is integrable for the trace measure. -/
theorem integrable_of_continuousOn_of_vanishing {q : ℕ} {T : LocalProductCurrent n U q}
    (hT : IsPositive T) {z₀ : (ComplexModel n)} {R : ℝ} (hR : 0 < R) (hBU : closedBall z₀ R ⊆ U)
    {f : (ComplexModel n) → ℝ} (hf : ContinuousOn f U) (h0 : ∀ x ∉ ball z₀ R, f x = 0) :
    Integrable f hT.traceMeasure :=
  (integrableOn_of_continuousOn hT (relativelyCompactIn_ballOpens hR hBU) hf
    (B := ⟨ball z₀ R, isOpen_ball⟩)).integrable_of_forall_notMem_eq_zero h0

/-- **The relative weighted Chern–Levine–Nirenberg inequality for a smooth weight** (FPT
`lem:relative-weighted-cln`, Step 1, in every bidimension `m + 1 ≥ 1`): for `0 < R₁ < R` and
`M ≥ 0` there is `C ≥ 0` such that for every closed positive current `S` of bidimension
`(m+1, m+1)` on `U ⊇ BBar(z₀, R)`, every locally bounded psh `v` with `|v| ≤ M` on `BBar(z₀, R)` and
every smooth psh `V ≤ 0` on `B(z₀, R)`,
`∫_{B(z₀,R₁)} (-V) dd^c v ∧ S ∧ ω^m ≤ C ∫_{B(z₀,R)} (-V) S ∧ ω^{m+1}`. -/
theorem exists_lintegral_neg_ddcMul_le_of_smooth (z₀ : (ComplexModel n)) {R R₁ M : ℝ} (hR₁ : 0 <
    R₁)
    (hR₁R : R₁ < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U : Opens (ComplexModel n)} {m : ℕ} {S : LocalProductCurrent n U (m + 1)}
      (hS : IsPositive S) (hSc : IsClosedCurrent S), closedBall z₀ R ⊆ U →
      ∀ {v : (ComplexModel n) → ℝ} (hv : IsLocallyBoundedPshOn U v), (∀ z ∈ closedBall z₀ R,
        |v z| ≤ M) →
      ∀ {V : (ComplexModel n) → ℝ}, ContDiffOn ℝ ∞ V U → (∀ x ∈ U, ∀ w, 0 ≤ leviForm V x w) →
      (∀ z ∈ ball z₀ R, V z ≤ 0) →
      ∫⁻ z in ball z₀ R₁, ENNReal.ofReal (-V z) ∂(isPositive_ddcMul hS hSc hv).1.traceMeasure ≤
        ENNReal.ofReal C * ∫⁻ z in ball z₀ R, ENNReal.ofReal (-V z) ∂hS.traceMeasure := by
  have hR : 0 < R := hR₁.trans hR₁R
  have hR₁R' : R₁ < (R₁ + R) / 2 := by linarith
  have hR'R : (R₁ + R) / 2 < R := by linarith
  obtain ⟨A, hA, V', -, hKV', hcol⟩ :=
    collarMax_eq_of_le hR (isCompact_closedBall z₀ ((R₁ + R) / 2))
    (closedBall_subset_ball hR'R) (2 * M + 1)
  refine ⟨A / Real.pi, by positivity, ?_⟩
  intro U m S hS hSc hBU v hv hMv V hV hVl hV0
  have hBU' : ball z₀ R ⊆ U := ball_subset_closedBall.trans hBU
  -- the normalized potential and its collar modification
  set v' : (ComplexModel n) → ℝ := fun z => v z + (-(M + 1)) with hv'_def
  have hv' : IsLocallyBoundedPshOn U v' := isLocallyBoundedPshOn_add_const hv _
  have hv'1 : ∀ z ∈ closedBall z₀ R, v' z ≤ -1 := fun z hz => by
    have := (abs_le.mp (hMv z hz)).2
    simp only [hv'_def]
    linarith
  have hv'2 : ∀ z ∈ closedBall z₀ R, -(2 * M + 1) ≤ v' z := fun z hz => by
    have := (abs_le.mp (hMv z hz)).1
    simp only [hv'_def]
    linarith
  have hψ : IsLocallyBoundedPshOn U (ballPot A z₀ R) := isLocallyBoundedPshOn_ballPot hA.le z₀ R
  have hw : IsLocallyBoundedPshOn U (collarMax A z₀ R v') :=
    isLocallyBoundedPshOn_collarMax hA.le z₀ R hv'
  obtain ⟨K₀, hK₀, hK₀B, hK₀eq⟩ := eqOffCompact_collarMax hA z₀ R hv'1
  have hK₁ : IsCompact (K₀ ∪ closedBall z₀ R₁) := hK₀.union (isCompact_closedBall _ _)
  have hK₁B : K₀ ∪ closedBall z₀ R₁ ⊆ ball z₀ R := union_subset hK₀B (closedBall_subset_ball hR₁R)
  obtain ⟨K₂, hK₂, hK₁K₂, hK₂B⟩ := exists_compact_between hK₁ isOpen_ball hK₁B
  obtain ⟨χf, hχs, hχ1, hχB, hχ01⟩ := exists_cutoff_unit hK₂ isOpen_ball hK₂B
  have hχc : HasCompactSupport χf :=
    (isCompact_closedBall z₀ R).of_isClosed_subset (isClosed_tsupport χf)
      (hχB.trans ball_subset_closedBall)
  let χ : 𝓓(U, ℝ) :=
    { toFun := χf, contDiff' := hχs, hasCompactSupport' := hχc,
      tsupport_subset' := hχB.trans hBU' }
  have hχ0 : ∀ x ∉ ball z₀ R, χf x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hχB h)
  -- the defect tests of the cutoff live in the collar, where the two potentials agree
  have hdef : ∀ a b x, defectTest hV a b χ x ≠ 0 → collarMax A z₀ R v' x = ballPot A z₀ R x := by
    intro a b x hx
    by_cases hxK : x ∈ K₀ ∪ closedBall z₀ R₁
    · refine absurd (defectTest_eq_zero_of_eventually_one hV a b χ ?_) hx
      exact Filter.eventually_of_mem (mem_interior_iff_mem_nhds.mp (hK₁K₂ hxK))
        fun y hy => hχ1 y hy
    · by_cases hxB : x ∈ ball z₀ R
      · exact hK₀eq x hxB fun h => hxK (Or.inl h)
      · exact absurd (defectTest_eq_zero_of_eventually_zero hV a b χ
          (notMem_tsupport_iff_eventuallyEq.mp fun h => hxB (hχB h))) hx
  have key := integral_cutoff_ddcMul_sub_eq hS hSc hw hψ hV hVl χ hdef
  set σ₁ := (isPositive_ddcMul hS hSc hw).1.traceMeasure with hσ₁
  set σ₂ := (isPositive_ddcMul hS hSc hψ).1.traceMeasure with hσ₂
  set σQ := (isPositive_ddcWedge hS hV hVl).traceMeasure with hσQ
  have hχV0 : ∀ x ∉ ball z₀ R, χf x * V x = 0 := fun x hx => by rw [hχ0 x hx, zero_mul]
  have hχVc : ContinuousOn (fun x => χf x * V x) U :=
    hχs.continuous.continuousOn.mul hV.continuousOn
  -- the comparison of the two potentials against `dd^c V ∧ S`
  have hQle : ∫ x, χ x * ballPot A z₀ R x ∂σQ ≤ ∫ x, χ x * collarMax A z₀ R v' x ∂σQ := by
    have hB := relativelyCompactIn_ballOpens hR hBU
    refine integral_mono
      ((integrableOn_mul_of_isLocallyBoundedPshOn (isPositive_ddcWedge hS hV hVl) hB
        hχs.continuous.continuousOn hψ).integrable_of_forall_notMem_eq_zero fun x hx => by
          change χf x * _ = 0
          rw [hχ0 x hx, zero_mul])
      ((integrableOn_mul_of_isLocallyBoundedPshOn (isPositive_ddcWedge hS hV hVl) hB
        hχs.continuous.continuousOn hw).integrable_of_forall_notMem_eq_zero fun x hx => by
          change χf x * _ = 0
          rw [hχ0 x hx, zero_mul]) fun x => ?_
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hχ01 x).1
  have hcomp : ∫ x, χ x * V x ∂σ₂ ≤ ∫ x, χ x * V x ∂σ₁ := by linarith
  -- the collar potential term
  have hσ₂eq : σ₂ = ENNReal.ofReal (A / Real.pi) • hS.traceMeasure := by
    rw [hσ₂, LocalBedfordTaylorCollar.traceMeasure_congr
      (ddcMul_eq_ddcWedge hS hSc (contDiff_ballPot A z₀ R).contDiffOn)
      _ (isPositive_ddcWedge hS (contDiff_ballPot A z₀ R).contDiffOn
        (leviForm_ballPot_nonneg hA.le z₀ R)),
      traceMeasure_ddcWedge_ballPot hS hA.le z₀ R]
  have hI₂ : ∫ x, χ x * V x ∂σ₂ = A / Real.pi * ∫ x, χ x * V x ∂hS.traceMeasure := by
    rw [hσ₂eq, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  -- nonnegativity of the weights `χ (-V)`
  have hnn : ∀ x, 0 ≤ χf x * -V x := fun x => by
    by_cases hxB : x ∈ ball z₀ R
    · exact mul_nonneg (hχ01 x).1 (neg_nonneg.mpr (hV0 x hxB))
    · rw [hχ0 x hxB, zero_mul]
  have hint : ∀ {q : ℕ} {T : LocalProductCurrent n U q} (hT : IsPositive T),
      Integrable (fun x => χf x * -V x) hT.traceMeasure := fun hT =>
    integrable_of_continuousOn_of_vanishing hT hR hBU (hχs.continuous.continuousOn.mul
      hV.continuousOn.neg) fun x hx => by rw [hχ0 x hx, zero_mul]
  -- `σ_v = σ₁` on `B(z₀, R₁)`
  set W : Opens (ComplexModel n) := ⟨ball z₀ R₁, isOpen_ball⟩
  have hWU : W ≤ U := fun x hx => hBU' (ball_subset_ball hR₁R.le hx)
  have hWeq : ∀ x ∈ (W : Set (ComplexModel n)), collarMax A z₀ R v' x = v' x := fun x hx =>
    hcol A le_rfl v' x (hKV' (ball_subset_closedBall.trans (closedBall_subset_closedBall
      hR₁R'.le) hx)) (hv'2 x (ball_subset_closedBall.trans (closedBall_subset_closedBall
        hR₁R.le) hx))
  have hσW : σ₁.restrict (W : Set (ComplexModel n)) =
      (isPositive_ddcMul hS hSc hv).1.traceMeasure.restrict (W : Set (ComplexModel n)) := by
    have hSW := isPositive_restrict hS hWU
    have e : restrict hWU (ddcMul S (collarMax A z₀ R v')) = restrict hWU (ddcMul S v) := by
      rw [← ddcMul_restrict hS hWU hw, ← ddcMul_restrict hS hWU hv,
        ddcMul_congr _ hWeq, hv'_def,
        ddcMul_add_const hSW (isClosedCurrent_restrict hSc hWU)
          (isLocallyBoundedPshOn_mono hv hWU)]
    have h1 := traceMeasure_restrict (isPositive_ddcMul hS hSc hw).1 hWU
    have h2 := traceMeasure_restrict (isPositive_ddcMul hS hSc hv).1 hWU
    rw [← h1, ← h2]
    exact LocalBedfordTaylorCollar.traceMeasure_congr e _ _
  -- assembly
  calc ∫⁻ z in ball z₀ R₁, ENNReal.ofReal (-V z) ∂(isPositive_ddcMul hS hSc hv).1.traceMeasure
      = ∫⁻ z in ball z₀ R₁, ENNReal.ofReal (χf z * -V z) ∂σ₁ := by
        change ∫⁻ z, _ ∂((isPositive_ddcMul hS hSc hv).1.traceMeasure.restrict (W : Set
          (ComplexModel n))) =
          ∫⁻ z, _ ∂(σ₁.restrict (W : Set (ComplexModel n)))
        rw [← hσW]
        refine setLIntegral_congr_fun (s := (W : Set (ComplexModel n))) isOpen_ball.measurableSet
          fun z hz => ?_
        rw [hχ1 z (interior_subset (hK₁K₂ (Or.inr (ball_subset_closedBall hz)))), one_mul]
    _ ≤ ∫⁻ z, ENNReal.ofReal (χf z * -V z) ∂σ₁ := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ z, χf z * -V z ∂σ₁) :=
        (ofReal_integral_eq_lintegral_ofReal (hint _) (Eventually.of_forall hnn)).symm
    _ ≤ ENNReal.ofReal (A / Real.pi * ∫ z, χf z * -V z ∂hS.traceMeasure) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : ∫ z, χf z * -V z ∂σ₁ = -∫ x, χ x * V x ∂σ₁ := by
          rw [← integral_neg]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          change χf x * -V x = -(χf x * V x)
          ring
        have e2 : ∫ z, χf z * -V z ∂hS.traceMeasure = -∫ x, χ x * V x ∂hS.traceMeasure := by
          rw [← integral_neg]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          change χf x * -V x = -(χf x * V x)
          ring
        rw [e1, e2]
        nlinarith [hcomp, hI₂, Real.pi_pos]
    _ = ENNReal.ofReal (A / Real.pi) * ∫⁻ z, ENNReal.ofReal (χf z * -V z) ∂hS.traceMeasure := by
        rw [ENNReal.ofReal_mul (by positivity),
          ofReal_integral_eq_lintegral_ofReal (hint _) (Eventually.of_forall hnn)]
    _ ≤ ENNReal.ofReal (A / Real.pi) *
        ∫⁻ z in ball z₀ R, ENNReal.ofReal (-V z) ∂hS.traceMeasure := by
        refine mul_le_mul_right ?_ _
        rw [← setLIntegral_eq_of_support_subset (s := ball z₀ R) ?_]
        · refine setLIntegral_mono' isOpen_ball.measurableSet fun x hx => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have := neg_nonneg.mpr (hV0 x hx)
          nlinarith [(hχ01 x).2]
        · intro x hx
          by_contra hxB
          exact hx (by simp only [hχ0 x hxB, zero_mul, ENNReal.ofReal_zero])

/-- Smooth psh functions (in the sense of `IsSmoothPshOn`) have a semipositive Levi form. -/
theorem leviForm_nonneg_of_isSmoothPshOn {A : Opens (ComplexModel n)} {f : (ComplexModel n)
    → ℝ} (hf : IsSmoothPshOn A f)
    (c : ℝ) : ∀ x ∈ A, ∀ w, 0 ≤ leviForm (fun z => f z + c) x w := by
  intro x hx w
  have h2 : ContDiffAt ℝ 2 f x :=
    ((hf.1.contDiffAt (A.isOpen.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have e : (fun z => f z + c) = f + fun _ => c := rfl
  rw [e, leviForm_add h2 contDiffAt_const, leviForm_const, add_zero]
  exact leviForm_nonneg_of_posSemidef h2 (hf.2.2 x hx) w

/-- **The relative weighted Chern–Levine–Nirenberg inequality** (FPT `lem:relative-weighted-cln`,
for bounded weights, in every bidimension `m + 1 ≥ 1`): for `0 < R₁ < R` and `M` there is `C ≥ 0`
such that for every closed positive current `S` of bidimension `(m+1, m+1)` on `U ⊇ BBar(z₀, R)`,
every locally bounded psh `v` with `|v| ≤ M` on `BBar(z₀, R)` and every locally bounded psh
`V ≤ 0` on `BBar(z₀, R)`,
`∫_{B(z₀,R₁)} (-V) dd^c v ∧ S ∧ ω^m ≤ C ∫_{B(z₀,R)} (-V) S ∧ ω^{m+1}`. -/
theorem exists_lintegral_neg_ddcMul_le (z₀ : (ComplexModel n)) {R R₁ M : ℝ} (hR₁ : 0 < R₁)
    (hR₁R : R₁ < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U : Opens (ComplexModel n)} {m : ℕ} {S : LocalProductCurrent n U (m + 1)}
      (hS : IsPositive S) (hSc : IsClosedCurrent S), closedBall z₀ R ⊆ U →
      ∀ {v : (ComplexModel n) → ℝ} (hv : IsLocallyBoundedPshOn U v), (∀ z ∈ closedBall z₀ R,
        |v z| ≤ M) →
      ∀ {V : (ComplexModel n) → ℝ}, IsLocallyBoundedPshOn U V → (∀ z ∈ closedBall z₀ R, V z ≤ 0) →
      ∫⁻ z in ball z₀ R₁, ENNReal.ofReal (-V z) ∂(isPositive_ddcMul hS hSc hv).1.traceMeasure ≤
        ENNReal.ofReal C * ∫⁻ z in ball z₀ R, ENNReal.ofReal (-V z) ∂hS.traceMeasure := by
  have hR : 0 < R := hR₁.trans hR₁R
  obtain ⟨C, hC, hsm⟩ := exists_lintegral_neg_ddcMul_le_of_smooth (n := n) z₀ (M := M) hR₁ hR₁R
  refine ⟨C, hC, ?_⟩
  intro U m S hS hSc hBU v hv hMv V hV hV0
  -- a relatively compact neighbourhood `A` of `BBar(z₀, R)` and smooth approximations of `V` on it
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall z₀ R).exists_cthickening_subset_open U.isOpen hBU
  rw [cthickening_closedBall hδ.le hR.le] at hδU
  set A : Opens (ComplexModel n) := ⟨ball z₀ (R + δ / 2), isOpen_ball⟩
  have hAU' : closedBall z₀ (R + δ / 2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hδU
  have hArc : RelativelyCompactIn A U := relativelyCompactIn_ballOpens (by positivity) hAU'
  have hAU : A ≤ U := fun x hx => hAU' (ball_subset_closedBall hx)
  have hBA : closedBall z₀ R ⊆ (A : Set (ComplexModel n)) := closedBall_subset_ball (by linarith)
  obtain ⟨f, hf⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hV hArc
  have hfV : ∀ j, ∀ z ∈ (A : Set (ComplexModel n)), V z ≤ f j z := fun j z hz =>
    (hf.2.1 z hz).le_of_tendsto (hf.2.2 z hz) j
  -- the restricted data on `A`
  have hSA := isPositive_restrict hS hAU
  have hSAc := isClosedCurrent_restrict hSc hAU
  have hvA := isLocallyBoundedPshOn_mono hv hAU
  have hσA : (isPositive_ddcMul hSA hSAc hvA).1.traceMeasure =
      (isPositive_ddcMul hS hSc hv).1.traceMeasure.restrict A := by
    rw [← traceMeasure_restrict (isPositive_ddcMul hS hSc hv).1 hAU]
    exact LocalBedfordTaylorCollar.traceMeasure_congr (ddcMul_restrict hS hAU hv) _ _
  have hSAσ : hSA.traceMeasure = hS.traceMeasure.restrict A := traceMeasure_restrict hS hAU
  have hres : ∀ (μ : Measure (ComplexModel n)) {r : ℝ}, r ≤ R → (μ.restrict A).restrict (ball z₀
    r) =
      μ.restrict (ball z₀ r) := fun μ r hr => by
    rw [Measure.restrict_restrict isOpen_ball.measurableSet,
      inter_eq_left.mpr
        ((ball_subset_closedBall.trans (closedBall_subset_closedBall hr)).trans hBA)]
  -- the inequality with `ε - V`
  have hε : ∀ ε : ℝ, 0 < ε →
      ∫⁻ z in ball z₀ R₁, ENNReal.ofReal (ε - V z) ∂(isPositive_ddcMul hS hSc hv).1.traceMeasure ≤
        ENNReal.ofReal C * ∫⁻ z in ball z₀ R, ENNReal.ofReal (ε - V z) ∂hS.traceMeasure := by
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := exists_forall_lt_of_antitone A.isOpen (isCompact_closedBall z₀ R) hBA
      (fun j => (hf.1 j).1.continuousOn) hf.2.1 hf.2.2 (c := ε) fun z hz =>
        (hV0 z hz).trans_lt hε
    have hj : ∀ j, ∫⁻ z in ball z₀ R₁, ENNReal.ofReal (ε - f (j₀ + j) z)
        ∂(isPositive_ddcMul hS hSc hv).1.traceMeasure ≤
          ENNReal.ofReal C * ∫⁻ z in ball z₀ R, ENNReal.ofReal (ε - V z) ∂hS.traceMeasure := by
      intro j
      have h := hsm hSA hSAc hBA hvA hMv (V := fun z => f (j₀ + j) z + -ε)
        ((hf.1 (j₀ + j)).1.add contDiffOn_const) (leviForm_nonneg_of_isSmoothPshOn (hf.1 _) _)
        fun z hz => by
          have := hj₀ (j₀ + j) (Nat.le_add_right _ _) z (ball_subset_closedBall hz)
          linarith
      rw [hσA, hres _ hR₁R.le, hSAσ, hres _ le_rfl] at h
      refine le_trans (le_of_eq ?_) (h.trans (mul_le_mul_right ?_ _))
      · refine lintegral_congr fun z => ?_
        congr 1
        ring
      · refine setLIntegral_mono' isOpen_ball.measurableSet fun z hz => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have := hfV (j₀ + j) z (hBA (ball_subset_closedBall hz))
        linarith
    have hmeas : ∀ j, AEMeasurable (fun z => ENNReal.ofReal (ε - f (j₀ + j) z))
        ((isPositive_ddcMul hS hSc hv).1.traceMeasure.restrict (ball z₀ R₁)) := fun j =>
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((continuousOn_const.sub ((hf.1 (j₀ + j)).1.continuousOn.mono
          ((ball_subset_closedBall.trans (closedBall_subset_closedBall hR₁R.le)).trans hBA))
          ).aemeasurable isOpen_ball.measurableSet)
    have hlim := lintegral_tendsto_of_tendsto_of_monotone hmeas
      ((ae_restrict_mem isOpen_ball.measurableSet).mono fun z hz j j' hjj' => by
        have hzA : z ∈ (A : Set (ComplexModel n)) :=
          hBA (ball_subset_closedBall.trans (closedBall_subset_closedBall hR₁R.le) hz)
        exact ENNReal.ofReal_le_ofReal (by
          have := hf.2.1 z hzA (Nat.add_le_add_left hjj' j₀)
          linarith))
      ((ae_restrict_mem isOpen_ball.measurableSet).mono fun z hz => by
        have hzA : z ∈ (A : Set (ComplexModel n)) :=
          hBA (ball_subset_closedBall.trans (closedBall_subset_closedBall hR₁R.le) hz)
        exact (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub
          ((hf.2.2 z hzA).comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega)
            fun b => ⟨b, by omega⟩))))
    exact le_of_tendsto' hlim hj
  -- `ε → 0`
  set I := ∫⁻ z in ball z₀ R, ENNReal.ofReal (-V z) ∂hS.traceMeasure
  have hsfin : hS.traceMeasure (ball z₀ R) ≠ ⊤ :=
    (traceMeasure_lt_top_of_relativelyCompactIn hS (relativelyCompactIn_ballOpens hR hBU)).ne
  have hbound : ∀ k : ℕ,
      ∫⁻ z in ball z₀ R₁, ENNReal.ofReal (-V z) ∂(isPositive_ddcMul hS hSc hv).1.traceMeasure ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (1 / ((k : ℝ) + 1)) * hS.traceMeasure (ball z₀ R) + I) := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    refine (setLIntegral_mono' isOpen_ball.measurableSet fun z _ =>
      ENNReal.ofReal_le_ofReal (by linarith)).trans ((hε _ hk).trans (le_of_eq ?_))
    congr 1
    rw [← setLIntegral_const, ← lintegral_add_left measurable_const]
    refine setLIntegral_congr_fun isOpen_ball.measurableSet fun z hz => ?_
    rw [← ENNReal.ofReal_add hk.le (neg_nonneg.mpr (hV0 z (ball_subset_closedBall hz))),
      sub_eq_add_neg]
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal C *
      (ENNReal.ofReal (1 / ((k : ℝ) + 1)) * hS.traceMeasure (ball z₀ R) + I)) atTop
      (𝓝 (ENNReal.ofReal C * (0 * hS.traceMeasure (ball z₀ R) + I))) := by
    refine ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.mul_const ?_ (Or.inr hsfin)).add_const I)
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [zero_mul, zero_add] at hlim
  exact ge_of_tendsto' hlim hbound

/-! ### Relative Bedford–Taylor products do not charge pluripolar sets -/

/-- The pole set of a local pluripolar witness, cut to a closed ball inside its domain, is locally
pluripolar on `U`. -/
theorem locallyPluripolarOn_poleSet_inter_ball {V : Set (ComplexModel n)} {ψ : (ComplexModel n)
    → EReal} (hVo : IsOpen V)
    (hVc : IsPreconnected V) (hψ : PlurisubharmonicOn ψ V) (hne : ∃ a ∈ V, ψ a ≠ ⊥)
      {x : (ComplexModel n)}
    {r : ℝ} (hsub : closedBall x r ⊆ V) :
    LocallyPluripolarOn ({z | ψ z = ⊥} ∩ ball x r) (U : Set (ComplexModel n)) := by
  intro y _
  by_cases hyV : y ∈ V
  · exact ⟨V, ψ, hVo, hyV, hVc, hψ, hne, fun z _ hz => hz.1⟩
  · have hyB : r < dist y x := by
      by_contra h
      exact hyV (hsub (mem_closedBall.mpr (not_lt.mp h)))
    refine ⟨ball y (dist y x - r), fun _ => ((0 : ℝ) : EReal), isOpen_ball,
      mem_ball_self (by linarith), (convex_ball _ _).isPreconnected, ?_, ?_, ?_⟩
    · exact fun z _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) z
    · exact ⟨y, mem_ball_self (by linarith), EReal.coe_ne_bot _⟩
    · intro z hz hzs
      exfalso
      have h1 := mem_ball.mp hz
      have h2 := mem_ball.mp hzs.2
      have := dist_triangle y z x
      rw [dist_comm] at h1
      linarith

/-- **The pole set of a psh weight is not charged by `dd^c v ∧ S` when it is not charged by `S`**
(FPT, proof of `lem:bounded-product-preserves-nonpolar-current`, with the weights
`max(V/R, -1)`): if `ψ` is psh on `B(x, r) ⊆ U` and `σ_S({ψ = -∞} ∩ B(x, r/2)) = 0`, then the trace
measure of `dd^c v ∧ S` gives zero mass to `{ψ = -∞} ∩ B(x, r/4)`. -/
theorem traceMeasure_poleSet_ddcMul_eq_zero {S : LocalProductCurrent n U (m + 1)}
    (hS : IsPositive S) (hSc : IsClosedCurrent S) {v : (ComplexModel n) → ℝ} (hv :
      IsLocallyBoundedPshOn U v)
    {x : (ComplexModel n)} {r : ℝ} (hr : 0 < r) (hrb : ball x r ⊆ U) {ψ : (ComplexModel n) → EReal}
    (hψ₀ : PlurisubharmonicOn ψ (⟨ball x r, isOpen_ball⟩ : Opens (ComplexModel n)))
    (hpole : hS.traceMeasure ({z | ψ z = ⊥} ∩ ball x (r / 2)) = 0) :
    (isPositive_ddcMul hS hSc hv).1.traceMeasure ({z | ψ z = ⊥} ∩ ball x (r / 4)) = 0 := by
  set σ := (isPositive_ddcMul hS hSc hv).1.traceMeasure with hσ
  -- the data on `U₀ = B(x, r)`
  set U₀ : Opens (ComplexModel n) := ⟨ball x r, isOpen_ball⟩
  have hU₀ : U₀ ≤ U := hrb
  have hsubU : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrb
  have hB₀ : closedBall x (r / 2) ⊆ (U₀ : Set (ComplexModel n)) := closedBall_subset_ball (by
    linarith)
  obtain ⟨M, hM⟩ := exists_bound_on_compact hv (isCompact_closedBall x (r / 2)) hsubU
  obtain ⟨C, hC, hcln⟩ := exists_lintegral_neg_ddcMul_le (n := n) x (M := M)
    (by positivity : (0 : ℝ) < r / 4) (by linarith : r / 4 < r / 2)
  obtain ⟨S₀, hS₀, hψS₀⟩ := hψ₀.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall x (r / 2)) hB₀
  set S' : ℝ := S₀ + 1
  have hSU₀ := isPositive_restrict hS hU₀
  have hσU₀ : (isPositive_ddcMul hSU₀ (isClosedCurrent_restrict hSc hU₀)
      (isLocallyBoundedPshOn_mono hv hU₀)).1.traceMeasure = σ.restrict U₀ := by
    rw [hσ, ← traceMeasure_restrict (isPositive_ddcMul hS hSc hv).1 hU₀]
    exact LocalBedfordTaylorCollar.traceMeasure_congr (ddcMul_restrict hS hU₀ hv) _ _
  have hres : ∀ (μ : Measure (ComplexModel n)) {ρ : ℝ}, ρ ≤ r / 2 → (μ.restrict U₀).restrict (ball
    x ρ) =
      μ.restrict (ball x ρ) := fun μ ρ hρ => by
    rw [Measure.restrict_restrict isOpen_ball.measurableSet, inter_eq_left.mpr
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hρ)).trans hB₀)]
  -- the truncated weights
  set g : ℕ → (ComplexModel n) → ℝ≥0∞ := fun k z =>
    ENNReal.ofReal ((S' - truncationReal ψ k z) / (S' + k)) with hg_def
  have htr_le : ∀ k : ℕ, ∀ z ∈ closedBall x (r / 2), truncationReal ψ k z ≤ S₀ := by
    intro k z hz
    have h1 := coe_truncationReal hψ₀ k (hB₀ hz)
    have h2 : truncation ψ k z ≤ (S₀ : EReal) :=
      max_le (hψS₀ z hz) (EReal.coe_le_coe_iff.mpr (by
        linarith [Nat.cast_nonneg (α := ℝ) k]))
    rw [← h1] at h2
    exact EReal.coe_le_coe_iff.mp h2
  have htr_ge : ∀ (k : ℕ) (z : (ComplexModel n)), -(k : ℝ) ≤ truncationReal ψ k z := by
    intro k z
    have h2 : ((-(k : ℝ) : ℝ) : EReal) ≤ truncation ψ k z := le_max_right _ _
    by_cases ht : truncation ψ k z = ⊤
    · change -(k : ℝ) ≤ (truncation ψ k z).toReal
      rw [ht, EReal.toReal_top]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    · have hb : truncation ψ k z ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h2
      rw [← EReal.coe_toReal ht hb] at h2
      exact EReal.coe_le_coe_iff.mp h2
  have hmeasTr : ∀ (k : ℕ) (μ : Measure (ComplexModel n)) {ρ : ℝ}, ball x ρ ⊆ (U₀ : Set
    (ComplexModel n)) →
      AEMeasurable (truncationReal ψ k) (μ.restrict (ball x ρ)) := by
    intro k μ ρ hρ
    refine ((measurable_indicator_of_isLocallyBoundedPshOn
      (truncationReal_isLocallyBoundedPshOn hψ₀ k)).aemeasurable).congr ?_
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    exact Set.indicator_of_mem (hρ hz) _
  have hball₀ : ∀ {ρ : ℝ}, ρ ≤ r / 2 → ball x ρ ⊆ (U₀ : Set (ComplexModel n)) := fun hρ =>
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hρ)).trans hB₀
  -- the estimate at level `k`
  have hk : ∀ k : ℕ, σ ({z | ψ z = ⊥} ∩ ball x (r / 4)) ≤
      ENNReal.ofReal C * ∫⁻ z in ball x (r / 2), g k z ∂hS.traceMeasure := by
    intro k
    have hS'k : 0 < S' + k := by positivity
    have hw := isLocallyBoundedPshOn_add_const (truncationReal_isLocallyBoundedPshOn hψ₀ k) (-S')
    have h := hcln hSU₀ (isClosedCurrent_restrict hSc hU₀) hB₀
      (isLocallyBoundedPshOn_mono hv hU₀) hM hw fun z hz => by
        have := htr_le k z hz
        linarith
    rw [hσU₀, hres _ (by linarith), traceMeasure_restrict hS hU₀, hres _ le_rfl] at h
    -- the lower bound by the measure of the pole set
    have hlow : ENNReal.ofReal (S' + k) * σ ({z | ψ z = ⊥} ∩ ball x (r / 4)) ≤
        ∫⁻ z in ball x (r / 4), ENNReal.ofReal (-(truncationReal ψ k z + -S')) ∂σ := by
      have hmeas : AEMeasurable (fun z => ENNReal.ofReal (-(truncationReal ψ k z + -S')))
          (σ.restrict (ball x (r / 4))) :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((hmeasTr k σ (hball₀ (by linarith))).add_const _).neg
      refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (S' + k)))
      refine mul_le_mul_right ?_ _
      rw [Measure.restrict_apply' isOpen_ball.measurableSet]
      refine measure_mono fun z hz => ⟨?_, hz.2⟩
      have hzU : z ∈ (U₀ : Set (ComplexModel n)) := hB₀ ((ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith))) hz.2)
      have e : truncationReal ψ k z = -(k : ℝ) := by
        change (truncation ψ k z).toReal = _
        rw [truncation, hz.1, max_eq_right bot_le, EReal.toReal_coe]
      change ENNReal.ofReal (S' + k) ≤ ENNReal.ofReal (-(truncationReal ψ k z + -S'))
      rw [e]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hupper : ∫⁻ z in ball x (r / 2), ENNReal.ofReal (-(truncationReal ψ k z + -S'))
        ∂hS.traceMeasure = ENNReal.ofReal (S' + k) *
          ∫⁻ z in ball x (r / 2), g k z ∂hS.traceMeasure := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun z => ?_
      rw [hg_def, ← ENNReal.ofReal_mul hS'k.le]
      congr 1
      field_simp
      ring
    have := hlow.trans (h.trans (le_of_eq (by rw [hupper])))
    rw [mul_left_comm] at this
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hS'k).ne'
      ENNReal.ofReal_ne_top).mp this
  -- the limit `k → ∞`
  have hlim : Tendsto (fun k => ∫⁻ z in ball x (r / 2), g k z ∂hS.traceMeasure) atTop (𝓝 0) := by
    have hfin : hS.traceMeasure (ball x (r / 2)) ≠ ⊤ :=
      (traceMeasure_lt_top_of_relativelyCompactIn hS (relativelyCompactIn_ballOpens
        (by positivity) hsubU)).ne
    have := tendsto_lintegral_of_dominated_convergence' (μ := hS.traceMeasure.restrict
      (ball x (r / 2))) (F := g) (f := fun _ => 0) (fun _ => 1) (fun k =>
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((aemeasurable_const.sub (hmeasTr k _ (hball₀ le_rfl))).div_const _))
      (fun k => (ae_restrict_mem isOpen_ball.measurableSet).mono fun z hz => by
        change ENNReal.ofReal _ ≤ 1
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_one (by positivity)]
        linarith [htr_ge k z])
      (by rw [lintegral_const, Measure.restrict_apply_univ, one_mul]; exact hfin) ?_
    · simpa using this
    have hae : ∀ᵐ z ∂hS.traceMeasure.restrict (ball x (r / 2)), ψ z ≠ ⊥ := by
      rw [ae_iff, Measure.restrict_apply' isOpen_ball.measurableSet]
      refine measure_mono_null ?_ hpole
      intro z hz
      exact ⟨not_not.mp hz.1, hz.2⟩
    filter_upwards [hae, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzB
    have hzU : z ∈ (U₀ : Set (ComplexModel n)) := hB₀ (ball_subset_closedBall hzB)
    have hzt : ψ z ≠ ⊤ := (hψ₀ z hzU).ne_top
    set a := (ψ z).toReal
    have hψa : ψ z = (a : EReal) := (EReal.coe_toReal hzt hz).symm
    obtain ⟨K, hK⟩ := exists_nat_ge (-a)
    have hev : ∀ᶠ k : ℕ in atTop, g k z = ENNReal.ofReal ((S' - a) / (S' + k)) := by
      filter_upwards [eventually_ge_atTop K] with k hkK
      have : truncationReal ψ k z = a := by
        change (truncation ψ k z).toReal = a
        rw [truncation, hψa, max_eq_left (EReal.coe_le_coe_iff.mpr (by
          have : (K : ℝ) ≤ k := by exact_mod_cast hkK
          linarith)), EReal.toReal_coe]
      rw [hg_def]
      simp only [this]
    refine (tendsto_congr' hev).mpr ?_
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ S' tendsto_natCast_atTop_atTop)
  have hl2 := ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.ofReal_ne_top (r := C)))
  rw [mul_zero] at hl2
  exact le_antisymm (ge_of_tendsto hl2 (Eventually.of_forall hk)) bot_le

/-- A measure vanishing near every point of `U` on `s` vanishes on `s ∩ U`. -/
theorem measure_inter_eq_zero_of_local {μ : Measure (ComplexModel n)} {s : Set (ComplexModel n)}
    (h : ∀ x ∈ (U : Set (ComplexModel n)), ∃ W : Set (ComplexModel n), IsOpen W ∧ x ∈ W ∧ μ (s ∩
      W) = 0) :
    μ (s ∩ U) = 0 := by
  choose! W hWo hxW hW0 using h
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : (U : Set (ComplexModel n)) => W x) fun x => hWo x x.2
  have hcover : s ∩ U ⊆ ⋃ i ∈ T, s ∩ W i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, W (i : (ComplexModel n)) := hTU ▸ mem_iUnion.2 ⟨⟨z, hz.2⟩, hxW z hz.2⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 this
    exact mem_iUnion₂.2 ⟨i, hi, hz.1, hzi⟩
  exact measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 fun i _ => hW0 i i.2)

/-- **Relative Bedford–Taylor products with a base current not charging pluripolar sets do not
charge pluripolar sets** (FPT `lem:bounded-product-preserves-nonpolar-current`): if the trace
measure of the closed positive current `S` gives zero outer mass to every locally pluripolar set
of `U`, so does the trace measure of `dd^c v ∧ S` for every locally bounded psh `v`. -/
theorem doesNotChargePluripolarOn_ddcMul {S : LocalProductCurrent n U (m + 1)} (hS : IsPositive S)
    (hSc : IsClosedCurrent S) (hS0 : DoesNotChargePluripolarOn hS.traceMeasure (U : Set
      (ComplexModel n)))
    {v : (ComplexModel n) → ℝ} (hv : IsLocallyBoundedPshOn U v) :
    DoesNotChargePluripolarOn (isPositive_ddcMul hS hSc hv).1.traceMeasure (U : Set (ComplexModel
      n)) := by
  intro s hs
  refine measure_inter_eq_zero_of_local fun x hx => ?_
  obtain ⟨V, ψ, hVo, hxV, hVc, hψ, hne, hp⟩ := hs x hx
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp (hVo.inter U.isOpen) x ⟨hxV, hx⟩
  have hsub : closedBall x (r / 2) ⊆ V ∩ U := (closedBall_subset_ball (by linarith)).trans hrb
  refine ⟨ball x (r / 4), isOpen_ball, mem_ball_self (by positivity), ?_⟩
  have hpole : hS.traceMeasure ({z | ψ z = ⊥} ∩ ball x (r / 2)) = 0 := by
    have h0 := hS0 _ (locallyPluripolarOn_poleSet_inter_ball (U := U) hVo hVc hψ hne
      (fun z hz => (hsub hz).1))
    have hsubU : {z | ψ z = ⊥} ∩ ball x (r / 2) ⊆ (U : Set (ComplexModel n)) :=
      fun _ hz => (hsub (ball_subset_closedBall hz.2)).2
    rwa [inter_eq_left.mpr hsubU] at h0
  refine measure_mono_null ?_ (traceMeasure_poleSet_ddcMul_eq_zero hS hSc hv hr
    (fun z hz => (hrb hz).2) (hψ.mono fun z hz => (hrb hz).1) hpole)
  intro z hz
  refine ⟨hp z ?_ hz.1, hz.2⟩
  exact (hsub ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    hz.2)).1

/-- **Every relative Bedford–Taylor product `dd^c v₁ ∧ ⋯ ∧ dd^c v_q ∧ T` with a base not charging
pluripolar sets does not charge pluripolar sets** (FPT
`lem:bounded-product-preserves-nonpolar-current`, second assertion). -/
theorem doesNotChargePluripolarOn_btProduct_base : ∀ (q r : ℕ) (v : Fin q → (ComplexModel n) → ℝ)
    (T : LocalProductCurrent n U (r + q)) (hT : IsPositive T) (hTc : IsClosedAny (r + q) T)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i)),
    DoesNotChargePluripolarOn hT.traceMeasure (U : Set (ComplexModel n)) →
    DoesNotChargePluripolarOn (isPositive_btProduct q r v T hT hTc hv).1.traceMeasure (U : Set
      (ComplexModel n))
  | 0, _, _, _, _, _, _, h0 => h0
  | q + 1, r, v, _, hT, hTc, hv, h0 =>
    doesNotChargePluripolarOn_btProduct_base q r (Fin.init v) _ _
      (isPositive_ddcMul (m := r + q) hT hTc (hv (Fin.last q))).2 (fun _ => hv _)
      (doesNotChargePluripolarOn_ddcMul (m := r + q) hT hTc h0 (hv (Fin.last q)))

end SGPT.NPP.NonPluripolarCurrent
