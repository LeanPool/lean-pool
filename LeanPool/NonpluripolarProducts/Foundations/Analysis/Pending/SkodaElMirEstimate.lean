/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SlotTestForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SkodaElMirLimit
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConcentrationPotentialLevi

/-!
# The Skoda--El Mir estimate in one chart

Let `T` be a closed positive current of bidimension `(k+1, k+1)` on a compact Kähler manifold,
`β₀, …, β_{k-1}` closed semipositive `(1,1)`-forms and `Φ(γ) = T (Π₁₁ γ ∧ β)` the slot functional
(`SlotTestForms`).  For a chart-smooth `v` put

`s(v) = π (ddᶜ(v²) - 2 v ddᶜv)`  (`gradForm`; on complex lines `(dv(w)² + dv(iw)²)/2`).

* **Cauchy--Schwarz** (`sq_apply_slotForm_le`): if `h₁ ≥ 0` and `h₁ = 1` where `a ≠ 0`, then
  `Φ(a Π₁₁ d(v dg))² ≤ 4 Φ(h₁ s(v)) Φ(a² s(g))`, because
  `h₁ s(v) + t a Π₁₁ (dv ∧ dg) + t² a² s(g)` is nonnegative on complex lines for every real `t`.
* **The uniform bound** (`apply_slotForm_gradForm_le`): if `0 ≤ v ≤ 1`, `ddᶜv ≥ 0` where
  `h₁ ≠ 0`, `h₁` smooth with compact support in a chart and `B ω - ddᶜh₁ ≥ 0`, then
  `Φ(h₁ s(v)) ≤ π Φ(h₁ ddᶜ(v²)) = π Φ(v² ddᶜh₁) ≤ π B Φ(ω)` (integration by parts, `slotForm_ibp`),
  uniformly in `v`.
* **The El Mir lemma in a chart** (`restrictCurrent_closedTestForm_eq_zero`): for cut-offs `vᵢ`
  as above with `θ(vᵢ) → 𝟙_E` where `h₁ ≠ 0` and `θ'(vᵢ) → 0` where `f ≠ 0` (`θ = elMirCutoff`),
  `𝟙_E T (Π₁₁ d(f dg) ∧ β) = 0`: `T (h₁ θ(vᵢ) Π₁₁ d(f dg) ∧ β) → 𝟙_E T (…)` (`SkodaElMirLimit`), it
  equals `-Φ(f θ'(vᵢ) Π₁₁ d(vᵢ dg))` (Leibniz, closedness), whose square is at most
  `4 π B Φ(ω) Φ((f θ'(vᵢ))² s(g)) → 0` (dominated convergence).

This is steps (E4), (Bound) and the assembly of the Skoda--El Mir argument
(`demailly-cadg:III.2.3`), TN.4 step B4.3, the Skoda–El Mir extension argument.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.SkodaElMirEstimate

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents TopDegreeDensity ClosedProductCurrents
  SmoothCurrentClosedness ClosedCurrentLocalTests CurrentTraceMeasure SmoothDDCForm ChartPartition
  SlotTestForms SkodaElMirLimit CurrentRestriction ConcentrationPotentialLevi

/-! ### The cut-off `θ` -/

section Cutoff

/-- The cut-off `θ(t) = σ(3t - 1)` (`σ` the smooth transition): `θ = 0` on `(-∞, 1/3]`,
`θ = 1` on `[2/3, ∞)`. -/
def elMirCutoff (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)

theorem contDiff_elMirCutoff : ContDiff ℝ ∞ elMirCutoff :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.mul contDiff_id).sub
    contDiff_const)

theorem elMirCutoff_nonneg (t : ℝ) : 0 ≤ elMirCutoff t := Real.smoothTransition.nonneg _

theorem elMirCutoff_le_one (t : ℝ) : elMirCutoff t ≤ 1 := Real.smoothTransition.le_one _

theorem elMirCutoff_zero : elMirCutoff 0 = 0 :=
  Real.smoothTransition.zero_of_nonpos (by norm_num)

theorem elMirCutoff_one : elMirCutoff 1 = 1 :=
  Real.smoothTransition.one_of_one_le (by norm_num)

theorem deriv_elMirCutoff_zero : deriv elMirCutoff 0 = 0 := by
  have h : elMirCutoff =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t ht
    exact Real.smoothTransition.zero_of_nonpos (by simp only [mem_Iio] at ht; linarith)
  rw [h.deriv_eq, deriv_const]

theorem deriv_elMirCutoff_one : deriv elMirCutoff 1 = 0 := by
  have h : elMirCutoff =ᶠ[𝓝 1] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t ht
    exact Real.smoothTransition.one_of_one_le (by simp only [mem_Ioi] at ht; linarith)
  rw [h.deriv_eq, deriv_const]

theorem contDiff_deriv_elMirCutoff : ContDiff ℝ ∞ (deriv elMirCutoff) :=
  (contDiff_infty_iff_deriv.mp contDiff_elMirCutoff).2

theorem continuous_deriv_elMirCutoff : Continuous (deriv elMirCutoff) :=
  contDiff_deriv_elMirCutoff.continuous

theorem exists_abs_deriv_elMirCutoff_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    |deriv elMirCutoff t| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_deriv_elMirCutoff.continuousOn (s := Icc (0 : ℝ) 1)
  exact ⟨max C 0, le_max_right _ _, fun t ht => (hC t ht).trans (le_max_left _ _)⟩

end Cutoff

/-! ### The form `s(v)` -/

section Grad

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `s(v) = π (ddᶜ(v²) - 2 v ddᶜv) = 2π dv ∧ dᶜv`. -/
def gradForm (v : M → ℝ) (hv : ChartSmooth (n := n) v) : SmoothRealForm n M 2 :=
  Real.pi • (ddcForm (fun x => v x * v x) (chartSmooth_mul hv hv) - (2 : ℝ) • smulFun v hv
    (ddcForm v hv))

omit [IsComplexManifold n M] in
theorem contDiffAt_two_of_chartSmooth {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ContDiffAt ℝ 2 (fun y => v (e.val.symm y)) z :=
  ((hv e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)

/-- **`s(v)` on complex lines**: `(dv(w)² + dv(iw)²)/2`. -/
theorem gradForm_coeff_line {v : M → ℝ} (hv : ChartSmooth (n := n) v) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) (w : ComplexModel n) :
    (gradForm v hv).coeff e z ![w, Complex.I • w] =
      (fderiv ℝ (fun y => v (e.val.symm y)) z w ^ 2 +
        fderiv ℝ (fun y => v (e.val.symm y)) z (Complex.I • w) ^ 2) / 2 := by
  have hV := contDiffAt_two_of_chartSmooth hv e hz
  have hVV : ContDiffAt ℝ 2 (fun y => v (e.val.symm y) * v (e.val.symm y)) z := hV.mul hV
  simp only [gradForm, coeff_smul, coeff_sub, smulFun_coeff, ddcForm_coeff,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply, smul_eq_mul]
  rw [smoothDDC_complexDiagonal_eq_leviForm hVV, smoothDDC_complexDiagonal_eq_leviForm hV,
    leviForm_mul hV hV]
  field_simp
  ring

theorem gradForm_coeff_line_nonneg {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) (w : ComplexModel n) :
    0 ≤ (gradForm v hv).coeff e z ![w, Complex.I • w] := by
  rw [gradForm_coeff_line hv e hz]
  positivity

/-- `d(v dg)` on complex lines. -/
theorem exactPair_coeff_line {v g : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hg : ChartSmooth (n := n) g) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) (w : ComplexModel n) :
    (exactPair v g hv hg).coeff e z ![w, Complex.I • w] =
      fderiv ℝ (fun y => v (e.val.symm y)) z w * fderiv ℝ (fun y => g (e.val.symm y))
        z (Complex.I • w) -
        fderiv ℝ (fun y => v (e.val.symm y)) z (Complex.I • w) *
          fderiv ℝ (fun y => g (e.val.symm y)) z w :=
  exactPair_coeff_apply v g hv hg e hz _ _

end Grad

/-! ### Cauchy--Schwarz and the uniform bound -/

section Estimates

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {k : ℕ} {T : ProductCurrent n M (k + 1)}

/-- **Cauchy--Schwarz for the slot functional**: if `h₁ ≥ 0` and `h₁ = 1` where `a ≠ 0`, then
`Φ(a Π₁₁ d(v dg))² ≤ 4 Φ(h₁ s(v)) Φ(a² s(g))`. -/
theorem sq_apply_slotForm_le (hT : IsPositive T) {β : Fin k → ClosedRealOneOneForm n M}
    (hβ : ∀ j, (β j).val.IsSemipositive) {v g a h₁ : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hg : ChartSmooth (n := n) g) (ha : ChartSmooth (n := n) a) (hh₁ : ChartSmooth (n := n) h₁)
    (hh₁0 : ∀ x, 0 ≤ h₁ x) (hah : ∀ x, a x ≠ 0 → h₁ x = 1) :
    T (slotForm (smulFun a ha (exactPair v g hv hg)) k β) ^ 2 ≤
      4 * T (slotForm (smulFun h₁ hh₁ (gradForm v hv)) k β) *
        T (slotForm (smulFun (fun x => a x * a x) (chartSmooth_mul ha ha) (gradForm g hg)) k β)
          := by
  set A := smulFun h₁ hh₁ (gradForm v hv)
  set Bf := smulFun a ha (exactPair v g hv hg)
  set C := smulFun (fun x => a x * a x) (chartSmooth_mul ha ha) (gradForm g hg)
  have hquad : ∀ t : ℝ, 0 ≤ T (slotForm C k β) * (t * t) + T (slotForm Bf k β) * t +
      T (slotForm A k β) := by
    intro t
    have hpos := apply_slotForm_nonneg hT hβ (γ := A + t • Bf + (t * t) • C) fun e z hz w => by
      set x := e.val.symm z
      simp only [coeff_add, coeff_smul, ContinuousAlternatingMap.add_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul, A, Bf, C, smulFun_coeff]
      rw [gradForm_coeff_line hv e hz, gradForm_coeff_line hg e hz, exactPair_coeff_line hv hg e
        hz]
      set p := fderiv ℝ (fun y => v (e.val.symm y)) z w
      set q := fderiv ℝ (fun y => v (e.val.symm y)) z (Complex.I • w)
      set r := fderiv ℝ (fun y => g (e.val.symm y)) z w
      set s := fderiv ℝ (fun y => g (e.val.symm y)) z (Complex.I • w)
      by_cases hax : a x = 0
      · rw [hax]
        have := hh₁0 x
        have : 0 ≤ (p ^ 2 + q ^ 2) / 2 := by positivity
        simp only [zero_mul, mul_zero, add_zero]
        positivity
      · rw [hah x hax]
        nlinarith [sq_nonneg (p + t * a x * s), sq_nonneg (q - t * a x * r)]
    rw [slotForm_add, slotForm_add, slotForm_smul, slotForm_smul, map_add, map_add, map_smul,
      map_smul, smul_eq_mul, smul_eq_mul] at hpos
    linarith
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  linarith

/-- **The uniform bound**: `Φ(h₁ s(v)) ≤ π B Φ(ω)` when `0 ≤ v ≤ 1`, `ddᶜv ≥ 0` where `h₁ ≠ 0`,
`h₁` is smooth with compact support in one chart and `B ω - ddᶜh₁ ≥ 0` on complex lines. -/
theorem apply_slotForm_gradForm_le (hT : IsPositive T) (hTc : IsClosedCurrent T)
    {β : Fin k → ClosedRealOneOneForm n M} (hβ : ∀ j, (β j).val.IsSemipositive)
    (w : KahlerBackground n M) (e : ComplexChart n M) {χ : ComplexModel n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχt : tsupport χ ⊆ e.val.target)
    (hχ0 : ∀ z, 0 ≤ χ z) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (e' : ComplexChart n M) z, z ∈ e'.val.target → ∀ u : ComplexModel n,
      (ddcForm (chartExtend e χ) (chartSmooth_chartExtend e hχ hχc hχt)).coeff e' z
        ![u, Complex.I • u] ≤ B * w.form.val.coeff e' z ![u, Complex.I • u])
    {v : M → ℝ} (hv : ChartSmooth (n := n) v) (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1)
    (hpsh : ∀ (e' : ComplexChart n M) z, z ∈ e'.val.target → chartExtend e χ (e'.val.symm z) ≠ 0 →
      CoefficientSemipositive ((ddcForm v hv).coeff e' z)) :
    T (slotForm (smulFun (chartExtend e χ) (chartSmooth_chartExtend e hχ hχc hχt) (gradForm v hv))
      k β)
      ≤ Real.pi * B * T (slotForm w.form.val k β) := by
  set hh := chartSmooth_chartExtend e hχ hχc hχt
  set h := chartExtend e χ
  have hh0 : ∀ x, 0 ≤ h x := chartExtend_nonneg hχ0
  have hvv : ChartSmooth (n := n) (fun x => v x * v x) := chartSmooth_mul hv hv
  have hω : ∀ (e' : ComplexChart n M) z, z ∈ e'.val.target → ∀ u : ComplexModel n,
      0 ≤ w.form.val.coeff e' z ![u, Complex.I • u] := fun e' z hz u => w.isSemipositive e' z hz u
  -- `h s(v) ≤ π h ddᶜ(v²)`
  have h1 : T (slotForm (smulFun h hh (gradForm v hv)) k β) ≤
      Real.pi * T (slotForm (smulFun h hh (ddcForm _ hvv)) k β) := by
    have := apply_slotForm_nonneg hT hβ
      (γ := Real.pi • smulFun h hh (ddcForm _ hvv) - smulFun h hh (gradForm v hv))
      fun e' z hz u => by
        simp only [gradForm, coeff_smul, coeff_sub, smulFun_coeff,
          ContinuousAlternatingMap.smul_apply,
          ContinuousAlternatingMap.sub_apply, smul_eq_mul]
        by_cases hx : h (e'.val.symm z) = 0
        · rw [hx]; simp
        · have hp := hpsh e' z hz hx u
          have := hh0 (e'.val.symm z)
          have := hv0 (e'.val.symm z)
          have hprod : 0 ≤ h (e'.val.symm z) * v (e'.val.symm z) *
              (ddcForm v hv).coeff e' z ![u, Complex.I • u] := by positivity
          have hπ := Real.pi_pos
          have key := mul_nonneg hπ.le hprod
          nlinarith
    rw [slotForm_sub, slotForm_smul, map_sub, map_smul, smul_eq_mul] at this
    linarith
  -- integration by parts
  have h2 := slotForm_ibp hT hTc β e hχ hχc hχt hvv
  -- `v² ddᶜh ≤ B v² ω ≤ B ω`
  have h3 : T (slotForm (smulFun _ hvv (ddcForm h hh)) k β) ≤
      B * T (slotForm (smulFun _ hvv w.form.val) k β) := by
    have := apply_slotForm_nonneg hT hβ
      (γ := B • smulFun _ hvv w.form.val - smulFun _ hvv (ddcForm h hh)) fun e' z hz u => by
        simp only [coeff_smul, coeff_sub, smulFun_coeff, ContinuousAlternatingMap.smul_apply,
          ContinuousAlternatingMap.sub_apply, smul_eq_mul]
        have hb := hB e' z hz u
        have : 0 ≤ v (e'.val.symm z) * v (e'.val.symm z) := mul_self_nonneg _
        nlinarith
    rw [slotForm_sub, slotForm_smul, map_sub, map_smul, smul_eq_mul] at this
    linarith
  have h4 : T (slotForm (smulFun _ hvv w.form.val) k β) ≤ T (slotForm w.form.val k β) := by
    have := apply_slotForm_nonneg hT hβ
      (γ := w.form.val - smulFun _ hvv w.form.val) fun e' z hz u => by
        simp only [coeff_sub, smulFun_coeff, ContinuousAlternatingMap.sub_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        have := hω e' z hz u
        have h0 := hv0 (e'.val.symm z)
        have h1' := hv1 (e'.val.symm z)
        have : v (e'.val.symm z) * v (e'.val.symm z) ≤ 1 := by nlinarith
        nlinarith
    rw [slotForm_sub, map_sub] at this
    linarith
  have hπ := Real.pi_pos
  calc T (slotForm (smulFun h hh (gradForm v hv)) k β)
      ≤ Real.pi * T (slotForm (smulFun h hh (ddcForm _ hvv)) k β) := h1
    _ = Real.pi * T (slotForm (smulFun _ hvv (ddcForm h hh)) k β) := by rw [h2]
    _ ≤ Real.pi * (B * T (slotForm w.form.val k β)) := by
        refine mul_le_mul_of_nonneg_left (h3.trans ?_) hπ.le
        exact mul_le_mul_of_nonneg_left h4 hB0
    _ = Real.pi * B * T (slotForm w.form.val k β) := by ring

/-- A constant `B ≥ 0` with `ddᶜh ≤ B ω` on complex lines, for a chart-smooth `h` on a compact
Kähler manifold. -/
theorem exists_ddcForm_le_smul [CompactSpace M] (w : KahlerBackground n M) {h : M → ℝ}
    (hh : ChartSmooth (n := n) h) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (e' : ComplexChart n M) z, z ∈ e'.val.target → ∀ u : ComplexModel n,
      (ddcForm h hh).coeff e' z ![u, Complex.I • u] ≤ B * w.form.val.coeff e' z ![u,
        Complex.I • u] := by
  obtain ⟨B, hB, hdom⟩ := KahlerDomination.exists_isSemipositive_add_smul (-ddcForm h hh)
    w.form.val w.isKahler.1
  refine ⟨B, hB.le, fun e' z hz u => ?_⟩
  have := hdom e' z hz u
  simp only [coeff_neg, ContinuousAlternatingMap.neg_apply] at this
  linarith

/-- **Slot functional of function multiples, as integrals.** -/
theorem tendsto_apply_slotForm_smulFun [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (w : KahlerBackground n M) (hT : IsPositive T) {β : Fin k → ClosedRealOneOneForm n M}
    (hβ : ∀ j, (β j).val.IsSemipositive) {γ : SmoothRealForm n M 2}
    (hγ : ∀ (e : ComplexChart n M) z, z ∈ e.val.target → CoefficientSemipositive (γ.coeff e z))
    {F : ℕ → M → ℝ} (hF : ∀ i, ChartSmooth (n := n) (F i)) {C : ℝ} (hFC : ∀ i x, |F i x| ≤ C)
    (hlim : ∀ x, Tendsto (fun i => F i x) atTop (𝓝 0)) :
    Tendsto (fun i => T (slotForm (smulFun (F i) (hF i) γ) k β)) atTop (𝓝 0) := by
  have hpos := slotForm_mem_positiveCone hγ k β hβ
  have heq : ∀ i, T (slotForm (smulFun (F i) (hF i) γ) k β) =
      ∫ x, F i x ∂(testMeasure w T hT _ hpos) := fun i => by
    rw [slotForm_smulFun, integral_testMeasure w T hT _ hpos _ (hF i)]
  simp_rw [heq]
  have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂(testMeasure w T hT _ hpos) := by simp
  rw [h0]
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun i => (chartSmooth_continuous (hF i)).aestronglyMeasurable) (integrable_const C)
    (fun i => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFC i x)
    (Eventually.of_forall hlim)

end Estimates

/-! ### The El Mir lemma in a chart -/

section ElMir

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] {k : ℕ}
  {T : ProductCurrent n M (k + 1)}

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
omit [IsComplexManifold n M] in
theorem chartSmooth_comp_real {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {v : M → ℝ}
    (hv : ChartSmooth (n := n) v) : ChartSmooth (n := n) (fun x => θ (v x)) :=
  fun e => hθ.comp_contDiffOn (hv e)

theorem tendsto_zero_of_sq_le {u r : ℕ → ℝ} {K : ℝ} (hle : ∀ i, u i ^ 2 ≤ K * r i)
    (hr : Tendsto r atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  have hsq : Tendsto (fun i => u i ^ 2) atTop (𝓝 0) := by
    have hK : Tendsto (fun i => K * r i) atTop (𝓝 0) := by simpa using hr.const_mul K
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK
      (fun i => sq_nonneg _) hle
  have habs : Tendsto (fun i => |u i|) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at this
    exact this
  exact (tendsto_zero_iff_abs_tendsto_zero u).mpr habs

/-- **The Skoda--El Mir lemma in one chart.**  Let `T` be closed positive, `β` closed
semipositive, `h₁ = χ ∘ e` a chart bump (`0 ≤ χ ≤ 1`) equal to `1` near the support of `f`, and
`vᵢ` chart-smooth with `0 ≤ vᵢ ≤ 1` and `ddᶜvᵢ ≥ 0` where `h₁ ≠ 0`.  If `θ(vᵢ) → 𝟙_E` where
`h₁ ≠ 0` and `θ'(vᵢ) → 0` where `f ≠ 0`, then `𝟙_E T (Π₁₁ d(f dg) ∧ β) = 0`. -/
theorem restrictCurrent_closedTestForm_eq_zero (w : KahlerBackground n M) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {β : Fin k → ClosedRealOneOneForm n M}
    (hβ : ∀ j, (β j).val.IsSemipositive) {E : Set M} (hE : MeasurableSet E) {f g : M → ℝ}
    (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g) (e : ComplexChart n M)
    {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχt : tsupport χ ⊆ e.val.target) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hχf : ∀ x ∈ tsupport f, ∀ᶠ y in 𝓝 x, chartExtend e χ y = 1)
    {v : ℕ → M → ℝ} (hv : ∀ i, ChartSmooth (n := n) (v i)) (hv0 : ∀ i x, 0 ≤ v i x)
    (hv1 : ∀ i x, v i x ≤ 1)
    (hpsh : ∀ i (e' : ComplexChart n M) z, z ∈ e'.val.target →
      chartExtend e χ (e'.val.symm z) ≠ 0 → CoefficientSemipositive ((ddcForm (v i)
        (hv i)).coeff e' z))
    (hU : ∀ x, chartExtend e χ x ≠ 0 →
      Tendsto (fun i => elMirCutoff (v i x)) atTop (𝓝 (E.indicator (fun _ => (1 : ℝ)) x)))
    (hD : ∀ x, f x ≠ 0 → Tendsto (fun i => deriv elMirCutoff (v i x)) atTop (𝓝 0)) :
    restrictCurrent w T hT E (closedTestForm f g hf hg k β) = 0 := by
  classical
  set hh := chartSmooth_chartExtend e hχ hχc hχt
  set h := chartExtend e χ with h_def
  have hh0 : ∀ x, 0 ≤ h x := chartExtend_nonneg hχ0
  have hh1 : ∀ x, h x ≤ 1 := chartExtend_le_one hχ1
  set φ := closedTestForm f g hf hg k β with hφ_def
  -- the cut-offs `Uᵢ = h θ(vᵢ)`
  have hθv : ∀ i, ChartSmooth (n := n) (fun x => elMirCutoff (v i x)) := fun i =>
    chartSmooth_comp_real contDiff_elMirCutoff (hv i)
  set U : ℕ → M → ℝ := fun i x => h x * elMirCutoff (v i x) with hU_def
  have hUs : ∀ i, ChartSmooth (n := n) (U i) := fun i => chartSmooth_mul hh (hθv i)
  have hUC : ∀ i x, |U i x| ≤ 1 := fun i x => by
    rw [abs_le]
    have := hh0 x; have := hh1 x
    have := elMirCutoff_nonneg (v i x); have := elMirCutoff_le_one (v i x)
    constructor <;> nlinarith
  have hUlim : ∀ x, Tendsto (fun i => U i x) atTop (𝓝 (E.indicator h x)) := by
    intro x
    by_cases hx : h x = 0
    · have : E.indicator h x = 0 := by
        by_cases hxE : x ∈ E
        · rw [indicator_of_mem hxE, hx]
        · rw [indicator_of_notMem hxE]
      rw [this]
      simp only [hU_def, hx, zero_mul]
      exact tendsto_const_nhds
    · have := (hU x hx).const_mul (h x)
      have e1 : h x * E.indicator (fun _ => (1 : ℝ)) x = E.indicator h x := by
        by_cases hxE : x ∈ E
        · rw [indicator_of_mem hxE, indicator_of_mem hxE, mul_one]
        · rw [indicator_of_notMem hxE, indicator_of_notMem hxE, mul_zero]
      rwa [e1] at this
  -- `h φ = φ` at chart points
  have hφh : ∀ (e' : ComplexChart n M) z, z ∈ e'.val.target →
      h (e'.val.symm z) • (φ : SmoothRealForm n M (2 * (k + 1))).coeff e' z =
        (φ : SmoothRealForm n M (2 * (k + 1))).coeff e' z := by
    intro e' z hz
    by_cases hx : e'.val.symm z ∈ tsupport f
    · rw [(hχf _ hx).self_of_nhds, one_smul]
    · have h0 := chart_eventuallyEq_zero (N := n) hx (e'.val.map_target hz)
      rw [e'.val.right_inv hz] at h0
      rw [hφ_def, closedTestForm_coeff, exactPair_coeff_eq_zero hf hg hz h0, pi11_zero,
        wedgeProd_cons_zero, smul_zero]
  have hlimit := tendsto_apply_smulTest w T hT hE φ hh hh1 hφh hUs hUC hUlim
  -- the coefficients `aᵢ = f θ'(vᵢ)`
  have hθ'v : ∀ i, ChartSmooth (n := n) (fun x => deriv elMirCutoff (v i x)) := fun i =>
    chartSmooth_comp_real contDiff_deriv_elMirCutoff (hv i)
  set a : ℕ → M → ℝ := fun i x => f x * deriv elMirCutoff (v i x) with ha_def
  have has : ∀ i, ChartSmooth (n := n) (a i) := fun i => chartSmooth_mul hf (hθ'v i)
  -- Leibniz and the chain rule
  have hLeib : ∀ i, T (smulTest (U i) (hUs i) φ) =
      -T (slotForm (smulFun (a i) (has i) (exactPair (v i) g (hv i) hg)) k β) := by
    intro i
    rw [hφ_def, apply_smulTest_closedTestForm hT hTc (hUs i) hf hg β, ← slotForm_smulFun]
    congr 1
    refine apply_slotForm_congr' hT β fun e' z hz => ?_
    rw [smulFun_coeff, smulFun_coeff]
    by_cases hfx : f (e'.val.symm z) = 0
    · simp [hfx, ha_def]
    · have hx : e'.val.symm z ∈ tsupport f := subset_tsupport _ hfx
      have hev : ∀ᶠ y in 𝓝 z, h (e'.val.symm y) = 1 := by
        have hc : ContinuousAt e'.val.symm z := e'.val.continuousAt_symm hz
        exact hc.eventually (hχf _ hx)
      have heq : (fun y => U i (e'.val.symm y)) =ᶠ[𝓝 z]
          fun y => elMirCutoff (v i (e'.val.symm y)) := by
        filter_upwards [hev] with y hy
        simp only [hU_def, hy, one_mul]
      rw [exactPair_coeff_eq_deriv_smul contDiff_elMirCutoff (hUs i) (hv i) hg e' hz heq,
        smul_smul]
  -- Cauchy--Schwarz
  have hah : ∀ i x, a i x ≠ 0 → h x = 1 := fun i x hax =>
    (hχf x (subset_tsupport _ (left_ne_zero_of_mul hax))).self_of_nhds
  have hCS : ∀ i, T (slotForm (smulFun (a i) (has i) (exactPair (v i) g (hv i) hg)) k β) ^ 2 ≤
      4 * T (slotForm (smulFun h hh (gradForm (v i) (hv i))) k β) *
        T (slotForm (smulFun (fun x => a i x * a i x) (chartSmooth_mul (has i) (has i))
          (gradForm g hg)) k β) := fun i =>
    sq_apply_slotForm_le hT hβ (hv i) hg (has i) hh hh0 (hah i)
  -- the uniform bound
  obtain ⟨B, hB0, hB⟩ := exists_ddcForm_le_smul w hh
  have hbound : ∀ i, T (slotForm (smulFun h hh (gradForm (v i) (hv i))) k β) ≤
      Real.pi * B * T (slotForm w.form.val k β) := fun i =>
    apply_slotForm_gradForm_le hT hTc hβ w e hχ hχc hχt hχ0 hB0 hB (hv i) (hv0 i) (hv1 i) (hpsh i)
  -- the second factor tends to zero
  obtain ⟨Cθ, hCθ0, hCθ⟩ := exists_abs_deriv_elMirCutoff_le
  set Cf := ‖(⟨f, ChartSmooth.continuous hf⟩ : C(M, ℝ))‖
  have hfC : ∀ x, |f x| ≤ Cf := fun x => by
    simpa [Real.norm_eq_abs] using (⟨f, ChartSmooth.continuous hf⟩ : C(M, ℝ)).norm_coe_le_norm x
  have haC : ∀ i x, |a i x * a i x| ≤ (Cf * Cθ) * (Cf * Cθ) := fun i x => by
    have h1 : |a i x| ≤ Cf * Cθ := by
      rw [ha_def, abs_mul]
      exact mul_le_mul (hfC x) (hCθ _ ⟨hv0 i x, hv1 i x⟩) (abs_nonneg _)
        ((abs_nonneg _).trans (hfC x))
    rw [abs_mul]
    exact mul_le_mul h1 h1 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have haLim : ∀ x, Tendsto (fun i => a i x * a i x) atTop (𝓝 0) := by
    intro x
    by_cases hfx : f x = 0
    · simp only [ha_def, hfx, zero_mul]
      exact tendsto_const_nhds
    · have := ((hD x hfx).const_mul (f x))
      rw [mul_zero] at this
      simpa using this.mul this
  have hsecond := tendsto_apply_slotForm_smulFun w hT hβ
    (γ := gradForm g hg) (fun e z hz u => gradForm_coeff_line_nonneg hg e hz u)
    (F := fun i x => a i x * a i x) (fun i => chartSmooth_mul (has i) (has i)) haC haLim
  -- conclusion
  have hK0 : 0 ≤ T (slotForm (smulFun h hh (gradForm (v 0) (hv 0))) k β) :=
    apply_slotForm_nonneg hT hβ fun e z hz u => by
      rw [smulFun_coeff, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (hh0 _) (gradForm_coeff_line_nonneg (hv 0) e hz u)
  have hK : 0 ≤ Real.pi * B * T (slotForm w.form.val k β) := hK0.trans (hbound 0)
  have hsecond0 : ∀ i, 0 ≤ T (slotForm (smulFun (fun x => a i x * a i x)
      (chartSmooth_mul (has i) (has i)) (gradForm g hg)) k β) := fun i =>
    apply_slotForm_nonneg hT hβ fun e z hz u => by
      rw [smulFun_coeff, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (mul_self_nonneg _) (gradForm_coeff_line_nonneg hg e hz u)
  have hle : ∀ i, T (slotForm (smulFun (a i) (has i) (exactPair (v i) g (hv i) hg)) k β) ^ 2 ≤
      (4 * (Real.pi * B * T (slotForm w.form.val k β))) *
        T (slotForm (smulFun (fun x => a i x * a i x) (chartSmooth_mul (has i) (has i))
          (gradForm g hg)) k β) := fun i =>
    (hCS i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound i) (by norm_num)) (hsecond0 i))
  have hzero := tendsto_zero_of_sq_le hle hsecond
  have hneg := hzero.neg
  rw [neg_zero] at hneg
  have hcomb : Tendsto (fun i => T (smulTest (U i) (hUs i) φ)) atTop (𝓝 0) := by
    simp_rw [hLeib]
    exact hneg
  exact tendsto_nhds_unique hlimit hcomb

end ElMir

end SGPT.Foundations.Analysis.Pending.SkodaElMirEstimate
