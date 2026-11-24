/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DirectionalLeviDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IntegrationCurrentChart
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.TestLeviPairing

/-!
# From positivity of a `(1,1)`-current to the Levi form of its chart potentials

Source: Demailly, CADG III.1 (a `(1,1)`-current is positive iff it is nonnegative on the forms
`χ · i dz₂ ∧ dzBar₂ ∧ ⋯ ∧ i dzₙ ∧ dzBarₙ` in unitary coordinates, III.1.8) and I.5.8 (nonnegative
distributional Levi form ⇒ plurisubharmonic, `Pending.PshRepresentative`).  TN.4 plan, step B6,
finding F6 route (i), the positivity-to-Levi link (the proof of Boucksom's mass estimate,
"LINK SCRIPT"): a positive current `R - σ` with `R = θ₀ + ddᶜV` (in the weak sense below) has, in
every chart, a potential `V ∘ e⁻¹` whose distribution is locally `(θ₀ - σ)`-psh; the chart gluing
(`ThetaPshChartLimitGluing`) then produces a Kähler current.

## The test forms

For a chart `e`, a cut-off `ψ ∈ 𝓓(e.target)`, a unit vector `a` and `φ ∈ 𝓓(e.target)`,
`leviTest e ψ a φ = (φ ∘ e) · β_a^q` with `β_a = ddᶜ(ψ q_a ∘ e)` (`leviSlot`),
`q_a(z) = ‖z‖² - |⟨a, z⟩|²` (`DirectionalLeviDensity.perpQuadratic`).  `β_a` is a closed real
`(1,1)`-form on the whole manifold; it is semipositive only where `ψ ≡ 1`, so positivity of the
    test
form is proved POINTWISE (`leviTest_mem_positiveCone`, where `φ ∘ e ≠ 0` the cut-off is `≡ 1` and
`ddᶜ q_a ≥ 0` in every chart), not through `SlotTestForms.slotForm_mem_positiveCone`.

* `smoothCurrent_leviTest`: if `θ = ddᶜρ` on `supp φ`, then
  `[X] ∧ θ (leviTest e ψ a φ) = (q!/π^{q+1}) ∫ φ · L_ρ(a)` (flat core
  `DirectionalLeviDensity.topDensity_smoothDDC_perpQuadratic`, chart reading
  `IntegrationCurrentChart.integrationCurrent_apply_eq_setIntegral`).
* `isLocallyThetaPshDistribution_of_leviTest` (the link): if `P` is positive and
  `P η = [X] ∧ θ (η) + (q!/π^{q+1}) · Levi_a(T_e)(φ)` on these test forms, then every `T_e` is
    locally
  `θ`-psh as a distribution.
* `isLocallyThetaPshDistribution_sub_of_leviTest`: the same for `P = R - [X] ∧ σ` and `θ = θ₀ - σ`.
* `exists_kahlerCurrent_of_leviTest`: with chart weak limits, a Kähler current in `{θ₀}` with lower
  bound `ω_δ` (`ThetaPshChartLimitGluing.exists_kahlerCurrent_of_isChartLimit`).

The identity `R η = [X] ∧ θ₀ (η) + (q!/π^{q+1}) · Levi_a(T_e)(φ)` is what `R = θ₀ + ddᶜV` means on
these test forms (`ddᶜ η = ddᶜ(φ ∘ e) ∧ β_a^q`, whose density is `(q!/π^{q+1}) L_φ(a)` by the same
flat core); for the limit current of B6 it is step (i-1) of the plan.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions InnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.PositivityLeviLink

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent TopDegreeDensity
  SmoothCurrentTraceMeasure CurrentTraceMeasure SmoothDDCForm ChartPartition SlotTestForms
  ManifoldTubePositivity DirectionalLeviDensity ThetaPshChartLimitGluing IntegrationCurrentChart
  SmoothCurrentClosedness

/-! ### Distribution helpers -/

section Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {Ω U : Opens E}

/-- The Levi operator commutes with restriction to a smaller open set. -/
theorem distributionalLeviCLM_restrictDistribution (T : 𝓓'(Ω, ℝ)) (hUΩ : U ≤ Ω) (v : E)
    (φ : 𝓓(U, ℝ)) :
    distributionalLeviCLM v (restrictDistribution T hUΩ) φ =
      distributionalLeviCLM v T (TestFunction.monoCLM ℝ φ) := by
  have hcoe := testFunction_inclusion_coe hUΩ φ
  rw [distributionalLeviCLM_apply, distributionalLeviCLM_apply, restrictDistribution_apply,
    restrictDistribution_apply]
  congr 2
  · congr 1
    apply TestFunction.ext
    intro x
    rw [testFunction_lineDerivCLM_lineDerivCLM_apply,
      congrFun (testFunction_inclusion_coe hUΩ _) x,
      testFunction_lineDerivCLM_lineDerivCLM_apply, hcoe]
  · congr 1
    apply TestFunction.ext
    intro x
    rw [testFunction_lineDerivCLM_lineDerivCLM_apply,
      congrFun (testFunction_inclusion_coe hUΩ _) x,
      testFunction_lineDerivCLM_lineDerivCLM_apply, hcoe]

/-- The Levi operator is quadratic in the direction. -/
theorem distributionalLeviCLM_smul_apply (T : 𝓓'(Ω, ℝ)) (c : ℝ) (v : E) (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM (c • v) T φ = c ^ 2 * distributionalLeviCLM v T φ := by
  have hI : Complex.I • (c • v) = c • (Complex.I • v) := smul_comm _ _ _
  rw [distributionalLeviCLM_apply, distributionalLeviCLM_apply, hI,
    TestFunction.lineDerivCLM_smul, TestFunction.lineDerivCLM_smul]
  simp only [smul_apply, map_smul, smul_eq_mul]
  ring

end Distributions

/-! ### The cut-off quadratic and the slot form `β_a` -/

section Slot

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X]

omit [IsComplexManifold (q + 1) X] in
theorem contDiff_cutQuadratic {e : ComplexChart (q + 1) X} (ψ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (q + 1)) : ContDiff ℝ ∞ (fun z => ψ z * perpQuadratic a z) :=
  ψ.contDiff.mul (contDiff_perpQuadratic a)

omit [IsComplexManifold (q + 1) X] in
theorem tsupport_cutQuadratic_subset {e : ComplexChart (q + 1) X} (ψ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (q + 1)) :
    tsupport (fun z => ψ z * perpQuadratic a z) ⊆ tsupport ψ :=
  tsupport_mul_subset_left

theorem chartSmooth_cutQuadratic (e : ComplexChart (q + 1) X) (ψ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (q + 1)) :
    ChartSmooth (n := q + 1) (chartExtend e fun z => ψ z * perpQuadratic a z) :=
  chartSmooth_chartExtend e (contDiff_cutQuadratic ψ a)
    (ψ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_cutQuadratic_subset ψ a))
    ((tsupport_cutQuadratic_subset ψ a).trans ψ.tsupport_subset)

/-- **The slot form** `β_a = ddᶜ(ψ q_a ∘ e)`, a closed real `(1,1)`-form on the manifold. -/
def leviSlot (e : ComplexChart (q + 1) X) (ψ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) :
    ClosedRealOneOneForm (q + 1) X :=
  ddcClosedForm (chartExtend e fun z => ψ z * perpQuadratic a z) (chartSmooth_cutQuadratic e ψ a)

/-- Where the cut-off is `≡ 1`, the slot form is `ddᶜ q_a` in the chart `e`. -/
theorem leviSlot_coeff_eq {e : ComplexChart (q + 1) X} {ψ : 𝓓(chartTarget e, ℝ)}
    {a : ComplexModel (q + 1)} {z : ComplexModel (q + 1)} (hz : z ∈ e.val.target)
    (hψ : (ψ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] 1) :
    (leviSlot e ψ a).val.coeff e z = smoothDDC (perpQuadratic a) z := by
  rw [leviSlot, ddcClosedForm_coeff, smoothDDC_congr (chartExtend_eventuallyEq hz)]
  apply smoothDDC_congr
  filter_upwards [hψ] with y hy
  simp only [hy, Pi.one_apply, one_mul]

/-- The Levi form of `q_a` is `‖v‖² - |⟨a, v⟩|²`. -/
theorem leviForm_perpQuadratic (a z v : ComplexModel (q + 1)) :
    leviForm (perpQuadratic a) z v = ‖v‖ ^ 2 - ‖⟪a, v⟫_ℂ‖ ^ 2 := by
  have hsplit : perpQuadratic a = (fun y : ComplexModel (q + 1) => ‖y‖ ^ 2) +
      (-1 : ℝ) • fun y : ComplexModel (q + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2 := by
    funext y
    simp [perpQuadratic, sub_eq_add_neg]
  have h1 : ContDiffAt ℝ 2 (fun y : ComplexModel (q + 1) => ‖y‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun y : ComplexModel (q + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2) z :=
    (contDiff_normSq_inner a).contDiffAt
  rw [hsplit, leviForm_add (v := (-1 : ℝ) • fun y : ComplexModel (q + 1) => ‖⟪a, y⟫_ℂ‖ ^ 2) h1
    (h2.const_smul (-1 : ℝ)), leviForm_smul h2]
  simp only [leviForm, realHessian_norm_sq, realHessian_normSq_inner, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  have hc : ∀ w : ℂ, (w * (starRingEnd ℂ) w).re = ‖w‖ ^ 2 := fun w => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hII : (Complex.I * ⟪a, v⟫_ℂ * (starRingEnd ℂ) (Complex.I * ⟪a, v⟫_ℂ)).re =
      ‖⟪a, v⟫_ℂ‖ ^ 2 := by
    rw [hc, norm_mul, Complex.norm_I, one_mul]
  rw [hII, hc]
  ring

/-- `ddᶜ q_a` is semipositive for `‖a‖ ≤ 1`. -/
theorem coefficientSemipositive_smoothDDC_perpQuadratic {a : ComplexModel (q + 1)}
    (ha : ‖a‖ ≤ 1) (z : ComplexModel (q + 1)) :
    CoefficientSemipositive (smoothDDC (perpQuadratic a) z) := by
  intro v
  rw [smoothDDC_complexDiagonal_eq_leviForm (contDiff_perpQuadratic a).contDiffAt,
    leviForm_perpQuadratic]
  apply div_nonneg _ Real.pi_pos.le
  have h := norm_inner_le_norm (𝕜 := ℂ) a v
  have h' : ‖⟪a, v⟫_ℂ‖ ≤ ‖v‖ := h.trans (by nlinarith [norm_nonneg a, norm_nonneg v])
  nlinarith [norm_nonneg ⟪a, v⟫_ℂ]

/-- At a point of `X` where the cut-off is `≡ 1` (read in `e`), the slot form is semipositive in
EVERY chart (the chart transition is complex linear). -/
theorem isSemipositiveOneOne_leviSlot_coeff {e : ComplexChart (q + 1) X}
    {ψ : 𝓓(chartTarget e, ℝ)} {a : ComplexModel (q + 1)} (ha : ‖a‖ ≤ 1) {x : X}
    (hx : x ∈ e.val.source) (hψ : (ψ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 (e.val x)] 1)
    (e' : ComplexChart (q + 1) X) {z : ComplexModel (q + 1)} (hz : z ∈ e'.val.target)
    (hzx : e'.val.symm z = x) :
    IsSemipositiveOneOne ((leviSlot e ψ a).val.coeff e' z) := by
  refine ⟨(leviSlot e ψ a).2.2 e' z hz, ?_⟩
  have hzs : z ∈ (chartTransition e' e).source := ⟨hz, by
    change e'.val.symm z ∈ e.val.source
    rw [hzx]
    exact hx⟩
  have htr : chartTransition e' e z = e.val x := by
    rw [chartTransition_apply_eq, hzx]
  rw [coeff_eq_compContinuousLinearMap _ hzs, htr,
    leviSlot_coeff_eq (e.val.map_source hx) hψ]
  intro v
  have h := coefficientSemipositive_smoothDDC_perpQuadratic ha (e.val x)
    (chartTransitionDerivative e' e z v)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  convert h using 2
  ext i
  fin_cases i <;> simp [chartTransitionDerivative_complex_smul e' e z hzs]

end Slot

/-! ### The test forms `(φ ∘ e) · β_a^q` -/

section TestForm

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X]

theorem chartSmooth_testFunction (e : ComplexChart (q + 1) X) (φ : 𝓓(chartTarget e, ℝ)) :
    ChartSmooth (n := q + 1) (chartExtend e φ) :=
  chartSmooth_chartExtend e φ.contDiff φ.hasCompactSupport φ.tsupport_subset

/-- The power `β_a^q` as a test form. -/
def leviSlotPow (e : ComplexChart (q + 1) X) (ψ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (q + 1)) : testSpace (q + 1) X q :=
  ⟨formPow (leviSlot e ψ a).val q, formPow_mem_testSpace (leviSlot e ψ a).2.2 q⟩

/-- **The Levi test form** `(φ ∘ e) · β_a^q`, `β_a = ddᶜ(ψ q_a ∘ e)`. -/
def leviTest (e : ComplexChart (q + 1) X) (ψ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (φ : 𝓓(chartTarget e, ℝ)) : testSpace (q + 1) X q :=
  smulTest (chartExtend e φ) (chartSmooth_testFunction e φ) (leviSlotPow e ψ a)

theorem leviTest_coeff (e : ComplexChart (q + 1) X) (ψ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (q + 1)) (φ : 𝓓(chartTarget e, ℝ)) (e' : ComplexChart (q + 1) X)
    (z : ComplexModel (q + 1)) :
    ((leviTest e ψ a φ : testSpace (q + 1) X q) : SmoothRealForm (q + 1) X (2 * q)).coeff e' z =
      chartExtend e φ (e'.val.symm z) • formPower ((leviSlot e ψ a).val.coeff e' z) q := by
  change (smulFun (chartExtend e φ) (chartSmooth_testFunction e φ)
    (formPow (leviSlot e ψ a).val q)).coeff e' z = _
  rw [smulFun_coeff, formPow_coeff]

/-- **Positivity of the Levi test form**, pointwise: where `φ ∘ e ≠ 0` the cut-off is `≡ 1`, so
the slot form is semipositive there in every chart. -/
theorem leviTest_mem_positiveCone {e : ComplexChart (q + 1) X} {ψ : 𝓓(chartTarget e, ℝ)}
    {a : ComplexModel (q + 1)} (ha : ‖a‖ ≤ 1) {φ : 𝓓(chartTarget e, ℝ)} (hφ : ∀ z, 0 ≤ φ z)
    (hψ : ∀ z ∈ tsupport φ, (ψ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] 1) :
    leviTest e ψ a φ ∈ positiveCone (q + 1) X q := by
  intro e' z hz
  change ((leviTest e ψ a φ : testSpace (q + 1) X q) :
    SmoothRealForm (q + 1) X (2 * q)).coeff e' z ∈ spCone q
  rw [leviTest_coeff]
  by_cases h0 : chartExtend e φ (e'.val.symm z) = 0
  · rw [h0, zero_smul]
    exact (spCone q).zero_mem
  · have hxs : e'.val.symm z ∈ e.val.source := by
      by_contra hns
      exact h0 (chartExtend_of_notMem hns)
    have hsupp : e.val (e'.val.symm z) ∈ tsupport φ := by
      apply subset_tsupport
      rw [chartExtend_of_mem hxs] at h0
      exact h0
    exact smul_mem_spCone (formPower_mem_spCone
      (isSemipositiveOneOne_leviSlot_coeff ha hxs (hψ _ hsupp) e' hz rfl) q)
      (chartExtend_nonneg hφ _)

end TestForm

/-! ### The chart reading of `[X] ∧ θ` on the Levi test forms -/

section Chart

/-- Moving the last of `q + 1` slots to the front does not change the mixed density. -/
theorem actualMixedTopDensity_append_one {q : ℕ} (α : Fin q → RealForm (q + 1) 2)
    (γ : Fin 1 → RealForm (q + 1) 2) :
    actualMixedTopDensity (Fin.append α γ) =
      actualMixedTopDensity (Fin.cons (γ 0) α : Fin (q + 1) → RealForm (q + 1) 2) := by
  have h : (Fin.append α γ : Fin (q + 1) → RealForm (q + 1) 2) =
      fun i => (Fin.cons (γ 0) α : Fin (q + 1) → RealForm (q + 1) 2) (finRotate (q + 1) i) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [finRotate_last, Fin.cons_zero]
      have hl : (Fin.last q : Fin (q + 1)) = Fin.natAdd q (0 : Fin 1) := by
        ext
        simp
      rw [hl, Fin.append_right]
    · rw [finRotate_apply, Fin.coeSucc_eq_succ, Fin.cons_succ]
      exact Fin.append_left α γ j
  rw [h, actualMixedTopDensity_perm]

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem leviTest_eq_smulTest (e : ComplexChart (q + 1) X) (ψ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (q + 1)) (φ : 𝓓(chartTarget e, ℝ)) :
    leviTest e ψ a φ =
      smulTest (chartExtend e φ) (chartSmooth_testFunction e φ) (leviSlotPow e ψ a) := rfl

/-- **The smooth current `[X] ∧ θ` on a Levi test form**: if `θ = ddᶜρ` in the chart on the
support of `φ` and the cut-off is `≡ 1` there, then
`[X] ∧ θ ((φ ∘ e) β_a^q) = (q!/π^{q+1}) ∫ φ · L_ρ(a)`. -/
theorem smoothCurrent_leviTest (w : KahlerBackground (q + 1) X)
    (θ : ClosedRealOneOneForm (q + 1) X) {e : ComplexChart (q + 1) X}
    {ψ : 𝓓(chartTarget e, ℝ)} {a : ComplexModel (q + 1)} (ha : ‖a‖ = 1)
    {φ : 𝓓(chartTarget e, ℝ)}
    (hψ : ∀ z ∈ tsupport φ, (ψ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] 1)
    {ρ : ComplexModel (q + 1) → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hθ : ∀ z ∈ tsupport φ, θ.val.coeff e z = smoothDDC ρ z) :
    smoothCurrent (q := q) (p := 1) w ![θ] (leviTest e ψ a φ) =
      ((q.factorial : ℝ) / Real.pi ^ (q + 1)) * ∫ z, φ z * leviForm ρ z a := by
  set K := tsupport (φ : ComplexModel (q + 1) → ℝ) with hK
  have hKt : K ⊆ e.val.target := φ.tsupport_subset
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hcoe := chainTestLM_smulTest 1 (fun j => (![θ] j).val) (fun j => (![θ] j).2.2) q
    (chartExtend e φ) (chartSmooth_testFunction e φ) (leviSlotPow e ψ a)
  rw [smoothCurrent_apply, integrationCurrent_apply_eq_setIntegral w e hKm hKt]
  · rw [leviTest_eq_smulTest, hcoe]
    have hpt : ∀ z ∈ K, topDensity ((smulFun (chartExtend e φ) (chartSmooth_testFunction e φ)
        ((chainTestLM 1 (fun j => (![θ] j).val) (fun j => (![θ] j).2.2) q
          (leviSlotPow e ψ a) : testSpace (q + 1) X (q + 1)) :
            SmoothRealForm (q + 1) X (2 * (q + 1)))).coeff e z) =
        ((q.factorial : ℝ) / Real.pi ^ (q + 1)) * (φ z * leviForm ρ z a) := by
      intro z hz
      have hzt := hKt hz
      have hpow : ((leviSlotPow e ψ a : testSpace (q + 1) X q) :
          SmoothRealForm (q + 1) X (2 * q)).coeff e z =
            wedgeProd q (fun _ => (leviSlot e ψ a).val.coeff e z) := by
        change (formPow (leviSlot e ψ a).val q).coeff e z = _
        rw [formPow_coeff, formPower_eq_wedgeProd]
      rw [smulFun_coeff, chartExtend_symm hzt, topDensity_smul,
        chainTestLM_coeff 1 _ _ q _ e z hpow, topDensity_wedgeProd,
        actualMixedTopDensity_append_one, ← topDensity_wedgeProd]
      simp only [Matrix.cons_val_zero]
      rw [hθ z hz, leviSlot_coeff_eq hzt (hψ z hz),
        topDensity_smoothDDC_perpQuadratic (hρ.contDiffAt) a ha]
      ring
    rw [setIntegral_congr_fun hKm hpt, integral_const_mul]
    congr 1
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  · intro x hx
    rw [leviTest_eq_smulTest, hcoe, topRatio_smulFun, chartExtend_eq_zero_of_notMem_image hx,
      zero_mul]

end Chart

/-! ### The link -/

section Link

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The Levi identity on the test forms**: `P ((φ ∘ e) β_a^q) = [X] ∧ θ ((φ ∘ e) β_a^q) +
(q!/π^{q+1}) · Levi_a(T_e)(φ)` for every chart, cut-off `ψ ≡ 1` near `supp φ`, unit `a` and
`φ ≥ 0`.  For `P = θ + ddᶜV` and `T_e = [V ∘ e⁻¹]` this is
    `∫ V ddᶜη = (q!/π^{q+1}) ∫ V∘e⁻¹ L_φ(a)`. -/
def LeviTestIdentity (w : KahlerBackground (q + 1) X) (P : ProductCurrent (q + 1) X q)
    (θ : ClosedRealOneOneForm (q + 1) X) (T : ∀ e : ComplexChart (q + 1) X, 𝓓'(chartTarget e, ℝ)) :
    Prop :=
  ∀ (e : ComplexChart (q + 1) X) (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)),
    ‖a‖ = 1 → (∀ z, 0 ≤ φ z) → (∀ z ∈ tsupport φ, (ψ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] 1) →
      P (leviTest e ψ a φ) = smoothCurrent (q := q) (p := 1) w ![θ] (leviTest e ψ a φ) +
        ((q.factorial : ℝ) / Real.pi ^ (q + 1)) * distributionalLeviCLM a (T e) φ

/-- **The positivity-to-Levi link.**  If `P` is a positive current and satisfies the Levi identity
with `θ` (which has smooth local potentials) and the chart distributions `T_e`, then every `T_e` is
locally `θ`-psh as a distribution. -/
theorem isLocallyThetaPshDistribution_of_leviTest (w : KahlerBackground (q + 1) X)
    {P : ProductCurrent (q + 1) X q} (hP : IsPositive P) (θ : ClosedRealOneOneForm (q + 1) X)
    (hθ : HasSmoothLocalPotentials θ.val)
    (T : ∀ e : ComplexChart (q + 1) X, 𝓓'(chartTarget e, ℝ)) (hPT : LeviTestIdentity w P θ T)
    (e : ComplexChart (q + 1) X) : IsLocallyThetaPshDistribution volume θ.val e (T e) := by
  intro z₀ hz₀
  obtain ⟨W₀, ρ, hz₀W₀, hpot⟩ := hθ e z₀ hz₀
  obtain ⟨r, hr, hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hpot.1.mem_nhds hz₀W₀)
  let Ω₀ : Opens (ComplexModel (q + 1)) := ⟨W₀, hpot.1⟩
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact (Ω := Ω₀)
    (isCompact_closedBall z₀ r) hrW
  have hχ1' : ∀ z ∈ Metric.closedBall z₀ r, (χ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] 1 :=
    fun z hz => (hχ1.filter_mono (nhds_le_nhdsSet hz)).mono fun y hy => by simpa using hy
  have hΩ₀ : Ω₀ ≤ chartTarget e := hpot.2.1
  let ψ : 𝓓(chartTarget e, ℝ) := TestFunction.monoCLM ℝ χ
  have hψv : (ψ : ComplexModel (q + 1) → ℝ) = χ := testFunction_inclusion_coe hΩ₀ χ
  set ρ' : ComplexModel (q + 1) → ℝ := fun z => χ z * ρ z with hρ'def
  have hρ' : ContDiff ℝ ∞ ρ' :=
    contDiff_mul_of_tsupport_subset hpot.1 χ.contDiff χ.tsupport_subset hpot.2.2.1
  have hρ'2 : ContDiff ℝ 2 ρ' := hρ'.of_le (WithTop.coe_le_coe.mpr le_top)
  have hρρ' : ∀ z ∈ Metric.closedBall z₀ r, ρ' =ᶠ[𝓝 z] ρ := fun z hz => by
    filter_upwards [hχ1' z hz] with y hy
    simp only [hρ'def, hy, Pi.one_apply, one_mul]
  have hθρ' : ∀ z ∈ Metric.closedBall z₀ r, θ.val.coeff e z = smoothDDC ρ' z := fun z hz => by
    rw [smoothDDC_congr (hρρ' z hz)]
    exact (hpot.2.2.2 (hrW hz)).symm
  let W : Opens (ComplexModel (q + 1)) := ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩
  have hWB : (W : Set (ComplexModel (q + 1))) ⊆ Metric.closedBall z₀ r :=
    Metric.ball_subset_closedBall
  have hW : W ≤ chartTarget e := fun z hz => hpot.2.1 (hrW (hWB hz))
  have hloc : LocallyIntegrableOn ρ' W volume :=
    hρ'.continuous.locallyIntegrable.locallyIntegrableOn _
  refine ⟨W, hW, ρ', hloc, Metric.mem_ball_self hr,
    ⟨Metric.isOpen_ball, fun z hz => hW hz, hρ'.contDiffOn, fun z hz => (hθρ' z (hWB hz)).symm⟩,
      ?_⟩
  -- the Levi form, first for unit vectors
  have hunit : ∀ a : ComplexModel (q + 1), ‖a‖ = 1 → ∀ φ' : 𝓓(W, ℝ), (∀ x, 0 ≤ φ' x) →
      0 ≤ distributionalLeviCLM a
        (restrictDistribution (T e) hW + regularDistribution volume ρ' hloc) φ' := by
    intro a ha φ' hφ'
    set φ : 𝓓(chartTarget e, ℝ) := TestFunction.monoCLM ℝ φ' with hφdef
    have hφv : (φ : ComplexModel (q + 1) → ℝ) = φ' := testFunction_inclusion_coe hW φ'
    have hsupp : tsupport (φ : ComplexModel (q + 1) → ℝ) ⊆ Metric.closedBall z₀ r := by
      rw [hφv]
      exact φ'.tsupport_subset.trans hWB
    have hφ0 : ∀ z, 0 ≤ φ z := fun z => by rw [hφv]; exact hφ' z
    have hψ1 : ∀ z ∈ tsupport φ, (ψ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] 1 := fun z hz => by
      rw [hψv]
      exact hχ1' z (hsupp hz)
    have hpos := hP _ (leviTest_mem_positiveCone ha.le hφ0 hψ1)
    rw [hPT e ψ φ a ha hφ0 hψ1,
      smoothCurrent_leviTest w θ ha hψ1 hρ'2 fun z hz => hθρ' z (hsupp hz)] at hpos
    have hc : 0 < (q.factorial : ℝ) / Real.pi ^ (q + 1) := by
      have := q.factorial_pos
      positivity
    rw [map_add, add_apply, distributionalLeviCLM_restrictDistribution,
      distributionalLeviCLM_regularDistribution hρ'2, regularDistribution_apply]
    have hint : ∫ x, φ' x * leviForm ρ' x a = ∫ z, φ z * leviForm ρ' z a := by
      rw [hφv]
    rw [hint, ← hφdef]
    nlinarith
  intro v φ' hφ'
  by_cases hv : v = 0
  · have h0 : v = (0 : ℝ) • v := by rw [hv, smul_zero]
    rw [h0, distributionalLeviCLM_smul_apply]
    simp
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hva : v = ‖v‖ • ((‖v‖⁻¹ : ℝ) • v) := by
      rw [smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
    have ha : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hvn.ne']
    rw [hva, distributionalLeviCLM_smul_apply]
    exact mul_nonneg (sq_nonneg _) (hunit _ ha φ' hφ')

/-- `[X] ∧ θ₀ - [X] ∧ σ = [X] ∧ (θ₀ - σ)`. -/
theorem smoothCurrent_sub_apply (w : KahlerBackground (q + 1) X)
    (θ₀ σ : ClosedRealOneOneForm (q + 1) X) (η : testSpace (q + 1) X q) :
    smoothCurrent (q := q) (p := 1) w ![θ₀] η - smoothCurrent (q := q) (p := 1) w ![σ] η =
      smoothCurrent (q := q) (p := 1) w ![θ₀ - σ] η := by
  rw [smoothCurrent_apply, smoothCurrent_apply, smoothCurrent_apply, ← map_sub]
  congr 1
  apply Subtype.ext
  apply smoothRealForm_ext
  intro e z
  change coordinateWedge ((η : SmoothRealForm (q + 1) X (2 * q)).coeff e z) (θ₀.val.coeff e z) -
      coordinateWedge ((η : SmoothRealForm (q + 1) X (2 * q)).coeff e z) (σ.val.coeff e z) =
    coordinateWedge ((η : SmoothRealForm (q + 1) X (2 * q)).coeff e z) ((θ₀ - σ).val.coeff e z)
  rw [sub_eq_add_neg θ₀ σ, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
    coordinateWedge_add_right, ← neg_one_smul ℝ (σ.val.coeff e z),
    coordinateWedge_smul_right]
  rw [sub_eq_add_neg]
  exact congrArg _ (neg_one_smul ℝ _).symm

/-- **The link for `R - [X] ∧ σ`**: if `R - [X] ∧ σ` is positive and `R` satisfies the Levi
    identity
with `θ₀`, every `T_e` is locally `(θ₀ - σ)`-psh. -/
theorem isLocallyThetaPshDistribution_sub_of_leviTest (w : KahlerBackground (q + 1) X)
    {R : ProductCurrent (q + 1) X q} (θ₀ σ : ClosedRealOneOneForm (q + 1) X)
    (hR : IsPositive (R - smoothCurrent (q := q) (p := 1) w ![σ]))
    (hθ : HasSmoothLocalPotentials (θ₀ - σ).val)
    (T : ∀ e : ComplexChart (q + 1) X, 𝓓'(chartTarget e, ℝ)) (hRT : LeviTestIdentity w R θ₀ T)
    (e : ComplexChart (q + 1) X) : IsLocallyThetaPshDistribution volume (θ₀ - σ).val e (T e) :=
  isLocallyThetaPshDistribution_of_leviTest w hR (θ₀ - σ) hθ T
    (fun e ψ φ a ha hφ hψ => by
      rw [LinearMap.sub_apply, hRT e ψ φ a ha hφ hψ, ← smoothCurrent_sub_apply]
      ring) e

/-- **F6 closed modulo the Levi identity**: chart weak limits `T_e` of `v_i ∘ e⁻¹`,
    a current `R` with
`R - [X] ∧ ω_δ` positive and the Levi identity for `θ₀` give a Kähler current in `{θ₀}` with lower
bound `ω_δ` whose potential represents every `T_e`. -/
theorem exists_kahlerCurrent_of_leviTest {ι : Type*} {l : Filter ι} [l.NeBot] (v : ι → X → ℝ)
    (w : KahlerBackground (q + 1) X) {R : ProductCurrent (q + 1) X q}
    (θ₀ : ClosedRealOneOneForm (q + 1) X) (ωδ : KahlerBackground (q + 1) X)
    (hR : IsPositive (R - smoothCurrent (q := q) (p := 1) w ![ωδ.form]))
    (hθ : HasSmoothLocalPotentials (θ₀ - ωδ.form).val)
    (T : ∀ e : ComplexChart (q + 1) X, 𝓓'(chartTarget e, ℝ))
    (hT : ∀ e, IsChartLimit volume l v e (T e)) (hRT : LeviTestIdentity w R θ₀ T) :
    ∃ K : NonKahlerLocus.KahlerCurrent (RealBottChern.ofRepresentative θ₀),
      K.representative = θ₀ ∧ K.lowerBound = ωδ ∧ ∀ e : ComplexChart (q + 1) X,
        ∃ hV : LocallyIntegrableOn (fun z => (chartFunction K.potential e z).toReal)
          (chartTarget e) volume,
          T e = regularDistribution volume (fun z => (chartFunction K.potential e z).toReal) hV :=
  exists_kahlerCurrent_of_isChartLimit v θ₀ ωδ T hT
    (isLocallyThetaPshDistribution_sub_of_leviTest w θ₀ ωδ.form hR hθ T hRT)

end Link

/-! ### The Levi identity passes to weak limits -/

section Limit

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The Levi identity is closed under weak limits**: if `P_i → P` and `[X] ∧ θ_i → [X] ∧ θ` on
test forms and `T_{i,e} → T_e` weakly in every chart, the identity for every `i` (eventually) gives
the identity for the limits. -/
theorem LeviTestIdentity.of_tendsto (w : KahlerBackground (q + 1) X) {ι : Type*} {l : Filter ι}
    [l.NeBot] {P : ι → ProductCurrent (q + 1) X q} {P' : ProductCurrent (q + 1) X q}
    {θ : ι → ClosedRealOneOneForm (q + 1) X} {θ' : ClosedRealOneOneForm (q + 1) X}
    {T : ι → ∀ e : ComplexChart (q + 1) X, 𝓓'(chartTarget e, ℝ)}
    {T' : ∀ e : ComplexChart (q + 1) X, 𝓓'(chartTarget e, ℝ)}
    (hP : ∀ η, Tendsto (fun i => P i η) l (𝓝 (P' η)))
    (hθ : ∀ η, Tendsto (fun i => smoothCurrent (q := q) (p := 1) w ![θ i] η) l
      (𝓝 (smoothCurrent (q := q) (p := 1) w ![θ'] η)))
    (hT : ∀ e φ, Tendsto (fun i => T i e φ) l (𝓝 (T' e φ)))
    (h : ∀ᶠ i in l, LeviTestIdentity w (P i) (θ i) (T i)) : LeviTestIdentity w P' θ' T' := by
  intro e ψ φ a ha hφ hψ
  refine tendsto_nhds_unique (hP _) ?_
  have hR := (hθ (leviTest e ψ a φ)).add
    ((PshUltrafilterLimit.tendsto_distributionalLeviCLM (hT e) a φ).const_mul
      ((q.factorial : ℝ) / Real.pi ^ (q + 1)))
  refine hR.congr' ?_
  filter_upwards [h] with i hi
  exact (hi e ψ φ a ha hφ hψ).symm

/-- **The Levi identity for chart weak limits of functions**: if the identity holds for `P_i`,
    `θ_i`
and the regular distributions of `v_i ∘ e⁻¹`, and these converge weakly to `T_e` in every chart, it
holds for the limits. -/
theorem LeviTestIdentity.of_isChartLimit (w : KahlerBackground (q + 1) X) {ι : Type*}
    {l : Filter ι} [l.NeBot] {P : ι → ProductCurrent (q + 1) X q} {P' : ProductCurrent (q + 1) X q}
    {θ : ι → ClosedRealOneOneForm (q + 1) X} {θ' : ClosedRealOneOneForm (q + 1) X}
    (v : ι → X → ℝ)
    (hv : ∀ i (e : ComplexChart (q + 1) X),
      LocallyIntegrableOn (fun z => v i (e.val.symm z)) (chartTarget e) volume)
    {T' : ∀ e : ComplexChart (q + 1) X, 𝓓'(chartTarget e, ℝ)}
    (hP : ∀ η, Tendsto (fun i => P i η) l (𝓝 (P' η)))
    (hθ : ∀ η, Tendsto (fun i => smoothCurrent (q := q) (p := 1) w ![θ i] η) l
      (𝓝 (smoothCurrent (q := q) (p := 1) w ![θ'] η)))
    (hT : ∀ e, IsChartLimit volume l v e (T' e))
    (h : ∀ᶠ i in l, LeviTestIdentity w (P i) (θ i)
      (fun e => regularDistribution volume (fun z => v i (e.val.symm z)) (hv i e))) :
    LeviTestIdentity w P' θ' T' :=
  LeviTestIdentity.of_tendsto w hP hθ (fun e φ => by
    simpa only [regularDistribution_apply] using hT e φ) h

end Limit

end SGPT.Foundations.Analysis.Pending.PositivityLeviLink
