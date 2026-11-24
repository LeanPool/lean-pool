/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositivityPerturbation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ExteriorDerivative
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BottChern
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GeometricForms

/-!
# Kähler forms as small perturbations on compact manifolds

* `isStrictlyPositive_of_chartTransition`: strict positivity of a two-form is independent of
  the chart;
* `StrictPosAt.eventually`: strict positivity at a point persists nearby;
* `exists_isKahler_add_smul`: on a compact complex manifold, if `A` is a semipositive closed
  real `(1,1)`-form and every point has some `ε₀ > 0` with `A + ε₀ Θ` strictly positive there,
  then `A + ε Θ` is Kähler for one `ε > 0`.  (For `0 < ε ≤ ε₀`,
  `A + ε Θ = (1 - ε/ε₀) A + (ε/ε₀)(A + ε₀ Θ)`.)
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.KahlerPerturbation

open FirstPass PositivityPerturbation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem chartTransitionDerivative_injective (e f : ComplexChart n M) {u : ComplexModel n}
    (hu : u ∈ (chartTransition e f).source) :
    Function.Injective (chartTransitionDerivative e f u) := by
  set T := chartTransition e f
  set T' := chartTransition f e
  have hTu : T u ∈ T'.source := by
    refine ⟨HolomorphicMaps.coordinateMap_mem_target (f := id) hu, ?_⟩
    have hu2 : e.val.symm u ∈ f.val.source := hu.2
    change f.val.symm (f.val (e.val.symm u)) ∈ e.val.source
    rw [f.val.left_inv hu2]
    exact e.val.map_target hu.1
  have hinv : ∀ᶠ u' in 𝓝 u, T' (T u') = u' := by
    filter_upwards [T.open_source.mem_nhds hu] with u' hu'
    have hu2 : e.val.symm u' ∈ f.val.source := hu'.2
    have hu1 : u' ∈ e.val.target := hu'.1
    change e.val (f.val.symm (f.val (e.val.symm u'))) = u'
    rw [f.val.left_inv hu2, e.val.right_inv hu1]
  have hT := (HolomorphicMaps.chartTransition_contDiffAt_real e f hu).differentiableAt (by simp)
  have hT' := (HolomorphicMaps.chartTransition_contDiffAt_real f e hTu).differentiableAt
    (by simp)
  have hcomp : (fderiv ℝ T' (T u)).comp (fderiv ℝ T u) = ContinuousLinearMap.id ℝ _ := by
    rw [← fderiv_comp u hT' hT]
    have hinv' : (⇑T' ∘ ⇑T) =ᶠ[𝓝 u] id := hinv
    rw [hinv'.fderiv_eq, fderiv_id]
  intro v w hvw
  have := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L v) hcomp
  have h2 := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L w) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
  rw [← this, ← h2]
  exact congrArg _ hvw

/-- Strict positivity transfers along chart changes. -/
theorem isStrictlyPositive_of_chartTransition (α : SmoothRealForm n M 2) (e f : ComplexChart n M)
    {u : ComplexModel n} (hu : u ∈ (chartTransition e f).source)
    (h : IsStrictlyPositive (α.coeff f (chartTransition e f u))) :
    IsStrictlyPositive (α.coeff e u) := by
  intro v hv
  have hDv : chartTransitionDerivative e f u v ≠ 0 := fun h0 =>
    hv (chartTransitionDerivative_injective e f hu (h0.trans (map_zero _).symm))
  rw [α.compatible e f u hu]
  have hvec : (fun i => chartTransitionDerivative e f u ((![v, Complex.I • v] : Fin 2 → _) i)) =
      ![chartTransitionDerivative e f u v, Complex.I • chartTransitionDerivative e f u v] := by
    funext i
    fin_cases i
    · rfl
    · exact chartTransitionDerivative_complex_smul e f u hu Complex.I v
  rw [hvec]
  exact h _ hDv

/-- Strict positivity at a point, in the preferred chart. -/
def StrictPosAt (α : SmoothRealForm n M 2) (y : M) : Prop :=
  IsStrictlyPositive (α.coeff (complexChartAt (n := n) y) (chartAt (ComplexModel n) y y))

omit [IsComplexManifold n M] in
theorem mem_chartTransition_source {e f : ComplexChart n M} {y : M} (he : y ∈ e.val.source)
    (hf : y ∈ f.val.source) : e.val y ∈ (chartTransition e f).source :=
  ⟨e.val.map_source he, by
    change e.val.symm (e.val y) ∈ f.val.source
    rw [e.val.left_inv he]; exact hf⟩

omit [IsComplexManifold n M] in
theorem chartTransition_apply_self {e f : ComplexChart n M} {y : M} (he : y ∈ e.val.source) :
    chartTransition e f (e.val y) = f.val y := by
  change f.val (e.val.symm (e.val y)) = f.val y
  rw [e.val.left_inv he]

/-- Strict positivity at a point holds in every chart. -/
theorem StrictPosAt.isStrictlyPositive {α : SmoothRealForm n M 2} {y : M} (h : StrictPosAt α y)
    (e : ComplexChart n M) (hy : y ∈ e.val.source) : IsStrictlyPositive (α.coeff e (e.val y)) := by
  have hmem := mem_chartTransition_source (f := complexChartAt (n := n) y) hy
    (mem_complexChartAt_source y)
  refine isStrictlyPositive_of_chartTransition α e _ hmem ?_
  rw [chartTransition_apply_self hy]
  exact h

/-- Strict positivity in a fixed chart is an open condition. -/
theorem eventually_isStrictlyPositive_coeff (α : SmoothRealForm n M 2) (e : ComplexChart n M)
    {u : ComplexModel n} (hu : u ∈ e.val.target) (h : IsStrictlyPositive (α.coeff e u)) :
    ∀ᶠ u' in 𝓝 u, IsStrictlyPositive (α.coeff e u') := by
  set S := sphere (0 : ComplexModel n) 1
  have hSne : ∀ w ∈ S, w ≠ 0 := fun w hw h0 => by
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hw; exact zero_ne_one hw
  obtain ⟨m, hm, hmS⟩ : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ S, m ≤ quad (α.coeff e u) w := by
    by_cases hn : S.Nonempty
    · obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere (0 : ComplexModel n) 1).exists_isMinOn hn
        (continuous_quad _).continuousOn
      exact ⟨_, h w₀ (hSne w₀ hw₀), fun w hw => hmin hw⟩
    · exact ⟨1, one_pos, fun w hw => absurd ⟨w, hw⟩ hn⟩
  have hcont : ContinuousAt (α.coeff e) u :=
    ((α.smooth e).continuousOn).continuousAt (e.val.open_target.mem_nhds hu)
  filter_upwards [hcont.eventually (Metric.ball_mem_nhds (α.coeff e u) hm)] with u' hu' v hv
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set w := ‖v‖⁻¹ • v
  have hwS : w ∈ S := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
  have hvw : v = ‖v‖ • w := by rw [smul_inv_smul₀ hvn.ne']
  have hbound : |quad (α.coeff e u') w - quad (α.coeff e u) w| < m := by
    have h1 : quad (α.coeff e u') w - quad (α.coeff e u) w = quad (α.coeff e u' - α.coeff e u) w :=
      rfl
    rw [h1]
    rw [dist_eq_norm] at hu'
    refine lt_of_le_of_lt ?_ hu'
    have := (α.coeff e u' - α.coeff e u).le_opNorm ![w, Complex.I • w]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, norm_smul,
      Complex.norm_I, mem_sphere_zero_iff_norm.mp hwS, mul_one] at this
    exact (Real.norm_eq_abs _ ▸ this)
  have hw : 0 < quad (α.coeff e u') w := by
    have := hmS w hwS
    have := abs_lt.mp hbound
    linarith
  change 0 < quad (α.coeff e u') v
  rw [hvw, quad_smul]
  positivity

theorem StrictPosAt.eventually {α : SmoothRealForm n M 2} {y : M} (h : StrictPosAt α y) :
    ∀ᶠ y' in 𝓝 y, StrictPosAt α y' := by
  set e := complexChartAt (n := n) y
  have hy : y ∈ e.val.source := mem_complexChartAt_source y
  have h1 := eventually_isStrictlyPositive_coeff α e (e.val.map_source hy) h
  have h2 : ∀ᶠ y' in 𝓝 y, y' ∈ e.val.source := e.val.open_source.mem_nhds hy
  filter_upwards [(e.val.continuousAt hy).eventually h1, h2] with y' hy' hy'e
  have hmem := mem_chartTransition_source (e := complexChartAt (n := n) y') (f := e)
    (mem_complexChartAt_source y') hy'e
  refine isStrictlyPositive_of_chartTransition α _ e hmem ?_
  convert hy' using 2
  exact chartTransition_apply_self (mem_complexChartAt_source y')

/-- **Kähler forms as perturbations.**  On a compact complex manifold, a semipositive closed
real `(1,1)`-form `A` such that every point has some `ε₀ > 0` with `A + ε₀ Θ` strictly positive
there admits `ε > 0` with `A + ε Θ` Kähler. -/
theorem exists_isKahler_add_smul [CompactSpace M] (A Θ : ClosedRealOneOneForm n M)
    (hA : A.val.IsSemipositive)
    (hloc : ∀ y : M, ∃ ε₀ : ℝ, 0 < ε₀ ∧ StrictPosAt (A + ε₀ • Θ).val y) :
    ∃ ε : ℝ, 0 < ε ∧ (A + ε • Θ).val.IsKahler := by
  classical
  choose ε₀ hε₀ hpos using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun y => {y' | StrictPosAt (A + ε₀ y • Θ).val y'}) fun y _ => (hpos y).eventually
  set ε : ℝ := if h : t.Nonempty then t.inf' h ε₀ else 1
  have hε : 0 < ε := by
    by_cases h : t.Nonempty
    · simp only [ε, dite_eq_left h]
      exact (Finset.lt_inf'_iff h).mpr fun y _ => hε₀ y
    · simp [ε, h]
  refine ⟨ε, hε, ⟨fun e u hu => ⟨(A + ε • Θ).2.2 e u hu, fun v hv => ?_⟩, (A + ε • Θ).2.1⟩⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (ht (mem_univ (e.val.symm u)))
  have hne : t.Nonempty := ⟨y, hyt⟩
  have hεy : ε ≤ ε₀ y := by
    simp only [ε, dite_eq_left hne]
    exact Finset.inf'_le _ hyt
  have hsymm : e.val.symm u ∈ e.val.source := e.val.map_target hu
  have h1 := (hy : StrictPosAt (A + ε₀ y • Θ).val (e.val.symm u)).isStrictlyPositive e hsymm v hv
  rw [e.val.right_inv hu] at h1
  have h2 := hA e u hu v
  have hsum : ∀ c : ℝ, (A + c • Θ).val.coeff e u ![v, Complex.I • v] =
      A.val.coeff e u ![v, Complex.I • v] + c * Θ.val.coeff e u ![v, Complex.I • v] := by
    intro c
    simp [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
  rw [hsum] at h1 ⊢
  set a := A.val.coeff e u ![v, Complex.I • v]
  set b := Θ.val.coeff e u ![v, Complex.I • v]
  -- `a + ε b = (1 - ε/ε₀) a + (ε/ε₀) (a + ε₀ b)`
  have hε₀y := hε₀ y
  have key : a + ε * b = (1 - ε / ε₀ y) * a + (ε / ε₀ y) * (a + ε₀ y * b) := by
    field_simp
    ring
  rw [key]
  have ht1 : 0 ≤ 1 - ε / ε₀ y := by
    rw [sub_nonneg, div_le_one hε₀y]; exact hεy
  have ht2 : 0 < ε / ε₀ y := div_pos hε hε₀y
  have := mul_nonneg ht1 h2
  have := mul_pos ht2 h1
  linarith

end

end SGPT.Foundations.Analysis.Pending.KahlerPerturbation
