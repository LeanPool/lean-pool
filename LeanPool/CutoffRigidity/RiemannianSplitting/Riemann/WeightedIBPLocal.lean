/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPChart
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.Jacobi

/-! # The coordinate divergence formula for the Levi-Civita trace

In the chart `chartAt F x₀` with volume density `D = √det g`, the trace of the Levi-Civita
derivative of a vector field `Y` with coordinate expression `Yc` satisfies
`D · tr(∇Y) = ∂_{Yc} D + D · div Yc`.
-/

@[expose] public section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace CutoffRigidity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) 2 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- Left inverse of the chart frame: the trivialization map at `y`. -/
noncomputable def chartFrameInv (x₀ y : M) : TangentSpace 𝓘(ℝ, F) y →L[ℝ] F :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt ℝ y

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartFrameInv_chartFrame {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u : F) :
    chartFrameInv x₀ y (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y u) = u :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL (by simpa using hy) u

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartFrame_chartFrameInv {x₀ y : M} (hy : y ∈ (chartAt F x₀).source)
    (w : TangentSpace 𝓘(ℝ, F) y) :
    chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y (chartFrameInv x₀ y w) = w :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).symmL_continuousLinearMapAt (by simpa using hy) w

/-- Derivative of the chart volume density (Jacobi's formula), along a family orthonormal for
the metric at `z`. -/
theorem hasFDerivAt_chartRiemannianVolumeDensity (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) {y : M}
    (hydef : (extChartAt 𝓘(ℝ, F) x₀).symm z = y)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ (TangentSpace 𝓘(ℝ, F) y)) :
    let _ : AddCommGroup (F →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
    let _ : AddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
    HasFDerivAt (chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀)
      ((chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀ z / 2) •
        ∑ l, (ContinuousLinearMap.apply ℝ ℝ
            (chartFrameInv x₀ y (b l))).comp
          ((ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ)
            (chartFrameInv x₀ y (b l))).comp
            (fderiv ℝ (chartMetric (I := 𝓘(ℝ, F)) x₀) z))) z := by
  dsimp only
  have hy : y ∈ (chartAt F x₀).source := hydef ▸ extChartAt_symm_mem_source hz
  set e : Fin (Module.finrank ℝ F) → F := ⇑(stdOrthonormalBasis ℝ F) with he_def
  set f : Fin (Module.finrank ℝ F) → F := fun l => chartFrameInv x₀ y (b l) with hf_def
  set Q : Matrix (Fin (Module.finrank ℝ F)) (Fin (Module.finrank ℝ F)) ℝ :=
    fun j l => inner ℝ (b l) (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y (e j)) with hQ
  have hmetric : ∀ u v : F, chartMetric (I := 𝓘(ℝ, F)) x₀ z u v =
      inner ℝ (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y u) (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y v) := by
    subst hydef
    exact fun u v => rfl
  have he : ∀ j, e j = ∑ l, Q j l • f l := by
    intro j
    have h1 := b.sum_repr' (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y (e j))
    have h2 := congrArg (chartFrameInv x₀ y) h1
    rw [chartFrameInv_chartFrame hy, map_sum] at h2
    rw [← h2]
    apply Finset.sum_congr rfl
    intro l _
    simp [hQ, hf_def]
  have hf : ∀ l m, chartMetric (I := 𝓘(ℝ, F)) x₀ z (f l) (f m) = if l = m then 1 else 0 := by
    intro l m
    rw [hmetric]
    simp only [hf_def, chartFrame_chartFrameInv hy]
    exact (orthonormal_iff_ite.mp b.orthonormal) l m
  have hβ : DifferentiableAt ℝ (chartMetric (I := 𝓘(ℝ, F)) x₀) z :=
    (contDiffAt_chartMetric_target x₀ hz).differentiableAt one_ne_zero
  have hJ := hasFDerivAt_det_gram hβ e f Q he hf
  have hpos : 0 < (Matrix.of fun j k => chartMetric (I := 𝓘(ℝ, F)) x₀ z (e j) (e k)).det := by
    have := chartRiemannianVolumeDensity_pos (I := 𝓘(ℝ, F)) x₀ hz
    change 0 < (chartRiemannianGram (I := 𝓘(ℝ, F)) x₀ z).det
    rw [← chartRiemannianVolumeDensity_sq]
    exact sq_pos_of_pos this
  have hS := hJ.sqrt hpos.ne'
  have hfun : chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀ =
      fun x => Real.sqrt
        (Matrix.of fun j k => chartMetric (I := 𝓘(ℝ, F)) x₀ x (e j) (e k)).det := by
    funext x
    exact chartRiemannianVolumeDensity_eq_sqrt x₀ x
  rw [hfun]
  convert hS using 1
  rw [smul_smul]
  have hs : 0 < Real.sqrt (Matrix.of fun j k => chartMetric (I := 𝓘(ℝ, F)) x₀ z (e j) (e k)).det :=
    Real.sqrt_pos.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  have key : ∀ a d : ℝ, 0 < a → a ^ 2 = d → a / 2 = 1 / (2 * a) * d := by
    intro a d ha had
    rw [← had]
    field_simp
  congr 1
  exact key _ _ hs hsq

/-- The chart volume density is C¹ at every point of the chart target. -/
theorem contDiffAt_chartRiemannianVolumeDensity_target (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    ContDiffAt ℝ 1 (chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀) z := by
  have hEntry (i j : Fin (Module.finrank ℝ F)) :
      ContDiffAt ℝ 1 (fun w => chartRiemannianGram (I := 𝓘(ℝ, F)) x₀ w i j) z :=
    ((contDiffAt_chartMetric_target x₀ hz).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hDet : ContDiffAt ℝ 1 (fun w => (chartRiemannianGram (I := 𝓘(ℝ, F)) x₀ w).det) z := by
    classical
    simp only [Matrix.det_apply]
    fun_prop
  have hPos : 0 < (chartRiemannianGram (I := 𝓘(ℝ, F)) x₀ z).det := by
    rw [← chartRiemannianVolumeDensity_sq]
    exact sq_pos_of_pos (chartRiemannianVolumeDensity_pos x₀ hz)
  have hh := hDet.sqrt hPos.ne'
  convert! hh using 1
  funext w
  exact chartRiemannianVolumeDensity_eq_sqrt x₀ w

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- Conjugation of the trace by the chart frame. -/
theorem trace_chartFrame_conj (x₀ : M) {y : M} (hy : y ∈ (chartAt F x₀).source) (D : F →L[ℝ] F) :
    LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) y)
      ((chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y).comp (D.comp (chartFrameInv x₀ y))).toLinearMap =
    LinearMap.trace ℝ F D.toLinearMap := by
  have h := LinearMap.trace_comp_comm' (R := ℝ) (chartFrameInv x₀ y).toLinearMap
    ((chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y).comp D).toLinearMap
  have h1 : (((chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y).comp D).toLinearMap ∘ₗ
      (chartFrameInv x₀ y).toLinearMap) =
      ((chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y).comp (D.comp (chartFrameInv x₀ y))).toLinearMap := by
    ext w; rfl
  have h2 : ((chartFrameInv x₀ y).toLinearMap ∘ₗ
      ((chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y).comp D).toLinearMap) = D.toLinearMap := by
    ext w
    exact chartFrameInv_chartFrame hy (D w)
  rw [h1, h2] at h
  exact h

/-- **Coordinate divergence formula**: `D · tr ∇Y = ∂_{Yc} D + D · div Yc`. -/
theorem chartRiemannianVolumeDensity_mul_trace (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target)
    {Y : (x : M) → TangentSpace 𝓘(ℝ, F) x}
    (hY : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% Y) ((extChartAt 𝓘(ℝ, F) x₀).symm z)) :
    chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀ z *
        LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) ((extChartAt 𝓘(ℝ, F) x₀).symm z))
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y
            ((extChartAt 𝓘(ℝ, F) x₀).symm z)).toLinearMap =
      fderiv ℝ (chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀) z
          (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y z) +
        chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀ z *
          LinearMap.trace ℝ F (fderiv ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y) z).toLinearMap
              := by
  have hy : (extChartAt 𝓘(ℝ, F) x₀).symm z ∈ (chartAt F x₀).source :=
    extChartAt_symm_mem_source hz
  let b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ
      (TangentSpace 𝓘(ℝ, F) ((extChartAt 𝓘(ℝ, F) x₀).symm z)) :=
    (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) ((extChartAt 𝓘(ℝ, F) x₀).symm z))).reindex
      (finCongr rfl)
  have hD := (hasFDerivAt_chartRiemannianVolumeDensity x₀ hz rfl b).fderiv
  set A := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y ((extChartAt 𝓘(ℝ, F) x₀).symm z)
    with hA
  set D' := fderiv ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y) z with hD'
  set w := chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y z with hw
  set f : Fin (Module.finrank ℝ F) → F := fun l =>
    chartFrameInv x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z) (b l) with hf
  have hkos : ∀ l, inner ℝ (b l) (A (b l)) =
      (fderiv ℝ (chartMetric (I := 𝓘(ℝ, F)) x₀) z w) (f l) (f l) / 2 +
        inner ℝ (b l) (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z)
          (D' (f l))) := by
    intro l
    have hbl : chartFrameCLM (I := 𝓘(ℝ, F)) x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z) (f l) = b l :=
      chartFrame_chartFrameInv hy (b l)
    have hk := inner_leviCivita_chartFrame_self x₀ hz (f l) hY
    change inner ℝ (A (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ (f l)))
      (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ (f l)) = _ at hk
    rw [hbl] at hk
    rw [real_inner_comm, hk]
    congr 1
    rw [← hbl]
    rfl
  have hAtr : LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) ((extChartAt 𝓘(ℝ, F) x₀).symm z))
      A.toLinearMap = ∑ l, inner ℝ (b l) (A (b l)) :=
    LinearMap.trace_eq_sum_inner _ b
  have hsecond : ∑ l, inner ℝ (b l) (chartFrameCLM (I := 𝓘(ℝ, F)) x₀
      ((extChartAt 𝓘(ℝ, F) x₀).symm z) (D' (f l))) = LinearMap.trace ℝ F D'.toLinearMap := by
    rw [← trace_chartFrame_conj x₀ hy D', LinearMap.trace_eq_sum_inner _ b]
    rfl
  have hfirst : fderiv ℝ (chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀) z w =
      chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀ z / 2 *
        ∑ l, (fderiv ℝ (chartMetric (I := 𝓘(ℝ, F)) x₀) z w) (f l) (f l) := by
    rw [hD]
    simp [Finset.mul_sum]
    rfl
  rw [hAtr, hfirst]
  simp only [hkos, Finset.sum_add_distrib, hsecond, ← Finset.sum_div, mul_add]
  ring

end CutoffRigidity
