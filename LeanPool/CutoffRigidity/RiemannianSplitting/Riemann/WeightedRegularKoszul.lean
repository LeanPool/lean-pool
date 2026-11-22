/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedRegularChart

/-! # G0 (part 2): smoothness of the Levi-Civita coefficients in a chart frame

From the Koszul formula `leviCivitaConnection_apply_inner` applied to the chart frame, the
bilinear coefficients `(u, w) ↦ ⟪∇_{E_u} Y, E_w⟫` of the Levi-Civita derivative of a smooth
vector field `Y` are smooth functions of the chart coordinate.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutCur.WReg


variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

open CutoffRigidity

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- `y ↦ d g (y) (E_W(y))` is smooth for `g` smooth on the chart and `W` smooth. -/
theorem contMDiffAt_mvfderiv_frame {x₀ : M} {g : M → ℝ}
    (hg : ∀ y ∈ (chartAt F x₀).source, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g y)
    {W : M → F} (hW : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ W x₀)
    {X : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    (hX : ∀ y ∈ (chartAt F x₀).source, X y = chartFrame (I := 𝓘(ℝ, F)) x₀ (W y) y) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y => mvfderiv 𝓘(ℝ, F) g y (X y)) x₀ := by
  let e := extChartAt 𝓘(ℝ, F) x₀
  have hG : ContDiffAt ℝ ∞ (g ∘ e.symm) (e x₀) :=
    ((hg x₀ (mem_chart_source F x₀)).comp_of_eq ((contMDiffOn_extChartAt_symm x₀).contMDiffAt
      (extChartAt_target_mem_nhds x₀)) (extChartAt_to_inv x₀)).contDiffAt
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (g ∘ e.symm)) (e x₀) := hG.fderiv_right (m := ∞) (by simp)
  have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      (fun y => fderiv ℝ (g ∘ e.symm) (e y) (W y)) x₀ :=
    (hD.contMDiffAt.comp x₀ (contMDiffAt_extChartAt (I := 𝓘(ℝ, F)) (x := x₀) (n := ∞))).clm_apply hW
  apply h1.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds F x₀] with y hy
  have hys : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have hz : e y ∈ e.target := e.map_source hys
  have hfy : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) g (e.symm (e y)) := by
    simpa only [e.left_inv hys] using (hg y hy).mdifferentiableAt (by simp)
  have := fderiv_chartScalar_frame (I := 𝓘(ℝ, F)) x₀ hz hfy (W y)
  rw [e.left_inv hys] at this
  rw [hX y hy]
  exact this.symm

/-- Smoothness of the Koszul expression in the chart frame. -/
theorem contMDiffAt_koszul {x₀ : M} {Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    (hY : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% Y)) (u w : F) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y =>
      (mvfderiv 𝓘(ℝ, F) (fun x => inner ℝ (Y x) (chartFrame (I := 𝓘(ℝ, F)) x₀ w x)) y
          (chartFrame (I := 𝓘(ℝ, F)) x₀ u y)
        + mvfderiv 𝓘(ℝ, F) (fun x => inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ w x)
            (chartFrame (I := 𝓘(ℝ, F)) x₀ u x)) y (Y y)
        - mvfderiv 𝓘(ℝ, F) (fun x => inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u x) (Y x)) y
            (chartFrame (I := 𝓘(ℝ, F)) x₀ w y)
        - inner ℝ (Y y) (VectorField.mlieBracket 𝓘(ℝ, F) (chartFrame (I := 𝓘(ℝ, F)) x₀ u)
            (chartFrame (I := 𝓘(ℝ, F)) x₀ w) y)
        - inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ w y)
            (VectorField.mlieBracket 𝓘(ℝ, F) Y (chartFrame (I := 𝓘(ℝ, F)) x₀ u) y)
        + inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u y)
            (VectorField.mlieBracket 𝓘(ℝ, F) (chartFrame (I := 𝓘(ℝ, F)) x₀ w) Y y)) / 2) x₀ := by
  have hEu : ∀ y ∈ (chartAt F x₀).source, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞
      (T% (chartFrame (I := 𝓘(ℝ, F)) x₀ u)) y := fun y hy => contMDiffAt_chartFrame' hy u
  have hEw : ∀ y ∈ (chartAt F x₀).source, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞
      (T% (chartFrame (I := 𝓘(ℝ, F)) x₀ w)) y := fun y hy => contMDiffAt_chartFrame' hy w
  have hYc : ∀ y ∈ (chartAt F x₀).source,
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (coord x₀ Y) y := fun y hy => contMDiffAt_coord hy (hY y)
  have inn : ∀ {A B : (y : M) → TangentSpace 𝓘(ℝ, F) y} {y : M},
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% A) y →
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% B) y →
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y' => inner ℝ (A y') (B y')) y :=
    fun hA hB => ContMDiffAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F)) hA hB
  have hsrc : x₀ ∈ (chartAt F x₀).source := mem_chart_source F x₀
  have : IsManifold 𝓘(ℝ, F) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by simp)
  have h1 : ((∞ : ℕ∞ω) + 1) = ∞ := by
    rfl
  have : IsManifold 𝓘(ℝ, F) (∞ + 1) M := by
    rw [h1]; infer_instance
  have br : ∀ {A B : (y : M) → TangentSpace 𝓘(ℝ, F) y},
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% A) x₀ →
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% B) x₀ →
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% (VectorField.mlieBracket 𝓘(ℝ, F) A B)) x₀ :=
    fun hA hB => ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) hA hB (by simp)
  have hY0 := hY x₀
  have hu0 := hEu x₀ hsrc
  have hw0 := hEw x₀ hsrc
  simp only [div_eq_mul_inv]
  refine ContMDiffAt.mul ?_ contMDiffAt_const
  refine ContMDiffAt.add (ContMDiffAt.sub (ContMDiffAt.sub (ContMDiffAt.sub
    (ContMDiffAt.add ?_ ?_) ?_) ?_) ?_) ?_
  · exact contMDiffAt_mvfderiv_frame (fun y hy => inn (hY y) (hEw y hy))
      (contMDiffAt_const (c := u)) (fun y hy => rfl)
  · exact contMDiffAt_mvfderiv_frame (fun y hy => inn (hEw y hy) (hEu y hy)) (hYc x₀ hsrc)
      (fun y hy => (chartFrame_coord hy Y).symm)
  · exact contMDiffAt_mvfderiv_frame (fun y hy => inn (hEu y hy) (hY y))
      (contMDiffAt_const (c := w)) (fun y hy => rfl)
  · exact inn hY0 (br hu0 hw0)
  · exact inn hw0 (br hY0 hu0)
  · exact inn hu0 (br hw0 hY0)

/-- Bilinear coefficients `(u, w) ↦ ⟪∇_{E_u} Y, E_w⟫` of the Levi-Civita derivative of `Y` at
`e.symm z`, in the chart frame at `x₀`. -/
noncomputable def hessCoeff (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x₀ : M) (z : F) :
    F →L[ℝ] F →L[ℝ] ℝ :=
  (innerSL ℝ (E := TangentSpace 𝓘(ℝ, F) ((extChartAt 𝓘(ℝ, F) x₀).symm z))).bilinearComp
    ((CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y
        ((extChartAt 𝓘(ℝ, F) x₀).symm z)).comp
      (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z)))
    (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z))

theorem hessCoeff_apply (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x₀ : M) (z u w : F) :
    hessCoeff Y x₀ z u w =
      inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y
        ((extChartAt 𝓘(ℝ, F) x₀).symm z)
          (chartFrame (I := 𝓘(ℝ, F)) x₀ u ((extChartAt 𝓘(ℝ, F) x₀).symm z)))
        (chartFrame (I := 𝓘(ℝ, F)) x₀ w ((extChartAt 𝓘(ℝ, F) x₀).symm z)) := rfl

theorem contDiffAt_hessCoeff {Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    (hY : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% Y)) (x₀ : M) :
    ContDiffAt ℝ ∞ (hessCoeff Y x₀) (extChartAt 𝓘(ℝ, F) x₀ x₀) := by
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (extChartAt 𝓘(ℝ, F) x₀).symm
      (extChartAt 𝓘(ℝ, F) x₀ x₀) :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt (extChartAt_target_mem_nhds x₀)
  rw [← contDiffWithinAt_univ]
  apply contDiffWithinAt_clm_apply.mpr
  intro u
  apply contDiffWithinAt_clm_apply.mpr
  intro w
  have hk := (contMDiffAt_koszul (x₀ := x₀) hY u w).comp_of_eq hsymm (extChartAt_to_inv x₀)
  have hk' := hk.contDiffAt.contDiffWithinAt (s := univ)
  have hev : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, F) x₀ x₀), hessCoeff Y x₀ z u w =
      ((fun y =>
        (mvfderiv 𝓘(ℝ, F) (fun x => inner ℝ (Y x) (chartFrame (I := 𝓘(ℝ, F)) x₀ w x)) y
          (chartFrame (I := 𝓘(ℝ, F)) x₀ u y)
        + mvfderiv 𝓘(ℝ, F) (fun x => inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ w x)
            (chartFrame (I := 𝓘(ℝ, F)) x₀ u x)) y (Y y)
        - mvfderiv 𝓘(ℝ, F) (fun x => inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u x) (Y x)) y
            (chartFrame (I := 𝓘(ℝ, F)) x₀ w y)
        - inner ℝ (Y y) (VectorField.mlieBracket 𝓘(ℝ, F) (chartFrame (I := 𝓘(ℝ, F)) x₀ u)
            (chartFrame (I := 𝓘(ℝ, F)) x₀ w) y)
        - inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ w y)
            (VectorField.mlieBracket 𝓘(ℝ, F) Y (chartFrame (I := 𝓘(ℝ, F)) x₀ u) y)
        + inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u y)
            (VectorField.mlieBracket 𝓘(ℝ, F) (chartFrame (I := 𝓘(ℝ, F)) x₀ w) Y y)) / 2) ∘
        (extChartAt 𝓘(ℝ, F) x₀).symm) z := by
    filter_upwards [extChartAt_target_mem_nhds x₀] with z hz
    have hy : (extChartAt 𝓘(ℝ, F) x₀).symm z ∈ (chartAt F x₀).source := by
      simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, F) x₀).map_target hz
    rw [hessCoeff_apply]
    exact CovariantDerivative.leviCivitaConnection_apply_inner 𝓘(ℝ, F)
      ((contMDiffAt_chartFrame' hy u).mdifferentiableAt (by simp))
      ((hY _).mdifferentiableAt (by simp))
      ((contMDiffAt_chartFrame' hy w).mdifferentiableAt (by simp))
  exact hk'.congr_of_eventuallyEq (nhdsWithin_le_nhds hev) hev.self_of_nhds

end CutCur.WReg
