/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitAction

/-! # The potential along the action of the frame: `V(t · y) = V(y) + ρ|t|²/2` -/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

namespace Frame

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] {k : ℕ} (fr : Frame F M k)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
/-- For an eigenfunction `sᵢ` with parallel gradient, `⟨∇V, ∇sᵢ⟩ = ρ sᵢ`. -/
theorem mvfderiv_V_X [MeasurableSpace M] {V : M → ℝ} {μ : Measure M} {ρ : ℝ} (i : Fin k)
    (hi : IsMEigenfunction F μ V ρ (fr.s i)) (x : M) :
    mvfderiv 𝓘(ℝ, F) V x (fr.X i x) = ρ * fr.s i x := by
  have h1 := hi.2.2 x
  have h2 : mlaplacian F (fr.s i) x = 0 := by
    unfold mlaplacian
    simp [fr.parallel i x]
  unfold mgenerator at h1
  rw [h2] at h1
  have h3 : inner ℝ (mgrad F V x) (fr.X i x) = mvfderiv 𝓘(ℝ, F) V x (fr.X i x) :=
    mgrad_inner F V x _
  rw [← h3]
  have : inner ℝ (mgrad F V x) (mgrad F (fr.s i) x) = ρ * fr.s i x := by linarith
  exact this

variable {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V) {ρ : ℝ}
  (hVX : ∀ i x, mvfderiv 𝓘(ℝ, F) V x (fr.X i x) = ρ * fr.s i x)

include hV hVX in
/-- Quadratic growth of the potential along a flow line. -/
theorem V_flow (i : Fin k) (x : M) (t : ℝ) :
    V (fr.flow i x t) = V x + ρ * (t * fr.s i x + t ^ 2 / 2) := by
  have hγ := CutoffRigidity.completeBoundedFlow_isMIntegralCurve (fr.contMDiff_X_one i)
    (fr.enorm_X_le i) x
  have hVmd : MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, ℝ) V := hV.mdifferentiable (by simp)
  have hd : ∀ r, HasDerivAt (fun r => V (fr.flow i x r) - ρ * (r * fr.s i x + r ^ 2 / 2)) 0 r := by
    intro r
    have h1 : HasDerivAt (fun s => V (fr.flow i x s)) (ρ * fr.s i (fr.flow i x r)) r :=
      (CutoffRigidity.hasDerivAt_scalar_integralCurve hγ hVmd r).congr_deriv (hVX i _)
    have h2 : HasDerivAt (fun r : ℝ => ρ * (r * fr.s i x + r ^ 2 / 2))
        (ρ * (fr.s i x + r)) r := by
      have h := (((hasDerivAt_id r).mul_const (fr.s i x)).add
        ((hasDerivAt_pow 2 r).div_const 2)).const_mul ρ
      refine h.congr_deriv ?_
      simp
    refine (h1.sub h2).congr_deriv ?_
    rw [fr.s_flow]
    simp
  have hc := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv)
      t 0
  have h0 : fr.flow i x 0 = x := CutoffRigidity.completeBoundedFlow_zero (fr.contMDiff_X_one i)
    (fr.enorm_X_le i) x
  simp only [h0] at hc
  linarith

include hV hVX in
theorem V_comp (L : List (Fin k)) (hL : L.Nodup) (t : EuclideanSpace ℝ (Fin k)) (y : M) :
    V (fr.comp L t y) = V y + ρ * (L.map (fun a => t a * fr.s a y + t a ^ 2 / 2)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hnd := List.nodup_cons.mp hL
    rw [comp_cons, fr.V_flow hV hVX, ih hnd.2, fr.s_comp a L hnd.2]
    simp only [hnd.1, ite_false, add_zero, List.map_cons, List.sum_cons]
    ring

include hV hVX in
/-- **The potential on the product**: `V(t · y) = V(y) + ρ‖t‖²/2` for `y` in the level. -/
theorem V_action (t : EuclideanSpace ℝ (Fin k)) (y : M) (hy : fr.sv y = 0) :
    V (fr.comp (List.finRange k) t y) = V y + ρ * ‖t‖ ^ 2 / 2 := by
  rw [fr.V_comp hV hVX _ (List.nodup_finRange k)]
  have hj : ∀ j, fr.s j y = 0 := fun j => by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v j) hy
    simpa [sv] using this
  have : ((List.finRange k).map (fun a => t a * fr.s a y + t a ^ 2 / 2)).sum = ‖t‖ ^ 2 / 2 := by
    rw [← Fin.sum_univ_def, EuclideanSpace.norm_sq_eq]
    simp only [hj, mul_zero, zero_add, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_div]
  rw [this]
  ring

end Frame

end CutCur
