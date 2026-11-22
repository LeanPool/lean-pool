/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitTangent

/-! # The product metric identity for the action of a frame -/

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

/-- Pythagoras: the differential of the action `(t, y) ↦ φ_t(y)` is an isometry for the product
metric on `ℝ^k × ker ds`. -/
theorem norm_sq_action (t : EuclideanSpace ℝ (Fin k)) (y : M) (w : EuclideanSpace ℝ (Fin k))
    (u : TangentSpace 𝓘(ℝ, F) y) (hu : ∀ i, inner ℝ (fr.X i y) u = 0) :
    ‖(∑ i, w i • fr.X i (fr.comp (List.finRange k) t y)) +
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.comp (List.finRange k) t z) y u‖ ^ 2 =
      ‖w‖ ^ 2 + ‖u‖ ^ 2 := by
  set z := fr.comp (List.finRange k) t y with hz
  set S : TangentSpace 𝓘(ℝ, F) z := ∑ i, w i • fr.X i z with hS
  set T : TangentSpace 𝓘(ℝ, F) z :=
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.comp (List.finRange k) t z) y u with hT
  have hTT : ‖T‖ = ‖u‖ := by
    have := fr.inner_mfderiv_comp (List.finRange k) t y u u
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    nlinarith [norm_nonneg T, norm_nonneg u]
  have hSS : ‖S‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hS, inner_sum, EuclideanSpace.norm_sq_eq]
    simp only [sum_inner, inner_smul_left, inner_smul_right, fr.inner_X]
    simp [sq]
  have hST : inner ℝ S T = 0 := by
    rw [hS, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left]
    have h1 : fr.X i z = mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z => fr.comp (List.finRange k) t z) y
        (fr.X i y) := (fr.mfderiv_comp_X (List.finRange k) t i y).symm
    have h2 : inner ℝ (fr.X i z) T = 0 := by
      rw [h1, hT, fr.inner_mfderiv_comp]
      exact hu i
    simp [h2]
  change ‖S + T‖ ^ 2 = _
  rw [norm_add_sq_real, hST, hSS, hTT]
  ring

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsRiemannianManifold 𝓘(ℝ, F) M]
  [CompleteSpace M] in
theorem mvfderiv_comp_map (f : M → ℝ) (g : M → M) (x : M)
    (hf : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f (g x))
    (hg : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) g x) (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) f (g x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) g x v) = mvfderiv 𝓘(ℝ, F) (fun y => f (g y))
        x v := by
  have h1 := mfderiv_comp x hf hg
  simp only [mvfderiv, ContinuousLinearMap.comp_apply]
  rw [show (fun y => f (g y)) = f ∘ g from rfl, h1]
  rfl

/-- The retraction differential has no component along the frame. -/
theorem inner_X_dretr (i : Fin k) (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    inner ℝ (fr.X i (fr.retr x)) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v) = 0 := by
  rw [Frame.X, inner_mgrad]
  rw [mvfderiv_comp_map (fr.s i) fr.retr x
    (((fr.smooth i).mdifferentiable (by simp)) _) (fr.contMDiff_retr_mdiff x) v]
  have : (fun y => fr.s i (fr.retr y)) = fun _ => (0 : ℝ) := funext fun y => fr.s_retr y i
  rw [this, mvfderiv_const]
  rfl

/-- Pointwise Pythagoras: `‖v‖² = ‖ds v‖² + ‖dretr v‖²`. -/
theorem norm_sq_split (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    ‖v‖ ^ 2 = ‖fr.dsv x v‖ ^ 2 + ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v‖ ^ 2 := by
  have hPM := fr.norm_sq_action (fr.sv x) (fr.retr x) (fr.dsv x v)
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v) (fun i => fr.inner_X_dretr i x v)
  have hdec := fr.decomp x v
  -- transport along `comp (sv x) (retr x) = x`
  have key : ∀ z : M, z = x → ∀ e : TangentSpace 𝓘(ℝ, F) z, tf e = tf v → ‖e‖ = ‖v‖ := by
    intro z hz e he
    subst hz
    have : e = v := he
    rw [this]
  have hn := key _ (fr.comp_retr x) _ hdec.symm
  rw [hn] at hPM
  exact hPM

/-- The differential of the level retraction has operator norm at most one. -/
theorem norm_mfderiv_retr_le (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v‖ ≤ ‖v‖ := by
  have h := fr.norm_sq_split x v
  nlinarith [norm_nonneg (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v), norm_nonneg v,
    sq_nonneg ‖fr.dsv x v‖]

end Frame

end CutCur
