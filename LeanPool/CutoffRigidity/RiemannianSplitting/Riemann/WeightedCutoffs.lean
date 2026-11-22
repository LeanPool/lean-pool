/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedProper
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedSmoothing
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Topology.EMetricSpace.Lipschitz

/-! # Smooth compactly supported cutoffs on complete Riemannian manifolds (G3)

`weightedCutoffs_of_complete`: on a complete connected Riemannian manifold there are smooth
compactly supported cutoffs `0 ≤ χₙ ≤ 1` with `‖∇χₙ‖ ≤ 1/(n+1)` and `χₙ → 1` pointwise
(eventually equal to `1`).  Proof: Hopf–Rinow (`properSpace_of_complete_riemannian`), a smooth
approximation `ψ` of the distance function with bounded gradient
(`exists_smooth_lip_approx`) and composition with a smooth transition.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal Topology


namespace CutCur

/-- A uniform bound on the derivative of the smooth transition. -/
theorem exists_deriv_smoothTransition_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t, |deriv Real.smoothTransition t| ≤ B := by
  obtain ⟨B, hB⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  refine ⟨max B 1, le_max_right _ _, fun t => ?_⟩
  exact (by simpa only [Real.norm_eq_abs] using hB t : |deriv Real.smoothTransition t| ≤ B)
    |>.trans (le_max_left _ _)

section Cutoffs

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

include F

/-- **(G3)** Smooth compactly supported cutoffs on a complete connected Riemannian manifold. -/
theorem weightedCutoffs_of_complete : WeightedCutoffs F M := by
  classical
  have := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  have hfin := edist_ne_top_of_connected (F := F) (M := M)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  set f : M → ℝ := fun x => (edist x₀ x).toReal with hfdef
  have hf : LipschitzWith 1 f := TauCeti.lipschitzWith_toReal_edist x₀
  obtain ⟨ψ, hψs, hψf, hψg⟩ := exists_smooth_lip_approx F hfin hf
  obtain ⟨B, hB1, hB⟩ := exists_deriv_smoothTransition_bound
  set w : ℕ → ℝ := fun n => 5 * B * ((n : ℝ) + 1) with hw
  have hwpos : ∀ n, 0 < w n := fun n => by simp only [hw]; positivity
  set φ : ℕ → ℝ → ℝ := fun n t => 1 - Real.smoothTransition ((t - n) / w n) with hφ
  have hφsm : ∀ n, ContDiff ℝ ∞ (φ n) := fun n => by
    simp only [hφ]
    exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _))
  have hφd : ∀ n t, |deriv (φ n) t| ≤ B / w n := by
    intro n t
    have h1 : HasDerivAt (fun t : ℝ => (t - n) / w n) (1 / w n) t :=
      ((hasDerivAt_id t).sub_const (n : ℝ)).div_const (w n)
    have h2 := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
        _).hasDerivAt.comp
      t h1
    have h3 := h2.const_sub 1
    have h4 : deriv (φ n) t = -(deriv Real.smoothTransition ((t - n) / w n) * (1 / w n)) :=
      h3.deriv
    rw [h4, abs_neg, abs_mul, abs_of_pos (by have := hwpos n; positivity : (0 : ℝ) < 1 / w n)]
    calc |deriv Real.smoothTransition ((t - n) / w n)| * (1 / w n) ≤ B * (1 / w n) :=
          mul_le_mul_of_nonneg_right (hB _) (by have := hwpos n; positivity)
      _ = B / w n := by ring
  refine ⟨fun n => φ n ∘ ψ, fun n => ⟨?_, ?_, fun x => ⟨?_, ?_, ?_⟩⟩, fun x => ?_⟩
  · exact (hφsm n).contMDiff.comp hψs
  · refine HasCompactSupport.intro (isCompact_edist_le F x₀ (r := n + w n + 1)
      (by have := hwpos n; positivity)) ?_
    intro x hx
    by_contra hne
    apply hx
    have hne' : Real.smoothTransition ((ψ x - n) / w n) ≠ 1 := by
      intro h; apply hne; simp [hφ, h]
    have hlt : (ψ x - n) / w n < 1 := by
      by_contra h
      push Not at h
      exact hne' (Real.smoothTransition.one_of_one_le h)
    have h5 : ψ x < n + w n := by
      rw [div_lt_one (hwpos n)] at hlt; linarith
    have h6 : f x ≤ n + w n + 1 := by
      have := (abs_le.1 (hψf x)).1
      linarith
    change edist x₀ x ≤ ENNReal.ofReal (n + w n + 1)
    calc edist x₀ x = ENNReal.ofReal (f x) := (ENNReal.ofReal_toReal (hfin _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h6
  · simp only [Function.comp_apply, hφ]
    linarith [Real.smoothTransition.le_one ((ψ x - n) / w n)]
  · simp only [Function.comp_apply, hφ]
    linarith [Real.smoothTransition.nonneg ((ψ x - n) / w n)]
  · apply norm_mgrad_le_of F (by positivity)
    intro v
    have hd := mvfderiv_comp_real F (φ n) ψ (x := x)
      ((hφsm n).differentiable (by simp) _) (hψs.mdifferentiable (by simp) x) v
    change |mvfderiv 𝓘(ℝ, F) (φ n ∘ ψ) x v| ≤ _
    rw [hd, abs_mul]
    have h1 : |mvfderiv 𝓘(ℝ, F) ψ x v| ≤ 5 * ‖v‖ :=
      (abs_mvfderiv_le_norm_mgrad F ψ x v).trans
        (mul_le_mul_of_nonneg_right (hψg x) (norm_nonneg _))
    calc |deriv (φ n) (ψ x)| * |mvfderiv 𝓘(ℝ, F) ψ x v|
        ≤ (B / w n) * (5 * ‖v‖) := mul_le_mul (hφd n _) h1 (abs_nonneg _)
          (by have := hwpos n; positivity)
      _ = 1 / ((n : ℝ) + 1) * ‖v‖ := by
          simp only [hw]
          field_simp
  · refine eventually_atTop.2 ⟨⌈f x + 1⌉₊, fun n hn => ?_⟩
    simp only [Function.comp_apply, hφ]
    have h1 : f x + 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h2 : ψ x ≤ n := by
      have := (abs_le.1 (hψf x)).2
      linarith
    have h3 : Real.smoothTransition ((ψ x - n) / w n) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
        (hwpos n).le)
    rw [h3]; ring
end Cutoffs

end CutCur
