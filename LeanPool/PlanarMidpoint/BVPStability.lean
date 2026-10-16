/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.GreenOperator
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Dirichlet stability with a quantitatively absorbable differential residual. -/

@[expose] public section
namespace PlanarMidpoint

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A residual bound controls a zero-endpoint curve and its velocity whenever the
sum of the two Lipschitz constants is less than one. Compactness supplies the
maximum, so no a priori bound on the unknown error is assumed. -/
theorem dirichlet_stability (x v a : ℝ → V) (R Lx Lv : ℝ)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (a t) t)
    (hx0 : x 0 = 0) (hx1 : x 1 = 0)
    (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv) (hsmall : Lx + Lv < 1)
    (hres : ∀ t ∈ Icc (0 : ℝ) 1, ‖a t‖ ≤ R + Lx * ‖x t‖ + Lv * ‖v t‖)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x t‖ ≤ R / (1 - Lx - Lv) ∧ ‖v t‖ ≤ R / (1 - Lx - Lv) := by
  have hxc : ContinuousOn x (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hx s hs).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hv s hs).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) (hxc.norm.sup hvc.norm)
  let M := max ‖x s‖ ‖v s‖
  have hxM : ∀ u ∈ Icc (0 : ℝ) 1, ‖x u‖ ≤ M :=
    fun u hu ↦ (le_max_left _ _).trans (hmax hu)
  have hvM : ∀ u ∈ Icc (0 : ℝ) 1, ‖v u‖ ≤ M :=
    fun u hu ↦ (le_max_right _ _).trans (hmax hu)
  have haM : ∀ u ∈ Icc (0 : ℝ) 1, ‖a u‖ ≤ R + Lx * M + Lv * M := by
    intro u hu
    have h1 := mul_le_mul_of_nonneg_left (hxM u hu) hLx
    have h2 := mul_le_mul_of_nonneg_left (hvM u hu) hLv
    linarith [hres u hu]
  have hMx : ‖x s‖ ≤ R + Lx * M + Lv * M :=
    dirichlet_position_bound x v a _ hx hv haM hx0 hx1 s hs
  have hMv : ‖v s‖ ≤ R + Lx * M + Lv * M :=
    dirichlet_velocity_bound x v a _ hx hv haM hx0 hx1 s hs
  have hMM : M ≤ R + Lx * M + Lv * M := max_le hMx hMv
  have hd : 0 < 1 - Lx - Lv := by linarith
  have hfinal : M ≤ R / (1 - Lx - Lv) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  exact ⟨(hxM t ht).trans hfinal, (hvM t ht).trans hfinal⟩

/-- Stability for a true and an approximate curve having the same endpoints. -/
theorem bvp_stability (x v a y w b : ℝ → V) (R Lx Lv : ℝ)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (a t) t)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt y (w t) t)
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt w (b t) t)
    (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv) (hsmall : Lx + Lv < 1)
    (hres : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖a t - b t‖ ≤ R + Lx * ‖x t - y t‖ + Lv * ‖v t - w t‖)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x t - y t‖ ≤ R / (1 - Lx - Lv) ∧ ‖v t - w t‖ ≤ R / (1 - Lx - Lv) := by
  exact dirichlet_stability (fun s ↦ x s - y s) (fun s ↦ v s - w s)
    (fun s ↦ a s - b s) R Lx Lv
    (fun s hs ↦ (hx s hs).fun_sub (hy s hs))
    (fun s hs ↦ (hv s hs).fun_sub (hw s hs))
    (sub_eq_zero.mpr h0) (sub_eq_zero.mpr h1) hLx hLv hsmall hres t ht

end PlanarMidpoint
