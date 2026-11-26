/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.Linarith

/-!
# A slit ball at the end of a straight arc

For the leaf-entry patch on XII page 243, straighten the incident arc
near its end. The local complement is a ball with the positive real
ray removed and its origin restored. It is star-convex at that origin.
After the origin is removed too, it is star-convex at a negative real
point. Thus the patch contracts to its leaf and its puncture stays
path-connected.
-/

public section

namespace GraphMinor.GM12

open Set Metric

/-- A ball slit along the positive real ray, with its tip retained,
is star-convex at that tip. -/
theorem starConvex_slit_ball_tip
    {q : ℂ} (hq : q.im = 0) {δ : ℝ} (hδ : 0 < δ) :
    StarConvex ℝ q (ball q δ ∩ {z : ℂ | z.im ≠ 0 ∨ z.re ≤ q.re}) := by
  intro x hx a b ha hb hab
  refine ⟨(convex_ball q δ) (mem_ball_self hδ) hx.1 ha hb hab, ?_⟩
  change (a • q + b • x).im ≠ 0 ∨ (a • q + b • x).re ≤ q.re
  by_cases hb0 : b = 0
  · right
    have ha1 : a = 1 := by linarith
    simp only [hb0, ha1, one_smul, zero_smul, add_zero]
    exact le_rfl
  · rcases hx.2 with hxim | hxre
    · left
      simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul, hq, mul_zero, zero_add]
        using mul_ne_zero hb0 hxim
    · right
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      have hmul := mul_nonneg hb (sub_nonneg.mpr hxre)
      have hsum : a * q.re + b * q.re = q.re := by rw [← add_mul, hab, one_mul]
      nlinarith only [hmul, hsum]

/-- The punctured slit ball is star-convex at every negative real
point in the ball. -/
theorem starConvex_slit_ball_negative
    {q w : ℂ} (hwim : w.im = 0) (hwre : w.re < q.re)
    {δ : ℝ} (hwball : w ∈ ball q δ) :
    StarConvex ℝ w (ball q δ ∩ {z : ℂ | z.im ≠ 0 ∨ z.re < q.re}) := by
  intro x hx a b ha hb hab
  refine ⟨(convex_ball q δ) hwball hx.1 ha hb hab, ?_⟩
  change (a • w + b • x).im ≠ 0 ∨ (a • w + b • x).re < q.re
  by_cases hb0 : b = 0
  · right
    have ha1 : a = 1 := by linarith
    simpa only [hb0, ha1, one_smul, zero_smul, add_zero] using hwre
  · rcases hx.2 with hxim | hxre
    · left
      simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul, hwim, mul_zero, zero_add]
        using mul_ne_zero hb0 hxim
    · right
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hmul₁ := mul_pos hbpos (sub_pos.mpr hxre)
      have hmul₂ := mul_nonneg ha (sub_nonneg.mpr hwre.le)
      have hsum : a * q.re + b * q.re = q.re := by rw [← add_mul, hab, one_mul]
      nlinarith only [hmul₁, hmul₂, hsum]

/-- Removing the tip from the slit ball leaves a path-connected set. -/
theorem isPathConnected_slit_ball_puncture
    {q : ℂ} (hq : q.im = 0) {δ : ℝ} (hδ : 0 < δ) :
    IsPathConnected ((ball q δ ∩ {z : ℂ | z.im ≠ 0 ∨ z.re ≤ q.re}) \ {q}) := by
  let w : ℂ := q - (δ / 2 : ℝ)
  have hwim : w.im = 0 := by simp only [w, Complex.sub_im, Complex.ofReal_im, sub_zero, hq]
  have hwre : w.re < q.re := by
    change (q - (δ / 2 : ℝ)).re < q.re
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hwball : w ∈ ball q δ := by
    rw [mem_ball, dist_eq_norm]
    have heq : w - q = -((δ / 2 : ℝ) : ℂ) := by dsimp [w]; abel
    rw [heq, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
    linarith
  have hpath : IsPathConnected (ball q δ ∩ {z : ℂ | z.im ≠ 0 ∨ z.re < q.re}) :=
    (starConvex_slit_ball_negative hwim hwre hwball).isPathConnected ⟨hwball, Or.inr hwre⟩
  have heq : (ball q δ ∩ {z : ℂ | z.im ≠ 0 ∨ z.re ≤ q.re}) \ {q} =
      ball q δ ∩ {z : ℂ | z.im ≠ 0 ∨ z.re < q.re} := by
    ext z
    constructor
    · rintro ⟨⟨hzball, hzim | hzre⟩, hzne⟩
      · exact ⟨hzball, Or.inl hzim⟩
      · refine ⟨hzball, ?_⟩
        by_cases hzim : z.im = 0
        · right
          apply lt_of_le_of_ne hzre
          intro he
          have hzq : z = q := Complex.ext he (hzim.trans hq.symm)
          exact hzne hzq
        · exact Or.inl hzim
    · rintro ⟨hzball, hzim | hzre⟩
      · exact ⟨⟨hzball, Or.inl hzim⟩, fun he => hzim (he ▸ hq)⟩
      · exact ⟨⟨hzball, Or.inr hzre.le⟩, fun he => hzre.ne (congrArg Complex.re he)⟩
  exact heq.symm ▸ hpath

end GraphMinor.GM12
