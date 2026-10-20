/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Proofs.GdConvex

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.OracleTemplate.GeneralizedAccelerated

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma ms_inner {M : ℝ} (hM : 0 < M) (g d : E)
    (hr : ‖g + M • d‖ ≤ M / 2 * ‖d‖) :
    ⟪g, d⟫ ≤ -(3 * M / 8) * ‖d‖ ^ 2 - ‖g‖ ^ 2 / (2 * M) := by
  have hsq : ‖g + M • d‖ ^ 2 ≤ (M / 2 * ‖d‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hr 2
  rw [norm_add_sq_real] at hsq
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsq
  have hM0 := hM.ne'
  field_simp
  nlinarith

lemma damped_step {f : E → ℝ} {g : E → E} {M A a γ : ℝ}
    (hM : 0 < M) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (x z u w : E) (hA : 0 ≤ A) (ha : 0 < a)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hweight : γ * a ^ 2 * M ≤ A + a)
    (hr : let y := (A / (A + a)) • x + (a / (A + a)) • z
      ‖g w + M • (w - y)‖ ≤ M / 2 * ‖w - y‖) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    let B := A + γ * a
    let xnew := ((1 - γ) * A / B) • x + (γ * (A + a) / B) • w
    B * (f xnew - f u) + 1 / 2 * ‖z - (γ * a) • g w - u‖ ^ 2 +
        γ * (A + a) * (3 * M / 8) * ‖w - y‖ ^ 2 ≤
      A * (f x - f u) + 1 / 2 * ‖z - u‖ ^ 2 := by
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  let B := A + γ * a
  let xnew := ((1 - γ) * A / B) • x + (γ * (A + a) / B) • w
  change ‖g w + M • (w - y)‖ ≤ M / 2 * ‖w - y‖ at hr
  change B * (f xnew - f u) + 1 / 2 * ‖z - (γ * a) • g w - u‖ ^ 2 +
    γ * (A + a) * (3 * M / 8) * ‖w - y‖ ^ 2 ≤ _
  have hB : 0 < B := by dsimp [B]; positivity
  have hAa : 0 < A + a := by positivity
  have hx := Gradient.convex_support hc hg w x
  have hu := Gradient.convex_support hc hg w u
  have hid : A • (x - w) + a • (u - w) =
      a • (u - z) + (A + a) • (y - w) := by
    dsimp [y]
    match_scalars
    all_goals field_simp [hAa.ne'] <;> ring
  have hi := congrArg (fun v => ⟪g w, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hneg (v₁ v₂ : E) : ⟪g w, v₁ - v₂⟫ = -⟪g w, v₂ - v₁⟫ := by
    rw [← inner_neg_right]
    congr 1
    module
  rw [hneg u z, hneg y w] at hi
  have hs : (A + a) * (f w - f u) ≤ A * (f x - f u) +
      a * ⟪g w, z - u⟫ + (A + a) * ⟪g w, w - y⟫ := by
    have hx' := mul_le_mul_of_nonneg_left hx hA
    have hu' := mul_le_mul_of_nonneg_left hu ha.le
    nlinarith
  have hsum : (1 - γ) * A / B + γ * (A + a) / B = 1 := by
    dsimp [B]
    field_simp; ring
  have hmix := hc.2 (mem_univ x) (mem_univ w)
    (show 0 ≤ (1 - γ) * A / B by positivity)
    (show 0 ≤ γ * (A + a) / B by positivity) hsum
  change f xnew ≤ _ at hmix
  have hmix' := mul_le_mul_of_nonneg_left hmix hB.le
  have hmix'' : B * (f xnew - f u) ≤
      (1 - γ) * A * (f x - f u) + γ * (A + a) * (f w - f u) := by
    have he : B * (((1 - γ) * A / B) • f x +
        (γ * (A + a) / B) • f w) =
        (1 - γ) * A * f x + γ * (A + a) * f w := by
      simp only [smul_eq_mul]
      field_simp
    rw [he] at hmix'
    dsimp [B] at hmix' ⊢
    nlinarith
  have hs' := mul_le_mul_of_nonneg_left hs hγ.le
  have hinner := ms_inner hM (g w) (w - y) hr
  have hinner' := mul_le_mul_of_nonneg_left hinner
    (show 0 ≤ γ * (A + a) by positivity)
  have hweight' := mul_le_mul_of_nonneg_right hweight
    (show 0 ≤ γ * ‖g w‖ ^ 2 by positivity)
  have hn : z - (γ * a) • g w - u = (z - u) - (γ * a) • g w := by module
  rw [hn, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← real_inner_comm (z - u) (g w)]
  have hcancel : γ ^ 2 * a ^ 2 * ‖g w‖ ^ 2 / 2 ≤
      γ * (A + a) * (‖g w‖ ^ 2 / (2 * M)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < 2 * M by positivity)).mpr
    nlinarith only [hweight']
  dsimp [B] at hmix'' ⊢
  nlinarith only [hmix'', hs', hinner', hcancel]

end LongTails.OracleTemplate.GeneralizedAccelerated
