/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyCoarseLogBound
public import LeanPool.NairTenenbaum.Progressions.AffineIntervalRange

/-! # Hooley moments without the no-fixed-prime-divisor restriction

A logarithmic exponent margin absorbs the subexponential factor. The interval
range `y ≤ x/2` suffices for the power-shaped intervals in Theorem 2.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset Real

theorem exists_hooleyPolynomialSum_log_margin_unrestricted {Q : ℤ[X]}
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t α δ : ℝ}
    (ht : 1 ≤ t) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x y : ℝ,
      x₀ < x → x ^ α ≤ y → y ≤ x / 2 →
        hooleyPolynomialSum Q t x y ≤ C * y * (Real.log x) ^ ((2 : ℝ) ^ t - t - 1 + δ) := by
  classical
  obtain ⟨M, hM, HM⟩ := exists_affine_primitive_reduction hirr
  let R (a : Fin M) := (affineRestriction Q M a.val).primPart
  have HR (a : Fin M) := exists_hooleyPolynomialSum_log_margin (HM a.val).1 (HM a.val).2 ht
      (half_pos hα) hδ
  choose z B hz hB HB using HR
  choose X hX hXM HX using fun a : Fin M => exists_affine_interval_range hM hα (z a)
  let w (a : Fin M) : ℝ := ((affineRestriction Q M a.val).content.natAbs.divisors.card : ℝ) ^ t
  let x₀ : ℝ := (∑ a : Fin M, max (X a) 0) + M + 2
  let C : ℝ := 1 + ∑ a : Fin M, w a * B a
  have hs : 0 ≤ ∑ a : Fin M, max (X a) 0 := sum_nonneg (fun _ _ => le_max_right _ _)
  have hw (a : Fin M) : 0 ≤ w a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCsum : 0 ≤ ∑ a : Fin M, w a * B a := sum_nonneg (fun a _ => mul_nonneg (hw a) (hB a).le)
  have hx₀ : 1 < x₀ := by dsimp [x₀]; linarith [Nat.cast_nonneg (α := ℝ) M]
  have hxM : (M : ℝ) ≤ x₀ := by dsimp [x₀]; linarith
  have hXa (a : Fin M) : X a ≤ x₀ := by
    have H := single_le_sum (fun b (_ : b ∈ (univ : Finset (Fin M))) => le_max_right (X b) 0)
        (mem_univ a)
    have HM₀ : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    dsimp [x₀]
    linarith [le_max_left (X a) 0]
  refine ⟨x₀, C, hx₀, by dsimp [C]; linarith, fun x y hx hy hyx => ?_⟩
  have hx₁ : 1 < x := hx₀.trans hx
  have hxpos : 0 < x := by linarith
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hxpos.le α).trans hy
  have hM₀ : (0 : ℝ) < M := by exact_mod_cast hM
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hyM : y / M ≤ y := (div_le_self hy₀ hM₁)
  let b : ℝ := (2 : ℝ) ^ t - t - 1 + δ
  have hb : 0 ≤ b := by dsimp [b]; linarith [hooley_short_exponent_nonneg ht]
  have HA (a : Fin M) :
      hooleyPolynomialSum (R a) t ((x - a.val) / M) (y / M) ≤ B a * y * (Real.log x) ^ b := by
    obtain ⟨hu, hv, hvu, hux⟩ := HX a x y ((hXa a).trans_lt hx) hy hyx a.val a.isLt
    have hu₁ : 1 < (x - (a.val : ℝ)) / M := (hz a).trans hu
    have HL := Real.log_le_log (show 0 < (x - (a.val : ℝ)) / M by linarith) hux
    have HP := Real.rpow_le_rpow (Real.log_pos hu₁).le HL hb
    apply (HB a _ _ hu hv hvu).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hyM (hB a).le) HP
      (Real.rpow_nonneg (Real.log_pos hu₁).le _) (mul_nonneg (hB a).le hy₀)
  have HS := hooleyPolynomialSum_le_affine_primitive_sums Q hM (by linarith : 0 ≤ t)
    (hxM.trans hx.le) hy₀
  rw [← Fin.sum_univ_eq_sum_range] at HS
  calc
    _ ≤ ∑ a : Fin M, w a * hooleyPolynomialSum (R a) t ((x - a.val) / M) (y / M) := HS
    _ ≤ ∑ a : Fin M, w a * (B a * y * (Real.log x) ^ b) :=
      sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (HA a) (hw a))
    _ = (∑ a : Fin M, w a * B a) * y * (Real.log x) ^ b := by
      simp only [sum_mul]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ C * y * (Real.log x) ^ b := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Real.log_pos hx₁).le _)
      apply mul_le_mul_of_nonneg_right _ hy₀
      dsimp [C]
      linarith

end NairTenenbaum
