/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.SummatoryAbel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Fractional moments from a linear summatory bound -/

@[expose] public section

namespace NairTenenbaum

open Finset Real MeasureTheory intervalIntegral

theorem arithmeticSummatory_rpow_le {a : ℕ → ℝ} (ha0 : a 0 = 0)
    (ha : ∀ n, 0 ≤ a n) {C θ x : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 1 ≤ t → arithmeticSummatory a t ≤ C * t)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hx : 1 ≤ x) :
    arithmeticSummatory (fun n => a n / (n : ℝ) ^ θ) x ≤ C / (1 - θ) * x ^ (1 - θ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hcont (r : ℝ) : ContinuousOn (fun t : ℝ => t ^ r) (Set.Icc 1 x) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (by dsimp; linarith [ht.1]))
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun t : ℝ => t ^ (-θ)) (-θ * t ^ (-θ - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))
  have H := arithmeticSummatory_mul_eq_sub_integral ha0 hx hd ((hcont (-θ - 1)).const_mul (-θ))
  have heq : arithmeticSummatory (fun n => (n : ℝ) ^ (-θ) * a n) x =
      arithmeticSummatory (fun n => a n / (n : ℝ) ^ θ) x := by
    apply sum_congr rfl
    intro n hn
    dsimp only
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    ring
  rw [heq] at H
  have hi : IntervalIntegrable (fun t => t ^ (-θ - 1) * arithmeticSummatory a t) volume 1 x :=
    (arithmeticSummatory_mono ha).intervalIntegrable.continuousOn_mul
      (by simpa only [Set.uIcc_of_le hx] using hcont (-θ - 1))
  have hi' : IntervalIntegrable (fun t : ℝ => C * t ^ (-θ)) volume 1 x :=
    ((hcont (-θ)).const_mul C).intervalIntegrable_of_Icc hx
  have hb : (∫ t in (1 : ℝ)..x, t ^ (-θ - 1) * arithmeticSummatory a t) ≤
      C * ((x ^ (1 - θ) - 1) / (1 - θ)) := by
    calc
      _ ≤ ∫ t in (1 : ℝ)..x, C * t ^ (-θ) := by
        apply integral_mono_on hx hi hi'
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        calc
          _ ≤ t ^ (-θ - 1) * (C * t) :=
            mul_le_mul_of_nonneg_left (hbound t ht.1) (Real.rpow_nonneg ht0.le _)
          _ = C * t ^ (-θ) := by
            have HE : t ^ (-θ - 1) * t = t ^ (-θ) := by
              calc
                _ = t ^ (-θ - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
                _ = t ^ ((-θ - 1) + 1) := (Real.rpow_add ht0 _ _).symm
                _ = _ := by congr 1; ring
            calc
              _ = C * (t ^ (-θ - 1) * t) := by ring
              _ = _ := by rw [HE]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < -θ))]
        rw [show -θ + 1 = 1 - θ by ring, Real.one_rpow]
  have hend : x ^ (-θ) * arithmeticSummatory a x ≤ C * x ^ (1 - θ) := by
    calc
      _ ≤ x ^ (-θ) * (C * x) := mul_le_mul_of_nonneg_left (hbound x hx) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add hx0, Real.rpow_one]; ring
  have hrewrite : (∫ t in (1 : ℝ)..x, -θ * t ^ (-θ - 1) * arithmeticSummatory a t) =
      -θ * ∫ t in (1 : ℝ)..x, t ^ (-θ - 1) * arithmeticSummatory a t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [H, hrewrite]
  have hden : 0 < 1 - θ := by linarith
  have hlast : C * x ^ (1 - θ) + θ * (C * ((x ^ (1 - θ) - 1) / (1 - θ))) ≤
      C / (1 - θ) * x ^ (1 - θ) := by
    calc
      _ = C / (1 - θ) * x ^ (1 - θ) - C * θ / (1 - θ) := by
        field_simp [hden.ne']
        ring
      _ ≤ _ := sub_le_self _ (div_nonneg (mul_nonneg hC hθ) hden.le)
  have hmul := mul_le_mul_of_nonneg_left hb hθ
  linarith

end NairTenenbaum
