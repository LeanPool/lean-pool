/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.Estimates
public import LeanPool.ArnoldKAM.Arnold1963.Basic.Spaces
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
Summation of the exponential lattice kernel in the sum-of-absolute-coordinates norm.
The product decomposition supplies normal convergence bounds for Fourier series.
-/

@[expose] public section
noncomputable section
namespace KamProject.Arnold1963

/-- Splitting an integer Fourier index into its first coordinate and its tail. -/
abbrev fourierIndexSuccEquiv (n : ℕ) : FourierIndex (n + 1) ≃ ℤ × FourierIndex n :=
  (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).symm

theorem hasSum_exp_int_abs {δ : ℝ} (hδ : 0 < δ) :
    HasSum (fun k : ℤ => Real.exp (-δ * |(k : ℝ)|))
      ((1 + Real.exp (-δ)) / (1 - Real.exp (-δ))) := by
  have hr : |Real.exp (-δ)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hn : HasSum (fun m : ℕ => Real.exp (-δ * |((m : ℤ) : ℝ)|))
      (1 - Real.exp (-δ))⁻¹ := by
    convert hasSum_geometric_of_abs_lt_one hr using 1
    funext m
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    ring
  have hm : HasSum (fun m : ℕ => Real.exp (-δ * |((-(m : ℤ)) : ℝ)|))
      (1 - Real.exp (-δ))⁻¹ := by simpa using hn
  have hs := HasSum.of_nat_of_neg
    (f := fun k : ℤ => Real.exp (-δ * |(k : ℝ)|)) hn (by simpa only [Int.cast_neg] using hm)
  have hd : 1 - Real.exp (-δ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (lt_of_le_of_lt (le_abs_self _) hr))
  have he : (1 + Real.exp (-δ)) / (1 - Real.exp (-δ)) =
      (1 - Real.exp (-δ))⁻¹ + (1 - Real.exp (-δ))⁻¹ - 1 := by
    field_simp [hd]
    ring
  rw [he]
  simpa only [Int.cast_zero, abs_zero, mul_zero, Real.exp_zero] using hs

theorem hasSum_exp_indexLength (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    HasSum (fun k : FourierIndex n => Real.exp (-δ * indexLength k))
      (((1 + Real.exp (-δ)) / (1 - Real.exp (-δ))) ^ n) := by
  induction n with
  | zero => simp [indexLength]
  | succ n ih =>
    have hi := hasSum_exp_int_abs hδ
    have hp := hi.mul ih (hi.summable.mul_of_nonneg ih.summable
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
    have he : (fun k : FourierIndex (n+1) => Real.exp (-δ * indexLength k)) =
        (fun p : ℤ × FourierIndex n => Real.exp (-δ * |(p.1 : ℝ)|) *
          Real.exp (-δ * indexLength p.2)) ∘ fourierIndexSuccEquiv n := by
      funext k
      change Real.exp (-δ * indexLength k) =
        Real.exp (-δ * |(k 0 : ℝ)|) * Real.exp (-δ * indexLength (fun j => k j.succ))
      simp only [indexLength, Fin.sum_univ_succ, mul_add, Real.exp_add]
    rw [he]
    simpa [pow_succ, mul_comm] using (fourierIndexSuccEquiv n).hasSum_iff.mpr hp

theorem summable_exp_indexLength (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun k : FourierIndex n => Real.exp (-δ * indexLength k)) :=
  (hasSum_exp_indexLength n hδ).summable

theorem tsum_exp_indexLength_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' k : FourierIndex n, Real.exp (-δ * indexLength k)) ≤ (4 / δ) ^ n := by
  rw [(hasSum_exp_indexLength n hδ).tsum_eq]
  have he : Real.exp (-δ) ≤ 1 := (Real.exp_le_one_iff).mpr (by linarith)
  have hd : 0 < 1 - Real.exp (-δ) := by
    have := half_le_one_sub_exp_neg hδ.le hδ1
    linarith
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ hd).mpr
  have := half_le_one_sub_exp_neg hδ.le hδ1
  apply (mul_le_mul_iff_right₀ hδ).mp
  have heq : δ * (4 / δ * (1 - Real.exp (-δ))) = 4 * (1 - Real.exp (-δ)) := by
    field_simp
  rw [heq]
  nlinarith

end KamProject.Arnold1963
