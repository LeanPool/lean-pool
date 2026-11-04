/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.HypersurfaceLocalDeterminant
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Sharp leading term for the hypersurface local determinant exponent.
The linear error depends on dimension alone, not on singular multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Optimize the binomial cutoff at the nonnegative mth root. -/
private theorem local_exponent_root_bound (m s e : ℕ) (hm : 0 < m)
    {μ : ℕ} (R : ℝ) (hR0 : 0 ≤ R)
    (hR : (μ : ℝ) * R ^ m = (m.factorial : ℝ) * s)
    (hcutoff : ∀ K : ℕ, s * K ≤ e + μ * (m + K).choose (m + 1)) :
    (s : ℝ) * R * m / (m + 1) ≤
      e + (m + 1 : ℝ) * s := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hμ0 : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hfac1 : (0 : ℝ) < (m + 1).factorial := by exact_mod_cast Nat.factorial_pos (m + 1)
  have hE0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  by_cases hRm : (m : ℝ) ≤ R
  · let K : ℕ := ⌊R⌋₊ - m
    have hmf : m ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR0).mpr hRm
    have hK : (K : ℝ) = (⌊R⌋₊ : ℝ) - m := Nat.cast_sub hmf
    have hupper : (m : ℝ) + K ≤ R := by linarith [Nat.floor_le hR0]
    have hlower : R - m - 1 ≤ (K : ℝ) := by linarith [Nat.lt_floor_add_one R]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    have hcut := hcutoff K
    have hcutR : (s : ℝ) * K ≤ e +
        (μ : ℝ) * ((n + 1 + K).choose (n + 2) : ℝ) := by exact_mod_cast hcut
    have hb := Nat.choose_le_pow_div (α := ℝ) (n + 2) (n + 1 + K)
    have hpow : ((n + 1 + K : ℕ) : ℝ) ^ (n + 2) ≤ R ^ (n + 2) := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hupper
    have hb' := hb.trans (div_le_div_of_nonneg_right hpow (le_of_lt hfac1))
    have hfacEq : ((n + 2).factorial : ℝ) = ((n + 1 : ℕ) : ℝ) * (n + 1).factorial +
        (n + 1).factorial := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      ring
    have hp : (μ : ℝ) * (R ^ (n + 2) / (n + 2).factorial) =
        (s : ℝ) * R / ((n + 1 : ℕ) + 1 : ℝ) := by
      calc
        _ = ((μ : ℝ) * R ^ (n + 1)) * R / (n + 2).factorial := by
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          ring
        _ = ((n + 1).factorial : ℝ) * s * R / (n + 2).factorial := by rw [hR]
        _ = _ := by
          apply (div_eq_div_iff (ne_of_gt hfac1) (ne_of_gt hm1)).mpr
          rw [hfacEq]
          ring
    have hpenalty := mul_le_mul_of_nonneg_left hb' hμ0
    rw [hp] at hpenalty
    have hmain : (s : ℝ) * K ≤ e +
        (s : ℝ) * R / ((n + 1 : ℕ) + 1 : ℝ) := by linarith
    have hlow := mul_le_mul_of_nonneg_left hlower hs0
    apply (div_le_iff₀ hm1).mpr
    have hmain' := (le_div_iff₀ hm1).mp
      (show (s : ℝ) * K - e ≤
        (s : ℝ) * R / ((n + 1 : ℕ) + 1 : ℝ) by linarith)
    nlinarith
  · have hsmall : R ≤ m := le_of_lt (lt_of_not_ge hRm)
    have hprod := mul_le_mul_of_nonneg_left hsmall hs0
    apply (div_le_iff₀ hm1).mpr
    have hsr : 0 ≤ (s : ℝ) * R := mul_nonneg hs0 hR0
    nlinarith

/-- The sharp multiplicity-dependent leading term, with a dimension-only
linear error. This is the numerical bound needed in CCDN Section 2. -/
private theorem local_exponent_lower_bound (m s e : ℕ) (hm : 0 < m)
    {μ : ℕ} (hμ : 0 < μ)
    (hcutoff : ∀ K : ℕ, s * K ≤ e + μ * (m + K).choose (m + 1)) :
    (s : ℝ) * (((m.factorial : ℝ) * s / μ) ^ (1 / (m : ℝ))) * m / (m + 1) ≤
      e + (m + 1 : ℝ) * s := by
  have hbase : (0 : ℝ) ≤ (m.factorial : ℝ) * s / μ := by positivity
  apply local_exponent_root_bound m s e hm _ (Real.rpow_nonneg hbase _) ?_ hcutoff
  rw [one_div, Real.rpow_inv_natCast_pow hbase (Nat.ne_of_gt hm)]
  have hμ0 : (μ : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hμ
  field_simp

/-- Under the binomial cutoff hypothesis, `(m!/μ)^(1/m) · m/(m+1) · s^(1+1/m) − (m+1)s ≤ e`:
the local exponent bound in the paper's separated-power notation. The error constant `m+1` is
uniform in both the equation and its multiplicity. -/
theorem local_exponent_separated_lower_bound (m s e : ℕ) (hm : 0 < m)
    {μ : ℕ} (hμ : 0 < μ)
    (hcutoff : ∀ K : ℕ, s * K ≤ e + μ * (m + K).choose (m + 1)) :
    ((m.factorial : ℝ) / μ) ^ (1 / (m : ℝ)) * m / (m + 1) *
      (s : ℝ) ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * s ≤
        e := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hb : (0 : ℝ) ≤ (m.factorial : ℝ) / μ := by positivity
  have hpower : (s : ℝ) ^ (1 + 1 / (m : ℝ)) = s * (s : ℝ) ^ (1 / (m : ℝ)) := by
    rw [Real.rpow_add' hs (by positivity), Real.rpow_one]
  have hsplit : (((m.factorial : ℝ) * s / μ) ^ (1 / (m : ℝ))) =
      ((m.factorial : ℝ) / μ) ^ (1 / (m : ℝ)) * (s : ℝ) ^ (1 / (m : ℝ)) := by
    rw [show (m.factorial : ℝ) * s / μ = ((m.factorial : ℝ) / μ) * s by ring,
      Real.mul_rpow hb hs]
  have h := local_exponent_lower_bound m s e hm hμ hcutoff
  rw [hsplit] at h
  rw [hpower]
  convert (sub_le_iff_le_add.mpr h) using 1
  ring

/-- The local hypersurface profile satisfies the cutoff hypothesis in every
positive dimension. -/
lemma hypersurfaceMultiplicityExponent_cutoff_pos (m s K : ℕ) (hm : 0 < m)
    {μ : ℕ} (hμ : 0 < μ) :
    s * K ≤ hypersurfaceMultiplicityExponent m μ s + μ * (m + K).choose (m + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact hypersurfaceMultiplicityExponent_cutoff n s K hμ

/-- The sharp local estimate in the paper's separated-power notation. -/
theorem hypersurfaceMultiplicityExponent_lower_bound (m s : ℕ) (hm : 0 < m)
    {μ : ℕ} (hμ : 0 < μ) :
    ((m.factorial : ℝ) / μ) ^ (1 / (m : ℝ)) * m / (m + 1) *
      (s : ℝ) ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * s ≤
        hypersurfaceMultiplicityExponent m μ s :=
  local_exponent_separated_lower_bound m s _ hm hμ
    (fun K => hypersurfaceMultiplicityExponent_cutoff_pos m s K hm hμ)

end
end CCDN
