/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ConcaveSlopes

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Shifted tripling and diagonal increments

These are the two estimates on the limiting row slopes used in Section 6.
Iteration retains the additive shift in the tripling inequality. Symmetry
then expresses a diagonal step as one increment in each of two adjacent rows.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- The indices obtained by repeatedly applying the affine tripling map. -/
def shiftedTriplingIndex (c h : ℕ) : ℕ → ℕ
  | 0 => h
  | j + 1 => 3 * shiftedTriplingIndex c h j + c

/-- Starting at a positive index, affine tripling escapes to infinity. -/
theorem shiftedTriplingIndex_lower (c h : ℕ) (hh : 1 ≤ h) (j : ℕ) :
    h + j ≤ shiftedTriplingIndex c h j := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      simp only [shiftedTriplingIndex]
      omega

theorem shiftedTriplingIndex_tendsto (c h : ℕ) (hh : 1 ≤ h) :
    Tendsto (shiftedTriplingIndex c h) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  change j ≤ shiftedTriplingIndex c h j
  have := shiftedTriplingIndex_lower c h hh j
  omega

/-- The exact affine solution, written without truncated natural subtraction. -/
theorem shiftedTriplingIndex_cast (c h j : ℕ) :
    (shiftedTriplingIndex c h j : ℝ) + (c : ℝ) / 2 =
      (3 : ℝ) ^ j * ((h : ℝ) + (c : ℝ) / 2) := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      simp only [shiftedTriplingIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        pow_succ]
      nlinarith

/-- Iterating the tripling inequality multiplies the profile by powers of three. -/
theorem shiftedTripling_profile_lower {P : ℕ → ℝ} {c h : ℕ} (hh : 1 ≤ h)
    (htrip : ∀ n : ℕ, 1 ≤ n → 3 * P n ≤ P (3 * n + c)) (j : ℕ) :
    (3 : ℝ) ^ j * P h ≤ P (shiftedTriplingIndex c h j) := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      have hj : 1 ≤ shiftedTriplingIndex c h j := by
        have := shiftedTriplingIndex_lower c h hh j
        omega
      have hstep := htrip (shiftedTriplingIndex c h j) hj
      simp only [shiftedTriplingIndex, pow_succ]
      nlinarith

/-- A row with a limiting linear slope and shifted tripling lies below the
corresponding affine multiple of that slope. -/
theorem profile_le_affine_slope {P : ℕ → ℝ} {g : ℝ} {c h : ℕ}
    (hh : 1 ≤ h)
    (htrip : ∀ n : ℕ, 1 ≤ n → 3 * P n ≤ P (3 * n + c))
    (hlim : Tendsto (fun n : ℕ => P n / (n : ℝ)) atTop (𝓝 g)) :
    P h ≤ ((h : ℝ) + (c : ℝ) / 2) * g := by
  have hpow : Tendsto (fun j : ℕ => (3 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hzero : Tendsto (fun j : ℕ => ((c : ℝ) / 2) / (3 : ℝ) ^ j)
      atTop (𝓝 0) := hpow.const_div_atTop _
  have hindex : Tendsto
      (fun j : ℕ => (shiftedTriplingIndex c h j : ℝ) / (3 : ℝ) ^ j)
      atTop (𝓝 ((h : ℝ) + (c : ℝ) / 2)) := by
    have heq (j : ℕ) :
        (shiftedTriplingIndex c h j : ℝ) / (3 : ℝ) ^ j =
          (h : ℝ) + (c : ℝ) / 2 - ((c : ℝ) / 2) / (3 : ℝ) ^ j := by
      have hj := shiftedTriplingIndex_cast c h j
      have hp : (3 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      nlinarith
    simpa only [heq, sub_zero] using tendsto_const_nhds.sub hzero
  have hproduct := (hlim.comp (shiftedTriplingIndex_tendsto c h hh)).mul hindex
  have hprofile : Tendsto
      (fun j : ℕ => P (shiftedTriplingIndex c h j) / (3 : ℝ) ^ j)
      atTop (𝓝 (g * ((h : ℝ) + (c : ℝ) / 2))) := by
    apply hproduct.congr'
    apply Eventually.of_forall
    intro j
    have hj : (shiftedTriplingIndex c h j : ℝ) ≠ 0 := by
      have := shiftedTriplingIndex_lower c h hh j
      exact_mod_cast (show shiftedTriplingIndex c h j ≠ 0 by omega)
    dsimp only [Function.comp_def]
    field_simp
  have hbound : ∀ j : ℕ, P h ≤ P (shiftedTriplingIndex c h j) / (3 : ℝ) ^ j := by
    intro j
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) j)).mpr
    simpa only [mul_comm] using shiftedTripling_profile_lower hh htrip j
  simpa only [mul_comm] using ge_of_tendsto hprofile (Eventually.of_forall hbound)

/-- The row estimate in the positive-index notation of the paper. -/
theorem profile_row_le_slope {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (htrip : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hlim : ∀ a : ℕ, 1 ≤ a →
      Tendsto (fun h : ℕ => P a h / (h : ℝ)) atTop (𝓝 (g a)))
    (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    P a h ≤ ((h : ℝ) + ((a : ℝ) - 1) / 2) * g a := by
  have ht : ∀ n : ℕ, 1 ≤ n → 3 * P a n ≤ P a (3 * n + (a - 1)) := by
    intro n hn
    have hi : 3 * n + (a - 1) = 3 * n + a - 1 := by omega
    rw [hi]
    exact htrip a ha n hn
  have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha, Nat.cast_one]
  simpa only [hcast] using profile_le_affine_slope hh ht (hlim a ha)

/-- The diagonal is bounded above by the limiting row slope with the precise
coefficient `(3a-1)/2`. -/
theorem profile_diagonal_le_slope {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (htrip : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hlim : ∀ a : ℕ, 1 ≤ a →
      Tendsto (fun h : ℕ => P a h / (h : ℝ)) atTop (𝓝 (g a)))
    (a : ℕ) (ha : 1 ≤ a) :
    P a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
  have hc : (a : ℝ) + ((a : ℝ) - 1) / 2 = (3 * (a : ℝ) - 1) / 2 := by ring
  simpa only [hc] using profile_row_le_slope htrip hlim a a ha ha

/-- Symmetry identifies a diagonal step with one increment in each adjacent
row. Only positive-index symmetry and slope bounds are used. -/
theorem diagonal_increment_of_slope_lower {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (hsymm : ∀ a : ℕ, 1 ≤ a → ∀ b : ℕ, 1 ≤ b → P a b = P b a)
    (hinc : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      g a ≤ P a (h + 1) - P a h)
    (n : ℕ) (hn : 1 ≤ n) :
    P n n + g n + g (n + 1) ≤ P (n + 1) (n + 1) := by
  have hfirst := hinc n hn n hn
  have hsecond := hinc (n + 1) (by omega) n hn
  have hsym := hsymm n hn (n + 1) (by omega)
  linarith

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
