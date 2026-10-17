/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ConcaveSlopes
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ProfileSlopes
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Recurrence
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Growth of the scalar profile

This file proves the scalar implication of Section 6 (Lemma 6.1). The profile
properties are explicit hypotheses: the construction of a profile from a tensor
character and the proof of those properties are separate arguments.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- The scalar profile hypotheses used in Section 6. Only positive indices
carry mathematical content; the values on either coordinate axis are unused. -/
structure ScalarProfile (t : ℝ) where
  value : ℕ → ℕ → ℝ
  positive : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 0 < value a b
  symmetric : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → value a b = value b a
  boundary : ∀ b : ℕ, 1 ≤ b → value 1 b = (b : ℝ)
  concave : ∀ a h : ℕ, 1 ≤ a → 2 ≤ h →
    value a (h - 1) + value a (h + 1) ≤ 2 * value a h
  tripling : ∀ a h : ℕ, 1 ≤ a → 1 ≤ h →
    3 * value a h ≤ value a (3 * h + a - 1)
  rank_bound : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    value a b ≤ ((a : ℝ) + (b : ℝ) - 1) ^ (1 / t)

namespace ScalarProfile

/-- Each row has a nonnegative limiting slope that bounds every increment
from below and equals the limit of the row divided by its index. -/
theorem exists_row_slope {t : ℝ} (P : ScalarProfile t) (a : ℕ) (ha : 1 ≤ a) :
    ∃ g : ℝ, 0 ≤ g ∧
      (∀ h : ℕ, 1 ≤ h → g ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 g) := by
  have hd : Antitone (fun n : ℕ => P.value a (n + 2) - P.value a (n + 1)) := by
    apply antitone_nat_of_succ_le
    intro n
    have hc := P.concave a (n + 2) ha (by omega)
    have hpred : n + 2 - 1 = n + 1 := by omega
    rw [hpred] at hc
    simp only [Nat.add_assoc] at *
    linarith
  obtain ⟨g, hg, hinc, _, hratio⟩ := exists_concave_slope_limit
    (P := P.value a) (fun n => P.positive a (n + 1) ha (by omega)) hd
  refine ⟨g, hg, ?_, hratio⟩
  intro h hh
  cases h with
  | zero => omega
  | succ n => simpa only [Nat.add_assoc] using hinc n

/-- Choose the row slopes together, retaining their bounds and limits on all
positive rows. -/
theorem exists_row_slopes {t : ℝ} (P : ScalarProfile t) :
    ∃ g : ℕ → ℝ, ∀ a : ℕ, 1 ≤ a → 0 ≤ g a ∧
      (∀ h : ℕ, 1 ≤ h → g a ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 (g a)) := by
  classical
  have hex (a : ℕ) : ∃ g : ℝ, 1 ≤ a → 0 ≤ g ∧
      (∀ h : ℕ, 1 ≤ h → g ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 g) := by
    by_cases ha : 1 ≤ a
    · obtain ⟨g, hg⟩ := P.exists_row_slope a ha
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun ha' => False.elim (ha ha')⟩
  choose g hg using hex
  exact ⟨g, hg⟩

/-- The exact polynomial lower bound on the diagonal, obtained from row
concavity, shifted tripling, and the simultaneous scalar induction. -/
theorem diagonal_fourth_power_lower {t : ℝ} (P : ScalarProfile t)
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ 4 ≤ P.value n n ^ 3 := by
  obtain ⟨g, hg⟩ := P.exists_row_slopes
  have hupper : ∀ a : ℕ, 1 ≤ a →
      P.value a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
    apply profile_diagonal_le_slope
    · intro a ha h hh
      exact P.tripling a h ha hh
    · intro a ha
      exact (hg a ha).2.2
  have hincrement : ∀ a : ℕ, 1 ≤ a →
      P.value a a + g a + g (a + 1) ≤ P.value (a + 1) (a + 1) := by
    apply diagonal_increment_of_slope_lower
    · intro a ha b hb
      exact P.symmetric a b ha hb
    · intro a ha h hh
      exact (hg a ha).2.1 h hh
  have hDbase : 1 ≤ P.value 1 1 := by
    rw [P.boundary 1 (by omega)]
    norm_num
  have hgbase : 1 ≤ g 1 := by
    have hu := hupper 1 (by omega)
    rw [P.boundary 1 (by omega)] at hu
    norm_num at hu
    exact hu
  exact MatrixMultiplication.AuxiliarySeparation.diagonal_fourth_power_lower_of_one_le
    (fun a => P.value a a) g hgbase hDbase hupper hincrement n hn

/-- Lemma 6.1: a positive symmetric profile satisfying the stated concavity,
tripling, boundary, and rank bounds has exponent at most `3/4`. -/
theorem exponent_le_three_quarters {t : ℝ} (P : ScalarProfile t) (ht : 0 < t) :
    t ≤ 3 / 4 := by
  apply diagonal_exponent_le_three_quarters (D := fun a => P.value a a) ht
  · intro n hn
    exact (P.positive n n hn hn).le
  · exact P.diagonal_fourth_power_lower
  · intro n hn
    have hu := P.rank_bound n n hn hn
    simpa only [two_mul] using hu

end ScalarProfile

/-- The scalar profile implication, with every profile assumption displayed
explicitly rather than bundled in `ScalarProfile`. -/
theorem profile_exponent_le_three_quarters {P : ℕ → ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hpositive : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 0 < P a b)
    (hsymmetric : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → P a b = P b a)
    (hboundary : ∀ b : ℕ, 1 ≤ b → P 1 b = (b : ℝ))
    (hconcave : ∀ a h : ℕ, 1 ≤ a → 2 ≤ h →
      P a (h - 1) + P a (h + 1) ≤ 2 * P a h)
    (htripling : ∀ a h : ℕ, 1 ≤ a → 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hrank : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      P a b ≤ ((a : ℝ) + (b : ℝ) - 1) ^ (1 / t)) :
    t ≤ 3 / 4 := by
  exact ScalarProfile.exponent_le_three_quarters
    ⟨P, hpositive, hsymmetric, hboundary, hconcave, htripling, hrank⟩ ht

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
