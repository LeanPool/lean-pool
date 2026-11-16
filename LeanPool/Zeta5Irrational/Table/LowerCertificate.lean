/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.Zeta5Irrational.PotentialV
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.TableCheck

/-! # Shared lower certificates for the external field -/

@[expose] public section

namespace Zeta5Irrational

/-- Transfer square-root and arctangent enclosures to the product in the external field. -/
lemma Vfield_product_lower {t lo hi s A B : ℝ} (ht : 0 < t) (hlo : 0 < lo)
    (hrootLo : lo ≤ Real.sqrt t) (hrootHi : Real.sqrt t ≤ hi)
    (hA : A ≤ Real.arctan (1 / hi)) (hB : Real.arctan ((3 / 40) / lo) ≤ B)
    (side : (s = lo ∧ 0 ≤ Real.pi + A - 6 * B) ∨
      (s = hi ∧ Real.pi + A - 6 * B ≤ 0)) :
    s * (Real.pi + A - 6 * B) ≤ Real.sqrt t *
      (Real.pi + Real.arctan (1 / Real.sqrt t) -
        6 * Real.arctan ((3 / 40) / Real.sqrt t)) := by
  have hroot := Real.sqrt_pos.mpr ht
  have hA' := arctan_ge_of_le (one_div_le_one_div_of_le hroot hrootHi) hA
  have hB' := arctan_le_of_ge
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3 / 40) hlo hrootLo) hB
  have hangle : Real.pi + A - 6 * B ≤ Real.pi + Real.arctan (1 / Real.sqrt t) -
      6 * Real.arctan ((3 / 40) / Real.sqrt t) := by
    linarith only [hA', hB']
  apply le_trans ?_ (mul_le_mul_of_nonneg_left hangle hroot.le)
  rcases side with ⟨rfl, hsign⟩ | ⟨rfl, hsign⟩
  · exact mul_le_mul_of_nonneg_right hrootLo hsign
  · exact mul_le_mul_of_nonpos_right hrootHi hsign

/-- Check the closed geometry in the rationals and retain the analytic logarithm bounds. -/
lemma Vfield_lower_certificate {t lo hi s r₁ r₂ z₁ z₂ L U : ℚ} {A B : ℝ}
    (certificate : 0 < t ∧ 0 < lo ∧ lo ^ 2 ≤ t ∧ 0 ≤ hi ∧ t ≤ hi ^ 2 ∧
      z₁ = 1 / hi ∧ z₂ = (3 / 40) / lo ∧ r₁ = 1 + t ∧ r₂ = t + (3 / 40) ^ 2)
    (hL : (L : ℝ) ≤ Real.log (r₁ : ℝ)) (hU : Real.log (r₂ : ℝ) ≤ (U : ℝ))
    (hA : A ≤ Real.arctan (z₁ : ℝ)) (hB : Real.arctan (z₂ : ℝ) ≤ B)
    (side : (s = lo ∧ 0 ≤ Real.pi + A - 6 * B) ∨
      (s = hi ∧ Real.pi + A - 6 * B ≤ 0)) :
    (L : ℝ) - 6 * (3 / 40) * (U : ℝ) - 2 + 12 * (3 / 40) +
      2 * ((s : ℝ) * (Real.pi + A - 6 * B)) ≤ Vfield (t : ℝ) := by
  rcases certificate with ⟨ht, hlo, hslo, hhi, hshi, hz₁, hz₂, hr₁, hr₂⟩
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hlo' : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hslo' : (lo : ℝ) ≤ Real.sqrt t :=
    le_sqrt_of_sq_le hlo'.le (by exact_mod_cast hslo)
  have hshi' : Real.sqrt (t : ℝ) ≤ hi :=
    sqrt_le_of_sq_le (by exact_mod_cast hhi) (by exact_mod_cast hshi)
  have hz₁' : (z₁ : ℝ) = 1 / (hi : ℝ) := by exact_mod_cast hz₁
  have hz₂' : (z₂ : ℝ) = (3 / 40) / (lo : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using congrArg (Rat.cast : ℚ → ℝ) hz₂
  have hr₁' : (r₁ : ℝ) = 1 + (t : ℝ) := by exact_mod_cast hr₁
  have hr₂' : (r₂ : ℝ) = (t : ℝ) + (3 / 40) ^ 2 := by
    simpa only [Rat.cast_add, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using
      congrArg (Rat.cast : ℚ → ℝ) hr₂
  rw [hz₁'] at hA
  rw [hz₂'] at hB
  have hside : ((s : ℝ) = (lo : ℝ) ∧ 0 ≤ Real.pi + A - 6 * B) ∨
      ((s : ℝ) = (hi : ℝ) ∧ Real.pi + A - 6 * B ≤ 0) := by
    rcases side with ⟨rfl, hsign⟩ | ⟨rfl, hsign⟩
    · exact Or.inl ⟨rfl, hsign⟩
    · exact Or.inr ⟨rfl, hsign⟩
  have hprod := Vfield_product_lower ht' hlo' hslo' hshi' hA hB hside
  rw [hr₁'] at hL
  rw [hr₂'] at hU
  rw [Vfield_eq ht']
  linarith only [hL, hU, hprod]

end Zeta5Irrational
