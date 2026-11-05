/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!+# The square weights in auxiliary separation

Sections 4.1–4.3 use the phase `u - v + 2 * (g - h)` to select monomials.
On a selected monomial, the three integer variable weights add to `(g - h)^2`.
Thus the surviving monomials have nonnegative total degree, although individual
variable weights may be negative. Their degree is zero precisely when the guess
`g` matches the sector `h` and the auxiliary labels agree.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

/-- The exponent occurring in the finite Fourier projection. -/
def phase (g h u v : ℤ) : ℤ := u - v + 2 * (g - h)

/-- Weight on the first tensor leg, which carries the guessed sector label. -/
def firstWeight (g : ℤ) : ℤ := g ^ 2

/-- Weight on the second tensor leg. -/
def secondWeight (h u : ℤ) : ℤ := h * u - h ^ 2

/-- Weight on the third tensor leg. -/
def thirdWeight (h v : ℤ) : ℤ := -(h * v)

/-- Total weight of a target monomial after the three independent substitutions. -/
def totalWeight (g h u v : ℤ) : ℤ :=
  firstWeight g + secondWeight h u + thirdWeight h v

theorem totalWeight_eq_square_add_phase (g h u v : ℤ) :
    totalWeight g h u v = (g - h) ^ 2 + h * phase g h u v := by
  unfold totalWeight firstWeight secondWeight thirdWeight phase
  ring

/-- The projection equation converts the total weight into a square. -/
theorem totalWeight_eq_sq_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalWeight g h u v = (g - h) ^ 2 := by
  rw [totalWeight_eq_square_add_phase, hphase, mul_zero, add_zero]

theorem totalWeight_nonneg_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) : 0 ≤ totalWeight g h u v := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase]
  exact sq_nonneg (g - h)

/-- On the Fourier support, precisely the correctly matched terms have weight zero. -/
theorem totalWeight_eq_zero_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalWeight g h u v = 0 ↔ g = h ∧ u = v := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase, sq_eq_zero_iff]
  constructor
  · intro hzero
    have hgh : g = h := sub_eq_zero.mp hzero
    refine ⟨hgh, ?_⟩
    unfold phase at hphase
    omega
  · rintro ⟨hgh, _⟩
    exact sub_eq_zero.mpr hgh

theorem phase_and_totalWeight_eq_zero_iff (g h u v : ℤ) :
    (phase g h u v = 0 ∧ totalWeight g h u v = 0) ↔ g = h ∧ u = v := by
  constructor
  · rintro ⟨hphase, hweight⟩
    exact (totalWeight_eq_zero_iff_of_phase_eq_zero hphase).mp hweight
  · rintro ⟨rfl, rfl⟩
    simp [phase, totalWeight, firstWeight, secondWeight, thirdWeight]

theorem totalWeight_pos_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    0 < totalWeight g h u v ↔ g ≠ h := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase, sq_pos_iff, sub_ne_zero]

/-- The degree bound in Section 4.3, for sector labels in `1, …, M`. -/
theorem totalWeight_le_of_labels {M g h u v : ℤ}
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hphase : phase g h u v = 0) :
    totalWeight g h u v ≤ (M - 1) ^ 2 := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase]
  have hprod : 0 ≤ ((M - 1) - (g - h)) * ((M - 1) + (g - h)) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- The polynomial degree attached to a surviving monomial. -/
def totalDegree (g h u v : ℤ) : ℕ := (totalWeight g h u v).toNat

theorem totalDegree_cast_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    (totalDegree g h u v : ℤ) = totalWeight g h u v := by
  exact Int.toNat_of_nonneg (totalWeight_nonneg_of_phase_eq_zero hphase)

theorem totalDegree_eq_zero_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalDegree g h u v = 0 ↔ g = h ∧ u = v := by
  have hcast := totalDegree_cast_of_phase_eq_zero hphase
  have hzero : totalDegree g h u v = 0 ↔ totalWeight g h u v = 0 := by omega
  exact hzero.trans (totalWeight_eq_zero_iff_of_phase_eq_zero hphase)

theorem totalDegree_le_of_labels {M : ℕ} {g h u v : ℤ}
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hphase : phase g h u v = 0) :
    totalDegree g h u v ≤ (M - 1) ^ 2 := by
  have hM : 1 ≤ M := by omega
  have hbound := totalWeight_le_of_labels hg hh hphase
  have hcast := totalDegree_cast_of_phase_eq_zero hphase
  have hsub : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
  exact_mod_cast (show (totalDegree g h u v : ℤ) ≤ ((M - 1 : ℕ) : ℤ) ^ 2 by
    rw [hcast, hsub]
    exact hbound)

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
