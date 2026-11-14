/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Separation/NoWrap.lean`, by
Jeroen Zuiddam, 2026: added the no-wrap lemma for an arbitrary period `L > 3(M-1)`
(`fourierPhase_dvd_iff_eq_zero_of_lt`).
-/
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Lean.Elab.Tactic.Omega

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The Fourier projection has no modular wrap

Section 4.1 of *Matrix Multiplication via Auxiliary Separation and Polynomial
Multiplication* uses exactly `5 * M` Fourier phases. The exponent
`u - v + 2 * (g - h)` has absolute value at most `3 * (M - 1)` when all four
labels lie in `{1, ..., M}`. Consequently, divisibility by `5 * M` is equivalent
to the exact integer support equation.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

/-- The explicit bound for the exponent in the finite Fourier projection. -/
theorem fourierPhase_abs_le {M h g u v : ℤ}
    (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    |u - v + 2 * (g - h)| ≤ 3 * (M - 1) := by
  rw [abs_le']
  constructor <;> omega

/-- The Fourier modulus exceeds the full possible range of the exponent. -/
theorem fourierRadius_lt_modulus {M : ℤ} (hM : 1 ≤ M) :
    3 * (M - 1) < 5 * M := by
  omega

/-- Every possible exponent lies strictly between minus and plus the modulus. -/
theorem fourierPhase_abs_lt {M h g u v : ℤ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    |u - v + 2 * (g - h)| < 5 * M :=
  lt_of_le_of_lt (fourierPhase_abs_le hh hg hu hv) (fourierRadius_lt_modulus hM)

/-- Modular Fourier support is exact integer support for the allowed labels. -/
theorem fourierPhase_eq_zero_of_dvd {M h g u v : ℤ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (hdiv : 5 * M ∣ u - v + 2 * (g - h)) :
    u - v + 2 * (g - h) = 0 :=
  Int.eq_zero_of_abs_lt_dvd hdiv (fourierPhase_abs_lt hM hh hg hu hv)

/-- Characterization of the surviving Fourier support without modular arithmetic. -/
theorem fourierPhase_dvd_iff_eq_zero {M h g u v : ℤ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    (5 * M ∣ u - v + 2 * (g - h)) ↔ u - v + 2 * (g - h) = 0 := by
  constructor
  · exact fourierPhase_eq_zero_of_dvd hM hh hg hu hv
  · intro hzero
    rw [hzero]
    exact ⟨0, by simp⟩

/-- Characterization of the surviving Fourier support for an arbitrary period
`L > 3 * (M - 1)` (all-fields version: the period need not be `5 * M`). -/
theorem fourierPhase_dvd_iff_eq_zero_of_lt {M L h g u v : ℤ}
    (hL : 3 * (M - 1) < L) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    (L ∣ u - v + 2 * (g - h)) ↔ u - v + 2 * (g - h) = 0 := by
  constructor
  · intro hdiv
    exact Int.eq_zero_of_abs_lt_dvd hdiv
      (lt_of_le_of_lt (fourierPhase_abs_le hh hg hu hv) hL)
  · intro hzero
    rw [hzero]
    exact ⟨0, by simp⟩

/-- The same exponent bound for natural-number labels, interpreted in `ℤ`. -/
theorem fourierPhase_abs_le_nat {M h g u v : ℕ}
    (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    |(u : ℤ) - v + 2 * ((g : ℤ) - h)| ≤ 3 * ((M : ℤ) - 1) := by
  apply fourierPhase_abs_le <;> omega

/-- Natural-number labels admit no additional solutions modulo `5 * M`. -/
theorem fourierPhase_dvd_iff_eq_zero_nat {M h g u v : ℕ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    ((5 : ℤ) * M ∣ (u : ℤ) - v + 2 * ((g : ℤ) - h)) ↔
      (u : ℤ) - v + 2 * ((g : ℤ) - h) = 0 := by
  apply fourierPhase_dvd_iff_eq_zero <;> omega

/-- Zero-based finite labels have the same exponent as the paper's labels plus one. -/
theorem fourierPhase_abs_le_fin {M : ℕ} (h g u v : Fin M) :
    |(u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val)| ≤
      3 * ((M : ℤ) - 1) := by
  have hh := h.isLt
  have hg := g.isLt
  have hu := u.isLt
  have hv := v.isLt
  rw [abs_le']
  constructor <;> omega

/-- The support test for a Fourier projection indexed by `Fin M`. -/
theorem fourierPhase_dvd_iff_eq_zero_fin {M : ℕ} (h g u v : Fin M) :
    ((5 : ℤ) * M ∣ (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val)) ↔
      (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val) = 0 := by
  constructor
  · intro hdiv
    apply Int.eq_zero_of_abs_lt_dvd hdiv
    apply lt_of_le_of_lt (fourierPhase_abs_le_fin h g u v)
    apply fourierRadius_lt_modulus
    have hh := h.isLt
    omega
  · intro hzero
    rw [hzero]
    exact ⟨0, by simp⟩

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
