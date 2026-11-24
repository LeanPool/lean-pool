/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityLowDim
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityFrame
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardKahlerTopPower

/-!
# The normalized density in complex dimension two

This is the determinant half of the complex-dimension-two exterior-density
identity.  For a real `(1,1)` two-form, the four entries of the normalized
matrix reduce to the three real coefficients on the standard complex frame.
Expanding the `2 × 2` determinant then yields the exact real quadratic
coefficient.  The Pfaffian pairing-sum expansion is then reduced to the same
finite real quadratic identity on the interleaved four-frame.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

/-- A real `(1,1)` two-form intertwines multiplication by `i` in its two
slots with a minus sign. -/
theorem coordinateTwoForm_I_smul_left_of_isOneOne {n : ℕ}
    {A : CoordinateRealTwoForm n} (hA : IsOneOne A) (u v : ComplexModel n) :
    A ![Complex.I • u, v] = -A ![u, Complex.I • v] :=
  coordinateFrame_twoForm_I_smul_left_of_isOneOne hA u v

/-- The real coefficient matrix of a `(1,1)` form on the standard complex
two-frame.  It records the six independent real values using the four
coordinates `e₀, Ie₀, e₁, Ie₁`. -/
def coordinateTwoFrameMatrix (A : CoordinateRealTwoForm 2) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  ![![0,
      A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (0 : Fin 2)],
      A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)],
      A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)]],
    ![-A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (0 : Fin 2)], 0,
      -A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)],
      A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)]],
    ![-A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)],
      A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)], 0,
      A ![coordinateVector (1 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)]],
    ![-A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)],
      -A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)],
      -A ![coordinateVector (1 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)], 0]]

private def swapFour01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1
private def swapFour12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2
private def swapFour23 : Equiv.Perm (Fin 4) := Equiv.swap 2 3

/-- A concrete listing of `S₄` by words in the three adjacent swaps.  It is
used only to turn the dimension-two Pfaffian sum into a finite ring identity. -/
private def permuteFour : Fin 24 → Equiv.Perm (Fin 4) :=
  ![1,
    swapFour01,
    swapFour12,
    swapFour23,
    swapFour01 * swapFour12,
    swapFour01 * swapFour23,
    swapFour12 * swapFour01,
    swapFour12 * swapFour23,
    swapFour23 * swapFour12,
    swapFour01 * swapFour12 * swapFour01,
    swapFour01 * swapFour12 * swapFour23,
    swapFour01 * swapFour23 * swapFour12,
    swapFour12 * swapFour01 * swapFour23,
    swapFour12 * swapFour23 * swapFour12,
    swapFour23 * swapFour12 * swapFour01,
    swapFour01 * swapFour12 * swapFour01 * swapFour23,
    swapFour01 * swapFour12 * swapFour23 * swapFour12,
    swapFour01 * swapFour23 * swapFour12 * swapFour01,
    swapFour12 * swapFour01 * swapFour23 * swapFour12,
    swapFour12 * swapFour23 * swapFour12 * swapFour01,
    swapFour01 * swapFour12 * swapFour01 * swapFour23 * swapFour12,
    swapFour01 * swapFour12 * swapFour23 * swapFour12 * swapFour01,
    swapFour12 * swapFour01 * swapFour23 * swapFour12 * swapFour01,
    swapFour01 * swapFour12 * swapFour01 * swapFour23 * swapFour12 * swapFour01]

private theorem permuteFour_injective : Function.Injective permuteFour := by
  decide

private theorem univ_perm_four_eq_image :
    (Finset.univ : Finset (Equiv.Perm (Fin 4))) =
      Finset.image permuteFour Finset.univ := by
  decide

/-- A real `(1,1)` two-form has the standard skew coefficient matrix on the
interleaved frame `e₀, Ie₀, e₁, Ie₁`.  This makes the remaining exterior
square calculation a finite identity in four real variables. -/
theorem coordinateTwoForm_apply_realFrame_two
    (A : CoordinateRealTwoForm 2) (hA : IsOneOne A) (i j : Fin 4) :
    A ![coordinateRealFrame i, coordinateRealFrame j] =
      coordinateTwoFrameMatrix A i j := by
  have hself (k : Fin 2) :
      A ![coordinateVector k, coordinateVector k] = 0 := by
    exact A.map_eq_zero_of_eq ![coordinateVector k, coordinateVector k]
      (i := 0) (j := 1) (by rfl) (by decide)
  have h10I :
      A ![coordinateVector (1 : Fin 2), Complex.I • coordinateVector (0 : Fin 2)] =
        A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)] := by
    rw [coordinateFrame_twoForm_swap A (Complex.I • coordinateVector (0 : Fin 2))
      (coordinateVector (1 : Fin 2)),
      coordinateTwoForm_I_smul_left_of_isOneOne hA]
    ring
  fin_cases i <;> fin_cases j
  · change A ![coordinateVector (0 : Fin 2), coordinateVector (0 : Fin 2)] = 0
    exact hself 0
  · change A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (0 : Fin 2)] = _
    rfl
  · change A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)] = _
    rfl
  · change A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)] = _
    rfl
  · change A ![Complex.I • coordinateVector (0 : Fin 2), coordinateVector (0 : Fin 2)] = _
    exact coordinateFrame_twoForm_swap A _ _
  · change A ![Complex.I • coordinateVector (0 : Fin 2),
      Complex.I • coordinateVector (0 : Fin 2)] = 0
    exact (hA (coordinateVector (0 : Fin 2))
      (coordinateVector (0 : Fin 2))).trans (hself 0)
  · change A ![Complex.I • coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)] = _
    exact coordinateTwoForm_I_smul_left_of_isOneOne hA _ _
  · change A ![Complex.I • coordinateVector (0 : Fin 2),
      Complex.I • coordinateVector (1 : Fin 2)] = _
    exact hA _ _
  · change A ![coordinateVector (1 : Fin 2), coordinateVector (0 : Fin 2)] = _
    exact coordinateFrame_twoForm_swap A _ _
  · change A ![coordinateVector (1 : Fin 2), Complex.I • coordinateVector (0 : Fin 2)] = _
    exact h10I
  · change A ![coordinateVector (1 : Fin 2), coordinateVector (1 : Fin 2)] = 0
    exact hself 1
  · change A ![coordinateVector (1 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)] = _
    rfl
  · change A ![Complex.I • coordinateVector (1 : Fin 2), coordinateVector (0 : Fin 2)] = _
    exact coordinateFrame_twoForm_swap A _ _
  · change A ![Complex.I • coordinateVector (1 : Fin 2),
      Complex.I • coordinateVector (0 : Fin 2)] = _
    calc
      A ![Complex.I • coordinateVector (1 : Fin 2),
          Complex.I • coordinateVector (0 : Fin 2)] =
          -A ![Complex.I • coordinateVector (0 : Fin 2),
            Complex.I • coordinateVector (1 : Fin 2)] :=
        coordinateFrame_twoForm_swap A _ _
      _ = -A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)] := by
        rw [hA]
  · change A ![Complex.I • coordinateVector (1 : Fin 2), coordinateVector (1 : Fin 2)] = _
    exact coordinateFrame_twoForm_swap A _ _
  · change A ![Complex.I • coordinateVector (1 : Fin 2),
      Complex.I • coordinateVector (1 : Fin 2)] = 0
    exact (hA (coordinateVector (1 : Fin 2))
      (coordinateVector (1 : Fin 2))).trans (hself 1)

/-- The normalized coefficient matrix of a real `(1,1)` form in complex
dimension two.  This is the concrete coefficient expansion needed before the
Pfaffian pairing-sum can be compared to the determinant. -/
theorem normalizedHermitianMatrix_two_entries
    (A : CoordinateRealTwoForm 2) (hA : IsOneOne A) :
    normalizedHermitianMatrix A 0 0 =
      (Real.pi : ℂ) * (A ![coordinateVector (0 : Fin 2),
        Complex.I • coordinateVector (0 : Fin 2)] : ℂ) ∧
    normalizedHermitianMatrix A 1 1 =
      (Real.pi : ℂ) * (A ![coordinateVector (1 : Fin 2),
        Complex.I • coordinateVector (1 : Fin 2)] : ℂ) ∧
    normalizedHermitianMatrix A 0 1 =
      (Real.pi : ℂ) * ((A ![coordinateVector (0 : Fin 2),
        Complex.I • coordinateVector (1 : Fin 2)] : ℂ) - Complex.I *
        (A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)] : ℂ)) ∧
    normalizedHermitianMatrix A 1 0 =
      (Real.pi : ℂ) * ((A ![coordinateVector (0 : Fin 2),
        Complex.I • coordinateVector (1 : Fin 2)] : ℂ) + Complex.I *
        (A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)] : ℂ)) := by
  have hself (j : Fin 2) :
      A ![coordinateVector j, coordinateVector j] = 0 := by
    exact A.map_eq_zero_of_eq ![coordinateVector j, coordinateVector j]
      (i := 0) (j := 1) (by rfl) (by decide)
  have h10I :
      A ![coordinateVector (1 : Fin 2), Complex.I • coordinateVector (0 : Fin 2)] =
        A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)] := by
    rw [coordinateFrame_twoForm_swap A (Complex.I • coordinateVector (0 : Fin 2))
      (coordinateVector (1 : Fin 2)),
      coordinateTwoForm_I_smul_left_of_isOneOne hA]
    ring
  have h10 : A ![coordinateVector (1 : Fin 2), coordinateVector (0 : Fin 2)] =
      -A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)] :=
    coordinateFrame_twoForm_swap A (coordinateVector (0 : Fin 2)) (coordinateVector (1 : Fin 2))
  constructor
  · rw [normalizedHermitianMatrix, hself]
    simp
  constructor
  · rw [normalizedHermitianMatrix, hself]
    simp
  constructor
  · rfl
  · rw [normalizedHermitianMatrix, h10I, h10]
    simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add]

/-- The determinant normalization of a real `(1,1)` two-form in complex
dimension two is the explicit real quadratic expression on its frame
coefficients. -/
theorem normalizedTopPowerDensity_two_eq
    (A : CoordinateRealTwoForm 2) (hA : IsOneOne A) :
    normalizedTopPowerDensity A =
      2 * (A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (0 : Fin 2)] *
          A ![coordinateVector (1 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)] -
        A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)] ^ 2 -
        A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)] ^ 2) := by
  obtain ⟨h00, h11, h01, h10⟩ := normalizedHermitianMatrix_two_entries A hA
  unfold normalizedTopPowerDensity
  rw [complexTopCoefficient_eq, Matrix.det_fin_two, h00, h11, h01, h10]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, mul_zero, zero_add, sub_zero]
  field_simp [Real.pi_ne_zero]
  ring

private theorem coordinatePairingSum_realFrame_two_eq
    (A : CoordinateRealTwoForm 2) (hA : IsOneOne A) :
    coordinatePairingSum A
        (finProdFinEquiv : Fin 2 × Fin 2 → Fin 4) coordinateRealFrame =
      8 * (A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (0 : Fin 2)] *
          A ![coordinateVector (1 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)] -
        A ![coordinateVector (0 : Fin 2), coordinateVector (1 : Fin 2)] ^ 2 -
        A ![coordinateVector (0 : Fin 2), Complex.I • coordinateVector (1 : Fin 2)] ^ 2) := by
  unfold coordinatePairingSum
  rw [univ_perm_four_eq_image, Finset.sum_image permuteFour_injective.injOn]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, permuteFour,
    swapFour01, swapFour12, swapFour23, Equiv.Perm.sign_mul,
    Equiv.swap_apply_def, coordinateTwoForm_apply_realFrame_two A hA,
    coordinateTwoFrameMatrix, finProdFinEquiv]
  ring

/-- In complex dimension two, the genuine exterior-square density of a real
`(1,1)` form agrees with the determinant normalization.  The proof reduces
the Pfaffian pairing sum to its finite four-frame coefficient expansion. -/
theorem actualTopPowerDensity_eq_normalizedTopPowerDensity_two
    (A : CoordinateRealTwoForm 2) (hA : IsOneOne A) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  rw [normalizedTopPowerDensity_two_eq A hA]
  unfold actualTopPowerDensity
  rw [coordinateWedgePower_apply_eq_pairingSum,
    coordinatePairingSum_realFrame_two_eq A hA]
  ring

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
