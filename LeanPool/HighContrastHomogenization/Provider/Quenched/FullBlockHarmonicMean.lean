/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Support.Ambient.MatrixOrderBridge
public import Mathlib.Tactic.NoncommRing

/-!
# High-contrast homogenization: Provider.Quenched.FullBlockHarmonicMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Arithmetic and harmonic means of doubled block matrices

This module records the finite matrix identity that compares the arithmetic
and harmonic means of positive definite doubled block matrices.  The
comparison keeps an arbitrary deterministic centre, as required by the
quadratic fluctuation estimate in the small-contrast argument.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open scoped BigOperators MatrixOrder

noncomputable section

/-- The arithmetic mean of a nonempty finite family of doubled block
matrices. -/
@[expose]
def fullBlockArithmeticMean {N d : ℕ}
    (b : Fin N → FullBlockMat d) : FullBlockMat d :=
  (N : ℝ)⁻¹ • ∑ i, b i

/-- The harmonic mean of a nonempty finite family of doubled block
matrices. -/
@[expose]
def fullBlockHarmonicMean {N d : ℕ}
    (b : Fin N → FullBlockMat d) : FullBlockMat d :=
  ((N : ℝ)⁻¹ • ∑ i, (b i)⁻¹)⁻¹

private theorem natCast_pos_of_neZero (N : ℕ) [NeZero N] : 0 < (N : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

private theorem fullBlockAverage_inv_posDef {N d : ℕ} [NeZero N]
    {b : Fin N → FullBlockMat d} (hb : ∀ i, (b i).PosDef) :
    ((N : ℝ)⁻¹ • ∑ i, (b i)⁻¹).PosDef := by
  classical
  have hsum : (∑ i : Fin N, (b i)⁻¹).PosDef :=
    Matrix.posDef_sum (s := Finset.univ) Finset.univ_nonempty
      (fun i _hi ↦ (hb i).inv)
  exact hsum.smul (inv_pos.mpr (natCast_pos_of_neZero N))

/-- The harmonic mean of positive definite doubled block matrices is
positive definite. -/
theorem fullBlockHarmonicMean_posDef {N d : ℕ} [NeZero N]
    {b : Fin N → FullBlockMat d} (hb : ∀ i, (b i).PosDef) :
    (fullBlockHarmonicMean b).PosDef := by
  simp [fullBlockHarmonicMean, (fullBlockAverage_inv_posDef (b := b) hb).inv]

private theorem fullBlockHarmonicMean_inv_eq_average_inv {N d : ℕ}
    [NeZero N] {b : Fin N → FullBlockMat d} (hb : ∀ i, (b i).PosDef) :
    (fullBlockHarmonicMean b)⁻¹ = (N : ℝ)⁻¹ • ∑ i, (b i)⁻¹ := by
  let S : FullBlockMat d := (N : ℝ)⁻¹ • ∑ i, (b i)⁻¹
  have hS : S.PosDef := by
    simpa [S] using fullBlockAverage_inv_posDef (b := b) hb
  let _ := hS.isUnit.invertible
  change S⁻¹⁻¹ = S
  exact Matrix.inv_inv_of_invertible S

private theorem inv_natCast_smul_sum_const {N d : ℕ} [NeZero N]
    (G : FullBlockMat d) :
    (N : ℝ)⁻¹ • (∑ _i : Fin N, G) = G := by
  rw [Finset.sum_const, Finset.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (natCast_pos_of_neZero N)), one_smul]

private theorem inv_natCast_smul_sum_mul_left_right {N d : ℕ} [NeZero N]
    (G : FullBlockMat d) (A : Fin N → FullBlockMat d) :
    (N : ℝ)⁻¹ • (∑ i, G * A i * G) =
      G * ((N : ℝ)⁻¹ • ∑ i, A i) * G := by
  calc
    (N : ℝ)⁻¹ • (∑ i, G * A i * G) =
        ∑ i, (N : ℝ)⁻¹ • (G * A i * G) := by
          rw [Finset.smul_sum]
    _ = ∑ i, G * ((N : ℝ)⁻¹ • A i) * G := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [Matrix.mul_assoc]
    _ = G * (∑ i, (N : ℝ)⁻¹ • A i) * G := by
          simp [Matrix.mul_sum, Matrix.sum_mul]
    _ = G * ((N : ℝ)⁻¹ • ∑ i, A i) * G := by
          rw [Finset.smul_sum]

private theorem fullBlockQuadraticTerm_expand {d : ℕ}
    {B G : FullBlockMat d} (hB : B.PosDef) :
    (B - G) * B⁻¹ * (B - G) = B - G - G + G * B⁻¹ * G := by
  have hdet : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det (A := B)).mp hB.isUnit
  have hright : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  have hleft : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  noncomm_ring [hright, hleft]

private theorem fullBlockHarmonicQuadraticTerm_expand {d : ℕ}
    {H G S : FullBlockMat d} (hH : H.PosDef) (hHinv : H⁻¹ = S) :
    (H - G) * H⁻¹ * (H - G) = H - G - G + G * S * G := by
  have hdet : IsUnit H.det :=
    (Matrix.isUnit_iff_isUnit_det (A := H)).mp hH.isUnit
  have hright : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hleft : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hexpand :
      (H - G) * H⁻¹ * (H - G) = H - G - G + G * H⁻¹ * G := by
    noncomm_ring [hright, hleft]
  rw [hexpand, hHinv]

private theorem fullBlockAverageQuadraticTerms_expand {N d : ℕ}
    [NeZero N] {b : Fin N → FullBlockMat d} (G : FullBlockMat d)
    (hb : ∀ i, (b i).PosDef) :
    (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) =
      fullBlockArithmeticMean b - G - G +
        G * ((N : ℝ)⁻¹ • ∑ i, (b i)⁻¹) * G := by
  calc
    (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) =
        (N : ℝ)⁻¹ •
          (∑ i, (b i - G - G + G * (b i)⁻¹ * G)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact fullBlockQuadraticTerm_expand (G := G) (hb i)
    _ = (N : ℝ)⁻¹ •
          ((∑ i, b i) - (∑ _i : Fin N, G) - (∑ _i : Fin N, G) +
            ∑ i, G * (b i)⁻¹ * G) := by
          congr 1
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (N : ℝ)⁻¹ • (∑ i, b i) -
          (N : ℝ)⁻¹ • (∑ _i : Fin N, G) -
          (N : ℝ)⁻¹ • (∑ _i : Fin N, G) +
          (N : ℝ)⁻¹ • (∑ i, G * (b i)⁻¹ * G) := by
          simp [sub_eq_add_neg, smul_add]
    _ = fullBlockArithmeticMean b - G - G +
          G * ((N : ℝ)⁻¹ • ∑ i, (b i)⁻¹) * G := by
          rw [fullBlockArithmeticMean]
          rw [inv_natCast_smul_sum_const G]
          rw [inv_natCast_smul_sum_mul_left_right]

/-- Exact arithmetic-harmonic mean identity with an arbitrary symmetric
comparison matrix. -/
theorem fullBlockArithmeticMean_eq_harmonicMean_add_averageQuadratic_sub
    {N d : ℕ} [NeZero N] (b : Fin N → FullBlockMat d)
    (G : FullBlockMat d) (hb : ∀ i, (b i).PosDef) :
    fullBlockArithmeticMean b =
      fullBlockHarmonicMean b +
        (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) -
          (fullBlockHarmonicMean b - G) * (fullBlockHarmonicMean b)⁻¹ *
            (fullBlockHarmonicMean b - G) := by
  let H : FullBlockMat d := fullBlockHarmonicMean b
  let S : FullBlockMat d := (N : ℝ)⁻¹ • ∑ i, (b i)⁻¹
  have hH : H.PosDef := by
    simpa [H] using fullBlockHarmonicMean_posDef (b := b) hb
  have hHinv : H⁻¹ = S := by
    simpa [H, S] using fullBlockHarmonicMean_inv_eq_average_inv (b := b) hb
  have hAvg := fullBlockAverageQuadraticTerms_expand (b := b) G hb
  have hHquad :=
    fullBlockHarmonicQuadraticTerm_expand (H := H) (G := G) (S := S) hH hHinv
  calc
    fullBlockArithmeticMean b =
        H + (fullBlockArithmeticMean b - G - G + G * S * G) -
          (H - G - G + G * S * G) := by
          noncomm_ring
    _ = H +
        (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) -
          (H - G) * H⁻¹ * (H - G) := by
          rw [← hAvg, ← hHquad]
    _ = fullBlockHarmonicMean b +
        (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) -
          (fullBlockHarmonicMean b - G) * (fullBlockHarmonicMean b)⁻¹ *
            (fullBlockHarmonicMean b - G) := by
          rfl

private theorem fullBlockHarmonicMean_quadratic_posSemidef {N d : ℕ}
    [NeZero N] {b : Fin N → FullBlockMat d} {G : FullBlockMat d}
    (hb : ∀ i, (b i).PosDef) (hG : G.IsSymm) :
    ((fullBlockHarmonicMean b - G) * (fullBlockHarmonicMean b)⁻¹ *
      (fullBlockHarmonicMean b - G)).PosSemidef := by
  let H : FullBlockMat d := fullBlockHarmonicMean b
  have hH : H.PosDef := by
    simpa [H] using fullBlockHarmonicMean_posDef (b := b) hb
  have hHsymm : H.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm, H] using hH.isHermitian
  have hKherm : (H - G).IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hHsymm.sub hG
  have hPSD :
      (Matrix.conjTranspose (H - G) * H⁻¹ * (H - G)).PosSemidef :=
    hH.inv.posSemidef.conjTranspose_mul_mul_same (H - G)
  change ((H - G) * H⁻¹ * (H - G)).PosSemidef
  have hterm : Matrix.conjTranspose (H - G) * H⁻¹ * (H - G) =
      (H - G) * H⁻¹ * (H - G) := by
    rw [hKherm.eq]
  exact hterm ▸ hPSD

/-- The arithmetic-harmonic gap is bounded by the average quadratic
fluctuation. -/
theorem fullBlockArithmeticMean_sub_harmonicMean_le_averageQuadratic
    {N d : ℕ} [NeZero N] (b : Fin N → FullBlockMat d)
    (G : FullBlockMat d) (hb : ∀ i, (b i).PosDef) (hG : G.IsSymm) :
    fullBlockArithmeticMean b - fullBlockHarmonicMean b ≤
      (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) := by
  rw [Matrix.le_iff]
  have hId := fullBlockArithmeticMean_eq_harmonicMean_add_averageQuadratic_sub
    (b := b) G hb
  have hPSD := fullBlockHarmonicMean_quadratic_posSemidef
    (b := b) (G := G) hb hG
  have hEq : (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) -
      (fullBlockArithmeticMean b - fullBlockHarmonicMean b) =
      (fullBlockHarmonicMean b - G) * (fullBlockHarmonicMean b)⁻¹ *
        (fullBlockHarmonicMean b - G) := by
    rw [hId]
    noncomm_ring
  rw [hEq]
  exact hPSD

end

end Quenched
end HighContrast
end HCPolySupport
