/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AnnealedSharpOrder
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FullBlockHarmonicMean

/-!
# High-contrast homogenization: Provider.Quenched.FullBlockSharpHarmonic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Harmonic means and the sharp involution

Conjugation by the doubled-block reflection turns the inverse of a sharp
matrix back into the original matrix.  Consequently, the harmonic mean of a
finite family of sharp matrices is exactly the sharp of the arithmetic mean
of the original family.  Combining this identity with order reversal gives
the lower comparison used in the quadratic fluctuation estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open scoped BigOperators MatrixOrder

noncomputable section

private theorem fullBlockArithmeticMean_posDef {N d : ℕ} [NeZero N]
    {A : Fin N → FullBlockMat d} (hA : ∀ i, (A i).PosDef) :
    (fullBlockArithmeticMean A).PosDef := by
  classical
  have hsum : (∑ i : Fin N, A i).PosDef :=
    Matrix.posDef_sum (s := Finset.univ) Finset.univ_nonempty
      (fun i _hi ↦ hA i)
  exact hsum.smul (inv_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))

private theorem fullBlockArithmeticMean_reflConj {N d : ℕ} [NeZero N]
    (A : Fin N → FullBlockMat d) :
    fullBlockArithmeticMean
        (fun i ↦ fullBlockRefl d * A i * fullBlockRefl d) =
      fullBlockRefl d * fullBlockArithmeticMean A * fullBlockRefl d := by
  classical
  simp only [fullBlockArithmeticMean]
  calc
    (N : ℝ)⁻¹ • ∑ i, fullBlockRefl d * A i * fullBlockRefl d =
        (N : ℝ)⁻¹ •
          (fullBlockRefl d * (∑ i, A i) * fullBlockRefl d) := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = fullBlockRefl d * ((N : ℝ)⁻¹ • ∑ i, A i) * fullBlockRefl d := by
          simp [Matrix.mul_assoc]

/-- The harmonic mean of a finite family of sharp matrices is the sharp of
the arithmetic mean of the original matrices. -/
theorem fullBlockHarmonicMean_fullBlockSharp {N d : ℕ} [NeZero N]
    (A : Fin N → FullBlockMat d) (hA : ∀ i, (A i).PosDef) :
    fullBlockHarmonicMean (fun i ↦ fullBlockSharp (A i)) =
      fullBlockSharp (fullBlockArithmeticMean A) := by
  have hsharp : ∀ i, (fullBlockSharp (A i)).PosDef :=
    fun i ↦ posDef_fullBlockSharp (hA i)
  have hinv : ∀ i, (fullBlockSharp (A i))⁻¹ =
      fullBlockRefl d * A i * fullBlockRefl d :=
    fun i ↦ fullBlockSharp_inv (hA i)
  rw [fullBlockHarmonicMean]
  simp_rw [hinv]
  change
    (fullBlockArithmeticMean
      (fun i ↦ fullBlockRefl d * A i * fullBlockRefl d))⁻¹ =
        fullBlockSharp (fullBlockArithmeticMean A)
  rw [fullBlockArithmeticMean_reflConj]
  exact refl_conj_inv (fullBlockArithmeticMean_posDef hA)

/-- If a positive definite parent lies below the arithmetic mean of its
children, then the harmonic mean of the children’s sharps lies below the
sharp of the parent. -/
theorem fullBlockHarmonicMean_fullBlockSharp_le {N d : ℕ} [NeZero N]
    {A : Fin N → FullBlockMat d} {P : FullBlockMat d}
    (hA : ∀ i, (A i).PosDef) (hP : P.PosDef)
    (hle : P ≤ fullBlockArithmeticMean A) :
    fullBlockHarmonicMean (fun i ↦ fullBlockSharp (A i)) ≤ fullBlockSharp P := by
  rw [fullBlockHarmonicMean_fullBlockSharp A hA]
  exact fullBlockSharp_le_fullBlockSharp hP (fullBlockArithmeticMean_posDef hA) hle

/-- The arithmetic mean of the children’s sharps, minus the parent sharp, is
bounded by the average quadratic fluctuation around any symmetric centre. -/
theorem fullBlockArithmeticMean_sharp_sub_parentSharp_le_averageQuadratic
    {N d : ℕ} [NeZero N] (A : Fin N → FullBlockMat d)
    (G P : FullBlockMat d) (hA : ∀ i, (A i).PosDef) (hG : G.IsSymm)
    (hP : P.PosDef) (hle : P ≤ fullBlockArithmeticMean A) :
    fullBlockArithmeticMean (fun i ↦ fullBlockSharp (A i)) -
        fullBlockSharp P ≤
      (N : ℝ)⁻¹ •
        ∑ i, (fullBlockSharp (A i) - G) *
          (fullBlockSharp (A i))⁻¹ * (fullBlockSharp (A i) - G) := by
  have hsharp : ∀ i, (fullBlockSharp (A i)).PosDef :=
    fun i ↦ posDef_fullBlockSharp (hA i)
  have hmean := fullBlockHarmonicMean_fullBlockSharp_le hA hP hle
  have hgap := fullBlockArithmeticMean_sub_harmonicMean_le_averageQuadratic
    (b := fun i ↦ fullBlockSharp (A i)) G hsharp hG
  rw [Matrix.le_iff] at hmean hgap ⊢
  convert hmean.add hgap using 1
  noncomm_ring

/-- Finset-indexed form of the sharp arithmetic-harmonic gap.  This avoids an
enumeration choice when the children are supplied by an aligned subdivision. -/
theorem fullBlockFinsetAverage_sharp_sub_parentSharp_le_averageQuadratic
    {ι : Type*} [DecidableEq ι] {d : ℕ} (Z : Finset ι) (hZ : Z.Nonempty)
    (A : ι → FullBlockMat d) (G P : FullBlockMat d)
    (hA : ∀ i ∈ Z, (A i).PosDef) (hG : G.IsSymm) (hP : P.PosDef)
    (hle : P ≤ (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, A i) :
    (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, fullBlockSharp (A i) - fullBlockSharp P ≤
      (Z.card : ℝ)⁻¹ •
        ∑ i ∈ Z, (fullBlockSharp (A i) - G) *
          (fullBlockSharp (A i))⁻¹ * (fullBlockSharp (A i) - G) := by
  classical
  let e : Fin Z.card ≃ ↥Z :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe Z)).symm
  let B : Fin Z.card → FullBlockMat d := fun i ↦ A (e i).1
  let : NeZero Z.card := ⟨Finset.card_ne_zero.mpr hZ⟩
  have hsum (f : ι → FullBlockMat d) :
      ∑ i : Fin Z.card, f (e i).1 = ∑ i ∈ Z, f i := by
    calc
      ∑ i : Fin Z.card, f (e i).1 = ∑ i : ↥Z, f i.1 :=
        e.sum_comp (fun i : ↥Z ↦ f i.1)
      _ = Z.attach.sum (fun i ↦ f i.1) := by
        rw [Finset.attach_eq_univ]
      _ = ∑ i ∈ Z, f i := Finset.sum_attach Z f
  have hB : ∀ i, (B i).PosDef := fun i ↦ hA (e i).1 (e i).2
  have hleB : P ≤ fullBlockArithmeticMean B := by
    simpa only [fullBlockArithmeticMean, B, hsum] using hle
  have hmain := fullBlockArithmeticMean_sharp_sub_parentSharp_le_averageQuadratic
    B G P hB hG hP hleB
  simp only [fullBlockArithmeticMean, B] at hmain
  rw [hsum (fun i ↦ fullBlockSharp (A i)),
    hsum (fun i ↦ (fullBlockSharp (A i) - G) *
      (fullBlockSharp (A i))⁻¹ * (fullBlockSharp (A i) - G))] at hmain
  exact hmain

end

end Quenched
end HighContrast
end HCPolySupport
