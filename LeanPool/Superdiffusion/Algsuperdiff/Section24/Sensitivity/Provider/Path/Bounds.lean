/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Densities
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.EllipticBounds

/-!
# Bounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform pointwise bounds along the perturbation path

The minimizer-continuity step of `l.sensitivity.coarse.grained.general` needs
three uniform pointwise estimates, all measured against the *doubled energy
density* of the base coefficient rather than against an `L²` norm:

* an a.e. uniform entry bound for an `L∞` matrix field (restated here as a
  standalone lemma; the frozen `perturbCoeffOn` body carries the same argument
  inline, and that file is never edited);
* the two-sided comparison `c |X|² ≤ X · bfA(a) X ≤ C |X|²` supplied by the
  Chapter 2 block formalism; and
* the resulting domination of the linear and quadratic response densities by
  the energy density, with a free Young parameter.

Because every bound is expressed through the energy density itself, the
continuity argument downstream never has to leave the doubled functional.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## A standalone a.e. entry bound for `L∞` matrix fields -/

/-- The `L∞` entry bound of a bounded matrix field: the sum of the essential
suprema of all entries.  This is the same quantity that the frozen
`perturbCoeffOn` body builds inline; it is restated here so that the
perturbation estimates can be proved without touching the frozen file. -/
def lInfEntryBound {U : Domain d} (h : LInfMatrixFieldOn U) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (eLpNorm (fun x : Vec d => h.1 x i j) ∞
      (volumeMeasureOn (U : Set (Vec d)))).toReal

/-- Every entry of an `L∞` matrix field is a.e. bounded by its entry bound. -/
theorem ae_abs_apply_le_lInfEntryBound {U : Domain d} (h : LInfMatrixFieldOn U)
    (i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      |h.1 x i j| ≤ lInfEntryBound h := by
  set E : ℝ≥0∞ := eLpNorm (fun x : Vec d => h.1 x i j) ∞
    (volumeMeasureOn (U : Set (Vec d))) with hEdef
  have hE : E ≠ ∞ := (h.2 i j).eLpNorm_ne_top
  have hae : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), ‖h.1 x i j‖ₑ ≤ E := by
    simpa only [hEdef, eLpNorm_exponent_top (h.2 i j).aestronglyMeasurable] using!
      (ae_le_eLpNormEssSup (f := fun x : Vec d => h.1 x i j)
        (μ := volumeMeasureOn (U : Set (Vec d))))
  filter_upwards [hae] with x hx
  have hx' : |h.1 x i j| ≤ E.toReal := by
    have hxE : (↑‖h.1 x i j‖₊ : ℝ≥0∞) ≤ E := by
      simpa only [enorm_eq_nnnorm] using hx
    have htoReal := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hE).2 hxE
    simpa only [ENNReal.coe_toReal, Real.norm_eq_abs] using! htoReal
  refine hx'.trans ?_
  calc
    E.toReal ≤ ∑ j : Fin d,
        (eLpNorm (fun x : Vec d => h.1 x i j) ∞
          (volumeMeasureOn (U : Set (Vec d)))).toReal := by
          rw [hEdef]
          exact Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin d => (eLpNorm (fun x : Vec d => h.1 x i j) ∞
              (volumeMeasureOn (U : Set (Vec d)))).toReal)
            (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
    _ ≤ lInfEntryBound h :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun i : Fin d => ∑ j : Fin d,
            (eLpNorm (fun x : Vec d => h.1 x i j) ∞
              (volumeMeasureOn (U : Set (Vec d)))).toReal)
          (fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
          (Finset.mem_univ i)

/-- The a.e. uniform entry bound in the packaged form used downstream. -/
theorem ae_forall_abs_apply_le_lInfEntryBound {U : Domain d}
    (h : LInfMatrixFieldOn U) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      ∀ i j : Fin d, |h.1 x i j| ≤ lInfEntryBound h :=
  ae_all_iff.2 fun i => ae_all_iff.2 fun j => ae_abs_apply_le_lInfEntryBound h i j

/-! ## The Frobenius operator bound -/

/-- The Frobenius bound for the image of a matrix. -/
theorem vecNormSq_matVecMul_le_frobenius (A : Mat d) (η : Vec d) :
    vecNormSq (matVecMul A η) ≤
      (∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2) * vecNormSq η := by
  have hrow : ∀ i : Fin d,
      (matVecMul A η i) ^ 2 ≤ (∑ j : Fin d, (A i j) ^ 2) * vecNormSq η := by
    intro i
    have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq (fun j => A i j) η
    have hrowNorm : vecNormSq (fun j => A i j) = ∑ j : Fin d, (A i j) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    simpa [matVecMul, vecDot, hrowNorm] using hcs
  calc
    vecNormSq (matVecMul A η) = ∑ i : Fin d, (matVecMul A η i) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i : Fin d, (∑ j : Fin d, (A i j) ^ 2) * vecNormSq η :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2) * vecNormSq η := by
      rw [Finset.sum_mul]

/-- An entrywise bound gives a uniform bound on the image of a matrix. -/
theorem vecNormSq_matVecMul_le_of_abs_apply_le {A : Mat d} {b : ℝ}
    (hb : ∀ i j : Fin d, |A i j| ≤ b) (w : Vec d) :
    vecNormSq (matVecMul A w) ≤ ((d : ℝ) * (d : ℝ) * b ^ 2) * vecNormSq w := by
  refine (vecNormSq_matVecMul_le_frobenius A w).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg w)
  calc
    (∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2)
        ≤ ∑ _i : Fin d, ∑ _j : Fin d, b ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            nlinarith [abs_nonneg (A i j), sq_abs (A i j), hb i j]
    _ = (d : ℝ) * (d : ℝ) * b ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-! ## Comparison of the doubled quadratic form with the Euclidean norm -/

/-- Block self-pairing is the sum of the two component norms. -/
theorem blockVecDot_self_eq (Z : BlockVec d) :
    blockVecDot Z Z = vecNormSq Z.1 + vecNormSq Z.2 := rfl

theorem vecNormSq_fst_le_blockVecDot_self (Z : BlockVec d) :
    vecNormSq Z.1 ≤ blockVecDot Z Z := by
  rw [blockVecDot_self_eq]
  linarith [vecNormSq_nonneg Z.2]

theorem vecNormSq_snd_le_blockVecDot_self (Z : BlockVec d) :
    vecNormSq Z.2 ≤ blockVecDot Z Z := by
  rw [blockVecDot_self_eq]
  linarith [vecNormSq_nonneg Z.1]

theorem blockVecDot_self_nonneg (Z : BlockVec d) : 0 ≤ blockVecDot Z Z := by
  rw [blockVecDot_self_eq]
  linarith [vecNormSq_nonneg Z.1, vecNormSq_nonneg Z.2]

/-- The reciprocal coercivity constant of the doubled matrix. -/
def blockCoercivityConst (lam Lam : ℝ) : ℝ := (1 + 2 * Lam ^ 2) / lam

theorem blockCoercivityConst_pos {lam Lam : ℝ} (hlam : 0 < lam) :
    0 < blockCoercivityConst lam Lam := by
  unfold blockCoercivityConst
  positivity

/-- The Euclidean square norm of a block vector is controlled by its doubled
quadratic form. -/
theorem blockVecDot_self_le_blockQuadForm {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (Z : BlockVec d) :
    blockVecDot Z Z ≤
      blockCoercivityConst lam Lam *
        blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z) := by
  have hlam : 0 < lam := hA.1
  have hco := blockMatrixOfCoeff_coercive_of_isEllipticMatrix hA Z
  have hpos : 0 < 1 + 2 * Lam ^ 2 := by positivity
  have hmul :
      blockCoercivityConst lam Lam * ((lam / (1 + 2 * Lam ^ 2)) * blockVecDot Z Z) ≤
        blockCoercivityConst lam Lam *
          blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z) :=
    mul_le_mul_of_nonneg_left hco (blockCoercivityConst_pos (Lam := Lam) hlam).le
  have hid :
      blockCoercivityConst lam Lam * ((lam / (1 + 2 * Lam ^ 2)) * blockVecDot Z Z)
        = blockVecDot Z Z := by
    unfold blockCoercivityConst
    field_simp
  linarith [hid ▸ hmul]

/-- The doubled quadratic form is nonnegative under ellipticity. -/
theorem blockQuadForm_nonneg {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (Z : BlockVec d) :
    0 ≤ blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z) := by
  have hlam : 0 < lam := hA.1
  have hco := blockMatrixOfCoeff_coercive_of_isEllipticMatrix hA Z
  have hpos : 0 < lam / (1 + 2 * Lam ^ 2) := by positivity
  have := mul_nonneg hpos.le (blockVecDot_self_nonneg Z)
  linarith

/-- The block image of a block vector is controlled by its doubled quadratic
form. -/
theorem blockVecDot_image_self_le_blockQuadForm {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (Z : BlockVec d) :
    blockVecDot (blockMatVecMul (blockMatrixOfCoeff A) Z)
        (blockMatVecMul (blockMatrixOfCoeff A) Z) ≤
      (blockMatrixOfCoeffNormSqBound lam Lam * blockCoercivityConst lam Lam) *
        blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z) := by
  have himg := blockMatrixOfCoeff_image_bound_of_isEllipticMatrix hA Z
  have hcoer := blockVecDot_self_le_blockQuadForm hA Z
  have hlam : 0 < lam := hA.1
  have hbound_nonneg : 0 ≤ blockMatrixOfCoeffNormSqBound lam Lam := by
    unfold blockMatrixOfCoeffNormSqBound
    positivity
  calc
    blockVecDot (blockMatVecMul (blockMatrixOfCoeff A) Z)
        (blockMatVecMul (blockMatrixOfCoeff A) Z)
        ≤ blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot Z Z := himg
    _ ≤ blockMatrixOfCoeffNormSqBound lam Lam *
          (blockCoercivityConst lam Lam *
            blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z)) :=
          mul_le_mul_of_nonneg_left hcoer hbound_nonneg
    _ = (blockMatrixOfCoeffNormSqBound lam Lam * blockCoercivityConst lam Lam) *
          blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z) := by ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path
