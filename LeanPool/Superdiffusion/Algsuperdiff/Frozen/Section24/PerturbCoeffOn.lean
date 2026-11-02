/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# PerturbCoeffOn

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

-- FROZEN-STATEMENT-BEGIN
/-- Perturb a coefficient by an essentially bounded skew field while retaining ellipticity. -/
noncomputable def Algsuperdiff.Frozen.Section24.perturbCoeffOn
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (h : Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn U)
    (t : ℝ) : CoeffOn U := by
  classical
  let lInfEntryBound : ℝ :=
    ∑ i : Fin d, ∑ j : Fin d,
      (eLpNorm (fun x : Vec d => h.1.1 x i j) ∞
        (volumeMeasureOn (U : Set (Vec d)))).toReal
  have ae_abs_apply_le_lInfEntryBound (i j : Fin d) :
      ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), |h.1.1 x i j| ≤ lInfEntryBound := by
    let E : ℝ≥0∞ := eLpNorm (fun x : Vec d => h.1.1 x i j) ∞
      (volumeMeasureOn (U : Set (Vec d)))
    have hE : E ≠ ∞ := by
      rw [show E = eLpNorm (fun x : Vec d => h.1.1 x i j) ∞
        (volumeMeasureOn (U : Set (Vec d))) from rfl]
      exact (h.1.2 i j).eLpNorm_ne_top
    have hae : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), ‖h.1.1 x i j‖ₑ ≤ E := by
      simpa only [E, eLpNorm_exponent_top (h.1.2 i j).aestronglyMeasurable] using!
        (ae_le_eLpNormEssSup (f := fun x : Vec d => h.1.1 x i j)
          (μ := volumeMeasureOn (U : Set (Vec d))))
    filter_upwards [hae] with x hx
    have hx' : |h.1.1 x i j| ≤ E.toReal := by
      have hxE : (↑‖h.1.1 x i j‖₊ : ℝ≥0∞) ≤ E := by
        simpa only [enorm_eq_nnnorm] using hx
      have htoReal := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hE).2 hxE
      simpa only [ENNReal.coe_toReal, Real.norm_eq_abs] using! htoReal
    exact hx'.trans (by
      dsimp [lInfEntryBound]
      calc
        E.toReal ≤ ∑ j : Fin d,
            (eLpNorm (fun x : Vec d => h.1.1 x i j) ∞
              (volumeMeasureOn (U : Set (Vec d)))).toReal := by
                change (eLpNorm (fun x : Vec d => h.1.1 x i j) ∞
                  (volumeMeasureOn (U : Set (Vec d)))).toReal ≤ _
                exact Finset.single_le_sum (s := Finset.univ)
                  (f := fun j : Fin d => (eLpNorm (fun x : Vec d => h.1.1 x i j) ∞
                    (volumeMeasureOn (U : Set (Vec d)))).toReal)
                  (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
        _ ≤ ∑ i : Fin d, ∑ j : Fin d,
            (eLpNorm (fun x : Vec d => h.1.1 x i j) ∞
              (volumeMeasureOn (U : Set (Vec d)))).toReal :=
                Finset.single_le_sum (s := Finset.univ)
                  (f := fun i : Fin d => ∑ j : Fin d,
                    (eLpNorm (fun x : Vec d => h.1.1 x i j) ∞
                      (volumeMeasureOn (U : Set (Vec d)))).toReal)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
                  (Finset.mem_univ i))
  have vecNormSq_matVecMul_le_frobenius (A : Mat d) (η : Vec d) :
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
  have isEllipticMatrix_of_coercive_of_bound {A : Mat d} {lam B : ℝ}
      (hlam : 0 < lam) (hlamB : lam ^ 2 ≤ B)
      (hco : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ))
      (hbd : ∀ η : Vec d, vecNormSq (matVecMul A η) ≤ B * vecNormSq η) :
      IsEllipticMatrix lam (B / lam) A := by
    have hB : 0 < B := lt_of_lt_of_le (sq_pos_of_pos hlam) hlamB
    have hinj : Function.Injective A.mulVec := by
      intro ξ η hξη
      have hzero : A.mulVec (ξ - η) = 0 := by
        rw [sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg, ← sub_eq_add_neg,
          sub_eq_zero]
        exact hξη
      have hnorm : vecNormSq (ξ - η) = 0 := by
        have hle := hco (ξ - η)
        change lam * vecNormSq (ξ - η) ≤ vecDot (ξ - η) (A.mulVec (ξ - η)) at hle
        rw [hzero, vecDot_zero_right] at hle
        nlinarith [vecNormSq_nonneg (ξ - η)]
      exact sub_eq_zero.mp (vecNormSq_eq_zero hnorm)
    have hdet : IsUnit A.det :=
      (A.isUnit_iff_isUnit_det).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
    have hlamUpper : lam ≤ B / lam := (le_div_iff₀ hlam).mpr (by
      simpa only [pow_two] using hlamB)
    refine ⟨hlam, hlamUpper, hco, ?_⟩
    intro ξ
    set η : Vec d := matVecMul A⁻¹ ξ with hη
    have hAη : matVecMul A η = ξ := by
      rw [hη, matVecMul_mul, Matrix.mul_nonsing_inv A hdet]
      exact Matrix.one_mulVec ξ
    have hξ : vecNormSq ξ ≤ B * vecNormSq η := by simpa [hAη] using hbd η
    rw [show (B / lam)⁻¹ = lam / B by rw [inv_div]]
    calc
      lam / B * vecNormSq ξ ≤ lam / B * (B * vecNormSq η) :=
        mul_le_mul_of_nonneg_left hξ (div_nonneg hlam.le hB.le)
      _ = lam * vecNormSq η := by field_simp
      _ ≤ vecDot η (matVecMul A η) := hco η
      _ = vecDot ξ η := by rw [hAη, vecDot_comm]
      _ = vecDot ξ (matVecMul A⁻¹ ξ) := by rw [hη]
  exact {
    toCoeffField := fun x => a.toCoeffField x + t • h.1.1 x
    lam := a.lam
    Lam := (a.lam ^ 2 +
      (d : ℝ) * (d : ℝ) * (a.Lam + |t| * lInfEntryBound) ^ 2) / a.lam
    lam_pos := a.lam_pos
    lam_le_Lam := by
      apply (le_div_iff₀ a.lam_pos).mpr
      nlinarith [sq_nonneg a.lam,
        mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (Nat.cast_nonneg (α := ℝ) d))
          (sq_nonneg (a.Lam + |t| * lInfEntryBound))]
    aeStronglyMeasurable := by
      intro i j
      have hh := (h.1.2 i j).aestronglyMeasurable
      have hsum := (a.aeStronglyMeasurable i j).add (hh.const_mul t)
      have hrep :
          (fun x : Vec d => restrictCoeffField (U : Set (Vec d))
            (fun y => a.toCoeffField y + t • h.1.1 y) x i j)
            =ᵐ[volumeMeasureOn (U : Set (Vec d))]
          fun x => restrictCoeffField (U : Set (Vec d)) a.toCoeffField x i j +
            t * h.1.1 x i j := by
        filter_upwards [ae_restrict_mem U.measurableSet] with x hx
        simp [restrictCoeffField, hx]
      exact hsum.congr hrep.symm
    aeElliptic := by
      have hentry : ∀ i j : Fin d, ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
          |h.1.1 x i j| ≤ lInfEntryBound := fun i j => ae_abs_apply_le_lInfEntryBound i j
      filter_upwards [a.aeElliptic, h.2,
        ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry i j] with x hax hs hxentry
      apply isEllipticMatrix_of_coercive_of_bound a.lam_pos
      · nlinarith [sq_nonneg a.lam,
          mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (Nat.cast_nonneg (α := ℝ) d))
            (sq_nonneg (a.Lam + |t| * lInfEntryBound))]
      · intro ξ
        have hskew : vecDot ξ (matVecMul (h.1.1 x) ξ) = 0 := by
          rw [← vecDot_matVecMul_symmPart, hs]
          rw [show matVecMul (0 : Mat d) ξ = 0 by
            funext i
            change (∑ j : Fin d, (0 : ℝ) * ξ j) = 0
            simp]
          exact vecDot_zero_right ξ
        calc
          a.lam * vecNormSq ξ ≤ vecDot ξ (matVecMul (a.toCoeffField x) ξ) := hax.2.2.1 ξ
          _ = vecDot ξ (matVecMul (a.toCoeffField x + t • h.1.1 x) ξ) := by
            rw [add_matVecMul, smul_matVecMul, vecDot_add_right, vecDot_smul_right, hskew,
              mul_zero, add_zero]
      · intro η
        have hentrySum : ∀ i j : Fin d,
            |(a.toCoeffField x + t • h.1.1 x) i j| ≤ a.Lam + |t| * lInfEntryBound := by
          intro i j
          calc
            |(a.toCoeffField x + t • h.1.1 x) i j|
                ≤ |a.toCoeffField x i j| + |t * h.1.1 x i j| := by
                  simpa using abs_add_le (a.toCoeffField x i j) (t * h.1.1 x i j)
            _ = |a.toCoeffField x i j| + |t| * |h.1.1 x i j| := by rw [abs_mul]
            _ ≤ a.Lam + |t| * lInfEntryBound := by
              gcongr
              · exact abs_apply_le_of_isEllipticMatrix hax i j
              · exact hxentry i j
        calc
          vecNormSq (matVecMul (a.toCoeffField x + t • h.1.1 x) η)
              ≤ ((d : ℝ) * (d : ℝ) * (a.Lam + |t| * lInfEntryBound) ^ 2) *
                vecNormSq η := by
                  refine (vecNormSq_matVecMul_le_frobenius _ η).trans ?_
                  refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg η)
                  calc
                    (∑ i : Fin d, ∑ j : Fin d,
                      ((a.toCoeffField x + t • h.1.1 x) i j) ^ 2)
                        ≤ ∑ _i : Fin d, ∑ _j : Fin d,
                          (a.Lam + |t| * lInfEntryBound) ^ 2 :=
                            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
                              nlinarith [abs_nonneg ((a.toCoeffField x + t • h.1.1 x) i j),
                                sq_abs ((a.toCoeffField x + t • h.1.1 x) i j), hentrySum i j]
                    _ = (d : ℝ) * (d : ℝ) * (a.Lam + |t| * lInfEntryBound) ^ 2 := by
                      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                        nsmul_eq_mul]
                      ring
          _ ≤ (a.lam ^ 2 + (d : ℝ) * (d : ℝ) *
              (a.Lam + |t| * lInfEntryBound) ^ 2) * vecNormSq η := by
            refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg η)
            linarith [sq_nonneg a.lam]
  }
-- FROZEN-STATEMENT-END
