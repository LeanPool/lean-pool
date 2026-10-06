/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.HomogenizationErrorAllDepthMajorant

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.DescendantHomogenizationErrorInfinityTwo

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Descendant control for the quadratic homogenization error

The all-depth response row on a cube also controls the corresponding row on
any descendant.  Reindexing the geometric weights records the exact triadic
scale loss.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- A descendant at depth `h` has quadratic homogenization error at most
`3^(s h)` times that of its parent. -/
theorem homogenizationErrorOnCube_infinity_two_le_of_mem_descendantsAtScale
    [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ}
    (hs : 0 < s) (hR : R ∈ descendantsAtScale Q k) :
    Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) a a0 ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n ↦
    Book.Ch02.geometricWeight s 2 n *
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        Q (Q.scale - (n : ℤ)) a a0
  let fR : ℕ → ℝ := fun n ↦
    Book.Ch02.geometricWeight s 2 n *
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        R (R.scale - (n : ℤ)) a a0
  let factor : ℝ := Real.rpow (3 : ℝ) (2 * s * (h : ℝ))
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hsumQ : Summable fQ := by
    simpa only [fQ] using
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 hs
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp only [fQ]
    exact mul_nonneg
      (by
        simpa [Book.Ch02.geometricWeight_eq_old] using
          (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) n
            (by positivity : 0 ≤ s * (2 : ℝ))))
      (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        (by omega) a a0)
  have htailSummable : Summable (fun n : ℕ ↦ fQ (n + h)) :=
    (summable_nat_add_iff h).2 hsumQ
  have hfactorNonneg : 0 ≤ factor := Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale :
        R.scale - (n : ℤ) = Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hresp :
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            R (R.scale - (n : ℤ)) a a0 ≤
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            Q (Q.scale - ((n + h : ℕ) : ℤ)) a a0 := by
      have hl : R.scale - (n : ℤ) ≤ R.scale := by omega
      simpa only [hscale] using
        (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale
          a a0 hR hl)
    have hshift : Book.Ch02.geometricWeight s 2 n =
        factor * Book.Ch02.geometricWeight s 2 (n + h) := by
      rw [Book.Ch02.geometricWeight_eq_old,
        Book.Ch02.geometricWeight_eq_old]
      calc
        HCPolySupport.geometricWeight s 2 n =
            Real.rpow (3 : ℝ) (s * 2 * (h : ℝ)) *
              HCPolySupport.geometricWeight s 2 (n + h) :=
          HCPolySupport.geometricWeight_shift h n
        _ = factor * HCPolySupport.geometricWeight s 2 (n + h) := by
          congr 1
          rw [show factor = Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) from rfl]
          congr 1
          ring
    calc
      fR n = factor *
          (Book.Ch02.geometricWeight s 2 (n + h) *
            Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
              R (R.scale - (n : ℤ)) a a0) := by
          dsimp only [fR]
          rw [hshift]
          ring
      _ ≤ factor *
          (Book.Ch02.geometricWeight s 2 (n + h) *
            Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
              Q (Q.scale - ((n + h : ℕ) : ℤ)) a a0) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hresp
              (by
                simpa [Book.Ch02.geometricWeight_eq_old] using
                  (HCPolySupport.geometricWeight_nonneg
                    (s := s) (q := 2) (n + h)
                    (by positivity : 0 ≤ s * (2 : ℝ)))))
            hfactorNonneg
      _ = factor * fQ (n + h) := by rfl
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp only [fR]
    exact mul_nonneg
      (by
        simpa [Book.Ch02.geometricWeight_eq_old] using
          (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) n
            (by positivity : 0 ≤ s * (2 : ℝ))))
      (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg R
        (by omega) a a0)
  have hscaledSummable : Summable (fun n : ℕ ↦ factor * fQ (n + h)) :=
    htailSummable.mul_left factor
  have hsumR : Summable fR :=
    Summable.of_nonneg_of_le hRnonneg hterm hscaledSummable
  have hsumLe : ∑' n : ℕ, fR n ≤ ∑' n : ℕ, factor * fQ (n + h) :=
    hsumR.tsum_le_tsum hterm hscaledSummable
  have htailLe : ∑' n : ℕ, fQ (n + h) ≤ ∑' n : ℕ, fQ n := by
    have hsplit := hsumQ.sum_add_tsum_nat_add h
    have hprefixNonneg : 0 ≤ ∑ i ∈ Finset.range h, fQ i :=
      Finset.sum_nonneg fun i _ ↦ hQnonneg i
    linarith only [hsplit, hprefixNonneg]
  have hsq :
      Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) a a0 ^ 2 ≤
        factor *
          Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 ^ 2 := by
    rw [Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum R hs a a0,
      Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0]
    calc
      ∑' n : ℕ, fR n ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
      _ = factor * ∑' n : ℕ, fQ (n + h) := by
        simpa using htailSummable.tsum_mul_left factor
      _ ≤ factor * ∑' n : ℕ, fQ n :=
        mul_le_mul_of_nonneg_left htailLe hfactorNonneg
  have hER : 0 ≤ Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) a a0 := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    exact Real.rpow_nonneg (tsum_nonneg fun n ↦
      mul_nonneg
        (by
          simpa [Book.Ch02.geometricWeight_eq_old] using
            (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) n
              (by positivity : 0 ≤ s * (2 : ℝ))))
        (Real.rpow_nonneg
          (Book.Ch02.scaleResponseAtScale_infinity_nonneg R (by omega) a a0) _)) _
  have hEQ : 0 ≤ Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    exact Real.rpow_nonneg (tsum_nonneg fun n ↦
      mul_nonneg
        (by
          simpa [Book.Ch02.geometricWeight_eq_old] using
            (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) n
              (by positivity : 0 ≤ s * (2 : ℝ))))
        (Real.rpow_nonneg
          (Book.Ch02.scaleResponseAtScale_infinity_nonneg Q (by omega) a a0) _)) _
  have hfactorSqrt : Real.sqrt factor = Real.rpow (3 : ℝ) (s * (h : ℝ)) := by
    dsimp only [factor]
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) ^ (1 / 2 : ℝ) =
          Real.rpow (3 : ℝ) ((2 * s * (h : ℝ)) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
      _ = Real.rpow (3 : ℝ) (s * (h : ℝ)) := by
        congr 1
        ring
  calc
    Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) a a0 =
        Real.sqrt (Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) a a0 ^ 2) :=
      (Real.sqrt_sq hER).symm
    _ ≤ Real.sqrt
        (factor * Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt factor *
        Real.sqrt (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 ^ 2) := by
      rw [Real.sqrt_mul hfactorNonneg]
    _ = Real.rpow (3 : ℝ) (s * (h : ℝ)) *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
      rw [hfactorSqrt, Real.sqrt_sq hEQ]

end

end RowSupply
end HighContrast
end HCPolySupport
