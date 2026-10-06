/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Finite
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality

/-!
# High-contrast homogenization: Provider.Regularity.RoundedOuterScaleFubini

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Nonnegative Fubini comparison for the rounded boundary row

The outer `q = 2` response weight and the inner codimension-one filling
weight form a nonnegative convolution.  Regrouping it by total depth exposes
the exact gap `1 - 2 * s`; a fixed parent shift costs exactly
`3 ^ (2 * s * G)`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open scoped BigOperators

noncomputable section

private theorem geometricWeight_mul_boundary_zpow
    (s C : ℝ) (l u : ℕ) :
    Book.Ch02.geometricWeight s 2 l *
        (C * (3 : ℝ) ^ (-(u : ℤ))) =
      (C * Real.rpow (3 : ℝ) (-(1 - 2 * s) * (u : ℝ))) *
        Book.Ch02.geometricWeight s 2 (l + u) := by
  have hzpow : (3 : ℝ) ^ (-(u : ℤ)) =
      Real.rpow (3 : ℝ) (-(u : ℤ) : ℝ) :=
    by
      simpa only [Int.cast_neg, Int.cast_natCast] using!
        (Real.rpow_intCast (3 : ℝ) (-(u : ℤ))).symm
  have hjoin :
      Real.rpow (3 : ℝ) (-s * 2 * (l : ℝ)) *
          Real.rpow (3 : ℝ) (-(u : ℤ) : ℝ) =
        Real.rpow (3 : ℝ)
          (-s * 2 * (l : ℝ) + (-(u : ℤ) : ℝ)) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
  have hsplit :
      Real.rpow (3 : ℝ)
          ((-(1 - 2 * s) * (u : ℝ)) +
            (-s * 2 * ((l + u : ℕ) : ℝ))) =
        Real.rpow (3 : ℝ) (-(1 - 2 * s) * (u : ℝ)) *
          Real.rpow (3 : ℝ) (-s * 2 * ((l + u : ℕ) : ℝ)) :=
    Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
  rw [hzpow, Book.Ch02.geometricWeight, Book.Ch02.geometricWeight]
  calc
    Book.Ch02.geometricDiscount s 2 *
          Real.rpow (3 : ℝ) (-s * 2 * (l : ℝ)) *
          (C * Real.rpow (3 : ℝ) (-(u : ℤ) : ℝ)) =
        C * Book.Ch02.geometricDiscount s 2 *
          (Real.rpow (3 : ℝ) (-s * 2 * (l : ℝ)) *
            Real.rpow (3 : ℝ) (-(u : ℤ) : ℝ)) := by ring
    _ = C * Book.Ch02.geometricDiscount s 2 *
          Real.rpow (3 : ℝ)
            (-s * 2 * (l : ℝ) + (-(u : ℤ) : ℝ)) := by rw [hjoin]
    _ = C * Book.Ch02.geometricDiscount s 2 *
          Real.rpow (3 : ℝ)
            ((-(1 - 2 * s) * (u : ℝ)) +
              (-s * 2 * ((l + u : ℕ) : ℝ))) := by
      congr 2
      push_cast
      ring
    _ = (C * Real.rpow (3 : ℝ) (-(1 - 2 * s) * (u : ℝ))) *
          (Book.Ch02.geometricDiscount s 2 *
            Real.rpow (3 : ℝ) (-s * 2 * ((l + u : ℕ) : ℝ))) := by
      rw [hsplit]
      ring

private theorem geometricWeight_shift
    (s : ℝ) (G n : ℕ) :
    Book.Ch02.geometricWeight s 2 n =
      Real.rpow (3 : ℝ) (2 * s * (G : ℝ)) *
        Book.Ch02.geometricWeight s 2 (n + G) := by
  rw [Book.Ch02.geometricWeight, Book.Ch02.geometricWeight]
  calc
    Book.Ch02.geometricDiscount s 2 *
          Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ)) =
        Book.Ch02.geometricDiscount s 2 *
          Real.rpow (3 : ℝ)
            (2 * s * (G : ℝ) + -s * 2 * ((n + G : ℕ) : ℝ)) := by
      congr 2
      push_cast
      ring
    _ = Real.rpow (3 : ℝ) (2 * s * (G : ℝ)) *
          (Book.Ch02.geometricDiscount s 2 *
            Real.rpow (3 : ℝ) (-s * 2 * ((n + G : ℕ) : ℝ))) := by
      rw [show Real.rpow (3 : ℝ)
          (2 * s * (G : ℝ) + -s * 2 * ((n + G : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) (2 * s * (G : ℝ)) *
          Real.rpow (3 : ℝ) (-s * 2 * ((n + G : ℕ) : ℝ)) by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _]
      ring

private theorem sum_antidiagonal_boundaryGap_le
    {s C : ℝ} (hsHalf : s < 1 / 2) (hC : 0 ≤ C) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
        C * Real.rpow (3 : ℝ) (-(1 - 2 * s) * (p.2 : ℝ)) ≤
      C * (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹ := by
  let gap : ℝ := 1 - 2 * s
  let f : ℕ → ℝ := fun u ↦
    C * Real.rpow (3 : ℝ) (-gap * (u : ℝ))
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith only [hsHalf]
  have hg : Summable (fun u : ℕ ↦
      Real.rpow (3 : ℝ) (-gap * (u : ℝ))) :=
    Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hgap
  have hf : Summable f := hg.mul_left C
  have hfinite :
      (∑ p ∈ Finset.antidiagonal n,
          C * Real.rpow (3 : ℝ) (-gap * (p.2 : ℝ))) =
        ∑ u ∈ Finset.range (n + 1), f u := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    change (∑ u ∈ Finset.range (n + 1), f (n - u)) = _
    simpa only [Nat.add_sub_cancel_left] using!
      Finset.sum_range_reflect f (n + 1)
  rw [show 1 - 2 * s = gap by rfl, hfinite]
  calc
    (∑ u ∈ Finset.range (n + 1), f u) ≤ ∑' u : ℕ, f u :=
      hf.sum_le_tsum (Finset.range (n + 1)) (fun u _ ↦ by
        exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
    _ = C * (Book.Ch02.geometricDiscount gap 1)⁻¹ := by
      rw [show (∑' u : ℕ, f u) = C * ∑' u : ℕ,
          Real.rpow (3 : ℝ) (-gap * (u : ℝ)) by
        exact tsum_mul_left]
      rw [Book.Ch05.Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount
        hgap]
      rw [Book.Ch02.geometricDiscount_eq_old]

/-- The nonnegative outer response row and inner rounded-filling row may be
regrouped by total depth.  The theorem derives every inner-row summability
witness, outer summability, and the exact shifted convolution bound. -/
theorem summable_boundaryConvolution_shift_and_tsum_le
    {s C : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2) (hC : 0 ≤ C)
    (G : ℕ) (A : ℕ → ℝ) (hA0 : ∀ n, 0 ≤ A n)
    (hA : Summable (fun n : ℕ ↦
      Book.Ch02.geometricWeight s 2 n * A n)) :
    (∀ l : ℕ, Summable (fun u : ℕ ↦
      (C * (3 : ℝ) ^ (-(u : ℤ))) * A (G + (l + u)))) ∧
      Summable (fun l : ℕ ↦
        Book.Ch02.geometricWeight s 2 l *
          ∑' u : ℕ,
            (C * (3 : ℝ) ^ (-(u : ℤ))) * A (G + (l + u))) ∧
      (∑' l : ℕ,
          Book.Ch02.geometricWeight s 2 l *
            ∑' u : ℕ,
              (C * (3 : ℝ) ^ (-(u : ℤ))) * A (G + (l + u))) ≤
        (C * (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹) *
          Real.rpow (3 : ℝ) (2 * s * (G : ℝ)) *
            ∑' n : ℕ, Book.Ch02.geometricWeight s 2 n * A n := by
  classical
  let w : ℕ → ℝ := fun n ↦ Book.Ch02.geometricWeight s 2 n
  let shifted : ℕ → ℝ := fun n ↦ w n * A (G + n)
  let kernel : ℕ → ℝ := fun u ↦ C * (3 : ℝ) ^ (-(u : ℤ))
  let term : ℕ × ℕ → ℝ := fun p ↦
    w p.1 * kernel p.2 * A (G + (p.1 + p.2))
  let diagonal : ℕ → ℝ := fun n ↦
    ∑ p ∈ Finset.antidiagonal n, term p
  let boundaryFactor : ℝ :=
    C * (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹
  let shiftFactor : ℝ := Real.rpow (3 : ℝ) (2 * s * (G : ℝ))
  have hw0 : ∀ n, 0 ≤ w n := by
    intro n
    dsimp only [w]
    simpa only [Book.Ch02.geometricWeight_eq_old] using
      (HCPolySupport.geometricWeight_nonneg n
        (mul_nonneg hs.le (by norm_num : (0 : ℝ) ≤ 2)))
  have hwpos : ∀ n, 0 < w n := by
    intro n
    dsimp only [w]
    simpa only [Book.Ch02.geometricWeight_eq_old] using
      (HCPolySupport.geometricWeight_pos n
        (mul_pos hs (by norm_num : (0 : ℝ) < 2)))
  have hkernel0 : ∀ u, 0 ≤ kernel u := fun u ↦
    mul_nonneg hC (zpow_nonneg (by norm_num) _)
  have hterm0 : ∀ p, 0 ≤ term p := fun p ↦
    mul_nonneg (mul_nonneg (hw0 p.1) (hkernel0 p.2))
      (hA0 (G + (p.1 + p.2)))
  have hshiftEq : ∀ n, shifted n = shiftFactor *
      (w (n + G) * A (n + G)) := by
    intro n
    dsimp only [shifted, shiftFactor, w]
    rw [add_comm G n, geometricWeight_shift s G n]
    ring
  have htail : Summable (fun n : ℕ ↦ w (n + G) * A (n + G)) := by
    simpa only [w] using (summable_nat_add_iff G).2 hA
  have hshifted : Summable shifted :=
    (htail.mul_left shiftFactor).congr (fun n ↦ (hshiftEq n).symm)
  have hshifted0 : ∀ n, 0 ≤ shifted n := fun n ↦
    mul_nonneg (hw0 n) (hA0 (G + n))
  have hdiagEq : ∀ n, diagonal n =
      (∑ p ∈ Finset.antidiagonal n,
        C * Real.rpow (3 : ℝ) (-(1 - 2 * s) * (p.2 : ℝ))) *
          shifted n := by
    intro n
    dsimp only [diagonal]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hpadd : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    dsimp only [term, kernel, shifted, w]
    rw [geometricWeight_mul_boundary_zpow]
    rw [hpadd]
    ring
  have hdiag0 : ∀ n, 0 ≤ diagonal n := fun n ↦
    Finset.sum_nonneg fun p _ ↦ hterm0 p
  have hboundary0 : 0 ≤ boundaryFactor := by
    dsimp only [boundaryFactor]
    exact mul_nonneg hC (inv_nonneg.mpr
      (Book.Ch02.book_geometricDiscount_nonneg (by
        have hgap : 0 ≤ 1 - 2 * s := by linarith only [hsHalf]
        exact mul_nonneg hgap (by norm_num : (0 : ℝ) ≤ 1))))
  have hdiagLe : ∀ n, diagonal n ≤ boundaryFactor * shifted n := by
    intro n
    rw [hdiagEq n]
    exact mul_le_mul_of_nonneg_right
      (sum_antidiagonal_boundaryGap_le hsHalf hC n) (hshifted0 n)
  have hdiagMajor : Summable (fun n ↦ boundaryFactor * shifted n) :=
    hshifted.mul_left boundaryFactor
  have hdiagonal : Summable diagonal :=
    Summable.of_nonneg_of_le hdiag0 hdiagLe hdiagMajor
  let sigmaTerm : (Σ n : ℕ, {p // p ∈ Finset.antidiagonal n}) → ℝ :=
    fun i ↦ term i.2.1
  have hsigma0 : ∀ i, 0 ≤ sigmaTerm i := fun i ↦ hterm0 i.2.1
  have hsigmaOuter : Summable (fun n : ℕ ↦
      ∑' p : {p // p ∈ Finset.antidiagonal n}, sigmaTerm ⟨n, p⟩) := by
    refine hdiagonal.congr ?_
    intro n
    rw [tsum_fintype]
    simpa only [sigmaTerm, diagonal] using!
      (Finset.sum_finset_coe (s := Finset.antidiagonal n) term).symm
  have hsigma : Summable sigmaTerm :=
    (summable_sigma_of_nonneg hsigma0).2
      ⟨fun _ ↦ (hasSum_fintype _).summable, hsigmaOuter⟩
  have hpair : Summable term := by
    exact Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hsigma
  have hinner : ∀ l : ℕ, Summable (fun u : ℕ ↦
      kernel u * A (G + (l + u))) := by
    intro l
    have hfiber : Summable (fun u : ℕ ↦ term (l, u)) :=
      hpair.prod_factor l
    have hscaled := hfiber.mul_left (w l)⁻¹
    refine hscaled.congr ?_
    intro u
    dsimp only [term]
    rw [inv_mul_eq_iff_eq_mul₀ (hwpos l).ne']
    ring
  have houterEq : (fun l : ℕ ↦ ∑' u : ℕ, term (l, u)) =
      fun l : ℕ ↦ w l * ∑' u : ℕ, kernel u * A (G + (l + u)) := by
    funext l
    dsimp only [term]
    rw [show (fun u : ℕ ↦ w l * kernel u * A (G + (l + u))) =
        fun u : ℕ ↦ w l * (kernel u * A (G + (l + u))) by
      funext u
      ring,
      tsum_mul_left]
  have houter : Summable (fun l : ℕ ↦
      w l * ∑' u : ℕ, kernel u * A (G + (l + u))) := by
    exact hpair.prod.congr (fun l ↦ congrFun houterEq l)
  have hpairEqDiagonal : (∑' p : ℕ × ℕ, term p) = ∑' n : ℕ, diagonal n := by
    rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq term]
    change (∑' c, sigmaTerm c) = ∑' n : ℕ, diagonal n
    rw [hsigma.tsum_sigma' (fun _ ↦ (hasSum_fintype _).summable)]
    apply tsum_congr
    intro n
    rw [tsum_fintype]
    simpa only [sigmaTerm, diagonal] using!
      (Finset.sum_finset_coe (s := Finset.antidiagonal n) term)
  have houterTsum :
      (∑' l : ℕ, w l * ∑' u : ℕ,
          kernel u * A (G + (l + u))) = ∑' n : ℕ, diagonal n := by
    rw [← hpairEqDiagonal, hpair.tsum_prod]
    exact tsum_congr fun l ↦ (congrFun houterEq l).symm
  have htailLe :
      (∑' n : ℕ, w (n + G) * A (n + G)) ≤
        ∑' n : ℕ, w n * A n := by
    have hsplit := hA.sum_add_tsum_nat_add G
    rw [← hsplit]
    exact le_add_of_nonneg_left
      (Finset.sum_nonneg fun n _ ↦ mul_nonneg (hw0 n) (hA0 n))
  have hshiftedTsum : (∑' n : ℕ, shifted n) ≤
      shiftFactor * ∑' n : ℕ, w n * A n := by
    calc
      (∑' n : ℕ, shifted n) =
          shiftFactor * ∑' n : ℕ, w (n + G) * A (n + G) := by
        rw [show (∑' n : ℕ, shifted n) =
            ∑' n : ℕ, shiftFactor * (w (n + G) * A (n + G)) by
          exact tsum_congr hshiftEq]
        rw [tsum_mul_left]
      _ ≤ shiftFactor * ∑' n : ℕ, w n * A n :=
        mul_le_mul_of_nonneg_left htailLe (Real.rpow_nonneg (by norm_num) _)
  refine ⟨?_, ?_, ?_⟩
  · intro l
    simpa only [kernel, add_assoc] using hinner l
  · simpa only [w, kernel, add_assoc] using houter
  · rw [show
      (∑' l : ℕ,
          Book.Ch02.geometricWeight s 2 l *
            ∑' u : ℕ,
              (C * (3 : ℝ) ^ (-(u : ℤ))) * A (G + (l + u))) =
        ∑' l : ℕ, w l * ∑' u : ℕ,
          kernel u * A (G + (l + u)) by rfl,
      houterTsum]
    calc
      (∑' n : ℕ, diagonal n) ≤
          ∑' n : ℕ, boundaryFactor * shifted n :=
        hdiagonal.tsum_le_tsum hdiagLe hdiagMajor
      _ = boundaryFactor * ∑' n : ℕ, shifted n := by
        rw [tsum_mul_left]
      _ ≤ boundaryFactor *
          (shiftFactor * ∑' n : ℕ, w n * A n) :=
        mul_le_mul_of_nonneg_left hshiftedTsum hboundary0
      _ = _ := by
        dsimp only [boundaryFactor, shiftFactor, w]
        ring

end

end Transport
end HighContrast
end HCPolySupport
