/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AdaptedCellExcessQuenchedRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedResponseMax
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakTransport

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedResponseQuenchedRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized cube response from a quenched block row

The exact identity-normalized response on a reference origin cube is bounded
by the physical quenched row on a centered enlargement.  The response depth
weight and the boundary-filling loss leave the positive exponent gap
`2 * s - rho`.
-/

namespace HCPolySupport
namespace HighContrast

open Book.Ch02

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem boundary_response_weight_identity
    (s rho : ℝ) (n G : ℕ) :
    (3 : ℝ) ^ (-s * 2 * (n : ℝ)) *
        (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ)) =
      (3 : ℝ) ^ (rho * (G : ℝ)) *
        ((3 : ℝ) ^ (-(2 * s - rho))) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

/-- The `q = 2` normalized reference-cube error is controlled by the physical
quenched block row on a centered enlargement. -/
theorem homogenizationErrorOnCube_normalizedReference_infinity_two_sq_le_row
    [NeZero d] (t G : ℕ) (a : CoeffSpace d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS)
              (t : ℤ))).toCoeffField)
    (s rho sourceScale : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hrhoGap : rho < 2 * s)
    (henclose : adaptedCell (Selection.normalizedRoot (symmPart abar)) (t : ℤ) ⊆
      centeredCube d ((t + G : ℕ) : ℤ))
    (hactive : sourceScale ≤ (3 : ℝ) ^ (t + G)) :
    Book.Ch02.HomogenizationErrorOnCube (originCube d (t : ℤ)) s
        .infinity (.finite 2) aRef (1 : Mat d) ^ 2 ≤
      max 1 (6 * (d : ℝ) * Real.sqrt d *
          ‖(Selection.normalizedRoot (symmPart abar))⁻¹‖) *
        (3 : ℝ) ^ (rho * (G : ℝ)) *
        (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho)))) *
          Quenched.quenched_block_row rho
            (Book.Ch02.constantBlockMatrix abar) sourceScale a (t + G) := by
  classical
  let q : Mat d := Selection.normalizedRoot (symmPart abar)
  let F : BlockMat d := Book.Ch02.constantBlockMatrix abar
  let Cq : ℝ := max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖)
  let R : ℝ := Quenched.quenched_block_row rho F sourceScale a (t + G)
  let ratio : ℝ := (3 : ℝ) ^ (-(2 * s - rho))
  let K : ℝ := Cq * (3 : ℝ) ^ (rho * (G : ℝ)) * R
  have hq : q.PosDef := by
    simpa only [q] using normalizedRoot_posDef_of_posDef hS
  have hs : 0 < s := by linarith only [hrho, hrhoGap]
  have hgap : 0 < 2 * s - rho := sub_pos.mpr hrhoGap
  have hratio0 : 0 ≤ ratio := by
    exact Real.rpow_nonneg (by norm_num) _
  have hratio1 : ratio < 1 := by
    dsimp only [ratio]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.mpr hgap)
  have hmax : ∀ n : ℕ,
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d (t : ℤ)) ((t : ℤ) - (n : ℤ)) aRef (1 : Mat d) ≤
        Cq * (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ)) * R := by
    intro n
    rw [maxDescendantNormalizedBlockResponseAtScale_originCube_eq_alignedIndex]
    rw [Response.alignedIndex_one_eq hq (by omega)]
    refine Book.Ch02.finsetSupReal_le _
      (Response.alignedIndex_nonempty hq (by omega)) ?_
    intro w hw
    have href := normalizedBlockResponseMax_le_adaptedCell_blockExcess
      a abar hS (t : ℤ) ((t : ℤ) - (n : ℤ)) w aRef haRef
    have href' :
        Book.Ch02.normalizedBlockResponseMax
            (translateCube w (originCube d ((t : ℤ) - (n : ℤ))))
              aRef (1 : Mat d) ≤
          blockExcess
            (coarseBlock (adaptedCellAt q ((t : ℤ) - (n : ℤ)) w) a)
            F := by
      simpa only [q, F, ← coarseBlock_eq_coarseBlockMatrix] using! href
    exact href'.trans <|
      blockExcess_coarseBlock_adaptedCellAt_le_quenched_block_row
        hq t n G a abar hS rho sourceScale hrho hrho1 henclose hactive w hw
  have hweight : ∀ n : ℕ,
      Book.Ch02.geometricWeight s 2 n ≤
        (3 : ℝ) ^ (-s * 2 * (n : ℝ)) := by
    intro n
    have hdiscount : Book.Ch02.geometricDiscount s 2 ≤ 1 := by
      unfold Book.Ch02.geometricDiscount
      exact sub_le_self 1 (Real.rpow_nonneg (by norm_num) _)
    unfold Book.Ch02.geometricWeight
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by norm_num) _) hdiscount
  have hleftSummable : Summable (fun n : ℕ ↦
      Book.Ch02.geometricWeight s 2 n *
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d (t : ℤ)) ((t : ℤ) - (n : ℤ)) aRef (1 : Mat d)) := by
    exact
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        (originCube d (t : ℤ)) aRef (1 : Mat d) hs
  have hrightSummable : Summable (fun n : ℕ ↦ K * ratio ^ n) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_left K
  have hterm : ∀ n : ℕ,
      Book.Ch02.geometricWeight s 2 n *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            (originCube d (t : ℤ)) ((t : ℤ) - (n : ℤ)) aRef (1 : Mat d) ≤
        K * ratio ^ n := by
    intro n
    have hweight0 : 0 ≤ Book.Ch02.geometricWeight s 2 n := by
      simpa [Book.Ch02.geometricWeight_eq_old] using
        (HCPolySupport.geometricWeight_nonneg n (by positivity : 0 ≤ s * (2 : ℝ)))
    have hmax0 : 0 ≤
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d (t : ℤ)) ((t : ℤ) - (n : ℤ)) aRef (1 : Mat d) :=
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg
        (originCube d (t : ℤ)) (by
          change (t : ℤ) - (n : ℤ) ≤ (t : ℤ)
          omega) aRef (1 : Mat d)
    have hbound0 : 0 ≤ Cq *
        (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ)) * R :=
      hmax0.trans (hmax n)
    calc
      Book.Ch02.geometricWeight s 2 n *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            (originCube d (t : ℤ)) ((t : ℤ) - (n : ℤ)) aRef (1 : Mat d) ≤
          Book.Ch02.geometricWeight s 2 n *
            (Cq * (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ)) * R) :=
        mul_le_mul_of_nonneg_left (hmax n) hweight0
      _ ≤ (3 : ℝ) ^ (-s * 2 * (n : ℝ)) *
            (Cq * (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ)) * R) :=
        mul_le_mul_of_nonneg_right (hweight n) hbound0
      _ = K * ratio ^ n := by
        rw [show (3 : ℝ) ^ (-s * 2 * (n : ℝ)) *
            (Cq * (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ)) * R) =
          Cq * ((3 : ℝ) ^ (-s * 2 * (n : ℝ)) *
            (3 : ℝ) ^ (rho * ((n + G : ℕ) : ℝ))) * R by ring]
        rw [boundary_response_weight_identity]
        dsimp only [K, ratio]
        ring
  rw [Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum
    (originCube d (t : ℤ)) hs aRef (1 : Mat d)]
  have hsum := hleftSummable.tsum_le_tsum hterm hrightSummable
  calc
    ∑' n : ℕ, Book.Ch02.geometricWeight s 2 n *
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d (t : ℤ)) ((t : ℤ) - (n : ℤ)) aRef (1 : Mat d) ≤
        ∑' n : ℕ, K * ratio ^ n := hsum
    _ = K * (1 / (1 - ratio)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hratio0 hratio1]
      ring
    _ = Cq * (3 : ℝ) ^ (rho * (G : ℝ)) *
        (1 / (1 - ratio)) * R := by ring
    _ = _ := rfl

end

end HighContrast
end HCPolySupport
