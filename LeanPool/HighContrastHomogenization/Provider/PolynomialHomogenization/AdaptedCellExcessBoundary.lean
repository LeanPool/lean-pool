/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AdaptedCellExcessFilling
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterQuadratic
public import LeanPool.HighContrastHomogenization.Provider.Entry.IdentityCells

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.AdaptedCellExcessBoundary

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary-row control of an adapted-cell excess

Filling an adapted cell by Euclidean triadic cells loses one geometric boundary
weight per generation.  A nonnegative summable majorant for the Euclidean cell
excesses therefore controls the excess of the adapted cell by its convolution
with that boundary kernel.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {d : ℕ}

private theorem sum_range_to_Icc_descending {k m : ℤ} (hkm : k ≤ m)
    (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (Int.toNat (m - k)), F j) =
      ∑ n ∈ Finset.Icc (k + 1) m, F (Int.toNat (m - n)) := by
  classical
  refine Finset.sum_bij (fun j _ => m - (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
    have hjlt : (j : ℤ) < m - k := by
      have hjlt' : (j : ℤ) < ((Int.toNat (m - k) : ℕ) : ℤ) := by
        exact_mod_cast Finset.mem_range.mp hj
      simpa [hL] using hjlt'
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro j₁ _ j₂ _ h
    have hcast : (j₁ : ℤ) = (j₂ : ℤ) := by
      have : m - (j₁ : ℤ) = m - (j₂ : ℤ) := by simpa using h
      omega
    exact_mod_cast hcast
  · intro n hn
    have hnlo : k + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnhi : n ≤ m := (Finset.mem_Icc.mp hn).2
    refine ⟨Int.toNat (m - n), ?_, ?_⟩
    · have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
        Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
      have hmn0 : 0 ≤ m - n := sub_nonneg.mpr hnhi
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn0
      apply Finset.mem_range.mpr
      have hcast : ((Int.toNat (m - n) : ℕ) : ℤ) <
          ((Int.toNat (m - k) : ℕ) : ℤ) := by
        rw [hto, hL]
        omega
      exact_mod_cast hcast
    · have hmn0 : 0 ≤ m - n := sub_nonneg.mpr hnhi
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn0
      change m - ((Int.toNat (m - n) : ℕ) : ℤ) = n
      rw [hto]
      omega
  · intro j _
    have harg : Int.toNat (m - (m - (j : ℤ))) = j := by
      have hsub : m - (m - (j : ℤ)) = (j : ℤ) := by ring
      simp [hsub]
    exact congrArg F harg.symm

private theorem zpow_depth_identity {k r : ℤ} (hrk : r ≤ k) :
    (3 : ℝ) ^ (r - k) =
      (3 : ℝ) ^ (-(Int.toNat (k - r) : ℤ)) := by
  have hkr0 : 0 ≤ k - r := sub_nonneg.mpr hrk
  have hto : ((Int.toNat (k - r) : ℕ) : ℤ) = k - r :=
    Int.toNat_of_nonneg hkr0
  rw [hto]
  congr 1
  ring

private theorem sub_depth_identity {k r : ℤ} (hrk : r ≤ k) :
    k - (Int.toNat (k - r) : ℤ) = r := by
  have hkr0 : 0 ≤ k - r := sub_nonneg.mpr hrk
  rw [Int.toNat_of_nonneg hkr0]
  ring

/-- The excess of an adapted cell is bounded by the Euclidean-cell excess
majorant convolved with the geometric boundary kernel.  The hypothesis on `B`
is local to cells of at most the target's scale contained in the target, so a
containing Euclidean cube can be inserted later without changing this
deterministic statement. -/
theorem blockExcess_coarseBlock_adaptedCellAt_le_boundary_tsum
    [NeZero d] {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (z : Fin d → ℤ) (a : CoeffSpace d)
    {F : BlockMat d} (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    (B : ℤ → ℝ) (hB0 : ∀ r, 0 ≤ B r)
    (hBsum : Summable (fun n : ℕ =>
      (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ))))
    (hcell : ∀ (r : ℤ) (w : Fin d → ℤ), r ≤ k →
      standardCell d r w ⊆ adaptedCellAt q k z →
        blockExcess (coarseBlock (standardCell d r w) a) F ≤ B r) :
    blockExcess (coarseBlock (adaptedCellAt q k z) a) F ≤
      max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        ∑' n : ℕ, (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ)) := by
  classical
  let Cq : ℝ := max 1 (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖)
  have hCq0 : 0 ≤ Cq := le_trans zero_le_one (le_max_left _ _)
  have hCq1 : 1 ≤ Cq := le_max_left _ _
  have hCqgeom : 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖ ≤ Cq := le_max_right _ _
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  obtain ⟨Z, hZ, -, -, -, -, -, -, -⟩ :=
    Transport.maximal_filling hq hone k k (adaptedCellCenter q k z)
  have htarget : adaptedCellTranslate q k (adaptedCellCenter q k z) =
      adaptedCellAt q k z := rfl
  rw [← htarget]
  refine blockExcess_coarseBlock_adaptedCellTranslate_le_of_filling_rows
    hq hone hZ hF hFpd a
      (mul_nonneg hCq0 (tsum_nonneg fun n =>
        mul_nonneg (by positivity) (hB0 (k - (n : ℤ))))) ?_
  intro J hJk
  have hrow : ∀ r ∈ Finset.Icc J k,
      (∑ w ∈ Z r,
        (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q k (adaptedCellCenter q k z))).toReal *
          blockExcess (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) F) ≤
        Cq * (3 : ℝ) ^ (r - k) * B r := by
    intro r hr
    have hrk : r ≤ k := (Finset.mem_Icc.mp hr).2
    have hcellrow : ∀ w ∈ Z r,
        blockExcess (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) F ≤ B r := by
      intro w hw
      have hwfill : w ∈ Transport.fillingIndex (1 : Mat d) k
          (adaptedCellTranslate q k (adaptedCellCenter q k z)) r := by
        rw [← hZ r]
        exact Finset.mem_coe.mpr hw
      have hsub := Transport.adaptedCellAt_subset_of_mem_fillingIndex hwfill
      rw [Entry.adaptedCellAt_one] at hsub ⊢
      exact hcell r w hrk hsub
    have hweighted : ∀ {c : ℝ},
        (∑ w ∈ Z r,
          (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
              (volume (adaptedCellTranslate q k
                (adaptedCellCenter q k z))).toReal) ≤ c →
          (∑ w ∈ Z r,
            (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
                (volume (adaptedCellTranslate q k
                  (adaptedCellCenter q k z))).toReal *
              blockExcess (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) F) ≤
            c * B r := by
      intro c hmass
      exact Entry.sum_weight_mul_le (d := d) (Z := Z r)
        (V := fun w => adaptedCellAt (1 : Mat d) r w)
        (W := adaptedCellTranslate q k (adaptedCellCenter q k z))
        (A := fun w => blockExcess
          (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) F)
        (B := B r) (c := c) (hB0 r) hcellrow hmass
    by_cases hrEq : r = k
    · subst r
      have hmass := Transport.sum_relative_volume_row_le_one hq hone (hZ k)
      have hstep := hweighted hmass
      simpa [Cq, htarget] using
        hstep.trans (mul_le_mul_of_nonneg_right hCq1 (hB0 k))
    · have hrlt : r < k := lt_of_le_of_ne hrk hrEq
      have hmass := Transport.sum_relative_volume_row_le hq hone hrlt (hZ r)
      rw [Matrix.mul_one] at hmass
      have hstep := hweighted hmass
      have hpow0 : 0 ≤ (3 : ℝ) ^ (r - k) := by positivity
      have hfinal := mul_le_mul_of_nonneg_right hCqgeom
        (mul_nonneg hpow0 (hB0 r))
      exact hstep.trans (by
        simpa [mul_assoc, htarget] using hfinal)
  refine le_trans (Finset.sum_le_sum hrow) ?_
  have hreindex :
      (∑ r ∈ Finset.Icc J k, Cq * (3 : ℝ) ^ (r - k) * B r) =
        Cq * ∑ n ∈ Finset.range (Int.toNat (k - (J - 1))),
          (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ)) := by
    have hJ : J - 1 ≤ k := by omega
    have hmap := sum_range_to_Icc_descending hJ
      (fun n : ℕ => (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ)))
    have hmap' :
        (∑ n ∈ Finset.range (Int.toNat (k - (J - 1))),
          (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ))) =
          ∑ r ∈ Finset.Icc J k,
            (3 : ℝ) ^ (-(Int.toNat (k - r) : ℤ)) *
              B (k - (Int.toNat (k - r) : ℤ)) := by
      simpa only [sub_add_cancel] using hmap
    calc
      (∑ r ∈ Finset.Icc J k, Cq * (3 : ℝ) ^ (r - k) * B r) =
          Cq * ∑ r ∈ Finset.Icc J k, (3 : ℝ) ^ (r - k) * B r := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = Cq * ∑ r ∈ Finset.Icc J k,
          (3 : ℝ) ^ (-(Int.toNat (k - r) : ℤ)) *
            B (k - (Int.toNat (k - r) : ℤ)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        have hrk : r ≤ k := (Finset.mem_Icc.mp hr).2
        rw [zpow_depth_identity hrk, sub_depth_identity hrk]
      _ = Cq * ∑ n ∈ Finset.range (Int.toNat (k - (J - 1))),
          (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ)) := by rw [hmap']
  rw [hreindex]
  exact mul_le_mul_of_nonneg_left
    (hBsum.sum_le_tsum _ fun n _ => mul_nonneg (by positivity) (hB0 _)) hCq0

end

end HighContrast
end HCPolySupport
