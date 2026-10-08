/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LocalGradientTopology
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineGradientQuotientInverse
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Corrector.AffineSandwichDepth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

open scoped Matrix.Norms.L2Operator

/-!
# The affine sandwich depth for the centered cube exhaustion

The image of a centered exhaustion cube under a fixed matrix is contained in a
centered exhaustion cube of a fixed larger index: the depth depends on the
matrix alone, not on the cube.  This is the geometric half of the carrier-level
affine pullback.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The total absolute mass of the entries of a matrix. -/
@[expose]
def matAbsTotal (L : Mat d) : ℝ := ∑ i, ∑ j, |L i j|

theorem row_abs_le_matAbsTotal (L : Mat d) (i : Fin d) :
    ∑ j, |L i j| ≤ matAbsTotal L :=
  Finset.single_le_sum (f := fun i : Fin d ↦ ∑ j, |L i j|)
    (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)

/-- Coordinates of a matrix image are bounded by the total absolute mass times
the coordinate bound of the argument. -/
theorem abs_matVecMul_le_matAbsTotal_mul (L : Mat d) (x : Vec d) (i : Fin d)
    {c : ℝ} (hc : 0 ≤ c) (hx : ∀ j, |x j| ≤ c) :
    |matVecMul L x i| ≤ matAbsTotal L * c := by
  have hsum : |matVecMul L x i| ≤ ∑ j, |L i j * x j| := by
    simpa only [matVecMul] using
      Finset.abs_sum_le_sum_abs (fun j ↦ L i j * x j) Finset.univ
  have hterm : ∑ j, |L i j * x j| ≤ ∑ j, |L i j| * c := by
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
  have hrow : (∑ j, |L i j|) * c ≤ matAbsTotal L * c :=
    mul_le_mul_of_nonneg_right (row_abs_le_matAbsTotal L i) hc
  calc |matVecMul L x i| ≤ ∑ j, |L i j * x j| := hsum
    _ ≤ ∑ j, |L i j| * c := hterm
    _ = (∑ j, |L i j|) * c := by rw [Finset.sum_mul]
    _ ≤ matAbsTotal L * c := hrow

/-- **The affine sandwich depth.**  For every matrix there is a fixed depth `k`
such that the image of every centered exhaustion cube sits inside the centered
exhaustion cube `k` steps coarser. -/
theorem exists_matImage_localGradientCube_subset (L : Mat d) :
    ∃ k : ℕ, ∀ q : ℕ,
      matImage L (localGradientCube d q) ⊆ localGradientCube d (q + k) := by
  obtain ⟨k, hk⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).eventually_gt_atTop
      (matAbsTotal L)).exists
  refine ⟨k, fun q ↦ ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [localGradientCube, mem_openCubeSet_originCube_iff] at hx
  rw [localGradientCube, mem_openCubeSet_originCube_iff]
  intro i
  have hpow : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
  have hc : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ q := by positivity
  have hxbound : ∀ j, |x j| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ q := by
    intro j
    obtain ⟨hlo, hhi⟩ := hx j
    rw [zpow_natCast] at hlo hhi
    rw [abs_le]
    constructor <;> linarith only [hlo, hhi]
  have hbound := abs_matVecMul_le_matAbsTotal_mul L x i hc hxbound
  have hstrict :
      matAbsTotal L * ((1 / 2 : ℝ) * (3 : ℝ) ^ q) <
        (1 / 2 : ℝ) * (3 : ℝ) ^ (q + k) := by
    have hmul :
        matAbsTotal L * ((1 / 2 : ℝ) * (3 : ℝ) ^ q) <
          (3 : ℝ) ^ k * ((1 / 2 : ℝ) * (3 : ℝ) ^ q) :=
      mul_lt_mul_of_pos_right hk (by positivity)
    have hrewrite :
        (3 : ℝ) ^ k * ((1 / 2 : ℝ) * (3 : ℝ) ^ q) =
          (1 / 2 : ℝ) * (3 : ℝ) ^ (q + k) := by
      rw [pow_add]; ring
    rw [hrewrite] at hmul
    exact hmul
  have habs : |matVecMul L x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ (q + k) :=
    lt_of_le_of_lt hbound hstrict
  rw [zpow_natCast]
  rw [abs_lt] at habs
  exact ⟨by linarith only [habs.1], habs.2⟩

end

end Root
end HighContrast
end HCPolySupport
