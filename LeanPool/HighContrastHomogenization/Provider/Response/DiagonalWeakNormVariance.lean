/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormPartition

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormVariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite variance on an aligned scale

The child averages at a fixed scale have the parent average as their ordinary
finite mean.  Subtracting that mean can therefore only decrease their
normalized Euclidean square sum.  This is the variance step in the
scale-by-scale energy bound of the weak-norm estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

variable {d : ℕ}

/-- The scalar finite-variance identity for the normalized average. -/
theorem avsum_sq_sub_mean_eq {ι : Type*} {Z : Finset ι} (hZ : Z.Nonempty)
    (f : ι → ℝ) (m : ℝ) (hmean : avsum Z f = m) :
    avsum Z (fun z => (f z - m) ^ 2) =
      avsum Z (fun z => (f z) ^ 2) - m ^ 2 := by
  have hcard : ((Z.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hZ).ne'
  have hsum : ∑ z ∈ Z, (f z - m) ^ 2 =
      (∑ z ∈ Z, (f z) ^ 2) - 2 * m * (∑ z ∈ Z, f z) +
        (Z.card : ℝ) * m ^ 2 := by
    calc
      ∑ z ∈ Z, (f z - m) ^ 2 =
          ∑ z ∈ Z, ((f z) ^ 2 - 2 * m * f z + m ^ 2) :=
        Finset.sum_congr rfl fun z _ => by ring
      _ = (∑ z ∈ Z, (f z) ^ 2) - 2 * m * (∑ z ∈ Z, f z) +
          (Z.card : ℝ) * m ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hsumf : ∑ z ∈ Z, f z = (Z.card : ℝ) * m := by
    have hinv : ((Z.card : ℝ))⁻¹ * (Z.card : ℝ) = 1 := inv_mul_cancel₀ hcard
    calc
      ∑ z ∈ Z, f z =
          (Z.card : ℝ) * (((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, f z) := by
        rw [← mul_assoc, mul_comm (Z.card : ℝ), hinv, one_mul]
      _ = (Z.card : ℝ) * m := by rw [← avsum_eq, hmean]
  rw [avsum_eq, avsum_eq, hsum, hsumf]
  have hinv : ((Z.card : ℝ))⁻¹ * (Z.card : ℝ) = 1 := inv_mul_cancel₀ hcard
  calc
    ((Z.card : ℝ))⁻¹ *
          ((∑ z ∈ Z, (f z) ^ 2) - 2 * m * ((Z.card : ℝ) * m) +
            (Z.card : ℝ) * m ^ 2) =
        ((Z.card : ℝ))⁻¹ * (∑ z ∈ Z, (f z) ^ 2) +
          (((Z.card : ℝ))⁻¹ * (Z.card : ℝ)) * (-m ^ 2) := by ring
    _ = ((Z.card : ℝ))⁻¹ * (∑ z ∈ Z, (f z) ^ 2) - m ^ 2 := by
      rw [hinv, one_mul]
      ring

private theorem blockVecDot_sub_self_eq_sum (x m : BlockVec d) :
    blockVecDot (x - m) (x - m) =
      ∑ a : BlockCoord d, (toFullBlockVec x a - toFullBlockVec m a) ^ 2 := by
  rw [← dotProduct_toFullBlockVec]
  simp only [dotProduct, pow_two]
  exact Finset.sum_congr rfl fun a _ => by
    cases a <;> rfl

private theorem blockVecDot_self_eq_sum (x : BlockVec d) :
    blockVecDot x x = ∑ a : BlockCoord d, (toFullBlockVec x a) ^ 2 := by
  rw [← dotProduct_toFullBlockVec]
  simp only [dotProduct, pow_two]

private theorem avsum_sum_comm {ι κ : Type*} [Fintype κ]
    (Z : Finset ι) (f : ι → κ → ℝ) :
    avsum Z (fun z => ∑ a : κ, f z a) =
      ∑ a : κ, avsum Z (fun z => f z a) := by
  rw [avsum_eq]
  simp_rw [avsum_eq]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  exact @Finset.sum_comm κ ℝ ι _ Z Finset.univ
    (fun z a => (((Z.card : ℝ))⁻¹) * f z a)

/-- **Subtracting the finite mean decreases the normalized doubled
Euclidean length.** -/
theorem blockAvsumL2_sub_mean_le {ι : Type*} {Z : Finset ι}
    (hZ : Z.Nonempty) (u : ι → BlockVec d) (m : BlockVec d)
    (hmean : ∀ a : BlockCoord d,
      avsum Z (fun z => toFullBlockVec (u z) a) = toFullBlockVec m a) :
    blockAvsumL2 Z (fun z => u z - m) ≤ blockAvsumL2 Z u := by
  have hvar : avsum Z (fun z => blockVecDot (u z - m) (u z - m)) =
      avsum Z (fun z => blockVecDot (u z) (u z)) - blockVecDot m m := by
    calc
      avsum Z (fun z => blockVecDot (u z - m) (u z - m)) =
          avsum Z (fun z =>
            ∑ a : BlockCoord d,
              (toFullBlockVec (u z) a - toFullBlockVec m a) ^ 2) := by
        congr 1
        funext z
        exact blockVecDot_sub_self_eq_sum (u z) m
      _ = ∑ a : BlockCoord d,
          avsum Z (fun z =>
            (toFullBlockVec (u z) a - toFullBlockVec m a) ^ 2) :=
        avsum_sum_comm Z _
      _ = ∑ a : BlockCoord d,
          (avsum Z (fun z => (toFullBlockVec (u z) a) ^ 2) -
            (toFullBlockVec m a) ^ 2) := by
        exact Finset.sum_congr rfl fun a _ =>
          avsum_sq_sub_mean_eq hZ _ _ (hmean a)
      _ = (∑ a : BlockCoord d,
          avsum Z (fun z => (toFullBlockVec (u z) a) ^ 2)) -
            ∑ a : BlockCoord d, (toFullBlockVec m a) ^ 2 := by
        rw [Finset.sum_sub_distrib]
      _ = avsum Z (fun z => ∑ a : BlockCoord d,
          (toFullBlockVec (u z) a) ^ 2) -
            ∑ a : BlockCoord d, (toFullBlockVec m a) ^ 2 := by
        rw [avsum_sum_comm]
      _ = avsum Z (fun z => blockVecDot (u z) (u z)) - blockVecDot m m := by
        have hleft : (fun z => ∑ a : BlockCoord d,
            (toFullBlockVec (u z) a) ^ 2) =
            fun z => blockVecDot (u z) (u z) := by
          funext z
          exact (blockVecDot_self_eq_sum (u z)).symm
        rw [hleft, ← blockVecDot_self_eq_sum m]
  rw [blockAvsumL2_eq, blockAvsumL2_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [hvar]
  exact sub_le_self _ (blockVecDot_nonneg m)

end

end Response
end HighContrast
end HCPolySupport
