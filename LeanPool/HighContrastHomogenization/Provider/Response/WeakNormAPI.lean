/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNorm

/-!
# High-contrast homogenization: Provider.Response.WeakNormAPI

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scale-average seminorm: the estimates its proofs read

The weak-norm estimate for the optimizer state uses the concrete scale-average
seminorm through five operations, all recorded here.

* **At each scale**, the normalized `ℓ^2` length `(avsum_z|·|^2)^{1/2}` obeys
  Cauchy-Schwarz and the triangle inequality; the triangle inequality is what
  the recent-scale decomposition
  `(X_t)_{U_k(z)} - (X_t)_{U_t} = ((X(U_k(z)))_{U_k(z)} - (X_t)_{U_t})
    + (X_t - X(U_k(z)))_{U_k(z)}`
  is summed through, and the uniform bound is what turns the cell-averaged
  energy bound into the scale-by-scale energy bound.
* **Across scales**, a scalewise majorant majorizes the seminorm, and a scalewise
  splitting splits it; this is the passage from the scale-by-scale energy bound
  to the weak-norm bound on the bad event and to the contribution of the old
  scales.
* **The normalization** `3^{-st}[·]` of the printed left side is the seminorm
  with `3^{sk}` replaced by `3^{-s(t-k)}`.
* **The value** is recovered as a real number exactly on the summable branch,
  the estimate being asserted also when the sum diverges; the geometric sum that
  makes both scale sums converge is the companion module.

The `ℓ^2` inequalities are proved once on the flattened index `𝒵 × (d ⊕ d)`,
where the doubled Euclidean structure of `ℝ^{2d}` and the normalized counting
structure of the aligned index are a single finite sum.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The normalized `ℓ^2` length of one scale -/

/-- The doubled Euclidean pairing expands on the flattened index. -/
theorem sum_blockVecDot_eq_sum_prod {ι : Type*} (Z : Finset ι) (u v : ι → BlockVec d) :
    ∑ z ∈ Z, blockVecDot (u z) (v z) =
      ∑ p ∈ Z ×ˢ (Finset.univ : Finset (Fin d ⊕ Fin d)),
        Sum.elim (fun i => (u p.1).1 i) (fun i => (u p.1).2 i) p.2 *
          Sum.elim (fun i => (v p.1).1 i) (fun i => (v p.1).2 i) p.2 := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.sum_sum_type]
  rfl

/-- **Cauchy-Schwarz for the doubled pairing over a finite index set.** -/
theorem sq_sum_blockVecDot_le {ι : Type*} (Z : Finset ι) (u v : ι → BlockVec d) :
    (∑ z ∈ Z, blockVecDot (u z) (v z)) ^ 2 ≤
      (∑ z ∈ Z, blockVecDot (u z) (u z)) * ∑ z ∈ Z, blockVecDot (v z) (v z) := by
  classical
  set S : Finset (ι × (Fin d ⊕ Fin d)) := Z ×ˢ (Finset.univ : Finset (Fin d ⊕ Fin d)) with hS
  set U : ι × (Fin d ⊕ Fin d) → ℝ :=
    fun p => Sum.elim (fun i => (u p.1).1 i) (fun i => (u p.1).2 i) p.2 with hU
  set V : ι × (Fin d ⊕ Fin d) → ℝ :=
    fun p => Sum.elim (fun i => (v p.1).1 i) (fun i => (v p.1).2 i) p.2 with hV
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := S) (f := U) (g := V)
  have hUU : ∑ p ∈ S, U p ^ 2 = ∑ z ∈ Z, blockVecDot (u z) (u z) := by
    rw [sum_blockVecDot_eq_sum_prod Z u u]
    exact Finset.sum_congr rfl fun p _ => pow_two (U p)
  have hVV : ∑ p ∈ S, V p ^ 2 = ∑ z ∈ Z, blockVecDot (v z) (v z) := by
    rw [sum_blockVecDot_eq_sum_prod Z v v]
    exact Finset.sum_congr rfl fun p _ => pow_two (V p)
  rw [sum_blockVecDot_eq_sum_prod Z u v, ← hUU, ← hVV]
  exact hcs

/-- **Cauchy-Schwarz for the normalized cell average.** -/
theorem sq_avsum_blockVecDot_le {ι : Type*} (Z : Finset ι) (u v : ι → BlockVec d) :
    (avsum Z fun z => blockVecDot (u z) (v z)) ^ 2 ≤
      (avsum Z fun z => blockVecDot (u z) (u z)) * avsum Z fun z => blockVecDot (v z) (v z) := by
  have hkey := sq_sum_blockVecDot_le Z u v
  have hc : (0 : ℝ) ≤ (((Z.card : ℝ))⁻¹) ^ 2 := by positivity
  rw [avsum_eq, avsum_eq, avsum_eq, mul_pow]
  calc (((Z.card : ℝ))⁻¹) ^ 2 * (∑ z ∈ Z, blockVecDot (u z) (v z)) ^ 2
      ≤ (((Z.card : ℝ))⁻¹) ^ 2 *
          ((∑ z ∈ Z, blockVecDot (u z) (u z)) * ∑ z ∈ Z, blockVecDot (v z) (v z)) :=
        mul_le_mul_of_nonneg_left hkey hc
    _ = (((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (u z)) *
          (((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, blockVecDot (v z) (v z)) := by ring

/-- The doubled Euclidean square of a sum. -/
theorem blockVecDot_add_self (u v : BlockVec d) :
    blockVecDot (u + v) (u + v) =
      blockVecDot u u + 2 * blockVecDot u v + blockVecDot v v := by
  have hd : ∀ a b : Vec d, vecDot (a + b) (a + b) = vecDot a a + 2 * vecDot a b + vecDot b b := by
    intro a b
    rw [vecDot_add_left, vecDot_add_right, vecDot_add_right, vecDot_comm b a]
    ring
  have hL : blockVecDot (u + v) (u + v) =
      vecDot (u.1 + v.1) (u.1 + v.1) + vecDot (u.2 + v.2) (u.2 + v.2) := rfl
  have hR : blockVecDot u u + 2 * blockVecDot u v + blockVecDot v v =
      vecDot u.1 u.1 + vecDot u.2 u.2 + 2 * (vecDot u.1 v.1 + vecDot u.2 v.2) +
        (vecDot v.1 v.1 + vecDot v.2 v.2) := rfl
  rw [hL, hR, hd u.1 v.1, hd u.2 v.2]
  ring

/-- **The triangle inequality of one scale**: the normalized `ℓ^2` length is
subadditive.  This is the inequality the recent-scale decomposition of the
weak-norm estimate is summed through. -/
theorem blockAvsumL2_add_le {ι : Type*} (Z : Finset ι) (u v : ι → BlockVec d) :
    blockAvsumL2 Z (fun z => u z + v z) ≤ blockAvsumL2 Z u + blockAvsumL2 Z v := by
  set A : ℝ := avsum Z fun z => blockVecDot (u z) (u z) with hA
  set B : ℝ := avsum Z fun z => blockVecDot (v z) (v z) with hB
  set C : ℝ := avsum Z fun z => blockVecDot (u z) (v z) with hC
  have hA0 : 0 ≤ A := avsum_nonneg fun z _ => blockVecDot_self_nonneg _
  have hB0 : 0 ≤ B := avsum_nonneg fun z _ => blockVecDot_self_nonneg _
  have hexp : (avsum Z fun z => blockVecDot (u z + v z) (u z + v z)) = A + 2 * C + B := by
    have hfun : (fun z => blockVecDot (u z + v z) (u z + v z)) =
        fun z => blockVecDot (u z) (u z) + 2 * blockVecDot (u z) (v z) +
          blockVecDot (v z) (v z) := by
      funext z
      exact blockVecDot_add_self (u z) (v z)
    rw [hfun, avsum_add, avsum_add, avsum_const_mul]
  have hCS : C ≤ Real.sqrt A * Real.sqrt B := by
    have hsq : C ^ 2 ≤ A * B := sq_avsum_blockVecDot_le Z u v
    calc C ≤ |C| := le_abs_self C
      _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B
  have hexpand : (Real.sqrt A + Real.sqrt B) ^ 2 = A + 2 * (Real.sqrt A * Real.sqrt B) + B := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    ring
  calc blockAvsumL2 Z (fun z => u z + v z) = Real.sqrt (A + 2 * C + B) := by
        rw [blockAvsumL2_eq, hexp]
    _ ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hexpand]
        linarith only [hCS]
    _ = Real.sqrt A + Real.sqrt B := Real.sqrt_sq (by positivity)

/-! ## The seminorm across scales -/

/-- **The normalized left side** `3^{-st}[F]_{B^{-s}_{2,1}(U_t)}` of the
weak-norm estimate: the scale weights become the decay factors
`3^{-s(t-k)}`. -/
theorem ofReal_rpow_mul_adaptedWeakSeminorm (q : Mat d) (t : ℤ) (s : ℝ)
    (F : Vec d → BlockVec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) * adaptedWeakSeminorm q t s F =
      ∑' j : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ))) *
        blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
          (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) F)) := by
  rw [adaptedWeakSeminorm_eq, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  have hexp : -(s * (t : ℝ)) + s * ((t : ℝ) - (j : ℝ)) = -(s * (j : ℝ)) := by ring
  rw [adaptedWeakScaleTerm_eq, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hexp]

/-! ## The value on the summable branch -/

end

end Response
end HighContrast
end HCPolySupport
