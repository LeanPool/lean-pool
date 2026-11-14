/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.LatticePrescribedMinima
public import LeanPool.CCDN.ClassGroup.NumberFieldEuclideanLattice
import LeanPool.CCDN.ClassGroup.EuclideanNumberFieldBasis
import LeanPool.CCDN.ClassGroup.FieldBasisMultiplicationProduct
import LeanPool.CCDN.ClassGroup.LatticeMinimaFlag
import LeanPool.CCDN.ClassGroup.LatticeMinimaProduct

/-!
Short independent algebraic integers at the uniform discriminant-root
scale, from greedy lattice vectors, the multiplication pairing, and the
covolume estimate.

The product-of-lengths bound for a prescribed first lattice vector.
Each later vector is shortest outside the preceding span, and the covolume
bound for positive monotone flag thresholds applies.

Numerical conversion of a lattice norm-product bound into the uniform
discriminant-root scale for its largest minimum.
-/

@[expose] public section
namespace CCDN
noncomputable section

private theorem largest_minimum_le_discriminant_root
    {n : ℕ} (hn : 0 < n) {M P D : ℝ} (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hminimum : M ^ n ≤ P ^ 2)
    (hproduct : P ≤ Real.sqrt n * (n : ℝ) ^ n * Real.sqrt D) :
    M ≤ (n : ℝ) ^ 3 * D ^ (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq := (sq_le_sq₀ hP (by positivity)).mpr hproduct
  have hsq' : P ^ 2 ≤ (n : ℝ) ^ (2 * n + 1) * D := by
    convert hsq using 1
    rw [mul_pow, mul_pow, Real.sq_sqrt hnR.le, Real.sq_sqrt hD,
      pow_succ, pow_mul]
    ring
  have hdegrees : (n : ℝ) ^ (2 * n + 1) ≤ (n : ℝ) ^ (3 * n) :=
    pow_le_pow_right₀ hn1 (by omega)
  have hroot : (D ^ (1 / (n : ℝ))) ^ n = D := by
    rw [← Real.rpow_mul_natCast hD, one_div_mul_cancel hnR.ne', Real.rpow_one]
  apply le_of_pow_le_pow_left₀ hn.ne' (by positivity)
  rw [mul_pow, ← pow_mul, hroot]
  exact hminimum.trans (hsq'.trans (mul_le_mul_of_nonneg_right hdegrees hD))

private theorem sqrt_degree_le_discriminant_root
    {n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 1 ≤ D) :
    Real.sqrt n ≤ (n : ℝ) ^ 3 * D ^ (1 / (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt n ≤ (n : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Nat.cast_nonneg n)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith
  have hcube : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hn1 (by omega : 1 ≤ 3)
  have hroot : 1 ≤ D ^ (1 / (n : ℝ)) := Real.one_le_rpow hD (by positivity)
  exact (hsqrt.trans hcube).trans
    (by simpa using mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ (n : ℝ) ^ 3))

end
end CCDN

namespace CCDN
noncomputable section
open Module MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- If `δ > 0` bounds the norms of nonzero lattice vectors from below, then a prescribed greedy
lattice basis with first vector `w` satisfies
`∏ i, ‖b i‖ ≤ (‖w‖ / δ) * (n + 1) ^ (n + 1) * covol(L)`. -/
theorem prescribed_greedy_lattice_basis_product_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {n : ℕ} {w : E} (b : Basis (Fin (n + 1)) ℝ E)
    (hb : IsPrescribedGreedyLatticeFamily L w b)
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ x, x ∈ L → x ≠ 0 → δ ≤ ‖x‖) :
    (∏ i, ‖b i‖) ≤ (‖w‖ / δ) * (n + 1 : ℝ) ^ (n + 1) * ZLattice.covolume L := by
  obtain ⟨c, hflag⟩ := exists_orthonormal_basis_with_same_flag b
  have hprod := lattice_flag_minima_product_le (by omega : 0 < n + 1) L c
    (prescribedLatticeMinima b δ) (hb.minima_pos hδ) (hb.minima_mono hlower)
    (fun i x hx hxU => hb.minima_outside hlower i x hx (by rwa [← hflag i]))
  rw [prescribedLatticeMinima_prod b hb.first_eq hδ.ne']
  have hh := mul_le_mul_of_nonneg_left hprod (div_nonneg (norm_nonneg w) hδ.le)
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hh

end
end CCDN

namespace CCDN
noncomputable section
open Module NumberField
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

open Classical in
private theorem euclidean_prescribed_basis_last_minimum_pow
    {n : ℕ} (b : Basis (Fin (n + 2)) ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : IsPrescribedGreedyLatticeFamily (mixedEmbedding.euclidean.integerLattice K)
      (euclideanNumberFieldEmbedding K 1) b) :
    ‖b (Fin.last (n + 1))‖ ^ (n + 2) ≤ (∏ i, ‖b i‖) ^ 2 := by
  classical
  obtain ⟨v, q, hq, hmap⟩ :=
    exists_field_basis_of_euclidean_lattice_basis K b hb.mem
  have hpq : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro he
    have := congrArg Fin.val he
    simp at this
  have hq0 : q 0 = 1 := by
    apply euclideanNumberFieldEmbedding_injective K
    rw [hmap, hb.first_eq]
  have hunit : 1 ≤ ‖euclideanNumberFieldEmbedding K (q 0)‖ := by
    rw [hq0]
    exact one_le_euclidean_norm_integer K (x := 1) one_ne_zero
  have hmin (i j : {i : Fin (n + 2) // i ≠ 0 ∧ i ≠ Fin.last (n + 1)})
      (hij : q.coord (Fin.last (n + 1)) (q i * q j) ≠ 0) :
      ‖euclideanNumberFieldEmbedding K (q (Fin.last (n + 1)))‖ ≤
        ‖euclideanNumberFieldEmbedding K (q i * q j)‖ := by
    rw [hmap]
    apply hb.norm_le hpq.symm
    · simpa only [hq, RingOfIntegers.coe_eq_algebraMap, map_mul] using
        euclideanNumberFieldEmbedding_mem_integerLattice K (v i * v j)
    · exact euclidean_notMem_basis_span_of_coordinate_ne_zero K b q hmap hij
        (by simp)
  have hh := field_basis_multiplication_minimum_product q 0 (Fin.last (n + 1))
    hpq hq0 (fun x => ‖euclideanNumberFieldEmbedding K x‖) (fun _ => norm_nonneg _)
    (euclideanNumberFieldEmbedding_norm_mul_le K) hunit hmin
  simpa only [Fintype.card_fin, hmap] using hh

open Classical in
private theorem exists_numberField_short_basis_of_degree
    (n : ℕ) (hn : Module.finrank ℚ K = n + 2) :
    ∃ b : Basis (Fin (n + 2)) ℝ (mixedEmbedding.euclidean.mixedSpace K),
      (∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) ∧
      ∀ i, ‖b i‖ ≤ (n + 2 : ℝ) ^ 3 * |(discr K : ℝ)| ^ (1 / (n + 2 : ℝ)) := by
  classical
  let L := mixedEmbedding.euclidean.integerLattice K
  let w := euclideanNumberFieldEmbedding K 1
  have hw : w ∈ L := euclideanNumberFieldEmbedding_mem_integerLattice K 1
  have hw0 : w ≠ 0 := by
    exact (map_ne_zero (euclideanNumberFieldEmbedding K)).mpr one_ne_zero
  have hdim : Module.finrank ℝ (mixedEmbedding.euclidean.mixedSpace K) = (n + 1) + 1 := by
    rw [mixedEmbedding.euclidean.finrank, hn]
  obtain ⟨b, hb⟩ := exists_prescribed_greedy_lattice_basis L w hw hw0 hdim
  have hprod := prescribed_greedy_lattice_basis_product_le L b hb
    (by norm_num : (0 : ℝ) < 1)
    (fun x hx hx0 => one_le_euclidean_integerLattice_norm K hx hx0)
  have hD : 1 ≤ |(discr K : ℝ)| := by
    have hz : (0 : ℤ) < |discr K| := abs_pos.mpr (discr_ne_zero K)
    have hz' : (1 : ℤ) ≤ |discr K| := by omega
    exact_mod_cast hz'
  have hcov : ZLattice.covolume L ≤ Real.sqrt |(discr K : ℝ)| := by
    change ZLattice.covolume (mixedEmbedding.euclidean.integerLattice K) ≤ _
    rw [euclidean_integerLattice_covolume]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _)
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hwbound : ‖w‖ ≤ Real.sqrt (n + 2 : ℕ) := by
    simpa only [hn] using euclideanNumberFieldEmbedding_one_norm_le K
  have hprod' : (∏ i, ‖b i‖) ≤
      Real.sqrt (n + 2 : ℕ) * ((n + 2 : ℕ) : ℝ) ^ (n + 2) *
        Real.sqrt |(discr K : ℝ)| := by
    have hp : (∏ i, ‖b i‖) ≤
        ‖w‖ * ((n + 2 : ℕ) : ℝ) ^ (n + 2) * ZLattice.covolume L := by
      simpa only [div_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        show n + 1 + 1 = n + 2 by omega, show (n : ℝ) + 1 + 1 = n + 2 by ring]
        using hprod
    exact hp.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hwbound (by positivity)) hcov
      (ZLattice.covolume_pos L _).le (by positivity))
  have hlast : ‖b (Fin.last (n + 1))‖ ≤
      (n + 2 : ℝ) ^ 3 * |(discr K : ℝ)| ^ (1 / (n + 2 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      largest_minimum_le_discriminant_root (n := n + 2) (by omega)
        (Finset.prod_nonneg (fun i _ => norm_nonneg (b i))) (abs_nonneg _)
        (euclidean_prescribed_basis_last_minimum_pow K b hb) hprod'
  refine ⟨b, hb.mem, ?_⟩
  intro i
  by_cases hi : i = 0
  · rw [hi, hb.first_eq]
    apply hwbound.trans
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      sqrt_degree_le_discriminant_root (n := n + 2) (by omega) hD
  · apply (hb.norm_le hi (hb.mem _)
      (b.linearIndependent.notMem_span_image (not_lt_of_ge (Fin.le_last i)))).trans hlast

open Classical in
/-- A real basis of integral lattice vectors with an explicit
constant depending only on the field degree. -/
theorem exists_numberField_short_basis
    (hd : 2 ≤ Module.finrank ℚ K) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℝ (mixedEmbedding.euclidean.mixedSpace K),
      (∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) ∧
      ∀ i, ‖b i‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 *
        |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank ℚ K = n + 2 :=
    ⟨Module.finrank ℚ K - 2, by omega⟩
  rw [hn]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    exists_numberField_short_basis_of_degree K n hn

end
end CCDN
