/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-! The ring-of-integers lattice in the Euclidean mixed embedding.
The real and imaginary coordinates are unweighted; the covolume is
`2^(-r₂) √|D|`. All norm comparisons below have constants depending only
on the degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory
open scoped NNReal

variable (K : Type*) [Field K] [NumberField K]

/-- The mixed embedding with its Euclidean, rather than supremum, norm. -/
def euclideanNumberFieldEmbedding : K →+* mixedEmbedding.euclidean.mixedSpace K where
  toFun x := (mixedEmbedding.euclidean.toMixed K).symm (mixedEmbedding K x)
  map_zero' := by simp
  map_one' := by rw [map_one]; rfl
  map_add' x y := by simp
  map_mul' x y := by
    change (mixedEmbedding.euclidean.toMixed K).symm (mixedEmbedding K (x * y)) = _
    rw [map_mul]
    rfl

/-- Transporting the Euclidean embedding of `x` back to the mixed space gives the mixed embedding
of `x`. -/
@[simp] lemma toMixed_euclideanNumberFieldEmbedding (x : K) :
    mixedEmbedding.euclidean.toMixed K (euclideanNumberFieldEmbedding K x) =
      mixedEmbedding K x :=
  (mixedEmbedding.euclidean.toMixed K).apply_symm_apply _

/-- The Euclidean mixed embedding of a number field is injective. -/
lemma euclideanNumberFieldEmbedding_injective :
    Function.Injective (euclideanNumberFieldEmbedding K) :=
  (mixedEmbedding.euclidean.toMixed K).symm.injective.comp
    (mixedEmbedding_injective (K := K))

/-- The Euclidean mixed embedding of `K`, as a `ℚ`-linear map. -/
def euclideanNumberFieldLinearMap :
    K →ₗ[ℚ] mixedEmbedding.euclidean.mixedSpace K :=
  ((mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.restrictScalars ℚ).comp
    (mixedEmbedding K).toRatAlgHom.toLinearMap

/-- The `ℚ`-linear Euclidean embedding agrees with `euclideanNumberFieldEmbedding`. -/
@[simp] lemma euclideanNumberFieldLinearMap_apply (x : K) :
    euclideanNumberFieldLinearMap K x = euclideanNumberFieldEmbedding K x := rfl

/-- The Euclidean embedding of an algebraic integer lies in the Euclidean integer lattice. -/
lemma euclideanNumberFieldEmbedding_mem_integerLattice (x : 𝓞 K) :
    euclideanNumberFieldEmbedding K (x : K) ∈ mixedEmbedding.euclidean.integerLattice K := by
  change mixedEmbedding.euclidean.toMixed K (euclideanNumberFieldEmbedding K (x : K)) ∈
    mixedEmbedding.integerLattice K
  rw [toMixed_euclideanNumberFieldEmbedding]
  exact ⟨x, rfl⟩

/-- A vector lies in the Euclidean integer lattice if and only if it is the Euclidean embedding of
an algebraic integer. -/
lemma mem_euclidean_integerLattice_iff
    (x : mixedEmbedding.euclidean.mixedSpace K) :
    x ∈ mixedEmbedding.euclidean.integerLattice K ↔
      ∃ z : 𝓞 K, euclideanNumberFieldEmbedding K (z : K) = x := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, (mixedEmbedding.euclidean.toMixed K).injective ?_⟩
    rw [toMixed_euclideanNumberFieldEmbedding]
    exact hz
  · rintro ⟨z, rfl⟩
    exact euclideanNumberFieldEmbedding_mem_integerLattice K z

open Classical in
private lemma infinitePlace_le_euclidean_norm (w : InfinitePlace K) (x : K) :
    w x ≤ ‖euclideanNumberFieldEmbedding K x‖ := by
  rw [← mixedEmbedding.normAtPlace_apply w x,
    ← toMixed_euclideanNumberFieldEmbedding]
  rcases isReal_or_isComplex w with hw | hw
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
    exact (PiLp.norm_apply_le (euclideanNumberFieldEmbedding K x).fst ⟨w, hw⟩).trans
      (WithLp.norm_fst_le _ (euclideanNumberFieldEmbedding K x))
  · rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw]
    exact (PiLp.norm_apply_le (euclideanNumberFieldEmbedding K x).snd ⟨w, hw⟩).trans
      (WithLp.norm_snd_le _ (euclideanNumberFieldEmbedding K x))

open Classical in
private lemma euclideanNumberFieldEmbedding_norm_sq (x : K) :
    ‖euclideanNumberFieldEmbedding K x‖ ^ 2 =
      (∑ w : {w : InfinitePlace K // IsReal w}, (w.val x) ^ 2) +
      (∑ w : {w : InfinitePlace K // IsComplex w}, (w.val x) ^ 2) := by
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    change ‖(mixedEmbedding K x).1 w‖ ^ 2 = _
    rw [mixedEmbedding.mixedEmbedding_apply_isReal, norm_embedding_of_isReal]
  · apply Finset.sum_congr rfl
    intro w _
    change ‖(mixedEmbedding K x).2 w‖ ^ 2 = _
    rw [mixedEmbedding.mixedEmbedding_apply_isComplex, norm_embedding_eq]

open Classical in
/-- The Euclidean embedding of a nonzero algebraic integer has norm at least `1`. -/
lemma one_le_euclidean_norm_integer {x : 𝓞 K} (hx : x ≠ 0) :
    1 ≤ ‖euclideanNumberFieldEmbedding K (x : K)‖ := by
  by_contra! h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have hw := InfinitePlace.one_le_of_lt_one (w := w) hx
    (fun _ _ ↦ (infinitePlace_le_euclidean_norm K _ (x : K)).trans_lt h)
  exact (hw.trans (infinitePlace_le_euclidean_norm K w (x : K))).not_gt h

open Classical in
/-- Every nonzero vector of the Euclidean integer lattice has norm at least `1`. -/
lemma one_le_euclidean_integerLattice_norm
    {x : mixedEmbedding.euclidean.mixedSpace K}
    (hx : x ∈ mixedEmbedding.euclidean.integerLattice K) (hne : x ≠ 0) :
    1 ≤ ‖x‖ := by
  obtain ⟨z, rfl⟩ := (mem_euclidean_integerLattice_iff K x).mp hx
  apply one_le_euclidean_norm_integer K
  intro hz
  apply hne
  simp [hz]

open Classical in
/-- If `w x ≤ B` at every infinite place `w`, then the Euclidean embedding of `x` has norm at most
`√[K : ℚ] * B`. -/
lemma euclideanNumberFieldEmbedding_norm_le {B : ℝ} (hB : 0 ≤ B)
    (x : K) (hx : ∀ w : InfinitePlace K, w x ≤ B) :
    ‖euclideanNumberFieldEmbedding K x‖ ≤ Real.sqrt (Module.finrank ℚ K) * B := by
  have hreal : (∑ w : {w : InfinitePlace K // IsReal w}, (w.val x) ^ 2) ≤
      nrRealPlaces K * B ^ 2 := by
    simpa using Finset.sum_le_sum (fun (w : {w : InfinitePlace K // IsReal w})
      (_ : w ∈ Finset.univ) ↦
      (sq_le_sq₀ (apply_nonneg w.val x) hB).mpr (hx w.val))
  have hcomplex : (∑ w : {w : InfinitePlace K // IsComplex w}, (w.val x) ^ 2) ≤
      nrComplexPlaces K * B ^ 2 := by
    simpa using Finset.sum_le_sum (fun (w : {w : InfinitePlace K // IsComplex w})
      (_ : w ∈ Finset.univ) ↦
      (sq_le_sq₀ (apply_nonneg w.val x) hB).mpr (hx w.val))
  have hrank : (nrRealPlaces K : ℝ) + 2 * nrComplexPlaces K = Module.finrank ℚ K := by
    exact_mod_cast card_add_two_mul_card_eq_rank K
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hB)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), euclideanNumberFieldEmbedding_norm_sq]
  nlinarith [congrArg (fun r : ℝ ↦ r * B ^ 2) hrank,
    mul_nonneg (Nat.cast_nonneg (nrComplexPlaces K) (α := ℝ)) (sq_nonneg B)]

open Classical in
/-- The Euclidean embedding of `1` has norm at most `√[K : ℚ]`. -/
lemma euclideanNumberFieldEmbedding_one_norm_le :
    ‖euclideanNumberFieldEmbedding K 1‖ ≤ Real.sqrt (Module.finrank ℚ K) := by
  simpa using euclideanNumberFieldEmbedding_norm_le K (B := 1) zero_le_one 1
    (fun w ↦ by simp)

open Classical in
/-- The Euclidean norm is submultiplicative on embedded field elements: the norm of the embedding of
`x * y` is at most the product of the norms of the embeddings of `x` and `y`. -/
lemma euclideanNumberFieldEmbedding_norm_mul_le (x y : K) :
    ‖euclideanNumberFieldEmbedding K (x * y)‖ ≤
      ‖euclideanNumberFieldEmbedding K x‖ * ‖euclideanNumberFieldEmbedding K y‖ := by
  have hp (w : InfinitePlace K) :
      (w (x * y)) ^ 2 ≤ (w x) ^ 2 * ‖euclideanNumberFieldEmbedding K y‖ ^ 2 := by
    rw [map_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (apply_nonneg w y) (norm_nonneg _)).mpr
        (infinitePlace_le_euclidean_norm K w y)) (sq_nonneg _)
  have hreal := Finset.sum_le_sum (fun w (_ : w ∈
      (Finset.univ : Finset {w : InfinitePlace K // IsReal w})) ↦ hp w.val)
  have hcomplex := Finset.sum_le_sum (fun w (_ : w ∈
      (Finset.univ : Finset {w : InfinitePlace K // IsComplex w})) ↦ hp w.val)
  rw [← Finset.sum_mul] at hreal hcomplex
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, euclideanNumberFieldEmbedding_norm_sq K (x * y),
    euclideanNumberFieldEmbedding_norm_sq K x]
  nlinarith only [hreal, hcomplex]

open Classical in
/-- The Euclidean integer lattice has covolume `2 ^ (-r₂) * √|discr K|`, where `r₂` is the number of
complex places of `K`. -/
lemma euclidean_integerLattice_covolume :
    ZLattice.covolume (mixedEmbedding.euclidean.integerLattice K) =
      (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| := by
  rw [mixedEmbedding.euclidean.integerLattice,
    ZLattice.covolume_comap (mixedEmbedding.integerLattice K) volume volume
      (mixedEmbedding.euclidean.volumePreserving_toMixed K),
    ZLattice.covolume_eq_measure_fundamentalDomain (mixedEmbedding.integerLattice K) volume
      (mixedEmbedding.fundamentalDomain_integerLattice K)]
  simp only [Measure.real, mixedEmbedding.volume_fundamentalDomain_latticeBasis,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]

end
end CCDN
