/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.NumberFieldEuclideanLattice

/-! A real basis of integral lattice vectors gives a rational
number-field basis. Its real coordinates on embedded field elements are
the corresponding rational coordinates, so missing-span conditions
transfer without any rationality assumption on a real linear relation. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module NumberField
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- A real basis `b` of the Euclidean mixed space consisting of vectors of the integer lattice comes
from a `ℚ`-basis `q` of `K` consisting of algebraic integers `v i`, with
`euclideanNumberFieldEmbedding K (q i) = b i`. -/
theorem exists_field_basis_of_euclidean_lattice_basis
    {ι : Type*} [Finite ι]
    (b : Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : ∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) :
    ∃ (v : ι → 𝓞 K) (q : Basis ι ℚ K),
      (∀ i, q i = (v i : K)) ∧
      ∀ i, euclideanNumberFieldEmbedding K (q i) = b i := by
  classical
  let := Fintype.ofFinite ι
  have hv (i) := (mem_euclidean_integerLattice_iff K (b i)).mp (hb i)
  choose v hv using hv
  have hi : LinearIndependent ℚ (fun i => (v i : K)) := by
    apply LinearIndependent.of_comp (euclideanNumberFieldLinearMap K)
    simpa only [Function.comp_def, euclideanNumberFieldLinearMap_apply, hv] using
      b.linearIndependent.restrict_scalars' ℚ
  have hcard : Fintype.card ι = Module.finrank ℚ K :=
    (Module.finrank_eq_card_basis b).symm.trans (mixedEmbedding.euclidean.finrank K)
  let q := basisOfLinearIndependentOfCardEqFinrank' (fun i => (v i : K)) hi hcard
  have hq (i) : q i = (v i : K) :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ hi hcard) i
  exact ⟨v, q, hq, fun i => (congrArg (euclideanNumberFieldEmbedding K) (hq i)).trans (hv i)⟩

private theorem euclidean_field_basis_repr
    {ι : Type*} [Finite ι]
    (b : Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K)) (q : Basis ι ℚ K)
    (hmap : ∀ i, euclideanNumberFieldEmbedding K (q i) = b i) (x : K) (i : ι) :
    b.repr (euclideanNumberFieldEmbedding K x) i = (q.repr x i : ℝ) := by
  classical
  let := Fintype.ofFinite ι
  have hmaps :
      ((b.coord i).restrictScalars ℚ).comp (euclideanNumberFieldLinearMap K) =
        (Algebra.linearMap ℚ ℝ).comp (q.coord i) := by
    apply q.ext
    intro j
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      euclideanNumberFieldLinearMap_apply, hmap, Basis.coord_apply, Basis.repr_self]
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  exact congrArg (fun f => f x) hmaps

/-- If the real basis `b` is the image of the rational basis `q` and the `i`-th `q`-coordinate of
`x : K` is nonzero, then the embedding of `x` does not lie in the real span of `b '' S` for any
`S` not containing `i`. -/
theorem euclidean_notMem_basis_span_of_coordinate_ne_zero
    {ι : Type*} [Finite ι]
    (b : Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K)) (q : Basis ι ℚ K)
    (hmap : ∀ i, euclideanNumberFieldEmbedding K (q i) = b i)
    {x : K} {i : ι} (hi : q.repr x i ≠ 0)
    {S : Set ι} (hiS : i ∉ S) :
    euclideanNumberFieldEmbedding K x ∉ Submodule.span ℝ (b '' S) := by
  classical
  let := Fintype.ofFinite ι
  intro h
  have hs := b.repr_support_subset_of_mem_span S h
  apply hiS
  apply hs
  apply Finsupp.mem_support_iff.mpr
  rw [euclidean_field_basis_repr K b q hmap]
  exact_mod_cast hi

end
end CCDN
