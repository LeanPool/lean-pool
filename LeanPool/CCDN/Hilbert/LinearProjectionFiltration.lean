/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! Linear coordinate substitutions preserve the total-degree filtration.
Their image coordinate rings inject into the original filtered ring. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Substituting polynomials of total degree at most `m` multiplies the total degree by at most `m`.
-/
lemma aeval_totalDegree_le {K σ τ : Type*} [Field K] [Finite σ]
    (a : σ → MvPolynomial τ K) {m : ℕ} (ha : ∀ i, (a i).totalDegree ≤ m)
    (f : MvPolynomial σ K) : (aeval a f).totalDegree ≤ m * f.totalDegree := by
  classical
  let := Fintype.ofFinite σ
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [aeval_monomial]
  change (C (f.coeff e) * e.prod (fun i k => a i ^ k)).totalDegree ≤ _
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add, Finsupp.prod_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ i, (a i ^ e i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i, e i * m := Finset.sum_le_sum (fun i _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (ha i)))
    _ = m * e.sum (fun _ k => k) := by
      rw [← Finset.sum_mul, Finsupp.sum_fintype _ _ (by simp), Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left m (le_totalDegree he)

/-- The map from projection coordinates to the original coordinate ring. -/
def projectionCoordinateMap {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K) :
    MvPolynomial σ K →ₐ[K] (MvPolynomial τ K ⧸ I) :=
  (Ideal.Quotient.mkₐ K I).comp (aeval a)

/-- A linear coordinate substitution maps polynomials of total degree at most `M` into the filtered
piece of degree `M` of the coordinate ring. -/
lemma projectionCoordinateMap_filtered {K σ τ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) {M : ℕ}
    (f : MvPolynomial σ K) (hf : f.totalDegree ≤ M) :
    projectionCoordinateMap I a f ∈ filteredCoordinateSpace I M := by
  classical
  let := Fintype.ofFinite σ
  apply Submodule.mem_map.mpr
  refine ⟨aeval a f, ?_, rfl⟩
  rw [mem_restrictTotalDegree]
  exact (aeval_totalDegree_le a ha f).trans (by simpa using hf)

/-- Linear projection cannot increase any filtered coordinate-ring dimension. -/
theorem linear_projection_filtered_finrank_le {K σ τ : Type*} [Field K]
    [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (M : ℕ) :
    Module.finrank K (filteredCoordinateSpace (RingHom.ker (projectionCoordinateMap I a)) M) ≤
      Module.finrank K (filteredCoordinateSpace I M) := by
  classical
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite τ
  let ψ := projectionCoordinateMap I a
  let φ := Ideal.kerLiftAlg ψ
  let V := filteredCoordinateSpace (RingHom.ker ψ) M
  have hmem (v : V) : φ v.val ∈ filteredCoordinateSpace I M := by
    obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp v.property
    change (Ideal.Quotient.mk (RingHom.ker ψ)) f = v.val at he
    rw [← he]
    exact projectionCoordinateMap_filtered I a ha f ((mem_restrictTotalDegree _ _ _).mp hf)
  let T : V →ₗ[K] filteredCoordinateSpace I M :=
    (φ.toLinearMap.comp V.subtype).codRestrict _ hmem
  have hi : Function.Injective T := by
    intro x y h
    apply Subtype.ext
    apply Ideal.kerLiftAlg_injective ψ
    exact congrArg Subtype.val h
  exact LinearMap.finrank_le_finrank_of_injective hi

end
end CCDN
