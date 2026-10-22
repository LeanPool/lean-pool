/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection
import LeanPool.CCDN.Algebra.PointSeparation
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! A proper section bounds independent classes in any algebra-valued image,
not only distinct point evaluations. This is the multiplicity-ready form of
the Hilbert-function argument. -/

@[expose] public section
namespace CCDN
noncomputable section

private lemma section_image_filtered_lower {K B σ ι : Type*} [Field K]
    [CommRing B] [Algebra K B] [Finite σ] [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (φ : (MvPolynomial σ K ⧸ p) →ₐ[K] B)
    (h : ι → MvPolynomial σ K)
    (hlin : LinearIndependent K (fun i => φ ((Ideal.Quotient.mk p) (h i))))
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (hzero : φ ((Ideal.Quotient.mk p) l) = 0) :
    ∃ D : ℕ, ∀ N : ℕ,
      Fintype.card ι * (N + 1) ≤ Module.finrank K (filteredCoordinateSpace p (D + m * N)) := by
  classical
  let := Fintype.ofFinite σ
  let D := Finset.univ.sup (fun i => (h i).totalDegree)
  refine ⟨D, ?_⟩
  intro N
  have hli := section_powers_independent φ (fun i => (Ideal.Quotient.mk p) (h i)) hlin
    ((Ideal.Quotient.mk p) l) (fun hzero => hl (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
    hzero (N + 1)
  have hmem (t : ι × Fin (N + 1)) :
      (Ideal.Quotient.mk p) (h t.1) * ((Ideal.Quotient.mk p) l) ^ t.2.val ∈
        filteredCoordinateSpace p (D + m * N) := by
    apply Submodule.mem_map.mpr
    refine ⟨h t.1 * l ^ t.2.val, ?_, by simp⟩
    rw [MvPolynomial.mem_restrictTotalDegree]
    have hh : (h t.1).totalDegree ≤ D :=
      Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ t.1)
    have hp : (l ^ t.2.val).totalDegree ≤ m * N :=
      (MvPolynomial.totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left _ hld).trans (by nlinarith [t.2.isLt]))
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hh hp)
  let v : ι × Fin (N + 1) → filteredCoordinateSpace p (D + m * N) :=
    fun t => ⟨(Ideal.Quotient.mk p) (h t.1) * ((Ideal.Quotient.mk p) l) ^ t.2.val, hmem t⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace p (D + m * N)).subtype hli
  simpa using hv.fintype_card_le_finrank

/-- Independent polynomial images in a proper section number at most d*m.
This applies to truncated local expansions as well as to point values. -/
theorem section_image_rank_le {K B σ ι : Type*} [Field K]
    [CommRing B] [Algebra K B] [Finite σ] [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (d : ℕ) (hdegree : HasFilteredCurveDegree p d)
    (φ : (MvPolynomial σ K ⧸ p) →ₐ[K] B) (h : ι → MvPolynomial σ K)
    (hlin : LinearIndependent K (fun i => φ ((Ideal.Quotient.mk p) (h i))))
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (hzero : φ ((Ideal.Quotient.mk p) l) = 0) : Fintype.card ι ≤ d * m := by
  classical
  let := Fintype.ofFinite σ
  by_cases hm : m = 0
  · have hlC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (show l.totalDegree = 0 by omega)
    have hc : l.coeff 0 ≠ 0 := by
      intro he
      apply hl
      rw [hlC, he, map_zero]
      exact p.zero_mem
    have hu : IsUnit l := hlC ▸ (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
    have hz : IsUnit (0 : B) := hzero ▸ ((hu.map (Ideal.Quotient.mk p)).map φ.toRingHom)
    let : Subsingleton B := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hz)
    have hn := hlin.fintype_card_le_finrank
    simpa only [Module.finrank_zero_of_subsingleton, hm, Nat.mul_zero] using hn
  obtain ⟨D, hD⟩ := section_image_filtered_lower p φ h hlin l hl m hld hzero
  exact hdegree.le_mul_of_growth (Nat.pos_of_ne_zero hm) hD

end
end CCDN
