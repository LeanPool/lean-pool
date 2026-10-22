/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Hilbert.FilteredIntersection
import LeanPool.CCDN.Algebra.PointSeparation
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! A sharp affine curve intersection bound from the Hilbert function.
Bounds intersections with arbitrary section polynomials. No projective intersection theorem or
point-counting axiom is used. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Distinct points in a proper polynomial section force a corresponding lower
bound for the filtered coordinate-space growth. -/
private theorem polynomial_points_filtered_lower {K σ ι : Type*} [Field K] [Finite σ]
    [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ idealZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    ∃ D : ℕ, ∀ N : ℕ,
      Fintype.card ι * (N + 1) ≤ Module.finrank K (filteredCoordinateSpace p (D + m * N)) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨h, hsep⟩ := exists_point_separators z hz
  let φ : ι → (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
    fun i => Ideal.Quotient.liftₐ p (MvPolynomial.aeval (z i)) (by
      intro f hf
      simpa only [MvPolynomial.aeval_eq_eval] using hzp i f hf)
  have hφ (i : ι) (f : MvPolynomial σ K) :
      φ i ((Ideal.Quotient.mk p) f) = MvPolynomial.eval (z i) f := by
    simp [φ, Ideal.Quotient.liftₐ_apply]
  let D := Finset.univ.sup (fun i => (h i).totalDegree)
  refine ⟨D, ?_⟩
  intro N
  have hlin := separator_powers_independent φ (fun i => (Ideal.Quotient.mk p) (h i))
    ((Ideal.Quotient.mk p) l) (fun hzero => hl (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
    (fun i => by rw [hφ]; exact hzl i)
    (fun i j => by rw [hφ]; exact hsep i j) (N + 1)
  have hmem (t : ι × Fin (N + 1)) :
      (Ideal.Quotient.mk p) (h t.1) * ((Ideal.Quotient.mk p) l) ^ t.2.val ∈
        filteredCoordinateSpace p (D + m * N) := by
    apply Submodule.mem_map.mpr
    refine ⟨h t.1 * l ^ t.2.val, ?_, by simp⟩
    rw [MvPolynomial.mem_restrictTotalDegree]
    have hh : (h t.1).totalDegree ≤ D  :=
      Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ t.1)
    have hp : (l ^ t.2.val).totalDegree ≤ m * N :=
      (MvPolynomial.totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left _ hld).trans (by nlinarith [t.2.isLt]))
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hh hp)
  let v : ι × Fin (N + 1) → filteredCoordinateSpace p (D + m * N) :=
    fun t => ⟨(Ideal.Quotient.mk p) (h t.1) * ((Ideal.Quotient.mk p) l) ^ t.2.val, hmem t⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace p (D + m * N)).subtype hlin
  simpa using hv.fintype_card_le_finrank

/-- A proper polynomial section of a prime curve contains at most the product
of the curve's affine Hilbert degree and the section degree many distinct points. -/
theorem polynomial_section_card_le_degree {K σ ι : Type*} [Field K] [Finite σ]
    [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (d : ℕ)
    (hdegree : HasFilteredCurveDegree p d)
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ idealZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    Fintype.card ι ≤ d * m := by
  classical
  let := Fintype.ofFinite σ
  by_cases hm : m = 0
  · have hd0 : l.totalDegree = 0 := by omega
    have hlC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd0
    let : IsEmpty ι := ⟨fun i => by
      have he := hzl i
      rw [hlC, MvPolynomial.eval_C] at he
      apply hl
      rw [hlC, he, map_zero]
      exact p.zero_mem⟩
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _
  obtain ⟨D, hD⟩ := polynomial_points_filtered_lower p l hl m hld z hz hzp hzl
  obtain ⟨N₀, c, hN₀⟩ := hdegree
  by_contra h
  have hcard : d * m + 1 ≤ Fintype.card ι := by omega
  let N := d * D + c.natAbs + N₀ + 1
  have hlow := hD N
  have he := hN₀ (D + m * N) (by
    have hN : N₀ ≤ N := by dsimp [N]; omega
    have hm1 : 1 ≤ m := by omega
    nlinarith)
  push_cast at he
  have hlo : ((Fintype.card ι : ℕ) : ℤ) * (N + 1) ≤ (d : ℤ) * (D + m * N) + c := by
    rw [← he]
    exact_mod_cast hlow
  have hmul : ((d : ℤ) * m + 1) * (N + 1) ≤ (Fintype.card ι : ℤ) * (N + 1) := by
    exact_mod_cast Nat.mul_le_mul_right (N + 1) hcard
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = d * D + c.natAbs + N₀ + 1 := by simp [N]
  nlinarith

end
end CCDN
