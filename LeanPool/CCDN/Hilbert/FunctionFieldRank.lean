/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Algebraic.Basic

/-! Hilbert degree controls function-field rank over a transcendental linear
coordinate. Independent functions over the parameter field produce independent
blocks over the constant field, whose filtered growth bounds their number. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- In a tower `K → R → F`, the products `u k • v i` of a family `v` independent over `R` and a
family `u` independent over `K` are independent over `K`. -/
lemma tower_smul_independent {K R F ι κ : Type*} [Field K] [Field R] [Field F]
    [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [Finite ι] [Finite κ]
    (v : ι → F) (hv : LinearIndependent R v)
    (u : κ → R) (hu : LinearIndependent K u) :
    LinearIndependent K (fun t : ι × κ => u t.2 • v t.1) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff]
  intro c hc t
  have he : ∑ i, (∑ k, c (i, k) • u k) • v i = 0 := by
    simpa only [Fintype.sum_prod_type, Finset.sum_smul, smul_assoc] using hc
  have hz := Fintype.linearIndependent_iff.mp hv _ he t.1
  exact Fintype.linearIndependent_iff.mp hu (fun k => c (t.1, k)) hz t.2

/-- The powers `1, u, …, u ^ (N - 1)` of a transcendental element `u` are linearly independent. -/
lemma transcendental_powers_independent {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (u : R) (hu : Transcendental K u) (N : ℕ) :
    LinearIndependent K (fun i : Fin N => u ^ i.val) := by
  have hb := (Polynomial.basisMonomials K).linearIndependent.map'
    (Polynomial.aeval u).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hu))
  have hh := hb.comp (fun i : Fin N => i.val) Fin.val_injective
  simpa only [Function.comp_def, Polynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
    Polynomial.aeval_monomial, map_one, one_mul] using hh

/-- A finite family of polynomial classes independent over a parameter field
has cardinality at most the affine Hilbert degree. -/
theorem polynomial_parameter_rank_le {K R F σ ι : Type*} [Field K] [Field R] [Field F]
    [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [Finite σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d)
    (φ : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K) (hl : l.totalDegree ≤ 1)
    (u : R) (hu : Transcendental K u)
    (he : φ ((Ideal.Quotient.mk I) l) = algebraMap R F u)
    (h : ι → MvPolynomial σ K)
    (hi : LinearIndependent R (fun i => φ ((Ideal.Quotient.mk I) (h i)))) :
    Fintype.card ι ≤ d := by
  classical
  let := Fintype.ofFinite σ
  let D := Finset.univ.sup (fun i => (h i).totalDegree)
  have hlow (N : ℕ) : Fintype.card ι * (N + 1) ≤
      Module.finrank K (filteredCoordinateSpace I (D + N)) := by
    let v : ι × Fin (N + 1) → filteredCoordinateSpace I (D + N) := fun t =>
      ⟨(Ideal.Quotient.mk I) (h t.1 * l ^ t.2.val), by
        apply Submodule.mem_map.mpr
        refine ⟨_, ?_, rfl⟩
        rw [MvPolynomial.mem_restrictTotalDegree]
        have hh : (h t.1).totalDegree ≤ D :=
          Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ t.1)
        have hp := MvPolynomial.totalDegree_pow l t.2.val
        have hh' := MvPolynomial.totalDegree_mul (h t.1) (l ^ t.2.val)
        have hm := Nat.mul_le_mul_left t.2.val hl
        nlinarith [t.2.isLt]⟩
    have hli : LinearIndependent K (fun t => φ (v t).val) := by
      have hprod := tower_smul_independent _ hi (fun k : Fin (N + 1) => u ^ k.val)
        (transcendental_powers_independent u hu (N + 1))
      convert hprod using 1
      funext t
      simp only [v, map_mul, map_pow, he, Algebra.smul_def]
      rw [mul_comm]
    have hv : LinearIndependent K v :=
      LinearIndependent.of_comp (φ.toLinearMap.comp (filteredCoordinateSpace I (D + N)).subtype) hli
    simpa only [Fintype.card_prod, Fintype.card_fin] using hv.fintype_card_le_finrank
  obtain ⟨N₀, c, hN₀⟩ := hdegree
  by_contra hbad
  have hcard : d + 1 ≤ Fintype.card ι := by omega
  let N := d * D + c.natAbs + N₀ + 1
  have hn0 : N₀ ≤ D + N := by dsimp [N]; omega
  have heq := hN₀ (D + N) hn0
  push_cast at heq
  have hlo : (Fintype.card ι : ℤ) * (N + 1) ≤ (d : ℤ) * (D + N) + c := by
    rw [← heq]
    exact_mod_cast hlow N
  have hmul : ((d : ℤ) + 1) * (N + 1) ≤ (Fintype.card ι : ℤ) * (N + 1) := by
    exact_mod_cast Nat.mul_le_mul_right (N + 1) hcard
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = d * D + c.natAbs + N₀ + 1 := by simp [N]
  nlinarith

end
end CCDN
