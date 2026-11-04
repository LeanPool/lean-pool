/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.SingularTangent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset

/-!
Finite-precision generation of hypersurface local quotients.
Generator counts equal the layer dimensions; for plane curves each
weight needs at most μ generators.

Homogeneous generators lifted from the origin-adic layers of a
plane equation, with the number at every weight bounded by its multiplicity.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

/-- A basis of the graded layer lifts to homogeneous polynomials and
reduces every element of the ideal power modulo the equation and the next power. -/
private theorem exists_originLayer_generators {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (k : ℕ) :
    ∃ (r : ℕ) (g : Fin r → MvPolynomial (Fin (n + 1)) K),
      r = Module.finrank K (originLayer f k) ∧
      (∀ j, (g j).IsHomogeneous k) ∧
      ∀ u ∈ idealOfVars (Fin (n + 1)) K ^ k, ∃ c : Fin r → K,
        u - ∑ j, c j • g j ∈ originTruncationIdeal f k := by
  classical
  let b := Module.finBasis K (originLayer f k)
  let φ := (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap
  have hlift : ∀ j, ∃ g : MvPolynomial (Fin (n + 1)) K,
      g.IsHomogeneous k ∧ φ g = (b j).val := by
    intro j
    have hmem := (b j).property
    have hmem' : (b j).val ∈ homogeneousCoordinateSpace (originTruncationIdeal f k) k :=
      (originLayer_eq_homogeneousCoordinateSpace f k).le hmem
    exact Submodule.mem_map.mp hmem'
  choose g hg he using hlift
  refine ⟨Module.finrank K (originLayer f k), g, rfl, hg, ?_⟩
  intro u hu
  let ubar : originLayer f k := ⟨φ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩⟩
  refine ⟨fun j => b.repr ubar j, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change φ (u - ∑ j, b.repr ubar j • g j) = 0
  rw [map_sub, map_sum]
  simp only [map_smul, he]
  apply sub_eq_zero.mpr
  have hsum := congrArg Subtype.val (b.sum_repr ubar)
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using hsum.symm

/-- The singular multiplicity gives homogeneous local generators at
all weights, with at most μ generators at each weight. -/
private theorem exists_plane_origin_generators {K : Type*} [Field K] {μ : ℕ}
    (f : MvPolynomial (Fin 2) K) (hf : f ∈ idealOfVars (Fin 2) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin 2) K),
      (∀ k, r k ≤ μ) ∧ (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ k u, u ∈ idealOfVars (Fin 2) K ^ k → ∃ c : Fin (r k) → K,
        u - ∑ j, c j • g k j ∈ originTruncationIdeal f k := by
  classical
  choose r g hr hg hspan using fun k => exists_originLayer_generators (n := 1) f k
  refine ⟨r, g, ?_, hg, hspan⟩
  intro k
  rw [hr]
  exact plane_originLayer_finrank_le_multiplicity f hf hμ

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Successive layer reductions assemble into a finite-precision
polynomial representation, modulo the defining equation and the Nth origin power. -/
private lemma origin_layers_generate_truncation {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (r : ℕ → ℕ)
    (g : (k : ℕ) → Fin (r k) → MvPolynomial σ K)
    (hspan : ∀ k u, u ∈ idealOfVars σ K ^ k → ∃ c : Fin (r k) → K,
      u - ∑ j, c j • g k j ∈ originTruncationIdeal f k)
    (N : ℕ) (u : MvPolynomial σ K) :
    ∃ c : (k : Fin N) → Fin (r k.val) → K,
      u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈ Ideal.span {f} ⊔ idealOfVars σ K ^ N := by
  induction N with
  | zero =>
    refine ⟨fun k => Fin.elim0 k, ?_⟩
    simp
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨p, hp, q, hq, he⟩ := Submodule.mem_sup.mp hc
    obtain ⟨b, hb⟩ := hspan N q hq
    let c' : (k : Fin (N + 1)) → Fin (r k.val) → K := Fin.lastCases b c
    refine ⟨c', ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [c', Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last]
    have hp' : p ∈ Ideal.span {f} ⊔ idealOfVars σ K ^ (N + 1) := Submodule.mem_sup_left hp
    have hadd := (Ideal.span {f} ⊔ idealOfVars σ K ^ (N + 1)).add_mem hp' hb
    convert hadd using 1
    linear_combination -he

/-- In every ambient dimension, the numbers of homogeneous generators are
exactly the dimensions of the origin-adic layers. -/
theorem exists_origin_truncation_generators {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin (n + 1)) K),
      (∀ k, r k = Module.finrank K (originLayer f k)) ∧
      (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (r k.val) → K,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈
          Ideal.span {f} ⊔ idealOfVars (Fin (n + 1)) K ^ N := by
  classical
  choose r g hr hg hs using fun k => exists_originLayer_generators f k
  exact ⟨r, g, hr, hg, origin_layers_generate_truncation f r g hs⟩

/-- Finite-precision weighted generators for any plane equation of
multiplicity μ. -/
theorem exists_plane_truncation_generators {K : Type*} [Field K] {μ : ℕ}
    (f : MvPolynomial (Fin 2) K) (hf : f ∈ idealOfVars (Fin 2) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin 2) K),
      (∀ k, r k ≤ μ) ∧ (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (r k.val) → K,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈
          Ideal.span {f} ⊔ idealOfVars (Fin 2) K ^ N := by
  obtain ⟨r, g, hr, hg, hs⟩ := exists_plane_origin_generators f hf hμ
  exact ⟨r, g, hr, hg, origin_layers_generate_truncation f r g hs⟩

end
end CCDN
