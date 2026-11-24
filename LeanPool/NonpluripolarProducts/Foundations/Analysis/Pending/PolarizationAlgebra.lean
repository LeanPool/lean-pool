/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Finite-sum algebra for polarizing mass identities

Pure combinatorial lemmas used to polarize mass identities:

* `sum_eq_zero_of_forall_nat_ge`: if a real "polynomial in `N`" `∑ g, N ^ k g * d g`
  vanishes for all large naturals `N`, then its constant coefficient
  `∑ g with k g = 0, d g` vanishes.
* `sum_powerset_signed_eq_sum_bijective`: inclusion–exclusion over the images of maps
  `Fin n → Fin n` isolates the bijective maps.
* `sum_bijective_eq_sum_perm`: bijective self-maps of `Fin n` are reindexed by
  permutations.
* `sum_powerset_signed_eq_factorial_mul`: the corollary when `d` is constant on
  permutations.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.Pending.PolarizationAlgebra

open Finset Polynomial

/-- If `∑ g, N ^ k g * d g = 0` for all naturals `N ≥ N₀`, then the constant
coefficient `∑ g with k g = 0, d g` vanishes. -/
theorem sum_eq_zero_of_forall_nat_ge {G : Type*} [Fintype G] (k : G → ℕ) (d : G → ℝ)
    (N₀ : ℕ) (h : ∀ N : ℕ, N₀ ≤ N → ∑ g, (N : ℝ) ^ k g * d g = 0) :
    ∑ g with k g = 0, d g = 0 := by
  classical
  set p : ℝ[X] := ∑ g, C (d g) * X ^ (k g) with hp
  have hroot : ∀ N : ℕ, N₀ ≤ N → p.IsRoot (N : ℝ) := by
    intro N hN
    simp only [IsRoot, hp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← h N hN]
    exact Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hinf : Set.Infinite {x | p.IsRoot x} := by
    have : Set.Infinite ((fun N : ℕ => (N : ℝ)) '' Set.Ici N₀) :=
      (Set.Ici_infinite N₀).image Nat.cast_injective.injOn
    refine this.mono ?_
    rintro _ ⟨N, hN, rfl⟩
    exact hroot N hN
  have hp0 : p = 0 := p.eq_zero_of_infinite_isRoot hinf
  have hc := congrArg (fun q : ℝ[X] => q.coeff 0) hp0
  simp only [hp, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_filter]
  refine (Finset.sum_congr rfl fun g _ => ?_).trans hc
  simp only [eq_comm]

/-- Inclusion–exclusion over the images of maps `Fin n → Fin n`. -/
theorem sum_powerset_signed_eq_sum_bijective {n : ℕ} (d : (Fin n → Fin n) → ℝ) :
    ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        ∑ g : Fin n → Fin n with ∀ j, g j ∈ S, d g =
      ∑ g : Fin n → Fin n with Function.Bijective g, d g := by
  classical
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have hcompl : ∑ S : Finset (Fin n) with ∀ j, g j ∈ S, (-1 : ℝ) ^ (n - S.card) =
      ∑ T ∈ (univ.image g)ᶜ.powerset, (-1 : ℝ) ^ T.card := by
    refine Finset.sum_nbij' (fun S => Sᶜ) (fun T => Tᶜ) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_univ, true_and] at hS
      simp only [mem_powerset]
      intro x hx
      simp only [mem_compl, mem_image, mem_univ, true_and, not_exists] at hx ⊢
      intro j hj
      exact hx (hj ▸ hS j)
    · intro T hT
      simp only [mem_powerset] at hT
      simp only [mem_filter, mem_univ, true_and, mem_compl]
      intro j hj
      exact mem_compl.1 (hT hj) (mem_image_of_mem g (mem_univ j))
    · intro S _; simp
    · intro T _; simp
    · intro S _; simp [card_compl]
  have hint := congrArg (Int.cast : ℤ → ℝ)
    (Finset.sum_powerset_neg_one_pow_card (x := (univ.image g)ᶜ))
  push_cast at hint
  rw [hcompl, hint]
  have hiff : (univ.image g)ᶜ = ∅ ↔ Function.Bijective g := by
    rw [Finset.compl_eq_empty_iff, ← Finite.surjective_iff_bijective]
    constructor
    · intro h x
      have hx : x ∈ univ.image g := by rw [h]; exact mem_univ x
      obtain ⟨j, _, hj⟩ := mem_image.1 hx
      exact ⟨j, hj⟩
    · exact Finset.image_univ_of_surjective
  by_cases hg : Function.Bijective g
  · rw [ite_eq_left (hiff.2 hg), ite_eq_left hg, one_mul]
  · rw [ite_eq_right (mt hiff.1 hg), ite_eq_right hg, zero_mul]

/-- Bijective self-maps of `Fin n` are reindexed by permutations. -/
theorem sum_bijective_eq_sum_perm {n : ℕ} (d : (Fin n → Fin n) → ℝ) :
    ∑ g : Fin n → Fin n with Function.Bijective g, d g =
      ∑ σ : Equiv.Perm (Fin n), d σ := by
  classical
  symm
  refine Finset.sum_bij (fun σ _ => ⇑σ) ?_ ?_ ?_ ?_
  · intro σ _
    simp only [mem_filter, mem_univ, true_and]
    exact σ.bijective
  · intro σ₁ _ σ₂ _ h
    exact DFunLike.coe_injective h
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg
    exact ⟨Equiv.ofBijective g hg, mem_univ _, rfl⟩
  · intro σ _
    rfl

/-- If `d` takes the value `d id` on every permutation, the signed inclusion–exclusion
sum equals `n! * d id`. -/
theorem sum_powerset_signed_eq_factorial_mul {n : ℕ} (d : (Fin n → Fin n) → ℝ)
    (hd : ∀ σ : Equiv.Perm (Fin n), d σ = d id) :
    ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        ∑ g : Fin n → Fin n with ∀ j, g j ∈ S, d g =
      (n.factorial : ℝ) * d id := by
  rw [sum_powerset_signed_eq_sum_bijective, sum_bijective_eq_sum_perm]
  simp_rw [hd]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end SGPT.Foundations.Analysis.Pending.PolarizationAlgebra
