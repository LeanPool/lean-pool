/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import LeanPool.AaronsonAmbainis.DetBij.Perm

/-!
# DetBij / Main: `LowestUnit → LowestBound → DetInequality`

The determinant inequality (Corollary 3.2 of the paper) from the two interface propositions of
`AaronsonAmbainis.DetDefs`, through the bijection theorem in the form of `Perm.lean`. The
argument is the proof of Corollary 3.2 from Theorem 3.1 in the paper.
-/

@[expose] public section

namespace AaronsonAmbainis.DetBij

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The wings extended to all points: `A x` on `zone g`, the empty set elsewhere. -/
def extWing (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x : Cube ι) : Finset ι :=
  if x ∈ zone g then A x else ∅

theorem extWing_of_mem (g : Cube ι → Bool) (A : Cube ι → Finset ι) {x : Cube ι}
    (hx : x ∈ zone g) : extWing g A x = A x := by
  unfold extWing
  rw [ite_eq_left hx]

theorem extWing_of_notMem (g : Cube ι → Bool) (A : Cube ι → Finset ι) {x : Cube ι}
    (hx : x ∉ zone g) : extWing g A x = ∅ := by
  unfold extWing
  rw [ite_eq_right hx]

/-- The extended wings are 1-wings at every one of `g` (the empty set is a 1-wing). -/
theorem isWing_extWing (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ u ∈ zone g, IsWing g u (A u)) (x : Ones g) :
    IsWing g x.1 (extWing g A x.1) := by
  by_cases hx : x.1 ∈ zone g
  · rw [extWing_of_mem g A hx]
    exact hA x.1 hx
  · intro S hS
    rw [extWing_of_notMem g A hx] at hS
    rw [Finset.subset_empty.mp hS, flipSet_empty]
    exact x.2

/-- The weighted inequality for one instance, from a permutation as in `exists_perm`. -/
theorem det_inequality_of_perm (g : Cube ι → Bool) (ℓ : ι → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (A : Cube ι → Finset ι) (d : Cube ι → ℝ)
    (hd : ∀ u ∈ zone g, ∀ G : Finset ι, Disjoint G (A u) →
        g (flipSet (antipode u) G) = true → d u ≤ ∑ j ∈ G, ℓ j)
    (σ : Equiv.Perm (Ones g))
    (hσ : ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (extWing g A (σ x).1))
    (hcard : ∀ j, (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card ≤ bdry g j) :
    ∑ u ∈ zone g, d u ≤ ∑ j, ℓ j * (bdry g j : ℝ) := by
  -- Step 1: the sum over the zone as a sum over the ones of `g`
  have hz : zone g ⊆ univ.filter (fun x : Cube ι => g x = true) := by
    intro u hu
    simp only [zone, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1
  have e0 : ∑ u ∈ univ.filter (fun x : Cube ι => g x = true), (if u ∈ zone g then d u else 0)
      = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) :=
    Finset.sum_subtype _ (fun x => by simp) (fun u => if u ∈ zone g then d u else 0)
  have h1 : ∑ u ∈ zone g, d u = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) := by
    rw [← e0, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hz]
  -- Step 2: the bound at each point (the hypothesis on `d` at `G = ag(y, σ⁻¹ y)`)
  have h2 : ∀ y : Ones g,
      (if y.1 ∈ zone g then d y.1 else 0) ≤ ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j := by
    intro y
    split_ifs with hy
    · refine hd y.1 hy _ ?_ ?_
      · have h := hσ (σ.symm y)
        rw [Equiv.apply_symm_apply, extWing_of_mem g A hy] at h
        exact h
      · rw [flipSet_antipode_agSet]
        exact (σ.symm y).2
    · exact Finset.sum_nonneg fun j _ => (hℓ j).le
  -- Step 3: reindex by `σ`
  have h3 : ∑ y : Ones g, ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j
      = ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j := by
    refine (Equiv.sum_comp σ
      (fun y : Ones g => ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j)).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.symm_apply_apply]
  -- Step 4: exchange the two sums
  have h4 : ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
      = ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ) := by
    have e1 : ∀ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
        = ∑ j, if (σ x).1 j = x.1 j then ℓ j else 0 := by
      intro x
      unfold agSet
      rw [Finset.sum_filter]
    have e2 : ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
        = ∑ x : Ones g, ∑ j, if (σ x).1 j = x.1 j then ℓ j else 0 :=
      Finset.sum_congr rfl fun x _ => e1 x
    rw [e2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 5: the bound on the multiplicities
  have h5 : ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ)
      ≤ ∑ j, ℓ j * (bdry g j : ℝ) :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcard j)) (hℓ j).le
  calc ∑ u ∈ zone g, d u
      = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) := h1
    _ ≤ ∑ y : Ones g, ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j :=
        Finset.sum_le_sum fun y _ => h2 y
    _ = ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j := h3
    _ = ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ) := h4
    _ ≤ ∑ j, ℓ j * (bdry g j : ℝ) := h5

/-- The determinant inequality (Corollary 3.2 of the paper) from `LowestUnit` and
`LowestBound`. -/
theorem detInequality_of_lowest :
    AaronsonAmbainis.LowestUnit → AaronsonAmbainis.LowestBound →
      AaronsonAmbainis.DetInequality := by
  intro hU hB
  unfold DetInequality
  intro ι _ _ g ℓ hℓ A hA d hd
  obtain ⟨σ, hσ, hcard⟩ := exists_perm hU hB g (extWing g A) (isWing_extWing g A hA)
  exact det_inequality_of_perm g ℓ hℓ A d hd σ hσ hcard

end AaronsonAmbainis.DetBij
