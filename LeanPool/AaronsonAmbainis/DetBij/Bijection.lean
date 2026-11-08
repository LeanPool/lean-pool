/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Data.Fintype.Pi
public import LeanPool.AaronsonAmbainis.DetBij.Perm

/-!
# DetBij / Bijection: the bijection theorem, in the wording of the paper

Not needed for `detInequality_of_lowest`. From `LowestUnit` and `LowestBound`: for every choice
of 1-wings `A x` at the ones of `g` there is a bijection `τ` of the ones of `g` such that `τ x`
differs from `x` on all of `A x`, and `#{x : (τ x)_j = x_j} ≤ bdry g j` for every `j`
simultaneously. These are parts (a) and (b) of the bijection theorem (Theorem 3.1 of the paper).
The relation of part (a) to Reimer's Butterfly Lemma (Remark 3.10 of the paper) is not
formalised.
-/

@[expose] public section

namespace AaronsonAmbainis.DetBij

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bijection theorem as stated in the paper (Theorem 3.1; `τ` is the inverse of the
permutation of `exists_perm`), from the two interface propositions `LowestUnit` and
`LowestBound`, which are proved in the directory `DetLow`. -/
theorem exists_bijection (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ τ : Equiv.Perm (Ones g), (∀ x : Ones g, A x.1 ⊆ diffSet x.1 (τ x).1) ∧
      ∀ j, (univ.filter fun x : Ones g => (τ x).1 j = x.1 j).card ≤ bdry g j := by
  obtain ⟨σ, hσ, hcard⟩ := exists_perm hU hB g A hA
  refine ⟨σ.symm, fun x => ?_, fun j => ?_⟩
  · have h := hσ (σ.symm x)
    rw [Equiv.apply_symm_apply] at h
    intro i hi
    rw [mem_diffSet]
    exact fun hxi => Finset.disjoint_right.mp h hi (mem_agSet.mpr hxi)
  · have hc : (univ.filter fun y : Ones g => (σ.symm y).1 j = y.1 j).card
        = (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card := by
      refine Finset.card_bij (fun (y : Ones g) _ => σ.symm y) ?_ ?_ ?_
      · intro y hy
        have hy' : (σ.symm y).1 j = y.1 j := (Finset.mem_filter.mp hy).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [Equiv.apply_symm_apply]
        exact hy'.symm
      · intro y₁ _ y₂ _ h
        exact σ.symm.injective h
      · intro x hx
        have hx' : (σ x).1 j = x.1 j := (Finset.mem_filter.mp hx).2
        refine ⟨σ x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Equiv.symm_apply_apply σ x⟩
        rw [Equiv.symm_apply_apply]
        exact hx'.symm
    rw [hc]
    exact hcard j

end AaronsonAmbainis.DetBij
