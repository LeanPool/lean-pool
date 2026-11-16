/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Open sets in Noetherian quasi-sober spaces

In a Noetherian quasi-sober space, a set `E` stable under generalization is open as soon as, for
every `x ∈ E`, the set `E ∩ closure {x}` contains a nonempty open subset of `closure {x}`. The
proof is by Noetherian induction on closed subsets.

## Main statements

* `TopologicalSpace.NoetherianSpace.isOpen_of_stableUnderGeneralization`.
-/

public section

open Topology

variable {α : Type*} [TopologicalSpace α]

namespace TopologicalSpace

/-- In a Noetherian quasi-sober space, a set `E` stable under generalization is open as soon as,
for every `x ∈ E`, some open neighbourhood `W` of `x` satisfies `W ∩ closure {x} ⊆ E` (that is,
`E ∩ closure {x}` contains a nonempty open subset of `closure {x}`). -/
theorem NoetherianSpace.isOpen_of_stableUnderGeneralization [NoetherianSpace α] [QuasiSober α]
    {E : Set α} (hE : StableUnderGeneralization E)
    (hE' : ∀ x ∈ E, ∃ W : Set α, IsOpen W ∧ x ∈ W ∧ W ∩ closure {x} ⊆ E) : IsOpen E := by
  -- By Noetherian induction: a closed set `Z` in which `Z \ E` is dense does not meet `E`.
  have key (Z : Closeds α) (hZ : (Z : Set α) ⊆ closure ((Z : Set α) ∩ Eᶜ)) :
      (Z : Set α) ⊆ Eᶜ := by
    induction Z using WellFoundedLT.induction with | _ Z IH => ?_
    intro y hyZ hyE
    by_cases hZirr : IsPreirreducible (Z : Set α)
    · have hirr : IsIrreducible (Z : Set α) := ⟨⟨y, hyZ⟩, hZirr⟩
      have hg := hirr.isGenericPoint_genericPoint Z.isClosed
      obtain ⟨W, hW, hzW, hWE⟩ := hE' _ (hE (hg.specializes hyZ) hyE)
      obtain ⟨w, hwW, hwZ, hwE⟩ := mem_closure_iff.1 (hZ hg.mem) W hW hzW
      exact hwE (hWE ⟨hwW, hg.def.symm ▸ hwZ⟩)
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hZirr
      obtain ⟨z₁, z₂, hz₁, hz₂, hZz, hz₁', hz₂'⟩ := hZirr
      -- `Z \ E` is dense in a closed subset of `Z ∩ zᵢ`, which is strictly smaller than `Z`.
      have piece (z : Set α) (hz : IsClosed z) (hz' : ¬(Z : Set α) ⊆ z) :
          closure ((Z : Set α) ∩ z ∩ Eᶜ) ⊆ Eᶜ := by
        let Z' : Closeds α := ⟨closure ((Z : Set α) ∩ z ∩ Eᶜ), isClosed_closure⟩
        have sub : (Z' : Set α) ⊆ (Z : Set α) ∩ z :=
          closure_minimal (fun x hx ↦ hx.1) (Z.isClosed.inter hz)
        have lt : Z' < Z := lt_of_le_of_ne (sub.trans Set.inter_subset_left) fun e ↦
          hz' (e ▸ sub.trans Set.inter_subset_right)
        exact IH Z' lt (closure_mono fun x hx ↦ ⟨subset_closure hx, hx.2⟩)
      have hsplit : (Z : Set α) ∩ Eᶜ ⊆ ((Z : Set α) ∩ z₁ ∩ Eᶜ) ∪ ((Z : Set α) ∩ z₂ ∩ Eᶜ) := by
        rintro x ⟨hxZ, hxE⟩
        exact (hZz hxZ).imp (fun h ↦ ⟨⟨hxZ, h⟩, hxE⟩) fun h ↦ ⟨⟨hxZ, h⟩, hxE⟩
      rcases (closure_mono hsplit).trans closure_union.subset (hZ hyZ) with h | h
      exacts [piece z₁ hz₁ hz₁' h hyE, piece z₂ hz₂ hz₂' h hyE]
  exact isClosed_compl_iff.1 <| closure_subset_iff_isClosed.1 <|
    key ⟨closure Eᶜ, isClosed_closure⟩ (closure_mono fun x hx ↦ ⟨subset_closure hx, hx⟩)

end TopologicalSpace
