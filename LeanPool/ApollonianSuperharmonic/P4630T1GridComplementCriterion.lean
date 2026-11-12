/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.UniqueBoundedGridComplementComponent
public import Mathlib.Data.List.Chain

-- [TABLET NODE: P4630T1GridComplementCriterion]

/-!
# P4630T1GridComplementCriterion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4630T1GridComplementCriterion (B C : Set LatticeCell)
    (hfinite : C.Finite) (hC : FourNeighborConnected C)
    (hdisjoint : C ⊆ Bᶜ)
    (hboundary : ∀ x ∈ C, ∀ y, FourNeighborAdjacent x y → y ∉ C → y ∈ B)
    (hexterior : ∀ x, x ∉ C → x ∉ B →
      ∃ f : Nat → LatticeCell, Function.Injective f ∧ ∀ n,
        Relation.ReflTransGen
          (fun a b => FourNeighborAdjacent a b ∧ a ∉ B ∧ b ∉ B) x (f n)) :
    UniqueBoundedGridComplementComponent B C := by
-- BODY
  have symmetry : ∀ {x y : LatticeCell},
      FourNeighborAdjacent x y → FourNeighborAdjacent y x := by
    intro x y h
    rcases h with h | h | h | h
    all_goals subst y
    all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
  have fromList (S : Set LatticeCell) (hs : FourNeighborConnected S)
      (x : LatticeCell) (hx : x ∈ S) (y : LatticeCell) (hy : y ∈ S) :
      Relation.ReflTransGen
        (fun a b => FourNeighborAdjacent a b ∧ a ∈ S ∧ b ∈ S) x y := by
    obtain ⟨p, hp, hlast, hmem, hstep⟩ := hs.2 x hx y hy
    have hne : p ≠ [] := by rintro rfl; simp at hp
    have chain : p.IsChain
        (fun a b => FourNeighborAdjacent a b ∧ a ∈ S ∧ b ∈ S) :=
      (List.isChain_iff_forall_rel_of_append_cons_cons.mpr hstep).imp_of_mem_imp
        (fun a b ha hb e => ⟨e, hmem a ha, hmem b hb⟩)
    have h := List.relationReflTransGen_of_exists_isChain p chain hne
    rw [List.head?_eq_some_head hne] at hp
    rw [List.getLast?_eq_getLast_of_ne_nil hne] at hlast
    simpa only [Option.some.inj hp, Option.some.inj hlast] using h
  have toList (S : Set LatticeCell) {x y : LatticeCell} (hx : x ∈ S)
      (h : Relation.ReflTransGen
        (fun a b => FourNeighborAdjacent a b ∧ a ∈ S ∧ b ∈ S) x y) :
      ∃ p : List LatticeCell, p.head? = some x ∧ p.getLast? = some y ∧
        (∀ z ∈ p, z ∈ S) ∧ ∀ a b : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
          p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b := by
    obtain ⟨p, hp, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    refine ⟨x :: p, by simp, ?_, ?_, ?_⟩
    · rw [List.getLast?_eq_getLast_of_ne_nil (by simp), hlast]
    · exact hp.induction (fun z => z ∈ S) _ (fun {_ _} e _ => e.2.2)
        (fun _ => hx)
    · exact List.isChain_iff_forall_rel_of_append_cons_cons.mp
        (hp.imp (fun _ _ e => e.1))
  let R := fun a b : LatticeCell => FourNeighborAdjacent a b ∧ a ∉ B ∧ b ∉ B
  have maximal (D : Set LatticeCell) (hD : FourNeighborConnected D)
      (hCD : C ⊆ D) (hDB : D ⊆ Bᶜ) : D = C := by
    apply Set.Subset.antisymm _ hCD
    obtain ⟨x, hx⟩ := hC.1
    intro y hy
    have h : Relation.ReflTransGen R x y :=
      Relation.ReflTransGen.mono
        (fun a b e => ⟨e.1, hDB e.2.1, hDB e.2.2⟩)
        x y (fromList D hD x (hCD hx) y hy)
    clear hy
    induction h with
    | refl => exact hx
    | @tail y z h e ih =>
      by_contra hz
      exact e.2.2 (hboundary y ih z e.1 hz)
  change C.Finite ∧ C ⊆ Bᶜ ∧ FourNeighborConnected C ∧
    (∀ D, FourNeighborConnected D → C ⊆ D → D ⊆ Bᶜ → D = C) ∧
    ∀ D, D.Finite → D ⊆ Bᶜ → FourNeighborConnected D →
      (∀ E, FourNeighborConnected E → D ⊆ E → E ⊆ Bᶜ → E = D) → D = C
  refine ⟨hfinite, hdisjoint, hC, maximal, ?_⟩
  intro D hfin hDB hD hmax
  obtain ⟨x, hx⟩ := hD.1
  by_cases hxC : x ∈ C
  · have DC : D ⊆ C := by
      intro y hy
      have h : Relation.ReflTransGen R x y :=
        Relation.ReflTransGen.mono
          (fun a b e => ⟨e.1, hDB e.2.1, hDB e.2.2⟩)
          x y (fromList D hD x hx y hy)
      clear hy
      induction h with
      | refl => exact hxC
      | @tail y z h e ih =>
        by_contra hz
        exact e.2.2 (hboundary y ih z e.1 hz)
    exact (hmax C hC DC hdisjoint).symm
  · obtain ⟨f, hf, hroute⟩ := hexterior x hxC (hDB hx)
    let E : Set LatticeCell := {y | Relation.ReflTransGen R x y}
    have hEB : E ⊆ Bᶜ := by
      intro y hy
      induction hy with
      | refl => exact hDB hx
      | tail _ e _ => exact e.2.2
    have extend {y z : LatticeCell} (hy : y ∈ E)
        (h : Relation.ReflTransGen R y z) :
        Relation.ReflTransGen
          (fun a b => FourNeighborAdjacent a b ∧ a ∈ E ∧ b ∈ E) y z := by
      induction h with
      | refl => exact .refl
      | tail h e ih => exact ih.tail ⟨e.1, hy.trans h, (hy.trans h).tail e⟩
    have hE : FourNeighborConnected E := by
      refine ⟨⟨x, Relation.ReflTransGen.refl⟩, ?_⟩
      intro y hy z hz
      have rev : Relation.ReflTransGen R y x := by
        induction hy with
        | refl => exact .refl
        | tail _ e ih => exact
            (Relation.ReflTransGen.single ⟨symmetry e.1, e.2.2, e.2.1⟩).trans ih
      exact toList E hy (extend hy (rev.trans hz))
    have hDE : D ⊆ E := by
      intro y hy
      exact Relation.ReflTransGen.mono
        (fun a b e => ⟨e.1, hDB e.2.1, hDB e.2.2⟩)
        x y (fromList D hD x hx y hy)
    have eq := hmax E hE hDE hEB
    have hEF : E.Finite := eq.symm ▸ hfin
    have hrange : Set.range f ⊆ E := by rintro _ ⟨n, rfl⟩; exact hroute n
    exact False.elim ((Set.infinite_range_of_injective hf) (hEF.subset hrange))

end ApollonianSuperharmonic

end
