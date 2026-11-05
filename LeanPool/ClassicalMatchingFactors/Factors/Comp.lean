/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
/-!

Imported from [jtraverso/tutte-f-factor](https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean), registered as PALOMAR-2026-10-18-000005. The original proof is retained; module paths and imports are adapted for this collection.

# Auxiliary results on connected components for the f-factor theorem

* `FFactor.oddComponents_ncard_eq_of_label`: counting odd components via a labelling whose
  fibres are exactly the components.
* `FFactor.ncard_oddComponents_deleteVerts_le`: removing a vertex `x` from a vertex set `U`
  whose neighbours outside `U` meet at most two components of `G - U` decreases the number of
  odd components by at most one.
-/

@[expose] public section

open Finset SimpleGraph

namespace FFactor

section Label

variable {X L : Type*} (H : SimpleGraph X) (φ : X → L)

theorem label_eq_of_reachable (h1 : ∀ x y, H.Adj x y → φ x = φ y) {x y : X}
    (h : H.Reachable x y) : φ x = φ y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (h1 _ _ ha).trans ih

open Classical in
theorem oddComponents_ncard_eq_of_label [Fintype X]
    (h1 : ∀ x y, H.Adj x y → φ x = φ y) (h2 : ∀ x y, φ x = φ y → H.Reachable x y) :
    H.oddComponents.ncard = #{l ∈ univ.image φ | Odd #{x | φ x = l}} := by
  let ψ : H.ConnectedComponent → L :=
    ConnectedComponent.lift φ (fun v w p _ => label_eq_of_reachable H φ h1 ⟨p⟩)
  have hψ : ∀ x, ψ (H.connectedComponentMk x) = φ x := fun x => rfl
  have hinj : Function.Injective ψ := by
    intro c d hcd
    induction c using ConnectedComponent.ind with | h x => ?_
    induction d using ConnectedComponent.ind with | h y => ?_
    exact ConnectedComponent.sound (h2 x y hcd)
  have hsupp : ∀ c : H.ConnectedComponent, c.supp = {x | φ x = ψ c} := by
    intro c
    induction c using ConnectedComponent.ind with | h y => ?_
    ext x
    simp only [ConnectedComponent.mem_supp_iff, Set.mem_ofPred_eq, hψ]
    constructor
    · intro h; rw [← hψ, ← hψ, h]
    · intro h; exact ConnectedComponent.sound (h2 x y h)
  have key : ∀ l, ({x | φ x = l} : Set X).ncard = #{x | φ x = l} := fun l => by
    rw [← Set.ncard_coe_finset]; simp
  rw [← Set.ncard_image_of_injective _ hinj, ← Set.ncard_coe_finset]
  congr 1
  ext l
  simp only [Set.mem_image, Set.mem_ofPred_eq, coe_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩
    induction c using ConnectedComponent.ind with | h y => ?_
    refine ⟨⟨y, rfl⟩, ?_⟩
    rw [hsupp, key] at hc
    exact hc
  · rintro ⟨⟨y, rfl⟩, hodd⟩
    refine ⟨H.connectedComponentMk y, ?_, rfl⟩
    show Odd (H.connectedComponentMk y).supp.ncard
    rw [hsupp, key]
    exact hodd

end Label

section Removal

variable {W : Type*} (Γ : SimpleGraph W)

/-- The graph `Γ - U`, as in Mathlib's definition of a Tutte violator. -/
abbrev del (U : Set W) : SimpleGraph ((⊤ : Γ.Subgraph).deleteVerts U).verts :=
  ((⊤ : Γ.Subgraph).deleteVerts U).coe

theorem mem_del_verts {U : Set W} {a : W} :
    a ∈ ((⊤ : Γ.Subgraph).deleteVerts U).verts ↔ a ∉ U := by simp

theorem del_adj {U : Set W} {a b : ((⊤ : Γ.Subgraph).deleteVerts U).verts} :
    (del Γ U).Adj a b ↔ Γ.Adj a b := by
  constructor
  · intro h; exact Subgraph.coe_adj_sub _ _ _ h
  · intro h; exact Subgraph.deleteVerts_adj.mpr ⟨trivial, a.2.2, trivial, b.2.2, h⟩

/-- The inclusion `Γ - U → Γ - (U \ {x})`. -/
def delIncl (U : Set W) (x : W) : del Γ U →g del Γ (U \ {x}) where
  toFun a := ⟨a.1, ⟨trivial, fun h => a.2.2 h.1⟩⟩
  map_rel' h := (del_adj Γ (U := U \ {x})).mpr ((del_adj Γ (U := U)).mp h)

theorem delIncl_injective (U : Set W) (x : W) : Function.Injective (delIncl Γ U x) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

theorem ncard_oddComponents_del_le [Finite W] (U : Set W) (x : W) (hx : x ∈ U)
    (h3 : ∀ a b c : ((⊤ : Γ.Subgraph).deleteVerts U).verts, Γ.Adj x a → Γ.Adj x b →
      Γ.Adj x c → (del Γ U).Reachable a b ∨ (del Γ U).Reachable a c ∨
        (del Γ U).Reachable b c) :
    (del Γ U).oddComponents.ncard ≤ (del Γ (U \ {x})).oddComponents.ncard + 1 := by
  classical
  set H := del Γ U
  set H' := del Γ (U \ {x})
  let ι := delIncl Γ U x
  let A : Set H.ConnectedComponent :=
    {c | ∃ a : ((⊤ : Γ.Subgraph).deleteVerts U).verts, c = H.connectedComponentMk a ∧ Γ.Adj x a}
  let B : Set H.ConnectedComponent := {c | c ∉ A ∧ Odd c.supp.ncard}
  -- `A` has at most two elements
  have hA : A.ncard ≤ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2, c3, h1, h2, h3', h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).mp hcon
    obtain ⟨a1, rfl, ha1⟩ := h1
    obtain ⟨a2, rfl, ha2⟩ := h2
    obtain ⟨a3, rfl, ha3⟩ := h3'
    rcases h3 a1 a2 a3 ha1 ha2 ha3 with h | h | h
    · exact h12 (ConnectedComponent.sound h)
    · exact h13 (ConnectedComponent.sound h)
    · exact h23 (ConnectedComponent.sound h)
  have hsub : H.oddComponents ⊆ B ∪ A := by
    intro c hc
    by_cases hcA : c ∈ A
    · exact Or.inr hcA
    · exact Or.inl ⟨hcA, hc⟩
  have hodd1 : H.oddComponents.ncard ≤ B.ncard + 2 :=
    (Set.ncard_le_ncard hsub).trans ((Set.ncard_union_le _ _).trans (by omega))
  -- the label on `H'`
  let ψ : ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts → Option H.ConnectedComponent :=
    fun y => if h : y.1 ∉ U then
      (if H.connectedComponentMk ⟨y.1, by simpa using h⟩ ∈ A then none
        else some (H.connectedComponentMk ⟨y.1, by simpa using h⟩)) else none
  have hψι : ∀ a, H.connectedComponentMk a ∉ A → ψ (ι a) = some (H.connectedComponentMk a) := by
    intro a ha
    have h' : (a : W) ∉ U := a.2.2
    have e : ψ (ι a) = if H.connectedComponentMk a ∈ A then none
        else some (H.connectedComponentMk a) := dite_eq_left h'
    rw [e, ite_eq_right ha]
  have hψ1 : ∀ y z, H'.Adj y z → ψ y = ψ z := by
    have key : ∀ y z : ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts, H'.Adj y z →
        (y : W) ∈ U → ψ y = ψ z := by
      intro y z hyz hy
      have hyx : (y : W) = x := by have := y.2; simp_all
      have hy' : ψ y = none := by simp [ψ, hy]
      rw [hy']
      by_cases hz : (z : W) ∈ U
      · simp [ψ, hz]
      · have hmem : H.connectedComponentMk ⟨z.1, by simpa using hz⟩ ∈ A :=
          ⟨⟨z.1, by simpa using hz⟩, rfl, hyx ▸ (del_adj Γ (U := U \ {x})).mp hyz⟩
        simp [ψ, hz, hmem]
    intro y z hyz
    by_cases hy : (y : W) ∈ U
    · exact key y z hyz hy
    by_cases hz : (z : W) ∈ U
    · exact (key z y hyz.symm hz).symm
    have hc : H.connectedComponentMk ⟨y.1, by simpa using hy⟩ =
        H.connectedComponentMk ⟨z.1, by simpa using hz⟩ :=
      ConnectedComponent.connectedComponentMk_eq_of_adj
        ((del_adj Γ (U := U)).mpr ((del_adj Γ (U := U \ {x})).mp hyz))
    simp only [ψ, hy, hz, not_false_eq_true, dite_true, hc]
  have hBle : B.ncard ≤ H'.oddComponents.ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun c => c.map ι)
    · intro c hc
      obtain ⟨hcA, hcodd⟩ := hc
      induction c using ConnectedComponent.ind with | h a => ?_
      change Odd (H'.connectedComponentMk (ι a)).supp.ncard
      have hsupp : (H'.connectedComponentMk (ι a)).supp = ι '' (H.connectedComponentMk a).supp := by
        ext z
        simp only [ConnectedComponent.mem_supp_iff, Set.mem_image]
        constructor
        · intro hz
          have hzψ : ψ z = some (H.connectedComponentMk a) := by
            rw [← hψι a hcA]
            exact label_eq_of_reachable H' ψ hψ1 (ConnectedComponent.exact hz)
          have hzU : (z : W) ∉ U := by
            intro h; simp [ψ, h] at hzψ
          refine ⟨⟨z.1, by simpa using hzU⟩, ?_, rfl⟩
          simp only [ψ, hzU, not_false_eq_true, dite_true] at hzψ
          split_ifs at hzψ
          exact Option.some_injective _ hzψ
        · rintro ⟨b, hb, rfl⟩
          rw [← ConnectedComponent.map_mk, ← ConnectedComponent.map_mk, hb]
      rw [hsupp, Set.ncard_image_of_injective _ (delIncl_injective Γ U x)]
      exact hcodd
    · intro c hc d hd hcd
      induction c using ConnectedComponent.ind with | h a => ?_
      induction d using ConnectedComponent.ind with | h b => ?_
      have hr : H'.Reachable (ι a) (ι b) := by
        apply ConnectedComponent.exact
        exact hcd
      have := label_eq_of_reachable H' ψ hψ1 hr
      rw [hψι a hc.1, hψι b hd.1] at this
      exact Option.some_injective _ this
  -- parity
  have hcard : Nat.card ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts =
      Nat.card ((⊤ : Γ.Subgraph).deleteVerts U).verts + 1 := by
    simp only [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top]
    rw [show Set.univ \ (U \ {x}) = insert x (Set.univ \ U) by
      ext y; by_cases hy : y = x <;> simp [hy, hx]]
    rw [Set.ncard_insert_of_notMem (by simp [hx])]
  have hp1 := (odd_ncard_oddComponents H)
  have hp2 := (odd_ncard_oddComponents H')
  rw [hcard] at hp2
  simp only [Nat.odd_iff] at hp1 hp2
  have hpar : H'.oddComponents.ncard % 2 ≠ H.oddComponents.ncard % 2 := by
    omega
  omega

/-- The neighbours of `x` outside `U` meet at most two components of `Γ - U`. -/
def TwoComp (U : Set W) (x : W) : Prop :=
  ∀ a b c : ((⊤ : Γ.Subgraph).deleteVerts U).verts, Γ.Adj x a → Γ.Adj x b →
      Γ.Adj x c → (del Γ U).Reachable a b ∨ (del Γ U).Reachable a c ∨
        (del Γ U).Reachable b c

/-- There is a Tutte violator none of whose vertices satisfies `TwoComp`. -/
theorem exists_min_violator [Finite W] (h : ∃ U, Γ.IsTutteViolator U) :
    ∃ U, Γ.IsTutteViolator U ∧ ∀ x ∈ U, ¬ TwoComp Γ U x := by
  classical
  have hex : ∃ n, ∃ U, U.ncard = n ∧ Γ.IsTutteViolator U := by
    obtain ⟨U, hU⟩ := h; exact ⟨_, U, rfl, hU⟩
  obtain ⟨U, hUn, hU⟩ := Nat.find_spec hex
  refine ⟨U, hU, fun x hx htwo => ?_⟩
  have hle := ncard_oddComponents_del_le Γ U x hx htwo
  have hcard : (U \ {x}).ncard + 1 = U.ncard := Set.ncard_sdiff_singleton_add_one hx
  have hviol : Γ.IsTutteViolator (U \ {x}) := by
    unfold IsTutteViolator at hU ⊢
    change U.ncard < (del Γ U).oddComponents.ncard at hU
    change (U \ {x}).ncard < (del Γ (U \ {x})).oddComponents.ncard
    omega
  have := Nat.find_min' hex ⟨U \ {x}, rfl, hviol⟩
  omega

end Removal

end FFactor
