/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Card
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent

-- [TABLET NODE: FiniteGridEdgeGraphEncoding]

/-!
# FiniteGridEdgeGraphEncoding

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace GridEncodingFacts

private theorem adjacent_ne :
    ∀ a b : GaussianInt, FourNeighborAdjacent a b → a ≠ b := by
  intro a b hab heq
  rcases hab with hab | hab | hab | hab <;> subst b
  all_goals
    have hr := congrArg (fun z : GaussianInt => z.re) hab
    have hi := congrArg (fun z : GaussianInt => z.im) hab
    try norm_num at hr
    try norm_num at hi
    try omega

end GridEncodingFacts

namespace GridEncodingGeometry

private theorem inc_inj :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hendpoints : {x : GaussianInt |
        ∃ e ∈ E, x ∈ e} ⊆ X),
    let Y : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    let inc : Y → X := fun y => ⟨y.1, hendpoints y.2⟩
    Function.Injective inc := by
  classical
  intro X E hendpoints Y inc a b hab
  apply Subtype.ext
  exact congrArg (fun z : X => (z : GaussianInt)) hab

private theorem lift :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hendpoints : {x : GaussianInt |
        ∃ e ∈ E, x ∈ e} ⊆ X),
    let Y : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    let H : SimpleGraph Y := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    let inc : Y → X := fun y => ⟨y.1, hendpoints y.2⟩
    let inc_hom : H →g G := by
      refine ⟨inc, ?_⟩
      intro a b hab
      have hab' := (SimpleGraph.fromRel_adj _ _ _).mp hab
      rcases hab' with ⟨hneab, hrel | hrel⟩
      · exact (SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨fun h => hneab (Subtype.ext (congrArg (fun z : X => (z : GaussianInt)) h)), Or.inl hrel⟩
      · exact (SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨fun h => hneab (Subtype.ext (congrArg (fun z : X => (z : GaussianInt)) h)), Or.inr hrel⟩
    ∀ (inc_val : ∀ (y : Y), (inc_hom y : GaussianInt) = y), ∀ (u : X), ∀ (v : X), ∀ (hu : (u :
        GaussianInt) ∈ Y), ∀ (p : G.Walk u v), ∃ hv : (v : GaussianInt) ∈ Y, ∃ q : H.Walk ⟨u, hu⟩
        ⟨v, hv⟩,
        q.map inc_hom = p.copy
          (by apply Subtype.ext; exact (inc_val ⟨u.1, hu⟩).symm)
          (by apply Subtype.ext; exact (inc_val ⟨v.1, hv⟩).symm) := by
  classical
  intro X E hendpoints Y H G inc inc_hom inc_val u v hu p
  induction p with
  | nil => exact ⟨hu, .nil, by simp⟩
  | @cons u v w hadj p ih =>
    have hadj' := (SimpleGraph.fromRel_adj _ _ _).mp hadj
    rcases hadj' with ⟨hneuv, hrel | hrel⟩
    · have hv : (v.1 : GaussianInt) ∈ Y := ⟨{u.1, v.1}, hrel, by simp⟩
      have hwq := ih hv
      rcases hwq with ⟨hw, q, hq⟩
      have hstep : H.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
        exact (SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨fun h => hneuv (Subtype.ext (congrArg (fun z : Y => (z : GaussianInt)) h)), Or.inl
              hrel⟩
      exact ⟨hw, .cons hstep q, by
        have he : inc_hom ⟨v, hv⟩ = v := Subtype.ext (inc_val ⟨v, hv⟩).symm
        simpa [SimpleGraph.Walk.map] using (And.intro he hq)⟩
    · have hv : (v.1 : GaussianInt) ∈ Y := ⟨{v.1, u.1}, hrel, by simp⟩
      have hwq := ih hv
      rcases hwq with ⟨hw, q, hq⟩
      have hstep : H.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
        exact (SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨fun h => hneuv (Subtype.ext (congrArg (fun z : Y => (z : GaussianInt)) h)), Or.inr
              hrel⟩
      exact ⟨hw, .cons hstep q, by
        have he : inc_hom ⟨v, hv⟩ = v := Subtype.ext (inc_val ⟨v, hv⟩).symm
        simpa [SimpleGraph.Walk.map] using (And.intro he hq)⟩

private theorem hac :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hendpoints : {x : GaussianInt |
        ∃ e ∈ E, x ∈ e} ⊆ X),
    let Y : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    let H : SimpleGraph Y := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    (H.IsAcyclic) → (
    let inc : Y → X := fun y => ⟨y.1, hendpoints y.2⟩
    (Function.Injective inc) → (
    let inc_hom : H →g G := by
      refine ⟨inc, ?_⟩
      intro a b hab
      have hab' := (SimpleGraph.fromRel_adj _ _ _).mp hab
      rcases hab' with ⟨hneab, hrel | hrel⟩
      · exact (SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨fun h => hneab (Subtype.ext (congrArg (fun z : X => (z : GaussianInt)) h)), Or.inl hrel⟩
      · exact (SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨fun h => hneab (Subtype.ext (congrArg (fun z : X => (z : GaussianInt)) h)), Or.inr hrel⟩
    ∀ (inc_val : ∀ (y : Y), (inc_hom y : GaussianInt) = y), (∀ (u : X), ∀ (v : X), ∀ (hu : (u :
        GaussianInt) ∈ Y), ∀ (p : G.Walk u v), ∃ hv : (v : GaussianInt) ∈ Y, ∃ q : H.Walk ⟨u, hu⟩
        ⟨v, hv⟩, q.map inc_hom = p.copy (by apply Subtype.ext; exact (inc_val ⟨u.1, hu⟩).symm)
        (by apply Subtype.ext; exact (inc_val ⟨v.1, hv⟩).symm)) → (G.IsAcyclic))) := by
  classical
  intro X E hendpoints Y H G hacyclic' inc inc_inj inc_hom inc_val lift u c hc
  cases c with
  | nil => exact SimpleGraph.Walk.not_isCycle_nil hc
  | @cons u v w hadj p =>
    have hadj' := (SimpleGraph.fromRel_adj _ _ _).mp hadj
    rcases hadj' with ⟨hneuv, hrel | hrel⟩
    · have hu : (u : GaussianInt) ∈ Y := ⟨{u.1, v.1}, hrel, by simp⟩
      obtain ⟨hu', q, hq⟩ := lift u u hu (.cons hadj p)
      let close : H.Walk ⟨u, hu⟩ ⟨u, hu⟩ := q.copy (Subtype.ext rfl) (Subtype.ext rfl)
      have hmap : close.map inc_hom = .cons hadj p := by
        simpa [close, SimpleGraph.Walk.map] using hq
      have hcycle : (close.map inc_hom).IsCycle := by simpa [hmap] using hc
      exact hacyclic' close ((SimpleGraph.Walk.isCycle_map_iff_of_injective inc_inj).mp hcycle)
    · have hu : (u : GaussianInt) ∈ Y :=
        ⟨{u.1, v.1}, by simpa [Finset.pair_comm] using hrel, by simp⟩
      obtain ⟨hu', q, hq⟩ := lift u u hu (.cons hadj p)
      let close : H.Walk ⟨u, hu⟩ ⟨u, hu⟩ := q.copy (Subtype.ext rfl) (Subtype.ext rfl)
      have hmap : close.map inc_hom = .cons hadj p := by
        simpa [close, SimpleGraph.Walk.map] using hq
      have hcycle : (close.map inc_hom).IsCycle := by simpa [hmap] using hc
      exact hacyclic' close ((SimpleGraph.Walk.isCycle_map_iff_of_injective inc_inj).mp hcycle)

private theorem pick_spec :
    ∀ (E : Set (Finset GaussianInt)), ∀ (hgrid : ∀ e ∈ E, ∃ (a : GaussianInt) (b : GaussianInt),
        e = {a, b} ∧ FourNeighborAdjacent a b),
    let pair : Finset GaussianInt → GaussianInt × GaussianInt := fun e =>
      Classical.choose (show ∃ p : GaussianInt × GaussianInt,
        (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
        by_cases he : e ∈ E
        · obtain ⟨a, b, hab, hfour⟩ := hgrid e he
          exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
        · exact ⟨(0, 0), Or.inr he⟩)
    let pickA : Finset GaussianInt → GaussianInt := fun e => (pair e).1
    let pickB : Finset GaussianInt → GaussianInt := fun e => (pair e).2
    ∀ (e : Finset GaussianInt), (e ∈ E) → (e = {pickA e, pickB e} ∧ FourNeighborAdjacent (pickA
        e) (pickB e)) := by
  classical
  intro E hgrid pair pickA pickB e he
  rcases Classical.choose_spec (show ∃ p : GaussianInt × GaussianInt,
    (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
    by_cases he' : e ∈ E
    · obtain ⟨a, b, hab, hfour⟩ := hgrid e he'
      exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
    · exact ⟨(0, 0), Or.inr he'⟩) with hs | hs
  · exact hs
  · exact (hs he).elim

private theorem pickA_mem :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hgrid : ∀ e ∈ E, ∃ (a :
        GaussianInt) (b : GaussianInt), e = {a, b} ∧ FourNeighborAdjacent a b), ({x : GaussianInt
        | ∃ e ∈ E, x ∈ e} ⊆ X) → (
    let pair : Finset GaussianInt → GaussianInt × GaussianInt := fun e =>
      Classical.choose (show ∃ p : GaussianInt × GaussianInt,
        (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
        by_cases he : e ∈ E
        · obtain ⟨a, b, hab, hfour⟩ := hgrid e he
          exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
        · exact ⟨(0, 0), Or.inr he⟩)
    let pickA : Finset GaussianInt → GaussianInt := fun e => (pair e).1
    let pickB : Finset GaussianInt → GaussianInt := fun e => (pair e).2
    (∀ (e : Finset GaussianInt), (e ∈ E) → (e = {pickA e, pickB e} ∧ FourNeighborAdjacent (pickA
        e) (pickB e))) → (∀ (e : Finset GaussianInt), (e ∈ E) → (pickA e ∈ X))) := by
  classical
  intro X E hgrid hendpoints pair pickA pickB pick_spec e he
  apply hendpoints
  refine ⟨e, he, ?_⟩
  have hp : ({pickA e, pickB e} : Finset GaussianInt) = e := (pick_spec e he).1.symm
  have hs : ({pickA e, pickB e} : Finset GaussianInt) ⊆ e := by
    intro x hx
    rw [← hp]
    exact hx
  exact hs (Finset.mem_insert_self _ _)

private theorem pickB_mem :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hgrid : ∀ e ∈ E, ∃ (a :
        GaussianInt) (b : GaussianInt), e = {a, b} ∧ FourNeighborAdjacent a b), ({x : GaussianInt
        | ∃ e ∈ E, x ∈ e} ⊆ X) → (
    let pair : Finset GaussianInt → GaussianInt × GaussianInt := fun e =>
      Classical.choose (show ∃ p : GaussianInt × GaussianInt,
        (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
        by_cases he : e ∈ E
        · obtain ⟨a, b, hab, hfour⟩ := hgrid e he
          exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
        · exact ⟨(0, 0), Or.inr he⟩)
    let pickA : Finset GaussianInt → GaussianInt := fun e => (pair e).1
    let pickB : Finset GaussianInt → GaussianInt := fun e => (pair e).2
    (∀ (e : Finset GaussianInt), (e ∈ E) → (e = {pickA e, pickB e} ∧ FourNeighborAdjacent (pickA
        e) (pickB e))) → (∀ (e : Finset GaussianInt), (e ∈ E) → (pickB e ∈ X))) := by
  classical
  intro X E hgrid hendpoints pair pickA pickB pick_spec e he
  apply hendpoints
  refine ⟨e, he, ?_⟩
  have hp : ({pickA e, pickB e} : Finset GaussianInt) = e := (pick_spec e he).1.symm
  have hs : ({pickA e, pickB e} : Finset GaussianInt) ⊆ e := by
    intro x hx
    rw [← hp]
    exact hx
  exact hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

private theorem edgeOf_mem :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hgrid : ∀ e ∈ E, ∃ (a :
        GaussianInt) (b : GaussianInt), e = {a, b} ∧ FourNeighborAdjacent a b),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    (∀ (a : GaussianInt), ∀ (b : GaussianInt), FourNeighborAdjacent a b → a ≠ b) → (
    let pair : Finset GaussianInt → GaussianInt × GaussianInt := fun e =>
      Classical.choose (show ∃ p : GaussianInt × GaussianInt,
        (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
        by_cases he : e ∈ E
        · obtain ⟨a, b, hab, hfour⟩ := hgrid e he
          exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
        · exact ⟨(0, 0), Or.inr he⟩)
    let pickA : Finset GaussianInt → GaussianInt := fun e => (pair e).1
    let pickB : Finset GaussianInt → GaussianInt := fun e => (pair e).2
    (∀ (e : Finset GaussianInt), (e ∈ E) → (e = {pickA e, pickB e} ∧ FourNeighborAdjacent (pickA
        e) (pickB e))) → (∀ (pickA_mem : ∀ (e : Finset GaussianInt), (e ∈ E) → (pickA e ∈ X)), ∀
        (pickB_mem : ∀ (e : Finset GaussianInt), (e ∈ E) → (pickB e ∈ X)),
    let edgeOf (e : Finset GaussianInt) (he : e ∈ E) : Sym2 X :=
      s(⟨pickA e, pickA_mem e he⟩, ⟨pickB e, pickB_mem e he⟩)
    ∀ (e : Finset GaussianInt), ∀ (he : e ∈ E), edgeOf e he ∈ G.edgeSet)) := by
  classical
  intro X E hgrid G hne pair pickA pickB pick_spec pickA_mem pickB_mem edgeOf e he
  rw [SimpleGraph.mem_edgeSet]
  apply (SimpleGraph.fromRel_adj _ _ _).mpr
  have hp : ({pickA e, pickB e} : Finset GaussianInt) ∈ E :=
    (pick_spec e he).1 ▸ he
  refine ⟨?_, Or.inl hp⟩
  exact fun h => hne _ _ (pick_spec e he).2 (Subtype.ext_iff.mp h)

private theorem edgeOf_inj :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hgrid : ∀ e ∈ E, ∃ (a :
        GaussianInt) (b : GaussianInt), e = {a, b} ∧ FourNeighborAdjacent a b),
    let pair : Finset GaussianInt → GaussianInt × GaussianInt := fun e =>
      Classical.choose (show ∃ p : GaussianInt × GaussianInt,
        (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
        by_cases he : e ∈ E
        · obtain ⟨a, b, hab, hfour⟩ := hgrid e he
          exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
        · exact ⟨(0, 0), Or.inr he⟩)
    let pickA : Finset GaussianInt → GaussianInt := fun e => (pair e).1
    let pickB : Finset GaussianInt → GaussianInt := fun e => (pair e).2
    (∀ (e : Finset GaussianInt), (e ∈ E) → (e = {pickA e, pickB e} ∧ FourNeighborAdjacent (pickA
        e) (pickB e))) → (∀ (pickA_mem : ∀ (e : Finset GaussianInt), (e ∈ E) → (pickA e ∈ X)), ∀
        (pickB_mem : ∀ (e : Finset GaussianInt), (e ∈ E) → (pickB e ∈ X)),
    let edgeOf (e : Finset GaussianInt) (he : e ∈ E) : Sym2 X :=
      s(⟨pickA e, pickA_mem e he⟩, ⟨pickB e, pickB_mem e he⟩)
    ∀ (e : Finset GaussianInt), ∀ (f : Finset GaussianInt), ∀ (he : e ∈ E), ∀ (hf : f ∈ E),
        (edgeOf e he = edgeOf f hf) → (e = f)) := by
  classical
  intro X E hgrid pair pickA pickB pick_spec pickA_mem pickB_mem edgeOf e f he hf h
  have hs : ({pickA e, pickB e} : Finset GaussianInt) = {pickA f, pickB f} := by
    apply Finset.ext
    intro x
    dsimp [edgeOf] at h
    rcases (Sym2.eq_iff.mp h) with h' | h'
    · have h₁ := congrArg (fun z : X => (z : GaussianInt)) h'.1
      have h₂ := congrArg (fun z : X => (z : GaussianInt)) h'.2
      change pickA e = pickA f at h₁
      change pickB e = pickB f at h₂
      rw [h₁, h₂]
    · have h₁ := congrArg (fun z : X => (z : GaussianInt)) h'.1
      have h₂ := congrArg (fun z : X => (z : GaussianInt)) h'.2
      change pickA e = pickB f at h₁
      change pickB e = pickA f at h₂
      rw [h₁, h₂]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact or_comm
  calc
    e = {pickA e, pickB e} := (pick_spec e he).1
    _ = {pickA f, pickB f} := hs
    _ = f := (pick_spec f hf).1.symm

private theorem edgeOf_surj :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hgrid : ∀ e ∈ E, ∃ (a :
        GaussianInt) (b : GaussianInt), e = {a, b} ∧ FourNeighborAdjacent a b),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    let pair : Finset GaussianInt → GaussianInt × GaussianInt := fun e =>
      Classical.choose (show ∃ p : GaussianInt × GaussianInt,
        (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
        by_cases he : e ∈ E
        · obtain ⟨a, b, hab, hfour⟩ := hgrid e he
          exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
        · exact ⟨(0, 0), Or.inr he⟩)
    let pickA : Finset GaussianInt → GaussianInt := fun e => (pair e).1
    let pickB : Finset GaussianInt → GaussianInt := fun e => (pair e).2
    (∀ (e : Finset GaussianInt), (e ∈ E) → (e = {pickA e, pickB e} ∧ FourNeighborAdjacent (pickA
        e) (pickB e))) → (∀ (pickA_mem : ∀ (e : Finset GaussianInt), (e ∈ E) → (pickA e ∈ X)), ∀
        (pickB_mem : ∀ (e : Finset GaussianInt), (e ∈ E) → (pickB e ∈ X)),
    let edgeOf (e : Finset GaussianInt) (he : e ∈ E) : Sym2 X :=
      s(⟨pickA e, pickA_mem e he⟩, ⟨pickB e, pickB_mem e he⟩)
    ∀ (z : Sym2 X), (z ∈ G.edgeSet) → (∃ e, ∃ he : e ∈ E, edgeOf e he = z)) := by
  classical
  intro X E hgrid G pair pickA pickB pick_spec pickA_mem pickB_mem edgeOf z hz
  induction z using Sym2.inductionOn with
  | _ x y =>
    have hadj := (SimpleGraph.mem_edgeSet G).mp hz
    have hadj' := (SimpleGraph.fromRel_adj _ _ _).mp hadj
    rcases hadj' with ⟨hne_xy, hrel | hrel⟩
    · let e : Finset GaussianInt := {x.1, y.1}
      have he : e ∈ E := hrel
      refine ⟨e, he, ?_⟩
      have hset : ({pickA e, pickB e} : Finset GaussianInt) = {x.1, y.1} := by
        calc
          {pickA e, pickB e} = e := (pick_spec e he).1.symm
          _ = {x.1, y.1} := rfl
      have hxmem : x.1 ∈ ({pickA e, pickB e} : Finset GaussianInt) := by
        rw [hset]
        simp
      have hymem : y.1 ∈ ({pickA e, pickB e} : Finset GaussianInt) := by
        rw [hset]
        simp
      have hx : x.1 = pickA e ∨ x.1 = pickB e := by simpa using hxmem
      have hy : y.1 = pickA e ∨ y.1 = pickB e := by simpa using hymem
      dsimp [edgeOf]
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact (hne_xy (Subtype.ext (hx.trans hy.symm))).elim
      · exact (Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hx.symm, Subtype.ext hy.symm⟩))
      · exact (Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hy.symm, Subtype.ext hx.symm⟩))
      · exact (hne_xy (Subtype.ext (hx.trans hy.symm))).elim
    · let e : Finset GaussianInt := {x.1, y.1}
      have he : e ∈ E := by simpa [e, Finset.pair_comm] using hrel
      refine ⟨e, he, ?_⟩
      have hset : ({pickA e, pickB e} : Finset GaussianInt) = {x.1, y.1} := by
        calc
          {pickA e, pickB e} = e := (pick_spec e he).1.symm
          _ = {x.1, y.1} := rfl
      have hxmem : x.1 ∈ ({pickA e, pickB e} : Finset GaussianInt) := by
        rw [hset]
        simp
      have hymem : y.1 ∈ ({pickA e, pickB e} : Finset GaussianInt) := by
        rw [hset]
        simp
      have hx : x.1 = pickA e ∨ x.1 = pickB e := by simpa using hxmem
      have hy : y.1 = pickA e ∨ y.1 = pickB e := by simpa using hymem
      dsimp [edgeOf]
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact (hne_xy (Subtype.ext (hx.trans hy.symm))).elim
      · exact (Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hx.symm, Subtype.ext hy.symm⟩))
      · exact (Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hy.symm, Subtype.ext hx.symm⟩))
      · exact (hne_xy (Subtype.ext (hx.trans hy.symm))).elim

private theorem hcard :
    ∀ (X : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (hgrid : ∀ e ∈ E, ∃ (a :
        GaussianInt) (b : GaussianInt), e = {a, b} ∧ FourNeighborAdjacent a b),
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    let pair : Finset GaussianInt → GaussianInt × GaussianInt := fun e =>
      Classical.choose (show ∃ p : GaussianInt × GaussianInt,
        (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
        by_cases he : e ∈ E
        · obtain ⟨a, b, hab, hfour⟩ := hgrid e he
          exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
        · exact ⟨(0, 0), Or.inr he⟩)
    let pickA : Finset GaussianInt → GaussianInt := fun e => (pair e).1
    let pickB : Finset GaussianInt → GaussianInt := fun e => (pair e).2
    ∀ (pickA_mem : ∀ (e : Finset GaussianInt), (e ∈ E) → (pickA e ∈ X)), ∀ (pickB_mem : ∀ (e :
        Finset GaussianInt), (e ∈ E) → (pickB e ∈ X)),
    let edgeOf (e : Finset GaussianInt) (he : e ∈ E) : Sym2 X :=
      s(⟨pickA e, pickA_mem e he⟩, ⟨pickB e, pickB_mem e he⟩)
    (∀ (e : Finset GaussianInt), ∀ (he : e ∈ E), edgeOf e he ∈ G.edgeSet) → ((∀ (e : Finset
        GaussianInt), ∀ (f : Finset GaussianInt), ∀ (he : e ∈ E), ∀ (hf : f ∈ E), (edgeOf e he =
        edgeOf f hf) → (e = f)) → ((∀ (z : Sym2 X), (z ∈ G.edgeSet) → (∃ e, ∃ he : e ∈ E, edgeOf
        e he = z)) → (E.ncard = G.edgeSet.ncard))) := by
  classical
  intro X E hgrid G pair pickA pickB pickA_mem pickB_mem edgeOf edgeOf_mem edgeOf_inj edgeOf_surj
  apply Set.ncard_congr edgeOf edgeOf_mem
  · exact edgeOf_inj
  · exact edgeOf_surj

end GridEncodingGeometry

theorem FiniteGridEdgeGraphEncoding
    (X : Set GaussianInt) (E : Set (Finset GaussianInt))
    (hgrid : ∀ e ∈ E, ∃ a b : GaussianInt,
      e = {a, b} ∧ FourNeighborAdjacent a b)
    (hendpoints : {x | ∃ e ∈ E, x ∈ e} ⊆ X)
    (hacyclic :
      let Y : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
      let H : SimpleGraph Y := SimpleGraph.fromRel fun a b =>
        ({a.1, b.1} : Finset GaussianInt) ∈ E
      H.IsAcyclic) :
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    G.IsAcyclic ∧ Nat.card G.edgeSet = E.ncard := by
-- BODY
  let Y : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
  let H : SimpleGraph Y := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  have hne := GridEncodingFacts.adjacent_ne
  have hacyclic' : H.IsAcyclic := by
    simpa [Y, H] using hacyclic
  let inc : Y → X := fun y => ⟨y.1, hendpoints y.2⟩
  have inc_inj : Function.Injective inc := GridEncodingGeometry.inc_inj X E hendpoints
  let inc_hom : H →g G := by
    refine ⟨inc, ?_⟩
    intro a b hab
    have hab' := (SimpleGraph.fromRel_adj _ _ _).mp hab
    rcases hab' with ⟨hneab, hrel | hrel⟩
    · exact (SimpleGraph.fromRel_adj _ _ _).mpr
        ⟨fun h => hneab (Subtype.ext (congrArg (fun z : X => (z : GaussianInt)) h)), Or.inl hrel⟩
    · exact (SimpleGraph.fromRel_adj _ _ _).mpr
        ⟨fun h => hneab (Subtype.ext (congrArg (fun z : X => (z : GaussianInt)) h)), Or.inr hrel⟩
  have inc_val (y : Y) : (inc_hom y : GaussianInt) = y := by
    rfl
  change G.IsAcyclic ∧ Nat.card G.edgeSet = E.ncard
  have lift : ∀ (u v : X) (hu : (u : GaussianInt) ∈ Y) (p : G.Walk u v),
      ∃ hv : (v : GaussianInt) ∈ Y, ∃ q : H.Walk ⟨u, hu⟩ ⟨v, hv⟩,
        q.map inc_hom = p.copy
          (by apply Subtype.ext; exact (inc_val ⟨u.1, hu⟩).symm)
          (by apply Subtype.ext; exact (inc_val ⟨v.1, hv⟩).symm) := GridEncodingGeometry.lift X E
              hendpoints inc_val
  have hac : G.IsAcyclic := GridEncodingGeometry.hac X E hendpoints hacyclic' inc_inj inc_val lift
  let pair : Finset GaussianInt → GaussianInt × GaussianInt := fun e =>
    Classical.choose (show ∃ p : GaussianInt × GaussianInt,
      (e = {p.1, p.2} ∧ FourNeighborAdjacent p.1 p.2) ∨ e ∉ E by
      by_cases he : e ∈ E
      · obtain ⟨a, b, hab, hfour⟩ := hgrid e he
        exact ⟨(a, b), Or.inl ⟨hab, hfour⟩⟩
      · exact ⟨(0, 0), Or.inr he⟩)
  let pickA : Finset GaussianInt → GaussianInt := fun e => (pair e).1
  let pickB : Finset GaussianInt → GaussianInt := fun e => (pair e).2
  have pick_spec (e : Finset GaussianInt) (he : e ∈ E) :
      e = {pickA e, pickB e} ∧ FourNeighborAdjacent (pickA e) (pickB e) :=
          GridEncodingGeometry.pick_spec E hgrid e he
  have pickA_mem (e : Finset GaussianInt) (he : e ∈ E) : pickA e ∈ X :=
      GridEncodingGeometry.pickA_mem X E hgrid hendpoints pick_spec e he
  have pickB_mem (e : Finset GaussianInt) (he : e ∈ E) : pickB e ∈ X :=
      GridEncodingGeometry.pickB_mem X E hgrid hendpoints pick_spec e he
  let edgeOf (e : Finset GaussianInt) (he : e ∈ E) : Sym2 X :=
    s(⟨pickA e, pickA_mem e he⟩, ⟨pickB e, pickB_mem e he⟩)
  have edgeOf_mem (e : Finset GaussianInt) (he : e ∈ E) : edgeOf e he ∈ G.edgeSet :=
      GridEncodingGeometry.edgeOf_mem X E hgrid hne pick_spec pickA_mem pickB_mem e he
  have edgeOf_inj (e f : Finset GaussianInt) (he : e ∈ E) (hf : f ∈ E)
      (h : edgeOf e he = edgeOf f hf) : e = f := GridEncodingGeometry.edgeOf_inj X E hgrid
          pick_spec pickA_mem pickB_mem e f he hf h
  have edgeOf_surj (z : Sym2 X) (hz : z ∈ G.edgeSet) :
      ∃ e, ∃ he : e ∈ E, edgeOf e he = z := GridEncodingGeometry.edgeOf_surj X E hgrid pick_spec
          pickA_mem pickB_mem z hz
  have hcard : E.ncard = G.edgeSet.ncard := GridEncodingGeometry.hcard X E hgrid pickA_mem
      pickB_mem edgeOf_mem edgeOf_inj edgeOf_surj
  exact ⟨hac, hcard.symm⟩

end ApollonianSuperharmonic

end
