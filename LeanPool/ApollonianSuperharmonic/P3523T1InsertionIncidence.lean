/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.TypeStar

public import LeanPool.ApollonianSuperharmonic.P3523T1OrderedInsertion
public import LeanPool.ApollonianSuperharmonic.P3523T1FaceEnumeration

-- [TABLET NODE: P3523T1InsertionIncidence]

/-!
# P3523T1InsertionIncidence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace InsertionIncidenceProof

private theorem hface_inj :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), Function.Injective (fun k : Fin t.count =>
        Finset.univ.image (s.start ∘ t.face k)) ) := by
  classical
  intro r n q p s X K t k l heq
  apply t.face_distinct
  have h' : (Finset.univ.image (t.face k)).image s.start =
      (Finset.univ.image (t.face l)).image s.start := by
    simpa only [Finset.image_image, Function.comp_def] using heq
  have h'' := (Finset.image_injective s.start_injective) h'
  apply Set.ext
  intro x
  simpa only [Set.mem_range, Finset.mem_image, Finset.mem_univ, true_and] using Iff.of_eq
    (congrArg (fun A : Finset (Fin (r + 3)) => x ∈ A) h'')

private theorem hsplit_card :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (fs : Finset (Finset (Fin (n + (3 : ℕ))))), ∀ (a : Fin (n + (3 : ℕ))), ∀
            (d : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), (∀ F ∈ fs, F.card = (3 : ℕ)) → (∀
            F ∈ fs,
        d ∉ F) → ∀ G ∈ P3523T1BoundaryFaceSplit fs a d b, G.card = (3 : ℕ) ) := by
  classical
  intro n fs a d b hf hd G hG
  change G ∈ fs.biUnion (fun F =>
    if a ∈ F ∧ b ∈ F then {insert d (F.erase b), insert d (F.erase a)}
    else {F}) at hG
  rw [Finset.mem_biUnion] at hG
  rcases hG with ⟨F, hF, hG⟩
  by_cases hp : a ∈ F ∧ b ∈ F
  · simp only [hp, and_self, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hG
    rcases hG with hG | hG
    · subst G
      have hnot : d ∉ F.erase b := fun hx => hd F hF (Finset.mem_of_mem_erase hx)
      rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hp.2]
      rw [hf F hF]
    · subst G
      have hnot : d ∉ F.erase a := fun hx => hd F hF (Finset.mem_of_mem_erase hx)
      rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hp.1]
      rw [hf F hF]
  · simp only [hp, ↓reduceIte, Finset.mem_singleton] at hG
    subst G
    exact hf F hF

private theorem hsplit_sub :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (fs : Finset (Finset (Fin (n + (3 : ℕ))))), ∀ (a : Fin (n + (3 : ℕ))), ∀
            (d : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (V : Finset (Fin (n + (3 :
            ℕ)))), (∀ F ∈
        fs, F ⊆ V) → ∀ G ∈ P3523T1BoundaryFaceSplit fs a d b, G ⊆ insert d V ) := by
  classical
  intro n fs a d b V hf G hG
  change G ∈ fs.biUnion (fun F =>
    if a ∈ F ∧ b ∈ F then {insert d (F.erase b), insert d (F.erase a)}
    else {F}) at hG
  rw [Finset.mem_biUnion] at hG
  rcases hG with ⟨F, hF, hG⟩
  by_cases hp : a ∈ F ∧ b ∈ F
  · simp only [hp, and_self, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hG
    rcases hG with hG | hG
    · subst G
      intro x hx
      simp only [Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (hf F hF (Finset.mem_of_mem_erase hx))
    · subst G
      intro x hx
      simp only [Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (hf F hF (Finset.mem_of_mem_erase hx))
  · simp only [hp, ↓reduceIte, Finset.mem_singleton] at hG
    subst G
    intro x hx
    simp only [Finset.mem_insert]
    exact Or.inr (hf F hF hx)

private theorem hfaces_next :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length), c.faces (h + (1 : ℕ)) = P3523T1BoundaryFaceSplit
        (c.faces h) (c.steps.get ⟨h, hh⟩).1 (c.steps.get ⟨h, hh⟩).2.1 (c.steps.get ⟨h, hh⟩).2.2 )
            := by
  classical
  intro r n q p s X K t c h hh
  change (c.steps.take (h + 1)).foldl
      (fun fs e => P3523T1BoundaryFaceSplit fs e.1 e.2.1 e.2.2)
      (Finset.univ.image fun k : Fin t.count =>
        Finset.univ.image (s.start ∘ t.face k)) =
    P3523T1BoundaryFaceSplit ((c.steps.take h).foldl
      (fun fs e => P3523T1BoundaryFaceSplit fs e.1 e.2.1 e.2.2)
      (Finset.univ.image fun k : Fin t.count =>
        Finset.univ.image (s.start ∘ t.face k)))
      (c.steps.get ⟨h, hh⟩).1 (c.steps.get ⟨h, hh⟩).2.1 (c.steps.get ⟨h, hh⟩).2.2
  rw [← List.take_append_getElem hh]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [List.get_eq_getElem]

private theorem hboundary_next :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length), c.boundary (h + (1 : ℕ)) = insert {(c.steps.get ⟨h,
        hh⟩).1, (c.steps.get ⟨h, hh⟩).2.1} (insert {(c.steps.get ⟨h, hh⟩).2.1, (c.steps.get ⟨h,
        hh⟩).2.2} ((c.boundary h).erase {(c.steps.get ⟨h, hh⟩).1, (c.steps.get ⟨h, hh⟩).2.2})) )
            := by
  classical
  intro r n q p s X K t c h hh
  let B0 : Finset (Finset (Fin (n + 3))) := Finset.univ.image fun i : Fin (r + 3) =>
    ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3)))
  change (c.steps.take (h + 1)).foldl
      (fun es e => insert {e.1, e.2.1}
        (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))) B0 =
    insert {(c.steps.get ⟨h, hh⟩).1, (c.steps.get ⟨h, hh⟩).2.1}
      (insert {(c.steps.get ⟨h, hh⟩).2.1, (c.steps.get ⟨h, hh⟩).2.2}
        (((c.steps.take h).foldl (fun es e => insert {e.1, e.2.1}
          (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))) B0).erase
          {(c.steps.get ⟨h, hh⟩).1, (c.steps.get ⟨h, hh⟩).2.2}))
  rw [← List.take_append_getElem hh]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.get_eq_getElem]

private theorem hstage :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ (h : ℕ), ∀ (hh : h < (P3523T1InsertionConstruction s t).steps.length),
        let e :=
        (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
        (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈ (P3523T1InsertionConstruction
        s t).vertices h ∧ e.2.1 ∉ (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2}
        ∈ (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ)
        ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
        P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s t
        e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → ((∀ F ∈ c.faces 0, F.card = 3) → ((∀
            (fs : Finset (Finset (Fin (n + 3)))), ∀ (a : Fin (n + 3)), ∀ (d : Fin (n + 3)), ∀ (b
            : Fin (n + 3)), (∀ F ∈ fs, F.card = 3) → ((∀ F ∈ fs, d ∉ F) → (∀ G ∈
        P3523T1BoundaryFaceSplit fs a d b, G.card = 3))) → ((∀ (fs : Finset (Finset (Fin (n +
        3)))), ∀ (a : Fin (n + 3)), ∀ (d : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (V : Finset (Fin
        (n + 3))), (∀ F ∈ fs, F ⊆ V) → (∀ G ∈ P3523T1BoundaryFaceSplit fs a d b, G ⊆ insert d
        V)) → ((∀ F ∈ c.faces 0, F ⊆ c.vertices 0) → ((∀ (h : Nat), ∀ (hh : h < c.steps.length),
            c.faces (h + 1) = P3523T1BoundaryFaceSplit (c.faces h) (c.steps.get ⟨h, hh⟩).1
        (c.steps.get ⟨h, hh⟩).2.1 (c.steps.get ⟨h, hh⟩).2.2) → ((∀ (h : Nat), ∀ (hh : h <
        c.steps.length), c.vertices (h + 1) = insert (c.steps.get ⟨h, hh⟩).2.1 (c.vertices h)) →
        (∀ h : Nat, h ≤ c.steps.length → ∀ F ∈ c.faces h, F.card = 3 ∧ F ⊆ c.vertices h))))))) )
            := by
  classical
  intro r n q p s X K t c hsteps hinit hsplit_card hsplit_sub hinit_sub hfaces_next
      hvertices_next h hh
  induction h with
  | zero =>
      intro F hF
      exact ⟨hinit F hF, hinit_sub F hF⟩
  | succ h ih =>
      have hlt : h < c.steps.length := by omega
      have ih' := ih (by omega)
      intro F hF
      let e := c.steps.get ⟨h, hlt⟩
      have he := hsteps h hlt
      dsimp [e] at he
      rcases he with ⟨_, _, _, hdnew, _, _⟩
      rw [hfaces_next h hlt] at hF
      constructor
      · apply hsplit_card
        · intro G hG
          exact (ih' G hG).1
        · intro G hG hdG
          exact hdnew ((ih' G hG).2 hdG)
        · exact hF
      · rw [hvertices_next h hlt]
        apply hsplit_sub
        · intro G hG
          exact (ih' G hG).2
        · exact hF

private theorem hboundary_support :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ (h : ℕ), ∀ (hh : h < (P3523T1InsertionConstruction s t).steps.length),
        let e :=
        (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
        (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈ (P3523T1InsertionConstruction
        s t).vertices h ∧ e.2.1 ∉ (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2}
        ∈ (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ)
        ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
        P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s t
        e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → ((∀ (h : Nat), ∀ (hh : h <
        c.steps.length), c.vertices (h + 1) = insert (c.steps.get ⟨h, hh⟩).2.1 (c.vertices h)) →
        ((∀ (h : Nat), ∀ (hh : h < c.steps.length), c.boundary (h + 1) = insert {(c.steps.get ⟨h,
        hh⟩).1, (c.steps.get ⟨h, hh⟩).2.1} (insert {(c.steps.get ⟨h, hh⟩).2.1, (c.steps.get ⟨h,
        hh⟩).2.2} ((c.boundary h).erase {(c.steps.get ⟨h, hh⟩).1, (c.steps.get ⟨h, hh⟩).2.2}))) →
        (∀ h : Nat, h ≤ c.steps.length → ∀ P ∈ c.boundary h, ∀ x ∈ P, x ∈ c.vertices h))) ) := by
  classical
  intro r n q p s X K t c hsteps hvertices_next hboundary_next h hh
  induction h with
  | zero =>
      intro P hP x hx
      change P ∈ Finset.univ.image (fun i : Fin (r + 3) =>
        ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3)))) at hP
      rcases Finset.mem_image.mp hP with ⟨i, -, rfl⟩
      change x ∈ Finset.univ.image s.start
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · subst x
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · subst x
        exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩
  | succ h ih =>
      have hlt : h < c.steps.length := by omega
      have ih' := ih (by omega)
      let e := c.steps.get ⟨h, hlt⟩
      have he := hsteps h hlt
      dsimp [e] at he
      rcases he with ⟨_, ha, hb, _, _, _⟩
      intro P hP x hx
      rw [hboundary_next h hlt] at hP
      rw [hvertices_next h hlt]
      simp only [Finset.mem_insert] at hP
      rcases hP with hP | hP
      · subst P
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_insert]
        rcases hx with hx | hx
        · subst x
          exact Or.inr ha
        · subst x
          exact Or.inl rfl
      · rcases hP with hP | hP
        · subst P
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_insert]
          rcases hx with hx | hx
          · subst x
            exact Or.inl rfl
          · subst x
            exact Or.inr hb
        · simp only [Finset.mem_erase] at hP
          exact Finset.mem_insert.mpr (Or.inr (ih' P hP.2 x hx))

private theorem hthird :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (F : Finset (Fin (n + (3 : ℕ)))), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n +
        (3 : ℕ))), a ≠ b → F.card = (3 : ℕ) → a ∈ F → b ∈ F → ∃ (x : Fin (n + (3 : ℕ))), x ≠ a ∧
        x ≠ b ∧ F = {a, b, x} ) := by
  classical
  intro n F a b hab hcard ha hb
  have hb' : b ∈ F.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hFa : (F.erase a).card = 2 := by rw [Finset.card_erase_of_mem ha, hcard]
  have hS : ((F.erase a).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem hb', hFa]
  rcases Finset.card_eq_one.mp hS with ⟨x, hx⟩
  have hxa : x ≠ a := by
    intro h
    subst x
    have : a ∉ (F.erase a).erase b := by simp
    rw [hx] at this
    simp at this
  have hxb : x ≠ b := by
    intro h
    subst x
    have : b ∉ (F.erase a).erase b := by simp
    rw [hx] at this
    simp at this
  have hxF : x ∈ F := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
    (by rw [hx]; simp))
  refine ⟨x, hxa, hxb, ?_⟩
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hy
    by_cases hya : y = a
    · exact Or.inl hya
    · by_cases hyb : y = b
      · exact Or.inr (Or.inl hyb)
      · have hyS : y ∈ (F.erase a).erase b :=
          Finset.mem_erase.mpr ⟨hyb, Finset.mem_erase.mpr ⟨hya, hy⟩⟩
        have : y = x := by simpa [hx] using hyS
        exact Or.inr (Or.inr this)
  · rintro (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hxF

private theorem hfaceChoice :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let fs := c.faces c.steps.length
        (∀ F ∈ fs, F.card = 3) → (∀ (k : Fin fs.card), ∃ (g : Fin (3 : ℕ) → Fin (n + (3 : ℕ))),
        Function.Injective g ∧ Set.range g = (↑(↑((fs.equivFin.symm : Fin fs.card → ↥fs) k) :
        Finset (Fin (n + (3 : ℕ)))) : Set (Fin (n + (3 : ℕ))))) ) := by
  classical
  intro r n q p s X K t c fs hfinal_card k
  let F := (fs.equivFin.symm k).val
  have hF : F ∈ fs := (fs.equivFin.symm k).property
  have hc : F.card = 3 := hfinal_card F hF
  let g : Fin 3 → Fin (n + 3) := fun j =>
    (F.equivFin.symm (Fin.cast hc.symm j)).val
  refine ⟨g, ?_, ?_⟩
  · intro i j hij
    have hsub : F.equivFin.symm (Fin.cast hc.symm i) =
        F.equivFin.symm (Fin.cast hc.symm j) := Subtype.ext hij
    have hcast := F.equivFin.symm.injective hsub
    exact Fin.cast_injective hc.symm hcast
  · apply Set.ext
    intro x
    constructor
    · rintro ⟨j, rfl⟩
      exact (F.equivFin.symm (Fin.cast hc.symm j)).property
    · intro hx
      have hxF : x ∈ F := by simpa [F] using hx
      refine ⟨Fin.cast hc (F.equivFin ⟨x, hxF⟩), ?_⟩
      simp [g, Fin.cast_cast]

private theorem hindexed_filter_card :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let fs := c.faces c.steps.length
        let f := P3523T1FaceEnumeration fs
        (∀ (k : Fin fs.card), Function.Injective (f k) ∧ Set.range (f k) = ((fs.equivFin.symm k).val
        : Set (Fin (n + 3)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), ({k : Fin
        fs.card | i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)} : Finset (Fin fs.card)).card =
        {F ∈ fs | i ∈ F ∧ j ∈
        F}.card) ) := by
  classical
  intro r n q p s X K t c fs f hf_spec i j
  apply Finset.card_bij (fun k hk => (fs.equivFin.symm k).val)
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨_, hk⟩
    apply Finset.mem_filter.mpr
    refine ⟨(fs.equivFin.symm k).property, ?_⟩
    constructor
    · have hi : i ∈ Set.range (f k) := hk.1
      rw [(hf_spec k).2] at hi
      exact hi
    · have hj : j ∈ Set.range (f k) := hk.2
      rw [(hf_spec k).2] at hj
      exact hj
  · intro k hk l hl heq
    apply (fs.equivFin.symm).injective
    apply Subtype.ext
    exact heq
  · intro F hF
    rcases Finset.mem_filter.mp hF with ⟨hF, hp⟩
    let k := fs.equivFin ⟨F, hF⟩
    have hface : (fs.equivFin.symm k).val = F := by simp [k]
    have hrange : Set.range (f k) = (F : Set (Fin (n + 3))) := by
      rw [(hf_spec k).2, hface]
    refine ⟨k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hrange]
      exact hp
    · simp [k]

private theorem hindexed_exists :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let fs := c.faces c.steps.length
        let f := P3523T1FaceEnumeration fs
        (∀ (k : Fin fs.card), Function.Injective (f k) ∧ Set.range (f k) = ((fs.equivFin.symm k).val
        : Set (Fin (n + 3)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), (∃ (k :
        Fin fs.card), i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)) ↔ ∃ F ∈ fs, i ∈ F ∧ j ∈ F) ) := by
  classical
  intro r n q p s X K t c fs f hf_spec i j
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(fs.equivFin.symm k).val, (fs.equivFin.symm k).property, ?_⟩
    constructor
    · have hi : i ∈ Set.range (f k) := hk.1
      rw [(hf_spec k).2] at hi
      exact hi
    · have hj : j ∈ Set.range (f k) := hk.2
      rw [(hf_spec k).2] at hj
      exact hj
  · rintro ⟨F, hF, hp⟩
    let k := fs.equivFin ⟨F, hF⟩
    have hface : (fs.equivFin.symm k).val = F := by simp [k]
    have hrange : Set.range (f k) = (F : Set (Fin (n + 3))) := by
      rw [(hf_spec k).2, hface]
    refine ⟨k, ?_⟩
    rw [hrange]
    exact hp

private theorem hinitial_pair_count :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (Function.Injective (fun k : Fin t.count => Finset.univ.image (s.start ∘ t.face k))) → (∀
            (i : Fin (r + (3 : ℕ))), ∀ (j : Fin (r + (3 : ℕ))), {F ∈ c.faces (0 : ℕ) | s.start i
            ∈ F ∧
        s.start j ∈ F}.card = {k : Fin t.count | i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face
        k)}.ncard) ) := by
  classical
  intro r n q p s X K t c hface_inj i j
  change ((Finset.univ.image (fun k : Fin t.count =>
    Finset.univ.image (s.start ∘ t.face k))).filter
      (fun F => s.start i ∈ F ∧ s.start j ∈ F)).card = _
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ hface_inj]
  have hp (k : Fin t.count) :
      (s.start i ∈ Finset.univ.image (s.start ∘ t.face k) ∧
        s.start j ∈ Finset.univ.image (s.start ∘ t.face k)) ↔
      i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨⟨x, s.start_injective hx⟩, ⟨y, s.start_injective hy⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨⟨x, congrArg s.start hx⟩, ⟨y, congrArg s.start hy⟩⟩
  have heq : Finset.univ.filter (fun k : Fin t.count =>
      s.start i ∈ Finset.univ.image (s.start ∘ t.face k) ∧
      s.start j ∈ Finset.univ.image (s.start ∘ t.face k)) =
    Finset.univ.filter (fun k : Fin t.count =>
      i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp k
  rw [heq]
  have hset : (Finset.univ.filter (fun k : Fin t.count =>
      i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)) : Set (Fin t.count)) =
    {k : Fin t.count | i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)} := by
    ext k
    simp
  rw [← hset, Set.ncard_coe_finset]

private theorem pair_eq_pair :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), a ≠ b → c
        ≠ d → (({a, b} : Finset α) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c) ) := by
  classical
  intro α typeclassInstance0 a b c d hab hcd
  constructor
  · intro h
    have hc : c = a ∨ c = b := by
      have : c ∈ ({a, b} : Finset α) := by rw [h]; simp
      simpa using this
    have hd : d = a ∨ d = b := by
      have : d ∈ ({a, b} : Finset α) := by rw [h]; simp
      simpa using this
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · exact False.elim (hcd (hc.trans hd.symm))
    · exact Or.inl ⟨hc.symm, hd.symm⟩
    · exact Or.inr ⟨hd.symm, hc.symm⟩
    · have : a ∈ ({c, d} : Finset α) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with ha | ha
      · exact False.elim (hab (ha.trans hc))
      · exact False.elim (hab (ha.trans hd))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

private theorem hboundary_final_pair :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ((P3523T1InsertionConstruction s t).boundary (P3523T1InsertionConstruction s
        t).steps.length = Finset.image (fun (j : Fin (n + (3 : ℕ))) => {j,
        j + (1 : Fin (n + (3 : ℕ)))}) Finset.univ) → ((∀ {α : Type}, ∀ [DecidableEq α], ∀ (a :
            α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (a ≠ b) → ((c ≠ d) → (({a, b} : Finset α) = {c,
            d} ↔
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)))) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 :
        ℕ))), i ≠ j → ({i, j} ∈ c.boundary c.steps.length ↔ j = i + (1 : Fin (n + (3 : ℕ))) ∨ i =
        j + (1 : Fin (n + (3 : ℕ)))))) ) := by
  classical
  intro r n q p s X K t c hboundary pair_eq_pair i j hij
  rw [hboundary, Finset.mem_image]
  constructor
  · rintro ⟨k, -, hpair⟩
    have hk : k ≠ k + 1 := by
      intro heq
      have hv := congrArg Fin.val heq
      change k.val = (k.val + 1) % (n + 3) at hv
      by_cases hlt : k.val + 1 < n + 3
      · rw [Nat.mod_eq_of_lt hlt] at hv
        omega
      · have hend : k.val + 1 = n + 3 := by omega
        rw [hend, Nat.mod_self] at hv
        omega
    rcases (pair_eq_pair i j k (k + 1) hij hk).mp hpair.symm with h | h
    · left
      rw [h.1, h.2]
    · right
      rw [h.1, h.2]
  · intro h
    rcases h with h | h
    · subst j
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · subst i
      exact ⟨j, Finset.mem_univ _, Finset.pair_comm _ _⟩

private theorem hindexed_ledger :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let fs := c.faces c.steps.length
        let f := P3523T1FaceEnumeration fs
        (∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)), (Finset.univ.filter (fun k : Fin fs.card => i ∈
        Set.range (f k) ∧ j ∈ Set.range (f k))).card = (fs.filter (fun F => i ∈ F ∧ j ∈ F)).card)
        → ((∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)), (∃ k : Fin fs.card, i ∈ Set.range (f k) ∧ j
        ∈ Set.range (f k)) ↔ ∃ F ∈ fs, i ∈ F ∧ j ∈ F) → ((∀ (i : Fin (n + 3)), ∀ (j : Fin (n +
        3)), (i ≠ j) → (({i, j} : Finset (Fin (n + 3))) ∈ c.boundary c.steps.length ↔ j = i + 1 ∨
        i = j + 1)) → ((∀ h ≤ c.steps.length, ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 :
        ℕ))), a ≠ b → {F ∈ c.faces h | a ∈ F ∧ b ∈ F}.card = if {a, b} ∈ c.boundary h then (1 :
        ℕ) else if ∃ F ∈ c.faces h, a ∈ F ∧ b ∈ F then (2 : ℕ) else (0 : ℕ)) → ∀ (i : Fin (n + (3
        : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), i ≠ j → {k : Fin fs.card | i ∈ Set.range (f k) ∧ j ∈
        Set.range (f k)}.ncard = if j = i + (1 : Fin (n + (3 : ℕ))) ∨ i = j + (1 : Fin (n + (3 :
        ℕ))) then (1 : ℕ) else if ∃ (k : Fin fs.card), i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)
        then (2 : ℕ) else (0 : ℕ)))) ) := by
  classical
  intro r n q p s X K t c fs f hindexed_filter_card hindexed_exists hboundary_final_pair hinc i j
      hij
  have hset : (Finset.univ.filter (fun k : Fin fs.card =>
      i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)) : Set (Fin fs.card)) =
      {k : Fin fs.card | i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)} := by
    ext k
    simp
  rw [← hset, Set.ncard_coe_finset, hindexed_filter_card]
  have h := hinc c.steps.length le_rfl i j hij
  by_cases hbnd : {i, j} ∈ c.boundary c.steps.length
  · have hbSucc := (hboundary_final_pair i j hij).mp hbnd
    by_cases hex : ∃ F ∈ fs, i ∈ F ∧ j ∈ F
    · simp only [hbnd, ↓reduceIte, hbSucc] at h ⊢
      exact h
    · simp only [hbnd, ↓reduceIte, hbSucc] at h ⊢
      exact h
  · have hbSucc : ¬(j = i + 1 ∨ i = j + 1) := by
      intro hsucc
      exact hbnd ((hboundary_final_pair i j hij).mpr hsucc)
    by_cases hex : ∃ F ∈ fs, i ∈ F ∧ j ∈ F
    · have hex' : ∃ F ∈ c.faces c.steps.length, i ∈ F ∧ j ∈ F := by
        simpa [fs] using hex
      have hidx := (hindexed_exists i j).2 hex
      have hidx' : ∃ k : Fin fs.card, (∃ y, f k y = i) ∧ ∃ y, f k y = j := by
        simpa only [Set.mem_range] using hidx
      simp only [hbnd, ↓reduceIte, hex', hbSucc, Set.mem_range, hidx'] at h ⊢
      exact h
    · have hidx : ¬∃ k : Fin fs.card, i ∈ Set.range (f k) ∧ j ∈ Set.range (f k) := by
        intro hk
        exact hex ((hindexed_exists i j).1 hk)
      have hex' : ¬∃ F ∈ c.faces c.steps.length, i ∈ F ∧ j ∈ F := by
        simpa [fs] using hex
      have hidx' : ¬∃ k : Fin fs.card, (∃ y, f k y = i) ∧ ∃ y, f k y = j := by
        simpa only [Set.mem_range] using hidx
      simp only [hbnd, ↓reduceIte, hex', Finset.card_eq_zero, Finset.filter_eq_empty_iff,
          not_and, hbSucc, Set.mem_range, hidx'] at h ⊢
      exact h

private theorem hboundary0_pair :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (a ≠ b) →
            ((c ≠
        d) → (({a, b} : Finset α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)))) → (∀ (i : Fin
        (r + (3 : ℕ))), ∀ (j : Fin (r + (3 : ℕ))), i ≠ j → ({s.start i, s.start j} ∈ c.boundary
        (0 : ℕ) ↔ j = i + (1 : Fin (r + (3 : ℕ))) ∨ i = j + (1 : Fin (r + (3 : ℕ))))) ) := by
  classical
  intro r n q p s X K t c pair_eq_pair i j hij
  have hzero : c.boundary 0 = Finset.univ.image (fun k : Fin (r + 3) =>
      ({s.start k, s.start (k + 1)} : Finset (Fin (n + 3)))) := by
    rfl
  rw [hzero, Finset.mem_image]
  constructor
  · rintro ⟨k, -, hpair⟩
    have hk : k ≠ k + 1 := by
      intro heq
      have hv := congrArg Fin.val heq
      change k.val = (k.val + 1) % (r + 3) at hv
      by_cases hlt : k.val + 1 < r + 3
      · rw [Nat.mod_eq_of_lt hlt] at hv
        omega
      · have heq' : k.val + 1 = r + 3 := by omega
        rw [heq', Nat.mod_self] at hv
        omega
    rcases (pair_eq_pair (s.start i) (s.start j) (s.start k) (s.start (k + 1))
        (fun h => hij (s.start_injective h)) (fun h => hk (s.start_injective h))).mp hpair.symm with
      h | h
    · left
      have hi' := s.start_injective h.1
      have hj' := s.start_injective h.2
      rw [← hi'] at hj'
      exact hj'
    · right
      have hj' := s.start_injective h.2
      have hi' := s.start_injective h.1
      rw [← hj'] at hi'
      exact hi'
  · intro h
    rcases h with h | h
    · subst j
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rfl
    · subst i
      refine ⟨j, Finset.mem_univ _, ?_⟩
      exact Finset.pair_comm _ _

private theorem hexists_initial_pair :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (i : Fin (r + (3 : ℕ))), ∀ (j : Fin (r + (3 : ℕ))), (∃ F ∈ c.faces (0 : ℕ), s.start i ∈
            F ∧
        s.start j ∈ F) ↔ ∃ (k : Fin t.count), i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k)
            ) := by
  classical
  intro r n q p s X K t c i j
  have hp (k : Fin t.count) :
      (s.start i ∈ Finset.univ.image (s.start ∘ t.face k) ∧
        s.start j ∈ Finset.univ.image (s.start ∘ t.face k)) ↔
      i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face k) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨⟨x, s.start_injective hx⟩, ⟨y, s.start_injective hy⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨⟨x, congrArg s.start hx⟩, ⟨y, congrArg s.start hy⟩⟩
  constructor
  · rintro ⟨F, hF, hi, hj⟩
    change F ∈ Finset.univ.image (fun k : Fin t.count =>
      Finset.univ.image (s.start ∘ t.face k)) at hF
    rcases Finset.mem_image.mp hF with ⟨k, -, rfl⟩
    exact ⟨k, hp k |>.mp ⟨hi, hj⟩⟩
  · rintro ⟨k, hk⟩
    refine ⟨Finset.univ.image (s.start ∘ t.face k), ?_, (hp k).2 hk |>.1,
      (hp k).2 hk |>.2⟩
    · change _ ∈ Finset.univ.image (fun k : Fin t.count =>
        Finset.univ.image (s.start ∘ t.face k))
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

private theorem hboundary0_support :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ P ∈ c.boundary 0, ∀ x ∈ P, x ∈ c.vertices 0 ) := by
  classical
  intro r n q p s X K t c P hP x hx
  change P ∈ Finset.univ.image (fun i : Fin (r + 3) =>
    ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3)))) at hP
  rcases Finset.mem_image.mp hP with ⟨i, -, rfl⟩
  change x ∈ Finset.univ.image s.start
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx
  · subst x
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · subst x
    exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩

private theorem hinit_ledger :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ F ∈ c.faces 0, F ⊆ c.vertices 0) → ((∀ (i : Fin (r + 3)), ∀ (j : Fin (r + 3)), (i ≠ j) →
        (((c.faces 0).filter (fun F => s.start i ∈ F ∧ s.start j ∈ F)).card = if {s.start i,
        s.start j} ∈ c.boundary 0 then 1 else if ∃ F ∈ c.faces 0, s.start i ∈ F ∧ s.start j ∈ F
        then 2 else 0)) → ((∀ P ∈ c.boundary 0, ∀ x ∈ P, x ∈ c.vertices 0) → ((∀ x ∈ c.vertices
        0, ∃ i : Fin (r + 3), s.start i = x) → (∀ a b : Fin (n + 3), a ≠ b → ((c.faces 0).filter
        (fun F => a ∈ F ∧ b ∈ F)).card = if {a, b} ∈ c.boundary 0 then 1 else if ∃ F ∈ c.faces 0,
        a ∈ F ∧ b ∈ F then 2 else 0)))) ) := by
  classical
  intro r n q p s X K t c hinit_sub hinit_ledger_starts hboundary0_support hvertex0_start a b hab
  by_cases ha : ∃ i : Fin (r + 3), s.start i = a
  · by_cases hb : ∃ j : Fin (r + 3), s.start j = b
    · rcases ha with ⟨i, rfl⟩
      rcases hb with ⟨j, rfl⟩
      apply hinit_ledger_starts
      intro hij
      exact hab (congrArg s.start hij)
    · have hno : ¬ ∃ F ∈ c.faces 0, a ∈ F ∧ b ∈ F := by
        rintro ⟨F, hF, _, hbF⟩
        exact hb (hvertex0_start b (hinit_sub F hF hbF))
      have hnb : {a, b} ∉ c.boundary 0 := by
        intro hP
        exact hb (hvertex0_start b (hboundary0_support {a, b} hP b (by simp)))
      have he : (c.faces 0).filter (fun F => a ∈ F ∧ b ∈ F) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro F hF hp
        exact hno ⟨F, hF, hp⟩
      rw [he]
      simp [hnb, hno]
  · have hno : ¬ ∃ F ∈ c.faces 0, a ∈ F ∧ b ∈ F := by
      rintro ⟨F, hF, haF, _⟩
      exact ha (hvertex0_start a (hinit_sub F hF haF))
    have hnb : {a, b} ∉ c.boundary 0 := by
      intro hP
      exact ha (hvertex0_start a (hboundary0_support {a, b} hP a (by simp)))
    have he : (c.faces 0).filter (fun F => a ∈ F ∧ b ∈ F) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro F hF hp
      exact hno ⟨F, hF, hp⟩
    rw [he]
    simp [hnb, hno]

private theorem hsplit_eq :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (A : Finset (Finset (Fin (n + (3 : ℕ))))), ∀ (a : Fin (n + (3 : ℕ))), ∀ (d
            : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), a ≠ b → ∀ F ∈ A, a ∈ F ∧ b ∈ F → (∀
            G ∈ A,
        a ∈ G ∧ b ∈ G → G = F) → (∀ G ∈ A, d ∉ G) → P3523T1BoundaryFaceSplit A a d b = A.erase
        F ∪ {insert d (F.erase b), insert d (F.erase a)} ) := by
  classical
  intro n A a d b hab F hF hpF huniq hd
  let FL := insert d (F.erase b)
  let FR := insert d (F.erase a)
  have hFL : FL ∉ A := by
    intro h
    have : d ∈ FL := Finset.mem_insert_self _ _
    exact hd FL h this
  have hFR : FR ∉ A := by
    intro h
    have : d ∈ FR := Finset.mem_insert_self _ _
    exact hd FR h this
  have hFLFR : FL ≠ FR := by
    intro h
    have hda : d ≠ a := by intro hda; subst d; exact hd F hF hpF.1
    have haFL : a ∈ FL := Finset.mem_insert.mpr
      (Or.inr (Finset.mem_erase.mpr ⟨hab, hpF.1⟩))
    have haFR : a ∉ FR := by simp [FR, hda.symm]
    exact haFR (h ▸ haFL)
  ext G
  constructor
  · intro hG
    change G ∈ A.biUnion (fun H =>
      if a ∈ H ∧ b ∈ H then {insert d (H.erase b), insert d (H.erase a)} else {H}) at hG
    rw [Finset.mem_biUnion] at hG
    rcases hG with ⟨H, hH, hGH⟩
    by_cases hp : a ∈ H ∧ b ∈ H
    · have hEq := huniq H hH hp
      subst H
      simp only [hpF, and_self, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hGH
      rcases hGH with rfl | rfl
      · simp [FL, FR, hFL, hFLFR]
      · simp [FR, hFR]
    · simp [hp] at hGH
      subst G
      have hHF : H ≠ F := by
        intro h
        subst H
        exact hp ⟨hpF.1, hpF.2⟩
      simp [Finset.mem_erase, hHF, hH]
  · intro hG
    rw [Finset.mem_union] at hG
    rcases hG with hG | hG
    · rw [Finset.mem_erase] at hG
      rcases hG with ⟨hGF, hG⟩
      have hn : ¬(a ∈ G ∧ b ∈ G) := by
        intro hp
        exact hGF (huniq G hG hp)
      change G ∈ A.biUnion (fun H =>
        if a ∈ H ∧ b ∈ H then {insert d (H.erase b), insert d (H.erase a)} else {H})
      rw [Finset.mem_biUnion]
      refine ⟨G, hG, ?_⟩
      simp [hn]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hG
      rcases hG with hG | hG
      · subst G
        change insert d (F.erase b) ∈ A.biUnion (fun H =>
          if a ∈ H ∧ b ∈ H then {insert d (H.erase b), insert d (H.erase a)} else {H})
        rw [Finset.mem_biUnion]
        refine ⟨F, hF, ?_⟩
        simp [hpF]
      · subst G
        change insert d (F.erase a) ∈ A.biUnion (fun H =>
          if a ∈ H ∧ b ∈ H then {insert d (H.erase b), insert d (H.erase a)} else {H})
        rw [Finset.mem_biUnion]
        refine ⟨F, hF, ?_⟩
        simp [hpF]

private theorem hsplit_filter_card :
    (by
      classical
      exact
        ∀ (n : Nat), (∀ (A : Finset (Finset (Fin (n + 3)))), ∀ (a : Fin (n + 3)), ∀ (d : Fin (n +
        3)), ∀ (b : Fin (n + 3)), (a ≠ b) → (∀ (F : Finset (Fin (n + 3))), (F ∈ A) → ((a ∈ F ∧ b
        ∈ F) → ((∀ G ∈ A, a ∈ G ∧ b ∈ G → G = F) → ((∀ G ∈ A, d ∉ G) →
        (P3523T1BoundaryFaceSplit A a d b = A.erase F ∪ {insert d (F.erase b),
        insert d (F.erase a)})))))) → (∀ (A : Finset (Finset (Fin (n + (3 : ℕ))))), ∀ (a : Fin (n
        + (3 : ℕ))), ∀ (d : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), a ≠ b → ∀ F ∈ A, a ∈ F
        ∧ b ∈ F → (∀ G ∈ A, a ∈ G ∧ b ∈ G → G = F) → (∀ G ∈ A, d ∉ G) → ∀ (P : Finset (Fin (n +
        (3 : ℕ))) → Prop), ∀ [inst : DecidablePred P], (Finset.filter P
        (P3523T1BoundaryFaceSplit A a d b)).card = ((Finset.filter P (A.erase F)).card + if P
        (insert d (F.erase b)) then (1 : ℕ) else (0 : ℕ)) + if P (insert d (F.erase a)) then (1 :
        ℕ) else (0 : ℕ)) ) := by
  classical
  intro n hsplit_eq A a d b hab F hF hpF huniq hd P typeclassInstance0
  have heq := hsplit_eq A a d b hab F hF hpF huniq hd
  have hFL : insert d (F.erase b) ∉ A := by
    intro h
    exact hd _ h (Finset.mem_insert_self _ _)
  have hFR : insert d (F.erase a) ∉ A := by
    intro h
    exact hd _ h (Finset.mem_insert_self _ _)
  have hneq : insert d (F.erase b) ≠ insert d (F.erase a) := by
    intro h
    have hda : d ≠ a := by intro hda; subst d; exact hd F hF hpF.1
    have haL : a ∈ insert d (F.erase b) :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hab, hpF.1⟩))
    have haR : a ∉ insert d (F.erase a) := by simp [hda.symm]
    exact haR (h ▸ haL)
  have hDisj : Disjoint ((A.erase F).filter P)
      (({insert d (F.erase b), insert d (F.erase a)} : Finset (Finset (Fin (n + 3)))).filter P)
          := by
    apply Finset.disjoint_left.mpr
    intro G hG1 hG2
    rcases Finset.mem_filter.mp hG1 with ⟨hG1, _⟩
    rcases Finset.mem_filter.mp hG2 with ⟨hG2, _⟩
    have hGA : G ∈ A := Finset.mem_of_mem_erase hG1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hG2
    rcases hG2 with hG2 | hG2
    · subst G
      exact hFL hGA
    · subst G
      exact hFR hGA
  rw [heq, Finset.filter_union, Finset.card_union_of_disjoint hDisj]
  by_cases h1 : P (insert d (F.erase b)) <;>
    by_cases h2 : P (insert d (F.erase a)) <;>
      simp [Finset.filter_insert, Finset.filter_singleton, h1, h2, hneq]

private theorem herase_filter_card :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (A : Finset (Finset (Fin (n + (3 : ℕ))))), ∀ F ∈ A, ∀ (P : Finset (Fin (n
            + (3
        : ℕ))) → Prop), ∀ [inst : DecidablePred P], (Finset.filter P A).card = (Finset.filter P
        (A.erase F)).card + if P F then (1 : ℕ) else (0 : ℕ) ) := by
  classical
  intro n A F hF P typeclassInstance0
  have heq : A.filter P = (A.erase F).filter P ∪ ({F} : Finset (Finset (Fin (n + 3)))).filter P
      := by
    ext G
    by_cases hGF : G = F <;> simp [hGF, hF]
  have hdisj : Disjoint ((A.erase F).filter P)
      (({F} : Finset (Finset (Fin (n + 3)))).filter P) := by
    apply Finset.disjoint_left.mpr
    intro G hG1 hG2
    rcases Finset.mem_filter.mp hG1 with ⟨hG1, _⟩
    rcases Finset.mem_filter.mp hG2 with ⟨hG2, _⟩
    exact (Finset.mem_erase.mp hG1).1 (by simpa using hG2)
  rw [heq, Finset.card_union_of_disjoint hdisj]
  by_cases hPF : P F <;> simp [Finset.filter_singleton, hPF]

private theorem hfilter_exists_iff_pos :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (A : Finset (Finset (Fin (n + (3 : ℕ))))), ∀ (P : Finset (Fin (n + (3 :
            ℕ))) →
        Prop), ∀ [inst : DecidablePred P], (∃ F ∈ A, P F) ↔ (0 : ℕ) < (Finset.filter P A).card )
            := by
  classical
  intro n A P typeclassInstance0
  constructor
  · rintro ⟨F, hF, hP⟩
    apply Finset.card_pos.mpr
    exact ⟨F, Finset.mem_filter.mpr ⟨hF, hP⟩⟩
  · intro hpos
    obtain ⟨F, hF⟩ := Finset.card_pos.mp hpos
    exact ⟨F, (Finset.mem_filter.mp hF).1, (Finset.mem_filter.mp hF).2⟩

private theorem old_pair_split_indicators :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b : Fin (n + (3 : ℕ))), ∀ (z : Fin (n + (3 :
            ℕ))), ∀ (d : Fin (n + (3 : ℕ))), ∀ (x : Fin (n + (3 : ℕ))), ∀ (y : Fin (n + (3 :
            ℕ))), a ≠ b →
        a ≠ z → b ≠ z → x ≠ y → x ≠ d → y ≠ d → (if x ∈ ({a, b, z} : Finset (Fin (n + 3))) ∧ y ∈
        ({a, b, z} : Finset (Fin (n + 3))) then (1 : ℕ)
        else (0 : ℕ)) = ((if x ∈ ({a, d, z} : Finset (Fin (n + 3))) ∧ y ∈ ({a, d, z} : Finset
        (Fin (n + 3))) then (1 : ℕ) else (0 : ℕ)) + if x ∈
        ({d, b, z} : Finset (Fin (n + 3))) ∧ y ∈ ({d, b, z} : Finset (Fin (n + 3))) then (1 : ℕ)
        else (0 : ℕ)) + if x = a ∧ y = b ∨ x = b ∧ y = a
        then (1 : ℕ) else (0 : ℕ) ) := by
  classical
  intro n a b z d x y hab haz hbz hxy hxd hyd
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hxz : x = z <;> by_cases hya : y = a <;>
    by_cases hyb : y = b <;> by_cases hyz : y = z <;>
    simp_all [Finset.mem_insert, Finset.mem_singleton]

private theorem old_boundary_membership :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (B : Finset (Finset (Fin (n + (3 : ℕ))))), ∀ (a : Fin (n + (3 : ℕ))), ∀ (b
            : Fin (n + (3 : ℕ))), ∀ (d : Fin (n + (3 : ℕ))), ∀ (x : Fin (n + (3 : ℕ))), ∀ (y :
            Fin (n +
        (3 : ℕ))), x ≠ d → y ≠ d → (({x, y} : Finset (Fin (n + 3))) ∈ insert ({a, d} : Finset
        (Fin (n + 3))) (insert ({d, b} : Finset (Fin (n + 3))) (B.erase ({a, b} : Finset (Fin
        (n + 3))))) ↔ {x,
        y} ∈ B ∧ ({x, y} : Finset (Fin (n + 3))) ≠ ({a, b} : Finset (Fin (n + 3)))) ) := by
  classical
  intro n B a b d x y hxd hyd
  have hleft : ({x, y} : Finset _) ≠ {a, d} := by
    intro h
    have hdmem : d ∈ ({x, y} : Finset _) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
    exact hdmem.elim (fun h => hxd h.symm) (fun h => hyd h.symm)
  have hright : ({x, y} : Finset _) ≠ {d, b} := by
    intro h
    have hdmem : d ∈ ({x, y} : Finset _) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
    exact hdmem.elim (fun h => hxd h.symm) (fun h => hyd h.symm)
  simp only [Finset.mem_insert, Finset.mem_erase, hleft, hright, false_or]
  exact and_comm

private theorem hledger :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ (h : ℕ), ∀ (hh : h < (P3523T1InsertionConstruction s t).steps.length),
        let e :=
        (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
        (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈ (P3523T1InsertionConstruction
        s t).vertices h ∧ e.2.1 ∉ (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2}
        ∈ (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ)
        ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
        P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s t
        e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → ((∀ (h : Nat), ∀ (hh : h <
        c.steps.length), c.faces (h + 1) = P3523T1BoundaryFaceSplit (c.faces h) (c.steps.get
        ⟨h, hh⟩).1 (c.steps.get ⟨h, hh⟩).2.1 (c.steps.get ⟨h, hh⟩).2.2) → ((∀ (h : Nat), ∀ (hh :
            h < c.steps.length), c.boundary (h + 1) = insert {(c.steps.get ⟨h, hh⟩).1,
        (c.steps.get ⟨h, hh⟩).2.1} (insert {(c.steps.get ⟨h, hh⟩).2.1, (c.steps.get ⟨h, hh⟩).2.2}
        ((c.boundary h).erase {(c.steps.get ⟨h, hh⟩).1, (c.steps.get ⟨h, hh⟩).2.2}))) → ((∀ h :
        Nat, h ≤ c.steps.length → ∀ F ∈ c.faces h, F.card = 3 ∧ F ⊆ c.vertices h) → ((∀ h : Nat,
        h ≤ c.steps.length → ∀ P ∈ c.boundary h, ∀ x ∈ P, x ∈ c.vertices h) → ((∀ (F : Finset
        (Fin (n + 3))), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), (a ≠ b) → ((F.card = 3) → ((a ∈
        F) → ((b ∈ F) → (∃ x, x ≠ a ∧ x ≠ b ∧ F = {a, b, x}))))) → ((∀ {α : Type}, ∀ [DecidableEq
        α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), (a ≠ b) → ((c ≠ d) → (({a, b} : Finset α)
        = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)))) → ((∀ a b : Fin (n + 3), a ≠ b →
        ((c.faces 0).filter (fun F => a ∈ F ∧ b ∈ F)).card = if {a, b} ∈ c.boundary 0 then 1 else
        if ∃ F ∈ c.faces 0, a ∈ F ∧ b ∈ F then 2 else 0) → ((∀ (A : Finset (Finset (Fin (n +
        3)))), ∀ (a : Fin (n + 3)), ∀ (d : Fin (n + 3)), ∀ (b : Fin (n + 3)), (a ≠ b) → (∀ (F :
            Finset (Fin (n + 3))), (F ∈ A) → ((a ∈ F ∧ b ∈ F) → ((∀ G ∈ A, a ∈ G ∧ b ∈ G → G = F) →
        ((∀ G ∈ A, d ∉ G) → (∀ (P : Finset (Fin (n + 3)) → Prop), ∀ [DecidablePred P],
            ((P3523T1BoundaryFaceSplit A a d b).filter P).card = ((A.erase F).filter P).card + (if
        P (insert d (F.erase b)) then 1 else 0) + (if P (insert d (F.erase a)) then 1 else
        0))))))) → ((∀ (A : Finset (Finset (Fin (n + 3)))), ∀ (F : Finset (Fin (n + 3))), (F ∈ A)
        → (∀ (P : Finset (Fin (n + 3)) → Prop), ∀ [DecidablePred P], (A.filter P).card =
        ((A.erase F).filter P).card + if P F then 1 else 0)) → ((∀ (A : Finset (Finset (Fin (n +
        3)))), ∀ (P : Finset (Fin (n + 3)) → Prop), ∀ [DecidablePred P], (∃ F ∈ A, P F) ↔ 0 <
        (A.filter P).card) → ((∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (z : Fin (n + 3)), ∀
            (d : Fin (n + 3)), ∀ (x : Fin (n + 3)), ∀ (y : Fin (n + 3)), (a ≠ b) → ((a ≠ z) → ((b ≠
        z) → ((x ≠ y) → ((x ≠ d) → ((y ≠ d) → ((if x ∈ ({a, b, z} : Finset _) ∧ y ∈ ({a, b, z} :
        Finset _) then 1 else 0 : Nat) = (if x ∈ ({a, d, z} : Finset _) ∧ y ∈ ({a, d, z} : Finset
        _) then 1 else 0) + (if x ∈ ({d, b, z} : Finset _) ∧ y ∈ ({d, b, z} : Finset _) then 1
        else 0) + (if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then 1 else 0)))))))) → ((∀ (B : Finset
        (Finset (Fin (n + 3)))), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), ∀ (d : Fin (n + 3)), ∀
            (x : Fin (n + 3)), ∀ (y : Fin (n + 3)), (x ≠ d) → ((y ≠ d) → (({x, y} : Finset _) ∈
        insert {a, d} (insert {d, b} (B.erase {a, b})) ↔ ({x, y} : Finset _) ∈ B ∧ ({x, y} :
        Finset _) ≠ {a, b}))) → ((∀ (A : Finset (Finset (Fin (n + 3)))), ∀ (x : Fin (n + 3)), ∀
            (y : Fin (n + 3)), (A.filter (fun F => x ∈ F ∧ y ∈ F)).card = (A.filter (fun F => y ∈
            F ∧
        x ∈ F)).card) → ((∀ (old : Nat), ∀ (new : Nat), ∀ (onBoundary : Prop), ∀ (removed :
            Prop), ∀ [Decidable onBoundary], ∀ [Decidable removed], (old = if onBoundary then 1 else
        if 0 < old then 2 else 0) → ((removed → onBoundary) → ((old = new + (if removed then 1
        else 0)) → (new = if onBoundary ∧ ¬ removed then 1 else if 0 < new then 2 else 0)))) → (∀
        h : Nat, h ≤ c.steps.length → ∀ a b : Fin (n + 3), a ≠ b → ((c.faces h).filter (fun F =>
        a ∈ F ∧ b ∈ F)).card = if {a, b} ∈ c.boundary h then 1 else if ∃ F ∈ c.faces h, a ∈ F ∧ b
        ∈ F then 2 else 0))))))))))))))) ) := by
  classical
  intro r n q p s X K t c hsteps hfaces_next hboundary_next hstage hboundary_support hthird
      pair_eq_pair hinit_ledger hsplit_filter_card herase_filter_card hfilter_exists_iff_pos
      old_pair_split_indicators old_boundary_membership pair_filter_card_symmetry
      old_pair_ledger_transfer h hh
  induction h with
  | zero => exact hinit_ledger
  | succ h ih =>
      have hlt : h < c.steps.length := by omega
      have ih' := ih (by omega)
      let e := c.steps.get ⟨h, hlt⟩
      have he := hsteps h hlt
      dsimp [e] at he
      rcases he with ⟨hab, ha, hb, hd, hEdge, _⟩
      change e.1 ≠ e.2.2 at hab
      change e.1 ∈ c.vertices h at ha
      change e.2.2 ∈ c.vertices h at hb
      change e.2.1 ∉ c.vertices h at hd
      change {e.1, e.2.2} ∈ c.boundary h at hEdge
      have hcountAB : ((c.faces h).filter
          (fun G => e.1 ∈ G ∧ e.2.2 ∈ G)).card = 1 := by
        have hprev := ih' e.1 e.2.2 hab
        rw [ite_eq_left hEdge] at hprev
        exact hprev
      rcases Finset.card_eq_one.mp hcountAB with ⟨F, hfilter⟩
      have hFfilter : F ∈ (c.faces h).filter
          (fun G => e.1 ∈ G ∧ e.2.2 ∈ G) := by
        rw [hfilter]
        simp
      rcases Finset.mem_filter.mp hFfilter with ⟨hF, hpF⟩
      have huniq : ∀ G ∈ c.faces h, e.1 ∈ G ∧ e.2.2 ∈ G → G = F := by
        intro G hG hp
        have hGfilter : G ∈ (c.faces h).filter
            (fun H => e.1 ∈ H ∧ e.2.2 ∈ H) := Finset.mem_filter.mpr ⟨hG, hp⟩
        rw [hfilter] at hGfilter
        simpa using hGfilter
      have hdFaces : ∀ G ∈ c.faces h, e.2.1 ∉ G := by
        intro G hG hdG
        exact hd ((hstage h (by omega) G hG).2 hdG)
      have hthirdF := hthird F e.1 e.2.2 hab
        (hstage h (by omega) F hF).1 hpF.1 hpF.2
      rcases hthirdF with ⟨z, hza, hzb, hFtriple⟩
      let A := c.faces h
      let N := P3523T1BoundaryFaceSplit A e.1 e.2.1 e.2.2
      let B := insert {e.1, e.2.1}
        (insert {e.2.1, e.2.2} ((c.boundary h).erase {e.1, e.2.2}))
      have hda : e.2.1 ≠ e.1 := by
        intro heq
        exact hd (heq ▸ ha)
      have hdb : e.2.1 ≠ e.2.2 := by
        intro heq
        exact hd (heq ▸ hb)
      have hzF : z ∈ F := by rw [hFtriple]; simp
      have hdz : e.2.1 ≠ z := by
        intro heq
        exact hd (heq ▸ (hstage h (by omega) F hF).2 hzF)
      have hleftTriple : insert e.2.1 (F.erase e.2.2) = {e.1, e.2.1, z} := by
        clear * - e F z hab hza hzb hFtriple
        rw [hFtriple]
        ext w
        by_cases hwa : w = e.1 <;> by_cases hwb : w = e.2.2 <;>
          by_cases hwz : w = z <;>
          simp_all [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
      have hrightTriple : insert e.2.1 (F.erase e.1) = {e.2.1, e.2.2, z} := by
        clear * - e F z hab hza hzb hFtriple
        rw [hFtriple]
        ext w
        by_cases hwa : w = e.1 <;> by_cases hwb : w = e.2.2 <;>
          by_cases hwz : w = z <;>
          simp_all [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
      have hnoB (w : Fin (n + 3)) : {e.2.1, w} ∉ c.boundary h := by
        intro hP
        exact hd (hboundary_support h (by omega) {e.2.1, w} hP e.2.1 (by simp))
      -- The fresh label occurs only in the two replacement faces.
      have hcountFresh (w : Fin (n + 3)) (hdw : e.2.1 ≠ w) :
          (N.filter (fun G => e.2.1 ∈ G ∧ w ∈ G)).card =
            (if w = e.1 ∨ w = z then 1 else 0) +
            (if w = e.2.2 ∨ w = z then 1 else 0) := by
        have hzero : ((A.erase F).filter
            (fun G => e.2.1 ∈ G ∧ w ∈ G)).card = 0 := by
          have hempty : (A.erase F).filter
              (fun G => e.2.1 ∈ G ∧ w ∈ G) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro G hG hp
            exact hdFaces G (Finset.mem_of_mem_erase hG) hp.1
          rw [hempty, Finset.card_empty]
        dsimp only [N]
        rw [hsplit_filter_card A e.1 e.2.1 e.2.2 hab F hF hpF huniq hdFaces,
          hzero, hleftTriple, hrightTriple]
        simp [hdw.symm, hda, hdb, hdz]
      have hboundaryFresh (w : Fin (n + 3)) (hdw : e.2.1 ≠ w) :
          {e.2.1, w} ∈ B ↔ w = e.1 ∨ w = e.2.2 := by
        have hleft := pair_eq_pair e.2.1 w e.1 e.2.1 hdw hda.symm
        have hright := pair_eq_pair e.2.1 w e.2.1 e.2.2 hdw hdb
        dsimp only [B]
        simp only [Finset.mem_insert, Finset.mem_erase]
        simp [hleft, hright, hda, hdb, hnoB w]
      have hfresh (w : Fin (n + 3)) (hdw : e.2.1 ≠ w) :
          (N.filter (fun G => e.2.1 ∈ G ∧ w ∈ G)).card =
            if {e.2.1, w} ∈ B then 1
            else if 0 < (N.filter (fun G => e.2.1 ∈ G ∧ w ∈ G)).card then 2 else 0 := by
        simp only [hboundaryFresh w hdw, hcountFresh w hdw]
        by_cases hwa : w = e.1
        · subst w
          simp [hab, hza.symm]
        · by_cases hwb : w = e.2.2
          · subst w
            simp [hab.symm, hzb.symm]
          · by_cases hwz : w = z
            · subst w
              simp [hza, hzb]
            · simp [hwa, hwb, hwz]
      intro x y hxy
      rw [hfaces_next h hlt, hboundary_next h hlt]
      change (N.filter (fun G => x ∈ G ∧ y ∈ G)).card =
        if {x, y} ∈ B then 1
        else if ∃ G ∈ N, x ∈ G ∧ y ∈ G then 2 else 0
      simp only [hfilter_exists_iff_pos N (fun G => x ∈ G ∧ y ∈ G)]
      by_cases hxd : x = e.2.1
      · subst x
        exact hfresh y hxy
      · by_cases hyd : y = e.2.1
        · subst y
          rw [pair_filter_card_symmetry N x e.2.1, Finset.pair_comm x e.2.1]
          exact hfresh x hxy.symm
        · have hindicator := old_pair_split_indicators e.1 e.2.2 z e.2.1 x y
            hab hza.symm hzb.symm hxy hxd hyd
          simp only [← hFtriple, ← hleftTriple, ← hrightTriple,
            ← pair_eq_pair x y e.1 e.2.2 hxy hab] at hindicator
          have herase := herase_filter_card A F hF (fun G => x ∈ G ∧ y ∈ G)
          have hsplit := hsplit_filter_card A e.1 e.2.1 e.2.2
            hab F hF hpF huniq hdFaces (fun G => x ∈ G ∧ y ∈ G)
          have hdelta : (A.filter (fun G => x ∈ G ∧ y ∈ G)).card =
              (N.filter (fun G => x ∈ G ∧ y ∈ G)).card +
                if ({x, y} : Finset (Fin (n + 3))) = {e.1, e.2.2} then 1 else 0 := by
            dsimp only [N]
            omega
          have hprev := ih' x y hxy
          change (A.filter (fun G => x ∈ G ∧ y ∈ G)).card =
            if {x, y} ∈ c.boundary h then 1
            else if ∃ G ∈ A, x ∈ G ∧ y ∈ G then 2 else 0 at hprev
          simp only [hfilter_exists_iff_pos A (fun G => x ∈ G ∧ y ∈ G)] at hprev
          have hremove : ({x, y} : Finset _) = {e.1, e.2.2} →
              {x, y} ∈ c.boundary h := by
            intro heq
            rw [heq]
            exact hEdge
          have hboundaryOld := old_boundary_membership
            (c.boundary h) e.1 e.2.2 e.2.1 x y hxd hyd
          change ({x, y} ∈ B ↔ _) at hboundaryOld
          simp only [hboundaryOld]
          exact old_pair_ledger_transfer _ _ _ _ hprev hremove hdelta

private theorem hselected_face :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ (h : ℕ), ∀ (hh : h < (P3523T1InsertionConstruction s t).steps.length),
        let e :=
        (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
        (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈ (P3523T1InsertionConstruction
        s t).vertices h ∧ e.2.1 ∉ (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2}
        ∈ (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ)
        ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
        P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s t
        e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → ((∀ h : Nat, h ≤ c.steps.length → ∀ a
        b : Fin (n + 3), a ≠ b → ((c.faces h).filter (fun F => a ∈ F ∧ b ∈ F)).card = if {a, b} ∈
        c.boundary h then 1 else if ∃ F ∈ c.faces h, a ∈ F ∧ b ∈ F then 2 else 0) → (∀ (h : ℕ), ∀
            (hh : h < c.steps.length), ∃ F ∈ c.faces h, (c.steps.get ⟨h, hh⟩).1 ∈ F ∧ (c.steps.get
        ⟨h, hh⟩).2.2 ∈ F)) ) := by
  classical
  intro r n q p s X K t c hsteps hledger h hh
  let e := c.steps.get ⟨h, hh⟩
  have he := hsteps h hh
  dsimp [e] at he
  rcases he with ⟨hab, _, _, _, hEdge, _⟩
  change {e.1, e.2.2} ∈ c.boundary h at hEdge
  have hcount := hledger h (by omega) e.1 e.2.2 hab
  rw [ite_eq_left hEdge] at hcount
  have hpos : 0 < ((c.faces h).filter
      (fun F => e.1 ∈ F ∧ e.2.2 ∈ F)).card := by omega
  obtain ⟨F, hF⟩ := Finset.card_pos.mp hpos
  exact ⟨F, (Finset.mem_filter.mp hF).1, (Finset.mem_filter.mp hF).2.1,
    (Finset.mem_filter.mp hF).2.2⟩

private theorem husage :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ (h : ℕ), ∀ (hh : h < (P3523T1InsertionConstruction s t).steps.length),
        let e :=
        (P3523T1InsertionConstruction s t).steps.get ⟨h, hh⟩; e.1 ≠ e.2.2 ∧ e.1 ∈
        (P3523T1InsertionConstruction s t).vertices h ∧ e.2.2 ∈ (P3523T1InsertionConstruction
        s t).vertices h ∧ e.2.1 ∉ (P3523T1InsertionConstruction s t).vertices h ∧ {e.1, e.2.2}
        ∈ (P3523T1InsertionConstruction s t).boundary h ∧ ∃ (u : ℝ), (0 : ℝ) < u ∧ u < (1 : ℝ)
        ∧ p.vertex e.2.1 = ((1 : ℝ) - u) • p.vertex e.1 + u • p.vertex e.2.2 ∧
        P3523T1InterpolatedTarget s t e.2.1 = ((1 : ℝ) - u) • P3523T1InterpolatedTarget s t
        e.1 + u • P3523T1InterpolatedTarget s t e.2.2) → ((∀ (h : Nat), ∀ (hh : h <
        c.steps.length), c.faces (h + 1) = P3523T1BoundaryFaceSplit (c.faces h) (c.steps.get
        ⟨h, hh⟩).1 (c.steps.get ⟨h, hh⟩).2.1 (c.steps.get ⟨h, hh⟩).2.2) → ((∀ (h : Nat), ∀ (hh :
            h < c.steps.length), c.vertices (h + 1) = insert (c.steps.get ⟨h, hh⟩).2.1 (c.vertices
        h)) → ((∀ h : Nat, h ≤ c.steps.length → ∀ F ∈ c.faces h, F.card = 3 ∧ F ⊆ c.vertices h) →
        ((∀ (F : Finset (Fin (n + 3))), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n + 3)), (a ≠ b) →
        ((F.card = 3) → ((a ∈ F) → ((b ∈ F) → (∃ x, x ≠ a ∧ x ≠ b ∧ F = {a, b, x}))))) → ((∀ x ∈
        c.vertices 0, ∃ i : Fin (r + 3), s.start i = x) → ((∀ h : Nat, h ≤ c.steps.length → ∀ a b
        : Fin (n + 3), a ≠ b → ((c.faces h).filter (fun F => a ∈ F ∧ b ∈ F)).card = if {a, b} ∈
        c.boundary h then 1 else if ∃ F ∈ c.faces h, a ∈ F ∧ b ∈ F then 2 else 0) → ((∀ (h :
            Nat), ∀ (hh : h < c.steps.length), ∃ F ∈ c.faces h, (c.steps.get ⟨h, hh⟩).1 ∈ F ∧
        (c.steps.get ⟨h, hh⟩).2.2 ∈ F) → (∀ h : Nat, h ≤ c.steps.length → ∀ x ∈ c.vertices h, ∃ F
        ∈ c.faces h, x ∈ F)))))))) ) := by
  classical
  intro r n q p s X K t c hsteps hfaces_next hvertices_next hstage hthird hvertex0_start hledger
      hselected_face h hh
  induction h with
  | zero =>
      intro x hx
      rcases hvertex0_start x hx with ⟨i, rfl⟩
      rcases t.vertex_used i with ⟨k, j, hj⟩
      refine ⟨Finset.univ.image (s.start ∘ t.face k), ?_, ?_⟩
      · change _ ∈ Finset.univ.image (fun k : Fin t.count =>
          Finset.univ.image (s.start ∘ t.face k))
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg s.start hj⟩
  | succ h ih =>
      have hlt : h < c.steps.length := by omega
      have ih' := ih (by omega)
      let e := c.steps.get ⟨h, hlt⟩
      have he := hsteps h hlt
      dsimp [e] at he
      rcases he with ⟨hab, ha, hb, hd, _, _⟩
      obtain ⟨F, hF, hFa, hFb⟩ := hselected_face h hlt
      have huniq : ∀ G ∈ c.faces h, e.1 ∈ G ∧ e.2.2 ∈ G → G = F := by
        intro G hG hp
        have hcnt := hledger h (by omega) e.1 e.2.2 hab
        have hEdge := (hsteps h hlt).2.2.2.2.1
        change {e.1, e.2.2} ∈ c.boundary h at hEdge
        rw [ite_eq_left hEdge] at hcnt
        have hGmem : G ∈ (c.faces h).filter
            (fun H => e.1 ∈ H ∧ e.2.2 ∈ H) := Finset.mem_filter.mpr ⟨hG, hp⟩
        have hFmem : F ∈ (c.faces h).filter
            (fun H => e.1 ∈ H ∧ e.2.2 ∈ H) := Finset.mem_filter.mpr ⟨hF, ⟨hFa, hFb⟩⟩
        rcases Finset.card_eq_one.mp hcnt with ⟨H, hH⟩
        have hG' : G ∈ ({H} : Finset (Finset (Fin (n + 3)))) := by
          rw [← hH]
          exact hGmem
        have hF' : F ∈ ({H} : Finset (Finset (Fin (n + 3)))) := by
          rw [← hH]
          exact hFmem
        have hGH : G = H := by simpa using hG'
        have hFH : F = H := by simpa using hF'
        exact hGH.trans hFH.symm
      intro x hx
      rw [hvertices_next h hlt] at hx
      simp only [Finset.mem_insert] at hx
      rcases hx with hx | hx
      · subst x
        rcases hthird F e.1 e.2.2 hab (hstage h (by omega) F hF).1 hFa hFb with
          ⟨z, hza, hzb, hFtriple⟩
        refine ⟨insert e.2.1 (F.erase e.2.2), ?_, ?_⟩
        · rw [hfaces_next h hlt]
          change insert e.2.1 (F.erase e.2.2) ∈
            (c.faces h).biUnion (fun G =>
              if e.1 ∈ G ∧ e.2.2 ∈ G then
                {insert e.2.1 (G.erase e.2.2), insert e.2.1 (G.erase e.1)} else {G})
          rw [Finset.mem_biUnion]
          refine ⟨F, hF, ?_⟩
          rw [ite_eq_left ⟨hFa, hFb⟩]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_self _ _
      · rcases ih' x hx with ⟨G, hG, hxG⟩
        by_cases hGF : G = F
        · subst G
          rcases hthird F e.1 e.2.2 hab (hstage h (by omega) F hF).1 hFa hFb with
            ⟨z, hza, hzb, hFtriple⟩
          have hxCases : x = e.1 ∨ x = e.2.2 ∨ x = z := by
            rw [hFtriple] at hxG
            simpa only [Finset.mem_insert, Finset.mem_singleton] using hxG
          rcases hxCases with hxA | hxB | hxZ
          · subst x
            refine ⟨insert e.2.1 (F.erase e.2.2), ?_, ?_⟩
            · rw [hfaces_next h hlt]
              change insert e.2.1 (F.erase e.2.2) ∈ (c.faces h).biUnion _
              rw [Finset.mem_biUnion]
              refine ⟨F, hF, ?_⟩
              rw [ite_eq_left ⟨hFa, hFb⟩]
              exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert.mpr (Or.inr
                (Finset.mem_erase.mpr ⟨hab, hFa⟩))
          · subst x
            refine ⟨insert e.2.1 (F.erase e.1), ?_, ?_⟩
            · rw [hfaces_next h hlt]
              change insert e.2.1 (F.erase e.1) ∈ (c.faces h).biUnion _
              rw [Finset.mem_biUnion]
              refine ⟨F, hF, ?_⟩
              rw [ite_eq_left ⟨hFa, hFb⟩]
              exact Finset.mem_insert.mpr (Or.inr
                (Finset.mem_singleton.mpr rfl))
            · exact Finset.mem_insert.mpr (Or.inr
                (Finset.mem_erase.mpr ⟨(fun hba => hab hba.symm), hFb⟩))
          · subst x
            refine ⟨insert e.2.1 (F.erase e.2.2), ?_, ?_⟩
            · rw [hfaces_next h hlt]
              change insert e.2.1 (F.erase e.2.2) ∈ (c.faces h).biUnion _
              rw [Finset.mem_biUnion]
              refine ⟨F, hF, ?_⟩
              rw [ite_eq_left ⟨hFa, hFb⟩]
              exact Finset.mem_insert_self _ _
            · have hzF : z ∈ F := by rw [hFtriple]; simp
              exact Finset.mem_insert.mpr (Or.inr
                (Finset.mem_erase.mpr ⟨hzb, hzF⟩))
        · have hnot : ¬(e.1 ∈ G ∧ e.2.2 ∈ G) := by
            intro hp
            exact hGF (huniq G hG hp)
          refine ⟨G, ?_, hxG⟩
          rw [hfaces_next h hlt]
          change G ∈ (c.faces h).biUnion _
          rw [Finset.mem_biUnion]
          refine ⟨G, hG, ?_⟩
          change G ∈ (if e.1 ∈ G ∧ e.2.2 ∈ G then
            {insert e.2.1 (G.erase e.2.2), insert e.2.1 (G.erase e.1)} else {G})
          rw [ite_eq_right hnot]
          simp

end InsertionIncidenceProof

namespace InsertionDetails

private theorem hinner :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (k
            : Fin t.count), (Finset.image (s.start ∘ t.face k) Finset.univ).card = (3 : ℕ) ) := by
  classical
  intro r n q p s X K t k
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply t.face_injective k
    exact s.start_injective hij

private theorem hinit :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ (k : Fin t.count), (Finset.univ.image (s.start ∘ t.face k)).card = 3) → (∀ F ∈ c.faces
            0, F.card = 3) ) := by
  classical
  intro r n q p s X K t c hinner F hF
  change F ∈ Finset.univ.image
    (fun k : Fin t.count => Finset.univ.image (s.start ∘ t.face k)) at hF
  rcases Finset.mem_image.mp hF with ⟨k, -, rfl⟩
  exact hinner k

private theorem hinit_sub :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ F ∈ c.faces 0, F ⊆ c.vertices 0 ) := by
  classical
  intro r n q p s X K t c F hF x hx
  change F ∈ Finset.univ.image
    (fun k : Fin t.count => Finset.univ.image (s.start ∘ t.face k)) at hF
  rcases Finset.mem_image.mp hF with ⟨k, -, rfl⟩
  change x ∈ Finset.univ.image (s.start ∘ t.face k) at hx
  rcases Finset.mem_image.mp hx with ⟨j, -, rfl⟩
  change s.start (t.face k j) ∈ Finset.univ.image s.start
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

private theorem hvertices_next :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ (h : ℕ), ∀ (hh : h < c.steps.length), c.vertices (h + (1 : ℕ)) = insert (c.steps.get
            ⟨h, hh⟩).2.1 (c.vertices h) ) := by
  classical
  intro r n q p s X K t c h hh
  change (c.steps.take (h + 1)).foldl
      (fun vs e => insert e.2.1 vs) (Finset.univ.image s.start) =
    insert (c.steps.get ⟨h, hh⟩).2.1
      ((c.steps.take h).foldl (fun vs e => insert e.2.1 vs) (Finset.univ.image s.start))
  rw [← List.take_append_getElem hh]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [List.get_eq_getElem]

private theorem hfinal_card :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ h : Nat, h ≤ c.steps.length → ∀ F ∈ c.faces h, F.card = 3 ∧ F ⊆ c.vertices h) → (
        let fs := c.faces c.steps.length
        ∀ F ∈ fs, F.card = 3) ) := by
  classical
  intro r n q p s X K t c hstage fs F hF
  exact (hstage c.steps.length le_rfl F hF).1

private theorem hf_spec :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        let fs := c.faces c.steps.length
        let f := P3523T1FaceEnumeration fs
        (∀ (k : Fin fs.card), ∃ g : Fin 3 → Fin (n + 3), Function.Injective g ∧ Set.range g =
            ((fs.equivFin.symm k).val : Set (Fin (n + 3)))) → (∀ (k : Fin fs.card),
            Function.Injective (f k) ∧ Set.range (f k) = (↑(↑((fs.equivFin.symm : Fin fs.card →
            ↥fs) k) : Finset (Fin (n + (3 : ℕ)))) : Set (Fin (n + (3 : ℕ))))) ) := by
  classical
  intro r n q p s X K t c fs f hfaceChoice k
  have hh := hfaceChoice k
  dsimp [f, P3523T1FaceEnumeration]
  rw [dite_eq_left hh]
  exact Classical.choose_spec hh

private theorem hinit_ledger_starts :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        (∀ (i : Fin (r + 3)), ∀ (j : Fin (r + 3)), ((c.faces 0).filter (fun F => s.start i ∈ F ∧
            s.start j ∈ F)).card = Set.ncard {k : Fin t.count | i ∈ Set.range (t.face k) ∧ j ∈
            Set.range (t.face k)}) → ((∀ (i : Fin (r + 3)), ∀ (j : Fin (r + 3)), (i ≠ j) →
            (({s.start i, s.start j} : Finset (Fin (n + 3))) ∈ c.boundary 0 ↔ j = i + 1 ∨ i = j +
            1)) → ((∀ (i : Fin (r + 3)), ∀ (j : Fin (r + 3)), (∃ F ∈ c.faces 0, s.start i ∈ F ∧
            s.start j ∈ F) ↔ ∃ k : Fin t.count, i ∈ Set.range (t.face k) ∧ j ∈ Set.range (t.face
            k)) → (∀ (i : Fin (r + (3 : ℕ))), ∀ (j : Fin (r + (3 : ℕ))), i ≠ j → {F ∈ c.faces (0
            : ℕ) | s.start i ∈ F ∧ s.start j ∈ F}.card = if {s.start i, s.start j} ∈ c.boundary
            (0 : ℕ) then (1 : ℕ) else if ∃ F ∈ c.faces (0 : ℕ), s.start i ∈ F ∧ s.start j ∈ F
            then (2 : ℕ) else (0 : ℕ)))) ) := by
  classical
  intro r n q p s X K t c hinitial_pair_count hboundary0_pair hexists_initial_pair i j hij
  rw [hinitial_pair_count i j, t.edge_count i j hij]
  simp [hboundary0_pair i j hij, hexists_initial_pair i j]

private theorem hvertex0_start :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ∀ x ∈ c.vertices 0, ∃ i : Fin (r + 3), s.start i = x ) := by
  classical
  intro r n q p s X K t c x hx
  change x ∈ Finset.univ.image s.start at hx
  rcases Finset.mem_image.mp hx with ⟨i, -, hi⟩
  exact ⟨i, hi⟩

private theorem pair_filter_card_symmetry {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (x y : α) :
    {F ∈ A | x ∈ F ∧ y ∈ F}.card = {F ∈ A | y ∈ F ∧ x ∈ F}.card := by
  congr 1
  ext F
  simp only [Finset.mem_filter]
  tauto

private theorem old_pair_ledger_transfer :
    (by
      classical
      exact
        ∀ (old : ℕ), ∀ (new : ℕ), ∀ (onBoundary : Prop), ∀ (removed : Prop), ∀ [inst : Decidable
            onBoundary], ∀ [inst_1 : Decidable removed], (old = if onBoundary then (1 : ℕ) else
            if (0 : ℕ) < old then (2 : ℕ) else (0 : ℕ)) → (removed → onBoundary) → (old = new +
            if removed then (1 : ℕ) else (0 : ℕ)) → new = if onBoundary ∧ ¬removed then (1 : ℕ)
            else if (0 : ℕ) < new then (2 : ℕ) else (0 : ℕ) ) := by
  classical
  intro old new onBoundary removed typeclassInstance0 typeclassInstance1 hold hremove hdelta
  by_cases hr : removed <;> by_cases hb : onBoundary <;>
    by_cases hn : 0 < new <;> simp_all

private theorem hiV :
    (by
      classical
      exact
        ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p :
            P3381T1PolygonBoundary n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set
            (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (t : P3475T1TriangleTree q X K),
        let c := P3523T1InsertionConstruction s t
        ((P3523T1InsertionConstruction s t).vertices (P3523T1InsertionConstruction s
            t).steps.length = Finset.univ) → (∀ (i : Fin (n + (3 : ℕ))), i ∈ c.vertices
            c.steps.length) ) := by
  classical
  intro r n q p s X K t c hvertices i
  rw [hvertices]
  simp

end InsertionDetails

theorem P3523T1InsertionIncidence {r n : Nat}
    (q : P3381T1PolygonBoundary r) (p : P3381T1PolygonBoundary n)
    (s : P3475T1BoundarySubdivision q p)
    (X K : Set (Real × Real)) (t : P3475T1TriangleTree q X K) :
    let c := P3523T1InsertionConstruction s t
    let fs := c.faces c.steps.length
    let f := P3523T1FaceEnumeration fs
    (∀ h : Nat, h ≤ c.steps.length → ∀ F ∈ c.faces h,
      F.card = 3 ∧ F ⊆ c.vertices h) ∧
    (∀ h : Nat, h ≤ c.steps.length → ∀ a b : Fin (n + 3), a ≠ b →
      ((c.faces h).filter (fun F => a ∈ F ∧ b ∈ F)).card =
        if {a, b} ∈ c.boundary h then 1
        else if ∃ F ∈ c.faces h, a ∈ F ∧ b ∈ F then 2 else 0) ∧
    (∀ k, Function.Injective (f k)) ∧
    Function.Injective (fun k => Set.range (f k)) ∧
    (∀ i, ∃ k j, f k j = i) ∧
    (∀ i j : Fin (n + 3), i ≠ j →
      Set.ncard {k : Fin fs.card | i ∈ Set.range (f k) ∧ j ∈ Set.range (f k)} =
        if j = i + 1 ∨ i = j + 1 then 1
        else if ∃ k, i ∈ Set.range (f k) ∧ j ∈ Set.range (f k) then 2 else 0) ∧
    Set.range (fun k => Set.range (f k)) =
      {J : Set (Fin (n + 3)) | ∃ F ∈ fs, (F : Set (Fin (n + 3))) = J} := by
-- BODY
  classical
  dsimp only
  let c := P3523T1InsertionConstruction s t
  obtain ⟨hblocks, hsteps, hvertices, hboundary⟩ :=
    P3523T1OrderedInsertion q p s X K t
  have hface_inj := InsertionIncidenceProof.hface_inj r n q p s X K t
  have hinner (k : Fin t.count) := InsertionDetails.hinner r n q p s X K t k
  have hinit := InsertionDetails.hinit r n q p s X K t hinner
  have hsplit_card (fs : Finset (Finset (Fin (n + 3))))
      (a d b : Fin (n + 3))
      (hf : ∀ F ∈ fs, F.card = 3)
      (hd : ∀ F ∈ fs, d ∉ F) := InsertionIncidenceProof.hsplit_card n fs a d b hf hd
  have hsplit_sub (fs : Finset (Finset (Fin (n + 3))))
      (a d b : Fin (n + 3)) (V : Finset (Fin (n + 3)))
      (hf : ∀ F ∈ fs, F ⊆ V) := InsertionIncidenceProof.hsplit_sub n fs a d b V hf
  have hinit_sub := InsertionDetails.hinit_sub r n q p s X K t
  have hfaces_next (h : Nat) (hh : h < c.steps.length) := InsertionIncidenceProof.hfaces_next r n
      q p s X K t h hh
  have hvertices_next (h : Nat) (hh : h < c.steps.length) := InsertionDetails.hvertices_next r n
      q p s X K t h hh
  have hboundary_next (h : Nat) (hh : h < c.steps.length) :=
      InsertionIncidenceProof.hboundary_next r n q p s X K t h hh
  have hstage := InsertionIncidenceProof.hstage r n q p s
          X K t hsteps hinit hsplit_card hsplit_sub hinit_sub hfaces_next hvertices_next
  have hboundary_support := InsertionIncidenceProof.hboundary_support
          r n q p s X K t hsteps hvertices_next hboundary_next
  have hthird (F : Finset (Fin (n + 3))) (a b : Fin (n + 3))
      (hab : a ≠ b) (hcard : F.card = 3) (ha : a ∈ F) (hb : b ∈ F) :=
          InsertionIncidenceProof.hthird n F a b hab hcard ha hb
  let fs := c.faces c.steps.length
  let f := P3523T1FaceEnumeration fs
  have hfinal_card := InsertionDetails.hfinal_card r n q p s X K t hstage
  have hfaceChoice (k : Fin fs.card) := InsertionIncidenceProof.hfaceChoice r n q p s X K t
      hfinal_card k
  have hf_spec (k : Fin fs.card) := InsertionDetails.hf_spec r n q p s X K t hfaceChoice k
  have hindexed_filter_card (i j : Fin (n + 3)) := InsertionIncidenceProof.hindexed_filter_card
            r n q p s X K t hf_spec i j
  have hindexed_exists (i j : Fin (n + 3)) := InsertionIncidenceProof.hindexed_exists r n q p s X
      K t
            hf_spec i j
  have hinitial_pair_count (i j : Fin (r + 3)) := InsertionIncidenceProof.hinitial_pair_count r n
      q p s X K t hface_inj i j
  have pair_eq_pair {α : Type} [DecidableEq α] (a b c d : α)
      (hab : a ≠ b) (hcd : c ≠ d) := InsertionIncidenceProof.pair_eq_pair (α := α) a b c d hab hcd
  have hboundary_final_pair (i j : Fin (n + 3)) (hij : i ≠ j) :=
      InsertionIncidenceProof.hboundary_final_pair r n q p s X K t
            hboundary pair_eq_pair i j hij
  have hindexed_ledger (hinc : ∀ h : Nat, h ≤ c.steps.length →
        ∀ a b : Fin (n + 3), a ≠ b →
          ((c.faces h).filter (fun F => a ∈ F ∧ b ∈ F)).card =
            if {a, b} ∈ c.boundary h then 1
            else if ∃ F ∈ c.faces h, a ∈ F ∧ b ∈ F then 2 else 0)
      (i j : Fin (n + 3)) (hij : i ≠ j) := InsertionIncidenceProof.hindexed_ledger r n q p s X K
          t hindexed_filter_card
            hindexed_exists hboundary_final_pair hinc i j hij
  have hboundary0_pair (i j : Fin (r + 3)) (hij : i ≠ j) :=
      InsertionIncidenceProof.hboundary0_pair r n q p s X K t
            pair_eq_pair i j hij
  have hexists_initial_pair (i j : Fin (r + 3)) := InsertionIncidenceProof.hexists_initial_pair r
      n q p s X K t i j
  have hinit_ledger_starts (i j : Fin (r + 3)) (hij : i ≠ j) :=
      InsertionDetails.hinit_ledger_starts r n q p s X K t hinitial_pair_count
            hboundary0_pair hexists_initial_pair i j hij
  have hboundary0_support := InsertionIncidenceProof.hboundary0_support r n q p s X K t
  have hvertex0_start := InsertionDetails.hvertex0_start r n q p s X K t
  have hinit_ledger := InsertionIncidenceProof.hinit_ledger r n q p s X K t hinit_sub
      hinit_ledger_starts
            hboundary0_support hvertex0_start
  have hsplit_eq (A : Finset (Finset (Fin (n + 3))))
      (a d b : Fin (n + 3)) (hab : a ≠ b) (F : Finset (Fin (n + 3)))
      (hF : F ∈ A) (hpF : a ∈ F ∧ b ∈ F)
      (huniq : ∀ G ∈ A, a ∈ G ∧ b ∈ G → G = F)
      (hd : ∀ G ∈ A, d ∉ G) := InsertionIncidenceProof.hsplit_eq n A a d b hab F hF hpF huniq hd
  have hsplit_filter_card (A : Finset (Finset (Fin (n + 3))))
      (a d b : Fin (n + 3)) (hab : a ≠ b) (F : Finset (Fin (n + 3)))
      (hF : F ∈ A) (hpF : a ∈ F ∧ b ∈ F)
      (huniq : ∀ G ∈ A, a ∈ G ∧ b ∈ G → G = F)
      (hd : ∀ G ∈ A, d ∉ G) (P : Finset (Fin (n + 3)) → Prop)
      [DecidablePred P] := InsertionIncidenceProof.hsplit_filter_card n hsplit_eq A a d b hab F
          hF hpF huniq hd P
  have herase_filter_card (A : Finset (Finset (Fin (n + 3))))
      (F : Finset (Fin (n + 3))) (hF : F ∈ A)
      (P : Finset (Fin (n + 3)) → Prop) [DecidablePred P] :=
          InsertionIncidenceProof.herase_filter_card n A F hF P
  have hfilter_exists_iff_pos (A : Finset (Finset (Fin (n + 3))))
      (P : Finset (Fin (n + 3)) → Prop) [DecidablePred P] :=
          InsertionIncidenceProof.hfilter_exists_iff_pos n A P
  -- Old-pair contributions are conserved except for the removed boundary edge.
  have old_pair_split_indicators (a b z d x y : Fin (n + 3)) (hab : a ≠ b) (haz : a ≠ z) (hbz : b
      ≠ z)
      (hxy : x ≠ y) (hxd : x ≠ d) (hyd : y ≠ d) :=
          InsertionIncidenceProof.old_pair_split_indicators n a b z d x y hab haz hbz hxy hxd hyd
  have old_boundary_membership (B : Finset (Finset (Fin (n + 3)))) (a b d x y : Fin (n + 3))
      (hxd : x ≠ d) (hyd : y ≠ d) := InsertionIncidenceProof.old_boundary_membership n B a b d x
          y hxd hyd
  have pair_filter_card_symmetry (A : Finset (Finset (Fin (n + 3)))) (x y : Fin (n + 3)) :=
      InsertionDetails.pair_filter_card_symmetry A x y
  have old_pair_ledger_transfer (old new : Nat)
      (onBoundary removed : Prop) [Decidable onBoundary] [Decidable removed]
      (hold : old = if onBoundary then 1 else if 0 < old then 2 else 0)
      (hremove : removed → onBoundary)
      (hdelta : old = new + (if removed then 1 else 0)) :=
          InsertionDetails.old_pair_ledger_transfer old new onBoundary removed hold hremove hdelta
  have hledger := InsertionIncidenceProof.hledger
              r n q p s X K t hsteps hfaces_next hboundary_next hstage hboundary_support hthird
              pair_eq_pair hinit_ledger hsplit_filter_card herase_filter_card
              hfilter_exists_iff_pos old_pair_split_indicators old_boundary_membership
              pair_filter_card_symmetry old_pair_ledger_transfer
  have hselected_face (h : Nat) (hh : h < c.steps.length) :=
      InsertionIncidenceProof.hselected_face r n q p s X K t
            hsteps hledger h hh
  have husage := InsertionIncidenceProof.husage r n q p s X K
          t hsteps hfaces_next hvertices_next hstage hthird hvertex0_start hledger hselected_face
  refine ⟨hstage, ?_⟩
  constructor
  · exact hledger
  constructor
  · intro k
    exact (hf_spec k).1
  constructor
  · intro k l hkl
    change Set.range (f k) = Set.range (f l) at hkl
    apply (fs.equivFin.symm).injective
    apply Subtype.ext
    apply Finset.ext
    intro x
    have hmem := congrArg (fun A : Set (Fin (n + 3)) => x ∈ A) hkl
    rw [(hf_spec k).2, (hf_spec l).2] at hmem
    exact Iff.of_eq hmem
  constructor
  · intro i
    have hiV := InsertionDetails.hiV r n q p s X K t hvertices i
    rcases husage c.steps.length le_rfl i hiV with ⟨F, hF, hiF⟩
    have hFs : F ∈ fs := by simpa [fs] using hF
    let k := fs.equivFin ⟨F, hFs⟩
    have hface : (fs.equivFin.symm k).val = F := by simp [k]
    have hrange : Set.range (f k) = (F : Set (Fin (n + 3))) := by
      rw [(hf_spec k).2, hface]
    have hiRange : i ∈ Set.range (f k) := by rw [hrange]; exact hiF
    rcases Set.mem_range.mp hiRange with ⟨j, hj⟩
    exact ⟨k, j, hj⟩
  constructor
  · intro i j hij
    exact hindexed_ledger hledger i j hij
  apply Set.ext
  intro J
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(fs.equivFin.symm k).val, (fs.equivFin.symm k).property, ?_⟩
    exact (hf_spec k).2.symm
  · rintro ⟨F, hF, hFJ⟩
    let k := fs.equivFin ⟨F, hF⟩
    refine ⟨k, ?_⟩
    calc
      Set.range (f k) = ((fs.equivFin.symm k).val : Set (Fin (n + 3))) := (hf_spec k).2
      _ = (F : Set (Fin (n + 3))) := by simp [k]
      _ = J := hFJ

end ApollonianSuperharmonic

end
