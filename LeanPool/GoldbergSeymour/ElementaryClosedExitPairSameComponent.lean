/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponentLeafPaths

public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors

public import LeanPool.GoldbergSeymour.ClosedColorExitPathBoundaryEdge
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint

/-!
# Elementary Closed Exit Pair Same Component

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_chooseFirst_359.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k) (a b : Fin k) (a1 b1
    a2 b2 : V) (P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a1) (Sum.inl b1)) (P2 :
    (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl b2)), (∀ x ∈ P1.support, x ∉
    P2.support) → b1 ≠ b2 → let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b; ∀
    {u v : V ⊕ E} (p : H.Walk u v) (S : Finset (V ⊕ E)), {x ∈ S | x ∈ p.support}.Nonempty → ∃
    x ∈ S, ∃ (hx : x ∈ p.support), ∀ t ∈ S, t ∈ (p.takeUntil x hx).support → t = x := by
  classical
  intro V E _ _ G k phi a b a1 b1 a2 b2 P1 P2 _ _ H u v p S hnonempty
  have firstErase : ∃ x ∈ S, ∃ (hx : x ∈ p.support),
      {t ∈ S.erase x | t ∈ (p.takeUntil x hx).support} = ∅ := by
    simp only [← Finset.subset_empty]
    induction hn : p.length + S.card using Nat.strong_induction_on
        generalizing S v with
    | _ n ih =>
        simp only [Finset.Nonempty, Finset.mem_filter] at hnonempty
        obtain ⟨x, hxS, hxP⟩ := hnonempty
        obtain hempty | hmore := Finset.eq_empty_or_nonempty
          {t ∈ S.erase x | t ∈ (p.takeUntil x hxP).support}
        · exact ⟨x, hxS, hxP, hempty.le⟩
        · have hlt : (p.takeUntil x hxP).length +
              (S.erase x).card < n := by
            rw [← Finset.card_erase_add_one hxS] at hn
            have hle := p.length_takeUntil_le_length hxP
            omega
          obtain ⟨y, hyS, hyP, hyempty⟩ :=
            ih _ hlt (p.takeUntil x hxP) (S.erase x) hmore rfl
          refine ⟨y, Finset.mem_of_mem_erase hyS,
            p.support_takeUntil_subset_support hxP hyP, ?_⟩
          rwa [p.takeUntil_takeUntil, Finset.erase_right_comm,
            Finset.filter_erase, Finset.erase_eq_of_notMem] at hyempty
          simp only [Finset.mem_filter, Finset.mem_erase, ne_eq, not_and,
            and_imp]
          rintro hxy -
          exact p.notMem_support_takeUntil_support_takeUntil_subset
            (Ne.symm hxy) hxP hyP
  obtain ⟨x, hxS, hxP, hempty⟩ := firstErase
  refine ⟨x, hxS, hxP, ?_⟩
  suffices {t ∈ S | t ∈ (p.takeUntil x hxP).support} ⊆ {x} by
    simpa [Finset.subset_iff] using this
  rwa [Finset.filter_erase, ← Finset.subset_empty,
    ← Finset.subset_insert_iff, LawfulSingleton.insert_empty_eq] at hempty

private theorem helper_firstEntry_398.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E} (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (a b : Fin k) (a1 b1 a2 b2 : V)
      (P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a1) (Sum.inl b1))
      (P2 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl b2)),
      (∀ x ∈ P1.support, x ∉ P2.support) →
        b1 ≠ b2 →
          let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
          let X : Finset V := TreeSequenceVertexSet T;
          (∀ {u v : V ⊕ E} (p : H.Walk u v) (S : Finset (V ⊕ E)),
              {x ∈ S | x ∈ p.support}.Nonempty →
                ∃ x ∈ S, ∃ (hx : x ∈ p.support), ∀ t ∈ S, t ∈ (p.takeUntil x hx).support → t = x) →
            ∀ (r s : V) (Q : H.Walk (Sum.inl r) (Sum.inl s)),
              Q.IsPath →
                a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r →
                  r ∉ X →
                    (∃ x ∈ X, Sum.inl x ∈ Q.support) →
                      ∃ (c : V) (_ : c ∈ X) (hcQ : Sum.inl c ∈ Q.support),
                        let L : H.Walk (Sum.inl r) (Sum.inl c) := Q.takeUntil (Sum.inl c) hcQ;
                        TreeExitPath T phi a b r c L := by
  classical
  intro V E _ _ _ _ G k e0 T phi a b a1 b1 a2 b2 P1 P2 _ _ H X chooseFirst r s Q hQ hmissing hrX
      hmeet
  let _ := Fintype.ofFinite V
  let S : Finset (Sum V E) := X.image Sum.inl
  obtain ⟨q, hqS, hqQ, hqfirst⟩ :=
    chooseFirst Q S (by
      obtain ⟨x, hxX, hxQ⟩ := hmeet
      exact ⟨Sum.inl x, by simp [S, hxX, hxQ]⟩)
  obtain ⟨c, hcX, hcq⟩ : ∃ c, c ∈ X ∧ Sum.inl c = q := by
    simpa [S] using hqS
  subst q
  let L := Q.takeUntil (Sum.inl c) hqQ
  have hLc : ∀ x ∈ X, (Sum.inl x ∈ L.support ↔ x = c) := by
    intro x hxX
    constructor
    · intro hxL
      have heq := hqfirst (Sum.inl x) (by simp [S, hxX]) hxL
      exact Sum.inl.inj heq
    · rintro rfl
      exact L.end_mem_support
  have hrc : r ≠ c := by
    intro hrc
    apply hrX
    simpa [hrc] using hcX
  have hLpath : L.IsPath := hQ.takeUntil _
  have hLlen : 2 ≤ L.length := by
    have hpos : 0 < L.length := by
      apply Nat.pos_of_ne_zero
      intro hn
      have hnil : L.Nil := SimpleGraph.Walk.length_eq_zero_iff.mp hn
      exact hrc (Sum.inl.inj hnil.eq)
    by_contra hnotTwo
    have hlen : L.length = 1 := by omega
    have hadj := L.adj_getVert_succ (i := 0) (by omega)
    have hend : L.getVert 1 = Sum.inl c := by
      have heq := L.getVert_length
      rwa [hlen] at heq
    rw [L.getVert_zero, hend] at hadj
    simp [H, TwoColorIncidenceGraph] at hadj
  exact ⟨c, hcX, hqQ, hLpath, hLlen, hrX, hcX, hmissing, hLc⟩

private theorem helper_hCnontrivial_540.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E}
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a b : Fin k) (a1 b1 : V)
      (P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a1) (Sum.inl b1)),
      TreeExitPath T phi a b a1 b1 P1 →
        let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
        (∀ {u v : V ⊕ E} (p : H.Walk u v) {z : V ⊕ E}, z ∈ p.support → z ∈ TwoColorComponent G
            phi a b u) →
          ∃ (e : E), Sum.inr e ∈ TwoColorComponent G phi a b (Sum.inl a1) := by
  classical
  intro V E _ _ G k e0 T phi a b a1 b1 P1 hP1 H walk_support_component
  let _ := Fintype.ofFinite V
  have hpos : 0 < P1.length := by
    have htwo := hP1.2.1
    omega
  have hadj := P1.adj_getVert_succ (i := 0) hpos
  rw [P1.getVert_zero] at hadj
  cases hnext : P1.getVert 1 with
  | inl v =>
      rw [hnext] at hadj
      simp [TwoColorIncidenceGraph] at hadj
  | inr e =>
      refine ⟨e, walk_support_component P1 ?_⟩
      rw [← hnext]
      exact P1.getVert_mem_support 1

private theorem helper_hcomponents_ne_597.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E}
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a b : Fin k) (a1 b1 a2 b2 : V)
      (P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a1) (Sum.inl b1))
      (P2 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl b2)),
      TreeExitPath T phi a b a1 b1 P1 →
        TreeExitPath T phi a b a2 b2 P2 →
          (∀ x ∈ P1.support, x ∉ P2.support) →
            b1 ≠ b2 →
              let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
              ∀ (R : H.Walk (Sum.inl a1) (Sum.inl a2)),
                R.IsPath →
                  {y : V ⊕ E | y ∈ R.support} = TwoColorComponent G phi a b (Sum.inl a1) →
                    ∀ x ∈ TreeSequenceVertexSet T,
                      (H.neighborSet (Sum.inl x)).Subsingleton →
                        TwoColorComponent G phi a b (Sum.inl a1) ≠ TwoColorComponent G phi a b
                            (Sum.inl x) := by
  classical
  intro V E _ _ G k e0 T phi a b a1 b1 a2 b2 P1 P2 hP1 hP2 _ _ H R hRpath hRsupport x hxX hxleaf heq
  let _ := Fintype.ofFinite V
  have hxR : Sum.inl x ∈ R.support := by
    change Sum.inl x ∈ {z | z ∈ R.support}
    rw [hRsupport, heq]
    rfl
  have hxa1 : (Sum.inl x : Sum V E) ≠ Sum.inl a1 := by
    intro h
    have h' : x = a1 := Sum.inl.inj h
    exact hP1.2.2.1 (h' ▸ hxX)
  have hxa2 : (Sum.inl x : Sum V E) ≠ Sum.inl a2 := by
    intro h
    have h' : x = a2 := Sum.inl.inj h
    exact hP2.2.2.1 (h' ▸ hxX)
  exact (hRpath.isTrail.notMem_support_of_subsingleton_neighborSet
    hxa1 hxa2 hxleaf) hxR

lemma ElementaryClosedExitPairSameComponent {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (a b : Fin k) (hne : a ≠ b)
    (hamissing : a ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {a})
    (hbpresent : b ∉ TreeMissingColors phi T)
    (a1 b1 a2 b2 : V)
    (P1 : (TwoColorIncidenceGraph G phi a b).Walk
      (Sum.inl a1) (Sum.inl b1))
    (P2 : (TwoColorIncidenceGraph G phi a b).Walk
      (Sum.inl a2) (Sum.inl b2))
    (hP1 : TreeExitPath T phi a b a1 b1 P1)
    (hP2 : TreeExitPath T phi a b a2 b2 P2)
    (_ : ∀ x, x ∈ P1.support → x ∉ P2.support)
    (haends : a1 ≠ a2) (_ : b1 ≠ b2)
    (hcomponents :
      TwoColorComponent G phi a b (Sum.inl a1) =
        TwoColorComponent G phi a b (Sum.inl a2)) :
    ∃ (a3 b3 : V)
      (P3 : (TwoColorIncidenceGraph G phi a b).Walk
        (Sum.inl a3) (Sum.inl b3))
      (f3 : E),
      TreeExitPath T phi a b a3 b3 P3 ∧
      (∀ x, x ∈ P1.support → x ∉ P3.support) ∧
      (∀ x, x ∈ P2.support → x ∉ P3.support) ∧
      a3 ≠ a1 ∧ a3 ≠ a2 ∧ b3 ≠ b1 ∧ b3 ≠ b2 ∧
      f3 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b ∧
      Incident G b3 f3 ∧ Sum.inr f3 ∈ P3.support := by
  classical
  let H := TwoColorIncidenceGraph G phi a b
  let X := TreeSequenceVertexSet T
  have endpoint_missing := @TwoColorMissingOfVertexNeighborsSubsingleton V E inferInstance G k
      phi a b
      hne
  have missing_leaf := TwoColorMissingVertexNeighborsSubsingleton G phi hproper a b
  have walk_support_component : ∀ {u v : Sum V E}
      (p : H.Walk u v) {z : Sum V E},
      z ∈ p.support → z ∈ TwoColorComponent G phi a b u := by
    intro u v p z hz
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
    change H.connectedComponentMk z = H.connectedComponentMk u
    rw [← hi]
    exact (SimpleGraph.ConnectedComponent.sound (p.take i).reachable).symm
  have fullPathFromLeaf := @TwoColorComponent.pathFromLeaf V E inferInstance inferInstance G k phi
      hproper a b endpoint_missing
  have chooseFirst : ∀ {u v : Sum V E} (p : H.Walk u v)
      (S : Finset (Sum V E)),
      {x ∈ S | x ∈ p.support}.Nonempty →
      ∃ x ∈ S, ∃ (hx : x ∈ p.support),
        ∀ t ∈ S, t ∈ (p.takeUntil x hx).support → t = x := by
    exact @helper_chooseFirst_359 V E inferInstance inferInstance G k phi a b a1 b1 a2 b2 P1 P2
        (by assumption) (by assumption)
  have firstEntry : ∀ (r s : V) (Q : H.Walk (Sum.inl r) (Sum.inl s)),
      Q.IsPath →
      (a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r) →
      r ∉ X →
      (∃ x ∈ X, Sum.inl x ∈ Q.support) →
      ∃ (c : V) (hcX : c ∈ X) (hcQ : Sum.inl c ∈ Q.support),
        let L := Q.takeUntil (Sum.inl c) hcQ
        TreeExitPath T phi a b r c L := by
    exact @helper_firstEntry_398 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 T phi a b a1 b1 a2 b2 P1 P2 (by assumption) (by assumption) chooseFirst
  have ha1leaf : Set.Subsingleton (H.neighborSet (Sum.inl a1)) :=
    missing_leaf a1 hP1.2.2.2.2.1
  have ha2leaf : Set.Subsingleton (H.neighborSet (Sum.inl a2)) :=
    missing_leaf a2 hP2.2.2.2.2.1
  have ha1C : Sum.inl a1 ∈ TwoColorComponent G phi a b (Sum.inl a1) :=
    rfl
  have ha2C : Sum.inl a2 ∈ TwoColorComponent G phi a b (Sum.inl a1) := by
    rw [hcomponents]
    rfl
  have hCnontrivial := @helper_hCnontrivial_540 V E inferInstance inferInstance G k e0 T phi a b a1
      b1 P1 hP1 walk_support_component
  obtain ⟨s, R, hRpath, hRsupport, ha1s, hsMissing⟩ :=
    fullPathFromLeaf a1 (Sum.inl a1) ha1C ha1leaf hCnontrivial
  have hsa2 : s = a2 := by
    by_contra hsa2
    have ha2R : Sum.inl a2 ∈ R.support := by
      change Sum.inl a2 ∈ {z | z ∈ R.support}
      rw [hRsupport]
      exact ha2C
    have ha2start : (Sum.inl a2 : Sum V E) ≠ Sum.inl a1 := by
      exact fun h => haends (Sum.inl.inj h).symm
    have ha2end : (Sum.inl a2 : Sum V E) ≠ Sum.inl s := by
      exact fun h => hsa2 (Sum.inl.inj h).symm
    exact (hRpath.isTrail.notMem_support_of_subsingleton_neighborSet
      ha2start ha2end ha2leaf) ha2R
  subst s
  simp only [TreeMissingColors, Finset.mem_biUnion] at hamissing
  obtain ⟨x, hxX, hxa⟩ := hamissing
  have hxbnot : b ∉ MissingColors G phi x := by
    intro hxb
    apply hbpresent
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨x, hxX, hxb⟩
  have hxbpresent : b ∈ PresentColors G phi x := by
    simpa [MissingColors] using hxbnot
  obtain ⟨g, hxg, hgcolor⟩ := by
    simpa [PresentColors] using hxbpresent
  have hxleaf : Set.Subsingleton (H.neighborSet (Sum.inl x)) :=
    missing_leaf x (Or.inl hxa)
  have hxC : Sum.inl x ∈ TwoColorComponent G phi a b (Sum.inl x) := rfl
  have hCxnontrivial :
      ∃ e : E, Sum.inr e ∈ TwoColorComponent G phi a b (Sum.inl x) := by
    refine ⟨g, ?_⟩
    change H.connectedComponentMk (Sum.inr g) =
      H.connectedComponentMk (Sum.inl x)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (by
        simpa [H, TwoColorIncidenceGraph] using
          (show Incident G x g ∧
              (phi g = some a ∨ phi g = some b) from
            ⟨hxg, Or.inr hgcolor⟩))).symm
  obtain ⟨y, Q, hQpath, hQsupport, hxy, hyMissing⟩ :=
    fullPathFromLeaf x (Sum.inl x) hxC hxleaf hCxnontrivial
  have hcomponents_ne :
      TwoColorComponent G phi a b (Sum.inl a1) ≠
        TwoColorComponent G phi a b (Sum.inl x) := by
    exact @helper_hcomponents_ne_597 V E inferInstance inferInstance G k e0 T phi a b a1 b1 a2 b2
        P1 P2 hP1 hP2 (by assumption) (by assumption) R hRpath hRsupport x hxX hxleaf
  have hcompDisjoint :
      Disjoint (TwoColorComponent G phi a b (Sum.inl a1))
        (TwoColorComponent G phi a b (Sum.inl x)) :=
    (TwoColorComponentsDisjoint G phi a b
      (Sum.inl a1) (Sum.inl x)).resolve_left hcomponents_ne
  have hyX : y ∉ X := by
    intro hyX
    rcases hyMissing with hya | hyb
    · have hdis := helementary hxX hyX hxy
      exact (Finset.disjoint_left.mp hdis) hxa hya
    · apply hbpresent
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨y, hyX, hyb⟩
  have hmeet : ∃ z ∈ X, Sum.inl z ∈ Q.reverse.support := by
    refine ⟨x, hxX, ?_⟩
    simp only [SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact Q.start_mem_support
  obtain ⟨b3, hb3X, hb3Q, hP3⟩ :=
    firstEntry y x Q.reverse hQpath.reverse hyMissing hyX hmeet
  let P3 := Q.reverse.takeUntil (Sum.inl b3) hb3Q
  have hP3' : TreeExitPath T phi a b y b3 P3 := hP3
  have hP3component : ∀ z ∈ P3.support,
      z ∈ TwoColorComponent G phi a b (Sum.inl x) := by
    intro z hz
    have hzrev : z ∈ Q.reverse.support :=
      Q.reverse.support_takeUntil_subset_support hb3Q hz
    have hzQ : z ∈ Q.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzrev
    rw [← hQsupport]
    exact hzQ
  have hP1component : ∀ z ∈ P1.support,
      z ∈ TwoColorComponent G phi a b (Sum.inl a1) := by
    intro z hz
    exact walk_support_component P1 hz
  have hP2component : ∀ z ∈ P2.support,
      z ∈ TwoColorComponent G phi a b (Sum.inl a1) := by
    intro z hz
    rw [hcomponents]
    exact walk_support_component P2 hz
  have hP1P3 : ∀ z, z ∈ P1.support → z ∉ P3.support := by
    intro z hz1 hz3
    exact (Set.disjoint_left.mp hcompDisjoint)
      (hP1component z hz1) (hP3component z hz3)
  have hP2P3 : ∀ z, z ∈ P2.support → z ∉ P3.support := by
    intro z hz2 hz3
    exact (Set.disjoint_left.mp hcompDisjoint)
      (hP2component z hz2) (hP3component z hz3)
  have hyComponent : Sum.inl y ∈
      TwoColorComponent G phi a b (Sum.inl x) := by
    rw [← hQsupport]
    exact Q.end_mem_support
  have hb3Component : Sum.inl b3 ∈
      TwoColorComponent G phi a b (Sum.inl x) :=
    hP3component (Sum.inl b3) P3.end_mem_support
  have hb1Component : Sum.inl b1 ∈
      TwoColorComponent G phi a b (Sum.inl a1) :=
    hP1component (Sum.inl b1) P1.end_mem_support
  have hb2Component : Sum.inl b2 ∈
      TwoColorComponent G phi a b (Sum.inl a1) :=
    hP2component (Sum.inl b2) P2.end_mem_support
  have separated {u v : V}
      (hu : Sum.inl u ∈ TwoColorComponent G phi a b (Sum.inl a1))
      (hv : Sum.inl v ∈ TwoColorComponent G phi a b (Sum.inl x)) :
      v ≠ u := by
    intro hvu
    subst v
    exact (Set.disjoint_left.mp hcompDisjoint) hu hv
  have hya1 : y ≠ a1 := separated ha1C hyComponent
  have hya2 : y ≠ a2 := separated ha2C hyComponent
  have hb3b1 : b3 ≠ b1 := separated hb1Component hb3Component
  have hb3b2 : b3 ≠ b2 := separated hb2Component hb3Component
  obtain ⟨f3, hf3, hb3f3, hf3P3⟩ :=
    ClosedColorExitPathBoundaryEdge G T phi a b hclosed y b3 P3 hP3'
  exact ⟨y, b3, P3, f3, hP3', hP1P3, hP2P3, hya1, hya2,
    hb3b1, hb3b2, hf3, hb3f3, hf3P3⟩

end GoldbergSeymour

end
