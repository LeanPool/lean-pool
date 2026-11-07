/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideReplacementBoundaryParity
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint

/-!
# Scheide Replacement Boundary At Least Three

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_initial_avoids_U_217.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let Z : Finset V := X \ U;
    let _ : DecidablePred fun (f : E) ↦
    ∃ w ∉ X, Incident G w f := fun (x : E) ↦ Classical.propDecidable ((fun (f : E) ↦
    ∃ w ∉ X, Incident G w f) x);
    let B : Finset E := {f ∈ BoundaryColorEdges G phi Z (↑d : Fin k) |
    ∃ w ∉ X, Incident G w f};
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k); D.v0 d ∈ Z ∧ y0 ∈ Z ∧ (
    ∀ z ∈ Z,
    ∃! f : E, Incident G z f ∧ phi f = some delta) ∧ D.f0 d ∈ B ∧ Odd B.card → B = {D.f0 d} →
        IsProperEdgeColoring G phi → ColoredVertexSetClosed G phi X → alpha ∈ MissingColors G phi
        y0 →
    ∀ (h : E), phi h = some alpha → G.ends h = s(C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex
        i (1 : Fin (2 : ℕ))) → Incident G u0 h → Incident G u1 h →
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha delta;
    let I : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl y0); U ⊆ X →
    ∀ v ∈ U, Sum.inl v ∉ I := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X i u0 u1 U Z outsideDec B y0 alpha delta hp hBsingleton
      hproper hclosed hy0Missing h hhcolor hhends hhInc0 hhInc1 H I hUsubX v hvU hvI
  let p := D.initialPath d
  have hpath : p.IsPath := (D.initial_path_full d).2.1
  have hvSupport : Sum.inl v ∈ p.support := by
    change Sum.inl v ∈ {x | x ∈ p.support}
    rw [(D.initial_path_full d).2.2.2]
    exact hvI
  obtain ⟨t, ht, htle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvSupport
  have hAtT : t ≤ p.length ∧ ∃ w : V, w ∉ Z ∧ p.getVert t = Sum.inl w := by
    exact ⟨htle, v, fun hvZ => (Finset.mem_sdiff.mp hvZ).2 hvU, ht⟩
  have hleave : ∃ n : ℕ,
      n ≤ p.length ∧ ∃ w : V, w ∉ Z ∧ p.getVert n = Sum.inl w :=
    ⟨t, hAtT⟩
  let n := Nat.find hleave
  have hn := Nat.find_spec hleave
  obtain ⟨hnle, w, hwZ, hnw⟩ := hn
  have hnpos : 0 < n := by
    by_contra hn0
    have hnzero : n = 0 := by omega
    have hnw' : p.getVert n = Sum.inl w := hnw
    rw [hnzero, p.getVert_zero] at hnw'
    have hsum : (Sum.inl y0 : Sum V E) = Sum.inl w := hnw'
    have hyw : y0 = w := Sum.inl.inj hsum
    exact hwZ (hyw ▸ hp.2.1)
  have hnTwo : 2 ≤ n := by
    by_contra hntwo
    have hnOne : n = 1 := by omega
    have hadj := p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
    rw [p.getVert_zero] at hadj
    have hgetOne : p.getVert 1 = Sum.inl w := by
      have hnw' : p.getVert n = Sum.inl w := hnw
      simpa [hnOne] using hnw'
    have : H.Adj (Sum.inl y0) (Sum.inl w) := by
      simpa [H, alpha, delta, y0, hgetOne] using hadj
    simp [H, TwoColorIncidenceGraph] at this
  have hadjEnter := p.adj_getVert_succ (i := n - 1) (by omega : n - 1 < p.length)
  have hadjBefore := p.adj_getVert_succ (i := n - 2) (by omega : n - 2 < p.length)
  have hEnterIndex : n - 1 + 1 = n := by omega
  have hBeforeIndex : n - 2 + 1 = n - 1 := by omega
  rw [hEnterIndex, hnw] at hadjEnter
  cases hedge : p.getVert (n - 1) with
  | inl q =>
      rw [hedge] at hadjEnter
      simp [TwoColorIncidenceGraph] at hadjEnter
  | inr e =>
    have hEnterData : Incident G w e ∧
        (phi e = some alpha ∨ phi e = some delta) := by
      rw [hedge] at hadjEnter
      simpa [H, TwoColorIncidenceGraph] using hadjEnter
    rw [hBeforeIndex, hedge] at hadjBefore
    cases hprev : p.getVert (n - 2) with
    | inr g =>
        rw [hprev] at hadjBefore
        simp [TwoColorIncidenceGraph] at hadjBefore
    | inl z =>
      have hBeforeData : Incident G z e ∧
          (phi e = some alpha ∨ phi e = some delta) := by
        rw [hprev] at hadjBefore
        simpa [H, TwoColorIncidenceGraph] using hadjBefore
      have hzZ : z ∈ Z := by
        by_contra hz
        have hEarlier : n - 2 ≤ p.length ∧
            ∃ q : V, q ∉ Z ∧ p.getVert (n - 2) = Sum.inl q :=
          ⟨by omega, z, hz, hprev⟩
        have hmin := Nat.find_min' hleave hEarlier
        change n ≤ n - 2 at hmin
        omega
      have hzX : z ∈ X := (Finset.mem_sdiff.mp hzZ).1
      have edge_is_f0 : e = D.f0 d := by
        by_cases hwX : w ∈ X
        · have hwU : w ∈ U := by
            by_contra hwU
            exact hwZ (Finset.mem_sdiff.mpr ⟨hwX, hwU⟩)
          rcases hEnterData.2 with heAlpha | heDelta
          · have hw0or1 : w = u0 ∨ w = u1 := by
              simpa [U] using hwU
            have hwh : Incident G w h := by
              rcases hw0or1 with rfl | rfl
              · exact hhInc0
              · exact hhInc1
            have heh : e = h := by
              by_contra hne
              exact (hproper hne ⟨w, hEnterData.1, hwh⟩ heAlpha) hhcolor
            have hzInU : z ∈ U := by
              have hzEnds : z ∈ G.ends h := by
                rw [← heh]
                exact hBeforeData.1
              simpa [U, u0, u1, hhends] using hzEnds
            exact False.elim ((Finset.mem_sdiff.mp hzZ).2 hzInU)
          · have hbad := ScheideDefectiveNoCross G k e0 phi T C D d e heDelta
            exact False.elim (hbad ⟨w, hwU, hEnterData.1, z, hzZ,
              hBeforeData.1⟩)
        · rcases hEnterData.2 with heAlpha | heDelta
          · have heBoundary : e ∈ BoundaryEdges G X := by
              simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
                true_and]
              have hzw : z ≠ w := fun hzw => hwX (hzw ▸ hzX)
              exact ⟨z, hzX, w, hwX,
                (Sym2.mem_and_mem_iff hzw).mp
                  ⟨hBeforeData.1, hEnterData.1⟩⟩
            exact False.elim (hclosed heBoundary (Finset.mem_sdiff.mp hp.2.1).1
              heAlpha hy0Missing)
          · have heBoundaryZ : e ∈ BoundaryEdges G Z := by
              simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
                true_and]
              have hzw : z ≠ w := fun hzw => hwX (hzw ▸ hzX)
              exact ⟨z, hzZ, w, fun hw => hwX (Finset.mem_sdiff.mp hw).1,
                (Sym2.mem_and_mem_iff hzw).mp
                  ⟨hBeforeData.1, hEnterData.1⟩⟩
            have heB : e ∈ B := by
              apply Finset.mem_filter.mpr
              exact ⟨Finset.mem_filter.mpr ⟨heBoundaryZ, heDelta⟩,
                w, hwX, hEnterData.1⟩
            rw [hBsingleton] at heB
            simpa using heB
      have hIndexEq : n - 1 = (D.f0Index d).val := by
        have hget : p.getVert (n - 1) = p.getVert (D.f0Index d).val := by
          calc
            p.getVert (n - 1) = Sum.inr e := hedge
            _ = Sum.inr (D.f0 d) := by rw [edge_is_f0]
            _ = p.getVert (D.f0Index d).val := (D.f0_at_index d).symm
        have hfidxle : (D.f0Index d).val ≤ p.length := by
          change (D.f0Index d).val ≤ (D.initialPath d).length
          exact Nat.lt_succ_iff.mp (D.f0Index d).isLt
        have hnsub : n - 1 ≤ p.length := (Nat.sub_le n 1).trans hnle
        exact hpath.getVert_injOn hnsub hfidxle hget
      have hnv0 : (D.v0Index d).val < n := by
        have hs := (D.successive_indices d).1
        omega
      have hnt : n ≤ t := Nat.find_min' hleave hAtT
      let rt : Fin (p.length + 1) := ⟨t, by omega⟩
      have hvOutside := D.v0_is_last_tree_vertex d rt (by
        change (D.v0Index d).val < t
        omega) v
      have hrt : p.getVert rt.val = Sum.inl v := by simpa [rt] using ht
      exact hvOutside hrt (hUsubX hvU)

private theorem helper_hKavoidsZ_366.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let Z : Finset V := X \ U;
    let _ : DecidablePred fun (f : E) ↦
    ∃ w ∉ X, Incident G w f := fun (x : E) ↦ Classical.propDecidable ((fun (f : E) ↦
    ∃ w ∉ X, Incident G w f) x);
    let B : Finset E := {f ∈ BoundaryColorEdges G phi Z (↑d : Fin k) |
    ∃ w ∉ X, Incident G w f};
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k); D.v0 d ∈ Z ∧ y0 ∈ Z ∧ (
    ∀ z ∈ Z,
    ∃! f : E, Incident G z f ∧ phi f = some delta) ∧ D.f0 d ∈ B ∧ Odd B.card → B = {D.f0 d} →
        IsProperEdgeColoring G phi → ColoredVertexSetClosed G phi X → alpha ∈ MissingColors G phi
        y0 →
    ∀ (h : E), phi h = some alpha → G.ends h = s(C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex
        i (1 : Fin (2 : ℕ))) → u0 ∉ Z → Incident G u0 h → Incident G u1 h →
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha delta;
    let I : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl y0);
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl u0); Disjoint K I →
    ∀ z ∈ Z, Sum.inl z ∉ K := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X i u0 u1 U Z outsideDec B y0 alpha delta hp hBsingleton
      hproper hclosed hy0Missing h hhcolor hhends hu0notZ hhInc0 hhInc1 H I K hKI z hzZ hzK
  have hzK' : H.connectedComponentMk (Sum.inl z) =
      H.connectedComponentMk (Sum.inl u0) := by
    exact hzK
  have hreach : H.Reachable (Sum.inl u0) (Sum.inl z) := by
    exact SimpleGraph.ConnectedComponent.eq.mp hzK'.symm
  obtain ⟨p, hpath⟩ := hreach.exists_isPath
  have hAtEnd : p.length ≤ p.length ∧
      ∃ q : V, q ∈ Z ∧ p.getVert p.length = Sum.inl q := by
    exact ⟨le_rfl, z, hzZ, p.getVert_length⟩
  have henter : ∃ n : ℕ,
      n ≤ p.length ∧ ∃ q : V, q ∈ Z ∧ p.getVert n = Sum.inl q :=
    ⟨p.length, hAtEnd⟩
  let n := Nat.find henter
  have hn := Nat.find_spec henter
  obtain ⟨hnle, q, hqZ, hnq⟩ := hn
  have hnpos : 0 < n := by
    by_contra hn0
    have hnzero : n = 0 := by omega
    have hnq' : p.getVert n = Sum.inl q := hnq
    rw [hnzero, p.getVert_zero] at hnq'
    have huq : u0 = q := Sum.inl.inj hnq'
    exact hu0notZ (huq ▸ hqZ)
  have hnTwo : 2 ≤ n := by
    by_contra hntwo
    have hnOne : n = 1 := by omega
    have hadj := p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
    rw [p.getVert_zero] at hadj
    have hgetOne : p.getVert 1 = Sum.inl q := by
      have hnq' : p.getVert n = Sum.inl q := hnq
      simpa [hnOne] using hnq'
    have : H.Adj (Sum.inl u0) (Sum.inl q) := by
      simpa [hgetOne] using hadj
    simp [H, TwoColorIncidenceGraph] at this
  have hadjEnter := p.adj_getVert_succ (i := n - 1) (by omega : n - 1 < p.length)
  have hadjBefore := p.adj_getVert_succ (i := n - 2) (by omega : n - 2 < p.length)
  have hEnterIndex : n - 1 + 1 = n := by omega
  have hBeforeIndex : n - 2 + 1 = n - 1 := by omega
  rw [hEnterIndex, hnq] at hadjEnter
  cases hedge : p.getVert (n - 1) with
  | inl r =>
      rw [hedge] at hadjEnter
      simp [H, TwoColorIncidenceGraph] at hadjEnter
  | inr e =>
    have hEnterData : Incident G q e ∧
        (phi e = some alpha ∨ phi e = some delta) := by
      rw [hedge] at hadjEnter
      simpa [H, TwoColorIncidenceGraph] using hadjEnter
    rw [hBeforeIndex, hedge] at hadjBefore
    cases hprev : p.getVert (n - 2) with
    | inr g =>
        rw [hprev] at hadjBefore
        simp [H, TwoColorIncidenceGraph] at hadjBefore
    | inl w =>
      have hBeforeData : Incident G w e ∧
          (phi e = some alpha ∨ phi e = some delta) := by
        rw [hprev] at hadjBefore
        simpa [H, TwoColorIncidenceGraph] using hadjBefore
      have hwZ : w ∉ Z := by
        intro hwZ
        have hEarlier : n - 2 ≤ p.length ∧
            ∃ r : V, r ∈ Z ∧ p.getVert (n - 2) = Sum.inl r :=
          ⟨by omega, w, hwZ, hprev⟩
        have hmin := Nat.find_min' henter hEarlier
        change n ≤ n - 2 at hmin
        omega
      by_cases hwX : w ∈ X
      · have hwU : w ∈ U := by
          by_contra hwU
          exact hwZ (Finset.mem_sdiff.mpr ⟨hwX, hwU⟩)
        rcases hEnterData.2 with heAlpha | heDelta
        · have hw0or1 : w = u0 ∨ w = u1 := by simpa [U] using hwU
          have hwh : Incident G w h := by
            rcases hw0or1 with rfl | rfl
            · exact hhInc0
            · exact hhInc1
          have heh : e = h := by
            by_contra hne
            exact (hproper hne ⟨w, hBeforeData.1, hwh⟩ heAlpha) hhcolor
          have hqU : q ∈ U := by
            have hqEnds : q ∈ G.ends h := by
              rw [← heh]
              exact hEnterData.1
            simpa [U, u0, u1, hhends] using hqEnds
          exact (Finset.mem_sdiff.mp hqZ).2 hqU
        · exact (ScheideDefectiveNoCross G k e0 phi T C D d e heDelta)
            ⟨w, hwU, hBeforeData.1, q, hqZ, hEnterData.1⟩
      · rcases hEnterData.2 with heAlpha | heDelta
        · have heBoundary : e ∈ BoundaryEdges G X := by
            simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
              true_and]
            have hwq : q ≠ w := fun hqw => hwX (hqw ▸ (Finset.mem_sdiff.mp hqZ).1)
            exact ⟨q, (Finset.mem_sdiff.mp hqZ).1, w, hwX,
              (Sym2.mem_and_mem_iff hwq).mp
                ⟨hEnterData.1, hBeforeData.1⟩⟩
          exact hclosed heBoundary (Finset.mem_sdiff.mp hp.2.1).1
            heAlpha hy0Missing
        · have heBoundaryZ : e ∈ BoundaryEdges G Z := by
            simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
              true_and]
            have hqw : q ≠ w := fun hqw => hwX (hqw ▸ (Finset.mem_sdiff.mp hqZ).1)
            exact ⟨q, hqZ, w, fun hw => hwX (Finset.mem_sdiff.mp hw).1,
              (Sym2.mem_and_mem_iff hqw).mp
                ⟨hEnterData.1, hBeforeData.1⟩⟩
          have heB : e ∈ B := by
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨heBoundaryZ, heDelta⟩,
                w, hwX, hBeforeData.1⟩
          have hef0 : e = D.f0 d := by
            rw [hBsingleton] at heB
            simpa using heB
          have hreachEdge : H.Reachable (Sum.inl u0) (Sum.inr e) := by
            have ht := (p.take (n - 1)).reachable
            simpa [hedge] using ht
          have heK : Sum.inr e ∈ K := by
            change H.connectedComponentMk (Sum.inr e) =
              H.connectedComponentMk (Sum.inl u0)
            exact (SimpleGraph.ConnectedComponent.eq.mpr hreachEdge).symm
          have hf0I : Sum.inr (D.f0 d) ∈ I := by
            simpa [I, alpha, delta, y0] using D.f0_on_initial_component d
          exact (Set.disjoint_left.mp hKI) (hef0 ▸ heK) hf0I

private theorem helper_tree_edges_outside_K_506.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let Z : Finset V := X \ U;
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k); IsOneEdgeUncolored phi e0 → (
    ∀ (a : Fin C.p) (b : Fin (2 : ℕ)), C.y a ≠ C.blockVertex i b) →
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl u0); (
    ∀ {v : V} {e : E}, Sum.inr e ∈ K → Incident G v e → phi e = some alpha ∨ phi e = some delta →
        Sum.inl v ∈ K) → (
    ∀ z ∈ Z, Sum.inl z ∉ K) → (
    ∀ {e : E}, Sum.inr e ∈ K → phi e = some alpha ∨ phi e = some delta) →
    ∀ (q : Fin T.length), Sum.inr (T.edge q) ∉ K := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X i u0 u1 U Z alpha delta hone base_ne_block K
      vertex_mem_of_edge hKavoidsZ edge_colors_of_mem_K q hqK
  have hcolors := edge_colors_of_mem_K hqK
  by_cases hqzero : q.val = 0
  · have hqeq : q = ⟨0, T.positive⟩ := Fin.ext hqzero
    have hedge0 : T.edge q = e0 := by simpa [hqeq] using T.first_edge
    rcases hcolors with hc | hc <;> rw [hedge0, hone.1] at hc <;> simp at hc
  · obtain ⟨a, ha⟩ := T.attaches q
    let oldIndex : Fin (T.length + 1) :=
      Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))
    let newVertex := T.vertex q.succ
    let oldVertex := T.vertex oldIndex
    have hnewX : newVertex ∈ X := by simp [newVertex, X, TreeSequenceVertexSet]
    have holdX : oldVertex ∈ X := by simp [oldVertex, X, TreeSequenceVertexSet]
    have hnewInc : Incident G newVertex (T.edge q) := by
      simp [Incident, newVertex, ha]
    have holdInc : Incident G oldVertex (T.edge q) := by
      simp [Incident, oldVertex, oldIndex, ha]
    have hnewK : Sum.inl newVertex ∈ K :=
      vertex_mem_of_edge hqK hnewInc hcolors
    have holdK : Sum.inl oldVertex ∈ K :=
      vertex_mem_of_edge hqK holdInc hcolors
    have hnewU : newVertex ∈ U := by
      by_contra hnU
      exact hKavoidsZ newVertex (Finset.mem_sdiff.mpr ⟨hnewX, hnU⟩) hnewK
    have holdU : oldVertex ∈ U := by
      by_contra hoU
      exact hKavoidsZ oldVertex (Finset.mem_sdiff.mpr ⟨holdX, hoU⟩) holdK
    have hverticesNe : newVertex ≠ oldVertex := by
      intro hv
      have hi := T.vertex_injective hv
      have hiVal := congrArg Fin.val hi
      dsimp [newVertex, oldVertex, oldIndex] at hiVal
      have haLt := a.isLt
      omega
    have hnewCases : newVertex = u0 ∨ newVertex = u1 := by
      simpa [U] using hnewU
    have holdCases : oldVertex = u0 ∨ oldVertex = u1 := by
      simpa [U] using holdU
    let pos0 : Fin (T.length + 1) := ⟨C.p + 2 * i.val, by
      have hi := i.isLt
      have hl := C.length_eq
      omega⟩
    let pos1 : Fin (T.length + 1) := ⟨C.p + 2 * i.val + 1, by
      have hi := i.isLt
      have hl := C.length_eq
      omega⟩
    have hpos0 : T.vertex pos0 = u0 := by
      simpa [pos0, u0] using C.block_vertex_position i (0 : Fin 2)
    have hpos1 : T.vertex pos1 = u1 := by
      simpa [pos1, u1] using C.block_vertex_position i (1 : Fin 2)
    rcases hnewCases with hnew0 | hnew1
    · have hqpos : q.succ = pos0 := by
        apply T.vertex_injective
        exact hnew0.trans hpos0.symm
      have hold1 : oldVertex = u1 := by
        rcases holdCases with hold0 | hold1
        · exact False.elim (hverticesNe (hnew0.trans hold0.symm))
        · exact hold1
      have hapos : oldIndex = pos1 := by
        apply T.vertex_injective
        exact hold1.trans hpos1.symm
      have hqv := congrArg Fin.val hqpos
      have hav := congrArg Fin.val hapos
      have haLt := a.isLt
      dsimp [oldIndex, pos0, pos1] at hqv hav
      omega
    · have hqpos : q.succ = pos1 := by
        apply T.vertex_injective
        exact hnew1.trans hpos1.symm
      have hold0 : oldVertex = u0 := by
        rcases holdCases with hold0 | hold1
        · exact hold0
        · exact False.elim (hverticesNe (hnew1.trans hold1.symm))
      have hqval : q.val = C.p + 2 * i.val := by
        have hv := congrArg Fin.val hqpos
        dsimp [pos1] at hv
        omega
      let blockIndex : Fin T.length := ⟨C.p - 1 + 2 * i.val + 1, by
        have hi := i.isLt
        have hl := C.length_eq
        have hp2 := C.p_ge_two
        omega⟩
      have hqb : q = blockIndex := by
        apply Fin.ext
        dsimp [blockIndex]
        have hp2 := C.p_ge_two
        omega
      have hedgeBlock : T.edge q = C.blockEdge i 1 := by
        rw [hqb]
        simpa [blockIndex] using C.block_edge_position i (1 : Fin 2)
      obtain ⟨b, hb⟩ := C.block_attaches_to_base i (1 : Fin 2)
      have hyEnds : C.y b ∈ G.ends (T.edge q) := by
        rw [hedgeBlock, hb]
        simp
      rw [ha] at hyEnds
      have hyCases : C.y b = newVertex ∨ C.y b = oldVertex := by
        simpa [newVertex, oldVertex, oldIndex] using hyEnds
      rcases hyCases with hyNew | hyOld
      · exact base_ne_block b 1 (hyNew.trans (hnew1.trans rfl))
      · exact base_ne_block b 0 (hyOld.trans (hold0.trans rfl))

private theorem helper_htreePsi_732.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k);
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl u0); (
    ∀ (q : Fin T.length), Sum.inr (T.edge q) ∉ K) →
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha delta (Sum.inl u0);
        alpha ∈ MissingColors G psi y0 → (
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ delta → (c ∈ MissingColors G psi v ↔ c ∈ MissingColors
        G phi v)) → TashkinovTree G e0 psi T := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i u0 y0 alpha delta K tree_edges_outside_K psi hy0MissingPsi
      other_missing q hq
  obtain ⟨a, c, hcEdge, hcMissing⟩ := C.globally_maximum.2.1 q hq
  have hpsiEdge : psi (T.edge q) = some c := by
    simpa [psi, K, TwoColorComponentSwap, tree_edges_outside_K q] using hcEdge
  by_cases hca : c = alpha
  · subst c
    let zero : Fin (q.val + 1) := ⟨0, by omega⟩
    refine ⟨zero, alpha, hpsiEdge, ?_⟩
    have hvertex : T.vertex (Fin.castLT zero
        (Nat.lt_trans zero.isLt (Nat.succ_lt_succ q.isLt))) = y0 := by
      let vi : Fin (T.length + 1) := Fin.castLT zero
        (Nat.lt_trans zero.isLt (Nat.succ_lt_succ q.isLt))
      have hvi : vi = ⟨0, by
          have hl := C.length_eq
          omega⟩ := Fin.ext rfl
      change T.vertex vi = y0
      rw [hvi]
      simpa [y0] using C.base_vertex_position
        ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [hvertex] using hy0MissingPsi
  · have hcd : c ≠ delta := by
      intro hcd
      have hused : delta ∈ TreeUsedColors phi T := by
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨q, hq, by simpa [hcd] using hcEdge⟩
      exact (Finset.disjoint_left.mp
        (ScheideGlobalMaximumUnused G k e0 phi T C.globally_maximum).1)
          d.2 hused
    refine ⟨a, c, hpsiEdge, ?_⟩
    exact (other_missing _ c hca hcd).mpr hcMissing

private theorem helper_htreeS_766.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k);
    ∀ (ell : E),
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha delta (Sum.inl u0); psi
        ell = some alpha → alpha ∈ MissingColors G psi y0 → TashkinovTree G e0 psi T →
    ∀ (S : TreeSequence G e0), TreeSequenceAdjoinEdge T ell S → TashkinovTree G e0 psi S := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i u0 y0 alpha delta ell psi hellPsi hy0MissingPsi htreePsi S
      hTS
  rcases hTS with ⟨hlen, hinitial, hlast⟩
  rcases hinitial with ⟨hle, hvert, hedge⟩
  intro q hq
  by_cases hold : q.val < T.length
  · let qT : Fin T.length := ⟨q.val, hold⟩
    obtain ⟨a, c, hc, hm⟩ := htreePsi qT (by simpa [qT] using hq)
    let aS : Fin (q.val + 1) := ⟨a.val, by simpa [qT] using a.isLt⟩
    refine ⟨aS, c, ?_, ?_⟩
    · have hqeq : Fin.castLE hle qT = q := Fin.ext rfl
      rw [← hqeq, hedge]
      exact hc
    · let oldVertexIndex : Fin (T.length + 1) :=
        Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ qT.isLt))
      let newVertexIndex : Fin (S.length + 1) :=
        Fin.castLT aS (Nat.lt_trans aS.isLt (Nat.succ_lt_succ q.isLt))
      have hindex : Fin.castLE (Nat.succ_le_succ hle) oldVertexIndex =
          newVertexIndex := Fin.ext rfl
      have hvertex : S.vertex newVertexIndex = T.vertex oldVertexIndex := by
        rw [← hindex]
        exact hvert oldVertexIndex
      simpa [oldVertexIndex, newVertexIndex] using hvertex.symm ▸ hm
  · have hqval : q.val = T.length := by
      have hqbound : q.val < T.length + 1 := by simpa [hlen] using q.isLt
      omega
    let zero : Fin (q.val + 1) := ⟨0, by omega⟩
    refine ⟨zero, alpha, ?_, ?_⟩
    · have hqlast : q = Fin.cast hlen.symm (Fin.last T.length) := by
        apply Fin.ext
        simpa using hqval
      rw [hqlast, hlast]
      exact hellPsi
    · let oldZero : Fin (T.length + 1) := ⟨0, by omega⟩
      let newZero : Fin (S.length + 1) := Fin.castLT zero
        (Nat.lt_trans zero.isLt (Nat.succ_lt_succ q.isLt))
      have hindex : Fin.castLE (Nat.succ_le_succ hle) oldZero = newZero :=
        Fin.ext rfl
      have hvertex : S.vertex newZero = y0 := by
        rw [← hindex, hvert]
        simpa [oldZero, y0] using C.base_vertex_position
          ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
      simpa [newZero, hvertex] using hy0MissingPsi

private theorem helper_base_ne_block_716.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    ∀ (a : Fin C.p) (b : Fin (2 : ℕ)), C.y a ≠ C.blockVertex i b := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i a b hab
  let qa : Fin (T.length + 1) := ⟨a.val, by
    have ha := a.isLt
    have hi := i.isLt
    have hb := b.isLt
    have hl := C.length_eq
    omega⟩
  let qb : Fin (T.length + 1) := ⟨C.p + 2 * i.val + b.val, by
    have hi := i.isLt
    have hb := b.isLt
    have hl := C.length_eq
    omega⟩
  have hv : T.vertex qa = T.vertex qb := by
    rw [show T.vertex qa = C.y a by
      simpa [qa] using C.base_vertex_position a]
    rw [show T.vertex qb = C.blockVertex i b by
      simpa [qb] using C.block_vertex_position i b]
    exact hab
  have hq := congrArg Fin.val (T.vertex_injective hv)
  have ha := a.isLt
  dsimp [qa, qb] at hq
  omega

private theorem helper_other_missing_906.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
          TreeSequence G e0)
      (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi T C)
      (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
      let i : Fin C.s := D.gammaIndex d;
      let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
      let alpha : Fin k := D.alpha0;
      let delta : Fin k := (↑d : Fin k);
      let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl u0);
      let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha delta (Sum.inl u0);
      ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ delta → (c ∈ MissingColors G psi v ↔ c ∈
          MissingColors G phi v) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i u0 alpha delta K psi v c hca hcd
  have color_eq : ∀ e : E, psi e = some c ↔ phi e = some c := by
    intro e
    by_cases heK : Sum.inr e ∈ K
    · simp only [psi, K, TwoColorComponentSwap, heK, ite_eq_left]
      by_cases hea : phi e = some alpha
      · rw [ite_eq_left hea, hea]
        simp only [Option.some.injEq]
        constructor
        · intro hdc
          exact False.elim (hcd hdc.symm)
        · intro hac
          exact False.elim (hca hac.symm)
      · by_cases hed : phi e = some delta
        · rw [ite_eq_right hea, ite_eq_left hed, hed]
          simp only [Option.some.injEq]
          constructor
          · intro hac
            exact False.elim (hca hac.symm)
          · intro hdc
            exact False.elim (hcd hdc.symm)
        · rw [ite_eq_right hea, ite_eq_right hed]
    · simp [psi, K, TwoColorComponentSwap, heK]
  simp only [MissingColors, PresentColors, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_filter]
  constructor <;> intro hm hcPresent
  · obtain ⟨e, hve, hec⟩ := hcPresent
    exact hm ⟨e, hve, (color_eq e).mpr hec⟩
  · obtain ⟨e, hve, hec⟩ := hcPresent
    exact hm ⟨e, hve, (color_eq e).mp hec⟩

private theorem helper_hBsingleton_734.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let Z : Finset V := X \ U;
    let _ : DecidablePred fun (f : E) ↦
    ∃ w ∉ X, Incident G w f := fun (x : E) ↦ Classical.propDecidable ((fun (f : E) ↦
    ∃ w ∉ X, Incident G w f) x);
    let B : Finset E := {f ∈ BoundaryColorEdges G phi Z (↑d : Fin k) |
    ∃ w ∉ X, Incident G w f};
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let delta : Fin k := (↑d : Fin k); D.v0 d ∈ Z ∧ y0 ∈ Z ∧ (
    ∀ z ∈ Z,
    ∃! f : E, Incident G z f ∧ phi f = some delta) ∧ D.f0 d ∈ B ∧ Odd B.card → B.card = (1 : ℕ) →
        B = {D.f0 d} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X i u0 u1 U Z outsideDec B y0 delta hp hBcard
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hp.2.2.2.1, ?_⟩
  intro f hf
  have hsub : {D.f0 d, f} ⊆ B := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hp.2.2.2.1
    · exact hf
  have hc := Finset.card_le_card hsub
  by_contra hne
  have : ({D.f0 d, f} : Finset E).card = 2 := by
    simp [Ne.symm hne]
  omega

private theorem helper_edge_colors_of_mem_K_853.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k);
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha delta;
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl u0);
    ∀ {e : E}, Sum.inr e ∈ K → phi e = some alpha ∨ phi e = some delta := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i u0 alpha delta H K e heK
  have hsupp : Sum.inr e ∈ H.support := by
    apply SimpleGraph.mem_support_of_reachable (G := H)
      (u := Sum.inr e) (v := Sum.inl u0)
    · simp
    · exact SimpleGraph.ConnectedComponent.eq.mp heK
  obtain ⟨z, hz⟩ := H.mem_support.mp hsupp
  cases z with
  | inl v =>
      have hz' : Incident G v e ∧
          (phi e = some alpha ∨ phi e = some delta) := by
        simpa [H, TwoColorIncidenceGraph] using hz
      exact hz'.2
  | inr f =>
      have : False := by simp [H, TwoColorIncidenceGraph] at hz
      exact this.elim

private theorem helper_hxU_895.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let U : Finset V := { u0, u1 };
    let Z : Finset V := X \ U;
    let _ : DecidablePred fun (f : E) ↦
    ∃ w ∉ X, Incident G w f := fun (x : E) ↦ Classical.propDecidable ((fun (f : E) ↦
    ∃ w ∉ X, Incident G w f) x);
    let B : Finset E := {f ∈ BoundaryColorEdges G phi Z (↑d : Fin k) |
    ∃ w ∉ X, Incident G w f};
    let delta : Fin k := (↑d : Fin k); B = {D.f0 d} →
    ∀ (ell : E), ell ≠ D.f0 d → phi ell = some delta →
    ∀ x ∈ X,
    ∀ t ∉ X, G.ends ell = s(x, t) → x ∈ U := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X i u0 u1 U Z outsideDec B delta hBsingleton ell hellNe
      hellColor x hxX t htX hellEnds
  by_contra hxU
  have hxZ : x ∈ Z := Finset.mem_sdiff.mpr ⟨hxX, hxU⟩
  have hellB : ell ∈ B := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨(by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨x, hxZ, t, fun htZ => htX (Finset.mem_sdiff.mp htZ).1,
          hellEnds⟩), hellColor⟩, t, htX,
        by simp [Incident, hellEnds]⟩
  rw [hBsingleton] at hellB
  exact hellNe (by simpa using hellB)

private theorem helper_honePsi_922.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k); IsOneEdgeUncolored phi e0 → alpha ≠ delta →
    let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl u0);
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha delta (Sum.inl u0);
        IsOneEdgeUncolored psi e0 := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i u0 alpha delta hone hAlphaDelta K psi
  constructor
  · simp [psi, TwoColorComponentSwap, hone.1]
  · intro e he0
    obtain ⟨c, hc⟩ := hone.2 e he0
    by_cases heK : Sum.inr e ∈ K
    · by_cases hca : c = alpha
      · refine ⟨delta, ?_⟩
        simp [psi, K, TwoColorComponentSwap, heK, hc, hca]
      · by_cases hcd : c = delta
        · refine ⟨alpha, ?_⟩
          simp [psi, K, TwoColorComponentSwap, heK, hc, hcd,
            hAlphaDelta.symm]
        · refine ⟨c, ?_⟩
          simp [psi, K, TwoColorComponentSwap, heK, hc, hca, hcd]
    · exact ⟨c, by simpa [psi, K, TwoColorComponentSwap, heK] using hc⟩

private theorem helper_missing_fixed_outside_944.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k);
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl u0); (
    ∀ {v : V} {e : E}, Sum.inr e ∈ K → Incident G v e → phi e = some alpha ∨ phi e = some delta →
        Sum.inl v ∈ K) → (
    ∀ {e : E}, Sum.inr e ∈ K → phi e = some alpha ∨ phi e = some delta) →
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha delta (Sum.inl u0);
    ∀ (v : V), Sum.inl v ∉ K → MissingColors G psi v = MissingColors G phi v := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i u0 alpha delta K vertex_mem_of_edge edge_colors_of_mem_K
      psi v hv
  have edge_outside : ∀ e : E, Incident G v e → Sum.inr e ∉ K := by
    intro e hve heK
    exact hv (vertex_mem_of_edge heK hve (edge_colors_of_mem_K heK))
  have present_eq : PresentColors G psi v = PresentColors G phi v := by
    ext c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, hve, hc⟩
      refine ⟨e, hve, ?_⟩
      simpa [psi, K, TwoColorComponentSwap, edge_outside e hve] using hc
    · rintro ⟨e, hve, hc⟩
      refine ⟨e, hve, ?_⟩
      simpa [psi, K, TwoColorComponentSwap, edge_outside e hve] using hc
  simp only [MissingColors]
  rw [present_eq]

private theorem helper_hleOrder_974.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k);
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha delta (Sum.inl u0);
        IsProperEdgeColoring G psi → IsOneEdgeUncolored psi e0 →
    ∀ (S : TreeSequence G e0), TashkinovTree G e0 psi S → (TreeSequenceVertexSet S).card ≤
        TashkinovOrder G := by
  classical
  intro V E _ _ _ G k e0 phi T C D d i u0 alpha delta psi hproperPsi honePsi S htreeS
  unfold TashkinovOrder
  dsimp
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (by
    simp only [Finset.mem_filter, Finset.mem_range]
    have hk : ChromaticIndex G - 1 = k := by
      have hh := C.globally_maximum.1.2.1
      omega
    rw [hk]
    refine ⟨?_, e0, psi, S, ?_, htreeS, rfl⟩
    · have hV : (TreeSequenceVertexSet S).card ≤ Fintype.card V := by
        exact Finset.card_le_card (Finset.subset_univ _)
      omega
    · exact ⟨C.globally_maximum.1.1, C.globally_maximum.1.2.1,
        C.globally_maximum.1.2.2.1, hproperPsi, honePsi⟩)

private theorem helper_continuation_1038.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let i : Fin C.s := D.gammaIndex d;
    let u0 : V := C.blockVertex i (0 : Fin (2 : ℕ));
    let u1 : V := C.blockVertex i (1 : Fin (2 : ℕ));
    let U : Finset V := {u0, u1};
    let Z : Finset V := X \ U;
    let _ : DecidablePred fun (f : E) ↦
    ∃ w ∉ X, Incident G w f := fun (x : E) ↦ Classical.propDecidable ((fun (f : E) ↦
    ∃ w ∉ X, Incident G w f) x);
    let B : Finset E := {f ∈ BoundaryColorEdges G phi Z (↑d : Fin k) |
    ∃ w ∉ X, Incident G w f};
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let alpha : Fin k := D.alpha0;
    let delta : Fin k := (↑d : Fin k); D.v0 d ∈ Z ∧ y0 ∈ Z ∧ (
    ∀ z ∈ Z,
    ∃! f : E, Incident G z f ∧ phi f = some delta) ∧ D.f0 d ∈ B ∧ Odd B.card → B = {D.f0 d} →
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 → ColoredVertexSetClosed G phi X →
        alpha ∈ MissingColors G phi y0 → alpha ≠ delta →
    ∀ (h : E), phi h = some alpha → G.ends h = s(C.blockVertex i (0 : Fin (2 : ℕ)), C.blockVertex
        i (1 : Fin (2 : ℕ))) → (
    ∀ (a : Fin C.p) (b : Fin (2 : ℕ)), C.y a ≠ C.blockVertex i b) → u0 ∈ U → u0 ∉ Z → Incident G
        u0 h → Incident G u1 h →
    let I : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl y0);
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha delta (Sum.inl u0); Sum.inl y0 ∈ I →
        Sum.inl u0 ∈ K → (
    ∀ {v : V} {e : E}, Sum.inl v ∈ K → Incident G v e → phi e = some alpha ∨ phi e = some delta →
        Sum.inr e ∈ K) → (
    ∀ {v : V} {e : E}, Sum.inr e ∈ K → Incident G v e → phi e = some alpha ∨ phi e = some delta →
        Sum.inl v ∈ K) → Sum.inl u1 ∈ K → U ⊆ X → False := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d X i u0 u1 U Z outsideDec B y0 alpha delta hp hBsingleton
      hproper hone hclosed hy0Missing hAlphaDelta h hhcolor hhends base_ne_block hu0U hu0notZ
      hhInc0 hhInc1 I K hrootI hrootK edge_mem_of_vertex vertex_mem_of_edge hu1K hUsubX
  have initial_avoids_U := @helper_initial_avoids_U_217 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 phi T C D d hp hBsingleton hproper hclosed hy0Missing h
      hhcolor hhends hhInc0 hhInc1 hUsubX
  have hu0notI : Sum.inl u0 ∉ I := initial_avoids_U u0 hu0U
  have hKI : Disjoint K I := by
    rcases TwoColorComponentsDisjoint G phi alpha delta (Sum.inl u0) (Sum.inl y0) with heq | hd
    · exfalso
      apply hu0notI
      have heq' : K = I := by simpa [K, I] using heq
      rw [← heq']
      exact hrootK
    · exact hd
  have hKavoidsZ := @helper_hKavoidsZ_366 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d hp hBsingleton hproper hclosed hy0Missing h hhcolor hhends
      hu0notZ hhInc0 hhInc1 hKI
  have edge_colors_of_mem_K := @helper_edge_colors_of_mem_K_853 V E inferInstance inferInstance
      inferInstance G k e0 phi T C D d
  have tree_edges_outside_K := @helper_tree_edges_outside_K_506 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 phi T C D d hone base_ne_block vertex_mem_of_edge hKavoidsZ
      edge_colors_of_mem_K
  let BX := BoundaryColorEdges G phi X delta
  have hf0BX : D.f0 d ∈ BX := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simpa [delta] using D.f0_color d⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨D.v0 d, (Finset.mem_sdiff.mp hp.1).1, D.u0 d,
      by simpa [X] using D.u0_outside d, D.f0_ends d⟩
  have hBXcard : 3 ≤ BX.card := by
    simpa [BX, X, delta] using
      (ScheideGlobalMaximumBoundaryFacts G k e0 phi T C.globally_maximum).2.2
        delta (by simp [delta]) |>.2
  have hErasePos : 0 < (BX.erase (D.f0 d)).card := by
    rw [Finset.card_erase_of_mem hf0BX]
    omega
  obtain ⟨ell, hellErase⟩ := Finset.card_pos.mp hErasePos
  have hellNe : ell ≠ D.f0 d := (Finset.mem_erase.mp hellErase).1
  have hellBX : ell ∈ BX := (Finset.mem_erase.mp hellErase).2
  have hellBoundary : ell ∈ BoundaryEdges G X :=
    (Finset.mem_filter.mp hellBX).1
  have hellColor : phi ell = some delta :=
    (Finset.mem_filter.mp hellBX).2
  obtain ⟨x, hxX, t, htX, hellEnds⟩ := by
    simpa [BoundaryEdges] using hellBoundary
  have hxU := @helper_hxU_895 V E inferInstance inferInstance inferInstance inferInstance G k e0 phi
      T C D d hBsingleton ell hellNe hellColor x hxX t htX hellEnds
  have hxK : Sum.inl x ∈ K := by
    have hxCases : x = u0 ∨ x = u1 := by simpa [U] using hxU
    rcases hxCases with rfl | rfl
    · exact hrootK
    · exact hu1K
  have hxInc : Incident G x ell := by simp [Incident, hellEnds]
  have hellK : Sum.inr ell ∈ K :=
    edge_mem_of_vertex hxK hxInc (Or.inr hellColor)
  let psi := TwoColorComponentSwap G phi alpha delta (Sum.inl u0)
  have hproperPsi : IsProperEdgeColoring G psi := by
    simpa [psi, alpha, delta, u0] using
      TwoColorComponentSwapProper G phi alpha delta hAlphaDelta hproper
        (Sum.inl u0)
  have honePsi := @helper_honePsi_922 V E inferInstance inferInstance inferInstance G k e0 phi T C D
      d hone hAlphaDelta
  have hellPsi : psi ell = some alpha := by
    simp [psi, K, TwoColorComponentSwap, hellK, hellColor,
      hAlphaDelta.symm]
  have hy0notK : Sum.inl y0 ∉ K := by
    intro hyK
    exact (Set.disjoint_left.mp hKI) hyK hrootI
  have missing_fixed_outside := @helper_missing_fixed_outside_944 V E inferInstance inferInstance
      inferInstance G k e0 phi T C D d vertex_mem_of_edge edge_colors_of_mem_K
  have hy0MissingPsi : alpha ∈ MissingColors G psi y0 := by
    rw [missing_fixed_outside y0 hy0notK]
    exact hy0Missing
  have other_missing := @helper_other_missing_906 V E inferInstance inferInstance inferInstance G k
      e0 phi T C D d
  have htreePsi := @helper_htreePsi_732 V E inferInstance inferInstance inferInstance G k e0 phi T C
      D d tree_edges_outside_K hy0MissingPsi other_missing
  obtain ⟨S, hTS⟩ := TreeSequenceBoundaryEdgeAppendExists T ell (by
    simpa [X] using hellBoundary)
  have htreeS := @helper_htreeS_766 V E inferInstance inferInstance inferInstance G k e0 phi T C D d
      ell hellPsi hy0MissingPsi htreePsi S hTS
  have hleOrder := @helper_hleOrder_974 V E inferInstance inferInstance inferInstance G k e0 phi T C
      D d hproperPsi honePsi S htreeS
  have hcardS : (TreeSequenceVertexSet S).card = S.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      S.vertex_injective]
  have hcardT : X.card = T.length + 1 := by
    simp [X, TreeSequenceVertexSet, Finset.card_image_of_injective,
      T.vertex_injective]
  have hlen : S.length = T.length + 1 := hTS.1
  have hglobalCard : X.card = TashkinovOrder G := by
    simpa [X] using C.globally_maximum.2.2
  rw [hcardS, hlen, ← hglobalCard, hcardT] at hleOrder
  omega

theorem ScheideReplacementBoundaryAtLeastThree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) },
    let X := TreeSequenceVertexSet T
    let Z := X \ {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}
    let B :=
      @Finset.filter E (fun f => ∃ w, w ∉ X ∧ Incident G w f)
        (fun _ => Classical.propDecidable _) (BoundaryColorEdges G phi Z d.1)
    3 ≤ B.card := by
  classical
  intro d
  dsimp only
  let X := TreeSequenceVertexSet T
  let i := D.gammaIndex d
  let u0 := C.blockVertex i 0
  let u1 := C.blockVertex i 1
  let U := ({u0, u1} : Finset V)
  let Z := X \ U
  let outsideDec : DecidablePred (fun f : E =>
      ∃ w, w ∉ X ∧ Incident G w f) :=
    fun _ => Classical.propDecidable _
  let B := (BoundaryColorEdges G phi Z d.1).filter
    (fun f => ∃ w, w ∉ X ∧ Incident G w f)
  let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  let alpha := D.alpha0
  let delta := d.1
  change 3 ≤ B.card
  have hp0 := ScheideReplacementBoundaryParity G k e0 phi T C D d
  have hp : D.v0 d ∈ Z ∧ y0 ∈ Z ∧
      (∀ z ∈ Z, ∃! f : E, Incident G z f ∧ phi f = some delta) ∧
      D.f0 d ∈ B ∧ Odd B.card := by
    simpa only [X, i, u0, u1, U, Z, B, y0, delta] using hp0
  by_contra hnot
  have hsmall : B.card < 3 := Nat.lt_of_not_ge hnot
  have hBcard : B.card = 1 := by
    rcases hp.2.2.2.2 with ⟨q, hq⟩
    have hpos : 0 < B.card := Finset.card_pos.mpr ⟨D.f0 d, hp.2.2.2.1⟩
    omega
  have hBsingleton := @helper_hBsingleton_734 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 phi T C D d hp hBcard
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 :=
    C.globally_maximum.1.2.2.2.2
  have hclosed : ColoredVertexSetClosed G phi X :=
    (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
  have hy0Missing : alpha ∈ MissingColors G phi y0 := by
    simpa [alpha, y0] using D.alpha0_missing_at_y0
  have hAlphaDelta : alpha ≠ delta := by
    intro h
    obtain ⟨f, hf, hfc⟩ := hp.2.2.1 y0 hp.2.1
    have hpresent : delta ∈ PresentColors G phi y0 := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, hf.1, hf.2⟩
    have : alpha ∉ PresentColors G phi y0 := by
      simpa [MissingColors] using hy0Missing
    exact this (by simpa [h] using hpresent)
  have hAlphaGamma : alpha ≠ C.gamma i := by
    simpa [alpha, i] using D.alpha0_not_block i
  obtain ⟨h, hhcolor, hhends⟩ :=
    ScheideStructuralInternalPair G k e0 phi T C i alpha hAlphaGamma
      ⟨y0, hp.2.1, hy0Missing⟩
  have hu0X : u0 ∈ X := by
    unfold u0 X
    rw [← C.block_vertex_position i 0]
    simp [TreeSequenceVertexSet]
  have hu1X : u1 ∈ X := by
    unfold u1 X
    rw [← C.block_vertex_position i 1]
    simp [TreeSequenceVertexSet]
  have base_ne_block := @helper_base_ne_block_716 V E inferInstance inferInstance inferInstance G k
      e0 phi T C D d
  have hu0U : u0 ∈ U := by simp [U]
  have hu1U : u1 ∈ U := by simp [U]
  have hu0notZ : u0 ∉ Z := fun hz => (Finset.mem_sdiff.mp hz).2 hu0U
  have hu1notZ : u1 ∉ Z := fun hz => (Finset.mem_sdiff.mp hz).2 hu1U
  have hhInc0 : Incident G u0 h := by simp [Incident, u0, hhends]
  have hhInc1 : Incident G u1 h := by simp [Incident, u1, hhends]
  let H := TwoColorIncidenceGraph G phi alpha delta
  let I := TwoColorComponent G phi alpha delta (Sum.inl y0)
  let K := TwoColorComponent G phi alpha delta (Sum.inl u0)
  have hrootI : Sum.inl y0 ∈ I := by
    change H.connectedComponentMk (Sum.inl y0) = H.connectedComponentMk (Sum.inl y0)
    rfl
  have hrootK : Sum.inl u0 ∈ K := by
    change H.connectedComponentMk (Sum.inl u0) = H.connectedComponentMk (Sum.inl u0)
    rfl
  have edge_mem_of_vertex {v : V} {e : E}
      (hv : Sum.inl v ∈ K) (hve : Incident G v e)
      (hc : phi e = some alpha ∨ phi e = some delta) : Sum.inr e ∈ K := by
    have ha : H.Adj (Sum.inl v) (Sum.inr e) := by
      simpa [H, TwoColorIncidenceGraph] using ⟨hve, hc⟩
    change H.connectedComponentMk (Sum.inl v) = H.connectedComponentMk (Sum.inl u0) at hv
    change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk (Sum.inl u0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).symm.trans hv
  have vertex_mem_of_edge {v : V} {e : E}
      (he : Sum.inr e ∈ K) (hve : Incident G v e)
      (hc : phi e = some alpha ∨ phi e = some delta) : Sum.inl v ∈ K := by
    have ha : H.Adj (Sum.inl v) (Sum.inr e) := by
      simpa [H, TwoColorIncidenceGraph] using ⟨hve, hc⟩
    change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk (Sum.inl u0) at he
    change H.connectedComponentMk (Sum.inl v) = H.connectedComponentMk (Sum.inl u0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).trans he
  have hhK : Sum.inr h ∈ K := edge_mem_of_vertex hrootK hhInc0 (Or.inl hhcolor)
  have hu1K : Sum.inl u1 ∈ K := vertex_mem_of_edge hhK hhInc1 (Or.inl hhcolor)
  have hUsubX : U ⊆ X := by
    intro v hv
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hu0X
    · exact hu1X
  exact @helper_continuation_1038 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D d hp hBsingleton hproper hone hclosed hy0Missing hAlphaDelta h hhcolor hhends
      base_ne_block hu0U hu0notZ hhInc0 hhInc1 hrootI hrootK edge_mem_of_vertex
      vertex_mem_of_edge hu1K hUsubX
end GoldbergSeymour

end
