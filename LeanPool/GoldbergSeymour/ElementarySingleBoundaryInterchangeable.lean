/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidencePathFacts
public import LeanPool.GoldbergSeymour.BoundaryColorEdges

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

public import LeanPool.GoldbergSeymour.TreeInterchangeable

public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint

/-!
# Elementary Single Boundary Interchangeable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_boundary_of_walk_52.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k),
        BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha = ∅ →
    ∀ {a b : V} (p : (TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).Walk (Sum.inl
        a) (Sum.inl b)), a ∈ (TreeSequenceVertexSet T : Finset V) → b ∉ (TreeSequenceVertexSet T :
        Finset V) →
    ∃ f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T : Finset V) beta, Sum.inr f ∈
        p.support := by
  classical
  intro V E _ _ G k e0 phi T alpha beta halpha
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta
  set X : Finset V := TreeSequenceVertexSet T
  intro a b p ha hb
  let S : Set (Sum V E) := {y | match y with
    | Sum.inl q => q ∈ X
    | Sum.inr f => ∀ q, Incident G q f → q ∈ X}
  have hSa : Sum.inl a ∈ S := by simpa [S] using ha
  have hSb : Sum.inl b ∉ S := by simpa [S] using hb
  obtain ⟨d, hd, hds, hdt⟩ := p.exists_boundary_dart S hSa hSb
  have hadj := d.adj
  have hfirst : ∃ q : V, d.toProd.1 = Sum.inl q ∧ q ∈ X := by
    cases h : d.toProd.1 with
    | inl q =>
        rw [h] at hds
        exact ⟨q, rfl, by simpa [S] using hds⟩
    | inr f =>
        exfalso
        cases h2 : d.toProd.2 with
        | inl r =>
            rw [h, h2] at hadj
            change Incident G r f ∧
              (phi f = some alpha ∨ phi f = some beta) at hadj
            rw [h] at hds
            have hall : ∀ q, Incident G q f → q ∈ X := by
              simpa [S] using hds
            have hrnot : r ∉ X := by
              intro hr
              apply hdt
              simpa [S, h2] using hr
            exact hrnot (hall r hadj.1)
        | inr e =>
            rw [h, h2] at hadj
            exact hadj.elim
  obtain ⟨q, hq, hqX⟩ := hfirst
  have hsecond : ∃ f : E, d.toProd.2 = Sum.inr f := by
    cases h : d.toProd.2 with
    | inl r =>
        rw [hq, h] at hadj
        exact hadj.elim
    | inr f => exact ⟨f, rfl⟩
  obtain ⟨f, hf⟩ := hsecond
  have hfadj : H.Adj (Sum.inl q) (Sum.inr f) := by
    rw [hq, hf] at hadj
    exact hadj
  have hfdata : Incident G q f ∧
      (phi f = some alpha ∨ phi f = some beta) := by
    simpa [H, TwoColorIncidenceGraph] using hfadj
  have hnotall : ¬ ∀ r, Incident G r f → r ∈ X := by
    intro hall
    apply hdt
    simpa [S, hf, hall]
  obtain ⟨r, hrf, hrX⟩ : ∃ r, Incident G r f ∧ r ∉ X := by
    push Not at hnotall
    exact hnotall
  have hqr : q ≠ r := by
    intro h
    exact hrX (h ▸ hqX)
  have hend : G.ends f = s(q, r) :=
    (Sym2.mem_and_mem_iff hqr).mp ⟨hfdata.1, hrf⟩
  have hfb : f ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q, hqX, r, hrX, hend⟩
  have hfcolor : phi f = some beta := by
    rcases hfdata.2 with hfa | hfbeta
    · have : f ∈ BoundaryColorEdges G phi X alpha := by
        simp [BoundaryColorEdges, hfb, hfa]
      rw [halpha] at this
      simp at this
    · exact hfbeta
  refine ⟨f, ?_, ?_⟩
  · simp [BoundaryColorEdges, hfb, hfcolor]
  · rw [← hf]
    exact p.dart_snd_mem_support_of_mem_darts hd

private theorem helper_endpoint_missing_142.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        (phi : PartialEdgeColoring E k) (alpha beta : Fin k), alpha ≠ beta →
    ∀ (v : V), ((TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).neighborSet
        (Sum.inl v)).Subsingleton → alpha ∈ MissingColors G phi v ∨ beta ∈ MissingColors G phi v
  := by
  classical
  intro V E _ _ G k phi alpha beta
  let _ := Fintype.ofFinite V
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta
  intro hne v hleaf
  by_cases ha : alpha ∈ MissingColors G phi v
  · exact Or.inl ha
  · right
    have hap : alpha ∈ PresentColors G phi v := by
      simpa [MissingColors] using ha
    by_contra hb
    have hbp : beta ∈ PresentColors G phi v := by
      simpa [MissingColors] using hb
    obtain ⟨ea, hea, hca⟩ := by simpa [PresentColors] using hap
    obtain ⟨eb, heb, hcb⟩ := by simpa [PresentColors] using hbp
    have hada : H.Adj (Sum.inl v) (Sum.inr ea) := by
      simpa [H, TwoColorIncidenceGraph] using
        (show Incident G v ea ∧
            (phi ea = some alpha ∨ phi ea = some beta) from
          ⟨hea, Or.inl hca⟩)
    have hadb : H.Adj (Sum.inl v) (Sum.inr eb) := by
      simpa [H, TwoColorIncidenceGraph] using
        (show Incident G v eb ∧
            (phi eb = some alpha ∨ phi eb = some beta) from
          ⟨heb, Or.inr hcb⟩)
    have heab : ea = eb := Sum.inr.inj (hleaf hada hadb)
    subst eb
    exact hne (Option.some.inj (hca.symm.trans hcb))

private theorem helper_branch_198.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {k : ℕ} (phi :
        PartialEdgeColoring E k) (alpha beta : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta;
    ∀ (c low a b : V ⊕ E) (p : (TwoColorIncidenceGraph G phi alpha beta).Walk a b), p.IsPath →
        {x : V ⊕ E | x ∈ p.support} = TwoColorComponent G phi alpha beta c → low ∈ p.support → low
        = b →
    ∃ (b : V ⊕ E) (p : H.Walk low b), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G
        phi alpha beta c := by
  classical
  intro V E G k phi alpha beta H c low a b p hp hps hlowP hlb
  subst b
  refine ⟨a, p.reverse, hp.reverse, ?_⟩
  ext y
  change y ∈ p.reverse.support ↔
    y ∈ TwoColorComponent G phi alpha beta c
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  exact Set.ext_iff.mp hps y

private theorem helper_branch_206.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta;
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (c : V ⊕ E), (
    ∃ x ∈ X, Sum.inl x ∈ TwoColorComponent G phi alpha beta c) →
    ∀ (low b : V ⊕ E) (p : H.Walk low b), {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi
        alpha beta c → p.Nil → (
    ∃ x ∈ X, TwoColorComponent G phi alpha beta c = {Sum.inl x} ∧ alpha ∈ MissingColors G phi x ∧
        beta ∈ MissingColors G phi x) ∨
    ∃ (r : V) (s : V) (p : H.Walk (Sum.inl r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support}
        = TwoColorComponent G phi alpha beta c ∧ r ≠ s ∧ (alpha ∈ MissingColors G phi r ∨ beta ∈
        MissingColors G phi r) ∧ (alpha ∈ MissingColors G phi s ∨ beta ∈ MissingColors G phi s) ∧
        (r ∈ X ∧ s ∈ X ∨
    ∃ f ∈ BoundaryColorEdges G phi X beta, Sum.inr f ∈ TwoColorComponent G phi alpha beta c ∧ (r ∈
        X ∨ s ∈ X)) := by
  classical
  intro V E _ _ G k e0 phi T alpha beta H X c hcX low b p hps hnil
  obtain ⟨x, hxX, hxC⟩ := hcX
  have hxP : Sum.inl x ∈ p.support := by
    change Sum.inl x ∈ {y | y ∈ p.support}
    rw [hps]
    exact hxC
  have hxlow : Sum.inl x = low := by
    rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] at hxP
    simpa using hxP
  have hCsingle : TwoColorComponent G phi alpha beta c =
      {Sum.inl x} := by
    rw [← hps]
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff,
      SimpleGraph.Walk.nil_iff_support_eq.mp hnil]
    simp [hxlow]
  have hmissing : ∀ d : Fin k,
      (d = alpha ∨ d = beta) → d ∈ MissingColors G phi x := by
    intro d hd
    have hnotpresent : d ∉ PresentColors G phi x := by
      intro hpresent
      obtain ⟨e, heinc, hecolor⟩ := by
        simpa [PresentColors] using hpresent
      have hepair : phi e = some alpha ∨ phi e = some beta :=
        hd.elim
          (fun h => Or.inl (hecolor.trans (congrArg some h)))
          (fun h => Or.inr (hecolor.trans (congrArg some h)))
      have hadj : H.Adj (Sum.inl x) (Sum.inr e) := by
        simpa [H, TwoColorIncidenceGraph] using
          (show Incident G x e ∧
              (phi e = some alpha ∨ phi e = some beta) from
            ⟨heinc, hepair⟩)
      have hedgeC : Sum.inr e ∈
          TwoColorComponent G phi alpha beta c := by
        change H.connectedComponentMk (Sum.inr e) =
          H.connectedComponentMk c
        change H.connectedComponentMk (Sum.inl x) =
          H.connectedComponentMk c at hxC
        exact
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj).symm.trans hxC
      rw [hCsingle] at hedgeC
      simp at hedgeC
    simpa [MissingColors] using hnotpresent
  left
  exact ⟨x, hxX, hCsingle, hmissing alpha (Or.inl rfl),
    hmissing beta (Or.inr rfl)⟩

private theorem helper_branch_451.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta;
    let X : Finset V := TreeSequenceVertexSet T; (
    ∀ {a b : V} (p : H.Walk (Sum.inl a) (Sum.inl b)), a ∈ X → b ∉ X →
    ∃ f ∈ BoundaryColorEdges G phi X beta, Sum.inr f ∈ p.support) →
    ∀ (c : V ⊕ E) (r s : V) (p : H.Walk (Sum.inl r) (Sum.inl s)), {y : V ⊕ E | y ∈ p.support} =
        TwoColorComponent G phi alpha beta c → r ∈ X → r ∈ X ∧ s ∈ X ∨
    ∃ f ∈ BoundaryColorEdges G phi X beta, Sum.inr f ∈ TwoColorComponent G phi alpha beta c ∧ (r ∈
        X ∨ s ∈ X) := by
  classical
  intro V E _ _ G k e0 phi T alpha beta H X boundary_of_walk c r s p hps hrX
  by_cases hsX : s ∈ X
  · exact Or.inl ⟨hrX, hsX⟩
  · right
    obtain ⟨f, hfB, hfP⟩ := boundary_of_walk p hrX hsX
    have hfC : Sum.inr f ∈
        TwoColorComponent G phi alpha beta c := by
      rw [← hps]
      exact hfP
    exact ⟨f, hfB, hfC, Or.inl hrX⟩

private theorem helper_branch_460.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta;
    let X : Finset V := TreeSequenceVertexSet T; (BoundaryColorEdges G phi X beta).card ≤ (1 : ℕ)
        → (
    ∀ {a b : V} (p : H.Walk (Sum.inl a) (Sum.inl b)), a ∈ X → b ∉ X →
    ∃ f ∈ BoundaryColorEdges G phi X beta, Sum.inr f ∈ p.support) →
    ∀ (c : V ⊕ E), (
    ∃ x ∈ X, Sum.inl x ∈ TwoColorComponent G phi alpha beta c) →
    ∀ (r s : V) (p : H.Walk (Sum.inl r) (Sum.inl s)), p.IsPath → {y : V ⊕ E | y ∈ p.support} =
        TwoColorComponent G phi alpha beta c → r ∉ X → r ∈ X ∧ s ∈ X ∨
    ∃ f ∈ BoundaryColorEdges G phi X beta, Sum.inr f ∈ TwoColorComponent G phi alpha beta c ∧ (r ∈
        X ∨ s ∈ X) := by
  classical
  intro V E _ _ G k e0 phi T alpha beta H X hbeta boundary_of_walk c hcX r s p hp hps hrX
  by_cases hsX : s ∈ X
  · right
    obtain ⟨f, hfB, hfP⟩ := boundary_of_walk p.reverse hsX hrX
    have hfP' : Sum.inr f ∈ p.support := by
      simpa only [SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hfP
    have hfC : Sum.inr f ∈
        TwoColorComponent G phi alpha beta c := by
      rw [← hps]
      exact hfP'
    exact ⟨f, hfB, hfC, Or.inr hsX⟩
  · obtain ⟨x, hxX, hxC⟩ := hcX
    have hxP : Sum.inl x ∈ p.support := by
      change Sum.inl x ∈ {y | y ∈ p.support}
      rw [hps]
      exact hxC
    let pleft := (p.takeUntil (Sum.inl x) hxP).reverse
    let pright := p.dropUntil (Sum.inl x) hxP
    obtain ⟨f1, hf1B, hf1P⟩ :=
      boundary_of_walk pleft hxX hrX
    obtain ⟨f2, hf2B, hf2P⟩ :=
      boundary_of_walk pright hxX hsX
    have hf1take : Sum.inr f1 ∈
        (p.takeUntil (Sum.inl x) hxP).support := by
      simpa only [pleft, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hf1P
    have hf2drop : Sum.inr f2 ∈
        (p.dropUntil (Sum.inl x) hxP).support := by
      exact hf2P
    have happ : ((p.takeUntil (Sum.inl x) hxP).append
        (p.dropUntil (Sum.inl x) hxP)).IsPath := by
      rw [p.take_spec hxP]
      exact hp
    have hfne : f1 ≠ f2 := by
      intro heq
      exact
        (happ.ne_of_mem_support_of_append (by simp)
          hf1take hf2drop) (congrArg Sum.inr heq)
    have hsubset : ({f1, f2} : Finset E) ⊆
        BoundaryColorEdges G phi X beta := by
      intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hf1B
      · exact hf2B
    have htwo : 2 ≤ (BoundaryColorEdges G phi X beta).card := by
      have hle := Finset.card_le_card hsubset
      have hpair : ({f1, f2} : Finset E).card = 2 := by
        simp [hfne]
      omega
    have hbetaX : (BoundaryColorEdges G phi X beta).card ≤ 1 := by
      simpa [X] using hbeta
    exact False.elim (by omega)

private theorem helper_analyze_168.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k),
        IsProperEdgeColoring G phi → (BoundaryColorEdges G phi (TreeSequenceVertexSet T)
        beta).card ≤ (1 : ℕ) → (
    ∀ {a b : V} (p : (TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).Walk (Sum.inl
        a) (Sum.inl b)), a ∈ (TreeSequenceVertexSet T : Finset V) → b ∉ (TreeSequenceVertexSet T :
        Finset V) →
    ∃ f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T : Finset V) beta, Sum.inr f ∈
        p.support) →
    ∀ (_ : V ⊕ E), (
    ∀ (v : V), ((TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).neighborSet
        (Sum.inl v)).Subsingleton → alpha ∈ MissingColors G phi v ∨ beta ∈ MissingColors G phi v)
        →
    ∀ (c : V ⊕ E), TwoColorPathComponent G phi alpha beta c → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ TwoColorComponent G phi alpha beta c)
        → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), TwoColorComponent G phi alpha beta c = {Sum.inl x}
        ∧ alpha ∈ MissingColors G phi x ∧ beta ∈ MissingColors G phi x) ∨
    ∃ (r : V) (s : V) (p : (TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi
        alpha beta c ∧ r ≠ s ∧ (alpha ∈ MissingColors G phi r ∨ beta ∈ MissingColors G phi r) ∧
        (alpha ∈ MissingColors G phi s ∨ beta ∈ MissingColors G phi s) ∧ (r ∈
        (TreeSequenceVertexSet T : Finset V) ∧ s ∈ (TreeSequenceVertexSet T : Finset V) ∨
    ∃ f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T : Finset V) beta, Sum.inr f ∈
        TwoColorComponent G phi alpha beta c ∧ (r ∈ (TreeSequenceVertexSet T : Finset V) ∨ s ∈
        (TreeSequenceVertexSet T : Finset V))) := by
  classical
  intro V E _ _ G k e0 phi T alpha beta hproper hbeta
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta
  set X : Finset V := TreeSequenceVertexSet T
  intro boundary_of_walk z endpoint_missing c hc hcX
  obtain ⟨low, hlowC, hlow⟩ := hc.2
  obtain ⟨a, b, p, hp, hps⟩ :=
    TwoColorComponentSpanningPath G phi alpha beta hproper c
  have hlowP : low ∈ p.support := by
    change low ∈ {y | y ∈ p.support}
    rw [hps]
    exact hlowC
  have hlowEnd : low = a ∨ low = b := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hlow) hlowP
  obtain ⟨b, p, hp, hps⟩ : ∃ (b : Sum V E) (p : H.Walk low b),
      p.IsPath ∧ {y | y ∈ p.support} =
        TwoColorComponent G phi alpha beta c := by
    rcases hlowEnd with hla | hlb
    · subst a
      exact ⟨b, p, hp, hps⟩
    · exact @helper_branch_198 (@V) (@E) (@G) (@k) (@phi) (@alpha) (@beta) (@c) (@low) (@a) (@b)
        (@p) (@hp) (@hps) (@hlowP) (@hlb)
  by_cases hnil : p.Nil
  · exact @helper_branch_206 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T)
      (@alpha) (@beta) (@c) (@hcX) (@low) (@b) (@p) (@hps) (@hnil)
  · have hstartVertex : ∃ r : V, low = Sum.inl r :=
      incidenceLeafEndVertex p.reverse
        (by simpa only [SimpleGraph.Walk.length_reverse] using
          (SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil)) hlow
    obtain ⟨r, hr⟩ := hstartVertex
    subst low
    have hend_neighbor := degreeTwoComponentPathEndNeighbor p hp
      (TwoColorIncidenceDegreeAtMostTwo G phi alpha beta hproper)
      hlow hps
    have hendLeaf : Set.Subsingleton (H.neighborSet b) := by
      intro y hy y' hy'
      exact (hend_neighbor y hy).trans (hend_neighbor y' hy').symm
    have hp_pos : 0 < p.length :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil
    have hendVertex := incidenceLeafEndVertex p hp_pos hendLeaf
    obtain ⟨s, hs⟩ := hendVertex
    subst b
    have hrs : r ≠ s := by
      intro hrs
      apply hnil
      exact hp.nil_iff_eq.mpr (by simp [hrs])
    have hrmissing := endpoint_missing r hlow
    have hsmissing := endpoint_missing s hendLeaf
    have hrC : Sum.inl r ∈ TwoColorComponent G phi alpha beta c := by
      rw [← hps]
      change Sum.inl r ∈ p.support
      simp
    have hsC : Sum.inl s ∈ TwoColorComponent G phi alpha beta c := by
      rw [← hps]
      change Sum.inl s ∈ p.support
      simpa only [p.getVert_length] using
        p.getVert_mem_support p.length
    right
    refine ⟨r, s, p, hp, hps, hrs, hrmissing, hsmissing, ?_⟩
    by_cases hrX : r ∈ X
    · exact @helper_branch_451 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T)
        (@alpha) (@beta) (@boundary_of_walk) (@c) (@r) (@s) (@p) (@hps) (@hrX)
    · exact @helper_branch_460 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T)
        (@alpha) (@beta) (@hbeta) (@boundary_of_walk) (@c) (@hcX) (@r) (@s) (@p) (@hp) (@hps) (@hrX)
private theorem helper_branch_562.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k),
    ∀ (z w : V ⊕ E), ((
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), TwoColorComponent G phi alpha beta w = {Sum.inl x}
        ∧ alpha ∈ MissingColors G phi x ∧ beta ∈ MissingColors G phi x) ∨
    ∃ (r : V) (s : V) (p : (TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi
        alpha beta w ∧ r ≠ s ∧ (alpha ∈ MissingColors G phi r ∨ beta ∈ MissingColors G phi r) ∧
        (alpha ∈ MissingColors G phi s ∨ beta ∈ MissingColors G phi s) ∧ (r ∈
        (TreeSequenceVertexSet T : Finset V) ∧ s ∈ (TreeSequenceVertexSet T : Finset V) ∨
    ∃ f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T : Finset V) beta, Sum.inr f ∈
        TwoColorComponent G phi alpha beta w ∧ (r ∈ (TreeSequenceVertexSet T : Finset V) ∨ s ∈
        (TreeSequenceVertexSet T : Finset V)))) → (
    ∀ {u v : V}, u ∈ (TreeSequenceVertexSet T : Finset V) → v ∈ (TreeSequenceVertexSet T : Finset
        V) → u ≠ v →
    ∀ {d : Fin k}, d ∈ MissingColors G phi u → d ∈ MissingColors G phi v → False) → (
    ∀ {u v : V}, Sum.inl u ∈ TwoColorComponent G phi alpha beta z → Sum.inl v ∈ TwoColorComponent
        G phi alpha beta w → u ≠ v) → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), TwoColorComponent G phi alpha beta z = {Sum.inl x}
        ∧ alpha ∈ MissingColors G phi x ∧ beta ∈ MissingColors G phi x) → False := by
  classical
  intro V E _ _ G k e0 phi T alpha beta
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta
  set X : Finset V := TreeSequenceVertexSet T
  intro z w hwdata no_repeat separated hziso
  obtain ⟨x, hxX, hzsingle, hxa, hxb⟩ := hziso
  have hxC : Sum.inl x ∈ TwoColorComponent G phi alpha beta z := by
    rw [hzsingle]
    simp
  rcases hwdata with hwiso | hwnon
  · obtain ⟨y, hyX, hwsingle, hya, hyb⟩ := hwiso
    have hyC : Sum.inl y ∈ TwoColorComponent G phi alpha beta w := by
      rw [hwsingle]
      simp
    exact no_repeat hxX hyX (separated hxC hyC) hxa hya
  · obtain ⟨r, s, p, hp, hps, hrs, hrm, hsm, hclass⟩ := hwnon
    have hrC : Sum.inl r ∈ TwoColorComponent G phi alpha beta w := by
      rw [← hps]
      simp
    have hsC : Sum.inl s ∈ TwoColorComponent G phi alpha beta w := by
      rw [← hps]
      change Sum.inl s ∈ p.support
      simpa only [p.getVert_length] using
        p.getVert_mem_support p.length
    obtain ⟨v, hvX, hvm, hvC⟩ : ∃ v : V, v ∈ X ∧
        (alpha ∈ MissingColors G phi v ∨
          beta ∈ MissingColors G phi v) ∧
        Sum.inl v ∈ TwoColorComponent G phi alpha beta w := by
      rcases hclass with hinside | ⟨f, hfB, hfC, hend⟩
      · exact ⟨r, hinside.1, hrm, hrC⟩
      · rcases hend with hrX | hsX
        · exact ⟨r, hrX, hrm, hrC⟩
        · exact ⟨s, hsX, hsm, hsC⟩
    rcases hvm with hva | hvb
    · exact no_repeat hxX hvX (separated hxC hvC) hxa hva
    · exact no_repeat hxX hvX (separated hxC hvC) hxb hvb

private theorem helper_branch_593.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k),
        (BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta).card ≤ (1 : ℕ) →
    ∀ (z w : V ⊕ E), Disjoint (TwoColorComponent G phi alpha beta z) (TwoColorComponent G phi
        alpha beta w) → ((
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), TwoColorComponent G phi alpha beta w = {Sum.inl x}
        ∧ alpha ∈ MissingColors G phi x ∧ beta ∈ MissingColors G phi x) ∨
    ∃ (r : V) (s : V) (p : (TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi
        alpha beta w ∧ r ≠ s ∧ (alpha ∈ MissingColors G phi r ∨ beta ∈ MissingColors G phi r) ∧
        (alpha ∈ MissingColors G phi s ∨ beta ∈ MissingColors G phi s) ∧ (r ∈
        (TreeSequenceVertexSet T : Finset V) ∧ s ∈ (TreeSequenceVertexSet T : Finset V) ∨
    ∃ f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T : Finset V) beta, Sum.inr f ∈
        TwoColorComponent G phi alpha beta w ∧ (r ∈ (TreeSequenceVertexSet T : Finset V) ∨ s ∈
        (TreeSequenceVertexSet T : Finset V)))) → (
    ∀ {u v : V}, u ∈ (TreeSequenceVertexSet T : Finset V) → v ∈ (TreeSequenceVertexSet T : Finset
        V) → u ≠ v →
    ∀ {d : Fin k}, d ∈ MissingColors G phi u → d ∈ MissingColors G phi v → False) → (
    ∀ {u v : V}, Sum.inl u ∈ TwoColorComponent G phi alpha beta z → Sum.inl v ∈ TwoColorComponent
        G phi alpha beta w → u ≠ v) → (
    ∀ {u v t : V}, u ∈ (TreeSequenceVertexSet T : Finset V) → v ∈ (TreeSequenceVertexSet T :
        Finset V) → t ∈ (TreeSequenceVertexSet T : Finset V) → u ≠ v → u ≠ t → v ≠ t → alpha ∈
        MissingColors G phi u ∨ beta ∈ MissingColors G phi u → alpha ∈ MissingColors G phi v ∨
        beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi t ∨ beta ∈ MissingColors G phi
        t → False) → (
    ∃ (r : V) (s : V) (p : (TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi
        alpha beta z ∧ r ≠ s ∧ (alpha ∈ MissingColors G phi r ∨ beta ∈ MissingColors G phi r) ∧
        (alpha ∈ MissingColors G phi s ∨ beta ∈ MissingColors G phi s) ∧ (r ∈
        (TreeSequenceVertexSet T : Finset V) ∧ s ∈ (TreeSequenceVertexSet T : Finset V) ∨
    ∃ f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T : Finset V) beta, Sum.inr f ∈
        TwoColorComponent G phi alpha beta z ∧ (r ∈ (TreeSequenceVertexSet T : Finset V) ∨ s ∈
        (TreeSequenceVertexSet T : Finset V)))) → False := by
  classical
  intro V E _ _ G k e0 phi T alpha beta hbeta
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta
  set X : Finset V := TreeSequenceVertexSet T
  intro z w hdisj hwdata no_repeat separated three_impossible hznon
  rcases hwdata with hwiso | hwnon
  · obtain ⟨y, hyX, hwsingle, hya, hyb⟩ := hwiso
    have hyC : Sum.inl y ∈ TwoColorComponent G phi alpha beta w := by
      rw [hwsingle]
      simp
    obtain ⟨r, s, p, hp, hps, hrs, hrm, hsm, hclass⟩ := hznon
    have hrC : Sum.inl r ∈ TwoColorComponent G phi alpha beta z := by
      rw [← hps]
      simp
    have hsC : Sum.inl s ∈ TwoColorComponent G phi alpha beta z := by
      rw [← hps]
      change Sum.inl s ∈ p.support
      simpa only [p.getVert_length] using
        p.getVert_mem_support p.length
    obtain ⟨v, hvX, hvm, hvC⟩ : ∃ v : V, v ∈ X ∧
        (alpha ∈ MissingColors G phi v ∨
          beta ∈ MissingColors G phi v) ∧
        Sum.inl v ∈ TwoColorComponent G phi alpha beta z := by
      rcases hclass with hinside | ⟨f, hfB, hfC, hend⟩
      · exact ⟨r, hinside.1, hrm, hrC⟩
      · rcases hend with hrX | hsX
        · exact ⟨r, hrX, hrm, hrC⟩
        · exact ⟨s, hsX, hsm, hsC⟩
    have hvy : v ≠ y := separated hvC hyC
    rcases hvm with hva | hvb
    · exact no_repeat hvX hyX hvy hva hya
    · exact no_repeat hvX hyX hvy hvb hyb
  · obtain ⟨rz, sz, pz, hpz, hpsz, hrsz, hrzm, hszm, hzclass⟩ := hznon
    obtain ⟨rw, sw, pw, hpw, hpsw, hrsw, hrwm, hswm, hwclass⟩ := hwnon
    have hrzC : Sum.inl rz ∈ TwoColorComponent G phi alpha beta z := by
      rw [← hpsz]
      simp
    have hszC : Sum.inl sz ∈ TwoColorComponent G phi alpha beta z := by
      rw [← hpsz]
      change Sum.inl sz ∈ pz.support
      simpa only [pz.getVert_length] using
        pz.getVert_mem_support pz.length
    have hrwC : Sum.inl rw ∈ TwoColorComponent G phi alpha beta w := by
      rw [← hpsw]
      simp
    have hswC : Sum.inl sw ∈ TwoColorComponent G phi alpha beta w := by
      rw [← hpsw]
      change Sum.inl sw ∈ pw.support
      simpa only [pw.getVert_length] using
        pw.getVert_mem_support pw.length
    rcases hzclass with hzinside | ⟨fz, hfzB, hfzC, hzend⟩
    · obtain ⟨t, htX, htm, htC⟩ : ∃ t : V, t ∈ X ∧
          (alpha ∈ MissingColors G phi t ∨
            beta ∈ MissingColors G phi t) ∧
          Sum.inl t ∈ TwoColorComponent G phi alpha beta w := by
        rcases hwclass with hwinside | ⟨fw, hfwB, hfwC, hwend⟩
        · exact ⟨rw, hwinside.1, hrwm, hrwC⟩
        · rcases hwend with hrwX | hswX
          · exact ⟨rw, hrwX, hrwm, hrwC⟩
          · exact ⟨sw, hswX, hswm, hswC⟩
      exact three_impossible hzinside.1 hzinside.2 htX hrsz
        (separated hrzC htC) (separated hszC htC) hrzm hszm htm
    · rcases hwclass with hwinside | ⟨fw, hfwB, hfwC, hwend⟩
      · obtain ⟨t, htX, htm, htC⟩ : ∃ t : V, t ∈ X ∧
            (alpha ∈ MissingColors G phi t ∨
              beta ∈ MissingColors G phi t) ∧
            Sum.inl t ∈ TwoColorComponent G phi alpha beta z := by
          rcases hzend with hrzX | hszX
          · exact ⟨rz, hrzX, hrzm, hrzC⟩
          · exact ⟨sz, hszX, hszm, hszC⟩
        exact three_impossible hwinside.1 hwinside.2 htX hrsw
          (Ne.symm (separated htC hrwC))
          (Ne.symm (separated htC hswC)) hrwm hswm htm
      · have hfne : fz ≠ fw := by
          intro h
          subst fw
          exact (Set.disjoint_left.mp hdisj) hfzC hfwC
        have hsubset : ({fz, fw} : Finset E) ⊆
            BoundaryColorEdges G phi X beta := by
          intro f hf
          simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl
          · exact hfzB
          · exact hfwB
        have htwo : 2 ≤ (BoundaryColorEdges G phi X beta).card := by
          have hle := Finset.card_le_card hsubset
          have hpair : ({fz, fw} : Finset E).card = 2 := by
            simp [hfne]
          omega
        have hbetaX : (BoundaryColorEdges G phi X beta).card ≤ 1 := by
          simpa [X] using hbeta
        omega

private theorem helper_branch_132.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k),
        IsProperEdgeColoring G phi → ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) →
        (BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta).card ≤ (1 : ℕ) → (
    ∀ {a b : V} (p : (TwoColorIncidenceGraph G phi alpha beta : SimpleGraph (V ⊕ E)).Walk (Sum.inl
        a) (Sum.inl b)), a ∈ (TreeSequenceVertexSet T : Finset V) → b ∉ (TreeSequenceVertexSet T :
        Finset V) →
    ∃ f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T : Finset V) beta, Sum.inr f ∈
        p.support) →
    ∀ (z w : V ⊕ E), TwoColorPathComponent G phi alpha beta z → TwoColorPathComponent G phi alpha
        beta w → (
    ∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G phi alpha beta z) → (
    ∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G phi alpha beta w) → Disjoint
        (TwoColorComponent G phi alpha beta z) (TwoColorComponent G phi alpha beta w) →
        TwoColorComponent G phi alpha beta z = TwoColorComponent G phi alpha beta w := by
  classical
  intro V E _ _ G k e0 phi T alpha beta hproper helementary hbeta
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha beta
  set X : Finset V := TreeSequenceVertexSet T
  intro boundary_of_walk z w hz hw hzX hwX hdisj
  exfalso
  have hne : alpha ≠ beta := hz.1
  have endpoint_missing := @helper_endpoint_missing_142 V E inferInstance inferInstance G k phi
      alpha beta hne
  have analyze :=
    @helper_analyze_168 V E inferInstance inferInstance G k e0
        phi T alpha beta hproper hbeta boundary_of_walk z endpoint_missing
  obtain hzdata := analyze z hz hzX
  obtain hwdata := analyze w hw hwX
  have helementaryX : ColoredVertexSetElementary G phi X := by
    dsimp [X]
    exact helementary
  have no_repeat {u v : V} (huX : u ∈ X) (hvX : v ∈ X)
      (huv : u ≠ v) {d : Fin k}
      (hu : d ∈ MissingColors G phi u)
      (hv : d ∈ MissingColors G phi v) : False :=
    (Finset.disjoint_left.mp (helementaryX huX hvX huv)) hu hv
  have separated {u v : V}
      (hu : Sum.inl u ∈ TwoColorComponent G phi alpha beta z)
      (hv : Sum.inl v ∈ TwoColorComponent G phi alpha beta w) :
      u ≠ v := by
    intro huv
    subst v
    exact (Set.disjoint_left.mp hdisj) hu hv
  have three_impossible :
    ∀ {u v t : V}, u ∈ X → v ∈ X → t ∈ X → u ≠ v → u ≠ t → v ≠ t → (alpha ∈ MissingColors G phi u
        ∨ beta ∈ MissingColors G phi u) → (alpha ∈ MissingColors G phi v ∨ beta ∈ MissingColors G
        phi v) → (alpha ∈ MissingColors G phi t ∨ beta ∈ MissingColors G phi t) → False := by
    intro u v t huX hvX htX huv hut hvt hu hv ht
    rcases hu with hua | hub <;>
      rcases hv with hva | hvb <;>
      rcases ht with hta | htb
    · exact no_repeat huX hvX huv hua hva
    · exact no_repeat huX hvX huv hua hva
    · exact no_repeat huX htX hut hua hta
    · exact no_repeat hvX htX hvt hvb htb
    · exact no_repeat hvX htX hvt hva hta
    · exact no_repeat huX htX hut hub htb
    · exact no_repeat huX hvX huv hub hvb
    · exact no_repeat huX hvX huv hub hvb
  rcases hzdata with hziso | hznon
  · exact @helper_branch_562 V E inferInstance inferInstance G k e0 phi T alpha beta z w hwdata
      no_repeat separated hziso
  · exact @helper_branch_593 V E inferInstance inferInstance G k e0 phi T alpha
      beta hbeta z w hdisj hwdata no_repeat separated three_impossible hznon
lemma ElementarySingleBoundaryInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (alpha beta : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (halpha : BoundaryColorEdges G phi
      (TreeSequenceVertexSet T) alpha = {})
    (hbeta : (BoundaryColorEdges G phi
      (TreeSequenceVertexSet T) beta).card ≤ 1) :
    TreeInterchangeable G T phi alpha beta := by
  classical
  let H := TwoColorIncidenceGraph G phi alpha beta
  let X := TreeSequenceVertexSet T
  have boundary_of_walk :=
    @helper_boundary_of_walk_52 V E inferInstance inferInstance G k e0 phi T alpha beta halpha
  unfold TreeInterchangeable
  intro z w hz hw hzX hwX
  rcases TwoColorComponentsDisjoint G phi alpha beta z w with heq | hdisj
  · exact heq
  · exact @helper_branch_132 V E inferInstance inferInstance G k e0
      phi T alpha beta hproper helementary hbeta boundary_of_walk z w hz hw hzX hwX hdisj
end GoldbergSeymour

end
