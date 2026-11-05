/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeMissingColors

public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint

public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent

/-!
# Elementary Closed Noninterchangeable Disjoint Exit Paths

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_77.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {k : ℕ} (phi :
        PartialEdgeColoring E k) (a b : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
    ∀ (c low u v : V ⊕ E) (p : (TwoColorIncidenceGraph G phi a b).Walk u v), p.IsPath →
        {x : V ⊕ E | x ∈ p.support} = TwoColorComponent G phi a b c → low ∈ p.support → low = v →
    ∃ (v : V ⊕ E) (p : H.Walk low v), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G
        phi a b c := by
  classical
  intro V E G k phi a b H c low u v p hp hps hlowP hlv
  subst v
  refine ⟨u, p.reverse, hp.reverse, ?_⟩
  ext y
  change y ∈ p.reverse.support ↔
    y ∈ TwoColorComponent G phi a b c
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  exact Set.ext_iff.mp hps y

private theorem helper_branch_85.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a b : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (c : V ⊕ E), (
    ∃ x ∈ X, Sum.inl x ∈ TwoColorComponent G phi a b c) →
    ∀ (low v : V ⊕ E) (p : H.Walk low v), {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi a
        b c → p.Nil → (
    ∃ x ∈ X, TwoColorComponent G phi a b c = {Sum.inl x} ∧ a ∈ MissingColors G phi x ∧ b ∈
        MissingColors G phi x) ∨
    ∃ (r : V) (s : V) (p : H.Walk (Sum.inl r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support}
        = TwoColorComponent G phi a b c ∧ r ≠ s ∧ (a ∈ MissingColors G phi r ∨ b ∈ MissingColors G
        phi r) ∧ (a ∈ MissingColors G phi s ∨ b ∈ MissingColors G phi s) := by
  classical
  intro V E _ _ G k e0 T phi a b H X c hcX low v p hps hnil
  let _ := Fintype.ofFinite V
  obtain ⟨x, hxX, hxC⟩ := hcX
  have hxP : Sum.inl x ∈ p.support := by
    change Sum.inl x ∈ {y | y ∈ p.support}
    rw [hps]
    exact hxC
  have hxlow : Sum.inl x = low := by
    rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] at hxP
    simpa using hxP
  have hCsingle : TwoColorComponent G phi a b c = {Sum.inl x} := by
    rw [← hps]
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff,
      SimpleGraph.Walk.nil_iff_support_eq.mp hnil]
    simp [hxlow]
  have hmissing : ∀ d : Fin k,
      (d = a ∨ d = b) → d ∈ MissingColors G phi x := by
    intro d hd
    have hnotpresent : d ∉ PresentColors G phi x := by
      intro hpresent
      obtain ⟨e, heinc, hecolor⟩ := by
        simpa [PresentColors] using hpresent
      have hepair : phi e = some a ∨ phi e = some b :=
        hd.elim
          (fun h => Or.inl (hecolor.trans (congrArg some h)))
          (fun h => Or.inr (hecolor.trans (congrArg some h)))
      have hadj : H.Adj (Sum.inl x) (Sum.inr e) := by
        simpa [H, TwoColorIncidenceGraph] using
          (show Incident G x e ∧
              (phi e = some a ∨ phi e = some b) from
            ⟨heinc, hepair⟩)
      have hedgeC : Sum.inr e ∈ TwoColorComponent G phi a b c := by
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
  exact ⟨x, hxX, hCsingle, hmissing a (Or.inl rfl),
    hmissing b (Or.inr rfl)⟩

private theorem helper_branch_132.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {k : ℕ} (phi :
        PartialEdgeColoring E k) (a b : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
    ∀ (v : V ⊕ E) (e : E), ((TwoColorIncidenceGraph G phi a b).neighborSet (Sum.inr
        e)).Subsingleton →
    ∀ (p : H.Walk (Sum.inr e) v), ¬p.Nil →
    ∃ (r : V), Sum.inr e = Sum.inl r := by
  classical
  intro V E G k phi a b H v e hlow p hnil
  have hadj := p.adj_snd hnil
  have hecolor : phi e = some a ∨ phi e = some b := by
    cases hsnd : p.snd with
    | inl q =>
        rw [hsnd] at hadj
        have hdata : Incident G q e ∧
            (phi e = some a ∨ phi e = some b) := by
          simpa [H, TwoColorIncidenceGraph] using hadj
        exact hdata.2
    | inr f =>
        rw [hsnd] at hadj
        have : False := by
          simp [H, TwoColorIncidenceGraph] at hadj
        exact this.elim
  induction hends : G.ends e using Sym2.inductionOn with
  | _ q t =>
      have hqt : q ≠ t := by
        intro hqt
        subst t
        exact G.loopless e q hends
      have hqAdj : H.Adj (Sum.inr e) (Sum.inl q) := by
        simpa [H, TwoColorIncidenceGraph, Incident, hends] using
          (show Incident G q e ∧
              (phi e = some a ∨ phi e = some b) from
            ⟨by simp [Incident, hends], hecolor⟩)
      have htAdj : H.Adj (Sum.inr e) (Sum.inl t) := by
        simpa [H, TwoColorIncidenceGraph, Incident, hends] using
          (show Incident G t e ∧
              (phi e = some a ∨ phi e = some b) from
            ⟨by simp [Incident, hends], hecolor⟩)
      exact False.elim (hqt (Sum.inl.inj (hlow hqAdj htAdj)))

private theorem helper_hend_neighbor_166.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) {k : ℕ}
        (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi →
    ∀ (a b : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
    ∀ (c v : V ⊕ E) (r : V), ((TwoColorIncidenceGraph G phi a b).neighborSet (Sum.inl
        r)).Subsingleton →
    ∀ (p : H.Walk (Sum.inl r) v), p.IsPath → {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi
        a b c → ¬p.Nil →
    ∀ (y : V ⊕ E), H.Adj v y → y = p.getVert (p.length - (1 : ℕ)) := by
  classical
  intro V E _ _ G k phi hproper a b H c v r hlow p hp hps hnil y hvy
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  have hyC : y ∈ TwoColorComponent G phi a b c := by
    have hvC : v ∈ TwoColorComponent G phi a b c := by
      rw [← hps]
      change v ∈ p.support
      simpa only [p.getVert_length] using
        p.getVert_mem_support p.length
    change H.connectedComponentMk y = H.connectedComponentMk c
    change H.connectedComponentMk v = H.connectedComponentMk c at hvC
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hvy).symm.trans hvC
  have hySupport : y ∈ p.support := by
    change y ∈ {q | q ∈ p.support}
    rw [hps]
    exact hyC
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hySupport
  have hnlt : n < p.length := by
    have hnne : n ≠ p.length := by
      intro heq
      have hyv : y = v := by rw [← hn, heq, p.getVert_length]
      exact hvy.ne hyv.symm
    omega
  by_cases hpen : n + 1 = p.length
  · rw [← hn]
    congr 1
    omega
  by_cases hn0 : n = 0
  · have hnext : H.Adj (Sum.inl r) (p.getVert 1) := by
      simpa [hn0, p.getVert_zero] using p.adj_getVert_succ hnlt
    have hvstart : H.Adj (Sum.inl r) v := by
      rw [← hn, hn0, p.getVert_zero] at hvy
      exact hvy.symm
    have hneNext : p.getVert 1 ≠ v := by
      intro heq
      have hindices := hp.getVert_injOn
        (show 1 ≤ p.length by omega) (show p.length ≤ p.length by rfl)
        (heq.trans p.getVert_length.symm)
      omega
    exact False.elim (hneNext (hlow hnext hvstart))
  · have hleft : H.Adj y (p.getVert (n - 1)) := by
      rw [← hn]
      have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        hadj.symm
    have hright : H.Adj y (p.getVert (n + 1)) := by
      rw [← hn]
      exact p.adj_getVert_succ hnlt
    have hvneLeft : v ≠ p.getVert (n - 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show p.length ≤ p.length by rfl)
        (show n - 1 ≤ p.length by omega)
        (p.getVert_length.trans heq)
      omega
    have hvneRight : v ≠ p.getVert (n + 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show p.length ≤ p.length by rfl)
        (show n + 1 ≤ p.length by omega)
        (p.getVert_length.trans heq)
      omega
    have hlrne : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show n - 1 ≤ p.length by omega)
        (show n + 1 ≤ p.length by omega) heq
      omega
    let : Fintype (H.neighborSet y) := Fintype.ofFinite _
    have hthree : 3 ≤ @SimpleGraph.degree _ H y
        (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let ss : Finset (Sum V E) :=
        {v, p.getVert (n - 1), p.getVert (n + 1)}
      have hss : ss ⊆ H.neighborFinset y := by
        intro t ht
        simp only [ss, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hvy.symm
        · simpa [SimpleGraph.mem_neighborFinset] using hleft
        · simpa [SimpleGraph.mem_neighborFinset] using hright
      have hc3 : 3 ≤ ss.card := by
        simp [ss, hvneLeft, hvneRight, hlrne]
      exact hc3.trans (Finset.card_le_card hss)
    have htwo : @SimpleGraph.degree _ H y
        (Fintype.ofFinite _) ≤ 2 := by
      simpa [H] using
        TwoColorIncidenceDegreeAtMostTwo G phi a b hproper y
    omega

private theorem helper_hendVertex_263.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {k : ℕ} (phi :
        PartialEdgeColoring E k) (a b : Fin k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
    ∀ (v : V ⊕ E) (r : V) (p : H.Walk (Sum.inl r) v), (H.neighborSet v).Subsingleton → (0 : ℕ) <
        p.length →
    ∃ (s : V), v = Sum.inl s := by
  classical
  intro V E G k phi a b H v r p hendLeaf hp_pos
  cases hv : v with
  | inl s => exact ⟨s, rfl⟩
  | inr e =>
      have hlastAdj : H.Adj (p.getVert (p.length - 1)) v := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length),
          p.getVert_length] using
          p.adj_getVert_succ (i := p.length - 1) (by omega)
      have hecolor : phi e = some a ∨ phi e = some b := by
        cases hprev : p.getVert (p.length - 1) with
        | inl q =>
            rw [hprev, hv] at hlastAdj
            have hdata : Incident G q e ∧
                (phi e = some a ∨ phi e = some b) := by
              simpa [H, TwoColorIncidenceGraph] using hlastAdj
            exact hdata.2
        | inr f =>
            rw [hprev, hv] at hlastAdj
            have : False := by
              simp [H, TwoColorIncidenceGraph] at hlastAdj
            exact this.elim
      induction hends : G.ends e using Sym2.inductionOn with
      | _ q t =>
          have hqt : q ≠ t := by
            intro hqt
            subst t
            exact G.loopless e q hends
          have hqAdj : H.Adj v (Sum.inl q) := by
            rw [hv]
            simpa [H, TwoColorIncidenceGraph, Incident, hends] using
              (show Incident G q e ∧
                  (phi e = some a ∨ phi e = some b) from
                ⟨by simp [Incident, hends], hecolor⟩)
          have htAdj : H.Adj v (Sum.inl t) := by
            rw [hv]
            simpa [H, TwoColorIncidenceGraph, Incident, hends] using
              (show Incident G t e ∧
                  (phi e = some a ∨ phi e = some b) from
                ⟨by simp [Incident, hends], hecolor⟩)
          exact False.elim
            (hqt (Sum.inl.inj (hendLeaf hqAdj htAdj)))

private theorem helper_analyze_95.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k), IsProperEdgeColoring G
        phi →
    ∀ (a b : Fin k), (
    ∀ (v : V), ((TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).neighborSet (Sum.inl
        v)).Subsingleton → a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v) →
    ∀ (c : V ⊕ E), TwoColorPathComponent G phi a b c → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ TwoColorComponent G phi a b c) → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), TwoColorComponent G phi a b c = {Sum.inl x} ∧ a ∈
        MissingColors G phi x ∧ b ∈ MissingColors G phi x) ∨
    ∃ (r : V) (s : V) (p : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl
        r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi a b c ∧
        r ≠ s ∧ (a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r) ∧ (a ∈ MissingColors G phi
        s ∨ b ∈ MissingColors G phi s) := by
  classical
  intro V E _ _ G k e0 T phi hproper a b
  let _ := Fintype.ofFinite V
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b
  set X : Finset V := TreeSequenceVertexSet T
  intro endpoint_missing c hc hcX
  obtain ⟨low, hlowC, hlow⟩ := hc.2
  obtain ⟨u, v, p, hp, hps⟩ :=
    TwoColorComponentSpanningPath G phi a b hproper c
  have hlowP : low ∈ p.support := by
    change low ∈ {y | y ∈ p.support}
    rw [hps]
    exact hlowC
  have hlowEnd : low = u ∨ low = v := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hlow) hlowP
  obtain ⟨v, p, hp, hps⟩ : ∃ (v : Sum V E) (p : H.Walk low v),
      p.IsPath ∧ {y | y ∈ p.support} =
        TwoColorComponent G phi a b c := by
    rcases hlowEnd with hlu | hlv
    · subst u
      exact ⟨v, p, hp, hps⟩
    · exact @helper_branch_77 (@V) (@E) (@G) (@k) (@phi) (@a) (@b) (@c) (@low) (@u) (@v) (@p)
        (@hp) (@hps) (@hlowP) (@hlv)
  by_cases hnil : p.Nil
  · exact @helper_branch_85 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T) (@phi)
      (@a) (@b) (@c) (@hcX) (@low) (@v) (@p) (@hps) (@hnil)
  · have hstartVertex : ∃ r : V, low = Sum.inl r := by
      cases low with
      | inl r => exact ⟨r, rfl⟩
      | inr e =>
          exact @helper_branch_132 (@V) (@E) (@G) (@k) (@phi) (@a) (@b) (@v) (@e) (@hlow) (@p)
              (@hnil)
    obtain ⟨r, hr⟩ := hstartVertex
    subst low
    have hend_neighbor :=
      @helper_hend_neighbor_166 (@V) (@E) inferInstance inferInstance (@G) (@k) (@phi) (@hproper)
          (@a) (@b) (@c) (@v) (@r) (@hlow) (@p) (@hp) (@hps) (@hnil)
    have hendLeaf : Set.Subsingleton (H.neighborSet v) := by
      intro y hy y' hy'
      exact (hend_neighbor y hy).trans (hend_neighbor y' hy').symm
    have hp_pos : 0 < p.length :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil
    have hendVertex :=
      @helper_hendVertex_263 (@V) (@E) (@G) (@k) (@phi) (@a) (@b) (@v) (@r) (@p) (@hendLeaf)
          (@hp_pos)
    obtain ⟨s, hs⟩ := hendVertex
    subst v
    have hrs : r ≠ s := by
      intro hrs
      apply hnil
      exact hp.nil_iff_eq.mpr (by simp [hrs])
    right
    exact ⟨r, s, p, hp, hps, hrs, endpoint_missing r hlow,
      endpoint_missing s hendLeaf⟩

private theorem helper_chooseFirst_365.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E)
        {k : ℕ} (phi : PartialEdgeColoring E k) (a b : Fin k),
    ∀ {u v : V ⊕ E} (p : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk u v) (S :
        Finset (V ⊕ E)), {x ∈ S | x ∈ p.support}.Nonempty →
    ∃ x ∈ S,
    ∃ (hx : x ∈ p.support),
    ∀ t ∈ S, t ∈ (p.takeUntil x hx).support → t = x := by
  classical
  intro V E _ _ G k phi a b
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b
  intro u v p S hnonempty
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
        · have hlt : (p.takeUntil x hxP).length + (S.erase x).card < n := by
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

private theorem helper_firstEntry_403.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) {k : ℕ} {e0 : E} (T : TreeSequence G e0) (phi :
        PartialEdgeColoring E k) (a b : Fin k) (_ : TreeColorSetClosed G phi T { a }) (_ : (
    ∀ {u v : V ⊕ E} (p : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk u v) (S :
        Finset (V ⊕ E)) (_ : {x ∈ S | x ∈ p.support}.Nonempty),
    ∃ x ∈ S,
    ∃ (hx : x ∈ p.support),
    ∀ t ∈ S, t ∈ (p.takeUntil x hx).support → t = x)) (r s : V) (Q : (TwoColorIncidenceGraph G phi
        a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r) (Sum.inl s)) (_ : Q.IsPath) (_ : a ∈
        MissingColors G phi r ∨ b ∈ MissingColors G phi r) (_ : r ∉ (TreeSequenceVertexSet T :
        Finset V)) (_ : (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ Q.support)),
    ∃ (c : V) (_ : c ∈ (TreeSequenceVertexSet T : Finset V)) (hcQ : Sum.inl c ∈ Q.support),
    let L : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r) (Sum.inl c)
        := Q.takeUntil (Sum.inl c) hcQ; TreeExitPath T phi a b r c L ∧
    ∃ (g : E), L.getVert (L.length - (1 : ℕ)) = Sum.inr g ∧ Incident G c g ∧ g ∈ BoundaryEdges G
        (TreeSequenceVertexSet T : Finset V) ∧ phi g = some b := by
  classical
  intro V E _ _ _ _ G k e0 T phi a b hclosed
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b
  set X : Finset V := TreeSequenceVertexSet T
  intro chooseFirst r s Q hQ hmissing hrX hmeet
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
    simp [TwoColorIncidenceGraph] at hadj
  have hExit : TreeExitPath T phi a b r c L := by
    unfold TreeExitPath
    exact ⟨hLpath, hLlen, hrX, hcX, hmissing, hLc⟩
  have hlastAdj := L.adj_getVert_succ (i := L.length - 1) (by omega)
  have hlastSucc : L.length - 1 + 1 = L.length := by omega
  rw [hlastSucc, L.getVert_length] at hlastAdj
  cases hlast : L.getVert (L.length - 1) with
  | inl v =>
      rw [hlast] at hlastAdj
      simp [TwoColorIncidenceGraph] at hlastAdj
  | inr g =>
      rw [hlast] at hlastAdj
      have hgc : Incident G c g ∧
          (phi g = some a ∨ phi g = some b) := by
        simpa [H, TwoColorIncidenceGraph] using hlastAdj
      have hprevAdj := L.adj_getVert_succ (i := L.length - 2) (by omega)
      have hprevSucc : L.length - 2 + 1 = L.length - 1 := by omega
      rw [hprevSucc, hlast] at hprevAdj
      cases hprev : L.getVert (L.length - 2) with
      | inr f =>
          rw [hprev] at hprevAdj
          simp [TwoColorIncidenceGraph] at hprevAdj
      | inl x =>
          rw [hprev] at hprevAdj
          have hxg : Incident G x g := by
            have hdata : Incident G x g ∧
                (phi g = some a ∨ phi g = some b) := by
              simpa [H, TwoColorIncidenceGraph] using hprevAdj
            exact hdata.1
          have hxout : x ∉ X := by
            intro hxX
            have hxc := (hLc x hxX).mp (by
              rw [← hprev]
              exact L.getVert_mem_support (L.length - 2))
            have heq : L.getVert (L.length - 2) =
                L.getVert L.length := by
              rw [hprev, L.getVert_length, hxc]
            have := hLpath.getVert_injOn (Nat.sub_le _ _) (by simp) heq
            omega
          have hcx : c ≠ x := by
            intro hcx
            exact hxout (hcx ▸ hcX)
          have hends : G.ends g = s(c, x) :=
            (Sym2.mem_and_mem_iff hcx).mp ⟨hgc.1, hxg⟩
          have hboundary : g ∈ BoundaryEdges G X := by
            simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨c, hcX, x, hxout, hends⟩
          have hga : phi g ≠ some a := by
            intro hga
            have hgColor : g ∈ BoundaryColorEdges G phi X a := by
              simp [BoundaryColorEdges, hboundary, hga]
            have hclosedA : BoundaryColorEdges G phi X a = ∅ := by
              dsimp [X]
              exact hclosed a (by simp)
            rw [hclosedA] at hgColor
            simp at hgColor
          refine ⟨c, hcX, hqQ, hExit, g, hlast, hgc.1,
            hboundary, ?_⟩
          exact hgc.2.resolve_left hga

private theorem helper_differentExits_540.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) {k : ℕ} {e0 : E} (T : TreeSequence G e0) (phi :
        PartialEdgeColoring E k) (a b : Fin k) (z w : V ⊕ E) (_ : Disjoint (TwoColorComponent G
        phi a b z) (TwoColorComponent G phi a b w)) (_ : (
    ∀ (r s : V) (Q : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r)
        (Sum.inl s)) (_ : Q.IsPath) (_ : a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r) (_
        : r ∉ (TreeSequenceVertexSet T : Finset V)) (_ : (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ Q.support)),
    ∃ (c : V) (_ : c ∈ (TreeSequenceVertexSet T : Finset V)) (hcQ : Sum.inl c ∈ Q.support),
    let L : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r) (Sum.inl c)
        := Q.takeUntil (Sum.inl c) hcQ; TreeExitPath T phi a b r c L ∧
    ∃ (g : E), L.getVert (L.length - (1 : ℕ)) = Sum.inr g ∧ Incident G c g ∧ g ∈ BoundaryEdges G
        (TreeSequenceVertexSet T : Finset V) ∧ phi g = some b)) (r1 s1 r2 s2 : V) (p1 :
        (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r1) (Sum.inl s1))
        (p2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r2) (Sum.inl
        s2)) (_ : p1.IsPath) (_ : p2.IsPath) (_ : {q : V ⊕ E | q ∈ p1.support} = TwoColorComponent
        G phi a b z) (_ : {q : V ⊕ E | q ∈ p2.support} = TwoColorComponent G phi a b w) (_ : a ∈
        MissingColors G phi r1 ∨ b ∈ MissingColors G phi r1) (_ : a ∈ MissingColors G phi r2 ∨ b ∈
        MissingColors G phi r2) (_ : r1 ∉ (TreeSequenceVertexSet T : Finset V)) (_ : r2 ∉
        (TreeSequenceVertexSet T : Finset V)) (_ : (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ p1.support)) (_ : (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ p2.support)),
    ∃ (c1 : V) (c2 : V) (L1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r1) (Sum.inl c1)) (L2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕
        E)).Walk (Sum.inl r2) (Sum.inl c2)), TreeExitPath T phi a b r1 c1 L1 ∧ TreeExitPath T phi
        a b r2 c2 L2 ∧ (
    ∀ q ∈ L1.support, q ∉ L2.support) ∧ r1 ≠ r2 ∧ c1 ≠ c2 := by
  classical
  intro V E _ _ _ _ G k e0 T phi a b
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b
  set X : Finset V := TreeSequenceVertexSet T
  intro z w hdisj firstEntry r1 s1 r2 s2 p1 p2 hp1 hp2 hps1 hps2 hm1 hm2 hr1X hr2X hmeet1 hmeet2
  obtain ⟨c1, hc1X, hc1P, hExit1, g1, hg1last, hg1c,
    hg1B, hg1col⟩ := firstEntry r1 s1 p1 hp1 hm1 hr1X hmeet1
  obtain ⟨c2, hc2X, hc2P, hExit2, g2, hg2last, hg2c,
    hg2B, hg2col⟩ := firstEntry r2 s2 p2 hp2 hm2 hr2X hmeet2
  let L1 := p1.takeUntil (Sum.inl c1) hc1P
  let L2 := p2.takeUntil (Sum.inl c2) hc2P
  have hL1sub : L1.support ⊆ p1.support :=
    p1.support_takeUntil_subset_support hc1P
  have hL2sub : L2.support ⊆ p2.support :=
    p2.support_takeUntil_subset_support hc2P
  have hdis : ∀ q, q ∈ L1.support → q ∉ L2.support := by
    intro q hq1 hq2
    apply (Set.disjoint_left.mp hdisj)
    · rw [← hps1]
      exact hL1sub hq1
    · rw [← hps2]
      exact hL2sub hq2
  have hrne : r1 ≠ r2 := by
    intro hr
    apply hdis (Sum.inl r1)
    · exact L1.start_mem_support
    · simp [hr]
  have hcne : c1 ≠ c2 := by
    intro hc
    apply hdis (Sum.inl c1)
    · exact L1.end_mem_support
    · simp [hc]
  exact ⟨c1, c2, L1, L2, hExit1, hExit2, hdis, hrne, hcne⟩

private theorem helper_sameExits_588.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) {k : ℕ} {e0 : E} (T : TreeSequence G e0) (phi :
        PartialEdgeColoring E k) (_ : IsProperEdgeColoring G phi) (a b : Fin k) (_ : (
    ∀ (r s : V) (Q : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r)
        (Sum.inl s)) (_ : Q.IsPath) (_ : a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r) (_
        : r ∉ (TreeSequenceVertexSet T : Finset V)) (_ : (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ Q.support)),
    ∃ (c : V) (_ : c ∈ (TreeSequenceVertexSet T : Finset V)) (hcQ : Sum.inl c ∈ Q.support),
    let L : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r) (Sum.inl c)
        := Q.takeUntil (Sum.inl c) hcQ; TreeExitPath T phi a b r c L ∧
    ∃ (g : E), L.getVert (L.length - (1 : ℕ)) = Sum.inr g ∧ Incident G c g ∧ g ∈ BoundaryEdges G
        (TreeSequenceVertexSet T : Finset V) ∧ phi g = some b)) (r s : V) (p :
        (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r) (Sum.inl s)) (_
        : p.IsPath) (_ : r ≠ s) (_ : a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r) (_ : a
        ∈ MissingColors G phi s ∨ b ∈ MissingColors G phi s) (_ : r ∉ (TreeSequenceVertexSet T :
        Finset V)) (_ : s ∉ (TreeSequenceVertexSet T : Finset V)) (_ : (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ p.support)),
    ∃ (c1 : V) (c2 : V) (L1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl c1)) (L2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕
        E)).Walk (Sum.inl s) (Sum.inl c2)), TreeExitPath T phi a b r c1 L1 ∧ TreeExitPath T phi a
        b s c2 L2 ∧ (
    ∀ q ∈ L1.support, q ∉ L2.support) ∧ r ≠ s ∧ c1 ≠ c2 := by
  classical
  intro V E _ _ _ _ G k e0 T phi hproper a b
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b
  set X : Finset V := TreeSequenceVertexSet T
  intro firstEntry r s p hp hrs hrm hsm hrX hsX hmeet
  have hmeetRev : ∃ x ∈ X, Sum.inl x ∈ p.reverse.support := by
    obtain ⟨x, hxX, hxP⟩ := hmeet
    refine ⟨x, hxX, ?_⟩
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hxP
  obtain ⟨c1, hc1X, hc1P, hExit1, g1, hg1last, hg1c,
    hg1B, hg1col⟩ := firstEntry r s p hp hrm hrX hmeet
  obtain ⟨c2, hc2X, hc2P, hExit2, g2, hg2last, hg2c,
    hg2B, hg2col⟩ :=
    firstEntry s r p.reverse hp.reverse hsm hsX hmeetRev
  let L1 := p.takeUntil (Sum.inl c1) hc1P
  let L2 := p.reverse.takeUntil (Sum.inl c2) hc2P
  have hL1le : L1.length ≤ p.length :=
    p.length_takeUntil_le_length hc1P
  have hL2le : L2.length ≤ p.length := by
    have hle := p.reverse.length_takeUntil_le_length hc2P
    simpa using hle
  have hc1idx : p.getVert L1.length = Sum.inl c1 :=
    p.getVert_length_takeUntil hc1P
  have hc2idxRev : p.reverse.getVert L2.length = Sum.inl c2 :=
    p.reverse.getVert_length_takeUntil hc2P
  have hc2idx : p.getVert (p.length - L2.length) = Sum.inl c2 :=
    (SimpleGraph.Walk.getVert_reverse p L2.length).symm.trans hc2idxRev
  have hg1idx : p.getVert (L1.length - 1) = Sum.inr g1 := by
    have hpred : L1.length - 1 ≤
        (p.takeUntil (Sum.inl c1) hc1P).length := by
      dsimp [L1]
      omega
    rw [← p.getVert_takeUntil hc1P hpred]
    exact hg1last
  have hg2idxRev : p.reverse.getVert (L2.length - 1) = Sum.inr g2 := by
    have hpred : L2.length - 1 ≤
        (p.reverse.takeUntil (Sum.inl c2) hc2P).length := by
      dsimp [L2]
      omega
    rw [← p.reverse.getVert_takeUntil hc2P hpred]
    exact hg2last
  have hg2idx : p.getVert (p.length - (L2.length - 1)) = Sum.inr g2 :=
    (SimpleGraph.Walk.getVert_reverse p (L2.length - 1)).symm.trans
      hg2idxRev
  have hcne : c1 ≠ c2 := by
    intro hc
    subst c2
    have hci : L1.length = p.length - L2.length := by
      apply hp.getVert_injOn hL1le (Nat.sub_le _ _)
      exact hc1idx.trans hc2idx.symm
    have hgne : g1 ≠ g2 := by
      intro hg
      subst g2
      have hgi : L1.length - 1 = p.length - (L2.length - 1) := by
        apply hp.getVert_injOn ((Nat.sub_le _ _).trans hL1le)
          (Nat.sub_le _ _)
        exact hg1idx.trans hg2idx.symm
      have hL1two : 2 ≤ L1.length := hExit1.2.1
      have hL2two : 2 ≤ L2.length := hExit2.2.1
      omega
    exact (hproper hgne ⟨c1, hg1c, hg2c⟩ hg1col) hg2col
  have hdis : ∀ q, q ∈ L1.support → q ∉ L2.support := by
    intro q hq1 hq2
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hq1
    obtain ⟨j, hj, hjLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hq2
    have hiP : p.getVert i = q := by
      rw [← p.getVert_takeUntil hc1P hiLe]
      exact hi
    have hjRev : p.reverse.getVert j = q := by
      rw [← p.reverse.getVert_takeUntil hc2P hjLe]
      exact hj
    have hjP : p.getVert (p.length - j) = q :=
      (SimpleGraph.Walk.getVert_reverse p j).symm.trans hjRev
    have hij : i = p.length - j := by
      apply hp.getVert_injOn (hiLe.trans hL1le) (Nat.sub_le _ _)
      exact hiP.trans hjP.symm
    have hc2Before : p.length - L2.length ≤ L1.length := by omega
    have hc2L1 : Sum.inl c2 ∈ L1.support := by
      have hvertex : L1.getVert (p.length - L2.length) = Sum.inl c2 := by
        exact (p.getVert_takeUntil hc1P hc2Before).trans hc2idx
      rw [← hvertex]
      exact L1.getVert_mem_support (p.length - L2.length)
    exact hcne ((hExit1.2.2.2.2.2 c2 hc2X).mp hc2L1).symm
  exact ⟨c1, c2, L1, L2, hExit1, hExit2, hdis, hrs, hcne⟩

private theorem helper_branch_711.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a b : Fin k),
    ∀ (z w : V ⊕ E), (
    ∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G phi a b w) → (
    ∀ {u v : V}, u ∈ (TreeSequenceVertexSet T : Finset V) → v ∈ (TreeSequenceVertexSet T : Finset
        V) → u ≠ v →
    ∀ {d : Fin k}, d ∈ MissingColors G phi u → d ∈ MissingColors G phi v → False) → (
    ∀ (r s : V) (p : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r)
        (Sum.inl s)), p.IsPath → r ≠ s → a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r → a
        ∈ MissingColors G phi s ∨ b ∈ MissingColors G phi s → r ∉ (TreeSequenceVertexSet T :
        Finset V) → s ∉ (TreeSequenceVertexSet T : Finset V) → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ p.support) →
    ∃ (c1 : V) (c2 : V) (L1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl c1)) (L2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕
        E)).Walk (Sum.inl s) (Sum.inl c2)), TreeExitPath T phi a b r c1 L1 ∧ TreeExitPath T phi a
        b s c2 L2 ∧ (
    ∀ q ∈ L1.support, q ∉ L2.support) ∧ r ≠ s ∧ c1 ≠ c2) → (
    ∀ {u v : V}, Sum.inl u ∈ TwoColorComponent G phi a b z → Sum.inl v ∈ TwoColorComponent G phi a
        b w → u ≠ v) → (
    ∀ (r s : V), (
    ∃ (c1 : V) (c2 : V) (L1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl c1)) (L2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕
        E)).Walk (Sum.inl s) (Sum.inl c2)), TreeExitPath T phi a b r c1 L1 ∧ TreeExitPath T phi a
        b s c2 L2 ∧ (
    ∀ q ∈ L1.support, q ∉ L2.support) ∧ r ≠ s ∧ c1 ≠ c2) →
    ∃ (a1 : V) (b1 : V) (a2 : V) (b2 : V) (P1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V
        ⊕ E)).Walk (Sum.inl a1) (Sum.inl b1)) (P2 : (TwoColorIncidenceGraph G phi a b :
        SimpleGraph (V ⊕ E)).Walk (Sum.inl a2) (Sum.inl b2)), TreeExitPath T phi a b a1 b1 P1 ∧
        TreeExitPath T phi a b a2 b2 P2 ∧ (
    ∀ q ∈ P1.support, q ∉ P2.support) ∧ a1 ≠ a2 ∧ b1 ≠ b2) → ((
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), TwoColorComponent G phi a b w = {Sum.inl x} ∧ a ∈
        MissingColors G phi x ∧ b ∈ MissingColors G phi x) ∨
    ∃ (r : V) (s : V) (p : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl
        r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi a b w ∧
        r ≠ s ∧ (a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r) ∧ (a ∈ MissingColors G phi
        s ∨ b ∈ MissingColors G phi s)) → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), TwoColorComponent G phi a b z = {Sum.inl x} ∧ a ∈
        MissingColors G phi x ∧ b ∈ MissingColors G phi x) →
    ∃ (a1 : V) (b1 : V) (a2 : V) (b2 : V) (P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl
        a1) (Sum.inl b1)) (P2 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl
        b2)), TreeExitPath T phi a b a1 b1 P1 ∧ TreeExitPath T phi a b a2 b2 P2 ∧ (
    ∀ x ∈ P1.support, x ∉ P2.support) ∧ a1 ≠ a2 ∧ b1 ≠ b2 := by
  classical
  intro V E _ _ G k e0 T phi a b
  let _ := Fintype.ofFinite V
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b
  set X : Finset V := TreeSequenceVertexSet T
  intro z w hwX no_repeat sameExits separated finish hwdata hziso
  obtain ⟨x, hxX, hzsingle, hxa, hxb⟩ := hziso
  have hxC : Sum.inl x ∈ TwoColorComponent G phi a b z := by
    rw [hzsingle]
    simp
  rcases hwdata with hwiso | hwnon
  · obtain ⟨y, hyX, hwsingle, hya, hyb⟩ := hwiso
    have hyC : Sum.inl y ∈ TwoColorComponent G phi a b w := by
      rw [hwsingle]
      simp
    exact (no_repeat hxX hyX (separated hxC hyC) hxa hya).elim
  · obtain ⟨r, s, p, hp, hps, hrs, hrm, hsm⟩ := hwnon
    have hrC : Sum.inl r ∈ TwoColorComponent G phi a b w := by
      rw [← hps]
      simp
    have hsC : Sum.inl s ∈ TwoColorComponent G phi a b w := by
      rw [← hps]
      change Sum.inl s ∈ p.support
      simpa only [p.getVert_length] using p.getVert_mem_support p.length
    have hrOut : r ∉ X := by
      intro hrX
      rcases hrm with hra | hrb
      · exact no_repeat hxX hrX (separated hxC hrC) hxa hra
      · exact no_repeat hxX hrX (separated hxC hrC) hxb hrb
    have hsOut : s ∉ X := by
      intro hsX
      rcases hsm with hsa | hsb
      · exact no_repeat hxX hsX (separated hxC hsC) hxa hsa
      · exact no_repeat hxX hsX (separated hxC hsC) hxb hsb
    have hmeet : ∃ q ∈ X, Sum.inl q ∈ p.support := by
      obtain ⟨q, hqX, hqC⟩ := hwX
      refine ⟨q, by simpa [X] using hqX, ?_⟩
      change Sum.inl q ∈ {t | t ∈ p.support}
      rw [hps]
      exact hqC
    exact finish r s (sameExits r s p hp hrs hrm hsm hrOut hsOut hmeet)

private theorem helper_branch_746.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a b : Fin k),
    ∀ (z w : V ⊕ E), (
    ∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G phi a b z) → (
    ∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G phi a b w) → (
    ∀ {u v : V}, u ∈ (TreeSequenceVertexSet T : Finset V) → v ∈ (TreeSequenceVertexSet T : Finset
        V) → u ≠ v →
    ∀ {d : Fin k}, d ∈ MissingColors G phi u → d ∈ MissingColors G phi v → False) → (
    ∀ {u v t : V}, u ∈ (TreeSequenceVertexSet T : Finset V) → v ∈ (TreeSequenceVertexSet T :
        Finset V) → t ∈ (TreeSequenceVertexSet T : Finset V) → u ≠ v → u ≠ t → v ≠ t → a ∈
        MissingColors G phi u ∨ b ∈ MissingColors G phi u → a ∈ MissingColors G phi v ∨ b ∈
        MissingColors G phi v → a ∈ MissingColors G phi t ∨ b ∈ MissingColors G phi t → False) → (
    ∀ (r1 s1 r2 s2 : V) (p1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r1) (Sum.inl s1)) (p2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕
        E)).Walk (Sum.inl r2) (Sum.inl s2)), p1.IsPath → p2.IsPath → {q : V ⊕ E | q ∈ p1.support}
        = TwoColorComponent G phi a b z → {q : V ⊕ E | q ∈ p2.support} = TwoColorComponent G phi a
        b w → a ∈ MissingColors G phi r1 ∨ b ∈ MissingColors G phi r1 → a ∈ MissingColors G phi r2
        ∨ b ∈ MissingColors G phi r2 → r1 ∉ (TreeSequenceVertexSet T : Finset V) → r2 ∉
        (TreeSequenceVertexSet T : Finset V) → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ p1.support) → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ p2.support) →
    ∃ (c1 : V) (c2 : V) (L1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r1) (Sum.inl c1)) (L2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕
        E)).Walk (Sum.inl r2) (Sum.inl c2)), TreeExitPath T phi a b r1 c1 L1 ∧ TreeExitPath T phi
        a b r2 c2 L2 ∧ (
    ∀ q ∈ L1.support, q ∉ L2.support) ∧ r1 ≠ r2 ∧ c1 ≠ c2) → (
    ∀ (r s : V) (p : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl r)
        (Sum.inl s)), p.IsPath → r ≠ s → a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r → a
        ∈ MissingColors G phi s ∨ b ∈ MissingColors G phi s → r ∉ (TreeSequenceVertexSet T :
        Finset V) → s ∉ (TreeSequenceVertexSet T : Finset V) → (
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), Sum.inl x ∈ p.support) →
    ∃ (c1 : V) (c2 : V) (L1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl c1)) (L2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕
        E)).Walk (Sum.inl s) (Sum.inl c2)), TreeExitPath T phi a b r c1 L1 ∧ TreeExitPath T phi a
        b s c2 L2 ∧ (
    ∀ q ∈ L1.support, q ∉ L2.support) ∧ r ≠ s ∧ c1 ≠ c2) → (
    ∀ {u v : V}, Sum.inl u ∈ TwoColorComponent G phi a b z → Sum.inl v ∈ TwoColorComponent G phi a
        b w → u ≠ v) → (
    ∀ (r s : V), (
    ∃ (c1 : V) (c2 : V) (L1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk
        (Sum.inl r) (Sum.inl c1)) (L2 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕
        E)).Walk (Sum.inl s) (Sum.inl c2)), TreeExitPath T phi a b r c1 L1 ∧ TreeExitPath T phi a
        b s c2 L2 ∧ (
    ∀ q ∈ L1.support, q ∉ L2.support) ∧ r ≠ s ∧ c1 ≠ c2) →
    ∃ (a1 : V) (b1 : V) (a2 : V) (b2 : V) (P1 : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V
        ⊕ E)).Walk (Sum.inl a1) (Sum.inl b1)) (P2 : (TwoColorIncidenceGraph G phi a b :
        SimpleGraph (V ⊕ E)).Walk (Sum.inl a2) (Sum.inl b2)), TreeExitPath T phi a b a1 b1 P1 ∧
        TreeExitPath T phi a b a2 b2 P2 ∧ (
    ∀ q ∈ P1.support, q ∉ P2.support) ∧ a1 ≠ a2 ∧ b1 ≠ b2) → ((
    ∃ x ∈ (TreeSequenceVertexSet T : Finset V), TwoColorComponent G phi a b w = {Sum.inl x} ∧ a ∈
        MissingColors G phi x ∧ b ∈ MissingColors G phi x) ∨
    ∃ (r : V) (s : V) (p : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl
        r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi a b w ∧
        r ≠ s ∧ (a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r) ∧ (a ∈ MissingColors G phi
        s ∨ b ∈ MissingColors G phi s)) → (
    ∃ (r : V) (s : V) (p : (TwoColorIncidenceGraph G phi a b : SimpleGraph (V ⊕ E)).Walk (Sum.inl
        r) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G phi a b z ∧
        r ≠ s ∧ (a ∈ MissingColors G phi r ∨ b ∈ MissingColors G phi r) ∧ (a ∈ MissingColors G phi
        s ∨ b ∈ MissingColors G phi s)) →
    ∃ (a1 : V) (b1 : V) (a2 : V) (b2 : V) (P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl
        a1) (Sum.inl b1)) (P2 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl
        b2)), TreeExitPath T phi a b a1 b1 P1 ∧ TreeExitPath T phi a b a2 b2 P2 ∧ (
    ∀ x ∈ P1.support, x ∉ P2.support) ∧ a1 ≠ a2 ∧ b1 ≠ b2 := by
  classical
  intro V E _ _ G k e0 T phi a b
  let _ := Fintype.ofFinite V
  set H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b
  set X : Finset V := TreeSequenceVertexSet T
  intro z w hzX hwX no_repeat three_impossible differentExits sameExits separated finish hwdata
      hznon
  rcases hwdata with hwiso | hwnon
  · obtain ⟨y, hyX, hwsingle, hya, hyb⟩ := hwiso
    have hyC : Sum.inl y ∈ TwoColorComponent G phi a b w := by
      rw [hwsingle]
      simp
    obtain ⟨r, s, p, hp, hps, hrs, hrm, hsm⟩ := hznon
    have hrC : Sum.inl r ∈ TwoColorComponent G phi a b z := by
      rw [← hps]
      simp
    have hsC : Sum.inl s ∈ TwoColorComponent G phi a b z := by
      rw [← hps]
      change Sum.inl s ∈ p.support
      simpa only [p.getVert_length] using p.getVert_mem_support p.length
    have hrOut : r ∉ X := by
      intro hrX
      rcases hrm with hra | hrb
      · exact no_repeat hrX hyX (separated hrC hyC) hra hya
      · exact no_repeat hrX hyX (separated hrC hyC) hrb hyb
    have hsOut : s ∉ X := by
      intro hsX
      rcases hsm with hsa | hsb
      · exact no_repeat hsX hyX (separated hsC hyC) hsa hya
      · exact no_repeat hsX hyX (separated hsC hyC) hsb hyb
    have hmeet : ∃ q ∈ X, Sum.inl q ∈ p.support := by
      obtain ⟨q, hqX, hqC⟩ := hzX
      refine ⟨q, by simpa [X] using hqX, ?_⟩
      change Sum.inl q ∈ {t | t ∈ p.support}
      rw [hps]
      exact hqC
    exact finish r s (sameExits r s p hp hrs hrm hsm hrOut hsOut hmeet)
  · obtain ⟨rz, sz, pz, hpz, hpsz, hrsz, hrzm, hszm⟩ := hznon
    obtain ⟨rw, sw, pw, hpw, hpsw, hrsw, hrwm, hswm⟩ := hwnon
    have hrzC : Sum.inl rz ∈ TwoColorComponent G phi a b z := by
      rw [← hpsz]
      simp
    have hszC : Sum.inl sz ∈ TwoColorComponent G phi a b z := by
      rw [← hpsz]
      change Sum.inl sz ∈ pz.support
      simpa only [pz.getVert_length] using pz.getVert_mem_support pz.length
    have hrwC : Sum.inl rw ∈ TwoColorComponent G phi a b w := by
      rw [← hpsw]
      simp
    have hswC : Sum.inl sw ∈ TwoColorComponent G phi a b w := by
      rw [← hpsw]
      change Sum.inl sw ∈ pw.support
      simpa only [pw.getVert_length] using pw.getVert_mem_support pw.length
    have hmeetz : ∃ q ∈ X, Sum.inl q ∈ pz.support := by
      obtain ⟨q, hqX, hqC⟩ := hzX
      refine ⟨q, by simpa [X] using hqX, ?_⟩
      change Sum.inl q ∈ {t | t ∈ pz.support}
      rw [hpsz]
      exact hqC
    have hmeetw : ∃ q ∈ X, Sum.inl q ∈ pw.support := by
      obtain ⟨q, hqX, hqC⟩ := hwX
      refine ⟨q, by simpa [X] using hqX, ?_⟩
      change Sum.inl q ∈ {t | t ∈ pw.support}
      rw [hpsw]
      exact hqC
    have hmeetzRev : ∃ q ∈ X, Sum.inl q ∈ pz.reverse.support := by
      obtain ⟨q, hqX, hqP⟩ := hmeetz
      refine ⟨q, hqX, ?_⟩
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hqP
    have hmeetwRev : ∃ q ∈ X, Sum.inl q ∈ pw.reverse.support := by
      obtain ⟨q, hqX, hqP⟩ := hmeetw
      refine ⟨q, hqX, ?_⟩
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hqP
    have hpszRev : {q | q ∈ pz.reverse.support} =
        TwoColorComponent G phi a b z := by
      ext q
      change q ∈ pz.reverse.support ↔
        q ∈ TwoColorComponent G phi a b z
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
      exact Set.ext_iff.mp hpsz q
    have hpswRev : {q | q ∈ pw.reverse.support} =
        TwoColorComponent G phi a b w := by
      ext q
      change q ∈ pw.reverse.support ↔
        q ∈ TwoColorComponent G phi a b w
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
      exact Set.ext_iff.mp hpsw q
    by_cases hrzX : rz ∈ X
    · by_cases hszX : sz ∈ X
      · have hrwOut : rw ∉ X := by
          intro hrwX
          exact three_impossible hrzX hszX hrwX hrsz
            (separated hrzC hrwC) (separated hszC hrwC)
            hrzm hszm hrwm
        have hswOut : sw ∉ X := by
          intro hswX
          exact three_impossible hrzX hszX hswX hrsz
            (separated hrzC hswC) (separated hszC hswC)
            hrzm hszm hswm
        exact finish rw sw
          (sameExits rw sw pw hpw hrsw hrwm hswm hrwOut hswOut hmeetw)
      · by_cases hrwX : rw ∈ X
        · by_cases hswX : sw ∈ X
          · exact (three_impossible hrzX hrwX hswX
              (separated hrzC hrwC) (separated hrzC hswC) hrsw
              hrzm hrwm hswm).elim
          · exact finish sz sw
              (differentExits sz rz sw rw pz.reverse pw.reverse
                hpz.reverse hpw.reverse hpszRev hpswRev hszm hswm
                hszX hswX hmeetzRev hmeetwRev)
        · exact finish sz rw
            (differentExits sz rz rw sw pz.reverse pw
              hpz.reverse hpw hpszRev hpsw hszm hrwm hszX hrwX
              hmeetzRev hmeetw)
    · by_cases hrwX : rw ∈ X
      · by_cases hswX : sw ∈ X
        · have hszOut : sz ∉ X := by
            intro hszX
            exact three_impossible hrwX hswX hszX hrsw
              (Ne.symm (separated hszC hrwC))
              (Ne.symm (separated hszC hswC)) hrwm hswm hszm
          exact finish rz sz
            (sameExits rz sz pz hpz hrsz hrzm hszm hrzX hszOut hmeetz)
        · exact finish rz sw
            (differentExits rz sz sw rw pz pw.reverse hpz
              hpw.reverse hpsz hpswRev hrzm hswm hrzX hswX hmeetz
              hmeetwRev)
      · exact finish rz rw
          (differentExits rz sz rw sw pz pw hpz hpw hpsz hpsw
            hrzm hrwm hrzX hrwX hmeetz hmeetw)

lemma ElementaryClosedNoninterchangeableDisjointExitPaths {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (a b : Fin k) (hne : a ≠ b)
    (hclosed : TreeColorSetClosed G phi T {a})
    (hnot : ¬ TreeInterchangeable G T phi a b) :
    ∃ (a1 b1 a2 b2 : V) (P1 :
      (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a1) (Sum.inl b1)) (P2 :
      (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl b2)),
    TreeExitPath T phi a b a1 b1 P1 ∧
      TreeExitPath T phi a b a2 b2 P2 ∧
        (∀ x, x ∈ P1.support → x ∉ P2.support) ∧ a1 ≠ a2 ∧ b1 ≠ b2 := by
  classical
  let H := TwoColorIncidenceGraph G phi a b
  let X := TreeSequenceVertexSet T
  unfold TreeInterchangeable at hnot
  push Not at hnot
  obtain ⟨z, w, hz, hw, hzX, hwX, hzw⟩ := hnot
  have hdisj : Disjoint (TwoColorComponent G phi a b z)
      (TwoColorComponent G phi a b w) :=
    (TwoColorComponentsDisjoint G phi a b z w).resolve_left hzw
  have endpoint_missing (v : V)
      (hleaf : Set.Subsingleton (H.neighborSet (Sum.inl v))) :
      a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v := by
    by_cases ha : a ∈ MissingColors G phi v
    · exact Or.inl ha
    · right
      have hap : a ∈ PresentColors G phi v := by
        simpa [MissingColors] using ha
      by_contra hb
      have hbp : b ∈ PresentColors G phi v := by
        simpa [MissingColors] using hb
      obtain ⟨ea, hea, hca⟩ := by simpa [PresentColors] using hap
      obtain ⟨eb, heb, hcb⟩ := by simpa [PresentColors] using hbp
      have hada : H.Adj (Sum.inl v) (Sum.inr ea) := by
        simpa [H, TwoColorIncidenceGraph] using
          (show Incident G v ea ∧
              (phi ea = some a ∨ phi ea = some b) from
            ⟨hea, Or.inl hca⟩)
      have hadb : H.Adj (Sum.inl v) (Sum.inr eb) := by
        simpa [H, TwoColorIncidenceGraph] using
          (show Incident G v eb ∧
              (phi eb = some a ∨ phi eb = some b) from
            ⟨heb, Or.inr hcb⟩)
      have heab : ea = eb := Sum.inr.inj (hleaf hada hadb)
      subst eb
      exact hne (Option.some.inj (hca.symm.trans hcb))
  have analyze :=
    @helper_analyze_95 V E inferInstance inferInstance G k e0 T
        phi hproper a b endpoint_missing
  have chooseFirst :=
    @helper_chooseFirst_365 V E inferInstance inferInstance G k phi a b
  have firstEntry :=
    @helper_firstEntry_403 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 T phi a b hclosed chooseFirst
  have helementaryX : ColoredVertexSetElementary G phi X := by
    dsimp [X]
    exact helementary
  have no_repeat {u v : V} (huX : u ∈ X) (hvX : v ∈ X)
      (huv : u ≠ v) {d : Fin k}
      (hu : d ∈ MissingColors G phi u)
      (hv : d ∈ MissingColors G phi v) : False :=
    (Finset.disjoint_left.mp (helementaryX huX hvX huv)) hu hv
  have three_impossible :
    ∀ {u v t : V}, u ∈ X → v ∈ X → t ∈ X → u ≠ v → u ≠ t → v ≠ t → (a ∈ MissingColors G phi u ∨ b
        ∈ MissingColors G phi u) → (a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v) → (a ∈
        MissingColors G phi t ∨ b ∈ MissingColors G phi t) → False := by
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
  have differentExits :=
    @helper_differentExits_540 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 T phi a b z w hdisj firstEntry
  have sameExits :=
    @helper_sameExits_588 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 T phi hproper a b firstEntry
  have separated {u v : V}
      (hu : Sum.inl u ∈ TwoColorComponent G phi a b z)
      (hv : Sum.inl v ∈ TwoColorComponent G phi a b w) : u ≠ v := by
    intro huv
    subst v
    exact (Set.disjoint_left.mp hdisj) hu hv
  have finish :
    ∀ (r s : V), (
    ∃ (c1 c2 : V) (L1 : H.Walk (Sum.inl r) (Sum.inl c1)) (L2 : H.Walk (Sum.inl s) (Sum.inl c2)),
        TreeExitPath T phi a b r c1 L1 ∧ TreeExitPath T phi a b s c2 L2 ∧ (
    ∀ q, q ∈ L1.support → q ∉ L2.support) ∧ r ≠ s ∧ c1 ≠ c2) →
    ∃ (a1 b1 a2 b2 : V) (P1 : H.Walk (Sum.inl a1) (Sum.inl b1)) (P2 : H.Walk (Sum.inl a2) (Sum.inl
        b2)), TreeExitPath T phi a b a1 b1 P1 ∧ TreeExitPath T phi a b a2 b2 P2 ∧ (
    ∀ q, q ∈ P1.support → q ∉ P2.support) ∧ a1 ≠ a2 ∧ b1 ≠ b2 := by
    intro r s h
    obtain ⟨c1, c2, L1, L2, hExit1, hExit2, hdis, hrs, hc⟩ := h
    exact ⟨r, c1, s, c2, L1, L2, hExit1, hExit2, hdis, hrs, hc⟩
  obtain hzdata := analyze z hz (by simpa [X] using hzX)
  obtain hwdata := analyze w hw (by simpa [X] using hwX)
  rcases hzdata with hziso | hznon
  · exact @helper_branch_711 V E inferInstance inferInstance G k e0 T phi a b z w hwX no_repeat
      sameExits separated finish hwdata hziso
  · exact @helper_branch_746 V E inferInstance inferInstance G k e0 T phi a b z w
      hzX hwX no_repeat three_impossible differentExits sameExits separated finish hwdata hznon
end GoldbergSeymour

end
