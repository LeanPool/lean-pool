/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ClosedColorExitPathBoundaryEdge
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint

/-!
# Elementary Closed Exit Pair Same Component

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_missing_leaf_103.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G :
    LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k), IsProperEdgeColoring G
    phi → ∀ (a b : Fin k), let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b; ∀
    (v : V), a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v → (H.neighborSet (Sum.inl
    v)).Subsingleton := by
  classical
  intro V E _ _ G k phi hproper a b H v hmissing z hz w hw
  let _ := Fintype.ofFinite V
  cases hzv : z with
  | inl u =>
      rw [hzv] at hz
      simp [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hz
  | inr e =>
      cases hwv : w with
      | inl u =>
          rw [hwv] at hw
          simp [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hw
      | inr f =>
          rw [hzv] at hz
          rw [hwv] at hw
          have he : Incident G v e ∧
              (phi e = some a ∨ phi e = some b) := by
            simpa [H, SimpleGraph.mem_neighborSet,
              TwoColorIncidenceGraph] using hz
          have hf : Incident G v f ∧
              (phi f = some a ∨ phi f = some b) := by
            simpa [H, SimpleGraph.mem_neighborSet,
              TwoColorIncidenceGraph] using hw
          apply congrArg Sum.inr
          by_contra hef
          rcases hmissing with ha | hb
          · have hna : a ∉ PresentColors G phi v := by
              simpa [MissingColors] using ha
            have hea : phi e = some b := he.2.resolve_left (by
              intro hea
              apply hna
              simpa [PresentColors] using
                (show ∃ q, Incident G v q ∧ phi q = some a from
                  ⟨e, he.1, hea⟩))
            have hfa : phi f = some b := hf.2.resolve_left (by
              intro hfa
              apply hna
              simpa [PresentColors] using
                (show ∃ q, Incident G v q ∧ phi q = some a from
                  ⟨f, hf.1, hfa⟩))
            exact (hproper hef ⟨v, he.1, hf.1⟩ hea) hfa
          · have hnb : b ∉ PresentColors G phi v := by
              simpa [MissingColors] using hb
            have heb : phi e = some a := he.2.resolve_right (by
              intro heb
              apply hnb
              simpa [PresentColors] using
                (show ∃ q, Incident G v q ∧ phi q = some b from
                  ⟨e, he.1, heb⟩))
            have hfb : phi f = some a := hf.2.resolve_right (by
              intro hfb
              apply hnb
              simpa [PresentColors] using
                (show ∃ q, Incident G v q ∧ phi q = some b from
                  ⟨f, hf.1, hfb⟩))
            exact (hproper hef ⟨v, he.1, hf.1⟩ heb) hfb

private theorem helper_fullPathFromLeaf_170.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G :
    LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k), IsProperEdgeColoring G
    phi → ∀ (a b : Fin k), let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b; (∀
    (v : V), (H.neighborSet (Sum.inl v)).Subsingleton → a ∈ MissingColors G phi v ∨ b ∈
    MissingColors G phi v) → ∀ (v : V) (c : V ⊕ E), Sum.inl v ∈ TwoColorComponent G phi a b c
    → (H.neighborSet (Sum.inl v)).Subsingleton → (∃ (e : E), Sum.inr e ∈ TwoColorComponent G
    phi a b c) → ∃ (s : V) (p : H.Walk (Sum.inl v) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈
    p.support} = TwoColorComponent G phi a b c ∧ v ≠ s ∧ (a ∈ MissingColors G phi s ∨ b ∈
    MissingColors G phi s) := by
  classical
  intro V E _ _ G k phi hproper a b H endpoint_missing v c hvC hvleaf hnontrivial
  let _ := Fintype.ofFinite V
  obtain ⟨u, w, p, hp, hps⟩ :=
    TwoColorComponentSpanningPath G phi a b hproper c
  have hvP : Sum.inl v ∈ p.support := by
    change Sum.inl v ∈ {y | y ∈ p.support}
    rw [hps]
    exact hvC
  have hvEnd : Sum.inl v = u ∨ Sum.inl v = w := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hvleaf) hvP
  obtain ⟨t, q, hq, hqs⟩ : ∃ (t : Sum V E)
      (q : H.Walk (Sum.inl v) t),
      q.IsPath ∧ {y | y ∈ q.support} =
        TwoColorComponent G phi a b c := by
    rcases hvEnd with hvu | hvw
    · subst u
      exact ⟨w, p, hp, hps⟩
    · subst w
      refine ⟨u, p.reverse, hp.reverse, ?_⟩
      ext y
      change y ∈ p.reverse.support ↔
        y ∈ TwoColorComponent G phi a b c
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
      exact Set.ext_iff.mp hps y
  have hqnon : ¬ q.Nil := by
    intro hnil
    obtain ⟨e, heC⟩ := hnontrivial
    have heQ : Sum.inr e ∈ q.support := by
      change Sum.inr e ∈ {y | y ∈ q.support}
      rw [hqs]
      exact heC
    rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] at heQ
    simp at heQ
  have hend_neighbor : ∀ y, H.Adj t y →
      y = q.getVert (q.length - 1) := by
    intro y hty
    have hyC : y ∈ TwoColorComponent G phi a b c := by
      have htC : t ∈ TwoColorComponent G phi a b c := by
        rw [← hqs]
        change t ∈ q.support
        simpa only [q.getVert_length] using
          q.getVert_mem_support q.length
      change H.connectedComponentMk y = H.connectedComponentMk c
      change H.connectedComponentMk t = H.connectedComponentMk c at htC
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hty).symm.trans htC
    have hySupport : y ∈ q.support := by
      change y ∈ {z | z ∈ q.support}
      rw [hqs]
      exact hyC
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hySupport
    have hnlt : n < q.length := by
      have hnne : n ≠ q.length := by
        intro heq
        have hyt : y = t := by rw [← hn, heq, q.getVert_length]
        exact hty.ne hyt.symm
      omega
    by_cases hpen : n + 1 = q.length
    · rw [← hn]
      congr 1
      omega
    by_cases hn0 : n = 0
    · have hnext : H.Adj (Sum.inl v) (q.getVert 1) := by
        simpa [hn0, q.getVert_zero] using q.adj_getVert_succ hnlt
      have htstart : H.Adj (Sum.inl v) t := by
        rw [← hn, hn0, q.getVert_zero] at hty
        exact hty.symm
      have hneNext : q.getVert 1 ≠ t := by
        intro heq
        have hindices := hq.getVert_injOn
          (show 1 ≤ q.length by omega) (show q.length ≤ q.length by rfl)
          (heq.trans q.getVert_length.symm)
        omega
      exact False.elim (hneNext (hvleaf hnext htstart))
    · have hleft : H.Adj y (q.getVert (n - 1)) := by
        rw [← hn]
        have hadj := q.adj_getVert_succ (i := n - 1) (by omega)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
          hadj.symm
      have hright : H.Adj y (q.getVert (n + 1)) := by
        rw [← hn]
        exact q.adj_getVert_succ hnlt
      have htneLeft : t ≠ q.getVert (n - 1) := by
        intro heq
        have hindices := hq.getVert_injOn
          (show q.length ≤ q.length by rfl)
          (show n - 1 ≤ q.length by omega)
          (q.getVert_length.trans heq)
        omega
      have htneRight : t ≠ q.getVert (n + 1) := by
        intro heq
        have hindices := hq.getVert_injOn
          (show q.length ≤ q.length by rfl)
          (show n + 1 ≤ q.length by omega)
          (q.getVert_length.trans heq)
        omega
      have hlrne : q.getVert (n - 1) ≠ q.getVert (n + 1) := by
        intro heq
        have hindices := hq.getVert_injOn
          (show n - 1 ≤ q.length by omega)
          (show n + 1 ≤ q.length by omega) heq
        omega
      let : Fintype (H.neighborSet y) := Fintype.ofFinite _
      have hthree : 3 ≤ @SimpleGraph.degree _ H y
          (Fintype.ofFinite _) := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        let ss : Finset (Sum V E) :=
          {t, q.getVert (n - 1), q.getVert (n + 1)}
        have hss : ss ⊆ H.neighborFinset y := by
          intro r hr
          simp only [ss, Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl | rfl
          · simpa [SimpleGraph.mem_neighborFinset] using hty.symm
          · simpa [SimpleGraph.mem_neighborFinset] using hleft
          · simpa [SimpleGraph.mem_neighborFinset] using hright
        have hc3 : 3 ≤ ss.card := by
          simp [ss, htneLeft, htneRight, hlrne]
        exact hc3.trans (Finset.card_le_card hss)
      have htwo : @SimpleGraph.degree _ H y
          (Fintype.ofFinite _) ≤ 2 := by
        simpa [H] using
          TwoColorIncidenceDegreeAtMostTwo G phi a b hproper y
      omega
  have hendLeaf : Set.Subsingleton (H.neighborSet t) := by
    intro y hy y' hy'
    exact (hend_neighbor y hy).trans (hend_neighbor y' hy').symm
  have hqpos : 0 < q.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hqnon
  have hendVertex : ∃ s : V, t = Sum.inl s := by
    cases ht : t with
    | inl s => exact ⟨s, rfl⟩
    | inr e =>
        have hlastAdj : H.Adj (q.getVert (q.length - 1)) t := by
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ q.length),
            q.getVert_length] using
            q.adj_getVert_succ (i := q.length - 1) (by omega)
        have hecolor : phi e = some a ∨ phi e = some b := by
          cases hprev : q.getVert (q.length - 1) with
          | inl r =>
              rw [hprev, ht] at hlastAdj
              have hdata : Incident G r e ∧
                  (phi e = some a ∨ phi e = some b) := by
                simpa [H, TwoColorIncidenceGraph] using hlastAdj
              exact hdata.2
          | inr f =>
              rw [hprev, ht] at hlastAdj
              have : False := by
                simp [H, TwoColorIncidenceGraph] at hlastAdj
              exact this.elim
        induction hends : G.ends e using Sym2.inductionOn with
        | _ r s =>
            have hrs : r ≠ s := by
              intro hrs
              subst s
              exact G.loopless e r hends
            have hrAdj : H.Adj t (Sum.inl r) := by
              rw [ht]
              simpa [H, TwoColorIncidenceGraph, Incident, hends] using
                (show Incident G r e ∧
                    (phi e = some a ∨ phi e = some b) from
                  ⟨by simp [Incident, hends], hecolor⟩)
            have hsAdj : H.Adj t (Sum.inl s) := by
              rw [ht]
              simpa [H, TwoColorIncidenceGraph, Incident, hends] using
                (show Incident G s e ∧
                    (phi e = some a ∨ phi e = some b) from
                  ⟨by simp [Incident, hends], hecolor⟩)
            exact False.elim
              (hrs (Sum.inl.inj (hendLeaf hrAdj hsAdj)))
  obtain ⟨s, hs⟩ := hendVertex
  subst t
  have hvs : v ≠ s := by
    intro hvs
    apply hqnon
    exact hq.nil_iff_eq.mpr (by simp [hvs])
  exact ⟨s, q, hq, hqs, hvs, endpoint_missing s hendLeaf⟩

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

private theorem helper_endpoint_missing_454.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
      (phi : PartialEdgeColoring E k) (a b : Fin k),
      a ≠ b →
        let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi a b;
        ∀ (v : V), (H.neighborSet (Sum.inl v)).Subsingleton → a ∈ MissingColors G phi v ∨ b ∈
            MissingColors G phi v := by
  classical
  intro V E _ _ G k phi a b hne H v hleaf
  let _ := Fintype.ofFinite V
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
  have endpoint_missing := @helper_endpoint_missing_454 V E inferInstance inferInstance G k phi a b
      hne
  have missing_leaf := @helper_missing_leaf_103 V E inferInstance inferInstance G k phi hproper a b
  have walk_support_component : ∀ {u v : Sum V E}
      (p : H.Walk u v) {z : Sum V E},
      z ∈ p.support → z ∈ TwoColorComponent G phi a b u := by
    intro u v p z hz
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
    change H.connectedComponentMk z = H.connectedComponentMk u
    rw [← hi]
    exact (SimpleGraph.ConnectedComponent.sound (p.take i).reachable).symm
  have fullPathFromLeaf := @helper_fullPathFromLeaf_170 V E inferInstance inferInstance G k phi
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
