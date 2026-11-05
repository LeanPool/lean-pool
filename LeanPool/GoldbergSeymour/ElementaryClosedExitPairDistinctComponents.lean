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

public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent

/-!
# Elementary Closed Exit Pair Distinct Components

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ElementaryClosedExitPairDistinctComponents_missing_leaf_104.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi →
    ∀ (a b : Fin k),
    let H := TwoColorIncidenceGraph G phi a b;
    ∀ (v : V), a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v → (H.neighborSet (Sum.inl
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

private theorem ElementaryClosedExitPairDistinctComponents_fullPathFromLeaf_172.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k :
    ℕ} (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi → ∀ (a b : Fin k), a ≠ b →
    let H := TwoColorIncidenceGraph G phi a b; (∀ (v : V), (H.neighborSet (Sum.inl
    v)).Subsingleton → a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v) → ∀ (v : V) (c :
    V ⊕ E), Sum.inl v ∈ TwoColorComponent G phi a b c → (H.neighborSet (Sum.inl
    v)).Subsingleton → (∃ (e : E), Sum.inr e ∈ TwoColorComponent G phi a b c) → ∃ (s : V) (p :
    H.Walk (Sum.inl v) (Sum.inl s)), p.IsPath ∧ {y : V ⊕ E | y ∈ p.support} =
    TwoColorComponent G phi a b c ∧ v ≠ s ∧ (a ∈ MissingColors G phi s ∨ b ∈ MissingColors G
    phi s) := by
  classical
  intro V E _ _ G k phi hproper a b hne H endpoint_missing v c hvC hvleaf hnontrivial
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

private theorem ElementaryClosedExitPairDistinctComponents_chooseFirst_361.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E
          k) (a b : Fin k),
      a ≠ b →
        let H := TwoColorIncidenceGraph G phi a b;
        ∀ {u v : V ⊕ E} (p : H.Walk u v) (S : Finset (V ⊕ E)),
          {x ∈ S | x ∈ p.support}.Nonempty →
            ∃ x ∈ S, ∃ (hx : x ∈ p.support), ∀ t ∈ S, t ∈ (p.takeUntil x hx).support → t = x := by
  classical
  intro V E _ _ _ _ G k phi a b hne H u v p S hnonempty
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
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

private theorem ElementaryClosedExitPairDistinctComponents_firstEntry_400.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) {k : ℕ} {e0 : E} (T : TreeSequence G e0) (phi :
        PartialEdgeColoring E k) (a b : Fin k), a ≠ b → TreeColorSetClosed G phi T {a} →
    let H := TwoColorIncidenceGraph G phi a b;
    let X := TreeSequenceVertexSet T; (
    ∀ {u v : V ⊕ E} (p : H.Walk u v) (S : Finset (V ⊕ E)), {x ∈ S | x ∈ p.support}.Nonempty →
    ∃ x ∈ S,
    ∃ (hx : x ∈ p.support),
    ∀ t ∈ S, t ∈ (p.takeUntil x hx).support → t = x) →
    ∀ (r s : V) (Q : H.Walk (Sum.inl r) (Sum.inl s)), Q.IsPath → a ∈ MissingColors G phi r ∨ b ∈
        MissingColors G phi r → r ∉ X → (
    ∃ x ∈ X, Sum.inl x ∈ Q.support) →
    ∃ (c : V) (_ : c ∈ X) (hcQ : Sum.inl c ∈ Q.support),
    let L := Q.takeUntil (Sum.inl c) hcQ; TreeExitPath T phi a b r c L ∧
    ∃ (g : E), L.getVert (L.length - 1) = Sum.inr g ∧ Incident G c g ∧ g ∈ BoundaryEdges G X ∧ phi
        g = some b := by
  classical
  intro V E _ _ _ _ G k e0 T phi a b hne hclosed H X chooseFirst r s Q hQ hmissing hrX hmeet
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
  have hExit : TreeExitPath T phi a b r c L := by
    unfold TreeExitPath
    exact ⟨hLpath, hLlen, hrX, hcX, hmissing, hLc⟩
  have hlastAdj := L.adj_getVert_succ (i := L.length - 1) (by omega)
  have hlastSucc : L.length - 1 + 1 = L.length := by omega
  rw [hlastSucc, L.getVert_length] at hlastAdj
  cases hlast : L.getVert (L.length - 1) with
  | inl v =>
      rw [hlast] at hlastAdj
      simp [H, TwoColorIncidenceGraph] at hlastAdj
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
          simp [H, TwoColorIncidenceGraph] at hprevAdj
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

private theorem ElementaryClosedExitPairDistinctComponents_pathPrefix_533.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b →
    let H := TwoColorIncidenceGraph G phi a b; (
    ∀ {u v : V ⊕ E} (p : H.Walk u v) {z : V ⊕ E}, z ∈ p.support → z ∈ TwoColorComponent G phi a b
        u) → (
    ∀ {x y z w : V ⊕ E}, H.Adj x y → H.Adj x z → y ≠ z → H.Adj x w → w = y ∨ w = z) →
    ∀ {u v w : V} (p : H.Walk (Sum.inl u) (Sum.inl v)) (q : H.Walk (Sum.inl u) (Sum.inl w)),
        p.IsPath → q.IsPath → (H.neighborSet (Sum.inl u)).Subsingleton →
        {z : V ⊕ E | z ∈ q.support} = TwoColorComponent G phi a b (Sum.inl u) →
    ∃ (hvq : Sum.inl v ∈ q.support), p = q.takeUntil (Sum.inl v) hvq := by
  classical
  intro V E _ _ _ _ G k phi a b hne H walk_support_component neighbor_of_two u v w p q hp hq
      huleaf hqs
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  have hvC : Sum.inl v ∈
      TwoColorComponent G phi a b (Sum.inl u) :=
    walk_support_component p p.end_mem_support
  have hvq : Sum.inl v ∈ q.support := by
    change Sum.inl v ∈ {z | z ∈ q.support}
    rw [hqs]
    exact hvC
  let L := q.takeUntil (Sum.inl v) hvq
  have hLpath : L.IsPath := hq.takeUntil _
  have hsync : ∀ n, n ≤ p.length → n ≤ L.length →
      p.getVert n = L.getVert n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hnp hnL
        by_cases hn0 : n = 0
        · subst n
          simp [L]
        by_cases hn1 : n = 1
        · subst n
          have hpAdj := p.adj_getVert_succ (i := 0) (by omega)
          have hLAdj := L.adj_getVert_succ (i := 0) (by omega)
          rw [p.getVert_zero] at hpAdj
          rw [L.getVert_zero] at hLAdj
          exact huleaf hpAdj hLAdj
        · have hcur : p.getVert (n - 1) = L.getVert (n - 1) :=
            ih (n - 1) (by omega) (by omega) (by omega)
          have hprev : p.getVert (n - 2) = L.getVert (n - 2) :=
            ih (n - 2) (by omega) (by omega) (by omega)
          have hpAdj : H.Adj (L.getVert (n - 1)) (p.getVert n) := by
            have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
            have hsucc : n - 1 + 1 = n := by omega
            rw [hsucc, hcur] at hadj
            exact hadj
          have hLleft : H.Adj (L.getVert (n - 1))
              (L.getVert (n - 2)) := by
            have hadj := L.adj_getVert_succ (i := n - 2) (by omega)
            have hsucc : n - 2 + 1 = n - 1 := by omega
            rw [hsucc] at hadj
            exact hadj.symm
          have hLright : H.Adj (L.getVert (n - 1))
              (L.getVert n) := by
            have hadj := L.adj_getVert_succ (i := n - 1) (by omega)
            have hsucc : n - 1 + 1 = n := by omega
            rwa [hsucc] at hadj
          have hleftRight : L.getVert (n - 2) ≠ L.getVert n := by
            intro heq
            have hidx := hLpath.getVert_injOn
              (show n - 2 ≤ L.length by omega) hnL heq
            omega
          have hpnextLeft : p.getVert n ≠ L.getVert (n - 2) := by
            intro heq
            have heq' : p.getVert n = p.getVert (n - 2) :=
              heq.trans hprev.symm
            have hidx := hp.getVert_injOn hnp
              (show n - 2 ≤ p.length by omega) heq'
            omega
          exact (neighbor_of_two hLleft hLright hleftRight hpAdj).resolve_left
            hpnextLeft
  have hplen : p.length ≤ L.length := by
    by_contra hnot
    have heq := hsync L.length (by omega) le_rfl
    have hverts : p.getVert L.length = p.getVert p.length := by
      exact heq.trans (L.getVert_length.trans p.getVert_length.symm)
    have hidx := hp.getVert_injOn
      (show L.length ≤ p.length by omega)
      (show p.length ≤ p.length by rfl) hverts
    omega
  have hLlen : L.length ≤ p.length := by
    by_contra hnot
    have heq := hsync p.length le_rfl (by omega)
    have hverts : L.getVert p.length = L.getVert L.length := by
      exact heq.symm.trans (p.getVert_length.trans L.getVert_length.symm)
    have hidx := hLpath.getVert_injOn
      (show p.length ≤ L.length by omega)
      (show L.length ≤ L.length by rfl) hverts
    omega
  have hlen : p.length = L.length := hplen.antisymm hLlen
  have hpL : p = L := by
    apply SimpleGraph.Walk.ext_getVert_le_length hlen
    intro n hn
    exact hsync n hn (hlen ▸ hn)
  exact ⟨hvq, hpL⟩

private theorem ElementaryClosedExitPairDistinctComponents_oppositeExit_626.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) {k : ℕ} {e0 : E} (T : TreeSequence G e0) (phi :
        PartialEdgeColoring E k), IsProperEdgeColoring G phi →
    ∀ (a b : Fin k), a ≠ b → TreeColorSetClosed G phi T {a} →
    let H := TwoColorIncidenceGraph G phi a b;
    let X := TreeSequenceVertexSet T; (
    ∀ (v : V), a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v → (H.neighborSet (Sum.inl
        v)).Subsingleton) → (
    ∀ (r s : V) (Q : H.Walk (Sum.inl r) (Sum.inl s)), Q.IsPath → a ∈ MissingColors G phi r ∨ b ∈
        MissingColors G phi r → r ∉ X → (
    ∃ x ∈ X, Sum.inl x ∈ Q.support) →
    ∃ (c : V) (_ : c ∈ X) (hcQ : Sum.inl c ∈ Q.support),
    let L := Q.takeUntil (Sum.inl c) hcQ; TreeExitPath T phi a b r c L ∧
    ∃ (g : E), L.getVert (L.length - 1) = Sum.inr g ∧ Incident G c g ∧ g ∈ BoundaryEdges G X ∧ phi
        g = some b) → (
    ∀ {u v w : V} (p : H.Walk (Sum.inl u) (Sum.inl v)) (q : H.Walk (Sum.inl u) (Sum.inl w)),
        p.IsPath → q.IsPath → (H.neighborSet (Sum.inl u)).Subsingleton →
        {z : V ⊕ E | z ∈ q.support} = TwoColorComponent G phi a b (Sum.inl u) →
    ∃ (hvq : Sum.inl v ∈ q.support), p = q.takeUntil (Sum.inl v) hvq) →
    ∀ (u v s : V) (P : H.Walk (Sum.inl u) (Sum.inl v)) (R : H.Walk (Sum.inl u) (Sum.inl s)),
        TreeExitPath T phi a b u v P → R.IsPath → {z : V ⊕ E | z ∈ R.support} = TwoColorComponent
        G phi a b (Sum.inl u) → u ≠ s → a ∈ MissingColors G phi s ∨ b ∈ MissingColors G phi s → s
        ∉ X →
    ∃ (c : V) (L : H.Walk (Sum.inl s) (Sum.inl c)) (f : E), TreeExitPath T phi a b s c L ∧ (
    ∀ z ∈ P.support, z ∉ L.support) ∧ s ≠ u ∧ c ≠ v ∧ f ∈ BoundaryColorEdges G phi X b ∧ Incident
        G c f ∧ Sum.inr f ∈ L.support ∧
    ∀ z ∈ L.support, z ∈ TwoColorComponent G phi a b (Sum.inl u) := by
  classical
  intro V E _ _ _ _ G k e0 T phi hproper a b hne hclosed H X missing_leaf firstEntry pathPrefix u
      v s P R hP hRpath hRsupport hus hsMissing hsX
  have huLeaf : Set.Subsingleton (H.neighborSet (Sum.inl u)) :=
    missing_leaf u hP.2.2.2.2.1
  obtain ⟨hvR, hPprefix⟩ :=
    pathPrefix P R hP.1 hRpath huLeaf hRsupport
  obtain ⟨d, hdX, hdP, hExitD, g1, hg1last, hg1d, hg1B, hg1col⟩ :=
    firstEntry u v P hP.1 hP.2.2.2.2.1 hP.2.2.1
      ⟨v, hP.2.2.2.1, P.end_mem_support⟩
  have hdv : d = v := (hP.2.2.2.2.2 d hdX).mp hdP
  subst d
  let D := P.takeUntil (Sum.inl v) hdP
  have hDlen : D.length = P.length := by
    apply (hP.1.getVert_eq_end_iff
      (P.length_takeUntil_le_length hdP)).mp
    exact P.getVert_length_takeUntil hdP
  have hDP : D = P := by
    apply SimpleGraph.Walk.ext_getVert_le_length hDlen
    intro n hn
    exact P.getVert_takeUntil hdP hn
  have hg1lastP : P.getVert (P.length - 1) = Sum.inr g1 := by
    simpa [D, hDP] using hg1last
  have hmeetRev : ∃ x ∈ X, Sum.inl x ∈ R.reverse.support := by
    refine ⟨v, hP.2.2.2.1, ?_⟩
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hvR
  obtain ⟨c, hcX, hcR, hExit, g3, hg3last, hg3c, hg3B, hg3col⟩ :=
    firstEntry s u R.reverse hRpath.reverse hsMissing hsX hmeetRev
  let L := R.reverse.takeUntil (Sum.inl c) hcR
  have hPLe : P.length ≤ R.length := by
    rw [hPprefix]
    exact R.length_takeUntil_le_length hvR
  have hLLe : L.length ≤ R.length := by
    have hle := R.reverse.length_takeUntil_le_length hcR
    simpa [L] using hle
  have hvIdx : R.getVert P.length = Sum.inl v := by
    rw [hPprefix]
    exact R.getVert_length_takeUntil hvR
  have hcIdxRev : R.reverse.getVert L.length = Sum.inl c := by
    exact R.reverse.getVert_length_takeUntil hcR
  have hcIdx : R.getVert (R.length - L.length) = Sum.inl c :=
    (SimpleGraph.Walk.getVert_reverse R L.length).symm.trans hcIdxRev
  have hg1Idx : R.getVert (P.length - 1) = Sum.inr g1 := by
    have hpred : P.length - 1 ≤
        (R.takeUntil (Sum.inl v) hvR).length := by
      rw [← hPprefix]
      omega
    rw [← R.getVert_takeUntil hvR hpred, ← hPprefix]
    exact hg1lastP
  have hg3IdxRev : R.reverse.getVert (L.length - 1) = Sum.inr g3 := by
    have hpred : L.length - 1 ≤
        (R.reverse.takeUntil (Sum.inl c) hcR).length := by
      dsimp [L]
      omega
    rw [← R.reverse.getVert_takeUntil hcR hpred]
    exact hg3last
  have hg3Idx : R.getVert (R.length - (L.length - 1)) = Sum.inr g3 :=
    (SimpleGraph.Walk.getVert_reverse R (L.length - 1)).symm.trans
      hg3IdxRev
  have hcv : c ≠ v := by
    intro hcv
    subst c
    have hvi : P.length = R.length - L.length := by
      apply hRpath.getVert_injOn hPLe (Nat.sub_le _ _)
      exact hvIdx.trans hcIdx.symm
    have hg13 : g1 ≠ g3 := by
      intro hg
      subst g3
      have hgi : P.length - 1 = R.length - (L.length - 1) := by
        apply hRpath.getVert_injOn ((Nat.sub_le _ _).trans hPLe)
          (Nat.sub_le _ _)
        exact hg1Idx.trans hg3Idx.symm
      have hPtwo : 2 ≤ P.length := hP.2.1
      have hLtwo : 2 ≤ L.length := hExit.2.1
      omega
    exact (hproper hg13 ⟨v, hg1d, hg3c⟩ hg1col) hg3col
  have hdis : ∀ z, z ∈ P.support → z ∉ L.support := by
    intro z hzP hzL
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzP
    obtain ⟨j, hj, hjLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzL
    have hprefixLength :
        P.length = (R.takeUntil (Sum.inl v) hvR).length :=
      congrArg SimpleGraph.Walk.length hPprefix
    have hiR : R.getVert i = z := by
      have hiTakeLe : i ≤ (R.takeUntil (Sum.inl v) hvR).length := by
        rw [← hprefixLength]
        exact hiLe
      have hiTake : (R.takeUntil (Sum.inl v) hvR).getVert i = z := by
        rw [← hPprefix]
        exact hi
      exact (R.getVert_takeUntil hvR hiTakeLe).symm.trans hiTake
    have hjRev : R.reverse.getVert j = z := by
      rw [← R.reverse.getVert_takeUntil hcR hjLe]
      exact hj
    have hjR : R.getVert (R.length - j) = z :=
      (SimpleGraph.Walk.getVert_reverse R j).symm.trans hjRev
    have hij : i = R.length - j := by
      apply hRpath.getVert_injOn (hiLe.trans hPLe) (Nat.sub_le _ _)
      exact hiR.trans hjR.symm
    have hcBefore : R.length - L.length ≤ P.length := by omega
    have hcP : Sum.inl c ∈ P.support := by
      have hvertex : P.getVert (R.length - L.length) = Sum.inl c := by
        have hcTake : R.length - L.length ≤
            (R.takeUntil (Sum.inl v) hvR).length := by
          rw [← hprefixLength]
          exact hcBefore
        rw [hPprefix]
        exact (R.getVert_takeUntil hvR hcTake).trans hcIdx
      rw [← hvertex]
      exact P.getVert_mem_support (R.length - L.length)
    exact hcv ((hP.2.2.2.2.2 c hcX).mp hcP)
  have hLcomponent : ∀ z, z ∈ L.support →
      z ∈ TwoColorComponent G phi a b (Sum.inl u) := by
    intro z hz
    have hzRev : z ∈ R.reverse.support :=
      R.reverse.support_takeUntil_subset_support hcR hz
    have hzR : z ∈ R.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzRev
    rw [← hRsupport]
    exact hzR
  obtain ⟨f, hfB, hcf, hfL⟩ :=
    ClosedColorExitPathBoundaryEdge G T phi a b hclosed s c L hExit
  exact ⟨c, L, f, hExit, hdis, hus.symm, hcv, by simpa [X] using hfB,
    hcf, hfL, hLcomponent⟩

private theorem ElementaryClosedExitPairDistinctComponents_endpoint_missing_781.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        (phi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b →
    let H := TwoColorIncidenceGraph G phi a b;
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

private theorem ElementaryClosedExitPairDistinctComponents_neighbor_of_two_851.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) {k : ℕ}
        (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi →
    ∀ (a b : Fin k), a ≠ b →
    let H := TwoColorIncidenceGraph G phi a b;
    ∀ {x y z w : V ⊕ E}, H.Adj x y → H.Adj x z → y ≠ z → H.Adj x w → w = y ∨ w = z := by
  classical
  intro V E _ _ G k phi hproper a b hne H x y z w hxy hxz hyz hxw
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  by_contra hw
  push Not at hw
  let : Fintype (H.neighborSet x) := Fintype.ofFinite _
  have hthree : 3 ≤ @SimpleGraph.degree _ H x (Fintype.ofFinite _) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let ss : Finset (Sum V E) := {w, y, z}
    have hss : ss ⊆ H.neighborFinset x := by
      intro q hq
      simp only [ss, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · simpa [SimpleGraph.mem_neighborFinset] using hxw
      · simpa [SimpleGraph.mem_neighborFinset] using hxy
      · simpa [SimpleGraph.mem_neighborFinset] using hxz
    have hc3 : 3 ≤ ss.card := by
      simp [ss, hw.1, hw.2, hyz]
    exact hc3.trans (Finset.card_le_card hss)
  have htwo : @SimpleGraph.degree _ H x (Fintype.ofFinite _) ≤ 2 := by
    simpa [H] using
      TwoColorIncidenceDegreeAtMostTwo G phi a b hproper x
  omega

lemma ElementaryClosedExitPairDistinctComponents {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (a b : Fin k) (hne : a ≠ b)
    (_ : a ∈ TreeMissingColors phi T)
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
    (_ : a1 ≠ a2) (_ : b1 ≠ b2)
    (hcomponents :
      TwoColorComponent G phi a b (Sum.inl a1) ≠
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
  have endpoint_missing (v : V)
      (hleaf : Set.Subsingleton (H.neighborSet (Sum.inl v))) :
      a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v := by
    exact @ElementaryClosedExitPairDistinctComponents_endpoint_missing_781 V E inferInstance
        inferInstance G k phi a b hne v hleaf
  have missing_leaf (v : V)
      (hmissing : a ∈ MissingColors G phi v ∨
        b ∈ MissingColors G phi v) :
      Set.Subsingleton (H.neighborSet (Sum.inl v)) := by
    exact @ElementaryClosedExitPairDistinctComponents_missing_leaf_104 V E inferInstance
        inferInstance G k phi hproper a b v hmissing
  have walk_support_component : ∀ {u v : Sum V E}
      (p : H.Walk u v) {z : Sum V E},
      z ∈ p.support → z ∈ TwoColorComponent G phi a b u := by
    intro u v p z hz
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
    change H.connectedComponentMk z = H.connectedComponentMk u
    rw [← hi]
    exact (SimpleGraph.ConnectedComponent.sound (p.take i).reachable).symm
  have fullPathFromLeaf :=
    @ElementaryClosedExitPairDistinctComponents_fullPathFromLeaf_172 V E inferInstance
        inferInstance G k phi hproper a b hne endpoint_missing
  have chooseFirst :=
    @ElementaryClosedExitPairDistinctComponents_chooseFirst_361 V E inferInstance inferInstance
        inferInstance inferInstance G k phi a b hne
  have firstEntry :=
    @ElementaryClosedExitPairDistinctComponents_firstEntry_400 V E inferInstance inferInstance
        inferInstance inferInstance G k e0 T phi a b hne hclosed chooseFirst
  have neighbor_of_two {x y z w : Sum V E}
      (hxy : H.Adj x y) (hxz : H.Adj x z) (hyz : y ≠ z)
      (hxw : H.Adj x w) : w = y ∨ w = z := by
    exact @ElementaryClosedExitPairDistinctComponents_neighbor_of_two_851 V E inferInstance
        inferInstance G k phi hproper a b hne x y z w hxy hxz hyz hxw
  have pathPrefix :=
    @ElementaryClosedExitPairDistinctComponents_pathPrefix_533 V E inferInstance inferInstance
        inferInstance inferInstance G k phi a b hne walk_support_component neighbor_of_two
  have oppositeExit :=
    @ElementaryClosedExitPairDistinctComponents_oppositeExit_626 V E inferInstance inferInstance
        inferInstance inferInstance G k e0 T phi hproper a b hne hclosed missing_leaf firstEntry
        pathPrefix
  have componentNontrivial :
    ∀ {u v : V} (P : H.Walk (Sum.inl u) (Sum.inl v)), 2 ≤ P.length →
    ∃ e : E, Sum.inr e ∈ TwoColorComponent G phi a b (Sum.inl u) := by
    intro u v P htwo
    have hpos : 0 < P.length := by omega
    have hadj := P.adj_getVert_succ (i := 0) hpos
    rw [P.getVert_zero] at hadj
    cases hnext : P.getVert 1 with
    | inl q =>
        rw [hnext] at hadj
        simp [H, TwoColorIncidenceGraph] at hadj
    | inr e =>
        refine ⟨e, walk_support_component P ?_⟩
        rw [← hnext]
        exact P.getVert_mem_support 1
  have ha1Leaf : Set.Subsingleton (H.neighborSet (Sum.inl a1)) :=
    missing_leaf a1 hP1.2.2.2.2.1
  have ha2Leaf : Set.Subsingleton (H.neighborSet (Sum.inl a2)) :=
    missing_leaf a2 hP2.2.2.2.2.1
  obtain ⟨s1, R1, hR1path, hR1support, ha1s1, hs1Missing⟩ :=
    fullPathFromLeaf a1 (Sum.inl a1) rfl ha1Leaf
      (componentNontrivial P1 hP1.2.1)
  obtain ⟨s2, R2, hR2path, hR2support, ha2s2, hs2Missing⟩ :=
    fullPathFromLeaf a2 (Sum.inl a2) rfl ha2Leaf
      (componentNontrivial P2 hP2.2.1)
  have hcompDisjoint :
      Disjoint (TwoColorComponent G phi a b (Sum.inl a1))
        (TwoColorComponent G phi a b (Sum.inl a2)) :=
    (TwoColorComponentsDisjoint G phi a b
      (Sum.inl a1) (Sum.inl a2)).resolve_left hcomponents
  have ha1C : Sum.inl a1 ∈
      TwoColorComponent G phi a b (Sum.inl a1) := rfl
  have ha2C : Sum.inl a2 ∈
      TwoColorComponent G phi a b (Sum.inl a2) := rfl
  have hs1C : Sum.inl s1 ∈
      TwoColorComponent G phi a b (Sum.inl a1) := by
    rw [← hR1support]
    exact R1.end_mem_support
  have hs2C : Sum.inl s2 ∈
      TwoColorComponent G phi a b (Sum.inl a2) := by
    rw [← hR2support]
    exact R2.end_mem_support
  have hP1component : ∀ z, z ∈ P1.support →
      z ∈ TwoColorComponent G phi a b (Sum.inl a1) := by
    intro z hz
    exact walk_support_component P1 hz
  have hP2component : ∀ z, z ∈ P2.support →
      z ∈ TwoColorComponent G phi a b (Sum.inl a2) := by
    intro z hz
    exact walk_support_component P2 hz
  have separated {u v : V}
      (hu : Sum.inl u ∈ TwoColorComponent G phi a b (Sum.inl a1))
      (hv : Sum.inl v ∈ TwoColorComponent G phi a b (Sum.inl a2)) :
      u ≠ v := by
    intro huv
    subst v
    exact (Set.disjoint_left.mp hcompDisjoint) hu hv
  have no_b_missing {v : V} (hvX : v ∈ X) :
      b ∉ MissingColors G phi v := by
    intro hvb
    apply hbpresent
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨v, by simpa [X] using hvX, hvb⟩
  have hsOutside : s1 ∉ X ∨ s2 ∉ X := by
    by_contra hnot
    push Not at hnot
    obtain ⟨hs1X, hs2X⟩ := hnot
    have hs1a : a ∈ MissingColors G phi s1 :=
      hs1Missing.resolve_right (no_b_missing hs1X)
    have hs2a : a ∈ MissingColors G phi s2 :=
      hs2Missing.resolve_right (no_b_missing hs2X)
    have hsne : s1 ≠ s2 := separated hs1C hs2C
    have hmissingDisjoint := helementary
      (by simpa [X] using hs1X) (by simpa [X] using hs2X) hsne
    exact (Finset.disjoint_left.mp hmissingDisjoint) hs1a hs2a
  rcases hsOutside with hs1X | hs2X
  · obtain ⟨c, L, f, hExit, hP1L, hs1a1, hcb1, hfB, hcf, hfL,
        hLcomponent⟩ :=
      oppositeExit a1 b1 s1 P1 R1 hP1 hR1path hR1support ha1s1
        hs1Missing hs1X
    have hP2L : ∀ z, z ∈ P2.support → z ∉ L.support := by
      intro z hz2 hzL
      exact (Set.disjoint_left.mp hcompDisjoint)
        (hLcomponent z hzL) (hP2component z hz2)
    have hs1a2 : s1 ≠ a2 := separated hs1C ha2C
    have hcC : Sum.inl c ∈
        TwoColorComponent G phi a b (Sum.inl a1) :=
      hLcomponent (Sum.inl c) L.end_mem_support
    have hb2C : Sum.inl b2 ∈
        TwoColorComponent G phi a b (Sum.inl a2) :=
      hP2component (Sum.inl b2) P2.end_mem_support
    have hcb2 : c ≠ b2 := separated hcC hb2C
    exact ⟨s1, c, L, f, hExit, hP1L, hP2L, hs1a1, hs1a2,
      hcb1, hcb2, by simpa [X] using hfB, hcf, hfL⟩
  · obtain ⟨c, L, f, hExit, hP2L, hs2a2, hcb2, hfB, hcf, hfL,
        hLcomponent⟩ :=
      oppositeExit a2 b2 s2 P2 R2 hP2 hR2path hR2support ha2s2
        hs2Missing hs2X
    have hP1L : ∀ z, z ∈ P1.support → z ∉ L.support := by
      intro z hz1 hzL
      exact (Set.disjoint_left.mp hcompDisjoint)
        (hP1component z hz1) (hLcomponent z hzL)
    have hs2a1 : s2 ≠ a1 := (separated ha1C hs2C).symm
    have hcC : Sum.inl c ∈
        TwoColorComponent G phi a b (Sum.inl a2) :=
      hLcomponent (Sum.inl c) L.end_mem_support
    have hb1C : Sum.inl b1 ∈
        TwoColorComponent G phi a b (Sum.inl a1) :=
      hP1component (Sum.inl b1) P1.end_mem_support
    have hcb1 : c ≠ b1 := (separated hb1C hcC).symm
    exact ⟨s2, c, L, f, hExit, hP1L, hP2L, hs2a1, hs2a2,
      hcb1, hcb2, by simpa [X] using hfB, hcf, hfL⟩

end GoldbergSeymour

end
