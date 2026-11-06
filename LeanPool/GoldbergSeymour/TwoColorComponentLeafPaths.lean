/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors

public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath

/-!
# Paths Starting at Incidence Leaves

Shared facts from Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A leaf of a nontrivial component starts a spanning path
whose other endpoint is missing a color. -/
theorem TwoColorComponent.pathFromLeaf.{u_1, u_2} :
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

end GoldbergSeymour

end
