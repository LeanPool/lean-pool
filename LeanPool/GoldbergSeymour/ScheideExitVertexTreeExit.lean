/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideExitVertex
public import LeanPool.GoldbergSeymour.TreeExit

/-!
# Scheide Exit Vertex Tree Exit

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_108.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
        {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (v u : V) (gamma delta :
        Fin k), gamma ∈ MissingColors G phi u →
    ∀ (z : V) (p : (TwoColorIncidenceGraph G phi delta gamma).Walk (Sum.inl u) (Sum.inl z)) (i :
        Fin (p.length + (1 : ℕ))), p.getVert (↑i : ℕ) = Sum.inl v → (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑i : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet T) → p.IsPath → z ∉
        TreeSequenceVertexSet T → {x : V ⊕ E | x ∈ p.support} = TwoColorComponent G phi delta
        gamma (Sum.inl u) →
    ∀ (hivmem : Sum.inl v ∈ p.support),
    let a : (TwoColorIncidenceGraph G phi delta gamma).Walk (Sum.inl u) (Sum.inl v) := p.takeUntil
        (Sum.inl v) hivmem;
    let q : (TwoColorIncidenceGraph G phi delta gamma).Walk (Sum.inl v) (Sum.inl z) := p.dropUntil
        (Sum.inl v) hivmem; a.append q = p → a.length + q.length = p.length → a.length = (↑i : ℕ)
        → q.IsPath → q.reverse.IsPath → (0 : ℕ) < q.length → q.length ≠ (1 : ℕ) → (
    ∀ w ∈ TreeSequenceVertexSet T, Sum.inl w ∈ q.reverse.support ↔ w = v) → delta ∈ MissingColors
        G phi z ∨ gamma ∈ MissingColors G phi z := by
  classical
  intro V E _ _ G k e0 T phi v u gamma delta hgamma z p i hiv hafter hppath hz hpsupp hivmem a q
      hsplit hlen halen hqpath hqrev hqpos hqnotone hqonly
  let _ := Fintype.ofFinite V
  by_cases hd : delta ∈ MissingColors G phi z
  · exact Or.inl hd
  · right
    have component_of_endpoint : ∀ e, Incident G z e →
        Sum.inr e ∈ p.support → p.getVert (p.length - 1) = Sum.inr e := by
      intro e hez hem
      have hem' := hem
      obtain ⟨j, hj, hjle⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hem'
      have hje : p.getVert j = Sum.inr e := hj
      have hjlt : j < p.length := by
        by_contra hnot
        have : j = p.length := by omega
        subst j
        simp [p.getVert_length] at hje
      have endpoint_cases : ∀ x y : V, x ≠ y → x ∈ G.ends e → y ∈ G.ends e →
          z ∈ G.ends e → x = z ∨ y = z := by
        intro x y hxy hx hy hz
        refine Sym2.inductionOn (G.ends e) ?_ hx hy hz
        intro a b hx hy hz
        simp only [Sym2.mem_iff] at hx hy hz
        aesop
      have hprev : j = 0 ∨ p.getVert (j - 1) = Sum.inl z ∨
          p.getVert (j + 1) = Sum.inl z := by
        by_cases hj0 : j = 0
        · exact Or.inl hj0
        · right
          have hadj := p.adj_getVert_succ (i := j - 1) (by omega)
          have hleft : (TwoColorIncidenceGraph G phi delta gamma).Adj
              (p.getVert (j - 1)) (Sum.inr e) := by
            rw [← hje]
            simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)] using hadj
          have hright := p.adj_getVert_succ (i := j) hjlt
          cases hcase : p.getVert (j - 1) with
          | inl x =>
            have hleft' := hleft
            rw [hcase] at hleft'
            simp only [TwoColorIncidenceGraph] at hleft'
            rcases hleft' with ⟨hx, hxcol⟩
            cases hcase2 : p.getVert (j + 1) with
            | inl y =>
              have hright' := hright
              rw [hje, hcase2] at hright'
              simp only [TwoColorIncidenceGraph] at hright'
              rcases hright' with ⟨hy, hycol⟩
              have hxy : x ≠ y := by
                intro hxy
                have hjnext : j + 1 ≤ p.length := by omega
                have hjprev : j - 1 ≤ p.length := by omega
                have hi := hppath.getVert_injOn hjprev hjnext
                  (show p.getVert (j - 1) = p.getVert (j + 1) by rw [hcase, hcase2, hxy])
                omega
              rcases endpoint_cases x y hxy hx hy hez with h | h
              · aesop
              · aesop
            | inr y => rw [hje, hcase2] at hright; simp [TwoColorIncidenceGraph] at hright
          | inr x =>
            have hleft' := hleft
            rw [hcase] at hleft'
            simp [TwoColorIncidenceGraph] at hleft'
      cases hprev with
      | inl hj0 => subst j; simp at hje
      | inr hrest =>
        rcases hrest with hzprev | hznext
        · have hjprev : j - 1 ≤ p.length := by omega
          have hinj := hppath.getVert_injOn hjprev (by omega : p.length ≤ p.length)
            (hzprev.trans (p.getVert_length).symm)
          have hEq := hinj
          have hji : p.length - 1 = j := by omega
          rw [hji]
          exact hje
        · have hjnext : j + 1 ≤ p.length := by omega
          have hinj := hppath.getVert_injOn hjnext (by omega : p.length ≤ p.length)
            (hznext.trans (p.getVert_length).symm)
          have hEq := hinj
          have hji : p.length - 1 = j := by omega
          rw [hji]
          exact hje
    have support_of_endpoint : ∀ e, Incident G z e →
        (phi e = some delta ∨ phi e = some gamma) → Sum.inr e ∈ p.support := by
      intro e hez hecolor
      have hedge :
          (TwoColorIncidenceGraph G phi delta gamma).Adj (Sum.inl z) (Sum.inr e) :=
        ⟨hez, hecolor⟩
      have hecomp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hedge
      have hzcomp :
          (TwoColorIncidenceGraph G phi delta gamma).connectedComponentMk
              (Sum.inl z) =
            (TwoColorIncidenceGraph G phi delta gamma).connectedComponentMk
              (Sum.inl u) := by
        apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp
        change Sum.inl z ∈ TwoColorComponent G phi delta gamma (Sum.inl u)
        rw [← hpsupp]
        exact p.end_mem_support
      have hmem : Sum.inr e ∈ TwoColorComponent G phi delta gamma (Sum.inl u) := by
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr (hecomp.symm.trans hzcomp)
      have hset := congrArg (fun s : Set (Sum V E) => Sum.inr e ∈ s) hpsupp
      exact hset.mpr hmem
    change gamma ∈ Finset.univ \ PresentColors G phi z
    have hdp : delta ∈ PresentColors G phi z := by
      by_contra hn
      apply hd
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
    change gamma ∈ Finset.univ \ PresentColors G phi z
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_univ _
    · intro hgp
      change gamma ∈ (Finset.univ.filter (fun c => ∃ e, Incident G z e ∧ phi e = some c)) at hgp
      change delta ∈ (Finset.univ.filter (fun c => ∃ e, Incident G z e ∧ phi e = some c)) at hdp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hgp hdp
      rcases hgp with ⟨e, hez, hec⟩
      rcases hdp with ⟨d, hdz, hdc⟩
      have helast := component_of_endpoint e hez
        (support_of_endpoint e hez (Or.inr hec))
      have hdlast := component_of_endpoint d hdz
        (support_of_endpoint d hdz (Or.inl hdc))
      have hed : e = d := by
        apply Sum.inr.inj
        exact helast.symm.trans hdlast
      have hcol : gamma = delta := by
        have hc := congrArg phi hed
        rw [hec, hdc] at hc
        exact Option.some.inj hc
      have hpnon : 0 < p.length := by omega
      have hfirst := p.adj_getVert_succ (i := 0) (by omega)
      have hnot : gamma ∉ PresentColors G phi u := by
        exact (Finset.mem_sdiff.mp (show gamma ∈ MissingColors G phi u from hgamma)).2
      rw [p.getVert_zero] at hfirst
      cases hnext : p.getVert 1 with
      | inl x => rw [hnext] at hfirst; simp [TwoColorIncidenceGraph] at hfirst
      | inr f =>
        have hfirst' := hfirst
        rw [hnext] at hfirst'
        simp only [TwoColorIncidenceGraph] at hfirst'
        rcases hfirst' with ⟨hinc, hcolor⟩
        have hcolor' : phi f = some gamma := by
          rcases hcolor with hcolor | hcolor
          · rw [hcol]
            exact hcolor
          · exact hcolor
        apply hnot
        unfold PresentColors
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨f, hinc, hcolor'⟩⟩

theorem ScheideExitVertexTreeExit {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (v : V)
    (hexit : ScheideExitVertex T phi v) :
    ∃ gamma delta : Fin k,
    delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) ∧ TreeExit T phi delta gamma v := by
  classical
  rcases hexit with ⟨u, gamma, delta, hu, hgamma, hdelta, z, p, hp, i, hiv, hvi, hafter⟩
  rcases hp with ⟨hpu, hppath, hz, hpsupp⟩
  have hivmem : Sum.inl v ∈ p.support := by
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    exact ⟨i.val, hiv, by omega⟩
  let a := p.takeUntil (Sum.inl v) hivmem
  let q := p.dropUntil (Sum.inl v) hivmem
  have hsplit : a.append q = p := p.take_spec hivmem
  have hlen : a.length + q.length = p.length := by
    have ht := congrArg SimpleGraph.Walk.length hsplit
    simpa using ht
  have halen : a.length = i.val := by
    have haend : a.getVert a.length = Sum.inl v := by simp [a]
    have hpidx : p.getVert a.length = Sum.inl v := by
      rw [← hsplit, SimpleGraph.Walk.getVert_append]
      simp []
    have hpidx' : p.getVert a.length = p.getVert i.val := hpidx.trans hiv.symm
    apply hppath.getVert_injOn
    · have hale : a.length ≤ p.length := by rw [← hlen]; omega
      exact hale
    · have hi_le : i.val ≤ p.length := by omega
      exact hi_le
    · exact hpidx'
  have hqpath : q.IsPath := hppath.dropUntil _
  have hqrev : q.reverse.IsPath := hqpath.reverse
  have hqpos : 0 < q.length := by
    apply (SimpleGraph.Walk.not_nil_iff_lt_length).mp
    intro hnil
    have hev : (Sum.inl v : Sum V E) = Sum.inl z := SimpleGraph.Walk.Nil.eq hnil
    have hvz : v = z := Sum.inl.inj hev
    exact hz (hvz.symm ▸ hvi)
  have hqnotone : q.length ≠ 1 := by
    intro hone
    have hadj := q.adj_getVert_succ (i := 0) (by omega)
    have hend := q.getVert_length
    rw [hone] at hend
    rw [q.getVert_zero, hend] at hadj
    simp [TwoColorIncidenceGraph] at hadj
  have hqv : v ∈ TreeSequenceVertexSet T := hvi
  have hqonly : ∀ w ∈ TreeSequenceVertexSet T,
      (Sum.inl w ∈ q.reverse.support ↔ w = v) := by
    intro w hw
    constructor
    · intro hmem
      obtain ⟨j, hj, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
      have hj' : j ≤ q.reverse.length := hjle
      have hjq : q.reverse.getVert j = Sum.inl w := hj
      have hji : q.getVert (q.length - j) = Sum.inl w := by
        exact (SimpleGraph.Walk.getVert_reverse q j).symm.trans hjq
      have hqidx : q.getVert (q.length - j) = Sum.inl w := hji
      by_cases hn : q.length - j = 0
      · have : q.getVert 0 = Sum.inl w := by simpa [hn] using hqidx
        have hvw : v = w := by simpa using this
        exact hvw.symm
      · have hpos : 0 < q.length - j := Nat.pos_of_ne_zero hn
        have hpw : p.getVert (i.val + (q.length - j)) = Sum.inl w := by
          calc
            p.getVert (i.val + (q.length - j)) =
                (a.append q).getVert (i.val + (q.length - j)) := by rw [hsplit]
            _ = Sum.inl w := by
              have hnot : ¬ i.val + (q.length - j) < a.length := by omega
              simpa [SimpleGraph.Walk.getVert_append, hnot, halen] using hji
        have hjleq : j ≤ q.length := by simpa using hj'
        have hbound : i.val + (q.length - j) ≤ p.length := by omega
        have hgt : i.val < i.val + (q.length - j) := by omega
        exact (hafter ⟨i.val + (q.length - j), by omega⟩ hgt w hpw).elim hw
    · intro hwv
      subst w
      apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      exact ⟨q.reverse.length, q.reverse.getVert_length, by simp⟩
  refine ⟨gamma, delta, hdelta, ?_⟩
  refine ⟨z, q.reverse, ?_⟩
  unfold TreeExitPath
  refine ⟨hqrev, ?_, ?_, hqv, ?_, ?_⟩
  · have hlenrev : q.reverse.length = q.length := q.length_reverse
    omega
  · exact hz
  · exact @helper_branch_108 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T) (@phi)
      (@v) (@u) (@gamma) (@delta) (@hgamma) (@z) (@p) (@i) (@hiv) (@hafter) (@hppath) (@hz)
      (@hpsupp) (@hivmem) (@hsplit) (@hlen) (@halen) (@hqpath) (@hqrev) (@hqpos) (@hqnotone)
      (@hqonly)
  · exact hqonly

end GoldbergSeymour

end
