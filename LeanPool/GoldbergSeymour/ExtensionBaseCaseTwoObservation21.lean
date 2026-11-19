/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges

public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Extension Base Case Two Observation21

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hu_at_two_153.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} (rho1 : PartialEdgeColoring E k)
      (gammaN deltaN : Fin k) (fN : E) (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x))
      (_ : p.IsPath),
    let _ : BEq (V ⊕ E) := instBEqOfDecidableEq;
    ∀ (u : V) (_ : G.ends fN = s(terminalSupport, u)),
    ∀ j < p.length,
    ∀ (b : V),
    p.getVert (j + (1 : ℕ)) = Sum.inl b →
    b ∈ G.ends fN →
    j = (1 : ℕ) →
    p.getVert (2 : ℕ) = Sum.inl u := by
  classical
  intro V E _ _ G k rho1 gammaN deltaN fN terminalSupport x p hpath this u hfend j hjlt b hb hmb
      hjone
  have hjtwo : j + 1 = 2 := by omega
  have hbu : b = u := by
    have hm : b ∈ G.ends fN := hmb
    have : b = terminalSupport ∨ b = u := by
      rw [hfend] at hm
      simpa only [Sym2.mem_iff] using hm
    rcases this with h | h
    · exfalso
      have hi : 2 = 0 := by
        apply hpath.getVert_injOn (by omega : 2 ≤ p.length)
          (show 0 ≤ p.length from Nat.zero_le _)
        have htwo : p.getVert 2 = Sum.inl terminalSupport := by
          calc
            p.getVert 2 = p.getVert (j + 1) := congrArg p.getVert hjtwo.symm
            _ = Sum.inl b := hb
            _ = Sum.inl terminalSupport := by rw [h]
        exact htwo.trans p.getVert_zero.symm
      omega
    · exact h
  calc
    p.getVert 2 = p.getVert (j + 1) := congrArg p.getVert hjtwo.symm
    _ = Sum.inl b := hb
    _ = Sum.inl u := by rw [hbu]

private theorem helper_hiwgt_181.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn : TreeSequence G e0)
      (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (fN : E)
      (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x)),
    let _ : BEq (V ⊕ E) := instBEqOfDecidableEq;
    ∀ u ∉ TreeSequenceVertexSet Tn,
    ∀ w ∈ TreeSequenceVertexSet Tn,
    w ≠ terminalSupport →
    ∀ (j : ℕ),
    p.getVert j = Sum.inr fN →
    j = (1 : ℕ) →
    p.getVert (2 : ℕ) = Sum.inl u →
    ∀ (iw : ℕ),
    p.getVert iw = Sum.inl w →
    iw ≤ p.length →
    p.getVert iw = Sum.inl w →
    (2 : ℕ) < iw := by
  classical
  intro V E _ _ G k e0 Tn rho1 gammaN deltaN fN terminalSupport x p this u hu_not_Tn w hw hwu j
      hjf hjone hu_at_two iw hiw hiwle hiwval
  have hiwnzero : iw ≠ 0 := by
    intro hz
    have : w = terminalSupport := by
      subst iw
      exact Sum.inl.inj (hiwval.symm.trans p.getVert_zero)
    exact hwu this
  have hiwneone : iw ≠ 1 := by
    intro hz
    have : (Sum.inl w : Sum V E) = Sum.inr fN := by
      subst iw
      rw [hjone] at hjf
      exact hiwval.symm.trans hjf
    cases this
  have hiwneu : iw ≠ 2 := by
    intro hz
    have : w = u := by
      subst iw
      exact Sum.inl.inj (hiwval.symm.trans hu_at_two)
    exact hu_not_Tn (this ▸ hw)
  omega

private theorem helper_hw_suffix_217.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} (rho1 : PartialEdgeColoring E k)
      (gammaN deltaN : Fin k) (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x))
      (u : V),
    let uSupport : V ⊕ E := Sum.inl u;
    ∀ (huSupport : uSupport ∈ p.support),
    let suffix : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk uSupport (Sum.inl x) :=
      p.dropUntil uSupport huSupport;
    ∀ (w : V),
    ∀ j < p.length,
    j = (1 : ℕ) →
    ∀ iw ≤ p.length,
    p.getVert iw = Sum.inl w →
    (2 : ℕ) < iw →
    suffix.support = (p.drop (2 : ℕ)).support →
    Sum.inl w ∈ suffix.support := by
  classical
  intro V E _ _ G k rho1 gammaN deltaN terminalSupport x p u uSupport huSupport suffix w j hjlt
      hjone iw hiwle hiwval hiwgt hsuffix
  rw [hsuffix]
  have hdrop : (p.drop 2).support = p.support.drop 2 := by
    simp [Nat.min_eq_left (by omega : 2 ≤ p.length)]
  apply List.mem_iff_getElem.mpr
  refine ⟨iw - 2, ?_, ?_⟩
  · have hp : iw - 2 < p.length + 1 - 2 := by omega
    rw [hdrop]
    simp only [List.length_drop, SimpleGraph.Walk.length_support]
    omega
  · have hvalid : iw - 2 < (p.support.drop 2).length := by
      simp [List.length_drop, SimpleGraph.Walk.length_support]; omega
    have helem : (p.support.drop 2)[iw - 2]'hvalid = Sum.inl w := by
      simp only [List.getElem_drop]
      have hsum : 2 + (iw - 2) = iw := by omega
      have hiwlt : iw < p.support.length := by
        simpa [SimpleGraph.Walk.length_support] using Nat.lt_succ_of_le hiwle
      have hh := p.support_getElem_eq_getVert (n := iw) hiwlt
      simpa [hsum] using hh.trans hiwval
    simpa [hdrop] using helem

private theorem helper_branch_352.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0)
      (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (fN : E)
      (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x))
      (_ : p.IsPath)
      (_ : (∃ w ∈ TreeSequenceVertexSet Tn, w ≠ terminalSupport ∧ Sum.inl w ∈ p.support))
      (_ : Incident G terminalSupport fN),
    let _ : BEq (V ⊕ E) := instBEqOfDecidableEq;
    let vertexSet : Finset V := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime;
    ∀ (u : V),
    let uSupport : V ⊕ E := Sum.inl u;
    ∀ (huSupport : uSupport ∈ p.support),
    let suffix : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk uSupport (Sum.inl x) :=
      p.dropUntil uSupport huSupport;
    ∀
      (_ :
        List.filter
            (fun (z : V ⊕ E) =>
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support =
          [uSupport])
      (_ : u ≠ terminalSupport) (_ : V) (_ : u ∉ TreeSequenceVertexSet Tn)
      (_ : Sum.inr fN ∈ p.support),
    ¬Incident G u fN := by
  classical
  intro V E _ _ G k e0 Tn TjPrime rho1 gammaN deltaN fN terminalSupport x p hpath htwoN
      hfNterminal this vertexSet u uSupport huSupport suffix suffix_filter_singleton hu_terminal
      v hu_not_Tn hf_support huf
  obtain ⟨w, hw, hwu, hwm⟩ := htwoN
  have hut : u ≠ terminalSupport := hu_terminal
  have hfend : G.ends fN = s(terminalSupport, u) := by
    have hend_of_mem : ∀ {z : Sym2 V} {a b : V}, a ∈ z → b ∈ z → a ≠ b →
        z = s(a,b) := by
      intro z a b ha hb hab
      induction z using Sym2.inductionOn with
      | _ c d =>
        simp only [Sym2.mem_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          simp_all []
    exact hend_of_mem hfNterminal huf hut.symm
  obtain ⟨j, hj, hjle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf_support
  have hjf : p.getVert j = Sum.inr fN := hj
  have hjnotzero : j ≠ 0 := by
    intro hz
    have : (Sum.inl terminalSupport : Sum V E) = Sum.inr fN := by
      simpa [hz] using hjf.symm
    cases this
  have hjlt : j < p.length := by
    by_contra hn
    have he : j = p.length := by omega
    subst j
    have : (Sum.inl x : Sum V E) = Sum.inr fN := by
      simpa using hjf.symm
    cases this
  have hprev := p.adj_getVert_succ (i := j - 1) (by omega)
  have hnext := p.adj_getVert_succ (i := j) hjlt
  have hprev' : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Adj
      (p.getVert (j - 1)) (Sum.inr fN) := by
    rw [← hjf]
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hjnotzero)] using hprev
  have hprev_vertex : ∃ a : V, p.getVert (j - 1) = Sum.inl a := by
    cases hc : p.getVert (j - 1) with
    | inl a =>
        exact ⟨a, rfl⟩
    | inr e =>
        have ha := hprev'
        rw [hc] at ha
        exact False.elim (by simp [TwoColorIncidenceGraph] at ha)
  have hnext_vertex : ∃ b : V, p.getVert (j + 1) = Sum.inl b := by
    have ha := hnext
    rw [hjf] at ha
    cases hc : p.getVert (j + 1) with
    | inl a =>
        exact ⟨a, rfl⟩
    | inr e =>
        rw [hc] at ha
        exact False.elim (by simp [TwoColorIncidenceGraph] at ha)
  obtain ⟨a, ha⟩ := hprev_vertex
  obtain ⟨b, hb⟩ := hnext_vertex
  have hab : a ≠ b := by
    intro he
    have hi := hpath.getVert_injOn (by omega : j - 1 ≤ p.length)
      (by omega : j + 1 ≤ p.length)
      (by rw [ha, hb]; exact congrArg Sum.inl he)
    omega
  have hma : a ∈ G.ends fN := by
    have hh := hprev'
    rw [ha] at hh
    simpa [Incident, TwoColorIncidenceGraph] using hh.1
  have hmb : b ∈ G.ends fN := by
    have hh := hnext
    rw [hjf, hb] at hh
    simpa [Incident, TwoColorIncidenceGraph] using hh.1
  have edge_identity : ∀ {z : Sym2 V} {c d : V}, c ∈ z → d ∈ z → c ≠ d →
      z = s(c,d) := by
    intro z c d hc hd hcd
    induction z using Sym2.inductionOn with
    | _ r t =>
      simp only [Sym2.mem_iff] at hc hd
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp_all
  have hfends : G.ends fN = s(a,b) := edge_identity hma hmb hab
  have hterm_endpoint : terminalSupport ∈ s(a,b) := by
    rw [← hfends]
    exact hfNterminal
  have hendpoint : a = terminalSupport ∨ b = terminalSupport := by
    simp only [Sym2.mem_iff] at hterm_endpoint
    rcases hterm_endpoint with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hterm_prev : p.getVert (j - 1) = Sum.inl terminalSupport := by
    rcases hendpoint with h | h
    · simp [ha, h]
    · exfalso
      have hi : j + 1 = 0 := by
        apply hpath.getVert_injOn
          (show j + 1 ≤ p.length from Nat.succ_le_of_lt hjlt)
          (show 0 ≤ p.length from Nat.zero_le _)
        simp [hb, h]
      omega
  have hjone : j = 1 := by
    have hi : j - 1 = 0 := by
      apply hpath.getVert_injOn (by omega : j - 1 ≤ p.length)
          (show 0 ≤ p.length from Nat.zero_le _)
      exact hterm_prev.trans p.getVert_zero.symm
    have hjpos : 0 < j := Nat.pos_of_ne_zero hjnotzero
    omega
  have hu_at_two :=
    @helper_hu_at_two_153 V E inferInstance inferInstance G k rho1 gammaN deltaN fN
        terminalSupport x p hpath u hfend j hjlt b hb hmb hjone
  obtain ⟨iw, hiw, hiwle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (by
      exact hwm)
  have hiwval : p.getVert iw = Sum.inl w := hiw
  have hiwgt :=
    @helper_hiwgt_181 V E inferInstance inferInstance G k e0 Tn rho1 gammaN deltaN fN
        terminalSupport x p u hu_not_Tn w hw hwu j hjf hjone hu_at_two iw hiw hiwle hiwval
  have hidx : p.support.idxOf uSupport = 2 := by
    apply hpath.getVert_injOn
      (by
        have hh := List.idxOf_lt_length_of_mem huSupport
        simp only [SimpleGraph.Walk.length_support] at hh
        exact Nat.le_of_lt_succ hh)
      (by omega : 2 ≤ p.length)
    calc
      p.getVert (p.support.idxOf uSupport) = uSupport :=
        p.getVert_support_idxOf huSupport
      _ = p.getVert 2 := by simpa [uSupport] using hu_at_two.symm
  have hsuffix : suffix.support = (p.drop 2).support := by
    change (p.dropUntil uSupport huSupport).support = (p.drop 2).support
    rw [SimpleGraph.Walk.dropUntil_eq_drop]
    simp [hidx]
  have hw_suffix :=
    @helper_hw_suffix_217 V E inferInstance inferInstance G k rho1 gammaN deltaN
        terminalSupport x p u huSupport w j hjlt hjone iw hiwle hiwval hiwgt hsuffix
  have hwf : Sum.inl w ∈ suffix.support.filter (fun z : Sum V E => match z with
      | Sum.inl v => decide (v ∈ vertexSet)
      | Sum.inr _ => false) := by
    apply List.mem_filter.mpr
    exact ⟨hw_suffix, by simp [vertexSet, hw]⟩
  rw [suffix_filter_singleton] at hwf
  have : w = u := by simpa [uSupport] using hwf
  exact hu_not_Tn (this ▸ hw)

private theorem helper_suffix_filter_singleton_359.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0)
      (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x)),
    let vertexSet : Finset V := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime;
    ∀ (u : V),
    let uSupport : V ⊕ E := Sum.inl u;
    ∀ (huSupport : uSupport ∈ p.support) (_ : u ∈ vertexSet)
      (_ :
        (∀ (l : List (V ⊕ E)) (a : V ⊕ E) (_ : l.Nodup) (_ : l.head? = some a)
          (_ : l.getLast? = some a), l = [a])),
    let suffix : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk uSupport (Sum.inl x) :=
      p.dropUntil uSupport huSupport;
    ∀ (_ : suffix.IsPath)
      (suffix_eligible_nonempty :
        List.filter
            (fun (z : V ⊕ E) =>
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support ≠
          [])
      (_ :
        (List.filter
                (fun (z : V ⊕ E) =>
                  match z with
                  | Sum.inl v => decide (v ∈ vertexSet)
                  | Sum.inr _ => false)
                suffix.support).getLast
            suffix_eligible_nonempty =
          uSupport),
    List.filter
        (fun (z : V ⊕ E) =>
          match z with
          | Sum.inl v => decide (v ∈ vertexSet)
          | Sum.inr _ => false)
        suffix.support =
      [uSupport] := by
  classical
  intro V E _ _ G k e0 Tn TjPrime rho1 gammaN deltaN terminalSupport x p vertexSet u uSupport
      huSupport huVertex singleton_of_head_last suffix suffix_path suffix_eligible_nonempty
      suffix_filter_last
  refine singleton_of_head_last
    (suffix.support.filter (fun z : Sum V E => match z with
      | Sum.inl v => decide (v ∈ vertexSet)
      | Sum.inr _ => false)) uSupport ?_ ?_ ?_
  · exact (suffix_path.support_nodup).filter _
  · rw [← suffix.cons_tail_support]
    rw [List.filter_cons]
    simp [uSupport, huVertex]
  · change (suffix.support.filter (fun z : Sum V E => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false)).getLast? = some uSupport
    cases hlist : suffix.support.filter (fun z : Sum V E => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false) with
    | nil => exact False.elim (suffix_eligible_nonempty hlist)
    | cons a t =>
        have hlast := suffix_filter_last
        have hlast' : (a :: t).getLast (by simp) = uSupport := by
          simpa [hlist] using hlast
        simpa [List.getLast?, hlist] using congrArg some hlast'

private theorem helper_hu_not_Tn_489.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0)
      (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (fN : E)
      (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x))
      (_ : terminalSupport ∈ TreeSequenceVertexSet Tn)
      (_ : BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn) gammaN = { fN })
      (_ : Incident G terminalSupport fN),
    let vertexSet : Finset V := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime;
    let eligible : List (V ⊕ E) :=
      List.filter
        (fun (z : V ⊕ E) =>
          match z with
          | Sum.inl v => decide (v ∈ vertexSet)
          | Sum.inr _ => false)
        p.support;
    ∀ (eligible_nonempty : eligible ≠ []),
    let chosen : V ⊕ E := eligible.getLast eligible_nonempty;
    ∀ (u : V) (_ : chosen = Sum.inl u),
    let uSupport : V ⊕ E := Sum.inl u;
    ∀ (huSupport : uSupport ∈ p.support) (_ : u ∈ vertexSet),
    let suffix : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk uSupport (Sum.inl x) :=
      p.dropUntil uSupport huSupport;
    let exitPath :
      (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) uSupport :=
      suffix.reverse;
    ∀ (_ : suffix.IsPath) (_ : exitPath.IsPath)
      (_ : exitPath.support = suffix.support.reverse)
      (suffix_eligible_nonempty :
        List.filter
            (fun (z : V ⊕ E) =>
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support ≠
          [])
      (_ :
        (List.filter
                (fun (z : V ⊕ E) =>
                  match z with
                  | Sum.inl v => decide (v ∈ vertexSet)
                  | Sum.inr _ => false)
                suffix.support).getLast
            suffix_eligible_nonempty =
          uSupport)
      (_ :
        List.filter
            (fun (z : V ⊕ E) =>
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support =
          [uSupport])
      (_ : u ≠ terminalSupport) (_ : (0 : ℕ) < suffix.length) (_ : suffix.length ≠ (1 : ℕ))
      (_ : (2 : ℕ) ≤ suffix.length) (g : E) (_ : suffix.getVert (1 : ℕ) = Sum.inr g) (v : V)
      (_ : suffix.getVert (2 : ℕ) = Sum.inl v) (_ : v ∉ vertexSet) (_ : Incident G u g)
      (_ : Incident G v g) (_ : u ≠ v) (_ : G.ends g = s(u, v))
      (_ : g ∈ BoundaryEdges G vertexSet) (_ : rho1 g = some gammaN ∨ rho1 g = some deltaN)
      (_ : rho1 g = some gammaN) (_ : g ∈ BoundaryColorEdges G rho1 vertexSet gammaN),
    u ∉ TreeSequenceVertexSet Tn := by
  classical
  intro V E _ _ _ _ G k e0 Tn TjPrime rho1 gammaN deltaN fN terminalSupport x p hterminalN
      hgammaBoundary hfNterminal vertexSet eligible eligible_nonempty chosen u chosen_eq uSupport
      huSupport huVertex suffix exitPath suffix_path exit_path exit_support
      suffix_eligible_nonempty suffix_filter_last suffix_filter_singleton hu_terminal
      suffix_positive suffix_not_one suffix_length_two g hg v hv hv_outside hgu hgv huv hends
      hg_boundary hg_color hg_gamma hg_colored_boundary huT
  have hgt : g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn) gammaN := by
    unfold BoundaryColorEdges
    simp only [Finset.mem_filter]
    refine ⟨?_, hg_gamma⟩
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hvTn : v ∉ TreeSequenceVertexSet Tn := by
      intro hvT
      exact hv_outside (Finset.mem_union.mpr (Or.inl hvT))
    exact ⟨u, huT, v, hvTn, hends⟩
  rw [hgammaBoundary] at hgt
  have hgf : g = fN := by simpa using hgt
  subst g
  have heq : u = terminalSupport := by
    have ht : terminalSupport ∈ s(u, v) := by
      rw [← hends]
      exact hfNterminal
    simp only [Sym2.mem_iff] at ht
    rcases ht with rfl | rfl
    · rfl
    · exfalso
      apply hv_outside
      exact Finset.mem_union.mpr (Or.inl hterminalN)
  exact hu_terminal heq

private theorem helper_branch_530.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0)
      (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x)),
    let vertexSet : Finset V := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime;
    ∀ (u : V),
    let uSupport : V ⊕ E := Sum.inl u;
    ∀ (huSupport : uSupport ∈ p.support),
    let suffix : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk uSupport (Sum.inl x) :=
      p.dropUntil uSupport huSupport;
    let exitPath :
      (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) uSupport :=
      suffix.reverse;
    ∀ (_ : exitPath.support = suffix.support.reverse)
      (_ :
        List.filter
            (fun (z : V ⊕ E) =>
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support =
          [uSupport]),
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime,
    Sum.inl w ∈ exitPath.support ↔ w = u := by
  classical
  intro V E _ _ G k e0 Tn TjPrime rho1 gammaN deltaN terminalSupport x p vertexSet u uSupport
      huSupport suffix exitPath exit_support suffix_filter_singleton w hw
  constructor
  · intro hwm
    have hwm' : Sum.inl w ∈ suffix.support := by
      rw [exit_support] at hwm
      exact List.mem_reverse.mp hwm
    have hwf : Sum.inl w ∈ suffix.support.filter (fun z => match z with
        | Sum.inl z => decide (z ∈ vertexSet)
        | Sum.inr _ => false) :=
      List.mem_filter.mpr ⟨hwm', by simp [vertexSet, hw]⟩
    rw [suffix_filter_singleton] at hwf
    simpa [uSupport] using hwf
  · intro hwu
    subst w
    rw [exit_support]
    apply List.mem_reverse.mpr
    have huf : Sum.inl u ∈ suffix.support.filter (fun z => match z with
        | Sum.inl z => decide (z ∈ vertexSet)
        | Sum.inr _ => false) := by
      rw [suffix_filter_singleton]
      simp [uSupport]
    exact (List.mem_filter.mp huf).1

private theorem helper_singleton_of_head_last_580.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (l : List (V ⊕ E)) (a : V ⊕ E),
    l.Nodup →
    l.head? = some a →
    l.getLast? = some a →
    l = [a] := by
  classical
  intro V E l
  induction l with
  | nil => simp
  | cons b t ih =>
    intro a hn hh hl
    simp only [List.head?_cons] at hh
    have hba : b = a := Option.some.inj hh
    subst b
    by_cases ht : t = []
    · simp [ht]
    · have hlast : t.getLast? = some a := by
        cases t with
        | nil => contradiction
        | cons c r => simpa using hl
      obtain ⟨ys, hys⟩ := (List.getLast?_eq_some_iff.mp hlast)
      have hmem : a ∈ t := by
        rw [hys]
        simp
      exact False.elim ((List.nodup_cons.mp hn).1 hmem)

private theorem helper_hu_terminal_629.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0)
      (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x))
      (_ : (∃ w ∈ TreeSequenceVertexSet Tn, w ≠ terminalSupport ∧ Sum.inl w ∈ p.support)),
    let vertexSet : Finset V := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime;
    let eligible : List (V ⊕ E) :=
      List.filter
        (fun (z : V ⊕ E) =>
          match z with
          | Sum.inl v => decide (v ∈ vertexSet)
          | Sum.inr _ => false)
        p.support;
    ∀ (eligible_nonempty : eligible ≠ []),
    let chosen : V ⊕ E := eligible.getLast eligible_nonempty;
    ∀ (u : V) (_ : chosen = Sum.inl u),
    let uSupport : V ⊕ E := Sum.inl u;
    ∀ (huSupport : uSupport ∈ p.support) (_ : u ∈ vertexSet),
    let suffix : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk uSupport (Sum.inl x) :=
      p.dropUntil uSupport huSupport;
    let exitPath :
      (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) uSupport :=
      suffix.reverse;
    ∀ (_ : suffix.IsPath) (_ : exitPath.IsPath)
      (_ : exitPath.support = suffix.support.reverse)
      (suffix_eligible_nonempty :
        List.filter
            (fun (z : V ⊕ E) =>
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support ≠
          [])
      (_ :
        (List.filter
                (fun (z : V ⊕ E) =>
                  match z with
                  | Sum.inl v => decide (v ∈ vertexSet)
                  | Sum.inr _ => false)
                suffix.support).getLast
            suffix_eligible_nonempty =
          uSupport)
      (_ :
        List.filter
            (fun (z : V ⊕ E) =>
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support =
          [uSupport]),
    u ≠ terminalSupport := by
  classical
  intro V E _ _ G k e0 Tn TjPrime rho1 gammaN deltaN terminalSupport x p htwoN vertexSet eligible
      eligible_nonempty chosen u chosen_eq uSupport huSupport huVertex suffix exitPath
      suffix_path exit_path exit_support suffix_eligible_nonempty suffix_filter_last
      suffix_filter_singleton heq
  subst u
  have hs : suffix = p := by
    simp [suffix, uSupport]
  obtain ⟨w, hw, hwu, hwm⟩ := htwoN
  have hwm' : Sum.inl w ∈ suffix.support := by rw [hs]; exact hwm
  have hwf : Sum.inl w ∈ suffix.support.filter (fun z => match z with
      | Sum.inl v => decide (v ∈ vertexSet)
      | Sum.inr _ => false) := by
    apply List.mem_filter.mpr
    exact ⟨hwm', by simp [vertexSet, hw]⟩
  rw [suffix_filter_singleton] at hwf
  apply hwu
  simpa [uSupport] using hwf

private theorem helper_hv_outside_673.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0)
      (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x)),
    let vertexSet : Finset V := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime;
    ∀ (u : V),
    let uSupport : V ⊕ E := Sum.inl u;
    ∀ (huSupport : uSupport ∈ p.support),
    let suffix : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk uSupport (Sum.inl x) :=
      p.dropUntil uSupport huSupport;
    ∀ (_ : suffix.IsPath)
      (_ :
        List.filter
            (fun (z : V ⊕ E) =>
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support =
          [uSupport])
      (_ : (2 : ℕ) ≤ suffix.length) (v : V) (_ : suffix.getVert (2 : ℕ) = Sum.inl v),
    v ∉ vertexSet := by
  classical
  intro V E _ _ G k e0 Tn TjPrime rho1 gammaN deltaN terminalSupport x p vertexSet u uSupport
      huSupport suffix suffix_path suffix_filter_singleton suffix_length_two v hv hvin
  have hvm : Sum.inl v ∈ suffix.support := by
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    exact ⟨2, hv, by omega⟩
  have hvf : Sum.inl v ∈ suffix.support.filter (fun z => match z with
      | Sum.inl z => decide (z ∈ vertexSet)
      | Sum.inr _ => false) := by
    exact List.mem_filter.mpr ⟨hvm, by simp [hvin]⟩
  rw [suffix_filter_singleton] at hvf
  have hvu : v = u := by simpa [uSupport] using hvf
  have hinj := suffix_path.getVert_injOn (by omega : 0 ≤ suffix.length)
    (by omega : 2 ≤ suffix.length)
    (show suffix.getVert 0 = suffix.getVert 2 by
      rw [suffix.getVert_zero, hv]
      exact congrArg Sum.inl hvu.symm)
  omega

private theorem helper_continuation_847.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0)
      (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (fN : E)
      (terminalSupport x : V)
      (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
          (Sum.inl x))
      (_ : p.IsPath)
      (_ :
        {y : V ⊕ E | y ∈ p.support} =
          TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
      (_ : terminalSupport ∈ TreeSequenceVertexSet Tn)
      (_ : (∃ w ∈ TreeSequenceVertexSet Tn, w ≠ terminalSupport ∧ Sum.inl w ∈ p.support))
      (_ :
        BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn) gammaN = ({ fN } : Finset E))
      (_ :
        BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
            deltaN =
          ∅)
      (_ : Incident G terminalSupport fN),
    let vertexSet : Finset V := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime;
    let eligible : List (V ⊕ E) :=
      List.filter
        (fun (z : V ⊕ E) ↦
          match z with
          | Sum.inl v => decide (v ∈ vertexSet)
          | Sum.inr _ => false)
        p.support;
    ∀ (eligible_nonempty : eligible ≠ []),
    let chosen : V ⊕ E := eligible.getLast eligible_nonempty;
    ∀ (u : V) (_ : chosen = Sum.inl u),
    let uSupport : V ⊕ E := Sum.inl u;
    ∀ (huSupport : uSupport ∈ p.support) (_ : u ∈ vertexSet),
    let suffix : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk uSupport (Sum.inl x) :=
      p.dropUntil uSupport huSupport;
    let exitPath :
      (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) uSupport :=
      suffix.reverse;
    ∀ (_ : suffix.IsPath) (_ : exitPath.IsPath)
      (_ : exitPath.support = suffix.support.reverse)
      (suffix_eligible_nonempty :
        List.filter
            (fun (z : V ⊕ E) ↦
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support ≠
          [])
      (_ :
        (List.filter
                (fun (z : V ⊕ E) ↦
                  match z with
                  | Sum.inl v => decide (v ∈ vertexSet)
                  | Sum.inr _ => false)
                suffix.support).getLast
            suffix_eligible_nonempty =
          uSupport)
      (_ :
        List.filter
            (fun (z : V ⊕ E) ↦
              match z with
              | Sum.inl v => decide (v ∈ vertexSet)
              | Sum.inr _ => false)
            suffix.support =
          [uSupport])
      (_ : u ≠ terminalSupport) (_ : (0 : ℕ) < suffix.length) (_ : suffix.length ≠ (1 : ℕ))
      (_ : (2 : ℕ) ≤ suffix.length) (g : E) (_ : suffix.getVert (1 : ℕ) = Sum.inr g) (v : V)
      (_ : suffix.getVert (2 : ℕ) = Sum.inl v),
    ∃ (u : V) (exitPath :
      (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)),
    u ∈ TreeSequenceVertexSet TjPrime \ TreeSequenceVertexSet Tn ∧
      exitPath.IsPath ∧
        (2 : ℕ) ≤ exitPath.length ∧
          (∀ y ∈ exitPath.support, y ∈ p.support) ∧
            (∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime,
                Sum.inl w ∈ exitPath.support ↔ w = u) ∧
              (∃
                  g ∈
                    BoundaryColorEdges G rho1
                      (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
                  Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
                ¬Incident G u fN := by
  classical
  intro V E _ _ _ G k e0 Tn TjPrime rho1 gammaN deltaN fN terminalSupport x p hpath hcomponent
      hterminalN htwoN hgammaBoundary hdeltaBoundary hfNterminal vertexSet eligible
      eligible_nonempty chosen u chosen_eq uSupport huSupport huVertex suffix exitPath
      suffix_path exit_path exit_support suffix_eligible_nonempty suffix_filter_last
      suffix_filter_singleton hu_terminal suffix_positive suffix_not_one suffix_length_two g hg v hv
  have hv_outside :=
    @helper_hv_outside_673 V E inferInstance inferInstance G k e0 Tn TjPrime rho1 gammaN
        deltaN terminalSupport x p u huSupport suffix_path suffix_filter_singleton
        suffix_length_two v hv
  have hgu : Incident G u g := by
    have ha := suffix.adj_getVert_succ (i := 0) (by omega)
    rw [suffix.getVert_zero, hg] at ha
    simpa [uSupport, TwoColorIncidenceGraph] using ha.1
  have hgv : Incident G v g := by
    have ha := suffix.adj_getVert_succ (i := 1) (by omega)
    rw [hg, hv] at ha
    simpa [TwoColorIncidenceGraph] using ha.1
  have huv : u ≠ v := by
    intro huv
    have hinj := suffix_path.getVert_injOn (by omega : 0 ≤ suffix.length)
      (by omega : 2 ≤ suffix.length)
      (show suffix.getVert 0 = suffix.getVert 2 by
        rw [suffix.getVert_zero, hv]
        exact congrArg Sum.inl huv)
    omega
  have hends : G.ends g = s(u, v) := by
    have ends_eq_of_mem : ∀ {z : Sym2 V} {a b : V}, a ∈ z → b ∈ z → a ≠ b → z = s(a,b) := by
      intro z a b ha hb hab
      induction z using Sym2.inductionOn with
      | _ c d =>
        simp only [Sym2.mem_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all []
    exact ends_eq_of_mem hgu hgv huv
  have hg_boundary : g ∈ BoundaryEdges G vertexSet := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, huVertex, v, hv_outside, hends⟩
  have hg_color : rho1 g = some gammaN ∨ rho1 g = some deltaN := by
    have ha := suffix.adj_getVert_succ (i := 0) (by omega)
    rw [suffix.getVert_zero, hg] at ha
    simpa [TwoColorIncidenceGraph] using ha.2
  have hg_gamma : rho1 g = some gammaN := by
    rcases hg_color with hg' | hg'
    · exact hg'
    · exfalso
      have hmem : g ∈ BoundaryColorEdges G rho1 vertexSet deltaN := by
        unfold BoundaryColorEdges
        simp only [Finset.mem_filter]
        exact ⟨hg_boundary, hg'⟩
      simp [vertexSet, hdeltaBoundary] at hmem
  have hg_colored_boundary : g ∈ BoundaryColorEdges G rho1 vertexSet gammaN := by
    unfold BoundaryColorEdges
    simp only [Finset.mem_filter]
    exact ⟨hg_boundary, hg_gamma⟩
  have hu_not_Tn :=
    @helper_hu_not_Tn_489 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 Tn TjPrime rho1 gammaN deltaN fN terminalSupport x p hterminalN hgammaBoundary
        hfNterminal eligible_nonempty u chosen_eq huSupport huVertex suffix_path exit_path
        exit_support suffix_eligible_nonempty suffix_filter_last suffix_filter_singleton
        hu_terminal suffix_positive suffix_not_one suffix_length_two g hg v hv hv_outside hgu hgv
        huv hends hg_boundary hg_color hg_gamma hg_colored_boundary
  refine ⟨u, exitPath, ?_, exit_path, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_sdiff]
    constructor
    · rcases Finset.mem_union.mp huVertex with h | h
      · exact False.elim (hu_not_Tn h)
      · exact h
    · exact hu_not_Tn
  · simpa [exitPath] using suffix_length_two
  · intro y hy
    have hy' : y ∈ suffix.support := by
      rw [exit_support] at hy
      exact List.mem_reverse.mp hy
    have hsuf : suffix.support <:+ p.support := by
      simpa [suffix] using p.support_dropUntil_suffix_support huSupport
    exact hsuf.subset hy'
  · exact @helper_branch_530 V E inferInstance inferInstance G k e0 Tn TjPrime rho1 gammaN deltaN
      terminalSupport x p u huSupport exit_support suffix_filter_singleton
  · refine ⟨g, ?_, hgu, ?_⟩
    · simpa [vertexSet] using hg_colored_boundary
    · rw [exit_support]
      apply List.mem_reverse.mpr
      apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      exact ⟨1, hg, by omega⟩
  have hf_boundary : fN ∈ BoundaryColorEdges G rho1
      (TreeSequenceVertexSet Tn) gammaN := by
    rw [hgammaBoundary]
    simp
  have hf_color : rho1 fN = some gammaN := by
    have hh := hf_boundary
    unfold BoundaryColorEdges at hh
    exact (Finset.mem_filter.mp hh).2
  have hf_adj : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Adj
      (Sum.inl terminalSupport) (Sum.inr fN) :=
    ⟨hfNterminal, Or.inl hf_color⟩
  have hf_support : Sum.inr fN ∈ p.support := by
    change Sum.inr fN ∈ {y : Sum V E | y ∈ p.support}
    rw [hcomponent]
    apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hf_adj).symm
  · exact @helper_branch_352 V E inferInstance inferInstance G k e0 Tn TjPrime rho1 gammaN deltaN
      fN terminalSupport x p hpath htwoN hfNterminal u huSupport suffix_filter_singleton
      hu_terminal v hu_not_Tn hf_support

theorem ExtensionBaseCaseTwoObservation21 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn TjPrime : TreeSequence G e0)
    (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (fN : E) (terminalSupport x : V)
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (hpath : p.IsPath)
    (hcomponent : {y : Sum V E | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hterminalN : terminalSupport ∈ TreeSequenceVertexSet Tn)
    (hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime)
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (htwoN : ∃ w ∈ TreeSequenceVertexSet Tn,
      w ≠ terminalSupport ∧ Sum.inl w ∈ p.support)
    (hgammaBoundary : BoundaryColorEdges G rho1
      (TreeSequenceVertexSet Tn) gammaN = {fN})
    (hdeltaBoundary : BoundaryColorEdges G rho1
      (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) deltaN = ∅)
    (hfNterminal : Incident G terminalSupport fN) :
    ∃ (u : V) (exitPath :
      (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)),
    u ∈ TreeSequenceVertexSet TjPrime \ TreeSequenceVertexSet Tn ∧
      exitPath.IsPath ∧
        2 ≤ exitPath.length ∧
          (∀ y : Sum V E, y ∈ exitPath.support → y ∈ p.support) ∧
            (∀ w : V,
                w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
                  (Sum.inl w ∈ exitPath.support ↔ w = u)) ∧
              (∃
                  g ∈
                    BoundaryColorEdges G rho1
                      (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
                  Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
                ¬Incident G u fN := by
  classical
  let : BEq (Sum V E) := instBEqOfDecidableEq
  let vertexSet := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime
  let eligible : List (Sum V E) := p.support.filter (fun z =>
    match z with
    | Sum.inl v => decide (v ∈ vertexSet)
    | Sum.inr _ => false)
  have eligible_nonempty : eligible ≠ [] := by
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨p.start_mem_support, by
      simp [vertexSet, hterminalN, hterminalPrime]⟩)
  let chosen : Sum V E := eligible.getLast eligible_nonempty
  have chosen_mem : chosen ∈ eligible := List.getLast_mem eligible_nonempty
  have chosen_pred := (List.mem_filter.mp chosen_mem).2
  have chosen_support : chosen ∈ p.support := List.mem_of_mem_filter chosen_mem
  obtain ⟨u, chosen_eq⟩ : ∃ u : V, chosen = Sum.inl u := by
    by_cases h : ∃ v : V, chosen = Sum.inl v
    · exact h
    · exfalso
      obtain ⟨e, he⟩ : ∃ e : E, chosen = Sum.inr e := by
        cases hc : chosen with
        | inl v => exact False.elim (h ⟨v, hc⟩)
        | inr e => exact ⟨e, rfl⟩
      rw [he] at chosen_pred
      exact False.elim (by simp at chosen_pred)
  let uSupport : Sum V E := Sum.inl u
  have huSupport : uSupport ∈ p.support := by simpa [uSupport, chosen_eq] using chosen_support
  have huVertex : u ∈ vertexSet := by
    rw [chosen_eq] at chosen_pred
    simpa [vertexSet] using chosen_pred
  have singleton_of_head_last :=
    @helper_singleton_of_head_last_580 V E
  let suffix := p.dropUntil uSupport huSupport
  let exitPath := suffix.reverse
  have suffix_path : suffix.IsPath := hpath.dropUntil huSupport
  have exit_path : exitPath.IsPath := suffix_path.reverse
  have exit_support : exitPath.support = suffix.support.reverse := by
    simp [exitPath, SimpleGraph.Walk.support_reverse]
  have suffix_eligible_nonempty :
      (suffix.support.filter (fun z => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false)) ≠ [] := by
    apply List.ne_nil_of_mem (a := uSupport)
    exact List.mem_filter.mpr ⟨suffix.start_mem_support, by simp [uSupport, huVertex]⟩
  have suffix_filter_last :
      (suffix.support.filter (fun z => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false)).getLast suffix_eligible_nonempty = uSupport := by
    have hsuf : suffix.support <:+ p.support := by
      simpa [suffix] using p.support_dropUntil_suffix_support huSupport
    have hfiltered := hsuf.filter (fun z => match z with
      | Sum.inl v => decide (v ∈ vertexSet)
      | Sum.inr _ => false)
    have heq := hfiltered.getLast suffix_eligible_nonempty
    convert heq using 1; simp [eligible, chosen, chosen_eq, uSupport]
  have suffix_filter_singleton :=
    @helper_suffix_filter_singleton_359 V E inferInstance inferInstance G k e0 Tn TjPrime
        rho1 gammaN deltaN terminalSupport x p u huSupport huVertex singleton_of_head_last
        suffix_path suffix_eligible_nonempty suffix_filter_last
  have hu_terminal :=
    @helper_hu_terminal_629 V E inferInstance inferInstance G k e0 Tn TjPrime rho1 gammaN
        deltaN terminalSupport x p htwoN eligible_nonempty u chosen_eq huSupport huVertex
        suffix_path exit_path exit_support suffix_eligible_nonempty suffix_filter_last
        suffix_filter_singleton
  have suffix_positive : 0 < suffix.length := by
    by_contra hz
    have hz0 : suffix.length = 0 := by omega
    have hux := SimpleGraph.Walk.eq_of_length_eq_zero hz0
    have : x = u := by simpa [uSupport] using hux.symm
    apply hxOutside
    rw [this]
    exact huVertex
  have suffix_not_one : suffix.length ≠ 1 := by
    intro hone
    have ha := suffix.adj_getVert_succ (i := 0) (by omega)
    have hzero : suffix.getVert 0 = Sum.inl u := by simp [uSupport]
    rw [hzero] at ha
    rw [show suffix.getVert 1 = suffix.getVert suffix.length by simp [hone]] at ha
    rw [suffix.getVert_length] at ha
    simp [TwoColorIncidenceGraph] at ha
  have suffix_length_two : 2 ≤ suffix.length := by omega
  have first_edge : ∃ g : E, suffix.getVert 1 = Sum.inr g := by
    have ha := suffix.adj_getVert_succ (i := 0) (by omega)
    cases hcase : suffix.getVert 1 with
    | inl v =>
        exfalso; rw [suffix.getVert_zero, hcase] at ha; simp [uSupport, TwoColorIncidenceGraph]
            at ha
    | inr g => exact ⟨g, rfl⟩
  obtain ⟨g, hg⟩ := first_edge
  have next_vertex : ∃ v : V, suffix.getVert 2 = Sum.inl v := by
    have ha := suffix.adj_getVert_succ (i := 1) (by omega)
    cases hcase : suffix.getVert 2 with
    | inl v => exact ⟨v, rfl⟩
    | inr e => exfalso; rw [hg, hcase] at ha; simp [TwoColorIncidenceGraph] at ha
  obtain ⟨v, hv⟩ := next_vertex
  exact @helper_continuation_847 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@Tn) (@TjPrime) (@rho1) (@gammaN) (@deltaN) (@fN) (@terminalSupport) (@x) (@p)
      (@hpath) (@hcomponent) (@hterminalN) (@htwoN) (@hgammaBoundary) (@hdeltaBoundary)
      (@hfNterminal) (@eligible_nonempty) (@u) (@chosen_eq) (@huSupport) (@huVertex)
      (@suffix_path) (@exit_path) (@exit_support) (@suffix_eligible_nonempty)
      (@suffix_filter_last) (@suffix_filter_singleton) (@hu_terminal) (@suffix_positive)
      (@suffix_not_one) (@suffix_length_two) (@g) (@hg) (@v) (@hv)
end GoldbergSeymour

end
