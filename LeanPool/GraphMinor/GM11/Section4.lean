/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Graph Minors XI, Section 4: slopes

This file proves results of Section 4 of Graph Minors XI on a drawing `Γ` with a slope `ins`:

- (4.2): the restriction of a slope to a subdrawing is a slope (`theorem_4_2`);
- (4.3)(i): if `C` is a circuit of a confined subdrawing `Γ'` with `ins(C)` maximal, every path of
  `Γ'` with both ends in `V(C)` lies in `ins(C)` (`theorem_4_3_i`). The proof takes a shortest
  counterexample and applies the second slope axiom, as in the paper.
- (4.3)(ii): `Γ'` does not capture a region incident with an edge of `C` and not in `ins(C)`
  (`theorem_4_3_ii`). The paper's "and so there are distinct vertices $a, b \in V(C \cap C')$" is
  the
  connectedness of a circuit minus a vertex (`isPreconnected_U_diff`).
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A closed disc is compact. -/
theorem _root_.GraphMinor.Surface.IsClosedDisc.isCompact {Δ : Set S} (h : IsClosedDisc Δ) :
    IsCompact Δ := by
  obtain ⟨f⟩ := h
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  have : CompactSpace Δ := f.compactSpace
  exact isCompact_iff_compactSpace.mpr this

/-- A closed disc in a Hausdorff space is closed. -/
theorem _root_.GraphMinor.Surface.IsClosedDisc.isClosed [T2Space S] {Δ : Set S}
    (h : IsClosedDisc Δ) : IsClosed Δ :=
  h.isCompact.isClosed

theorem subBd_eq_frontier' (X : Set S) : frontier X = subBd X := by
  rw [frontier_eq_closure_inter_closure, subBd, compl_eq_univ_sdiff]

theorem subBd_subset_of_isClosed {X : Set S} (hX : IsClosed X) : subBd X ⊆ X :=
  fun _ hx => hX.closure_subset_iff.mpr subset_rfl hx.1

variable [T2Space S]

/-- Graph Minors XI, (4.2) (page 79): "Let $\Gamma'$ be a subdrawing of $\Gamma$. Then the
restriction of $\text{ins}$ to the set
circuits of $\Gamma'$ of length $< 2\theta$ is a slope of order $\theta$ in $\Gamma'$." -/
theorem theorem_4_2_proof {Γ Γ' : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
  (hs : IsSlope Γ k ins)
    (hsub : Γ'.IsSubdrawing Γ) : IsSlope Γ' k ins where
  two_le := hs.two_le
  isClosedDisc C hC hCs hlen := hs.isClosedDisc C hC (hCs.trans hsub) hlen
  subBd_eq C hC hCs hlen := hs.subBd_eq C hC (hCs.trans hsub) hlen
  monotone C₁ C₂ h₁ h₁s hl₁ h₂ h₂s hl₂ hU :=
    hs.monotone C₁ C₂ h₁ (h₁s.trans hsub) hl₁ h₂ (h₂s.trans hsub) hl₂ hU
  three_paths P₀ P₁ P₂ a b h₀ h₁ h₂ h₀s h₁s h₂s l₀ l₁ l₂ i₀ i₁ i₂ d₀ d₁ d₂ c₀ c₁ c₂ := by
    have hsup : ∀ {P Q : Drawing S}, P.IsSubdrawing Γ' → Q.IsSubdrawing Γ' →
        Γ'.sup P Q = Γ.sup P Q := by
      intro P Q hP hQ
      apply Drawing.ext_of_V_E
      · rw [Drawing.sup_V hP hQ, Drawing.sup_V (hP.trans hsub) (hQ.trans hsub)]
      · rw [Drawing.sup_E hP hQ, Drawing.sup_E (hP.trans hsub) (hQ.trans hsub)]
    rw [hsup h₁s h₂s] at c₀ ⊢
    rw [hsup h₂s h₀s] at c₁ ⊢
    rw [hsup h₀s h₁s] at c₂ ⊢
    exact hs.three_paths P₀ P₁ P₂ a b h₀ h₁ h₂ (h₀s.trans hsub) (h₁s.trans hsub) (h₂s.trans hsub)
      l₀ l₁ l₂ i₀ i₁ i₂ d₀ d₁ d₂ c₀ c₁ c₂

/-- `U(C) ⊆ ins(C)`. -/
theorem IsSlope.U_subset_ins {Γ : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ k ins) {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ)
    (hlen : C.length < k) : C.U ⊆ ins C := by
  rw [← hs.subBd_eq C hC hCs hlen]
  exact subBd_subset_of_isClosed (hs.isClosedDisc C hC hCs hlen).isClosed

omit [T2Space S] in
theorem isSimple_of_append {Γ : Drawing S} {a x b : S} {W₁ : GraphWalk Γ.toGraph a x}
    {W₂ : GraphWalk Γ.toGraph x b} (h : (W₁.append W₂).IsSimple) :
    W₁.IsSimple ∧ W₂.IsSimple :=
  GraphWalk.simple_parts_of_append h

omit [T2Space S] in
theorem exists_split_edge {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) {e : Set S}
    (he : e ∈ W.edges) :
    ∃ (x y : S) (W₁ : GraphWalk Γ.toGraph a x) (h : Γ.toGraph.IsLink e x y)
      (W₂ : GraphWalk Γ.toGraph y b), W = W₁.append (.cons h W₂) := by
  obtain ⟨x, y, h, W₁, W₂, heq⟩ := W.split_at_edge he
  exact ⟨x, y, W₁, h, W₂, heq⟩

omit [TopologicalSpace S] [T2Space S] in
theorem support_of_length_zero {G : Graph S (Set S)} {a b : S} {W : GraphWalk G a b}
    (h : W.length = 0) : W.support = [a] ∧ W.edges = [] := by
  cases W with
  | nil _ => exact ⟨rfl, rfl⟩
  | cons h' r => simp at h

/-- Under the setting of (4.3)(i), a simple walk with its ends in `C` and an edge in `C` is that
edge, so it lies in `U(C)`. -/
private theorem walk_subset_of_common_edge {C Γ' : Drawing S} (hCs : C.IsSubdrawing Γ') {a b : S}
    (W : GraphWalk Γ'.toGraph a b) (hW : W.IsSimple) (ha : a ∈ C.V) (hb : b ∈ C.V)
    (hint : ∀ x ∈ W.support, x ∈ C.V → x = a ∨ x = b) {e : Set S} (he : e ∈ W.edges)
    (heC : e ∈ C.E) : (walkDrawing Γ' W).U ⊆ C.U := by
  obtain ⟨x, y, W₁, h, W₂, rfl⟩ := exists_split_edge W he
  have hs := isSimple_of_append hW
  have hsplit : ((W₁.support ++ (GraphWalk.cons h W₂).support.tail).Nodup) := by
    have h' : (W₁.append (GraphWalk.cons h W₂)).support.Nodup := hW
    rwa [GraphWalk.support_append] at h'
  have hd := List.nodup_append.mp hsplit
  have hyneW₁ : y ∉ W₁.support := fun hy => hd.2.2 y hy y W₂.start_mem_support rfl
  have hbneW₁ : b ∉ W₁.support := fun hy => hd.2.2 b hy b W₂.end_mem_support rfl
  have haneW₂ : a ∉ W₂.support := fun hy => hd.2.2 a W₁.start_mem_support a hy rfl
  have hlC : C.toGraph.IsLink e x y := (hCs.isLink_iff heC).mpr h
  have hxC : x ∈ C.V := hlC.2.1
  have hyC : y ∈ C.V := hlC.2.2.1
  have hxW : x ∈ (W₁.append (GraphWalk.cons h W₂)).support :=
    (GraphWalk.mem_support_append _ _).mpr (Or.inl W₁.end_mem_support)
  have hyW : y ∈ (W₁.append (GraphWalk.cons h W₂)).support :=
    (GraphWalk.mem_support_append _ _).mpr (Or.inr (by simp [W₂.start_mem_support]))
  have hxa : x = a := (hint x hxW hxC).resolve_right fun hxb => hbneW₁ (hxb ▸ W₁.end_mem_support)
  have hyb : y = b := (hint y hyW hyC).resolve_left fun hya => haneW₂ (hya ▸ W₂.start_mem_support)
  subst hxa hyb
  have h₁ := support_of_length_zero hs.1.length_eq_zero
  have hs₂ : W₂.IsSimple := hs.2.of_cons
  have h₂ := support_of_length_zero hs₂.length_eq_zero
  intro z hz
  rw [mem_walkDrawing_U] at hz
  rcases hz with hz | ⟨f, hf, hz⟩
  · rw [GraphWalk.support_append, h₁.1] at hz
    simp only [GraphWalk.support_cons, List.tail_cons, h₂.1] at hz
    rw [C.U_eq]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hxC
    · exact Or.inl hyC
  · rw [GraphWalk.edges_append, h₁.2] at hf
    simp only [GraphWalk.edges_cons, h₂.2, List.nil_append, List.mem_singleton] at hf
    subst hf
    rw [C.U_eq]
    exact Or.inr (mem_iUnion₂.mpr ⟨f, heC, hz⟩)

/-- Graph Minors XI, (4.3)(i) (page 79):
"(4.3) *Let $\Gamma'$ be a confined subdrawing of $\Gamma$, and let $C$ be a circuit of $\Gamma'$
with $\text{ins}(C)$ maximal. Then* (i) $U(P) \subseteq \text{ins}(C)$ *for every path $P$ of
$\Gamma'$ with both ends in $V(C)$,*" The path is given as a simple walk. -/
theorem theorem_4_3_i {Γ Γ' C : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ k ins) (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ')
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ')
    (hmax : ∀ C' : Drawing S, C'.IsCircuit → C'.IsSubdrawing Γ' → ins C ⊆ ins C' → ins C' ⊆ ins C)
    {a b : S} (W : GraphWalk Γ'.toGraph a b) (hW : W.IsSimple) (ha : a ∈ C.V) (hb : b ∈ C.V) :
    (walkDrawing Γ' W).U ⊆ ins C := by
  have hs' := theorem_4_2_proof hs hsub
  have hCl := hconf C hC hCs
  have hUC := hs'.U_subset_ins hC hCs hCl
  -- Induction on the length gives the minimal counterexample of the paper.
  induction hn : W.length using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    by_cases hint : ∃ x ∈ W.support, x ∈ C.V ∧ x ≠ a ∧ x ≠ b
    · -- An internal vertex in `C` splits the walk into two shorter walks.
      obtain ⟨x, hx, hxC, hxa, hxb⟩ := hint
      obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hx
      have hsp := isSimple_of_append hW
      have hl₁ : W₁.length ≠ 0 := fun h => hxa (GraphWalk.eq_of_length_eq_zero h).symm
      have hl₂ : W₂.length ≠ 0 := fun h => hxb (GraphWalk.eq_of_length_eq_zero h)
      rw [GraphWalk.length_append] at hn
      have i₁ := ih W₁.length (by omega) W₁ hsp.1 ha hxC rfl
      have i₂ := ih W₂.length (by omega) W₂ hsp.2 hxC hb rfl
      intro z hz
      rw [mem_walkDrawing_U] at hz
      rcases hz with hz | ⟨f, hf, hz⟩
      · rcases (GraphWalk.mem_support_append _ _).mp hz with hz | hz
        · exact i₁ ((mem_walkDrawing_U _ _).mpr (Or.inl hz))
        · exact i₂ ((mem_walkDrawing_U _ _).mpr (Or.inl hz))
      · rw [GraphWalk.edges_append, List.mem_append] at hf
        rcases hf with hf | hf
        · exact i₁ ((mem_walkDrawing_U _ _).mpr (Or.inr ⟨f, hf, hz⟩))
        · exact i₂ ((mem_walkDrawing_U _ _).mpr (Or.inr ⟨f, hf, hz⟩))
    · have hint' : ∀ x ∈ W.support, x ∈ C.V → x = a ∨ x = b := by
        intro x hx hxC
        by_contra hcon
        push Not at hcon
        exact hint ⟨x, hx, hxC, hcon.1, hcon.2⟩
      by_cases hab : a = b
      · subst hab
        have h₀ := support_of_length_zero hW.length_eq_zero
        intro z hz
        rw [mem_walkDrawing_U, h₀.1, h₀.2] at hz
        simp only [List.mem_singleton, List.not_mem_nil, false_and, exists_false, or_false] at hz
        subst hz
        exact hUC (C.V_subset_U ha)
      by_cases hedge : ∃ e ∈ W.edges, e ∈ C.E
      · obtain ⟨e, he, heC⟩ := hedge
        exact (walk_subset_of_common_edge hCs W hW ha hb hint' he heC).trans hUC
      -- Now `P`, `P₁`, `P₂` are three paths to which the second slope axiom applies.
      obtain ⟨P₁, P₂, hP₁, hP₂, hP₁s, hP₂s, hl₁, hl₂, hV₁₂, hE₁₂, hsupC⟩
        := hC.exists_two_paths ha hb hab
      set P := walkDrawing Γ' W with hPdef
      have hPs : P.IsSubdrawing Γ' := walkDrawing_isSubdrawing Γ' W
      have hP : P.IsPathBetween a b := walkDrawing_isPathBetween Γ' hW
      have hP₁' := hP₁s.trans hCs
      have hP₂' := hP₂s.trans hCs
      have habV : a ∈ P₁.V ∩ P₂.V ∧ b ∈ P₁.V ∩ P₂.V := by rw [hV₁₂]; simp
      have hPlen : 0 < P.length := by
        have hne : W.edges ≠ [] := by
          intro h
          have : W.length = 0 := by simp [GraphWalk.length, h]
          exact hab (GraphWalk.eq_of_length_eq_zero this)
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
        have heP : e ∈ P.E := by
          rw [hPdef, walkDrawing_E]
          exact he
        exact Set.ncard_pos P.finite_edges |>.mpr ⟨e, heP⟩
      have hVP : ∀ {Q : Drawing S}, Q.IsSubdrawing C → a ∈ Q.V → b ∈ Q.V → P.V ∩ Q.V = {a, b} := by
        intro Q hQ haQ hbQ
        ext x
        constructor
        · rintro ⟨hxP, hxQ⟩
          rw [hPdef, walkDrawing_V] at hxP
          exact hint' x hxP (hQ.1 hxQ)
        · rintro (rfl | hx)
          · refine ⟨?_, haQ⟩
            rw [hPdef, walkDrawing_V]
            exact W.start_mem_support
          · rw [mem_singleton_iff.mp hx]
            refine ⟨?_, hbQ⟩
            rw [hPdef, walkDrawing_V]
            exact W.end_mem_support
      have hEP : ∀ {Q : Drawing S}, Q.IsSubdrawing C → Disjoint P.E Q.E := by
        intro Q hQ
        refine disjoint_left.mpr fun e he heQ => hedge ⟨e, ?_, hQ.2 heQ⟩
        rw [hPdef, walkDrawing_E] at he
        exact he
      have hV01 := hVP hP₁s habV.1.1 habV.2.1
      have hV02 := hVP hP₂s habV.1.2 habV.2.2
      have hsupC' : Γ'.sup P₁ P₂ = C := by
        rw [← hsupC]
        apply Drawing.ext_of_V_E
        · rw [Drawing.sup_V hP₁' hP₂', Drawing.sup_V hP₁s hP₂s]
        · rw [Drawing.sup_E hP₁' hP₂', Drawing.sup_E hP₁s hP₂s]
      -- The circuits `P ∪ P₁` and `P₂ ∪ P`.
      have hc₁ : (Γ'.sup P P₁).IsCircuit := Drawing.isCircuit_sup hP hP₁ hPs hP₁' hab hV01
        (hEP hP₁s)
      have hc₂ : (Γ'.sup P₂ P).IsCircuit :=
        Drawing.isCircuit_sup hP₂ hP hP₂' hPs hab (by rw [inter_comm]; exact hV02)
          (hEP hP₂s).symm
      have hc₁s := Drawing.sup_isSubdrawing Γ' P P₁
      have hc₂s := Drawing.sup_isSubdrawing Γ' P₂ P
      have hl₁' := hconf _ hc₁ hc₁s
      have hl₂' := hconf _ hc₂ hc₂s
      have hUP₁ : P.U ⊆ ins (Γ'.sup P P₁) :=
        ((Drawing.le_sup_left hPs hP₁').U_subset).trans (hs'.U_subset_ins hc₁ hc₁s hl₁')
      have hUP₂ : P.U ⊆ ins (Γ'.sup P₂ P) :=
        ((Drawing.le_sup_right hP₂' hPs).U_subset).trans (hs'.U_subset_ins hc₂ hc₂s hl₂')
      have h3 := hs'.three_paths P P₁ P₂ a b hP hP₁ hP₂ hPs hP₁' hP₂' hPlen hl₁ hl₂ hV01 hV₁₂
        (by rw [inter_comm]; exact hV02) (hEP hP₁s) hE₁₂ (hEP hP₂s).symm
        (by rw [hsupC']; exact hCl) hl₂' hl₁'
      rw [hsupC'] at h3
      rcases h3 with ⟨h, -⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
      · exact hUP₂.trans h
      · exact hUP₂.trans (hmax _ hc₂ hc₂s h)
      · exact hUP₁.trans (hmax _ hc₁ hc₁s h)

omit [T2Space S] in
/-- A circuit can be read as a simple-closed walk from any of its vertices. -/
theorem exists_walk_at {C : Drawing S} (hC : C.IsCircuit) {v : S} (hv : v ∈ C.V) :
    ∃ W : GraphWalk C.toGraph v v, W.IsSimpleClosed ∧ 0 < W.length ∧
      C.V = {x | x ∈ W.support} ∧ C.E = {e | e ∈ W.edges} := by
  obtain ⟨u, W, ⟨hnd, hed⟩, hpos, hV, hE⟩ := hC
  rw [hV] at hv
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hv
  refine ⟨W₂.append W₁, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h1 : (W₁.append W₂).support.tail = W₁.support.tail ++ W₂.support.tail := by
      rw [GraphWalk.support_append, W₁.support_eq_cons]; simp
    have h2 : (W₂.append W₁).support.tail = W₂.support.tail ++ W₁.support.tail := by
      rw [GraphWalk.support_append, W₂.support_eq_cons]; simp
    rw [h2]
    rw [h1] at hnd
    exact (List.perm_append_comm.nodup_iff).mp hnd
  · rw [GraphWalk.edges_append]
    rw [GraphWalk.edges_append] at hed
    exact (List.perm_append_comm.nodup_iff).mp hed
  · rw [GraphWalk.length_append] at hpos ⊢
    omega
  · rw [hV]
    ext x
    simp only [mem_ofPred_eq, GraphWalk.mem_support_append, or_comm]
  · rw [hE]
    ext e
    simp only [mem_ofPred_eq, GraphWalk.edges_append, List.mem_append, or_comm]

omit [T2Space S] in
/-- The closure of an edge minus a point is preconnected. -/
private theorem isPreconnected_closure_diff (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) {v : S}
    (hv : v ∈ Γ.V) : IsPreconnected (closure e \ {v}) := by
  have h₁ : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  refine h₁.subset_closure (fun x hx => ⟨subset_closure hx, ?_⟩) sdiff_subset
  rintro rfl
  exact (he.2.1 hx).2 hv

omit [T2Space S] in
/-- For a simple walk ending in `v`, its point set minus `v` is preconnected. -/
private theorem isPreconnected_walk_diff (Γ : Drawing S) {a v : S} (hv : v ∈ Γ.V)
    (W : GraphWalk Γ.toGraph a v) (hW : W.IsSimple) :
    IsPreconnected ({x | x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e} \ {v}) := by
  induction W with
  | nil h =>
    convert isPreconnected_empty using 1
    ext x
    simp
  | @cons u w v e h r ih =>
    have hr := hW.of_cons
    have hu : u ≠ v := fun huv => (List.nodup_cons.mp hW).1 (huv ▸ r.end_mem_support)
    have hEq : {x | x ∈ (GraphWalk.cons h r).support ∨ ∃ e' ∈ (GraphWalk.cons h r).edges,
        x ∈ closure e'} \ {v} = (closure e \ {v}) ∪
          ({x | x ∈ r.support ∨ ∃ e' ∈ r.edges, x ∈ closure e'} \ {v}) := by
      have hul : u ∈ closure e := by
        have : u ∈ closure e ∩ Γ.V := by rw [h.2.2.2]; simp
        exact this.1
      ext x
      simp only [GraphWalk.support_cons, GraphWalk.edges_cons, List.mem_cons, mem_sdiff,
        mem_ofPred_eq,
        mem_singleton_iff, mem_union, exists_eq_or_imp]
      constructor
      · rintro ⟨(h1 | h1) | (h1 | h1), hx⟩
        · exact Or.inl ⟨h1 ▸ hul, hx⟩
        · exact Or.inr ⟨Or.inl h1, hx⟩
        · exact Or.inl ⟨h1, hx⟩
        · exact Or.inr ⟨Or.inr h1, hx⟩
      · rintro (⟨h1, hx⟩ | ⟨h1 | h1, hx⟩)
        · exact ⟨Or.inr (Or.inl h1), hx⟩
        · exact ⟨Or.inl (Or.inr h1), hx⟩
        · exact ⟨Or.inr (Or.inr h1), hx⟩
    rw [hEq]
    by_cases hwv : w = v
    · subst hwv
      have h₀ := support_of_length_zero hr.length_eq_zero
      have hsmall : {x | x ∈ r.support ∨ ∃ e' ∈ r.edges, x ∈ closure e'} \ {w} = ∅ := by
        ext x
        simp [h₀.1, h₀.2]
      rw [hsmall, union_empty]
      exact isPreconnected_closure_diff Γ h.1 hv
    · refine IsPreconnected.union w ⟨?_, hwv⟩ ⟨Or.inl r.start_mem_support, hwv⟩
        (isPreconnected_closure_diff Γ h.1 hv) (ih hv hr)
      have : w ∈ closure e ∩ Γ.V := by rw [h.2.2.2]; simp
      exact this.1

omit [T2Space S] in
/-- A circuit minus one of its vertices is preconnected. -/
theorem isPreconnected_U_diff {C : Drawing S} (hC : C.IsCircuit) {v : S} (hv : v ∈ C.V) :
    IsPreconnected (C.U \ {v}) := by
  obtain ⟨W, ⟨hnd, -⟩, hpos, hV, hE⟩ := exists_walk_at hC hv
  have hU : C.U = {x | x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e} := by
    rw [C.U_eq, hV, hE]
    ext x
    simp
  rw [hU]
  cases W with
  | nil _ => simp at hpos
  | @cons _ w _ e h r =>
    have hr : r.IsSimple := by simpa [GraphWalk.IsSimple] using hnd
    have hEq : {x | x ∈ (GraphWalk.cons h r).support ∨ ∃ e' ∈ (GraphWalk.cons h r).edges,
        x ∈ closure e'} \ {v} = (closure e \ {v}) ∪
          ({x | x ∈ r.support ∨ ∃ e' ∈ r.edges, x ∈ closure e'} \ {v}) := by
      ext x
      simp only [GraphWalk.support_cons, GraphWalk.edges_cons, List.mem_cons, mem_sdiff,
        mem_ofPred_eq,
        mem_singleton_iff, mem_union, exists_eq_or_imp]
      constructor
      · rintro ⟨(h1 | h1) | (h1 | h1), hx⟩
        · exact absurd h1 hx
        · exact Or.inr ⟨Or.inl h1, hx⟩
        · exact Or.inl ⟨h1, hx⟩
        · exact Or.inr ⟨Or.inr h1, hx⟩
      · rintro (⟨h1, hx⟩ | ⟨h1 | h1, hx⟩)
        · exact ⟨Or.inr (Or.inl h1), hx⟩
        · exact ⟨Or.inl (Or.inr h1), hx⟩
        · exact ⟨Or.inr (Or.inr h1), hx⟩
    rw [hEq]
    by_cases hwv : w = v
    · subst hwv
      have h₀ := support_of_length_zero hr.length_eq_zero
      have hsmall : {x | x ∈ r.support ∨ ∃ e' ∈ r.edges, x ∈ closure e'} \ {w} = ∅ := by
        ext x
        simp [h₀.1, h₀.2]
      rw [hsmall, union_empty]
      exact isPreconnected_closure_diff C h.1 hv
    · refine IsPreconnected.union w ⟨?_, hwv⟩ ⟨Or.inl r.start_mem_support, hwv⟩
        (isPreconnected_closure_diff C h.1 hv) (isPreconnected_walk_diff C hv r hr)
      have : w ∈ closure e ∩ C.V := by rw [h.2.2.2]; simp
      exact this.1

omit [T2Space S] in
/-- A circuit with a loop consists of that loop. -/
theorem IsCircuit.E_eq_of_loop {C : Drawing S} (hC : C.IsCircuit) {f : Set S} (hf : f ∈ C.E)
    {v : S} (hl : closure f ∩ C.V = {v}) : C.E = {f} := by
  have hv : v ∈ C.V := by
    have : v ∈ closure f ∩ C.V := by rw [hl]; simp
    exact this.2
  obtain ⟨W, ⟨hnd, hed⟩, hpos, hV, hE⟩ := exists_walk_at hC hv
  have hloop : C.toGraph.IsLink f v v := ⟨hf, hv, hv, by simpa using hl⟩
  cases W with
  | nil _ => simp at hpos
  | @cons _ w _ e h r =>
    have hr : r.IsSimple := by simpa [GraphWalk.IsSimple] using hnd
    have hfr : f ∉ r.edges := by
      intro hfr
      obtain ⟨x, y, R₁, h', R₂, rfl⟩ := exists_split_edge r hfr
      have hxv : x = v := by
        have : x ∈ closure f ∩ C.V := by rw [h'.2.2.2]; simp
        rw [hl] at this
        exact this
      have hyv : y = v := by
        have : y ∈ closure f ∩ C.V := by rw [h'.2.2.2]; simp
        rw [hl] at this
        exact this
      subst hxv
      obtain rfl := hyv
      have hsplit : ((R₁.support ++ (GraphWalk.cons h' R₂).support.tail).Nodup) := by
        have h'' : (R₁.append (GraphWalk.cons h' R₂)).support.Nodup := hr
        rwa [GraphWalk.support_append] at h''
      have hd := List.nodup_append.mp hsplit
      exact hd.2.2 y R₁.end_mem_support y R₂.start_mem_support rfl
    have hfe : e = f := by
      have hmem : f ∈ (GraphWalk.cons h r).edges := by
        rw [hE] at hf
        exact hf
      rcases List.mem_cons.mp hmem with h1 | h1
      · exact h1.symm
      · exact absurd h1 hfr
    subst hfe
    have hwv : w = v := by
      have : w ∈ closure e ∩ C.V := by rw [h.2.2.2]; simp
      rw [hl] at this
      exact this
    subst hwv
    have h₀ := support_of_length_zero hr.length_eq_zero
    rw [hE]
    ext x
    simp [h₀.2]

/-- `U(P) ⊆ X` for a path given by a simple walk of `Γ'`. -/
theorem path_U_subset {Γ' P : Drawing S} {a b : S} (hP : P.IsPathBetween a b)
    (hPs : P.IsSubdrawing Γ') {X : Set S}
    (h : ∀ {W : GraphWalk Γ'.toGraph a b}, W.IsSimple → (walkDrawing Γ' W).U ⊆ X) : P.U ⊆ X := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  obtain ⟨W', hs, he⟩ := hPs.exists_walk_up W
  have hsimple : W'.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hs]
    exact hW
  refine subset_trans ?_ (h hsimple)
  intro z hz
  rw [mem_walkDrawing_U, hs, he]
  rw [P.U_eq, hV, hE] at hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · obtain ⟨e, he', hz⟩ := mem_iUnion₂.mp hz
    exact Or.inr ⟨e, he', hz⟩

/-- Graph Minors XI, (4.3)(ii) (page 79): for every edge `e` of `C`, `Γ'` does not capture the
region
of `Γ` incident with `e` not included in `ins(C)`. -/
theorem theorem_4_3_ii {Γ Γ' C : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ k ins) (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ')
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ')
    (hmax : ∀ C' : Drawing S, C'.IsCircuit → C'.IsSubdrawing Γ' → ins C ⊆ ins C' → ins C' ⊆ ins C)
    {e r : Set S} (he : e ∈ C.E) (hinc : (e ∩ closure r).Nonempty) (hnot : ¬ r ⊆ ins C) :
    ¬ Captures ins k Γ' r := by
  rintro ⟨C', hC', hC's, hl', hr⟩
  have hs' := theorem_4_2_proof hs hsub
  have hCl := hconf C hC hCs
  have hclosed' : IsClosed (ins C') := (hs'.isClosedDisc C' hC' hC's hl').isClosed
  have hUC' := hs'.U_subset_ins hC' hC's hl'
  obtain ⟨x, hxe, hxr⟩ := hinc
  have hxin : x ∈ ins C' := hclosed'.closure_subset_iff.mpr hr hxr
  by_cases hUU : C.U ⊆ ins C'
  · exact hnot (hr.trans (hmax C' hC' hC's (hs'.monotone C C' hC hCs hCl hC' hC's hl' hUU)))
  obtain ⟨y, hyC, hyout⟩ := not_subset.mp hUU
  -- Two distinct common vertices finish the proof, by (4.3)(i).
  have hdone : ∀ a b : S, a ∈ C.V → a ∈ C'.V → b ∈ C.V → b ∈ C'.V → a ≠ b → False := by
    intro a b haC haC' hbC hbC' hab
    obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, -, -, hsup⟩ := hC'.exists_two_paths haC' hbC' hab
    have hP' : P.U ⊆ ins C := path_U_subset hP (hPs.trans hC's) fun hW =>
      theorem_4_3_i hs hsub hconf hC hCs hmax _ hW haC hbC
    have hQ' : Q.U ⊆ ins C := path_U_subset hQ (hQs.trans hC's) fun hW =>
      theorem_4_3_i hs hsub hconf hC hCs hmax _ hW haC hbC
    have hU : C'.U ⊆ ins C := by
      rw [← hsup]
      intro z hz
      rw [Drawing.U_eq, Drawing.sup_V hPs hQs, Drawing.sup_E hPs hQs] at hz
      rcases hz with (hz | hz) | hz
      · exact hP' (P.V_subset_U hz)
      · exact hQ' (Q.V_subset_U hz)
      · obtain ⟨f, hf | hf, hz⟩ := mem_iUnion₂.mp hz
        · exact hP' (P.closure_subset_U hf hz)
        · exact hQ' (Q.closure_subset_U hf hz)
    exact hnot (hr.trans (hs'.monotone C' C hC' hC's hl' hC hCs hCl hU))
  -- A common edge gives two common vertices, unless it is a loop.
  have hnoedge : ∀ f, f ∈ C.E → f ∉ C'.E := by
    intro f hf hf'
    obtain ⟨p, q, hpq⟩ := (C.toGraph.edge_mem_iff_exists_isLink f).mp hf
    have hlC' : C'.toGraph.IsLink f p q :=
      ((hC's.isLink_iff hf').mpr ((hCs.isLink_iff hf).mp hpq))
    by_cases hpqe : p = q
    · subst hpqe
      have hl₁ : closure f ∩ C.V = {p} := by simpa using hpq.2.2.2
      have hl₂ : closure f ∩ C'.V = {p} := by simpa using hlC'.2.2.2
      have hE₁ := IsCircuit.E_eq_of_loop hC hf hl₁
      have hE₂ := IsCircuit.E_eq_of_loop hC' hf' hl₂
      apply hUU
      have hUeq : C.U ⊆ C'.U := by
        rw [C.U_eq, C'.U_eq, hE₁, hE₂]
        refine union_subset_union ?_ subset_rfl
        intro z hz
        have hzc : z ∈ C.U := C.V_subset_U hz
        have hzz : z = p := by
          by_contra hzp
          have hzE : ∃ e' ∈ C.E, z ∈ e' ∨ True := by
            exact ⟨f, hf, Or.inr trivial⟩
          -- `z` is a vertex of the circuit, whose only edge is `f`.
          obtain ⟨u, W, -, hpos, hV, hE⟩ := hC
          have hzW : z ∈ W.support := by rw [hV] at hz; exact hz
          have hedges : ∀ e' ∈ W.edges, e' = f := by
            intro e' he'
            have : e' ∈ C.E := by rw [hE]; exact he'
            rw [hE₁] at this
            exact this
          have hall : ∀ w ∈ W.support, w = p := by
            have hgen : ∀ {a b : S} (R : GraphWalk C.toGraph a b), (∀ e' ∈ R.edges, e' = f) →
                0 < R.length → ∀ w ∈ R.support, w = p := by
              intro a b R
              induction R with
              | nil _ => simp
              | @cons u' v' w' e' h' R' ih =>
                intro hed _ w hw
                have hee : e' = f := hed _ (by simp)
                subst hee
                have huu : u' = p := by
                  have : u' ∈ closure e' ∩ C.V := by rw [h'.2.2.2]; simp
                  rw [hl₁] at this
                  exact this
                have hvv : v' = p := by
                  have : v' ∈ closure e' ∩ C.V := by rw [h'.2.2.2]; simp
                  rw [hl₁] at this
                  exact this
                rcases List.mem_cons.mp hw with rfl | hw
                · exact huu
                · cases R' with
                  | nil _ =>
                    simp only [GraphWalk.support_nil, List.mem_singleton] at hw
                    exact hw.trans hvv
                  | cons h'' R'' =>
                    exact ih (fun e'' he'' => hed e'' (List.mem_cons_of_mem _ he'')) (by simp) w hw
            exact hgen W hedges hpos
          exact hzp (hall z hzW)
        rw [hzz]
        have : p ∈ closure f ∩ C'.V := by rw [hl₂]; simp
        exact this.2
      exact hUeq.trans hUC'
    · exact hdone p q hpq.2.1 hlC'.2.1 hpq.2.2.1 hlC'.2.2.1 hpqe
  -- The set `T`: `U(C)` minus the common vertex, if any.
  have hsep : ∀ T : Set S, IsPreconnected T → T ⊆ C.U → x ∈ T → y ∈ T →
      (∀ z ∈ T, z ∈ C.V → z ∉ C'.V) → False := by
    intro T hT hTC hxT hyT hTV
    have hnon : (T ∩ frontier (ins C')).Nonempty := by
      by_contra hcon
      have hcon' : ∀ z ∈ T, z ∉ frontier (ins C') := fun z hz hzf => hcon ⟨z, hz, hzf⟩
      have hcov : T ⊆ interior (ins C') ∪ (ins C')ᶜ := by
        intro z hz
        by_cases hzin : z ∈ ins C'
        · refine Or.inl ?_
          by_contra hzi
          exact hcon' z hz ⟨subset_closure hzin, hzi⟩
        · exact Or.inr hzin
      have hxi : x ∈ interior (ins C') := by
        by_contra hxi
        exact hcon' x hxT ⟨subset_closure hxin, hxi⟩
      obtain ⟨z, -, hz₁, hz₂⟩ := hT _ _ isOpen_interior hclosed'.isOpen_compl hcov ⟨x, hxT, hxi⟩
        ⟨y, hyT, hyout⟩
      exact hz₂ (interior_subset hz₁)
    obtain ⟨z, hzT, hzf⟩ := hnon
    rw [subBd_eq_frontier', hs'.subBd_eq C' hC' hC's hl'] at hzf
    have hzC := hTC hzT
    by_cases hzV : z ∈ C.V
    · have hzV' : z ∉ C'.V := hTV z hzT hzV
      obtain ⟨f, hf, hzf'⟩ := C'.exists_edge_of_mem hzf hzV'
      exact (((hC's.trans hsub).2 hf).2.1 hzf').2 ((hCs.trans hsub).1 hzV)
    · obtain ⟨g, hg, hzg⟩ := C.exists_edge_of_mem hzC hzV
      by_cases hzV' : z ∈ C'.V
      · exact (((hCs.trans hsub).2 hg).2.1 hzg).2 ((hC's.trans hsub).1 hzV')
      · obtain ⟨f, hf, hzf'⟩ := C'.exists_edge_of_mem hzf hzV'
        have hgf := Γ.edge_eq_of_mem ((hCs.trans hsub).2 hg) ((hC's.trans hsub).2 hf) hzg hzf'
        exact hnoedge g hg (hgf ▸ hf)
  have hxV : x ∉ Γ.V := ((hCs.trans hsub).2 he).2.1 hxe |>.2
  have hxC : x ∈ C.U := C.closure_subset_U he (subset_closure hxe)
  by_cases hcom : ∃ v, v ∈ C.V ∧ v ∈ C'.V
  · obtain ⟨v, hvC, hvC'⟩ := hcom
    have huniq : ∀ z, z ∈ C.V → z ∈ C'.V → z = v := by
      intro z hz hz'
      by_contra hne
      exact hdone z v hz hz' hvC hvC' hne
    refine hsep (C.U \ {v}) (isPreconnected_U_diff hC hvC) sdiff_subset ⟨hxC, ?_⟩ ⟨hyC, ?_⟩ ?_
    · rintro rfl
      exact hxV ((hCs.trans hsub).1 hvC)
    · rintro rfl
      exact hyout (hUC' (C'.V_subset_U hvC'))
    · intro z hz hzC hzC'
      exact hz.2 (huniq z hzC hzC')
  · obtain ⟨v, hv⟩ : C.V.Nonempty := by
      obtain ⟨u, W, -, -, hV, -⟩ := hC
      exact ⟨u, by rw [hV]; exact W.start_mem_support⟩
    have hprec : IsPreconnected (C.U \ {v}) := isPreconnected_U_diff hC hv
    have hclo : C.U ⊆ closure (C.U \ {v}) := by
      intro z hz
      by_cases hzv : z = v
      · subst hzv
        obtain ⟨W, -, hpos, hV, hE⟩ := exists_walk_at hC hv
        cases W with
        | nil _ => simp at hpos
        | @cons _ w _ e' h r =>
          have he' : e' ∈ C.E := h.1
          have hzc : z ∈ closure e' := by
            have : z ∈ closure e' ∩ C.V := by rw [h.2.2.2]; simp
            exact this.1
          have hsubs : e' ⊆ C.U \ {z} := by
            intro q hq
            refine ⟨C.closure_subset_U he' (subset_closure hq), ?_⟩
            rintro rfl
            exact (he'.2.1 hq).2 hv
          exact closure_mono hsubs hzc
      · exact subset_closure ⟨hz, hzv⟩
    exact hsep C.U (hprec.subset_closure sdiff_subset hclo) subset_rfl hxC hyC
      fun z _ hz hz' => hcom ⟨z, hz, hz'⟩

end GraphMinor.GM11
