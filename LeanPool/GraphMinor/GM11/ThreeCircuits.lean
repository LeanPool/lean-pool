/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rings

/-!
# Three circuits whose edges cover each other twice

At the end of the proof of (5.4) in Graph Minors XI we have three circuits `C₁, C₂, C₃` with
`E(C₃) = E(C₁) △ E(C₂)`, and we know that they are the only circuits of length `< 2θ` inside
`C₁ ∪ C₂`. Here we show that then `C₁ ∪ C₂` is three paths with the same ends (`exists_theta`), so
that the second slope axiom applies. This file is pure graph theory.

The proof looks at a piece `S` of `C₁`, called an *ear*, that meets `C₂` only in its ends. If some
edge of `C₁` outside `C₂` is not in `S`, then there are two disjoint ears, one of them has at most
half the length of `C₁`, and with the shorter of the two pieces of `C₂` between its ends it forms a
short circuit that is none of `C₁, C₂, C₃`. So there is one ear `S` and the rest of `C₁` lies in
`C₂`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] {Γ : Drawing S}

/-- The ends of an edge of a walk lie on the walk. -/
theorem mem_support_of_mem_closure {a b : S} (W : GraphWalk Γ.toGraph a b) {f : Set S} {x : S}
    (hf : f ∈ W.edges) (hx : x ∈ closure f) (hxV : x ∈ Γ.V) : x ∈ W.support := by
  induction W with
  | nil h => exact absurd hf List.not_mem_nil
  | @cons a v b e hl r ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · have hm : x ∈ closure f ∩ Γ.V := ⟨hx, hxV⟩
      rw [hl.2.2.2] at hm
      rcases hm with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((show x = v from h) ▸ r.start_mem_support)
    · exact List.mem_cons_of_mem _ (ih hf)

/-- A walk to `a` from another vertex has an edge at `a`. -/
theorem exists_edge_at_end {x a : S} (W : GraphWalk Γ.toGraph x a) (hne : x ≠ a) :
    ∃ f ∈ W.edges, a ∈ closure f := by
  induction W with
  | nil h => exact absurd rfl hne
  | @cons x v a e hl r ih =>
    by_cases hv : v = a
    · subst hv
      have hm : v ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; simp
      exact ⟨e, List.mem_cons_self, hm.1⟩
    · obtain ⟨f, hf, h⟩ := ih hv
      exact ⟨f, List.mem_cons_of_mem _ hf, h⟩

/-- All edges of a circuit cannot lie on a path. -/
theorem circuit_not_in_path {D : Drawing S} (hD : D.IsCircuit)
  (hDs : D.IsSubdrawing Γ) {a b : S}
    (W : GraphWalk Γ.toGraph a b) (hW : W.IsSimple) (h : ∀ e ∈ D.E, e ∈ W.edges) : False := by
  obtain ⟨g, hg⟩ := IsCircuit.E_nonempty hD
  induction W with
  | nil _ => exact absurd (h g hg) List.not_mem_nil
  | @cons a v b e hl r ih =>
    by_cases he : e ∈ D.E
    · have hmem : ∀ x, x ∈ closure e ∩ Γ.V → x ∈ D.V := fun x hx => by
        rw [← hDs.closure_inter_V he] at hx
        exact hx.2
      have haD : a ∈ D.V := hmem a (by rw [hl.2.2.2]; simp)
      have hvD : v ∈ D.V := hmem v (by rw [hl.2.2.2]; simp)
      have hne : a ∉ r.support := (List.nodup_cons.mp hW).1
      have hat : ∀ f ∈ D.E, a ∈ closure f → f = e := by
        intro f hf haf
        rcases List.mem_cons.mp (h f hf) with h' | h'
        · exact h'
        · exact absurd (mem_support_of_mem_closure r h' haf hl.2.1) hne
      obtain ⟨X, ⟨-, hed⟩, hpos, -, hE⟩ := exists_walk_at hD haD
      cases X with
      | nil _ => simp at hpos
      | @cons a y a' g' hg' t =>
        have hg'D : g' ∈ D.E := by rw [hE]; exact List.mem_cons_self
        have hcap : closure g' ∩ D.V = {a, y} := hg'.2.2.2
        have hag : a ∈ closure g' ∩ D.V := by rw [hcap]; simp
        have hge : g' = e := hat g' hg'D hag.1
        by_cases hy : y = a
        · have hv' : v ∈ closure g' ∩ D.V := ⟨hge ▸ (show v ∈ closure e ∩ Γ.V by
            rw [hl.2.2.2]; simp).1, hvD⟩
          rw [hcap, hy] at hv'
          have hva : v = a := by simpa using hv'
          exact hne (hva ▸ r.start_mem_support)
        · obtain ⟨f, hf, haf⟩ := exists_edge_at_end t hy
          have hfD : f ∈ D.E := by rw [hE]; exact List.mem_cons_of_mem _ hf
          have hfe : f = g' := (hat f hfD haf).trans hge.symm
          exact (List.nodup_cons.mp hed).1 (hfe ▸ hf)
    · exact ih hW.of_cons fun f hf =>
        (List.mem_cons.mp (h f hf)).resolve_left fun h' => he (h' ▸ hf)

/-- A circuit whose edges are edges of a circuit has all its edges. -/
theorem circuit_E_eq_of_subset {C D : Drawing S} (hC : C.IsCircuit) (hD : D.IsCircuit)
    (hCs : C.IsSubdrawing Γ) (hDs : D.IsSubdrawing Γ) (h : D.E ⊆ C.E) : D.E = C.E := by
  refine subset_antisymm h fun f hf => ?_
  by_contra hfD
  obtain ⟨u, W, ⟨hnd, -⟩, -, -, hE⟩ := hC
  obtain ⟨W', hs, he⟩ := hCs.exists_walk_up W
  have hf' : f ∈ W'.edges := by
    rw [he]
    rw [hE] at hf
    exact hf
  obtain ⟨x, y, W₁, hl, W₂, rfl⟩ := exists_split_edge W' hf'
  rw [← hs, GraphWalk.support_append] at hnd
  have hsup : (GraphWalk.cons hl W₂).support.tail = W₂.support := rfl
  rw [hsup, W₁.support_eq_cons, List.cons_append, List.tail_cons] at hnd
  refine circuit_not_in_path hD hDs (W₂.append W₁) ?_ fun e heD => ?_
  · unfold GraphWalk.IsSimple
    rw [GraphWalk.support_append]
    exact (List.perm_append_comm.nodup_iff).mp hnd
  · have heW : e ∈ (W₁.append (GraphWalk.cons hl W₂)).edges := by
      have heC : e ∈ C.E := h heD
      rw [hE] at heC
      rw [he]
      exact heC
    rw [GraphWalk.edges_append] at heW ⊢
    rcases List.mem_append.mp heW with h₁ | h₁
    · exact List.mem_append_right _ h₁
    · rcases List.mem_cons.mp h₁ with rfl | h₁
      · exact absurd heD hfD
      · exact List.mem_append_left _ h₁

/-- A circuit is determined by its edges. -/
theorem circuit_eq_of_E {C D : Drawing S} (hC : C.IsCircuit) (hD : D.IsCircuit)
    (hCs : C.IsSubdrawing Γ) (hDs : D.IsSubdrawing Γ) (h : C.E = D.E) : C = D := by
  have key : ∀ {A B : Drawing S}, A.IsCircuit → A.IsSubdrawing Γ → B.IsSubdrawing Γ → A.E = B.E →
      A.V ⊆ B.V := by
    intro A B hA hAs hBs hAB x hx
    obtain ⟨X, -, hpos, -, hE⟩ := exists_walk_at hA hx
    cases X with
    | nil _ => simp at hpos
    | @cons a y a' g hg t =>
      have hgA : g ∈ A.E := by rw [hE]; exact List.mem_cons_self
      have hm : x ∈ closure g ∩ A.V := by rw [hg.2.2.2]; simp
      rw [hAs.closure_inter_V hgA, ← hBs.closure_inter_V (hAB ▸ hgA)] at hm
      exact hm.2
  exact Drawing.ext_of_V_E (subset_antisymm (key hC hCs hDs h) (key hD hDs hCs h.symm)) h

/-- `W₁` and `W₂` cut the circuit `C` into two pieces, from `a` to `b` and back. -/
structure Splits (C : Drawing S) {a b : S} (W₁ : GraphWalk Γ.toGraph a b)
    (W₂ : GraphWalk Γ.toGraph b a) : Prop where
  s₁ : W₁.IsSimple
  s₂ : W₂.IsSimple
  meet : ∀ x, x ∈ W₁.support → x ∈ W₂.support → x = a ∨ x = b
  edge : ∀ e ∈ W₁.edges, e ∉ W₂.edges
  V : ∀ x, x ∈ C.V ↔ x ∈ W₁.support ∨ x ∈ W₂.support
  E : ∀ e, e ∈ C.E ↔ e ∈ W₁.edges ∨ e ∈ W₂.edges

namespace Splits

variable {C : Drawing S} {a b : S} {W₁ : GraphWalk Γ.toGraph a b} {W₂ : GraphWalk Γ.toGraph b a}

theorem swap (h : Splits C W₁ W₂) : Splits C W₂ W₁ where
  s₁ := h.s₂
  s₂ := h.s₁
  meet x h₂ h₁ := (h.meet x h₁ h₂).symm
  edge e h₂ h₁ := h.edge e h₁ h₂
  V x := (h.V x).trans or_comm
  E e := (h.E e).trans or_comm

theorem rev (h : Splits C W₁ W₂) : Splits C W₂.reverse W₁.reverse where
  s₁ := h.s₂.reverse
  s₂ := h.s₁.reverse
  meet x h₂ h₁ := by
    rw [GraphWalk.support_reverse, List.mem_reverse] at h₁ h₂
    exact h.meet x h₁ h₂
  edge e h₂ h₁ := by
    rw [GraphWalk.edges_reverse, List.mem_reverse] at h₁ h₂
    exact h.edge e h₁ h₂
  V x := by
    rw [GraphWalk.support_reverse, GraphWalk.support_reverse, List.mem_reverse, List.mem_reverse]
    exact (h.V x).trans or_comm
  E e := by
    rw [GraphWalk.edges_reverse, GraphWalk.edges_reverse, List.mem_reverse, List.mem_reverse]
    exact (h.E e).trans or_comm

/-- The vertices on the two sides of a joint of a simple walk. -/
theorem append_meet {c : S} {P₁ : GraphWalk Γ.toGraph a c} {P₂ : GraphWalk Γ.toGraph c b}
    (hW : (P₁.append P₂).IsSimple) {y : S} (h₁ : y ∈ P₁.support) (h₂ : y ∈ P₂.support) : y = c := by
  unfold GraphWalk.IsSimple at hW
  rw [GraphWalk.support_append] at hW
  by_contra hne
  have hy : y ∈ P₂.support.tail := by
    rw [P₂.support_eq_cons] at h₂
    exact (List.mem_cons.mp h₂).resolve_left hne
  exact (List.nodup_append.mp hW).2.2 y h₁ y hy rfl

theorem append_edge {c : S} {P₁ : GraphWalk Γ.toGraph a c} {P₂ : GraphWalk Γ.toGraph c b}
    (hW : (P₁.append P₂).IsSimple) {e : Set S} (h₁ : e ∈ P₁.edges) (h₂ : e ∈ P₂.edges) : False := by
  have hnd := hW.edges_nodup
  rw [GraphWalk.edges_append] at hnd
  exact (List.nodup_append.mp hnd).2.2 e h₁ e h₂ rfl

/-- Cutting the first piece at `c`: the part from `a` to `c`, and all the rest. -/
theorem split_left {c : S} {P₁ : GraphWalk Γ.toGraph a c} {P₂ : GraphWalk Γ.toGraph c b}
    (h : Splits C (P₁.append P₂) W₂) (hca : c ≠ a) (hcb : c ≠ b) :
    Splits C P₁ (P₂.append W₂) := by
  have hs := isSimple_of_append h.s₁
  have hbP : b ∉ P₁.support := fun hb => hcb (append_meet h.s₁ hb P₂.end_mem_support).symm
  have haP : a ∉ P₂.support := fun ha => hca (append_meet h.s₁ P₁.start_mem_support ha).symm
  have hin₁ : ∀ x ∈ P₁.support, x ∈ (P₁.append P₂).support := fun x hx =>
    (GraphWalk.mem_support_append _ _).mpr (Or.inl hx)
  have hin₂ : ∀ x ∈ P₂.support, x ∈ (P₁.append P₂).support := fun x hx =>
    (GraphWalk.mem_support_append _ _).mpr (Or.inr hx)
  refine ⟨hs.1, isSimple_append' hs.2 h.s₂ fun y h₁ h₂ => ?_, fun x h₁ h₂ => ?_, fun e h₁ h₂ => ?_,
    fun x => ?_, fun e => ?_⟩
  · exact (h.meet y (hin₂ y h₁) h₂).resolve_left fun hy => haP (hy ▸ h₁)
  · rcases (GraphWalk.mem_support_append _ _).mp h₂ with h₂ | h₂
    · exact Or.inr (append_meet h.s₁ h₁ h₂)
    · exact Or.inl ((h.meet x (hin₁ x h₁) h₂).resolve_right fun hx => hbP (hx ▸ h₁))
  · rw [GraphWalk.edges_append] at h₂
    rcases List.mem_append.mp h₂ with h₂ | h₂
    · exact append_edge h.s₁ h₁ h₂
    · refine h.edge e ?_ h₂
      rw [GraphWalk.edges_append]
      exact List.mem_append_left _ h₁
  · rw [h.V, GraphWalk.mem_support_append, GraphWalk.mem_support_append, or_assoc]
  · rw [h.E, GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append,
      or_assoc]

/-- Cutting the first piece at `c`: the part from `c` to `b`, and all the rest. -/
theorem split_right {c : S} {P₁ : GraphWalk Γ.toGraph a c} {P₂ : GraphWalk Γ.toGraph c b}
    (h : Splits C (P₁.append P₂) W₂) (hca : c ≠ a) (hcb : c ≠ b) :
    Splits C P₂ (W₂.append P₁) := by
  have hs := isSimple_of_append h.s₁
  have hbP : b ∉ P₁.support := fun hb => hcb (append_meet h.s₁ hb P₂.end_mem_support).symm
  have haP : a ∉ P₂.support := fun ha => hca (append_meet h.s₁ P₁.start_mem_support ha).symm
  have hin₁ : ∀ x ∈ P₁.support, x ∈ (P₁.append P₂).support := fun x hx =>
    (GraphWalk.mem_support_append _ _).mpr (Or.inl hx)
  have hin₂ : ∀ x ∈ P₂.support, x ∈ (P₁.append P₂).support := fun x hx =>
    (GraphWalk.mem_support_append _ _).mpr (Or.inr hx)
  refine ⟨hs.2, isSimple_append' h.s₂ hs.1 fun y h₂ h₁ => ?_, fun x h₂ h₃ => ?_, fun e h₁ h₂ => ?_,
    fun x => ?_, fun e => ?_⟩
  · exact (h.meet y (hin₁ y h₁) h₂).resolve_right fun hy => hbP (hy ▸ h₁)
  · rcases (GraphWalk.mem_support_append _ _).mp h₃ with h₃ | h₃
    · exact Or.inr ((h.meet x (hin₂ x h₂) h₃).resolve_left fun hx => haP (hx ▸ h₂))
    · exact Or.inl (append_meet h.s₁ h₃ h₂)
  · rw [GraphWalk.edges_append] at h₂
    rcases List.mem_append.mp h₂ with h₂ | h₂
    · refine h.edge e ?_ h₂
      rw [GraphWalk.edges_append]
      exact List.mem_append_right _ h₁
    · exact append_edge h.s₁ h₂ h₁
  · rw [h.V, GraphWalk.mem_support_append, GraphWalk.mem_support_append]
    tauto
  · rw [h.E, GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append]
    tauto

end Splits

/-- A circuit splits at any two of its vertices. -/
theorem exists_splits [T2Space S] {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ) {a b
  : S}
    (ha : a ∈ C.V) (hb : b ∈ C.V) (hab : a ≠ b) :
    ∃ (W₁ : GraphWalk Γ.toGraph a b) (W₂ : GraphWalk Γ.toGraph b a), Splits C W₁ W₂ := by
  obtain ⟨P, Q, ⟨X, hX, hXV, hXE⟩, ⟨Y, hY, hYV, hYE⟩, hPs, hQs, -, -, hVm, hEd, hsup⟩ :=
    hC.exists_two_paths ha hb hab
  obtain ⟨X', hs₁, he₁⟩ := (hPs.trans hCs).exists_walk_up X
  obtain ⟨Y', hs₂, he₂⟩ := (hQs.trans hCs).exists_walk_up Y
  have hV := congrArg Drawing.V hsup
  have hE := congrArg Drawing.E hsup
  rw [Drawing.sup_V hPs hQs] at hV
  rw [Drawing.sup_E hPs hQs] at hE
  have hmemV₁ : ∀ x, x ∈ P.V ↔ x ∈ X'.support := fun x => by rw [hXV, hs₁]; rfl
  have hmemV₂ : ∀ x, x ∈ Q.V ↔ x ∈ Y'.reverse.support := fun x => by
    rw [hYV, GraphWalk.support_reverse, List.mem_reverse, hs₂]; rfl
  have hmemE₁ : ∀ e, e ∈ P.E ↔ e ∈ X'.edges := fun e => by rw [hXE, he₁]; rfl
  have hmemE₂ : ∀ e, e ∈ Q.E ↔ e ∈ Y'.reverse.edges := fun e => by
    rw [hYE, GraphWalk.edges_reverse, List.mem_reverse, he₂]; rfl
  refine ⟨X', Y'.reverse, ?_, ?_, fun x h₁ h₂ => ?_, fun e h₁ h₂ => ?_, fun x => ?_, fun e => ?_⟩
  · unfold GraphWalk.IsSimple
    rw [hs₁]
    exact hX
  · have hsimple : Y'.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [hs₂]
      exact hY
    exact hsimple.reverse
  · have hm : x ∈ P.V ∩ Q.V := ⟨(hmemV₁ x).mpr h₁, (hmemV₂ x).mpr h₂⟩
    rw [hVm] at hm
    exact hm
  · exact disjoint_left.mp hEd ((hmemE₁ e).mpr h₁) ((hmemE₂ e).mpr h₂)
  · rw [← hV, mem_union, hmemV₁, hmemV₂]
  · rw [← hE, mem_union, hmemE₁, hmemE₂]

/-- `S` is an *ear* on `C₂`: a path between two vertices of `C₂` with nothing else in common. -/
structure IsEar (C₂ : Drawing S) {a b : S} (T : GraphWalk Γ.toGraph a b) : Prop where
  left : a ∈ C₂.V
  right : b ∈ C₂.V
  ne : a ≠ b
  inner : ∀ x ∈ T.support, x ∈ C₂.V → x = a ∨ x = b
  off : ∀ f ∈ T.edges, f ∉ C₂.E

/-- Inside a piece of `C` between two vertices of `C₂`, each edge off `C₂` lies on an ear. -/
theorem exists_ear {C C₂ : Drawing S} (hsub : C₂.IsSubdrawing Γ) {e : Set S} (he : e ∉ C₂.E)
  (n : ℕ) :
    ∀ {a b : S} (W₁ : GraphWalk Γ.toGraph a b) (W₂ : GraphWalk Γ.toGraph b a), Splits C W₁ W₂ →
      a ∈ C₂.V → b ∈ C₂.V → a ≠ b → e ∈ W₁.edges → W₁.length = n →
      ∃ (a' b' : S) (T : GraphWalk Γ.toGraph a' b') (T' : GraphWalk Γ.toGraph b' a'),
        Splits C T T' ∧ IsEar C₂ T ∧ e ∈ T.edges ∧ ∀ f ∈ T.edges, f ∈ W₁.edges := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b W₁ W₂ h ha hb hab heW hn
    by_cases hc : ∃ c ∈ W₁.support, c ∈ C₂.V ∧ c ≠ a ∧ c ≠ b
    · obtain ⟨c, hcW, hcC, hca, hcb⟩ := hc
      obtain ⟨P₁, P₂, rfl⟩ := W₁.exists_append_of_mem hcW
      have hl₁ : P₁.length ≠ 0 := fun h => hca (GraphWalk.eq_of_length_eq_zero h).symm
      have hl₂ : P₂.length ≠ 0 := fun h => hcb (GraphWalk.eq_of_length_eq_zero h)
      rw [GraphWalk.length_append] at hn
      rw [GraphWalk.edges_append] at heW
      rcases List.mem_append.mp heW with hP | hP
      · obtain ⟨a', b', T, T', h₁, h₂, h₃, h₄⟩ := ih P₁.length (by omega) P₁ _
          (h.split_left hca hcb) ha hcC hca.symm hP rfl
        refine ⟨a', b', T, T', h₁, h₂, h₃, fun f hf => ?_⟩
        rw [GraphWalk.edges_append]
        exact List.mem_append_left _ (h₄ f hf)
      · obtain ⟨a', b', T, T', h₁, h₂, h₃, h₄⟩ := ih P₂.length (by omega) P₂ _
          (h.split_right hca hcb) hcC hb hcb hP rfl
        refine ⟨a', b', T, T', h₁, h₂, h₃, fun f hf => ?_⟩
        rw [GraphWalk.edges_append]
        exact List.mem_append_right _ (h₄ f hf)
    · push Not at hc
      have hinner : ∀ x ∈ W₁.support, x ∈ C₂.V → x = a ∨ x = b := fun x hx hxC => by
        by_contra hne
        push Not at hne
        exact hne.2 (hc x hx hxC hne.1)
      refine ⟨a, b, W₁, W₂, h, ⟨ha, hb, hab, hinner, fun f hf hfC => ?_⟩, heW, fun _ h => h⟩
      obtain ⟨x, y, X, hl, Y, rfl⟩ := exists_split_edge W₁ hf
      have hs := isSimple_of_append h.s₁
      have hmeet : ∀ z ∈ X.support, z ∈ Y.support → False := fun z h₁ h₂ => by
        have hW : (X.append (GraphWalk.cons hl Y)).IsSimple := h.s₁
        unfold GraphWalk.IsSimple at hW
        rw [GraphWalk.support_append] at hW
        exact (List.nodup_append.mp hW).2.2 z h₁ z h₂ rfl
      have hmemC : ∀ z, z ∈ closure f ∩ Γ.V → z ∈ C₂.V := fun z hz => by
        rw [← hsub.closure_inter_V hfC] at hz
        exact hz.2
      have hxC := hmemC x (by rw [hl.2.2.2]; simp)
      have hyC := hmemC y (by rw [hl.2.2.2]; simp)
      have hxW : x ∈ (X.append (GraphWalk.cons hl Y)).support :=
        (GraphWalk.mem_support_append _ _).mpr (Or.inl X.end_mem_support)
      have hyW : y ∈ (X.append (GraphWalk.cons hl Y)).support :=
        (GraphWalk.mem_support_append _ _).mpr
          (Or.inr (List.mem_cons_of_mem _ Y.start_mem_support))
      have hxa : x = a := (hinner x hxW hxC).resolve_right fun hxb =>
        hmeet x X.end_mem_support (hxb ▸ Y.end_mem_support)
      have hyb : y = b := (hinner y hyW hyC).resolve_left fun hya =>
        hmeet a X.start_mem_support (hya ▸ Y.start_mem_support)
      subst hxa hyb
      have h₀ : X.edges = [] := by
        have := hs.1.length_eq_zero
        exact List.length_eq_zero_iff.mp this
      have h₁ : Y.edges = [] := by
        have := (GraphWalk.IsSimple.of_cons hs.2).length_eq_zero
        exact List.length_eq_zero_iff.mp this
      rw [GraphWalk.edges_append, h₀] at heW
      simp only [GraphWalk.edges_cons, h₁, List.nil_append, List.mem_singleton] at heW
      exact he (heW ▸ hfC)

/-- A simple walk from `p` to `a` in `C` that starts on the second piece and misses `b` stays on the
second piece. -/
theorem stays_on_piece {C : Drawing S} {a b : S} {W₁ : GraphWalk Γ.toGraph a b}
    {W₂ : GraphWalk Γ.toGraph b a} (h : Splits C W₁ W₂) {p : S}
    (X : GraphWalk Γ.toGraph p a) (hX : X.IsSimple) (hE : ∀ f ∈ X.edges, f ∈ C.E)
    (hp : p ∈ W₂.support) (hb : b ∉ X.support) :
    (∀ f ∈ X.edges, f ∈ W₂.edges) ∧ ∀ x ∈ X.support, x ∈ W₂.support := by
  induction X with
  | nil _ =>
    refine ⟨fun f hf => absurd hf List.not_mem_nil, fun x hx => ?_⟩
    rw [mem_support_nil.mp hx]
    exact hp
  | @cons p q a g hl r ih =>
    have hg : g ∈ C.E := hE g List.mem_cons_self
    have hpne : p ≠ b := fun h' => hb (h' ▸ List.mem_cons_self)
    have hpg : p ∈ closure g ∩ Γ.V := by rw [hl.2.2.2]; simp
    have hqg : q ∈ closure g ∩ Γ.V := by rw [hl.2.2.2]; simp
    have hgW : g ∈ W₂.edges := by
      refine ((h.E g).mp hg).resolve_left fun hg₁ => ?_
      have hp₁ := mem_support_of_mem_closure W₁ hg₁ hpg.1 hpg.2
      have hpa : p = a := (h.meet p hp₁ hp).resolve_right hpne
      exact (List.nodup_cons.mp hX).1 (hpa ▸ r.end_mem_support)
    have hq := mem_support_of_mem_closure W₂ hgW hqg.1 hqg.2
    obtain ⟨h₁, h₂⟩ := ih h hX.of_cons (fun f hf => hE f (List.mem_cons_of_mem _ hf)) hq
      fun h' => hb (List.mem_cons_of_mem _ h')
    refine ⟨fun f hf => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact hgW
      · exact h₁ f hf
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · exact h₂ x hx

/-- A simple walk inside the second piece, with the same ends, is the second piece. -/
theorem Splits.replace [T2Space S] {C : Drawing S} (hC : C.IsCircuit)
  (hCs : C.IsSubdrawing Γ) {a b : S}
    {W₁ : GraphWalk Γ.toGraph a b} {W₂ X : GraphWalk Γ.toGraph b a} (h : Splits C W₁ W₂)
    (hab : a ≠ b) (hX : X.IsSimple) (hE : ∀ f ∈ X.edges, f ∈ W₂.edges)
    (hV : ∀ x ∈ X.support, x ∈ W₂.support) : Splits C W₁ X := by
  have hsc : (W₁.append X).IsSimpleClosed := GraphWalk.isSimpleClosed_append h.s₁ hX
    (fun x h₁ h₂ => h.meet x h₁ (hV x h₂)) fun e h₁ h₂ => h.edge e h₁ (hE e h₂)
  have hpos : 0 < (W₁.append X).length := by
    rw [GraphWalk.length_append]
    have : W₁.length ≠ 0 := fun h => hab (GraphWalk.eq_of_length_eq_zero h)
    omega
  have hD := isCircuit_walkDrawing Γ hsc hpos
  have hDs := walkDrawing_isSubdrawing Γ (W₁.append X)
  have hEsub : (walkDrawing Γ (W₁.append X)).E ⊆ C.E := by
    rw [walkDrawing_E]
    intro f hf
    have hf' : f ∈ (W₁.append X).edges := hf
    rw [GraphWalk.edges_append] at hf'
    rcases List.mem_append.mp hf' with hf' | hf'
    · exact (h.E f).mpr (Or.inl hf')
    · exact (h.E f).mpr (Or.inr (hE f hf'))
  have heq := circuit_eq_of_E hD hC hDs hCs (circuit_E_eq_of_subset hC hD hCs hDs hEsub)
  refine ⟨h.s₁, hX, fun x h₁ h₂ => h.meet x h₁ (hV x h₂), fun e h₁ h₂ => h.edge e h₁ (hE e h₂),
    fun x => ?_, fun e => ?_⟩
  · rw [← heq, walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append]
  · rw [← heq, walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append]

/-- A simple walk of a circuit between two of its vertices leaves a simple walk as the rest. -/
theorem exists_complement [T2Space S] {C : Drawing S} (hC : C.IsCircuit)
  (hCs : C.IsSubdrawing Γ) {a b : S}
    {W₁ : GraphWalk Γ.toGraph a b} {W₂ : GraphWalk Γ.toGraph b a} (h : Splits C W₁ W₂) (hab : a ≠ b)
    (X : GraphWalk Γ.toGraph b a) (hX : X.IsSimple) (hE : ∀ f ∈ X.edges, f ∈ C.E) :
    ∃ Y : GraphWalk Γ.toGraph a b, Splits C Y X := by
  have main : ∀ {W₁' : GraphWalk Γ.toGraph a b} {W₂' : GraphWalk Γ.toGraph b a}, Splits C W₁' W₂' →
      (∀ {q : S} {g : Set S} (hl : Γ.toGraph.IsLink g b q) (r : GraphWalk Γ.toGraph q a),
        X = GraphWalk.cons hl r → g ∈ W₂'.edges) → Splits C W₁' X := by
    intro W₁' W₂' h' hfirst
    cases hc : X with
    | nil _ => exact absurd rfl hab
    | @cons b q a g hl r =>
      have hgW := hfirst hl r hc
      subst hc
      have hqg : q ∈ closure g ∩ Γ.V := by rw [hl.2.2.2]; simp
      have hq := mem_support_of_mem_closure W₂' hgW hqg.1 hqg.2
      obtain ⟨h₁, h₂⟩ := stays_on_piece h' r hX.of_cons
        (fun f hf => hE f (List.mem_cons_of_mem _ hf)) hq (List.nodup_cons.mp hX).1
      refine h'.replace hC hCs hab hX (fun f hf => ?_) fun x hx => ?_
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact hgW
        · exact h₁ f hf
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact W₂'.start_mem_support
        · exact h₂ x hx
  by_cases hfirst : ∀ {q : S} {g : Set S} (hl : Γ.toGraph.IsLink g b q)
      (r : GraphWalk Γ.toGraph q a), X = GraphWalk.cons hl r → g ∈ W₂.edges
  · exact ⟨W₁, main h hfirst⟩
  · refine ⟨W₂.reverse, main h.rev fun {q g} hl r hr => ?_⟩
    rw [GraphWalk.edges_reverse, List.mem_reverse]
    by_contra hg
    refine hfirst fun {q' g'} hl' r' hr' => ?_
    have hg' : g' ∈ C.E := hE g' (by rw [hr']; exact List.mem_cons_self)
    rcases (h.E g').mp hg' with h₁ | h₁
    · cases hr.symm.trans hr'
      exact absurd h₁ hg
    · exact h₁

/-- The edges of a walk, as a set. -/
def edgeSet {a b : S} (W : GraphWalk Γ.toGraph a b) : Set (Set S) := {e | e ∈ W.edges}

theorem finite_edgeSet {a b : S} (W : GraphWalk Γ.toGraph a b) : (edgeSet W).Finite :=
  W.edges.finite_toSet

/-- The two pieces of a circuit have total length that of the circuit. -/
theorem Splits.card_add {C : Drawing S} {a b : S} {W₁ : GraphWalk Γ.toGraph a b}
    {W₂ : GraphWalk Γ.toGraph b a} (h : Splits C W₁ W₂) :
    (edgeSet W₁).ncard + (edgeSet W₂).ncard = C.length := by
  have hE : C.E = edgeSet W₁ ∪ edgeSet W₂ := by
    ext e
    exact h.E e
  have hdis : Disjoint (edgeSet W₁) (edgeSet W₂) := disjoint_left.mpr fun e h₁ h₂ => h.edge e h₁ h₂
  rw [Drawing.length, hE]
  exact (ncard_union_eq hdis (finite_edgeSet _) (finite_edgeSet _)).symm

/-- A short ear cannot miss an edge of `C₁` outside `C₂`: it would make a short circuit that is none
of `C₁, C₂, C₃`. -/
theorem short_ear_false [T2Space S] {k : ℕ} {C₁ C₂ C₃ : Drawing S} (h₂ : C₂.IsCircuit)
    (s₂ : C₂.IsSubdrawing Γ) (l₁ : C₁.length < k) (l₂ : C₂.length < k)
    (hE : ∀ e, e ∈ C₃.E ↔ (e ∈ C₁.E ∧ e ∉ C₂.E) ∨ (e ∉ C₁.E ∧ e ∈ C₂.E))
    (hshort : ∀ T : Drawing S, T.IsCircuit → T.IsSubdrawing Γ → (∀ e ∈ T.E, e ∈ C₁.E ∨ e ∈ C₂.E) →
      T.length < k → T.E = C₁.E ∨ T.E = C₂.E ∨ T.E = C₃.E)
    {a b : S} (T : GraphWalk Γ.toGraph a b) (hT : T.IsSimple) (hear : IsEar C₂ T)
    (hlen : 2 * (edgeSet T).ncard ≤ C₁.length) (hsub : ∀ f ∈ T.edges, f ∈ C₁.E) {f : Set S}
    (hf₁ : f ∈ C₁.E) (hf₂ : f ∉ C₂.E) (hfT : f ∉ T.edges) : False := by
  obtain ⟨R, R', hspl⟩ := exists_splits h₂ s₂ hear.left hear.right hear.ne
  obtain ⟨R₁, R₂, hspl', hR⟩ : ∃ (R₁ : GraphWalk Γ.toGraph a b) (R₂ : GraphWalk Γ.toGraph b a),
      Splits C₂ R₁ R₂ ∧ 2 * (edgeSet R₂).ncard ≤ C₂.length := by
    have hc := hspl.card_add
    by_cases hle : 2 * (edgeSet R').ncard ≤ C₂.length
    · exact ⟨R, R', hspl, hle⟩
    · refine ⟨R'.reverse, R.reverse, hspl.rev, ?_⟩
      have hset : edgeSet R.reverse = edgeSet R := by
        ext e
        simp only [edgeSet, mem_ofPred_eq, GraphWalk.edges_reverse, List.mem_reverse]
      rw [hset]
      omega
  have hsc : (T.append R₂).IsSimpleClosed := GraphWalk.isSimpleClosed_append hT hspl'.s₂
    (fun x h₁ h₂' => hear.inner x h₁ ((hspl'.V x).mpr (Or.inr h₂')))
    fun e h₁ h₂' => hear.off e h₁ ((hspl'.E e).mpr (Or.inr h₂'))
  have hTpos : T.length ≠ 0 := fun h => hear.ne (GraphWalk.eq_of_length_eq_zero h)
  have hpos : 0 < (T.append R₂).length := by
    rw [GraphWalk.length_append]
    omega
  have hD := isCircuit_walkDrawing Γ hsc hpos
  have hDs := walkDrawing_isSubdrawing Γ (T.append R₂)
  have hDE : (walkDrawing Γ (T.append R₂)).E = edgeSet T ∪ edgeSet R₂ := by
    rw [walkDrawing_E]
    ext e
    simp only [edgeSet, mem_ofPred_eq, mem_union, GraphWalk.edges_append, List.mem_append]
  have hmem : ∀ e, e ∈ (walkDrawing Γ (T.append R₂)).E → e ∈ T.edges ∨ e ∈ R₂.edges := fun e he
    => by
    rw [hDE] at he
    exact he
  have hlenD : (walkDrawing Γ (T.append R₂)).length < k := by
    have := ncard_union_le (edgeSet T) (edgeSet R₂)
    rw [Drawing.length, hDE]
    omega
  have hin : ∀ e ∈ (walkDrawing Γ (T.append R₂)).E, e ∈ C₁.E ∨ e ∈ C₂.E := fun e he =>
    (hmem e he).imp (hsub e) fun h => (hspl'.E e).mpr (Or.inr h)
  have hnot : f ∉ (walkDrawing Γ (T.append R₂)).E := fun h =>
    (hmem f h).elim hfT fun h' => hf₂ ((hspl'.E f).mpr (Or.inr h'))
  rcases hshort _ hD hDs hin hlenD with h | h | h
  · exact hnot (h ▸ hf₁)
  · obtain ⟨e₀, he₀⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hTpos)
    refine hear.off e₀ he₀ ?_
    rw [← h, hDE]
    exact Or.inl he₀
  · exact hnot (h ▸ (hE f).mpr (Or.inl ⟨hf₁, hf₂⟩))

/-- Three circuits as in the statement are three paths with the same ends. -/
theorem exists_theta [T2Space S] {k : ℕ} {C₁ C₂ C₃ : Drawing S} (h₁ : C₁.IsCircuit)
    (h₂ : C₂.IsCircuit) (h₃ : C₃.IsCircuit) (s₁ : C₁.IsSubdrawing Γ) (s₂ : C₂.IsSubdrawing Γ)
    (s₃ : C₃.IsSubdrawing Γ) (l₁ : C₁.length < k) (l₂ : C₂.length < k)
    (hE : ∀ e, e ∈ C₃.E ↔ (e ∈ C₁.E ∧ e ∉ C₂.E) ∨ (e ∉ C₁.E ∧ e ∈ C₂.E))
    (hnot : ∃ e ∈ C₁.E, e ∉ C₂.E)
    (hshort : ∀ T : Drawing S, T.IsCircuit → T.IsSubdrawing Γ → (∀ e ∈ T.E, e ∈ C₁.E ∨ e ∈ C₂.E) →
      T.length < k → T.E = C₁.E ∨ T.E = C₂.E ∨ T.E = C₃.E) :
    ∃ (P₀ P₁ P₂ : Drawing S) (a b : S), P₀.IsPathBetween a b ∧ P₁.IsPathBetween a b ∧
      P₂.IsPathBetween a b ∧ P₀.IsSubdrawing Γ ∧ P₁.IsSubdrawing Γ ∧ P₂.IsSubdrawing Γ ∧
      0 < P₀.length ∧ 0 < P₁.length ∧ 0 < P₂.length ∧
      P₀.V ∩ P₁.V = {a, b} ∧ P₁.V ∩ P₂.V = {a, b} ∧ P₂.V ∩ P₀.V = {a, b} ∧
      Disjoint P₀.E P₁.E ∧ Disjoint P₁.E P₂.E ∧ Disjoint P₂.E P₀.E ∧
      Γ.sup P₀ P₁ = C₁ ∧ Γ.sup P₁ P₂ = C₂ ∧ Γ.sup P₂ P₀ = C₃ := by
  obtain ⟨e, he₁, he₂⟩ := hnot
  -- The circuits `C₁` and `C₂` have a common edge, since otherwise `C₁` lies inside `C₃`.
  obtain ⟨g, hg₁, hg₂⟩ : ∃ g ∈ C₁.E, g ∈ C₂.E := by
    by_contra hno
    push Not at hno
    have hsub : C₁.E ⊆ C₃.E := fun x hx => (hE x).mpr (Or.inl ⟨hx, hno x hx⟩)
    have heq := circuit_E_eq_of_subset h₃ h₁ s₃ s₁ hsub
    obtain ⟨y, hy⟩ := IsCircuit.E_nonempty h₂
    have hy₁ : y ∉ C₁.E := fun h => hno y h hy
    exact hy₁ (heq ▸ (hE y).mpr (Or.inr ⟨hy₁, hy⟩))
  -- Its ends are distinct, as `C₁` is not a single loop.
  obtain ⟨x, y, hl, hxy⟩ : ∃ (x y : S) (_ : C₁.toGraph.IsLink g x y), x ≠ y := by
    obtain ⟨u, W, -, -, -, hEC⟩ := id h₁
    have hgW : g ∈ W.edges := by
      rw [hEC] at hg₁
      exact hg₁
    obtain ⟨x, y, -, hl, -, -⟩ := exists_split_edge W hgW
    refine ⟨x, y, hl, ?_⟩
    rintro rfl
    have hloop : closure g ∩ C₁.V = {x} := by
      rw [hl.2.2.2]
      simp
    have hone := IsCircuit.E_eq_of_loop h₁ hg₁ hloop
    rw [hone] at he₁
    exact he₂ ((show e = g from he₁) ▸ hg₂)
  have hmem₂ : ∀ z, z ∈ closure g ∩ C₁.V → z ∈ C₂.V := fun z hz => by
    rw [s₁.closure_inter_V hg₁, ← s₂.closure_inter_V hg₂] at hz
    exact hz.2
  have hxg : x ∈ closure g ∩ C₁.V := by rw [hl.2.2.2]; simp
  have hyg : y ∈ closure g ∩ C₁.V := by rw [hl.2.2.2]; simp
  -- Cut `C₁` at the ends of `g`, and take an ear through `e`.
  obtain ⟨a₀, b₀, W₁, W₂, hspl₀, ha₀, hb₀, hab₀, heW⟩ :
      ∃ (a₀ b₀ : S) (W₁ : GraphWalk Γ.toGraph a₀ b₀) (W₂ : GraphWalk Γ.toGraph b₀ a₀),
        Splits C₁ W₁ W₂ ∧ a₀ ∈ C₂.V ∧ b₀ ∈ C₂.V ∧ a₀ ≠ b₀ ∧ e ∈ W₁.edges := by
    obtain ⟨W₁, W₂, hspl⟩ := exists_splits h₁ s₁ hxg.2 hyg.2 hxy
    rcases (hspl.E e).mp he₁ with h | h
    · exact ⟨x, y, W₁, W₂, hspl, hmem₂ x hxg, hmem₂ y hyg, hxy, h⟩
    · exact ⟨y, x, W₂, W₁, hspl.swap, hmem₂ y hyg, hmem₂ x hxg, hxy.symm, h⟩
  obtain ⟨a, b, T, T', hspl, hear, heT, -⟩ :=
    exists_ear s₂ he₂ _ W₁ W₂ hspl₀ ha₀ hb₀ hab₀ heW rfl
  -- All of the rest of `C₁` lies in `C₂`.
  have hrest : ∀ f ∈ T'.edges, f ∈ C₂.E := by
    intro f hfT
    by_contra hf
    obtain ⟨a', b', Q, Q', hspl', hear', hfQ, hsubQ⟩ :=
      exists_ear s₂ hf _ T' T hspl.swap hear.right hear.left hear.ne.symm hfT rfl
    have hdis : Disjoint (edgeSet T) (edgeSet Q) :=
      disjoint_left.mpr fun x hx hxQ => hspl.edge x hx (hsubQ x hxQ)
    have hcard : (edgeSet T).ncard + (edgeSet Q).ncard ≤ C₁.length := by
      rw [← ncard_union_eq hdis (finite_edgeSet _) (finite_edgeSet _)]
      refine ncard_le_ncard ?_ C₁.finite_edges
      rintro x (hx | hx)
      · exact (hspl.E x).mpr (Or.inl hx)
      · exact (hspl'.E x).mpr (Or.inl hx)
    by_cases hle : 2 * (edgeSet T).ncard ≤ C₁.length
    · exact short_ear_false h₂ s₂ l₁ l₂ hE hshort T hspl.s₁ hear hle
        (fun x hx => (hspl.E x).mpr (Or.inl hx)) ((hspl'.E f).mpr (Or.inl hfQ)) hf
        fun h => hspl.edge f h hfT
    · exact short_ear_false h₂ s₂ l₁ l₂ hE hshort Q hspl'.s₁ hear' (by omega)
        (fun x hx => (hspl'.E x).mpr (Or.inl hx)) he₁ he₂ fun h => hspl.edge e heT (hsubQ e h)
  obtain ⟨R, R', hspl₂⟩ := exists_splits h₂ s₂ hear.left hear.right hear.ne
  obtain ⟨Y, hY⟩ := exists_complement h₂ s₂ hspl₂ hear.ne T' hspl.s₂ hrest
  have mv₀ : ∀ x, x ∈ (walkDrawing Γ T).V ↔ x ∈ T.support := fun x => by rw [walkDrawing_V]; rfl
  have mv₁ : ∀ x, x ∈ (walkDrawing Γ T'.reverse).V ↔ x ∈ T'.support := fun x => by
    rw [walkDrawing_V]
    change x ∈ T'.reverse.support ↔ _
    rw [GraphWalk.support_reverse, List.mem_reverse]
  have mv₂ : ∀ x, x ∈ (walkDrawing Γ Y).V ↔ x ∈ Y.support := fun x => by rw [walkDrawing_V]; rfl
  have me₀ : ∀ x, x ∈ (walkDrawing Γ T).E ↔ x ∈ T.edges := fun x => by rw [walkDrawing_E]; rfl
  have me₁ : ∀ x, x ∈ (walkDrawing Γ T'.reverse).E ↔ x ∈ T'.edges := fun x => by
    rw [walkDrawing_E]
    change x ∈ T'.reverse.edges ↔ _
    rw [GraphWalk.edges_reverse, List.mem_reverse]
  have me₂ : ∀ x, x ∈ (walkDrawing Γ Y).E ↔ x ∈ Y.edges := fun x => by rw [walkDrawing_E]; rfl
  have hP₀ := walkDrawing_isPathBetween Γ hspl.s₁
  have hP₁ := walkDrawing_isPathBetween Γ hspl.s₂.reverse
  have hP₂ := walkDrawing_isPathBetween Γ hY.s₁
  have sP₀ := walkDrawing_isSubdrawing Γ T
  have sP₁ := walkDrawing_isSubdrawing Γ T'.reverse
  have sP₂ := walkDrawing_isSubdrawing Γ Y
  have hpos : ∀ (W : GraphWalk Γ.toGraph a b), 0 < (walkDrawing Γ W).length := fun W => by
    have hl : W.length ≠ 0 := fun h => hear.ne (GraphWalk.eq_of_length_eq_zero h)
    obtain ⟨e₀, he₀⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hl)
    have hm : e₀ ∈ (walkDrawing Γ W).E := by
      rw [walkDrawing_E]
      exact he₀
    exact (ncard_pos (walkDrawing Γ W).finite_edges).mpr ⟨e₀, hm⟩
  have hV₀₁ : (walkDrawing Γ T).V ∩ (walkDrawing Γ T'.reverse).V = {a, b} := by
    ext x
    rw [mem_inter_iff, mv₀, mv₁]
    constructor
    · exact fun h => hspl.meet x h.1 h.2
    · rintro (rfl | rfl)
      · exact ⟨T.start_mem_support, T'.end_mem_support⟩
      · exact ⟨T.end_mem_support, T'.start_mem_support⟩
  have hV₁₂ : (walkDrawing Γ T'.reverse).V ∩ (walkDrawing Γ Y).V = {a, b} := by
    ext x
    rw [mem_inter_iff, mv₁, mv₂]
    constructor
    · exact fun h => hY.meet x h.2 h.1
    · rintro (rfl | rfl)
      · exact ⟨T'.end_mem_support, Y.start_mem_support⟩
      · exact ⟨T'.start_mem_support, Y.end_mem_support⟩
  have hV₂₀ : (walkDrawing Γ Y).V ∩ (walkDrawing Γ T).V = {a, b} := by
    ext x
    rw [mem_inter_iff, mv₂, mv₀]
    constructor
    · exact fun h => hear.inner x h.2 ((hY.V x).mpr (Or.inl h.1))
    · rintro (rfl | rfl)
      · exact ⟨Y.start_mem_support, T.start_mem_support⟩
      · exact ⟨Y.end_mem_support, T.end_mem_support⟩
  have hE₀₁ : Disjoint (walkDrawing Γ T).E (walkDrawing Γ T'.reverse).E :=
    disjoint_left.mpr fun x h₁ h₂ => hspl.edge x ((me₀ x).mp h₁) ((me₁ x).mp h₂)
  have hE₁₂ : Disjoint (walkDrawing Γ T'.reverse).E (walkDrawing Γ Y).E :=
    disjoint_left.mpr fun x h₁ h₂ => hY.edge x ((me₂ x).mp h₂) ((me₁ x).mp h₁)
  have hE₂₀ : Disjoint (walkDrawing Γ Y).E (walkDrawing Γ T).E :=
    disjoint_left.mpr fun x h₁ h₂ =>
      hear.off x ((me₀ x).mp h₂) ((hY.E x).mpr (Or.inl ((me₂ x).mp h₁)))
  refine ⟨walkDrawing Γ T, walkDrawing Γ T'.reverse, walkDrawing Γ Y, a, b, hP₀, hP₁, hP₂, sP₀, sP₁,
    sP₂, hpos _, hpos _, ?_, hV₀₁, hV₁₂, hV₂₀, hE₀₁, hE₁₂, hE₂₀, ?_, ?_, ?_⟩
  · exact hpos _
  · refine Drawing.ext_of_V_E ?_ ?_
    · rw [Drawing.sup_V sP₀ sP₁]
      ext x
      rw [mem_union, mv₀, mv₁, hspl.V]
    · rw [Drawing.sup_E sP₀ sP₁]
      ext x
      rw [mem_union, me₀, me₁, hspl.E]
  · refine Drawing.ext_of_V_E ?_ ?_
    · rw [Drawing.sup_V sP₁ sP₂]
      ext x
      rw [mem_union, mv₁, mv₂, hY.V, or_comm]
    · rw [Drawing.sup_E sP₁ sP₂]
      ext x
      rw [mem_union, me₁, me₂, hY.E, or_comm]
  · have hcirc := Drawing.isCircuit_sup (Γ := Γ) hP₂ hP₀ sP₂ sP₀ hear.ne hV₂₀ hE₂₀
    refine circuit_eq_of_E hcirc h₃ (Drawing.sup_isSubdrawing _ _ _) s₃ ?_
    rw [Drawing.sup_E sP₂ sP₀]
    ext x
    rw [mem_union, me₂, me₀, hE]
    constructor
    · rintro (hx | hx)
      · refine Or.inr ⟨fun hx₁ => ?_, (hY.E x).mpr (Or.inl hx)⟩
        rcases (hspl.E x).mp hx₁ with h | h
        · exact hear.off x h ((hY.E x).mpr (Or.inl hx))
        · exact hY.edge x hx h
      · exact Or.inl ⟨(hspl.E x).mpr (Or.inl hx), hear.off x hx⟩
    · rintro (⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩)
      · exact Or.inr (((hspl.E x).mp hx₁).resolve_right fun h => hx₂ (hrest x h))
      · exact Or.inl (((hY.E x).mp hx₂).resolve_right fun h =>
          hx₁ ((hspl.E x).mpr (Or.inr h)))

end GraphMinor.GM11
