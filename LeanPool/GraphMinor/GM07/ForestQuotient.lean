/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.PullForest

/-!
# Identifying vertices of a forest

This is the combinatorial part of the proof of (4.5) of Graph Minors VII (page 223). There, `φ(H')`
is shown to be a forest from a shortest cyclic sequence of paths `P'_1, ..., P'_k` in distinct
components. We record this with a graph.

Let `X` be a set of vertices of a forest, let `f` identify some vertices of `X`, and let `c` name
the class of a vertex under paths. The graph `classGraph f c X` has a node for each value of `f`, a
node for each class, and for each `x` in `X` an edge from `f x`
to `c x`. A simple closed walk in it passes through distinct classes, which is what minimality of
`k` gives in the paper. If the graph after identifying is a forest, then `classGraph` is a forest
(`classGraph_forest`). Conversely, if `classGraph` is a forest
and `G` is a forest with the same classes on `X`, then the graph after identifying `G` is a forest
(`quotient_forest`). Since homotopic forests have the same classes on the boundary, this gives the
forest claim of (4.5).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

variable {α β β' γ κ : Type*}

/-- The graph with a node for each value of `f`, a node for each class, and an edge from `f x` to `c
x` for each `x` in `X`. -/
def classGraph (f : α → γ) (c : α → κ) (X : Set α) : Graph (γ ⊕ κ) α where
  vertexSet := univ
  IsLink x p q := x ∈ X ∧ ((p = .inl (f x) ∧ q = .inr (c x)) ∨ (p = .inr (c x) ∧ q = .inl (f x)))
  edgeSet := X
  isLink_symm _ _ := ⟨fun _ _ h => ⟨h.1, h.2.elim (fun h1 => .inr ⟨h1.2, h1.1⟩) (fun h1
    => .inl ⟨h1.2, h1.1⟩)⟩⟩
  eq_or_eq_of_isLink_of_isLink {e x y v w} h1 h2 := by
    rcases h1.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink e := ⟨fun he => ⟨_, _, he, .inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, h⟩ => h.1⟩
  left_mem_of_isLink _ _ _ _ := mem_univ _

/-- A walk of `classGraph` that ends at a value node turns into a walk of the graph after
identifying. Each class on the walk gives one path, and edges of different classes differ. -/
theorem class_walk {H : Graph γ β} {f : α → γ} {c : α → κ} {X : Set α} {t : β → κ}
    (hpath : ∀ x ∈ X, ∀ y ∈ X, c x = c y → x ≠ y → ∃ W : GraphWalk H (f x) (f y), 0 < W.length
      ∧ W.edges.Nodup ∧ ∀ e ∈ W.edges, t e = c x)
    {u v : γ ⊕ κ} (T : GraphWalk (classGraph f c X) u v) (hs : T.IsSimple) (hE : T.edges.Nodup)
      (b : γ) (hv : v = .inl b) (hb : b ∈ H.vertexSet) :
    (∀ a, u = .inl a → ∃ W : GraphWalk H a b, W.edges.Nodup ∧ ∀ e ∈ W.edges, Sum.inr
      (t e) ∈ T.support) ∧
    (∀ k, u = .inr k → ∀ x ∈ X, c x = k → x ∉ T.edges → ∃ W : GraphWalk H (f x) b, 0 < W.length
      ∧ W.edges.Nodup ∧ ∀ e ∈ W.edges, Sum.inr (t e) ∈ T.support) := by
  classical
  induction T with
  | nil _ =>
    subst hv
    refine ⟨fun a ha => ?_, fun k hk => ?_⟩
    · obtain rfl : b = a := Sum.inl.inj ha
      exact ⟨.nil hb, by simp [GraphWalk.edges], by simp [GraphWalk.edges]⟩
    · simp at hk
  | @cons u u' v y hl r ih =>
    have hnd := List.nodup_cons.mp hs
    have hnE := List.nodup_cons.mp hE
    obtain ⟨ihl, ihr⟩ := ih hnd.2 hnE.2 hv
    refine ⟨fun a ha => ?_, fun k hk x hx hxk hxE => ?_⟩
    · subst ha
      rcases hl.2 with ⟨h1, rfl⟩ | ⟨h1, -⟩
      · obtain rfl : a = f y := Sum.inl.inj h1
        obtain ⟨W, -, hN, hS⟩ := ihr (c y) rfl y hl.1 rfl hnE.1
        exact ⟨W, hN, fun e he => List.mem_cons_of_mem _ (hS e he)⟩
      · simp at h1
    · subst hk
      rcases hl.2 with ⟨h1, -⟩ | ⟨h1, rfl⟩
      · simp at h1
      · have hky : k = c y := Sum.inr.inj h1
        have hxy : x ≠ y := by
          rintro rfl
          exact hxE List.mem_cons_self
        obtain ⟨P, hP, hPn, hPt⟩ := hpath x hx y hl.1 (hxk.trans hky) hxy
        obtain ⟨W, hN, hS⟩ := ihl (f y) rfl
        refine ⟨P.append W, ?_, ?_, fun e he => ?_⟩
        · rw [GraphWalk.length_append]
          omega
        · rw [GraphWalk.edges_append]
          refine List.Nodup.append hPn hN fun e he he' => ?_
          have h2 := hS e he'
          rw [hPt e he, hxk] at h2
          exact hnd.1 h2
        · rw [GraphWalk.edges_append] at he
          rcases List.mem_append.mp he with h | h
          · rw [hPt e h, hxk]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hS e h)

/-- **From the forest after identifying to `classGraph`.** -/
theorem classGraph_forest {H : Graph γ β} {f : α → γ} {c : α → κ} {X : Set α} {t : β → κ}
  (hH : IsGraphForest H) (hV : ∀ x ∈ X, f x ∈ H.vertexSet)
    (hpath : ∀ x ∈ X, ∀ y ∈ X, c x = c y → x ≠ y → ∃ W : GraphWalk H (f x) (f y), 0 < W.length
      ∧ W.edges.Nodup ∧ ∀ e ∈ W.edges, t e = c x) : IsGraphForest (classGraph f c X) := by
  classical
  have key : ∀ (a : γ) (W : GraphWalk (classGraph f c X) (.inl a) (.inl a)), W.IsSimpleClosed
    → W.length = 0 := by
    intro a W hW
    cases W with
    | nil _ => rfl
    | @cons _ y _ x hl r =>
      exfalso
      have hrs : r.IsSimple := hW.1
      have hE := List.nodup_cons.mp hW.2
      rcases hl.2 with ⟨h1, rfl⟩ | ⟨h1, -⟩
      · obtain rfl : a = f x := Sum.inl.inj h1
        obtain ⟨-, h2⟩ := class_walk hpath r hrs hE.2 (f x) rfl (hV x hl.1)
        obtain ⟨W, hP, hN, -⟩ := h2 (c x) rfl x hl.1 rfl hE.1
        have := length_eq_zero_of_trail hH _ _ W rfl hN
        omega
      · simp at h1
  intro u W hW
  rcases u with a | k
  · exact key a W hW
  · cases W with
    | nil _ => rfl
    | @cons _ y _ x hl r =>
      exfalso
      rcases hl.2 with ⟨h1, -⟩ | ⟨h1, rfl⟩
      · simp at h1
      · have hl' : (classGraph f c X).IsLink x (.inr k) (.inl (f x)) := hl
        let W' : GraphWalk (classGraph f c X) (.inl (f x)) (.inl (f x)) := r.append (.cons hl'
          (.nil (mem_univ _)))
        have hW' : W'.IsSimpleClosed := by
          have hrs : r.support.Nodup := hW.1
          have hE := hW.2
          constructor
          · have h2 : W'.support.tail = r.support.tail ++ [Sum.inl (f x)] := by
              rw [GraphWalk.support_append, r.support_eq_cons, List.cons_append, List.tail_cons]
              rfl
            rw [h2]
            have hp : (r.support.tail ++ [Sum.inl (f x)]).Perm r.support := by
              rw [r.support_eq_cons, List.tail_cons]
              exact List.perm_append_singleton _ _
            exact hp.nodup_iff.mpr hrs
          · have h2 : W'.edges = r.edges ++ [x] := by
              rw [GraphWalk.edges_append]
              rfl
            rw [h2]
            exact (List.perm_append_singleton _ _).nodup_iff.mpr hE
        have h0 := key _ W' hW'
        have h1' : W'.length = r.length + 1 := by
          rw [GraphWalk.length_append]
          rfl
        omega

/-- The graph `G` with a new node for each value of `f` on `X`, and an edge from `x` to the node `f
x`. A walk may jump from `x` to another point of its fiber through this node. -/
def starGraph (G : Graph α β) (f : α → γ) (X : Set α) : Graph (α ⊕ γ) (β ⊕ α) where
  vertexSet := univ
  IsLink e p q := match e with
    | .inl e => ∃ u v, p = .inl u ∧ q = .inl v ∧ G.IsLink e u v
    | .inr x => x ∈ X ∧ ((p = .inl x ∧ q = .inr (f x)) ∨ (p = .inr (f x) ∧ q = .inl x))
  edgeSet := {e | match e with
    | .inl e => e ∈ G.edgeSet
    | .inr x => x ∈ X}
  isLink_symm e _ := ⟨fun a b h => by
    rcases e with e | x
    · obtain ⟨u, v, rfl, rfl, h⟩ := h
      exact ⟨v, u, rfl, rfl, h.symm⟩
    · exact ⟨h.1, h.2.elim (fun h1 => .inr ⟨h1.2, h1.1⟩) (fun h1 => .inl ⟨h1.2, h1.1⟩)⟩⟩
  eq_or_eq_of_isLink_of_isLink {e x y v w} h1 h2 := by
    rcases e with e | x'
    · obtain ⟨u, u', rfl, rfl, h⟩ := h1
      obtain ⟨a, a', rfl, rfl, h'⟩ := h2
      rcases G.eq_or_eq_of_isLink_of_isLink h h' with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
    · rcases h1.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink e := by
    rcases e with e | x
    · constructor
      · intro he
        obtain ⟨u, v, h⟩ := (G.edge_mem_iff_exists_isLink e).mp he
        exact ⟨_, _, u, v, rfl, rfl, h⟩
      · rintro ⟨_, _, u, v, -, -, h⟩
        exact (G.edge_mem_iff_exists_isLink e).mpr ⟨u, v, h⟩
    · exact ⟨fun he => ⟨_, _, he, .inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, h⟩ => h.1⟩
  left_mem_of_isLink _ _ _ _ := mem_univ _

/-- The node of `classGraph` for a node of `starGraph`. -/
def starNode (c : α → κ) : α ⊕ γ → γ ⊕ κ
  | .inl v => .inr (c v)
  | .inr z => .inl z

/-- Collapsing the edges of `G` maps a walk of `starGraph` to a walk of `classGraph`, keeping the
labels of the new edges. -/
theorem star_collapse {G : Graph α β} {f : α → γ} {c : α → κ} {X : Set α}
  (hc : ∀ e p q, G.IsLink e p q → c p = c q) {u v : α ⊕ γ} (T : GraphWalk (starGraph G f X) u v) :
    ∃ W : GraphWalk (classGraph f c X) (starNode c u) (starNode c v), W.edges = T.edges.filterMap
      (fun e => e.elim (fun _ => none) some) := by
  induction T with
  | nil _ => exact ⟨.nil (mem_univ _), rfl⟩
  | @cons a b d e hl r ih =>
    obtain ⟨W, hW⟩ := ih
    rcases e with e | x
    · obtain ⟨p, q, rfl, rfl, h⟩ := hl
      have hcq : c p = c q := hc e p q h
      rw [show starNode c (.inl p) = starNode c (.inl q) by simp [starNode, hcq]]
      exact ⟨W, by rw [hW]; rfl⟩
    · refine ⟨GraphWalk.cons (e := x) ?_ W, ?_⟩
      · rcases hl.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hl.1, .inr ⟨rfl, rfl⟩⟩
        · exact ⟨hl.1, .inl ⟨rfl, rfl⟩⟩
      · change x :: W.edges = _
        rw [hW]
        rfl

/-- A walk of `starGraph` from a vertex of `G` with no new edge is a walk of `G`. -/
theorem star_no_jump {G : Graph α β} {f : α → γ} {X : Set α} {p q : α ⊕ γ} (T : GraphWalk
  (starGraph G f X) p q) (hT : ∀ x, Sum.inr x ∉ T.edges) (u : α) (hu : u ∈ G.vertexSet) (hp : p
    = .inl u) :
    ∃ (v : α) (W : GraphWalk G u v), q = .inl v ∧ T.edges = W.edges.map Sum.inl := by
  induction T generalizing u with
  | @nil p' hv =>
    subst hp
    exact ⟨u, .nil hu, rfl, rfl⟩
  | @cons a b d e hl r ih =>
    subst hp
    rcases e with e | x
    · obtain ⟨p, q', hp, rfl, h⟩ := hl
      obtain rfl : u = p := Sum.inl.inj hp
      obtain ⟨v, W, hv, hE⟩ := ih (fun x hx => hT x (List.mem_cons_of_mem _ hx)) q' h.right_mem rfl
      exact ⟨v, .cons h W, hv, by simp [GraphWalk.edges, hE]⟩
    · exact (hT x List.mem_cons_self).elim

/-- **From `classGraph` back to the forest after identifying.** Let `P` be the graph after
identifying the vertices of `G`, so that each link of `P` lifts to a link of `G`, and let `G` be a
forest with `c` constant along its edges. If two vertices in one fiber
are distinct then they lie in `X`. A circuit of `P` lifts to a closed walk of `starGraph` with
distinct edges, which collapses to a closed walk of `classGraph` with distinct edges. -/
theorem quotient_forest {G : Graph α β} {P : Graph γ β'} {f : α → γ} {c : α → κ} {X : Set α} {ι : β
  → β'} (hG : IsGraphForest G) (hB : IsGraphForest (classGraph f c X))
    (hc : ∀ e p q, G.IsLink e p q → c p = c q)
    (hlift : ∀ e a b, P.IsLink e a b → ∃ e' p q, G.IsLink e' p q ∧ f p = a ∧ f q = b ∧ ι e' = e)
    (hjump : ∀ p ∈ G.vertexSet, ∀ q ∈ G.vertexSet, f p = f q → p ≠ q → p ∈ X
      ∧ q ∈ X) : IsGraphForest P := by
  classical
  have hstar : ∀ (u : α ⊕ γ) (T : GraphWalk (starGraph G f X) u u), T.edges.Nodup → T.length = 0
    := by
    intro u T hT
    obtain ⟨W, hW⟩ := star_collapse hc T (f := f)
    have hnd : W.edges.Nodup := by
      rw [hW]
      refine List.Nodup.filterMap ?_ hT
      rintro (e | x) (e' | x') y hy hy'
      · simp at hy
      · simp at hy
      · simp at hy'
      · simp only [Sum.elim_inr, Option.mem_def, Option.some.injEq] at hy hy'
        rw [hy, hy']
    have h0 := length_eq_zero_of_trail hB _ _ W rfl hnd
    have hno : ∀ x, Sum.inr x ∉ T.edges := fun x hx => by
      have hm : x ∈ W.edges := by
        rw [hW]
        exact List.mem_filterMap.mpr ⟨_, hx, rfl⟩
      have : W.edges = [] := List.length_eq_zero_iff.mp h0
      rw [this] at hm
      simp at hm
    rcases u with u | z
    · have hu : u ∈ G.vertexSet ∨ T.length = 0 := by
        cases T with
        | nil _ => exact .inr rfl
        | @cons _ b _ e hl r =>
          rcases e with e | x
          · obtain ⟨p, q, hp, -, h⟩ := hl
            exact .inl (Sum.inl.inj hp ▸ h.left_mem)
          · exact (hno x List.mem_cons_self).elim
      rcases hu with hu | hu
      swap
      · exact hu
      obtain ⟨v, W', hv, hE⟩ := star_no_jump T hno u hu rfl
      obtain rfl : u = v := Sum.inl.inj hv
      have hnd' : W'.edges.Nodup := by
        rw [hE] at hT
        exact List.Nodup.of_map _ hT
      have h1 := length_eq_zero_of_trail hG _ _ W' rfl hnd'
      change T.edges.length = 0
      rw [hE, List.length_map]
      exact h1
    · cases T with
      | nil _ => rfl
      | @cons _ b _ e hl r =>
        rcases e with e | x
        · obtain ⟨p, q, hp, -, -⟩ := hl
          simp at hp
        · exact (hno x List.mem_cons_self).elim
  have hlw : ∀ {a b : γ} (r : GraphWalk P a b), r.IsSimple → r.edges.Nodup → ∀ p ∈ G.vertexSet, f p
    = a → ∃ q ∈ G.vertexSet, f q = b ∧ ∃ T : GraphWalk (starGraph G f X) (.inl p) (.inl q),
      T.edges.Nodup ∧ (∀ x, Sum.inr x ∈ T.edges → f x ∈ r.support ∧ f x ≠ b)
        ∧ ∀ e', Sum.inl e' ∈ T.edges → ι e' ∈ r.edges := by
    intro a b r
    induction r with
    | nil _ =>
      intro _ _ p hp hf
      exact ⟨p, hp, hf, .nil (mem_univ _), by simp [GraphWalk.edges], by simp [GraphWalk.edges],
        by simp [GraphWalk.edges]⟩
    | @cons a a' b e hl r ih =>
      intro hs hE p hp hfp
      have hnd := List.nodup_cons.mp hs
      have hnE := List.nodup_cons.mp hE
      obtain ⟨e', p₁, q₁, hl', hp₁, hq₁, hι⟩ := hlift e a a' hl
      obtain ⟨q, hq, hfq, T, hTn, hTs, hTe⟩ := ih hnd.2 hnE.2 q₁ hl'.right_mem hq₁
      have hlk : (starGraph G f X).IsLink (.inl e') (.inl p₁) (.inl q₁) := ⟨p₁, q₁, rfl, rfl, hl'⟩
      have hstep : Sum.inl e' ∉ T.edges := fun h => hnE.1 (hι ▸ hTe e' h)
      have hba : a ≠ b := fun h => hnd.1 (h ▸ r.end_mem_support)
      by_cases hpp : p = p₁
      · subst hpp
        refine ⟨q, hq, hfq, .cons hlk T, List.nodup_cons.mpr ⟨hstep, hTn⟩, fun x hx => ?_,
          fun e'' he'' => ?_⟩
        · rcases List.mem_cons.mp hx with h | h
          · simp at h
          · exact ⟨List.mem_cons_of_mem _ (hTs x h).1, (hTs x h).2⟩
        · rcases List.mem_cons.mp he'' with h | h
          · rw [Sum.inl.inj h, hι]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hTe e'' h)
      · obtain ⟨hpX, hp₁X⟩ := hjump p hp p₁ hl'.left_mem (hfp.trans hp₁.symm) hpp
        have h1 : (starGraph G f X).IsLink (.inr p) (.inl p) (.inr a) :=
          ⟨hpX, .inl ⟨rfl, by rw [hfp]⟩⟩
        have h2 : (starGraph G f X).IsLink (.inr p₁) (.inr a) (.inl p₁)
          := ⟨hp₁X, .inr ⟨by rw [hp₁], rfl⟩⟩
        have hout : ∀ x, f x = a → Sum.inr x ∉ T.edges := fun x hx h => hnd.1 (hx ▸ (hTs x h).1)
        refine ⟨q, hq, hfq, .cons h1 (.cons h2 (.cons hlk T)), ?_, fun x hx => ?_,
          fun e'' he'' => ?_⟩
        · simp only [GraphWalk.edges, List.nodup_cons, List.mem_cons, Sum.inr.injEq,
            reduceCtorEq, false_or, not_or]
          exact ⟨⟨hpp, hout p hfp⟩, hout p₁ hp₁, hstep, hTn⟩
        · simp only [GraphWalk.edges, List.mem_cons, Sum.inr.injEq, reduceCtorEq, false_or] at hx
          rcases hx with rfl | rfl | h
          · exact ⟨hfp ▸ List.mem_cons_self, hfp ▸ hba⟩
          · exact ⟨hp₁ ▸ List.mem_cons_self, hp₁ ▸ hba⟩
          · exact ⟨List.mem_cons_of_mem _ (hTs x h).1, (hTs x h).2⟩
        · simp only [GraphWalk.edges, List.mem_cons, reduceCtorEq, false_or] at he''
          rcases he'' with h | h
          · rw [Sum.inl.inj h, hι]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hTe e'' h)
  intro a W hW
  cases W with
  | nil _ => rfl
  | @cons _ a' _ e hl r =>
    exfalso
    have hE := List.nodup_cons.mp hW.2
    obtain ⟨e', p₀, q₀, hl', hp₀, hq₀, hι⟩ := hlift e a a' hl
    obtain ⟨q, hq, hfq, T, hTn, hTs, hTe⟩ := hlw r hW.1 hE.2 q₀ hl'.right_mem hq₀
    have hlk : (starGraph G f X).IsLink (.inl e') (.inl p₀) (.inl q₀) := ⟨p₀, q₀, rfl, rfl, hl'⟩
    have hstep : Sum.inl e' ∉ T.edges := fun h => hE.1 (hι ▸ hTe e' h)
    by_cases hqp : q = p₀
    · subst hqp
      have := hstar _ (.cons hlk T) (List.nodup_cons.mpr ⟨hstep, hTn⟩)
      simp [GraphWalk.length, GraphWalk.edges] at this
    · obtain ⟨hqX, hpX⟩ := hjump q hq p₀ hl'.left_mem (hfq.trans hp₀.symm) hqp
      have h1 : (starGraph G f X).IsLink (.inr q) (.inl q) (.inr a) :=
        ⟨hqX, .inl ⟨rfl, by rw [hfq]⟩⟩
      have h2 : (starGraph G f X).IsLink (.inr p₀) (.inr a) (.inl p₀)
        := ⟨hpX, .inr ⟨by rw [hp₀], rfl⟩⟩
      have hout : ∀ x, f x = a → Sum.inr x ∉ T.edges := fun x hx h => (hTs x h).2 hx
      let C : GraphWalk (starGraph G f X) (.inl p₀) (.inl p₀) := (GraphWalk.cons hlk T).append
        (.cons h1 (.cons h2 (.nil (mem_univ _))))
      have hCe : C.edges = (Sum.inl e' :: T.edges) ++ [Sum.inr q, Sum.inr p₀] := by
        rw [GraphWalk.edges_append]
        rfl
      have hC : C.edges.Nodup := by
        rw [hCe]
        refine List.Nodup.append (List.nodup_cons.mpr ⟨hstep, hTn⟩) (by simp [hqp]) fun x hx hx'
          => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
        rcases hx' with rfl | rfl
        · rcases hx with h | h
          · simp at h
          · exact hout q hfq h
        · rcases hx with h | h
          · simp at h
          · exact hout p₀ hp₀ h
      have := hstar _ C hC
      rw [GraphWalk.length_append] at this
      simp [GraphWalk.length, GraphWalk.edges] at this

end GraphMinor.GM07
