/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs

/-!
# Walks, paths and circuits of drawings

Graph Minors XI uses freely the elementary facts about walks, paths and circuits of a drawing. This
file proves those we need:

- a subdrawing is determined by its vertices and edges (`Drawing.ext_of_V_E`), and the point set
  of a drawing is the union of its vertices and the closures of its edges (`Drawing.U_eq`);
- a subdrawing has the same links as the drawing (`Drawing.isLink_iff_of_isSubdrawing`), so walks
  pass to subdrawings (`GraphWalk.exists_transfer`);
- splitting a walk at a vertex, and rotating a closed walk;
- two internally disjoint paths with the same ends form a circuit (`Drawing.isCircuit_sup`), and
  two vertices split a circuit into two such paths (`Drawing.IsCircuit.exists_two_paths`).
-/

public section

namespace GraphMinor.Surface

open Set Topology Graph

universe u

variable {S : Type u} [TopologicalSpace S]

namespace GraphWalk

variable {α : Type u} {β : Type*} {G G' : Graph α β}

@[simp] theorem support_nil {v : α} (h : v ∈ V(G)) : (GraphWalk.nil h).support = [v] := rfl
@[simp] theorem edges_nil {v : α} (h : v ∈ V(G)) : (GraphWalk.nil h).edges = [] := rfl
@[simp] theorem support_cons {u v w : α} {e : β} (h : G.IsLink e u v) (r : GraphWalk G v w) :
    (GraphWalk.cons h r).support = u :: r.support := rfl
@[simp] theorem edges_cons {u v w : α} {e : β} (h : G.IsLink e u v) (r : GraphWalk G v w) :
    (GraphWalk.cons h r).edges = e :: r.edges := rfl
@[simp] theorem length_nil {v : α} (h : v ∈ V(G)) : (GraphWalk.nil h).length = 0 := rfl
@[simp] theorem length_cons {u v w : α} {e : β} (h : G.IsLink e u v) (r : GraphWalk G v w) :
    (GraphWalk.cons h r).length = r.length + 1 := by
  simp [length]

theorem start_mem_support {u v : α} (W : GraphWalk G u v) : u ∈ W.support := by
  cases W <;> simp

theorem end_mem_support {u v : α} (W : GraphWalk G u v) : v ∈ W.support := by
  induction W with
  | nil h => simp
  | cons h r ih => simp [ih]

theorem support_ne_nil {u v : α} (W : GraphWalk G u v) : W.support ≠ [] :=
  List.ne_nil_of_mem W.start_mem_support

theorem head_support {u v : α} (W : GraphWalk G u v) : W.support.head W.support_ne_nil = u := by
  cases W <;> simp

theorem support_eq_cons {u v : α} (W : GraphWalk G u v) : W.support = u :: W.support.tail := by
  cases W <;> simp

theorem mem_vertexSet_of_mem_support {u v : α} (W : GraphWalk G u v) {x : α}
    (hx : x ∈ W.support) : x ∈ V(G) := by
  induction W with
  | nil h =>
    simp only [support_nil, List.mem_singleton] at hx
    exact hx ▸ h
  | cons h r ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.left_mem
    · exact ih hx

theorem support_append {u v w : α} (W : GraphWalk G u v) (W' : GraphWalk G v w) :
    (W.append W').support = W.support ++ W'.support.tail := by
  induction W with
  | nil h =>
    change W'.support = _
    exact W'.support_eq_cons
  | cons h r ih => simp [append, ih]

theorem edges_append {u v w : α} (W : GraphWalk G u v) (W' : GraphWalk G v w) :
    (W.append W').edges = W.edges ++ W'.edges := by
  induction W with
  | nil h => rfl
  | cons h r ih => simp [append, ih]

theorem mem_support_append {u v w x : α} (W : GraphWalk G u v) (W' : GraphWalk G v w) :
    x ∈ (W.append W').support ↔ x ∈ W.support ∨ x ∈ W'.support := by
  rw [support_append, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_tail h)
  · rintro (h | h)
    · exact Or.inl h
    · rw [W'.support_eq_cons] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl W.end_mem_support
      · exact Or.inr h

theorem eq_of_length_eq_zero {u v : α} {W : GraphWalk G u v} (h : W.length = 0) : u = v := by
  cases W with
  | nil _ => rfl
  | cons h' r => simp at h

theorem length_append {u v w : α} (W : GraphWalk G u v) (W' : GraphWalk G v w) :
    (W.append W').length = W.length + W'.length := by
  simp [length, edges_append]

theorem support_reverse {u v : α} (W : GraphWalk G u v) : W.reverse.support = W.support.reverse
  := by
  induction W with
  | nil h => rfl
  | cons h r ih => simp [reverse, support_append, ih]

theorem edges_reverse {u v : α} (W : GraphWalk G u v) : W.reverse.edges = W.edges.reverse := by
  induction W with
  | nil h => rfl
  | cons h r ih => simp [reverse, edges_append, ih]

theorem length_reverse {u v : α} (W : GraphWalk G u v) : W.reverse.length = W.length := by
  simp [length, edges_reverse]

/-- A walk can be split at any of its vertices. -/
theorem exists_append_of_mem {u v x : α} (W : GraphWalk G u v) (hx : x ∈ W.support) :
    ∃ (W₁ : GraphWalk G u x) (W₂ : GraphWalk G x v), W = W₁.append W₂ := by
  induction W with
  | nil h =>
    simp only [support_nil, List.mem_singleton] at hx
    subst hx
    exact ⟨.nil h, .nil h, rfl⟩
  | cons h r ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨.nil h.left_mem, .cons h r, rfl⟩
    · obtain ⟨W₁, W₂, rfl⟩ := ih hx
      exact ⟨.cons h W₁, W₂, rfl⟩

/-- The ends of an edge of a walk are vertices of the walk. -/
theorem left_mem_support_of_mem_edges {u v : α} (W : GraphWalk G u v) {e : β} (he : e ∈ W.edges)
    {x y : α} (hl : G.IsLink e x y) : x ∈ W.support := by
  induction W with
  | nil h => simp at he
  | cons h r ih =>
    rcases List.mem_cons.mp he with rfl | he
    · rcases hl.left_eq_or_eq h with rfl | rfl
      · simp
      · simp [r.start_mem_support]
    · simp [ih he]

theorem IsSimple.of_cons {u v w : α} {e : β} {h : G.IsLink e u v} {r : GraphWalk G v w}
    (hW : (GraphWalk.cons h r).IsSimple) : r.IsSimple :=
  (List.nodup_cons.mp hW).2

theorem IsSimple.edges_nodup {u v : α} {W : GraphWalk G u v} (hW : W.IsSimple) : W.edges.Nodup := by
  induction W with
  | nil h => simp
  | cons h r ih =>
    refine List.nodup_cons.mpr ⟨fun he => ?_, ih hW.of_cons⟩
    exact (List.nodup_cons.mp hW).1 (r.left_mem_support_of_mem_edges he h)

theorem IsSimple.reverse {u v : α} {W : GraphWalk G u v} (hW : W.IsSimple) : W.reverse.IsSimple
  := by
  unfold GraphWalk.IsSimple at *
  rw [support_reverse]
  exact List.nodup_reverse.mpr hW

/-- A simple walk with equal ends has length zero. -/
theorem IsSimple.length_eq_zero {u : α} {W : GraphWalk G u u} (hW : W.IsSimple) : W.length = 0 := by
  cases W with
  | nil h => rfl
  | cons h r => exact absurd r.end_mem_support (List.nodup_cons.mp hW).1

/-- Walks pass to a graph that has the links used by the walk. -/
theorem exists_transfer {u v : α} (W : GraphWalk G u v)
    (hl : ∀ e x y, e ∈ W.edges → G.IsLink e x y → G'.IsLink e x y)
    (hV : ∀ x ∈ W.support, x ∈ V(G')) :
    ∃ W' : GraphWalk G' u v, W'.support = W.support ∧ W'.edges = W.edges := by
  induction W with
  | nil h => exact ⟨.nil (hV _ (by simp)), rfl, rfl⟩
  | cons h r ih =>
    obtain ⟨W', hs, he⟩ := ih (fun e x y he hxy => hl e x y (by simp [he]) hxy)
      (fun x hx => hV x (by simp [hx]))
    exact ⟨.cons (hl _ _ _ (by simp) h) W', by simp [hs], by simp [he]⟩

/-- `W₁ + W₂` is simple-closed if `W₁` from `a` to `b` and `W₂` from `b` to `a` are simple and
have only their ends and no edge in common. -/
theorem isSimpleClosed_append {a b : α} {W₁ : GraphWalk G a b} {W₂ : GraphWalk G b a}
    (h₁ : W₁.IsSimple) (h₂ : W₂.IsSimple)
    (hV : ∀ x, x ∈ W₁.support → x ∈ W₂.support → x = a ∨ x = b)
    (hE : ∀ e, e ∈ W₁.edges → e ∉ W₂.edges) : (W₁.append W₂).IsSimpleClosed := by
  constructor
  · rw [support_append, W₁.support_eq_cons, List.cons_append, List.tail_cons]
    have ht₁ : W₁.support.tail.Nodup := List.Nodup.tail h₁
    have ht₂ : W₂.support.tail.Nodup := List.Nodup.tail h₂
    refine List.nodup_append.mpr ⟨ht₁, ht₂, ?_⟩
    intro x hx y hy hxy
    subst hxy
    have hx' : x ∈ W₁.support := by
      rw [W₁.support_eq_cons]
      exact List.mem_cons_of_mem _ hx
    have hx₂ : x ∈ W₂.support := by
      rw [W₂.support_eq_cons]
      exact List.mem_cons_of_mem _ hy
    rcases hV x hx' hx₂ with rfl | rfl
    · have h : W₁.support.Nodup := h₁
      rw [W₁.support_eq_cons] at h
      exact (List.nodup_cons.mp h).1 hx
    · have h : W₂.support.Nodup := h₂
      rw [W₂.support_eq_cons] at h
      exact (List.nodup_cons.mp h).1 hy
  · rw [edges_append]
    exact List.nodup_append.mpr ⟨h₁.edges_nodup, h₂.edges_nodup, fun e he f hf hef =>
      hE e he (hef ▸ hf)⟩

/-- Split a simple closed walk at two distinct vertices. The two pieces preserve the support
and edges, and their tails and edge lists are jointly nodup. -/
theorem exists_circuit_split {u a b : α} (W : GraphWalk G u u)
    (hnd : W.support.tail.Nodup) (hed : W.edges.Nodup)
    (ha : a ∈ W.support) (hb : b ∈ W.support) (hab : a ≠ b) :
    ∃ (R₁ : GraphWalk G a b) (R₂ : GraphWalk G b a),
      R₁.IsSimple ∧ R₂.IsSimple ∧ (R₁.support.tail ++ R₂.support.tail).Nodup ∧
      (R₁.edges ++ R₂.edges).Nodup ∧
      (∀ x, x ∈ (R₁.append R₂).support ↔ x ∈ W.support) ∧
      (∀ e, e ∈ (R₁.append R₂).edges ↔ e ∈ W.edges) := by
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem ha
  set Rot := W₂.append W₁ with hRot
  have hmemRot : ∀ x, x ∈ Rot.support ↔ x ∈ (W₁.append W₂).support := by
    intro x
    rw [hRot, GraphWalk.mem_support_append, GraphWalk.mem_support_append, or_comm]
  have hmemE : ∀ e, e ∈ Rot.edges ↔ e ∈ (W₁.append W₂).edges := by
    intro e
    rw [hRot, GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append,
      or_comm]
  have htail : Rot.support.tail.Nodup := by
    have h1 : (W₁.append W₂).support.tail = W₁.support.tail ++ W₂.support.tail := by
      rw [GraphWalk.support_append, W₁.support_eq_cons]; simp
    have h2 : Rot.support.tail = W₂.support.tail ++ W₁.support.tail := by
      rw [hRot, GraphWalk.support_append, W₂.support_eq_cons]; simp
    rw [h2]
    rw [h1] at hnd
    exact (List.perm_append_comm.nodup_iff).mp hnd
  have hedRot : Rot.edges.Nodup := by
    rw [hRot, GraphWalk.edges_append]
    rw [GraphWalk.edges_append] at hed
    exact (List.perm_append_comm.nodup_iff).mp hed
  obtain ⟨R₁, R₂, hR⟩ := Rot.exists_append_of_mem ((hmemRot b).mpr hb)
  have htail' : (R₁.support.tail ++ R₂.support.tail).Nodup := by
    have : Rot.support.tail = R₁.support.tail ++ R₂.support.tail := by
      rw [hR, GraphWalk.support_append, R₁.support_eq_cons]; simp
    rwa [this] at htail
  have hdisjT := List.nodup_append.mp htail'
  have hbt₁ : b ∈ R₁.support.tail := by
    have h := R₁.end_mem_support
    rw [R₁.support_eq_cons] at h
    exact (List.mem_cons.mp h).resolve_left hab.symm
  have hat₂ : a ∈ R₂.support.tail := by
    have h := R₂.end_mem_support
    rw [R₂.support_eq_cons] at h
    exact (List.mem_cons.mp h).resolve_left hab
  have hS₁ : R₁.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [R₁.support_eq_cons]
    exact List.nodup_cons.mpr ⟨fun h => hdisjT.2.2 a h a hat₂ rfl, hdisjT.1⟩
  have hS₂ : R₂.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [R₂.support_eq_cons]
    exact List.nodup_cons.mpr ⟨fun h => hdisjT.2.2 b hbt₁ b h rfl, hdisjT.2.1⟩
  have hedR : (R₁.edges ++ R₂.edges).Nodup := by
    rw [hR, GraphWalk.edges_append] at hedRot
    exact hedRot
  refine ⟨R₁, R₂, hS₁, hS₂, htail', hedR, ?_, ?_⟩
  · simpa only [← hR] using hmemRot
  · simpa only [← hR] using hmemE

/-- Lift two simple paths with matching ends to a simple closed walk in one graph. -/
theorem isSimpleClosed_append_of_lifts {H K : Graph α β} {a b : α}
    {W₁ : GraphWalk H a b} {W₂ : GraphWalk K a b} {X₁ : GraphWalk G a b} {X₂ : GraphWalk G b a}
    (hW₁ : W₁.IsSimple) (hW₂ : W₂.IsSimple)
    (hs₁ : X₁.support = W₁.support) (hs₂ : X₂.support = W₂.reverse.support)
    (he₁ : X₁.edges = W₁.edges) (he₂ : X₂.edges = W₂.reverse.edges)
    (hV : {x | x ∈ W₁.support} ∩ {x | x ∈ W₂.support} = {a, b})
    (hE : Disjoint {e | e ∈ W₁.edges} {e | e ∈ W₂.edges}) :
    (X₁.append X₂).IsSimpleClosed := by
  have hX₁ : X₁.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₁]; exact hW₁
  have hX₂ : X₂.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₂]; exact hW₂.reverse
  apply isSimpleClosed_append hX₁ hX₂
  · intro x hx₁ hx₂
    rw [hs₁] at hx₁
    rw [hs₂, support_reverse, List.mem_reverse] at hx₂
    have hx : x ∈ {x | x ∈ W₁.support} ∩ {x | x ∈ W₂.support} := ⟨hx₁, hx₂⟩
    rwa [hV] at hx
  · intro e he₁' he₂'
    rw [he₁] at he₁'
    rw [he₂, edges_reverse, List.mem_reverse] at he₂'
    exact Set.disjoint_left.mp hE he₁' he₂'

end GraphWalk

namespace Drawing

variable (Γ : Drawing S)

/-- Every point of `U(Γ)` outside `V(Γ)` lies on an edge. -/
theorem exists_edge_of_mem {x : S} (hx : x ∈ Γ.U) (hxV : x ∉ Γ.V) : ∃ e ∈ Γ.E, x ∈ e := by
  have hxF : x ∈ Γ.U \ Γ.V := ⟨hx, hxV⟩
  refine ⟨pathComponentIn (Γ.U \ Γ.V) x, ⟨⟨x, mem_pathComponentIn_self hxF⟩,
    pathComponentIn_subset, isPathConnected_pathComponentIn hxF, ?_⟩,
    mem_pathComponentIn_self hxF⟩
  intro D hD hconn hsub
  exact subset_antisymm (hconn.subset_pathComponentIn (hsub (mem_pathComponentIn_self hxF)) hD) hsub

/-- `U(Γ)` is the union of `V(Γ)` and the closures of the edges. -/
theorem U_eq : Γ.U = Γ.V ∪ ⋃ e ∈ Γ.E, closure e := by
  apply subset_antisymm
  · intro x hx
    by_cases hxV : x ∈ Γ.V
    · exact Or.inl hxV
    · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hx hxV
      exact Or.inr (mem_iUnion₂.mpr ⟨e, he, subset_closure hxe⟩)
  · refine union_subset Γ.V_subset_U (iUnion₂_subset fun e he => Γ.closure_subset_U he)

variable {Γ}

/-- A drawing is determined by its vertices and edges. -/
theorem ext_of_V_E {Γ₁ Γ₂ : Drawing S} (hV : Γ₁.V = Γ₂.V) (hE : Γ₁.E = Γ₂.E) : Γ₁ = Γ₂ := by
  have hU : Γ₁.U = Γ₂.U := by rw [Γ₁.U_eq, Γ₂.U_eq, hV, hE]
  cases Γ₁
  cases Γ₂
  simp only at hU hV
  subst hU hV
  rfl

theorem IsSubdrawing.refl (Γ : Drawing S) : Γ.IsSubdrawing Γ := ⟨subset_rfl, subset_rfl⟩

theorem IsSubdrawing.trans {Γ₁ Γ₂ Γ₃ : Drawing S} (h₁ : Γ₁.IsSubdrawing Γ₂)
    (h₂ : Γ₂.IsSubdrawing Γ₃) : Γ₁.IsSubdrawing Γ₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem IsSubdrawing.U_subset {Γ₁ Γ₂ : Drawing S} (h : Γ₁.IsSubdrawing Γ₂) : Γ₁.U ⊆ Γ₂.U := by
  rw [Γ₁.U_eq, Γ₂.U_eq]
  exact union_subset_union h.1 (biUnion_subset_biUnion_left h.2)

/-- An edge of a subdrawing has the same ends in the subdrawing as in the drawing. -/
theorem IsSubdrawing.closure_inter_V {Γ₁ Γ₂ : Drawing S} (h : Γ₁.IsSubdrawing Γ₂) {e : Set S}
    (he : e ∈ Γ₁.E) : closure e ∩ Γ₁.V = closure e ∩ Γ₂.V := by
  have h₁ := Γ₁.closure_diff_V he
  have h₂ := Γ₂.closure_diff_V (h.2 he)
  ext x
  constructor
  · rintro ⟨hx, hxV⟩
    exact ⟨hx, h.1 hxV⟩
  · rintro ⟨hx, hxV⟩
    refine ⟨hx, ?_⟩
    by_contra hx₁
    have : x ∈ e := by rw [← h₁]; exact ⟨hx, hx₁⟩
    exact (by rw [← h₂] at this; exact this.2 : x ∉ Γ₂.V) hxV

theorem IsSubdrawing.isLink_iff {Γ₁ Γ₂ : Drawing S} (h : Γ₁.IsSubdrawing Γ₂) {e : Set S}
    (he : e ∈ Γ₁.E) {x y : S} : Γ₁.toGraph.IsLink e x y ↔ Γ₂.toGraph.IsLink e x y := by
  constructor
  · rintro ⟨_, hx, hy, hc⟩
    exact ⟨h.2 he, h.1 hx, h.1 hy, by rw [← h.closure_inter_V he, hc]⟩
  · rintro ⟨_, _, _, hc⟩
    have hc' : closure e ∩ Γ₁.V = {x, y} := by rw [h.closure_inter_V he, hc]
    have hx : x ∈ closure e ∩ Γ₁.V := by rw [hc']; simp
    have hy : y ∈ closure e ∩ Γ₁.V := by rw [hc']; simp
    exact ⟨he, hx.2, hy.2, hc'⟩

/-- The graph of a subdrawing is a subgraph of the graph of the drawing. -/
theorem IsSubdrawing.toGraph_le {Γ₁ Γ₂ : Drawing S} (h : Γ₁.IsSubdrawing Γ₂) :
    Γ₁.toGraph ≤ Γ₂.toGraph :=
  ⟨h.1, fun _ _ _ he => (h.isLink_iff he.1).mp he⟩

theorem toGraph_isLink_mem {Γ : Drawing S} {e : Set S} {x y : S} (h : Γ.toGraph.IsLink e x y) :
    e ∈ Γ.E := h.1

/-- A walk of a subdrawing is a walk of the drawing. -/
theorem IsSubdrawing.exists_walk_up {Γ₁ Γ₂ : Drawing S} (h : Γ₁.IsSubdrawing Γ₂) {u v : S}
    (W : GraphWalk Γ₁.toGraph u v) :
    ∃ W' : GraphWalk Γ₂.toGraph u v, W'.support = W.support ∧ W'.edges = W.edges :=
  W.exists_transfer (fun _ _ _ _ hl => (h.isLink_iff hl.1).mp hl)
    (fun _ hx => h.1 (W.mem_vertexSet_of_mem_support hx))

/-- A walk of the drawing, with its vertices and edges in a subdrawing, is a walk of the
subdrawing. -/
theorem IsSubdrawing.exists_walk_down {Γ₁ Γ₂ : Drawing S} (h : Γ₁.IsSubdrawing Γ₂) {u v : S}
    (W : GraphWalk Γ₂.toGraph u v) (hV : ∀ x ∈ W.support, x ∈ Γ₁.V)
    (hE : ∀ e ∈ W.edges, e ∈ Γ₁.E) :
    ∃ W' : GraphWalk Γ₁.toGraph u v, W'.support = W.support ∧ W'.edges = W.edges :=
  W.exists_transfer (fun _ _ _ he hl => (h.isLink_iff (hE _ he)).mpr hl) hV

variable [T1Space S]

theorem span_isSubdrawing (Γ : Drawing S) (V' : Set S) (E' : Set (Set S)) :
    (Γ.span V' E').IsSubdrawing Γ := by
  refine ⟨Γ.spanV_subset V' E', ?_⟩
  rw [Γ.span_E]
  exact inter_subset_right

theorem sup_isSubdrawing (Γ Γ₁ Γ₂ : Drawing S) : (Γ.sup Γ₁ Γ₂).IsSubdrawing Γ :=
  span_isSubdrawing Γ _ _

theorem sup_V {Γ Γ₁ Γ₂ : Drawing S} (h₁ : Γ₁.IsSubdrawing Γ) (h₂ : Γ₂.IsSubdrawing Γ) :
    (Γ.sup Γ₁ Γ₂).V = Γ₁.V ∪ Γ₂.V := by
  apply subset_antisymm
  · rintro x (⟨hx, -⟩ | hx)
    · exact hx
    · obtain ⟨e, ⟨he, -⟩, hxe, hxV⟩ := mem_iUnion₂.mp hx
      rcases he with he | he
      · have : x ∈ closure e ∩ Γ₁.V := by rw [h₁.closure_inter_V he]; exact ⟨hxe, hxV⟩
        exact Or.inl this.2
      · have : x ∈ closure e ∩ Γ₂.V := by rw [h₂.closure_inter_V he]; exact ⟨hxe, hxV⟩
        exact Or.inr this.2
  · intro x hx
    refine Or.inl ⟨hx, ?_⟩
    rcases hx with hx | hx
    · exact h₁.1 hx
    · exact h₂.1 hx

theorem sup_E {Γ Γ₁ Γ₂ : Drawing S} (h₁ : Γ₁.IsSubdrawing Γ) (h₂ : Γ₂.IsSubdrawing Γ) :
    (Γ.sup Γ₁ Γ₂).E = Γ₁.E ∪ Γ₂.E := by
  rw [sup, Γ.span_E]
  exact inter_eq_left.mpr (union_subset h₁.2 h₂.2)

/-- The union of subdrawings has the union of their point sets. -/
theorem sup_U {Γ Γ₁ Γ₂ : Drawing S} (h₁ : Γ₁.IsSubdrawing Γ) (h₂ : Γ₂.IsSubdrawing Γ) :
    (Γ.sup Γ₁ Γ₂).U = Γ₁.U ∪ Γ₂.U := by
  rw [Drawing.U_eq, Drawing.sup_V h₁ h₂, Drawing.sup_E h₁ h₂, Γ₁.U_eq, Γ₂.U_eq,
    biUnion_union, union_union_union_comm]

theorem le_sup_left {Γ Γ₁ Γ₂ : Drawing S} (h₁ : Γ₁.IsSubdrawing Γ) (h₂ : Γ₂.IsSubdrawing Γ) :
    Γ₁.IsSubdrawing (Γ.sup Γ₁ Γ₂) :=
  ⟨by rw [sup_V h₁ h₂]; exact subset_union_left, by rw [sup_E h₁ h₂]; exact subset_union_left⟩

theorem le_sup_right {Γ Γ₁ Γ₂ : Drawing S} (h₁ : Γ₁.IsSubdrawing Γ) (h₂ : Γ₂.IsSubdrawing Γ) :
    Γ₂.IsSubdrawing (Γ.sup Γ₁ Γ₂) :=
  ⟨by rw [sup_V h₁ h₂]; exact subset_union_right, by rw [sup_E h₁ h₂]; exact subset_union_right⟩

end Drawing

end GraphMinor.Surface

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

theorem walkDrawing_isSubdrawing (Γ : Drawing S) {u v : S} (W : GraphWalk Γ.toGraph u v) :
    (walkDrawing Γ W).IsSubdrawing Γ :=
  Drawing.span_isSubdrawing Γ _ _

theorem walkDrawing_V (Γ : Drawing S) {u v : S} (W : GraphWalk Γ.toGraph u v) :
    (walkDrawing Γ W).V = {x | x ∈ W.support} := by
  apply subset_antisymm
  · rintro x (⟨hx, -⟩ | hx)
    · exact hx
    · obtain ⟨e, ⟨he, heE⟩, hxe, hxV⟩ := mem_iUnion₂.mp hx
      obtain ⟨a, b, hab⟩ := (Γ.toGraph.edge_mem_iff_exists_isLink e).mp heE
      have hxab : x ∈ closure e ∩ Γ.V := ⟨hxe, hxV⟩
      rw [hab.2.2.2] at hxab
      rcases hxab with rfl | hxab
      · exact W.left_mem_support_of_mem_edges he hab
      · exact (mem_singleton_iff.mp hxab) ▸ W.left_mem_support_of_mem_edges he hab.symm
  · intro x hx
    exact Or.inl ⟨hx, W.mem_vertexSet_of_mem_support hx⟩

theorem walkDrawing_E (Γ : Drawing S) {u v : S} (W : GraphWalk Γ.toGraph u v) :
    (walkDrawing Γ W).E = {e | e ∈ W.edges} := by
  rw [walkDrawing, Γ.span_E]
  refine inter_eq_left.mpr fun e he => ?_
  induction W with
  | nil h => simp at he
  | cons h r ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · exact ih he

/-- The point set of `Γ | W`: the vertices of `W` and the closures of its edges. -/
theorem mem_walkDrawing_U (Γ : Drawing S) {u v : S} (W : GraphWalk Γ.toGraph u v) {x : S} :
    x ∈ (walkDrawing Γ W).U ↔ x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e := by
  rw [Drawing.U_eq, walkDrawing_V, walkDrawing_E]
  simp

/-- The point set of a concatenated walk is the union of the point
sets of the two walks. -/
theorem _root_.GraphMinor.Surface.GraphWalk.drawing_U_append
    (K : Drawing S) {u v w : S}
    (P : GraphWalk K.toGraph u v) (Q : GraphWalk K.toGraph v w) :
    (walkDrawing K (P.append Q)).U = (walkDrawing K P).U ∪ (walkDrawing K Q).U := by
  ext x
  simp only [mem_walkDrawing_U, GraphWalk.mem_support_append, GraphWalk.edges_append,
    List.mem_append, mem_union]
  constructor
  · rintro ((h | h) | ⟨e, (he | he), hxe⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨e, he, hxe⟩)
    · exact Or.inr (Or.inr ⟨e, he, hxe⟩)
  · rintro ((h | ⟨e, he, hxe⟩) | (h | ⟨e, he, hxe⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨e, Or.inl he, hxe⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨e, Or.inr he, hxe⟩

/-- A zero-edge walk has just its vertex as point set. -/
theorem _root_.GraphMinor.Surface.GraphWalk.drawing_U_nil
    (K : Drawing S) {u : S} (hu : u ∈ K.V) :
    (walkDrawing K (GraphWalk.nil hu)).U = {u} := by
  ext x
  simp only [mem_walkDrawing_U, GraphWalk.support, GraphWalk.edges, List.mem_singleton,
    List.not_mem_nil, false_and, exists_false, or_false, mem_singleton_iff]

/-- An edge step adds exactly its edge closure to the point set. -/
theorem _root_.GraphMinor.Surface.GraphWalk.drawing_U_cons
    (K : Drawing S) {u v w : S} {e : Set S}
    (hl : K.toGraph.IsLink e u v) (P : GraphWalk K.toGraph v w) :
    (walkDrawing K (GraphWalk.cons hl P)).U = closure e ∪ (walkDrawing K P).U := by
  have hu : u ∈ closure e := by
    have h : u ∈ closure e ∩ K.V := hl.2.2.2.symm ▸ Or.inl rfl
    exact h.1
  ext x
  simp only [mem_walkDrawing_U, GraphWalk.support, GraphWalk.edges, List.mem_cons, mem_union]
  constructor
  · rintro ((rfl | h) | ⟨f, (rfl | hf), hxf⟩)
    · exact Or.inl hu
    · exact Or.inr (Or.inl h)
    · exact Or.inl hxf
    · exact Or.inr (Or.inr ⟨f, hf, hxf⟩)
  · rintro (h | h | ⟨f, hf, hxf⟩)
    · exact Or.inr ⟨e, Or.inl rfl, h⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨f, Or.inr hf, hxf⟩

/-- A two-edge region visit has the two edge closures as its whole
point set. -/
theorem _root_.GraphMinor.Surface.GraphWalk.drawing_U_two_edges
    (K : Drawing S)
    {u v w : S} {e e' : Set S} (hl : K.toGraph.IsLink e u v) (hl' : K.toGraph.IsLink e' v w) :
    (walkDrawing K (GraphWalk.cons hl (GraphWalk.cons hl' (.nil hl'.right_mem)))).U =
      closure e ∪ closure e' := by
  rw [GraphWalk.drawing_U_cons, GraphWalk.drawing_U_cons,
    GraphWalk.drawing_U_nil K (u := w) hl'.right_mem]
  have hw : w ∈ closure e' := by
    have h : w ∈ closure e' ∩ K.V := hl'.2.2.2.symm ▸ Or.inr rfl
    exact h.1
  rw [union_eq_left.mpr (singleton_subset_iff.mpr hw)]

/-- A walk drawing has a preconnected point set. -/
theorem _root_.GraphMinor.Surface.GraphWalk.drawing_U_isPreconnected
    (Γ : Drawing S) {u v : S} (W : GraphWalk Γ.toGraph u v) :
    IsPreconnected (walkDrawing Γ W).U := by
  induction W with
  | nil ha =>
    rw [GraphWalk.drawing_U_nil Γ ha]
    exact isPreconnected_singleton
  | @cons a b c e h R ih =>
    rw [GraphWalk.drawing_U_cons]
    have hclosure : IsPreconnected (closure e) := h.1.2.2.1.isConnected.isPreconnected.closure
    have hb : b ∈ closure e ∩ Γ.V := by
      rw [h.2.2.2]
      exact .inr rfl
    exact hclosure.union b hb.1 ((mem_walkDrawing_U Γ R).mpr (.inl R.start_mem_support)) ih

/-- `Γ | W` is a path, for a simple walk `W`. -/
theorem walkDrawing_isPathBetween (Γ : Drawing S) {u v : S} {W : GraphWalk Γ.toGraph u v}
    (hW : W.IsSimple) : (walkDrawing Γ W).IsPathBetween u v := by
  obtain ⟨W', hs, he⟩ := (walkDrawing_isSubdrawing Γ W).exists_walk_down W
    (by rw [walkDrawing_V]; exact fun x hx => hx) (by rw [walkDrawing_E]; exact fun e he => he)
  refine ⟨W', by unfold GraphWalk.IsSimple; rw [hs]; exact hW, ?_, ?_⟩
  · rw [walkDrawing_V, hs]
  · rw [walkDrawing_E, he]

end GraphMinor.GM11

namespace GraphMinor.Surface.Drawing

open Set Topology GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- Graph Minors XI, Section 4: two paths with the same two ends, with no other common vertex and
no common edge, form a circuit. -/
theorem isCircuit_sup {Γ P Q : Drawing S} {a b : S} (hP : P.IsPathBetween a b)
    (hQ : Q.IsPathBetween a b) (hPs : P.IsSubdrawing Γ) (hQs : Q.IsSubdrawing Γ) (hab : a ≠ b)
    (hV : P.V ∩ Q.V = {a, b}) (hE : Disjoint P.E Q.E) : (Γ.sup P Q).IsCircuit := by
  obtain ⟨W₁, hW₁, hV₁, hE₁⟩ := hP
  obtain ⟨W₂, hW₂, hV₂, hE₂⟩ := hQ
  have hl := le_sup_left hPs hQs
  have hr := le_sup_right hPs hQs
  obtain ⟨X₁, hs₁, he₁⟩ := hl.exists_walk_up W₁
  obtain ⟨X₂, hs₂, he₂⟩ := hr.exists_walk_up W₂.reverse
  have hmem₂ : ∀ x, x ∈ X₂.support ↔ x ∈ W₂.support := by
    intro x
    rw [hs₂, GraphWalk.support_reverse, List.mem_reverse]
  have hmemE₂ : ∀ e, e ∈ X₂.edges ↔ e ∈ W₂.edges := by
    intro e
    rw [he₂, GraphWalk.edges_reverse, List.mem_reverse]
  have hsc := GraphWalk.isSimpleClosed_append_of_lifts hW₁ hW₂ hs₁ hs₂ he₁ he₂
    (by simpa only [hV₁, hV₂] using hV) (by simpa only [hE₁, hE₂] using hE)
  refine ⟨a, X₁.append X₂, hsc, ?_, ?_, ?_⟩
  · rw [GraphWalk.length_append]
    have : X₁.length ≠ 0 := fun h => hab (GraphWalk.eq_of_length_eq_zero h)
    omega
  · rw [sup_V hPs hQs, hV₁, hV₂]
    ext x
    simp only [mem_union, mem_ofPred_eq, GraphWalk.mem_support_append, hmem₂, hs₁]
  · rw [sup_E hPs hQs, hE₁, hE₂]
    ext e
    simp only [mem_union, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append, hmemE₂, he₁]

/-- The two parts of a circuit between two of its vertices. Graph Minors XI, proof of (4.3)
(page 80): "let $P_1$, $P_2$ be the two paths of $C$ between $a$ and $b$". -/
theorem IsCircuit.exists_two_paths {C : Drawing S} (hC : C.IsCircuit) {a b : S} (ha : a ∈ C.V)
    (hb : b ∈ C.V) (hab : a ≠ b) :
    ∃ P Q : Drawing S, P.IsPathBetween a b ∧ Q.IsPathBetween a b ∧ P.IsSubdrawing C ∧
      Q.IsSubdrawing C ∧ 0 < P.length ∧ 0 < Q.length ∧ P.V ∩ Q.V = {a, b} ∧ Disjoint P.E Q.E ∧
      C.sup P Q = C := by
  obtain ⟨u, W, ⟨hnd, hed⟩, -, hV, hE⟩ := hC
  rw [hV] at ha hb
  obtain ⟨R₁, R₂, hS₁, hS₂, htail, hedR, hmemRot, hmemE⟩ :=
    GraphWalk.exists_circuit_split W hnd hed ha hb hab
  have hdisjT := List.nodup_append.mp htail
  have hedD := List.nodup_append.mp hedR
  have hP₀ := walkDrawing_isPathBetween C hS₁
  have hQ₀ := walkDrawing_isPathBetween C hS₂.reverse
  have hPs := walkDrawing_isSubdrawing C R₁
  have hQs := walkDrawing_isSubdrawing C R₂.reverse
  have hlenpos : ∀ {x y : S} (R : GraphWalk C.toGraph x y), x ≠ y →
      0 < (walkDrawing C R).length := by
    intro x y R hxy
    have hne : R.edges ≠ [] := by
      intro h
      have : R.length = 0 := by simp [GraphWalk.length, h]
      exact hxy (GraphWalk.eq_of_length_eq_zero this)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    have hfin : (walkDrawing C R).E.Finite := (walkDrawing C R).finite_edges
    refine Set.ncard_pos hfin |>.mpr ⟨e, ?_⟩
    rw [walkDrawing_E]
    exact he
  refine ⟨_, _, hP₀, hQ₀, hPs, hQs, hlenpos _ hab, hlenpos _ hab, ?_, ?_, ?_⟩
  · rw [walkDrawing_V, walkDrawing_V]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse,
      mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      rw [R₁.support_eq_cons] at h₁
      rw [R₂.support_eq_cons] at h₂
      rcases List.mem_cons.mp h₁ with h₁ | h₁
      · exact Or.inl h₁
      · rcases List.mem_cons.mp h₂ with h₂ | h₂
        · exact Or.inr h₂
        · exact (hdisjT.2.2 x h₁ x h₂ rfl).elim
    · rintro (rfl | rfl)
      · exact ⟨R₁.start_mem_support, R₂.end_mem_support⟩
      · exact ⟨R₁.end_mem_support, R₂.start_mem_support⟩
  · rw [walkDrawing_E, walkDrawing_E]
    refine disjoint_left.mpr fun e he₁ he₂ => ?_
    simp only [mem_ofPred_eq, GraphWalk.edges_reverse, List.mem_reverse] at he₁ he₂
    exact hedD.2.2 e he₁ e he₂ rfl
  · apply ext_of_V_E
    · rw [sup_V hPs hQs, walkDrawing_V, walkDrawing_V, hV]
      ext x
      simp only [mem_union, mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse]
      rw [← hmemRot x, GraphWalk.mem_support_append]
    · rw [sup_E hPs hQs, walkDrawing_E, walkDrawing_E, hE]
      ext e
      simp only [mem_union, mem_ofPred_eq, GraphWalk.edges_reverse, List.mem_reverse]
      rw [← hmemE e, GraphWalk.edges_append, List.mem_append]

end GraphMinor.Surface.Drawing
