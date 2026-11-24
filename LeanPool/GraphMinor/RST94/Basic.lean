/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Section8
public import LeanPool.GraphMinor.GM10.Section12
public import LeanPool.GraphMinor.GM10.TangleLemmas
public import LeanPool.GraphMinor.Menger.Basic

/-!
# Subgraphs and separations for "Quickly excluding a planar graph"

Robertson, Seymour and Thomas, *Quickly excluding a planar graph*, J. Combin. Theory Ser. B 62
(1994), 323–348.
We work with a graph as a hypergraph `G` with `G.IsGraph`, since the tangles of Graph Minors X live
on hypergraphs.

This file holds the tools for subgraphs that the paper uses without comment: `subOf` builds a
subgraph from its vertices
and edges, `IsSeparation.restrict` restricts a separation to a subgraph, and `addVerts` adds
vertices to a subgraph.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G H A B C D : Hypergraph α β}

/-- The subgraph of `G` with vertex set `V` and edge set `E`, when `E` consists of edges of `G` with
all ends in `V`. -/
def subOf (G : Hypergraph α β) (V : Set α) (E : Set β) (hV : V ⊆ G.vertexSet)
    (hE : ∀ e ∈ E, e ∈ G.edgeSet ∧ ∀ v, G.Inc e v → v ∈ V) : Hypergraph α β where
  vertexSet := V
  edgeSet := E
  Inc e v := e ∈ E ∧ G.Inc e v
  vertex_mem_of_inc _ _ h := (hE _ h.1).2 _ h.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := G.vertexSet_finite.subset hV
  edgeSet_finite := G.edgeSet_finite.subset fun e he => (hE e he).1

theorem subOf_le {V : Set α} {E : Set β} {hV : V ⊆ G.vertexSet}
    {hE : ∀ e ∈ E, e ∈ G.edgeSet ∧ ∀ v, G.Inc e v → v ∈ V} : subOf G V E hV hE ≤ G :=
  ⟨hV, fun e he => (hE e he).1, fun e he => by
    ext v
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩⟩

/-- An edge of a subgraph has the same ends in the larger graph. -/
theorem inc_le (h : H ≤ G) {e : β} (he : e ∈ H.edgeSet) {v : α} (hv : G.Inc e v) : H.Inc e v :=
  (inc_iff_of_le h he).2 hv

theorem end_mem (h : H ≤ G) {e : β} (he : e ∈ H.edgeSet) {v : α} (hv : G.Inc e v) : v ∈ H.vertexSet
  :=
  H.vertex_mem_of_inc (inc_le h he hv)

/-- Two subgraphs of `G` are equal if they have the same vertices and edges. -/
theorem sub_ext (h₁ : H ≤ G) (h₂ : A ≤ G) (hV : H.vertexSet = A.vertexSet) (hE : H.edgeSet
  = A.edgeSet) : H = A :=
  eq_of_le_of_vertexSet_eq_of_edgeSet_eq h₁ h₂ hV hE

theorem le_of_sets (h₁ : H ≤ G) (h₂ : A ≤ G) (hV : H.vertexSet ⊆ A.vertexSet)
  (hE : H.edgeSet ⊆ A.edgeSet) : H ≤ A :=
  (le_iff_of_le h₁ h₂).2 ⟨hV, hE⟩

/-- A separation is a pair of subgraphs that together cover `G` and share no edge. -/
theorem sep_of_sets (hA : A ≤ G) (hB : B ≤ G) (hV : ∀ v ∈ G.vertexSet, v ∈ A.vertexSet
  ∨ v ∈ B.vertexSet)
    (hE : ∀ e ∈ G.edgeSet, e ∈ A.edgeSet ∨ e ∈ B.edgeSet) (hd : ∀ e ∈ A.edgeSet, e ∉ B.edgeSet) :
    G.IsSeparation A B := by
  refine (isSeparation_iff_of_le hA hB).2 ⟨?_, ?_, ?_⟩
  · exact subset_antisymm (union_subset hA.vertexSet_subset hB.vertexSet_subset) hV
  · exact subset_antisymm (union_subset hA.edgeSet_subset hB.edgeSet_subset) hE
  · exact eq_empty_of_forall_notMem fun e he => hd e he.1 he.2

theorem mem_V_or (h : G.IsSeparation A B) {v : α} (hv : v ∈ G.vertexSet) : v ∈ A.vertexSet
  ∨ v ∈ B.vertexSet := by
  rw [← h.vertexSet_union] at hv
  exact hv

theorem mem_E_or (h : G.IsSeparation A B) {e : β} (he : e ∈ G.edgeSet) : e ∈ A.edgeSet
  ∨ e ∈ B.edgeSet := by
  rw [← h.edgeSet_union] at he
  exact he

/-- The order of a separation counts the vertices in both sides. -/
theorem order_le_of_subset {X : Set α} (hf : X.Finite) (h : (A ∩ B).vertexSet ⊆ X) :
    separationOrder A B ≤ X.ncard :=
  ncard_le_ncard h hf

/-- Restricting a separation to a subgraph gives a separation of the subgraph. -/
theorem _root_.GraphMinor.Hypergraph.IsSeparation.restrict (h : G.IsSeparation A B) (hH : H ≤ G) :
    H.IsSeparation (A ∩ H) (B ∩ H) := by
  have hA : A ∩ H ≤ H := inter_le_right h.left_le hH
  have hB : B ∩ H ≤ H := inter_le_right h.right_le hH
  refine sep_of_sets hA hB (fun v hv => ?_) (fun e he => ?_) (fun e he he' => ?_)
  · exact (mem_V_or h (hH.vertexSet_subset hv)).imp (fun h' => ⟨h', hv⟩) fun h' => ⟨h', hv⟩
  · exact (mem_E_or h (hH.edgeSet_subset he)).imp (fun h' => ⟨h', he⟩) fun h' => ⟨h', he⟩
  · exact h.notMem_edgeSet_right he.1 he'.1

/-- Restricting a separation does not raise its order. -/
theorem order_restrict_le (A B H : Hypergraph α β) : separationOrder (A ∩ H) (B ∩ H)
  ≤ separationOrder A B :=
  ncard_le_ncard (fun _ hv => ⟨hv.1.1, hv.2.1⟩) (A.vertexSet_finite.subset fun _ hv => hv.1)

/-- `(A ∩ H) ∩ H'` is `A ∩ H'` when `H' ≤ H`. -/
theorem inter_inter_of_le {H' : Hypergraph α β} (hA : A ≤ G) (hH : H ≤ G) (hH' : H' ≤ H) :
  (A ∩ H) ∩ H' = A ∩ H' := by
  have hG' : H' ≤ G := hH'.trans hH
  refine sub_ext (G := G) (inter_le (inter_le hA hH) hG') (inter_le hA hG') ?_ ?_
  · ext v
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hH'.vertexSet_subset h.2⟩, h.2⟩⟩
  · ext e
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hH'.edgeSet_subset h.2⟩, h.2⟩⟩

/-- `A ∩ G = A` for a subgraph `A` of `G`. -/
theorem inter_eq_left_of_le (hA : A ≤ G) : A ∩ G = A := by
  refine sub_ext (G := G) (inter_le hA le_rfl) hA ?_ ?_
  · ext v
    exact ⟨fun h => h.1, fun h => ⟨h, hA.vertexSet_subset h⟩⟩
  · ext e
    exact ⟨fun h => h.1, fun h => ⟨h, hA.edgeSet_subset h⟩⟩

/-- The subgraph `A` with the vertices `Z` added. -/
def addVerts (G A : Hypergraph α β) (hA : A ≤ G) (Z : Set α) (hZ : Z ⊆ G.vertexSet) : Hypergraph α
  β :=
  subOf G (A.vertexSet ∪ Z) A.edgeSet (union_subset hA.vertexSet_subset hZ)
    fun _ he => ⟨hA.edgeSet_subset he, fun _ hv => Or.inl (end_mem hA he hv)⟩

theorem addVerts_le {hA : A ≤ G} {Z : Set α} {hZ : Z ⊆ G.vertexSet} : addVerts G A hA Z hZ ≤ G
  := subOf_le

theorem isSeparation_addVerts (h : G.IsSeparation A B) {Z : Set α} (hZ : Z ⊆ G.vertexSet) :
    G.IsSeparation (addVerts G A h.left_le Z hZ) (addVerts G B h.right_le Z hZ) :=
  sep_of_sets addVerts_le addVerts_le (fun _ hv => (mem_V_or h hv).imp Or.inl Or.inl)
    (fun _ he => mem_E_or h he) (fun _ he he' => h.notMem_edgeSet_right he he')

theorem order_addVerts_le (h : G.IsSeparation A B) {Z : Set α} (hZ : Z ⊆ G.vertexSet) :
    separationOrder (addVerts G A h.left_le Z hZ) (addVerts G B h.right_le Z hZ)
      ≤ separationOrder A B + Z.ncard := by
  have hf : Z.Finite := G.vertexSet_finite.subset hZ
  have hsub : (addVerts G A h.left_le Z hZ ∩ addVerts G B h.right_le Z hZ).vertexSet ⊆
    (A ∩ B).vertexSet ∪ Z := by
    rintro v ⟨h₁ | h₁, h₂ | h₂⟩
    · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr h₂
    · exact Or.inr h₁
    · exact Or.inr h₁
  exact (ncard_le_ncard hsub (((A ∩ B).vertexSet_finite).union hf)).trans (ncard_union_le _ _)

/-- A nonempty predicate has an element of least measure. -/
theorem exists_min_measure {γ : Type*} {P : γ → Prop} (μ : γ → ℕ) (h : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → μ x ≤ μ y := by
  classical
  have hex : ∃ n, ∃ x, P x ∧ μ x = n := by
    obtain ⟨x, hx⟩ := h
    exact ⟨_, x, hx, rfl⟩
  obtain ⟨x, hx, hn⟩ := Nat.find_spec hex
  exact ⟨x, hx, fun y hy => hn ▸ Nat.find_min' hex ⟨y, hy, rfl⟩⟩

/-- A nonempty predicate with bounded measure has an element of greatest measure. -/
theorem exists_max_measure {γ : Type*} {P : γ → Prop} (μ : γ → ℕ) (N : ℕ) (hN : ∀ x, P x → μ x ≤ N)
  (h : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → μ y ≤ μ x := by
  obtain ⟨x, hx, hm⟩ := exists_min_measure (P := P) (fun y => N - μ y) h
  refine ⟨x, hx, fun y hy => ?_⟩
  have := hm y hy
  have := hN x hx
  have := hN y hy
  omega

/-- The size `|V(A)| + |E(A)|` of a subgraph. -/
noncomputable def size (A : Hypergraph α β) : ℕ := A.vertexSet.ncard + A.edgeSet.ncard

theorem size_lt_of_lt (h : H ≤ G) (hne : H ≠ G) : size H < size G := by
  have h₁ := ncard_le_ncard h.vertexSet_subset G.vertexSet_finite
  have h₂ := ncard_le_ncard h.edgeSet_subset G.edgeSet_finite
  by_contra hcon
  have hV : H.vertexSet = G.vertexSet := eq_of_subset_of_ncard_le h.vertexSet_subset
    (by unfold size at hcon; omega)
    G.vertexSet_finite
  have hE : H.edgeSet = G.edgeSet := eq_of_subset_of_ncard_le h.edgeSet_subset
    (by unfold size at hcon; omega)
    G.edgeSet_finite
  exact hne (sub_ext h le_rfl hV hE)

theorem size_le_of_le (h : H ≤ G) : size H ≤ size G := by
  have h₁ := ncard_le_ncard h.vertexSet_subset G.vertexSet_finite
  have h₂ := ncard_le_ncard h.edgeSet_subset G.edgeSet_finite
  unfold size
  omega

/-- `X` is the vertex set of a connected subgraph of `G`: it is not empty, and any two of its
vertices are joined by a walk
of `G` with all vertices in `X`. -/
def Conn (G : Hypergraph α β) (X : Set α) : Prop :=
  X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X, ∃ w : G.skeleton.Walk x y, ∀ z ∈ w.support, z ∈ X

theorem conn_singleton {x : α} : Conn G {x} :=
  ⟨⟨x, rfl⟩, fun a ha b hb => by
    obtain rfl := ha
    obtain rfl := hb
    exact ⟨.nil, by simp⟩⟩

/-- Two connected sets that meet have a connected union. -/
theorem Conn.union {X Y : Set α} (hX : Conn G X) (hY : Conn G Y) (h : (X ∩ Y).Nonempty) : Conn G
  (X ∪ Y) := by
  obtain ⟨c, hcX, hcY⟩ := h
  have key : ∀ x ∈ X ∪ Y, ∃ w : G.skeleton.Walk x c, ∀ z ∈ w.support, z ∈ X ∪ Y := by
    rintro x (hx | hx)
    · obtain ⟨w, hw⟩ := hX.2 x hx c hcX
      exact ⟨w, fun z hz => Or.inl (hw z hz)⟩
    · obtain ⟨w, hw⟩ := hY.2 x hx c hcY
      exact ⟨w, fun z hz => Or.inr (hw z hz)⟩
  refine ⟨⟨c, Or.inl hcX⟩, fun x hx y hy => ?_⟩
  obtain ⟨w₁, h₁⟩ := key x hx
  obtain ⟨w₂, h₂⟩ := key y hy
  refine ⟨w₁.append w₂.reverse, fun z hz => ?_⟩
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with h | h
  · exact h₁ z h
  · exact h₂ z (by simpa using h)

/-- Two connected sets joined by an edge have a connected union. -/
theorem Conn.union_adj {X Y : Set α} (hX : Conn G X) (hY : Conn G Y) {x y : α} (hx : x ∈ X)
  (hy : y ∈ Y)
    (h : G.skeleton.Adj x y) : Conn G (X ∪ Y) := by
  have hp : Conn G ({x, y} : Set α) := by
    refine ⟨⟨x, Or.inl rfl⟩, ?_⟩
    have hs : ∀ (a b : α) (hab : G.skeleton.Adj a b) z,
        z ∈ (SimpleGraph.Walk.cons hab .nil).support → z ∈ ({a, b} : Set α) := fun a b hab z hz
          => by
      simpa using hz
    rintro a (rfl | rfl) b (rfl | rfl)
    · exact ⟨.nil, by simp⟩
    · exact ⟨_, hs _ _ h⟩
    · exact ⟨_, fun z hz => by simpa [or_comm] using hs _ _ h.symm z hz⟩
    · exact ⟨.nil, by simp⟩
  have h₁ := hX.union hp ⟨x, hx, Or.inl rfl⟩
  have h₂ := h₁.union hY ⟨y, Or.inr (Or.inr rfl), hy⟩
  refine (show (X ∪ {x, y}) ∪ Y = X ∪ Y from ?_) ▸ h₂
  ext z
  simp only [mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ((h | rfl | rfl) | h)
    · exact Or.inl h
    · exact Or.inl hx
    · exact Or.inr hy
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

/-- A walk gives a connected set. -/
theorem conn_support {x y : α} (w : G.skeleton.Walk x y) : Conn G {z | z ∈ w.support} := by
  classical
  refine ⟨⟨x, w.start_mem_support⟩, fun a ha b hb => ?_⟩
  refine ⟨(w.dropUntil a ha).append (w.dropUntil b hb).reverse, fun z hz => ?_⟩
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with h | h
  · exact SimpleGraph.Walk.support_dropUntil_subset_support _ _ h
  · exact SimpleGraph.Walk.support_dropUntil_subset_support _ _ (by simpa using h)

/-- A set that is not connected, and not empty, splits into two nonempty parts with no edge between
them. -/
theorem exists_split_of_not_conn {X : Set α} (hne : X.Nonempty) (h : ¬ Conn G X) :
    ∃ X₁ X₂ : Set α, X₁.Nonempty ∧ X₂.Nonempty ∧ X₁ ∪ X₂ = X ∧ Disjoint X₁ X₂ ∧
      ∀ x ∈ X₁, ∀ y ∈ X₂, ¬ G.skeleton.Adj x y := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  let X₁ : Set α := {y | y ∈ X ∧ ∃ w : G.skeleton.Walk x₀ y, ∀ z ∈ w.support, z ∈ X}
  have hx₁ : x₀ ∈ X₁ := ⟨hx₀, .nil, by simpa using hx₀⟩
  have hsplit : (X \ X₁).Nonempty := by
    by_contra hn
    have hall : ∀ y ∈ X, y ∈ X₁ := fun y hy => by
      by_contra hy'
      exact hn ⟨y, hy, hy'⟩
    refine h ⟨⟨x₀, hx₀⟩, fun a ha b hb => ?_⟩
    obtain ⟨-, wa, hwa⟩ := hall a ha
    obtain ⟨-, wb, hwb⟩ := hall b hb
    refine ⟨wa.reverse.append wb, fun z hz => ?_⟩
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with h | h
    · exact hwa z (by simpa using h)
    · exact hwb z h
  refine ⟨X₁, X \ X₁, ⟨x₀, hx₁⟩, hsplit, union_sdiff_cancel fun _ h => h.1, disjoint_sdiff_right,
    ?_⟩
  rintro x ⟨hxX, w, hw⟩ y ⟨hyX, hy⟩ hadj
  refine hy ⟨hyX, w.concat hadj, fun z hz => ?_⟩
  rw [SimpleGraph.Walk.support_concat, List.mem_append] at hz
  rcases hz with hz | hz
  · exact hw z hz
  · exact (List.mem_singleton.1 hz) ▸ hyX

/-- Two ends of an edge of a subgraph are adjacent in the larger graph. -/
theorem skeleton_mono (h : H ≤ G) : H.skeleton ≤ G.skeleton := fun _ _ hadj => by
  obtain ⟨hne, e, h₁, h₂⟩ := hadj
  exact ⟨hne, e, inc_of_le h h₁, inc_of_le h h₂⟩

/-- A connected set of a subgraph is connected in the larger graph. -/
theorem Conn.mono {X : Set α} (hX : Conn H X) (h : H ≤ G) : Conn G X :=
  ⟨hX.1, fun x hx y hy => by
    obtain ⟨w, hw⟩ := hX.2 x hx y hy
    exact ⟨w.mapLe (skeleton_mono h), fun z hz => hw z (by simpa using hz)⟩⟩

/-- Vertices of a path before a vertex `x` other than the last: the last vertex is not among them.
-/
theorem notMem_takeUntil {K : SimpleGraph α} [DecidableEq α] {u v x : α} (w : K.Walk u v)
  (hw : w.IsPath) (hx : x ∈ w.support)
    (hne : x ≠ v) : v ∉ (w.takeUntil x hx).support := by
  intro hv
  have hn : ((w.takeUntil x hx).append (w.dropUntil x hx)).support.Nodup := by
    rw [w.take_spec hx]
    exact hw.support_nodup
  rw [SimpleGraph.Walk.support_append, List.nodup_append] at hn
  refine hn.2.2 v hv v ?_ rfl
  have h₁ : v ∈ (w.dropUntil x hx).support := (w.dropUntil x hx).end_mem_support
  rw [← SimpleGraph.Walk.cons_tail_support] at h₁
  exact (List.mem_cons.1 h₁).resolve_left hne.symm

/-- A set in which every vertex has a walk to `b` is connected. -/
theorem conn_of_reach {X : Set α} {b : α} (hb : b ∈ X) (h : ∀ x ∈ X, ∃ w : G.skeleton.Walk x b, ∀ z
  ∈ w.support, z ∈ X) :
    Conn G X := by
  classical
  refine ⟨⟨b, hb⟩, fun x hx y hy => ?_⟩
  obtain ⟨w₁, h₁⟩ := h x hx
  obtain ⟨w₂, h₂⟩ := h y hy
  refine ⟨w₁.append w₂.reverse, fun z hz => ?_⟩
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with hz | hz
  · exact h₁ z hz
  · exact h₂ z (by simpa using hz)

/-- A walk of the skeleton stays in `V(G)`. -/
theorem support_mem {u v : α} (w : G.skeleton.Walk u v) (hu : u ∈ G.vertexSet) {x : α}
  (hx : x ∈ w.support) :
    x ∈ G.vertexSet := by
  induction w with
  | nil =>
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ hu
  | cons hadj p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | h
    · exact hu
    · obtain ⟨-, e, -, h₂⟩ := hadj
      exact ih (G.vertex_mem_of_inc h₂) h

/-- `k` injective values in a set of size `k` fill the set. -/
theorem exists_index {k : ℕ} {W : Set α} (f : Fin k → α) (hWf : W.Finite) (hWc : W.ncard = k)
    (hfi : Function.Injective f) (hfW : ∀ i, f i ∈ W) {x : α} (hx : x ∈ W) : ∃ i, f i = x := by
  have hsub : range f ⊆ W := range_subset_iff.2 hfW
  have hc : W.ncard ≤ (range f).ncard := by
    rw [← image_univ, ncard_image_of_injective _ hfi, ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, hWc]
  exact (eq_of_subset_of_ncard_le hsub hc hWf ▸ hx : x ∈ range f)

end GraphMinor.RST94
