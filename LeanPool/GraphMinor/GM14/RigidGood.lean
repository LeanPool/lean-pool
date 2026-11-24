/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidThread
public import LeanPool.GraphMinor.GM14.Suppress
import LeanPool.GraphMinor.GM11.RadialExists

/-!
# A rigid drawing with a wheel around it is good

Let `H` be rigid in a closed disc `Δ` in a sphere, and draw a wheel `W` in the closed disc on the
other
side of `bd(Δ)`, with its rim on `bd(Δ)`, with `V(H) ∩ bd(Δ)` among its rim vertices, and with no
edge of
`W` between two vertices of `H`. In the paper's proof of (6.4) the union is `J₁`, except that we
keep
the rim edges apart from `H` by new vertices on the rim.

`good_of_wheel` shows that the union `J` is `Good`, so that it is a subdivision of a simple
3-connected
graph (`good_sub`). Take a separation of order at most 2. The wheel stays on one side, apart from
the
common vertices. The edges of `H` on the other side then form a set with at most two boundary
vertices, and `exists_thread` says that this set is a path.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

section WalkFacts

variable {α : Type u} {β : Type v} {P : Graph α β}

theorem length_support {a b : α} (W : GraphWalk P a b) : W.support.length = W.edges.length + 1 := by
  induction W with
  | nil _ => simp [GraphWalk.support, GraphWalk.edges]
  | cons _ _ ih => simp [GraphWalk.support, GraphWalk.edges, ih]

/-- In a simple walk, only one edge meets the start. -/
theorem edge_at_start {a b : α} (W : GraphWalk P a b) (hs : W.IsSimple) {g g' : β}
    (hg : g ∈ W.edges) (hg' : g' ∈ W.edges) (hi : P.Inc g a) (hi' : P.Inc g' a) : g = g' := by
  cases W with
  | nil _ => simp [GraphWalk.edges] at hg
  | @cons u t b c hl rest =>
    have hun : a ∉ rest.support := (List.nodup_cons.mp hs).1
    have key : ∀ {x}, x ∈ (GraphWalk.cons hl rest).edges → P.Inc x a → x = c := by
      intro x hx hix
      simp only [GraphWalk.edges, List.mem_cons] at hx
      rcases hx with hx | hx
      · exact hx
      · exact absurd (inc_mem_support rest hx hix) hun
    rw [key hg hi, key hg' hi']

/-- In a simple walk, at most two edges meet an inner vertex. -/
theorem edge_at_inner {a b : α} (W : GraphWalk P a b) (hs : W.IsSimple) {v : α}
    (hva : v ≠ a) (hvb : v ≠ b) {e f g : β} (he : e ∈ W.edges) (hf : f ∈ W.edges) (hg : g ∈ W.edges)
    (hie : P.Inc e v) (hif : P.Inc f v) (hig : P.Inc g v) (hne : e ≠ f) : g = e ∨ g = f := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u t b c hl rest ih =>
    have hrs : rest.IsSimple := (List.nodup_cons.mp hs).2
    simp only [GraphWalk.edges, List.mem_cons] at he hf hg
    by_cases hvt : v = t
    · subst hvt
      rcases he with he | he <;> rcases hf with hf | hf
      · exact absurd (he.trans hf.symm) hne
      · rcases hg with hg | hg
        · exact Or.inl (hg.trans he.symm)
        · exact Or.inr (edge_at_start rest hrs hg hf hig hif)
      · rcases hg with hg | hg
        · exact Or.inr (hg.trans hf.symm)
        · exact Or.inl (edge_at_start rest hrs hg he hig hie)
      · exact absurd (edge_at_start rest hrs he hf hie hif) hne
    · have hnot : ∀ {x}, x = c ∨ x ∈ rest.edges → P.Inc x v → x ∈ rest.edges := by
        rintro x (rfl | hx) hi
        · exfalso
          obtain ⟨z, hz⟩ := hi
          rcases P.eq_or_eq_of_isLink_of_isLink hz hl with h₁ | h₁
          · exact hva h₁
          · exact hvt h₁
        · exact hx
      exact ih hrs hvt hvb (hnot he hie) (hnot hf hif) (hnot hg hig)

end WalkFacts

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- Counts for a path drawing. -/
theorem path_count {P : Drawing S} {x y : S} (h : P.IsPathBetween x y) (hxy : x ≠ y) (hx : x ∈ P.V)
    (hy : y ∈ P.V) : P.E.ncard ≤ (P.V \ {x, y}).ncard + 1 := by
  classical
  obtain ⟨W, hs, hV, hE⟩ := h
  have h₁ : P.V = ↑W.support.toFinset := by
    rw [hV]
    ext z
    simp
  have h₂ : P.E = ↑W.edges.toFinset := by
    rw [hE]
    ext z
    simp
  have hc₁ : P.V.ncard = W.support.length := by
    rw [h₁, ncard_coe_finset, List.toFinset_card_of_nodup hs]
  have hc₂ : P.E.ncard ≤ W.edges.length := by
    rw [h₂, ncard_coe_finset]
    exact List.toFinset_card_le _
  have hsub : ({x, y} : Set S) ⊆ P.V := by
    rintro z (rfl | rfl)
    · exact hx
    · exact hy
  have hc₃ : (P.V \ {x, y}).ncard = P.V.ncard - 2 := by
    rw [ncard_sdiff hsub (toFinite _), ncard_pair hxy]
  have := length_support W
  have hge : 2 ≤ P.V.ncard := by
    rw [← ncard_pair hxy]
    exact ncard_le_ncard hsub P.finite_V
  omega

omit [T2Space S] in
/-- An inner vertex of a path meets exactly two of its edges. -/
theorem path_two {P : Drawing S} {x y : S} (h : P.IsPathBetween x y) {v : S} (hv : v ∈ P.V)
    (hx : v ≠ x) (hy : v ≠ y) : {g | P.toGraph.Inc g v}.ncard = 2 := by
  obtain ⟨W, hs, hV, hE⟩ := h
  have hvs : v ∈ W.support := by
    rw [hV] at hv
    exact hv
  obtain ⟨e, he, f, hf, hne, hie, hif⟩ := exists_two_edges_at_inner W hs hvs hx hy
  have heq : {g | P.toGraph.Inc g v} = {e, f} := by
    ext g
    constructor
    · intro hig
      have hgE : g ∈ W.edges := by
        have : g ∈ P.E := hig.edge_mem
        rw [hE] at this
        exact this
      exact edge_at_inner W hs hx hy he hf hgE hie hif hig hne
    · rintro (rfl | rfl)
      · exact hie
      · exact hif
  rw [heq, ncard_pair hne]

/-- What we use about the wheel `W`. -/
structure Wheel (W : Drawing S) (B D₁ D₂ : Set S) : Prop where
  Usub : W.U ⊆ D₂
  bdU : discBd D₂ ⊆ W.U
  hconn : IsPreconnected (D₁ ∪ W.U)
  BV : B ⊆ W.V
  nl : ∀ e u, ¬ W.toGraph.IsLink e u u
  simple : ∀ e e' u v, W.toGraph.IsLink e u v → W.toGraph.IsLink e' u v → e = e'
  nob : ∀ e u v, W.toGraph.IsLink e u v → u ∈ B → v ∉ B
  four : ∃ T : Set S, T ⊆ W.V ∧ 4 ≤ T.ncard ∧ ∀ v ∈ T, 3 ≤ {e | W.toGraph.Inc e v}.ncard
  side : ∀ U₁ U₂ X : Set S, IsClosed U₁ → IsClosed U₂ → W.U ⊆ U₁ ∪ U₂ → W.U ∩ U₁ ∩ U₂ ⊆ X →
    X ⊆ W.V → X.ncard ≤ 2 → W.V \ X ⊆ U₁ ∨ W.V \ X ⊆ U₂

/-- `J` is the union of `H` and `W`, as graphs. -/
structure IsUnion (H W J : Drawing S) : Prop where
  hV : J.V = H.V ∪ W.V
  hE : J.E = H.E ∪ W.E
  linkH : ∀ e ∈ H.E, ∀ u v, J.toGraph.IsLink e u v ↔ H.toGraph.IsLink e u v
  linkW : ∀ e ∈ W.E, ∀ u v, J.toGraph.IsLink e u v ↔ W.toGraph.IsLink e u v

/-- The point set of a graph with edges in `J`. -/
def pts (G : Graph S (Set S)) : Set S := V(G) ∪ ⋃ e ∈ E(G), closure e

variable {H W J Γ' : Drawing S} {B Δ D₂ : Set S} {a : S}

section Sep

variable {G₁ G₂ : Graph S (Set S)}

omit [T2Space S] in
/-- A vertex of `J` in the closure of an edge of a subgraph is a vertex of the subgraph. -/
theorem mem_V_of_closure (hs : G₁ ≤ J.toGraph) {e : Set S} (he : e ∈ E(G₁)) {z : S}
    (hz : z ∈ closure e) (hzV : z ∈ J.V) : z ∈ V(G₁) := by
  obtain ⟨c, d, hl⟩ := (G₁.edge_mem_iff_exists_isLink e).mp he
  have hl' : J.toGraph.IsLink e c d := hs.isLink_mono hl
  have : z ∈ closure e ∩ J.V := ⟨hz, hzV⟩
  rw [hl'.2.2.2] at this
  rcases this with rfl | rfl
  · exact hl.left_mem
  · exact hl.right_mem

theorem isClosed_pts (hs : G₁ ≤ J.toGraph) : IsClosed (pts G₁) := by
  refine IsClosed.union ((J.finite_V.subset hs.vertexSet_mono).isClosed) ?_
  exact (J.finite_edges.subset hs.edgeSet_mono).isClosed_biUnion fun _ _ => isClosed_closure

omit [T2Space S] in
theorem mem_V_of_pts (hs : G₁ ≤ J.toGraph) {z : S} (hz : z ∈ pts G₁) (hzV : z ∈ J.V) : z ∈ V(G₁)
  := by
  rcases hz with hz | hz
  · exact hz
  · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
    exact mem_V_of_closure hs he hze hzV

omit [T2Space S] in
theorem pts_cover (hs : IsGraphSeparation J.toGraph G₁ G₂) : J.U ⊆ pts G₁ ∪ pts G₂ := by
  obtain ⟨-, -, hV, hE, -⟩ := hs
  intro z hz
  rw [Drawing.U_eq] at hz
  rcases hz with hz | hz
  · have : z ∈ V(G₁) ∪ V(G₂) := hV ▸ hz
    rcases this with h₁ | h₁
    · exact Or.inl (Or.inl h₁)
    · exact Or.inr (Or.inl h₁)
  · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
    have : e ∈ E(G₁) ∪ E(G₂) := hE ▸ he
    rcases this with h₁ | h₁
    · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, h₁, hze⟩))
    · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨e, h₁, hze⟩))

omit [T2Space S] in
theorem pts_cap (hs : IsGraphSeparation J.toGraph G₁ G₂) : pts G₁ ∩ pts G₂ ⊆ V(G₁) ∩ V(G₂) := by
  obtain ⟨hl₁, hl₂, hV, hE, hdis⟩ := id hs
  have hsubV₁ : V(G₁) ⊆ J.V := hl₁.vertexSet_mono
  have hsubV₂ : V(G₂) ⊆ J.V := hl₂.vertexSet_mono
  rintro z ⟨hz₁, hz₂⟩
  have hzV : z ∈ J.V := by
    rcases hz₁ with h₁ | h₁
    · exact hsubV₁ h₁
    · rcases hz₂ with h₂ | h₂
      · exact hsubV₂ h₂
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp h₁
        obtain ⟨e', he', hze'⟩ := mem_iUnion₂.mp h₂
        by_contra hn
        have heJ : e ∈ J.E := hl₁.edgeSet_mono he
        have heJ' : e' ∈ J.E := hl₂.edgeSet_mono he'
        have h₃ : z ∈ e := by
          rw [← J.closure_diff_V heJ]
          exact ⟨hze, hn⟩
        have h₄ : z ∈ e' := by
          rw [← J.closure_diff_V heJ']
          exact ⟨hze', hn⟩
        have := J.edge_eq_of_mem heJ heJ' h₃ h₄
        exact disjoint_left.mp hdis he (this ▸ he')
  exact ⟨mem_V_of_pts hl₁ hz₁ hzV, mem_V_of_pts hl₂ hz₂ hzV⟩

omit [T2Space S] in
/-- A vertex at an edge of a subdrawing is a vertex of that subdrawing. -/
theorem mem_V_of_inc_sub {P : Drawing S} (hs : P.IsSubdrawing J) {g : Set S} (hg : g ∈ P.E) {v : S}
    (hi : J.toGraph.Inc g v) : v ∈ P.V := by
  by_contra hn
  have hvg : v ∈ g := by
    rw [← P.closure_diff_V hg]
    exact ⟨mem_closure_of_inc hi, hn⟩
  exact edge_notMem_V (hs.2 hg) hvg hi.vertex_mem

/-- If the wheel, apart from the common vertices, is on the side of `G₁`, then `G₂` is thin. -/
theorem thin_of_side [ConnectedSpace S] (f : Frame H J Δ a) (r : Rad J Γ') (hw : Wheel W B Δ D₂)
    (hu : IsUnion H W J) (hB : ∀ v ∈ H.V, v ∈ W.V → v ∈ B) (hS : IsClosedSurface S)
    (hsph : IsSphere S) (hs : IsGraphSeparation J.toGraph G₁ G₂)
    (hord : (V(G₁) ∩ V(G₂)).ncard ≤ 2) (hP : W.V \ (V(G₁) ∩ V(G₂)) ⊆ V(G₁))
    (hJl : ∀ e v, ¬ J.toGraph.IsLink e v v) :
    Thin J.toGraph G₂ G₁ := by
  classical
  obtain ⟨hl₁, hl₂, hV, hE, hdis⟩ := id hs
  set X := V(G₁) ∩ V(G₂) with hX
  have hXfin : X.Finite := J.finite_V.subset fun z hz => hl₁.vertexSet_mono hz.1
  have hEfin₂ : E(G₂).Finite := J.finite_edges.subset hl₂.edgeSet_mono
  -- Vertices on the side of `G₂` that are not common are not in the wheel, and all their edges are
  -- on that side.
  have hnoW : ∀ {v}, v ∈ V(G₂) → v ∉ X → v ∉ W.V := fun {v} h₁ h₂ h₃ =>
    h₂ ⟨hP ⟨h₃, h₂⟩, h₁⟩
  have hside : ∀ {v g}, v ∈ V(G₂) → v ∉ X → g ∈ J.E → J.toGraph.Inc g v → g ∈ E(G₂) := by
    intro v g h₁ h₂ hg hi
    have : g ∈ E(G₁) ∪ E(G₂) := hE ▸ hg
    rcases this with h₃ | h₃
    · exact absurd ⟨mem_V_of_closure hl₁ h₃ (mem_closure_of_inc hi) hi.vertex_mem, h₁⟩ h₂
    · exact h₃
  have hendsW : ∀ {g v}, g ∈ W.E → J.toGraph.Inc g v → v ∈ W.V := by
    rintro g v hg ⟨t, ht⟩
    exact ((hu.linkW g hg v t).mp ht).left_mem
  let A : Set (Set S) := E(G₂) ∩ H.E
  have hAH : A ⊆ H.E := inter_subset_right
  have hE₂split : ∀ {g}, g ∈ E(G₂) → g ∉ A → g ∈ W.E := by
    intro g hg hn
    have : g ∈ J.E := hl₂.edgeSet_mono hg
    rw [hu.hE] at this
    rcases this with h₃ | h₃
    · exact absurd ⟨hg, h₃⟩ hn
    · exact h₃
  have hbX : Whitney.bdry J.toGraph A ⊆ X := by
    rintro v ⟨⟨g, hg, hi⟩, ⟨g', ⟨hg', hgA⟩, hi'⟩⟩
    by_contra hn
    have hv₂ : v ∈ V(G₂) := mem_V_of_closure hl₂ hg.1 (mem_closure_of_inc hi) hi.vertex_mem
    have hg'₂ := hside hv₂ hn hg' hi'
    exact hnoW hv₂ hn (hendsW (hE₂split hg'₂ hgA) hi')
  have hbfin : (Whitney.bdry J.toGraph A).Finite := hXfin.subset hbX
  have hbc : (Whitney.bdry J.toGraph A).ncard ≤ 2 := (ncard_le_ncard hbX hXfin).trans hord
  -- A vertex of `G₂` that is not common has an edge.
  have hedge : ∀ {v}, v ∈ J.V → ∃ g ∈ J.E, J.toGraph.Inc g v := by
    intro v hv
    obtain ⟨g, hg, hc⟩ := exists_edge_of_regionFacts hS r.facts hv
    exact ⟨g, hg, inc_of_mem_closure hg hc hv⟩
  by_cases hA : A = ∅
  · -- Only edges of the wheel are on the side of `G₂`.
    have hV₂ : V(G₂) ⊆ V(G₁) := by
      intro v hv
      by_contra hn
      have hnX : v ∉ X := fun h₃ => hn h₃.1
      obtain ⟨g, hg, hi⟩ := hedge (hl₂.vertexSet_mono hv)
      have hg₂ := hside hv hnX hg hi
      exact hnoW hv hnX (hendsW (hE₂split hg₂ (by rw [hA]; exact notMem_empty _)) hi)
    by_cases hemp : E(G₂) = ∅
    · exact Or.inl ⟨hV₂, hemp⟩
    obtain ⟨g, hg⟩ := nonempty_iff_ne_empty.mpr hemp
    obtain ⟨u, v, huv⟩ := (G₂.edge_mem_iff_exists_isLink g).mp hg
    have huv' : J.toGraph.IsLink g u v := hl₂.isLink_mono huv
    have hne : u ≠ v := fun h₃ => hJl g v (h₃ ▸ huv')
    have huX : u ∈ X := ⟨hV₂ huv.left_mem, huv.left_mem⟩
    have hvX : v ∈ X := ⟨hV₂ huv.right_mem, huv.right_mem⟩
    have hXeq : X = {u, v} := by
      have hsub : ({u, v} : Set S) ⊆ X := by
        rintro z (rfl | rfl)
        · exact huX
        · exact hvX
      exact (eq_of_subset_of_ncard_le hsub (by rw [ncard_pair hne]; exact hord) hXfin).symm
    have hgW := hE₂split hg (by rw [hA]; exact notMem_empty _)
    have hX₂ : (V(G₂) ∩ V(G₁)).ncard = 2 := by
      rw [inter_comm, ← hX, hXeq, ncard_pair hne]
    refine Or.inr ⟨hX₂, fun z hz => absurd (hV₂ hz.1) hz.2, ?_⟩
    have hsing : E(G₂) ⊆ {g} := by
      intro g' hg'
      have hg'W := hE₂split hg' (by rw [hA]; exact notMem_empty _)
      obtain ⟨c, d, hcd⟩ := (G₂.edge_mem_iff_exists_isLink g').mp hg'
      have hcd' : J.toGraph.IsLink g' c d := hl₂.isLink_mono hcd
      have hc : c ∈ X := ⟨hV₂ hcd.left_mem, hcd.left_mem⟩
      have hd : d ∈ X := ⟨hV₂ hcd.right_mem, hcd.right_mem⟩
      have hcdne : c ≠ d := fun h₃ => hJl g' d (h₃ ▸ hcd')
      have hlk₁ := (hu.linkW g hgW u v).mp huv'
      have hlk₂ := (hu.linkW g' hg'W c d).mp hcd'
      rw [hXeq] at hc hd
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact absurd rfl hcdne
      · exact hw.simple _ _ _ _ hlk₂ hlk₁
      · exact hw.simple _ _ _ _ hlk₂.symm hlk₁
      · exact absurd rfl hcdne
    have := ncard_le_ncard hsing (toFinite _)
    rw [ncard_singleton] at this
    omega
  -- Some edges of `H` are on the side of `G₂`, and they form a path.
  obtain ⟨x, y, P, hxy, hbd, hPs, hpath, hPE, hin⟩ :=
    exists_thread f r hS hsph hAH hbc hbfin (nonempty_iff_ne_empty.mpr hA)
  have hxX : x ∈ X := hbX (hbd ▸ Or.inl rfl)
  have hyX : y ∈ X := hbX (hbd ▸ Or.inr rfl)
  have hXeq : X = {x, y} := by
    have hsub : ({x, y} : Set S) ⊆ X := by
      rintro z (rfl | rfl)
      · exact hxX
      · exact hyX
    exact (eq_of_subset_of_ncard_le hsub (by rw [ncard_pair hxy]; exact hord) hXfin).symm
  have hPJ : P.IsSubdrawing J := ⟨hPs.1.trans f.Vsub, hPs.2.trans f.Esub⟩
  -- The ends are vertices of `H`.
  have hbdH : ∀ {z}, z ∈ Whitney.bdry J.toGraph A → z ∈ H.V := by
    rintro z ⟨⟨g, hg, hi⟩, -⟩
    obtain ⟨t, ht⟩ := hi
    exact ((hu.linkH g hg.2 z t).mp ht).left_mem
  have hxH : x ∈ H.V := hbdH (hbd ▸ Or.inl rfl)
  have hyH : y ∈ H.V := hbdH (hbd ▸ Or.inr rfl)
  have hE₂ : E(G₂) = P.E := by
    rw [hPE]
    refine subset_antisymm (fun g hg => ?_) inter_subset_left
    by_contra hn
    have hgW := hE₂split hg hn
    obtain ⟨c, d, hcd⟩ := (G₂.edge_mem_iff_exists_isLink g).mp hg
    have hcd' : J.toGraph.IsLink g c d := hl₂.isLink_mono hcd
    have hlk := (hu.linkW g hgW c d).mp hcd'
    have hcX : c ∈ X := by
      by_contra hn'
      exact hnoW hcd.left_mem hn' hlk.left_mem
    have hdX : d ∈ X := by
      by_contra hn'
      exact hnoW hcd.right_mem hn' hlk.right_mem
    have hcB : c ∈ B := hB c (by
      rw [hXeq] at hcX
      rcases hcX with rfl | rfl
      · exact hxH
      · exact hyH) hlk.left_mem
    have hdB : d ∈ B := hB d (by
      rw [hXeq] at hdX
      rcases hdX with rfl | rfl
      · exact hxH
      · exact hyH) hlk.right_mem
    exact hw.nob g c d hlk hcB hdB
  have hxP : x ∈ P.V := by
    obtain ⟨W₀, -, hV₀, -⟩ := id hpath
    rw [hV₀]
    exact start_mem_support W₀
  have hyP : y ∈ P.V := by
    obtain ⟨W₀, -, hV₀, -⟩ := id hpath
    rw [hV₀]
    exact end_mem_support W₀
  have hX₂ : (V(G₂) ∩ V(G₁)).ncard = 2 := by
    rw [inter_comm, ← hX, hXeq, ncard_pair hxy]
  -- A vertex on the path is on the side of `G₂`.
  have hPinV : ∀ {v}, v ∈ P.V → v ≠ x → v ≠ y → v ∈ V(G₂) \ V(G₁) := by
    intro v hv h₁ h₂
    have hedgeP : ∃ g ∈ P.E, P.toGraph.Inc g v := by
      obtain ⟨W₀, hs₀, hV₀, hE₀⟩ := id hpath
      have hvs : v ∈ W₀.support := by
        rw [hV₀] at hv
        exact hv
      obtain ⟨e, he, -, -, -, hie, -⟩ := exists_two_edges_at_inner W₀ hs₀ hvs h₁ h₂
      exact ⟨e, hE₀ ▸ he, hie⟩
    obtain ⟨g, hg, hi⟩ := hedgeP
    have hv₂ : v ∈ V(G₂) := mem_V_of_closure hl₂ (hE₂ ▸ hg) (mem_closure_of_inc hi) (hPJ.1 hv)
    refine ⟨hv₂, fun hv₁ => ?_⟩
    have : v ∈ X := ⟨hv₁, hv₂⟩
    rw [hXeq] at this
    rcases this with h₃ | h₃
    · exact h₁ h₃
    · exact h₂ h₃
  have hV₂P : ∀ {v}, v ∈ V(G₂) \ V(G₁) → v ∈ P.V ∧ v ≠ x ∧ v ≠ y := by
    rintro v ⟨hv, hn⟩
    have hnX : v ∉ X := fun h₃ => hn h₃.1
    have hvx : v ≠ x := fun h₃ => hnX (h₃ ▸ hxX)
    have hvy : v ≠ y := fun h₃ => hnX (h₃ ▸ hyX)
    obtain ⟨g, hg, hi⟩ := hedge (hl₂.vertexSet_mono hv)
    have hg₂ := hside hv hnX hg hi
    have hgP : g ∈ P.E := hE₂ ▸ hg₂
    exact ⟨mem_V_of_inc_sub hPJ hgP hi, hvx, hvy⟩
  refine Or.inr ⟨hX₂, fun v hv => ?_, ?_⟩
  · obtain ⟨hvP, h₁, h₂⟩ := hV₂P hv
    obtain ⟨-, hall⟩ := hin v hvP h₁ h₂
    have hset : {g | J.toGraph.Inc g v} = {g | P.toGraph.Inc g v} := by
      ext g
      constructor
      · intro hi
        have hgP := hall g hi.edge_mem hi
        exact inc_of_mem_closure hgP (mem_closure_of_inc hi) hvP
      · intro hi
        exact inc_of_mem_closure (hPJ.2 hi.edge_mem) (mem_closure_of_inc hi) (hPJ.1 hvP)
    change {g | J.toGraph.Inc g v}.ncard = 2
    rw [hset]
    exact path_two hpath hvP h₁ h₂
  · rw [hE₂]
    have hsub : P.V \ {x, y} ⊆ V(G₂) \ V(G₁) := fun v hv =>
      hPinV hv.1 (fun h₃ => hv.2 (Or.inl h₃)) (fun h₃ => hv.2 (Or.inr h₃))
    have hfinV : (V(G₂) \ V(G₁)).Finite :=
      J.finite_V.subset fun z hz => hl₂.vertexSet_mono hz.1
    exact (path_count hpath hxy hxP hyP).trans (by
      have := ncard_le_ncard hsub hfinV
      omega)

end Sep

/-- **The union of a rigid drawing and a wheel is good.** -/
theorem good_of_wheel [ConnectedSpace S] (f : Frame H J Δ a) (r : Rad J Γ') (hw : Wheel W B Δ D₂)
    (hu : IsUnion H W J) (hB : ∀ v ∈ H.V, v ∈ W.V → v ∈ B) (hc : H.U ∩ W.U ⊆ H.V ∩ W.V)
    (hS : IsClosedSurface S) (hsph : IsSphere S) : Good J.toGraph := by
  classical
  have hJl : ∀ e v, ¬ J.toGraph.IsLink e v v := by
    intro e v hl
    have he : e ∈ H.E ∪ W.E := hu.hE ▸ hl.edge_mem
    rcases he with he | he
    · have hsub : Whitney.bdry J.toGraph {e} ⊆ {v} := by
        rintro z ⟨⟨g, rfl, t, ht⟩, -⟩
        rcases J.toGraph.eq_or_eq_of_isLink_of_isLink ht hl with h₁ | h₁ <;> exact h₁
      have hc : (Whitney.bdry J.toGraph {e}).ncard ≤ 2 :=
        (ncard_le_ncard hsub (toFinite _)).trans (by simp)
      obtain ⟨F, D, x, y, -, -, -, -, -, -, hxy, hcap, -, -, hF⟩ :=
        exists_dial_of_edge f r hS hsph (singleton_subset_iff.mpr he) hc
          ((toFinite ({v} : Set S)).subset hsub) rfl
      have hx : x ∈ F ∩ H.V := hcap ▸ Or.inl rfl
      have hy : y ∈ F ∩ H.V := hcap ▸ Or.inr rfl
      exact hxy ((hsub (hF hx)).trans (hsub (hF hy)).symm)
    · exact hw.nl e v ((hu.linkW e he v v).mp hl)
  refine ⟨J.finite_V, J.finite_edges, hJl, ?_, ?_⟩
  · obtain ⟨T, hTV, hT4, hT3⟩ := hw.four
    have hsub : T ⊆ {v | v ∈ V(J.toGraph) ∧ deg J.toGraph v ≠ 2} := by
      intro v hv
      have hvJ : v ∈ J.V := hu.hV ▸ Or.inr (hTV hv)
      refine ⟨hvJ, fun hd => ?_⟩
      have hmono : {e | W.toGraph.Inc e v} ⊆ {e | J.toGraph.Inc e v} := by
        rintro e ⟨t, ht⟩
        exact ⟨t, (hu.linkW e ht.edge_mem v t).mpr ht⟩
      have hfin : {e | J.toGraph.Inc e v}.Finite := J.finite_edges.subset fun e he => he.edge_mem
      have h₁ := ncard_le_ncard hmono hfin
      have h₂ := hT3 v hv
      change {e | J.toGraph.Inc e v}.ncard = 2 at hd
      omega
    exact hT4.trans (ncard_le_ncard hsub (J.finite_V.subset fun _ hz => hz.1))
  · intro G₁ G₂ hs hord
    obtain ⟨hl₁, hl₂, hV, hE, hdis⟩ := id hs
    set X := V(G₁) ∩ V(G₂) with hX
    let Y := X ∩ W.V
    have hYfin : Y.Finite := W.finite_V.subset inter_subset_right
    have hXfin : X.Finite := J.finite_V.subset fun z hz => hl₁.vertexSet_mono hz.1
    have hYc : Y.ncard ≤ 2 := (ncard_le_ncard inter_subset_left hXfin).trans hord
    have hWJ : W.U ⊆ J.U := by
      rw [W.U_eq, J.U_eq]
      refine union_subset_union (hu.hV ▸ subset_union_right) ?_
      rw [hu.hE]
      exact biUnion_subset_biUnion_left subset_union_right
    have hside := hw.side (pts G₁) (pts G₂) Y (isClosed_pts hl₁) (isClosed_pts hl₂)
      (hWJ.trans (pts_cover hs)) (by
        rintro z ⟨⟨hzW, h₁⟩, h₂⟩
        have hzX := pts_cap hs ⟨h₁, h₂⟩
        refine ⟨hzX, ?_⟩
        have hzJ : z ∈ J.V := hl₁.vertexSet_mono hzX.1
        rw [hu.hV] at hzJ
        rcases hzJ with hzH | hzW'
        · exact (hc ⟨H.V_subset_U hzH, hzW⟩).2
        · exact hzW') inter_subset_right hYc
    have hvert : ∀ {K : Graph S (Set S)}, K ≤ J.toGraph → W.V \ Y ⊆ pts K →
        W.V \ X ⊆ V(K) := by
      intro K hK hsub v hv
      have hvJ : v ∈ J.V := hu.hV ▸ Or.inr hv.1
      exact mem_V_of_pts hK (hsub ⟨hv.1, fun h₁ => hv.2 h₁.1⟩) hvJ
    rcases hside with h₁ | h₁
    · exact Or.inr (thin_of_side f r hw hu hB hS hsph hs hord (hvert hl₁ h₁) hJl)
    · have hs' : IsGraphSeparation J.toGraph G₂ G₁ :=
        ⟨hl₂, hl₁, by rw [union_comm]; exact hV, by rw [union_comm]; exact hE, hdis.symm⟩
      refine Or.inl (thin_of_side f r hw hu hB hS hsph hs' (by rw [inter_comm]; exact hord) ?_ hJl)
      rw [inter_comm]
      exact hvert hl₂ h₁

end GraphMinor.GM14.Whitney
