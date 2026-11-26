/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM17.Defs

/-!
# From hypergraphs to graphs, and the double subdivision

XVII (13.1) rests on XVI (3.1), which is on graphs in the sense of `Graph`, with minors whose edges
are edges of the graph. The minors of XVII are minors of the simple graph `G*`. If `H` has loops or
parallel edges, then an `H`-minor of `G` need not give one of `G*`. So we apply (3.1) to the graph
`subdiv H a b`, in which every edge of `H` is subdivided twice. This graph is simple,
a minor of it gives an `H`-minor of `G*` (`controlsMinor_of_subdiv`), and a drawing of `H` gives a
drawing of it (in `SubdivideDraw`).

`toGraph` turns a hypergraph that is a graph into a `Graph`, with the same vertices, edges and
incidences (`ofGraph_toGraph`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Graph

universe u v

variable {α : Type u} {β : Type v}

theorem exists_ends {G : Hypergraph α β} (hG : G.IsGraph) {e : β} (he : e ∈ G.edgeSet) : ∃ x y,
  G.ends e = {x, y} := by
  obtain ⟨hne, hc⟩ := hG e he
  have hfin : (G.ends e).Finite := G.vertexSet_finite.subset fun v hv => G.vertex_mem_of_inc hv
  have hpos : 0 < (G.ends e).ncard := (Set.ncard_pos hfin).mpr hne
  have hcases : (G.ends e).ncard = 1 ∨ (G.ends e).ncard = 2 := by omega
  rcases hcases with h | h
  · obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp h
    exact ⟨x, x, by simp [hx]⟩
  · obtain ⟨x, y, -, hx⟩ := Set.ncard_eq_two.mp h
    exact ⟨x, y, hx⟩

/-- A hypergraph that is a graph, as a `Graph`. -/
def toGraph (G : Hypergraph α β) (hG : G.IsGraph) : Graph α β where
  vertexSet := G.vertexSet
  IsLink e x y := e ∈ G.edgeSet ∧ x ∈ G.ends e ∧ y ∈ G.ends e ∧ G.ends e ⊆ {x, y}
  edgeSet := G.edgeSet
  isLink_symm := fun e _ => ⟨fun x y h => ⟨h.1, h.2.2.1, h.2.1, fun z hz => by
    rcases h.2.2.2 hz with h | h
    · exact Or.inr h
    · exact Or.inl h⟩⟩
  eq_or_eq_of_isLink_of_isLink := fun e x y v w h h' => by
    rcases h'.2.2.2 h.2.1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  edge_mem_iff_exists_isLink := fun e => by
    constructor
    · intro he
      obtain ⟨x, y, hxy⟩ := exists_ends hG he
      refine ⟨x, y, he, ?_, ?_, ?_⟩
      · rw [hxy]; exact Or.inl rfl
      · rw [hxy]; exact Or.inr rfl
      · rw [hxy]
    · rintro ⟨x, y, h⟩
      exact h.1
  left_mem_of_isLink := fun e x y h => G.vertex_mem_of_inc h.2.1

theorem ofGraph_toGraph (G : Hypergraph α β) (hG : G.IsGraph) (hV : V(toGraph G hG).Finite)
  (hE : E(toGraph G hG).Finite) :
    Hypergraph.ofGraph (toGraph G hG) hV hE = G := by
  refine Hypergraph.ext rfl rfl ?_
  funext e v
  apply propext
  constructor
  · rintro ⟨y, h⟩
    exact h.2.1
  · intro h
    obtain ⟨x, y, hxy⟩ := exists_ends hG (G.edge_mem_of_inc h)
    have hv : v ∈ G.ends e := h
    have hx : x ∈ G.ends e := by rw [hxy]; exact Or.inl rfl
    have hy : y ∈ G.ends e := by rw [hxy]; exact Or.inr rfl
    rw [hxy] at hv
    rcases hv with rfl | rfl
    · exact ⟨y, G.edge_mem_of_inc h, hx, hy, hxy.le⟩
    · refine ⟨x, G.edge_mem_of_inc h, hy, hx, ?_⟩
      rw [hxy, Set.pair_comm]

variable {α' β' : Type} (H : Hypergraph α' β') (a b : ↥H.edgeSet → α')

/-- The vertices of the double subdivision: those of `H`, and two for each edge. -/
abbrev SV := α' ⊕ (↥H.edgeSet × Bool)

/-- The edges of the double subdivision: three for each edge of `H`. -/
abbrev SE := ↥H.edgeSet × Fin 3

/-- The ends of an edge of the double subdivision. -/
def lnk : SE H → SV H × SV H
  | (e, 0) => (.inl (a e), .inr (e, false))
  | (e, 1) => (.inr (e, false), .inr (e, true))
  | (e, 2) => (.inr (e, true), .inl (b e))

/-- The double subdivision of `H`. -/
def subdiv (ha : ∀ e, a e ∈ H.vertexSet) (hb : ∀ e, b e ∈ H.vertexSet) : Graph (SV H) (SE H) where
  vertexSet := Sum.inl '' H.vertexSet ∪ range Sum.inr
  IsLink f x y := lnk H a b f = (x, y) ∨ lnk H a b f = (y, x)
  edgeSet := univ
  isLink_symm := fun e _ => ⟨fun x y h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink := fun f x y v w h h' => by
    rcases h with h | h <;> rcases h' with h' | h' <;> rw [h] at h' <;> simp only [Prod.mk.injEq]
      at h' <;> simp [h'.1, h'.2]
  edge_mem_iff_exists_isLink := fun f => ⟨fun _ => ⟨_, _, Or.inl rfl⟩, fun _ => mem_univ _⟩
  left_mem_of_isLink := fun f x y h => by
    obtain ⟨e, i⟩ := f
    fin_cases i <;> simp only [lnk, Prod.mk.injEq] at h <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      <;> simp [ha, hb]

/-- The vertex of `H` that a vertex of the double subdivision goes to under the contraction. The
middle edges are not contracted. -/
def own : SV H → α'
  | .inl v => v
  | .inr (e, false) => a e
  | .inr (e, true) => b e

variable {H a b}

theorem subdiv_inl {ha : ∀ e, a e ∈ H.vertexSet} {hb : ∀ e, b e ∈ H.vertexSet} {v : α'}
  (hv : v ∈ H.vertexSet) : (Sum.inl v : SV H) ∈ V(subdiv H a b ha hb) :=
  Or.inl (mem_image_of_mem _ hv)

theorem subdiv_inr {ha : ∀ e, a e ∈ H.vertexSet} {hb : ∀ e, b e ∈ H.vertexSet}
  (x : ↥H.edgeSet × Bool) : (Sum.inr x : SV H) ∈ V(subdiv H a b ha hb) :=
  Or.inr (mem_range_self x)

/-- A minor of the double subdivision gives a minor of `H` in the simple graph of `G`. -/
theorem controlsMinor_of_subdiv [Nonempty α] (hH : H.IsGraph) (hab : ∀ e : ↥H.edgeSet, H.ends e.1
  = {a e, b e}) (ha : ∀ e, a e ∈ H.vertexSet) (hb : ∀ e, b e ∈ H.vertexSet)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite) {T : Set (Hypergraph α β × Hypergraph α
      β)}
    (h : GM16.ControlsMinor G (subdiv H a b ha hb) T) : ControlsMinor
      (Hypergraph.ofGraph G hV hE) T H := by
  classical
  obtain ⟨αv, αe, h1, h2, h3, -, -, h6⟩ := h
  set L := subdiv H a b ha hb with hL
  let K := Hypergraph.ofGraph G hV hE
  have piece : ∀ {w w' : SV H}, w ∈ V(L) → w' ∈ V(L) → ∀ {x : α}, x ∈ V(αv w) → x ∈ V(αv w') → w
    = w' := fun {w w'} hw hw' {x} hx hx' => by
    by_contra hne
    exact Set.disjoint_left.mp (h2 w hw w' hw' hne) hx hx'
  have link : ∀ (f : SE H), (lnk H a b f).1 ≠ (lnk H a b f).2 → (lnk H a b f).1 ∈ V(L) →
    (lnk H a b f).2 ∈ V(L) →
      ∃ x ∈ V(αv (lnk H a b f).1), ∃ y ∈ V(αv (lnk H a b f).2), G.IsLink (αe f) x y
        := fun f hne hu hw =>
    (h3 f (mem_univ f) _ hu _ hw hne (Or.inl rfl)).2
  have hmid : ∀ e : ↥H.edgeSet, ∃ x ∈ V(αv (.inr (e, false))), ∃ y ∈ V(αv (.inr
    (e, true))), G.IsLink (αe (e, 1)) x y := fun e =>
    link (e, 1) (by simp [lnk]) (subdiv_inr _) (subdiv_inr _)
  choose p hp q hq hpq using hmid
  have hleft : ∀ e : ↥H.edgeSet, ∃ x ∈ V(αv (.inl (a e))), ∃ y ∈ V(αv (.inr (e, false))), G.IsLink
    (αe (e, 0)) x y := fun e =>
    link (e, 0) (by simp [lnk]) (subdiv_inl (ha e)) (subdiv_inr _)
  have hright : ∀ e : ↥H.edgeSet, ∃ x ∈ V(αv (.inr (e, true))), ∃ y ∈ V(αv (.inl (b e))), G.IsLink
    (αe (e, 2)) x y := fun e =>
    link (e, 2) (by simp [lnk]) (subdiv_inr _) (subdiv_inl (hb e))
  let av : α' → Set α := fun v => {x | ∃ w ∈ V(L), own H a b w = v ∧ x ∈ V(αv w)}
  let o : α := Classical.arbitrary α
  let ae : β' → Sym2 α := fun e => if he : e ∈ H.edgeSet then s(p ⟨e, he⟩, q ⟨e, he⟩) else s(o, o)
  have hae : ∀ e : ↥H.edgeSet, ae e.1 = s(p e, q e) := fun e => by simp [ae, e.2]
  let ae' : α' → Set (Sym2 α) := fun v => {z | z ∈ K.skeleton.edgeSet ∧ (∀ u ∈ z, u ∈ av v)
    ∧ ∀ e ∈ H.edgeSet, z ≠ ae e}
  have hadj : ∀ {f : β} {x y : α}, G.IsLink f x y → x ≠ y → s(x, y) ∈ K.skeleton.edgeSet
    := fun {f x y} hl hne => by
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨hne, f, hl.inc_left, hl.inc_right⟩
  have hsame : ∀ {w : SV H}, w ∈ V(L) → ∀ {x y : α}, x ∈ V(αv w) → y ∈ V(αv w)
    → ∀ e ∈ H.edgeSet, s(x, y) ≠ ae e := by
    intro w hw x y hx hy e he heq
    rw [show ae e = s(p ⟨e, he⟩, q ⟨e, he⟩) from hae ⟨e, he⟩, Sym2.eq_iff] at heq
    have h4 : w = .inr (⟨e, he⟩, false) := by
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact piece hw (subdiv_inr _) hx (hp _)
      · exact piece hw (subdiv_inr _) hy (hp _)
    have h5 : w = .inr (⟨e, he⟩, true) := by
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact piece hw (subdiv_inr _) hy (hq _)
      · exact piece hw (subdiv_inr _) hx (hq _)
    rw [h4] at h5
    simp at h5
  have hmemav : ∀ {w : SV H}, w ∈ V(L) → ∀ {x : α}, x ∈ V(αv w) → x ∈ av (own H a b w)
    := fun {w} hw {x} hx => ⟨w, hw, rfl, hx⟩
  have hbr : ∀ {v : α'}, v ∈ H.vertexSet → ∀ {w : SV H}, w ∈ V(L) → own H a b w = v
    → ∀ {x y : α}, x ∈ V(αv w) → y ∈ V(αv w) →
      Relation.ReflTransGen (fun c d ↦ s(c, d) ∈ ae' v) x y := by
    intro v _ w hw hown x y hx hy
    have hconn := ((h1 w hw).2.2.2 x hx y hy)
    clear hy
    induction hconn with
    | refl => exact .refl
    | tail hp₁ hst ih =>
      rename_i c d
      obtain ⟨g, hg⟩ := hst
      have hc : c ∈ V(αv w) := hg.left_mem
      have hd : d ∈ V(αv w) := hg.right_mem
      by_cases hcd : c = d
      · exact hcd ▸ ih
      · refine ih.tail ⟨hadj ((h1 w hw).1.isLink_mono hg) hcd, ?_, hsame hw hc hd⟩
        intro u hu
        rw [Sym2.mem_iff] at hu
        rcases hu with rfl | rfl
        · exact hown ▸ hmemav hw hc
        · exact hown ▸ hmemav hw hd
  have hcross : ∀ {v : α'} {x y : α}, x ∈ V(αv (.inl v)) → v ∈ H.vertexSet →
    (∃ w ∈ V(L), w ≠ .inl v ∧ own H a b w = v ∧ y ∈ V(αv w)) → ∀ {f : β}, G.IsLink f x y →
      s(x, y) ∈ ae' v := by
    rintro v x y hx hv ⟨w, hw, hne, hown, hy⟩ f hl
    have hxy : x ≠ y := fun he => hne (piece hw (subdiv_inl hv) hy (he ▸ hx))
    refine ⟨hadj hl hxy, ?_, fun e he heq => ?_⟩
    · intro u hu
      rw [Sym2.mem_iff] at hu
      rcases hu with rfl | rfl
      · exact ⟨.inl v, subdiv_inl hv, rfl, hx⟩
      · exact hown ▸ hmemav hw hy
    · rw [show ae e = s(p ⟨e, he⟩, q ⟨e, he⟩) from hae ⟨e, he⟩, Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact absurd (piece (subdiv_inl hv) (subdiv_inr _) hx (hp _)) (by simp)
      · exact absurd (piece (subdiv_inl hv) (subdiv_inr _) hx (hq _)) (by simp)
  have hsymm : ∀ v {x y : α}, Relation.ReflTransGen (fun c d ↦ s(c, d) ∈ ae' v) x y
    → Relation.ReflTransGen (fun c d ↦ s(c, d) ∈ ae' v) y x := fun v {x y} h => by
    have : Std.Symm (fun c d ↦ s(c, d) ∈ ae' v) := ⟨fun c d h => by
      show s(d, c) ∈ ae' v
      rw [Sym2.eq_swap]
      exact h⟩
    exact Relation.ReflTransGen.stdSymm.symm x y h
  have hbase : ∀ {v : α'}, v ∈ H.vertexSet → ∀ {b₀ : α}, b₀ ∈ V(αv (.inl v))
    → ∀ x ∈ av v, Relation.ReflTransGen (fun c d ↦ s(c, d) ∈ ae' v) x b₀ := by
    rintro v hv b₀ hb₀ x ⟨w, hw, hown, hx⟩
    rcases w with v' | ⟨e, _ | _⟩
    · obtain rfl : v' = v := hown
      exact hbr hv hw rfl hx hb₀
    · have hown' : a e = v := hown
      obtain ⟨c, hc, d, hd, hl⟩ := hleft e
      rw [hown'] at hc
      have h4 : s(c, d) ∈ ae' v := hcross hc hv ⟨_, subdiv_inr _, by simp, hown, hd⟩ hl
      exact ((hbr hv hw hown hx hd).trans (hsymm v (.single h4))).trans (hbr hv
        (subdiv_inl hv) rfl hc hb₀)
    · have hown' : b e = v := hown
      obtain ⟨c, hc, d, hd, hl⟩ := hright e
      rw [hown'] at hd
      have h4 : s(d, c) ∈ ae' v := hcross hd hv ⟨_, subdiv_inr _, by simp, hown, hc⟩ hl.symm
      exact ((hbr hv hw hown hx hc).trans (hsymm v (.single h4))).trans (hbr hv
        (subdiv_inl hv) rfl hd hb₀)
  have hend : ∀ {e : β'} (he : e ∈ H.edgeSet), p ⟨e, he⟩ ∈ av (a ⟨e, he⟩) ∧ q ⟨e, he⟩ ∈ av
    (b ⟨e, he⟩) := fun {e} he =>
    ⟨hmemav (subdiv_inr (_, false)) (hp _), hmemav (subdiv_inr (_, true)) (hq _)⟩
  refine ⟨hH, av, ae', ae, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hw := subdiv_inl (ha := ha) (hb := hb) hv
    obtain ⟨b₀, hb₀⟩ := (h1 _ hw).2.1
    refine ⟨⟨b₀, _, hw, rfl, hb₀⟩, ?_, fun z hz => hz.1, fun x y hz => ⟨hz.2.1 _
      (Sym2.mem_mk_left x y), hz.2.1 _ (Sym2.mem_mk_right x y)⟩, fun x hx y hy => ?_⟩
    · rintro x ⟨w, hw', -, hx⟩
      exact (h1 w hw').1.vertexSet_mono hx
    · exact (hbase hv hb₀ x hx).trans (hsymm v (hbase hv hb₀ y hy))
  · intro u _ v _ hne
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨w, hw, rfl, hx⟩ ⟨w', hw', rfl, hx'⟩
    exact hne (by rw [piece hw hw' hx hx'])
  · intro e he
    rw [show ae e = s(p ⟨e, he⟩, q ⟨e, he⟩) from hae ⟨e, he⟩]
    refine hadj (hpq ⟨e, he⟩) fun heq => ?_
    have := piece (subdiv_inr _) (subdiv_inr _) (hp ⟨e, he⟩) (heq ▸ hq ⟨e, he⟩)
    simp at this
  · intro e he f hf heq
    have h4 : s(p ⟨e, he⟩, q ⟨e, he⟩) = s(p ⟨f, hf⟩, q ⟨f, hf⟩) := by
      rw [← hae ⟨e, he⟩, ← hae ⟨f, hf⟩]
      exact heq
    rw [Sym2.eq_iff] at h4
    rcases h4 with ⟨h5, -⟩ | ⟨h5, -⟩
    · have := piece (subdiv_inr _) (subdiv_inr _) (hp ⟨e, he⟩) (h5 ▸ hp ⟨f, hf⟩)
      simpa using this
    · have := piece (subdiv_inr _) (subdiv_inr _) (hp ⟨e, he⟩) (h5 ▸ hq ⟨f, hf⟩)
      simp at this
  · intro e he u v huv hu hv
    have hu' : u ∈ H.ends e := hu
    have hv' : v ∈ H.ends e := hv
    rw [hab ⟨e, he⟩] at hu' hv'
    obtain ⟨hp₁, hq₁⟩ := hend he
    rw [show ae e = s(p ⟨e, he⟩, q ⟨e, he⟩) from hae ⟨e, he⟩]
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact absurd rfl huv
    · exact ⟨_, hp₁, _, hq₁, rfl⟩
    · exact ⟨_, hq₁, _, hp₁, Sym2.eq_swap⟩
    · exact absurd rfl huv
  · intro e he v hv
    have h4 := hab ⟨e, he⟩
    rw [show H.ends (⟨e, he⟩ : ↥H.edgeSet) = {v} from hv] at h4
    have ha' : a ⟨e, he⟩ = v := by
      have : a ⟨e, he⟩ ∈ ({v} : Set α') := by rw [h4]; exact Or.inl rfl
      exact this
    have hb' : b ⟨e, he⟩ = v := by
      have : b ⟨e, he⟩ ∈ ({v} : Set α') := by rw [h4]; exact Or.inr rfl
      exact this
    obtain ⟨hp₁, hq₁⟩ := hend he
    rw [ha'] at hp₁
    rw [hb'] at hq₁
    refine ⟨_, hp₁, _, hq₁, hae ⟨e, he⟩, fun hz => hz.2.2 e he rfl⟩
  · intro A B hAB hord v hv hsub
    have hw := subdiv_inl (ha := ha) (hb := hb) hv
    have hfinL : V(L).Finite := by
      refine (H.vertexSet_finite.image _).union ?_
      have : Finite ↥H.edgeSet := H.edgeSet_finite.to_subtype
      exact Set.finite_range _
    have hle : H.vertexSet.ncard ≤ V(L).ncard := by
      rw [← Set.ncard_image_of_injective _ Sum.inl_injective]
      exact Set.ncard_le_ncard subset_union_left hfinL
    exact h6 hAB (hord.trans_le hle) _ hw fun x hx => hsub ⟨_, hw, rfl, hx⟩

end GraphMinor.GM17
