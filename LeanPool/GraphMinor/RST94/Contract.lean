/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section3a

/-!
# Contracting an edge

The graph `G/e` used in the proof of (4.1) of "Quickly excluding a planar graph" (page 335). We keep
the end `u` of `e` and remove the
end `v`. An edge at `v` becomes an edge at `u`. The paper uses `G/e` and lifts separations by hand,
and here `contract_lift_up` and
`contract_lift_down` are the paper's two lifts.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G H A₀ B₀ X Y : Hypergraph α β} {e : β} {u v : α}

/-- The graph `G/e` for an edge `e` with ends `u ≠ v`: it has the vertices of `G` other than `v` and
the edges of `G` other than `e`, and
an edge at `v` is an edge at `u`. -/
def contract (G : Hypergraph α β) (e : β) (u v : α) (hu : u ∈ G.vertexSet)
  (huv : u ≠ v) : Hypergraph α β where
  vertexSet := G.vertexSet \ {v}
  edgeSet := G.edgeSet \ {e}
  Inc f x := f ≠ e ∧ x ≠ v ∧ (G.Inc f x ∨ (x = u ∧ G.Inc f v))
  vertex_mem_of_inc := by
    rintro f x ⟨-, hx, h | ⟨rfl, -⟩⟩
    · exact ⟨G.vertex_mem_of_inc h, hx⟩
    · exact ⟨hu, hx⟩
  edge_mem_of_inc := by
    rintro f x ⟨hf, -, h | ⟨-, h⟩⟩
    · exact ⟨G.edge_mem_of_inc h, hf⟩
    · exact ⟨G.edge_mem_of_inc h, hf⟩
  vertexSet_finite := G.vertexSet_finite.subset sdiff_subset
  edgeSet_finite := G.edgeSet_finite.subset sdiff_subset

variable {hu : u ∈ G.vertexSet} {huv : u ≠ v}

open Classical in
/-- The map from `V(G)` to `V(G/e)`. -/
noncomputable def contractMap (u v : α) (x : α) : α := if x = v then u else x

omit hu huv in
theorem contractMap_of_ne {x : α} (h : x ≠ v) : contractMap u v x = x := by
  simp [contractMap, h]

omit hu huv in
theorem contractMap_self : contractMap u v v = u := by
  simp [contractMap]

theorem contractMap_inc {f : β} {x : α} (hf : f ≠ e) (h : G.Inc f x) :
    (contract G e u v hu huv).Inc f (contractMap u v x) := by
  by_cases hx : x = v
  · subst hx
    rw [contractMap_self]
    exact ⟨hf, huv, Or.inr ⟨rfl, h⟩⟩
  · rw [contractMap_of_ne hx]
    exact ⟨hf, hx, Or.inl h⟩

/-- `G/e` is a graph. -/
theorem isGraph_contract (hG : G.IsGraph) : (contract G e u v hu huv).IsGraph := by
  rintro f ⟨hf, hfe⟩
  obtain ⟨⟨x, hx⟩, h₂⟩ := hG f hf
  refine ⟨⟨_, contractMap_inc (hu := hu) (huv := huv) hfe hx⟩, ?_⟩
  have hsub : (contract G e u v hu huv).ends f ⊆ contractMap u v '' G.ends f := by
    rintro y ⟨-, hy, hi | ⟨rfl, hi⟩⟩
    · exact ⟨y, hi, contractMap_of_ne hy⟩
    · exact ⟨v, hi, contractMap_self⟩
  have hfin : (G.ends f).Finite := G.vertexSet_finite.subset fun _ h => G.vertex_mem_of_inc h
  exact (ncard_le_ncard hsub (hfin.image _)).trans ((ncard_image_le hfin).trans h₂)

/-- A subgraph of `G` that avoids `v` and `e` and the edges at `v` is a subgraph of `G/e`. -/
theorem le_contract (hH : H ≤ G) (hv : v ∉ H.vertexSet) (he : e ∉ H.edgeSet)
  (hno : ∀ f ∈ H.edgeSet, ¬ G.Inc f v) :
    H ≤ contract G e u v hu huv := by
  refine ⟨fun x hx => ⟨hH.vertexSet_subset hx, fun h => hv (h ▸ hx)⟩,
    fun f hf => ⟨hH.edgeSet_subset hf, fun h => he (h ▸ hf)⟩, fun f hf => ?_⟩
  ext x
  constructor
  · rintro ⟨-, -, h | ⟨-, h⟩⟩
    · exact inc_le hH hf h
    · exact absurd h (hno f hf)
  · intro h
    have hi := inc_of_le hH h
    exact ⟨fun e' => he (e' ▸ hf), fun e' => hno f hf (e' ▸ hi), Or.inl hi⟩

/-- A subgraph of `G/e` that avoids `u` is a subgraph of `G`, and it avoids `v` and `e` and the
edges at `v`. -/
theorem le_of_le_contract (hH : H ≤ contract G e u v hu huv) (huH : u ∉ H.vertexSet) :
    H ≤ G ∧ v ∉ H.vertexSet ∧ e ∉ H.edgeSet ∧ ∀ f ∈ H.edgeSet, ¬ G.Inc f v := by
  have hno : ∀ f ∈ H.edgeSet, ¬ G.Inc f v := fun f hf hi => by
    have hfc := hH.edgeSet_subset hf
    have : (contract G e u v hu huv).Inc f u := ⟨hfc.2, huv, Or.inr ⟨rfl, hi⟩⟩
    exact huH (end_mem hH hf this)
  refine ⟨⟨fun x hx => (hH.vertexSet_subset hx).1, fun f hf => (hH.edgeSet_subset hf).1, fun f hf
    => ?_⟩,
    fun hv => (hH.vertexSet_subset hv).2 rfl, fun he => (hH.edgeSet_subset he).2 rfl, hno⟩
  ext x
  constructor
  · intro h
    have hx : x ≠ v := fun e' => hno f hf (e' ▸ h)
    exact inc_le hH hf ⟨(hH.edgeSet_subset hf).2, hx, Or.inl h⟩
  · intro h
    obtain ⟨-, -, h' | ⟨-, h'⟩⟩ := inc_of_le hH h
    · exact h'
    · exact absurd h' (hno f hf)

/-- Two subgraphs with the same vertices and edges inside `H` have the same intersection with `H`.
-/
theorem inter_eq_of_agree {G₁ G₂ : Hypergraph α β} (hX : X ≤ G₁) (hY : Y ≤ G₂) (hH₁ : H ≤ G₁)
  (hH₂ : H ≤ G₂)
    (hV : ∀ x ∈ H.vertexSet, x ∈ X.vertexSet ↔ x ∈ Y.vertexSet) (hE : ∀ f ∈ H.edgeSet, f ∈
      X.edgeSet ↔ f ∈ Y.edgeSet) :
    X ∩ H = Y ∩ H := by
  refine sub_ext (G := H) (inter_le_right hX hH₁) (inter_le_right hY hH₂) ?_ ?_
  · ext x
    exact ⟨fun h => ⟨(hV x h.2).1 h.1, h.2⟩, fun h => ⟨(hV x h.2).2 h.1, h.2⟩⟩
  · ext f
    exact ⟨fun h => ⟨(hE f h.2).1 h.1, h.2⟩, fun h => ⟨(hE f h.2).2 h.1, h.2⟩⟩

/-- The first lift of the proof of (4.1) (pages 335–336): a separation of `G/e` gives a separation
of `G`, of order at most one more, and if
the order is one more then `e` is on the left. -/
theorem contract_lift_up (hG : G.IsGraph) (heu : G.Inc e u) (hev : G.Inc e v)
    (hs : (contract G e u v hu huv).IsSeparation A₀ B₀) :
    ∃ A' B', G.IsSeparation A' B' ∧ A₀.vertexSet ⊆ A'.vertexSet ∧
      separationOrder A' B' ≤ separationOrder A₀ B₀ + 1 ∧
      (separationOrder A' B' = separationOrder A₀ B₀ + 1 → e ∈ A'.edgeSet) ∧
      (∀ x, x ≠ v → (x ∈ A'.vertexSet ↔ x ∈ A₀.vertexSet)) ∧ (∀ x, x ≠ v →
        (x ∈ B'.vertexSet ↔ x ∈ B₀.vertexSet)) ∧
      (∀ f, f ≠ e → (f ∈ A'.edgeSet ↔ f ∈ A₀.edgeSet)) ∧ (∀ f, f ≠ e →
        (f ∈ B'.edgeSet ↔ f ∈ B₀.edgeSet)) := by
  classical
  have hAc := hs.left_le
  have hBc := hs.right_le
  have huc : u ∈ (contract G e u v hu huv).vertexSet := ⟨hu, huv⟩
  have hsubV : ∀ {Y : Hypergraph α β}, Y ≤ contract G e u v hu huv → Y.vertexSet ∪ {x | x = v
    ∧ u ∈ Y.vertexSet} ⊆ G.vertexSet := by
    rintro Y hY x (hx | ⟨rfl, -⟩)
    · exact (hY.vertexSet_subset hx).1
    · exact G.vertex_mem_of_inc hev
  have hend : ∀ {Y : Hypergraph α β}, Y ≤ contract G e u v hu huv → ∀ f ∈ Y.edgeSet, ∀ x, G.Inc f x
    →
      x ∈ Y.vertexSet ∪ {x | x = v ∧ u ∈ Y.vertexSet} := by
    intro Y hY f hf x hx
    have hfe := (hY.edgeSet_subset hf).2
    by_cases hxv : x = v
    · subst hxv
      exact Or.inr ⟨rfl, end_mem hY hf ⟨hfe, huv, Or.inr ⟨rfl, hx⟩⟩⟩
    · exact Or.inl (end_mem hY hf ⟨hfe, hxv, Or.inl hx⟩)
  have heE : e ∈ G.edgeSet := G.edge_mem_of_inc heu
  have hee : ∀ {Y : Hypergraph α β}, u ∈ Y.vertexSet → ∀ x, G.Inc e x → x ∈ Y.vertexSet ∪ {x | x
    = v ∧ u ∈ Y.vertexSet} := fun {Y} hY x hx => by
    rcases end_eq_or hG heu hev huv hx with rfl | rfl
    · exact Or.inl hY
    · exact Or.inr ⟨rfl, hY⟩
  let A' := subOf G (A₀.vertexSet ∪ {x | x = v ∧ u ∈ A₀.vertexSet}) (A₀.edgeSet ∪ {f | f = e
    ∧ u ∈ A₀.vertexSet}) (hsubV hAc) (by
    rintro f (hf | ⟨rfl, hf⟩)
    · exact ⟨(hAc.edgeSet_subset hf).1, hend hAc f hf⟩
    · exact ⟨heE, hee hf⟩)
  have huB : u ∉ A₀.vertexSet → u ∈ B₀.vertexSet := fun h => (mem_V_or hs huc).resolve_left h
  let B' := subOf G (B₀.vertexSet ∪ {x | x = v ∧ u ∈ B₀.vertexSet}) (B₀.edgeSet ∪ {f | f = e
    ∧ u ∉ A₀.vertexSet}) (hsubV hBc) (by
    rintro f (hf | ⟨rfl, hf⟩)
    · exact ⟨(hBc.edgeSet_subset hf).1, hend hBc f hf⟩
    · exact ⟨heE, hee (huB hf)⟩)
  have hsep : G.IsSeparation A' B' := by
    refine sep_of_sets subOf_le subOf_le (fun x hx => ?_) (fun f hf => ?_) ?_
    · by_cases hxv : x = v
      · subst hxv
        exact (mem_V_or hs huc).imp (fun h => Or.inr ⟨rfl, h⟩) fun h => Or.inr ⟨rfl, h⟩
      · exact (mem_V_or hs ⟨hx, hxv⟩).imp Or.inl Or.inl
    · by_cases hfe : f = e
      · subst hfe
        by_cases h : u ∈ A₀.vertexSet
        · exact Or.inl (Or.inr ⟨rfl, h⟩)
        · exact Or.inr (Or.inr ⟨rfl, h⟩)
      · exact (mem_E_or hs ⟨hf, hfe⟩).imp Or.inl Or.inl
    · rintro f (hf | ⟨h₁, hf⟩) (hf' | ⟨h₂, hf'⟩)
      · exact hs.notMem_edgeSet_right hf hf'
      · exact (hAc.edgeSet_subset hf).2 h₂
      · exact (hBc.edgeSet_subset hf').2 h₁
      · exact hf' hf
  have hsub₁ : (A' ∩ B').vertexSet ⊆ insert v (A₀ ∩ B₀).vertexSet := by
    rintro x ⟨hx | ⟨h₁, -⟩, hx' | ⟨h₂, -⟩⟩
    · exact Or.inr ⟨hx, hx'⟩
    · exact Or.inl h₂
    · exact Or.inl h₁
    · exact Or.inl h₁
  have hfin := (A₀ ∩ B₀).vertexSet_finite
  have ho₁ : separationOrder A' B' ≤ separationOrder A₀ B₀ + 1 :=
    (ncard_le_ncard hsub₁ (hfin.insert v)).trans (ncard_insert_le _ _)
  have hAv : ∀ x, x ≠ v → (x ∈ A'.vertexSet ↔ x ∈ A₀.vertexSet) := fun x hx =>
    ⟨fun h => h.resolve_right fun h' => hx h'.1, Or.inl⟩
  have hBv : ∀ x, x ≠ v → (x ∈ B'.vertexSet ↔ x ∈ B₀.vertexSet) := fun x hx =>
    ⟨fun h => h.resolve_right fun h' => hx h'.1, Or.inl⟩
  refine ⟨A', B', hsep, fun x hx => Or.inl hx, ho₁, fun heq => ?_, hAv, hBv, ?_, ?_⟩
  · -- If `e` is not on the left then `u ∉ V(A₀)`, and `v` is not on the left, so the order does
    -- not grow.
    by_contra hne
    have hu' : u ∉ A₀.vertexSet := fun h => hne (Or.inr ⟨rfl, h⟩)
    have hvA : v ∉ A'.vertexSet := by
      rintro (hv | ⟨-, h⟩)
      · exact (hAc.vertexSet_subset hv).2 rfl
      · exact hu' h
    have hsub₂ : (A' ∩ B').vertexSet ⊆ (A₀ ∩ B₀).vertexSet := fun x hx => by
      have hxv : x ≠ v := fun e' => hvA (e' ▸ hx.1)
      exact ⟨(hAv x hxv).1 hx.1, (hBv x hxv).1 hx.2⟩
    have := ncard_le_ncard hsub₂ hfin
    change (A' ∩ B').vertexSet.ncard = (A₀ ∩ B₀).vertexSet.ncard + 1 at heq
    omega
  · intro f hf
    exact ⟨fun h => h.resolve_right fun h' => hf h'.1, Or.inl⟩
  · intro f hf
    exact ⟨fun h => h.resolve_right fun h' => hf h'.1, Or.inl⟩

/-- The second lift of the proof of (4.1) (page 336): a separation `(A', B')` of `G` gives a
separation `(A*, B*)` of `G/e`, of order at most that
of `(A', B')`. -/
theorem contract_lift_down {A' B' : Hypergraph α β} (heu : G.Inc e u) (hev : G.Inc e v)
  (hs : G.IsSeparation A' B') :
    ∃ A₁ B₁, (contract G e u v hu huv).IsSeparation A₁ B₁ ∧ separationOrder A₁ B₁
      ≤ separationOrder A' B' ∧
      (∀ x, x ≠ v → x ≠ u → (x ∈ A₁.vertexSet ↔ x ∈ A'.vertexSet)) ∧ (∀ x, x ≠ v → x ≠ u →
        (x ∈ B₁.vertexSet ↔ x ∈ B'.vertexSet)) ∧
      (∀ f, f ≠ e → (f ∈ A₁.edgeSet ↔ f ∈ A'.edgeSet)) ∧ (∀ f, f ≠ e →
        (f ∈ B₁.edgeSet ↔ f ∈ B'.edgeSet)) := by
  classical
  have hsubV : ∀ {Y : Hypergraph α β}, Y ≤ G → {x | x ≠ v ∧ (x ∈ Y.vertexSet ∨ (x = u
    ∧ v ∈ Y.vertexSet))} ⊆ (contract G e u v hu huv).vertexSet := by
    rintro Y hY x ⟨hxv, hx | ⟨rfl, -⟩⟩
    · exact ⟨hY.vertexSet_subset hx, hxv⟩
    · exact ⟨hu, hxv⟩
  have hsubE : ∀ {Y : Hypergraph α β}, Y ≤ G → ∀ f ∈ Y.edgeSet \ {e}, f ∈
    (contract G e u v hu huv).edgeSet ∧
      ∀ x, (contract G e u v hu huv).Inc f x → x ∈ {x | x ≠ v ∧ (x ∈ Y.vertexSet ∨ (x = u
        ∧ v ∈ Y.vertexSet))} := by
    intro Y hY f hf
    refine ⟨⟨hY.edgeSet_subset hf.1, hf.2⟩, ?_⟩
    rintro x ⟨-, hxv, hi | ⟨rfl, hi⟩⟩
    · exact ⟨hxv, Or.inl (end_mem hY hf.1 hi)⟩
    · exact ⟨hxv, Or.inr ⟨rfl, end_mem hY hf.1 hi⟩⟩
  have hAG := hs.left_le
  have hBG := hs.right_le
  let A₁ := subOf (contract G e u v hu huv) _ _ (hsubV hAG) (hsubE hAG)
  let B₁ := subOf (contract G e u v hu huv) _ _ (hsubV hBG) (hsubE hBG)
  have hsep : (contract G e u v hu huv).IsSeparation A₁ B₁ := by
    refine sep_of_sets subOf_le subOf_le (fun x hx => ?_) (fun f hf => ?_) ?_
    · exact (mem_V_or hs hx.1).imp (fun h => ⟨hx.2, Or.inl h⟩) fun h => ⟨hx.2, Or.inl h⟩
    · exact (mem_E_or hs hf.1).imp (fun h => ⟨h, hf.2⟩) fun h => ⟨h, hf.2⟩
    · exact fun f hf hf' => hs.notMem_edgeSet_right hf.1 hf'.1
  have hside : (u ∈ A'.vertexSet ∧ v ∈ A'.vertexSet) ∨ (u ∈ B'.vertexSet ∧ v ∈ B'.vertexSet) := by
    have heE : e ∈ G.edgeSet := G.edge_mem_of_inc heu
    exact (mem_E_or hs heE).imp (fun h => ⟨end_mem hAG h heu, end_mem hAG h hev⟩)
      fun h => ⟨end_mem hBG h heu, end_mem hBG h hev⟩
  have hsub : (A₁ ∩ B₁).vertexSet ⊆ contractMap u v '' (A' ∩ B').vertexSet := by
    rintro x ⟨⟨hxv, hx⟩, -, hx'⟩
    by_cases hxu : x = u
    · subst hxu
      have hA : x ∈ A'.vertexSet ∨ v ∈ A'.vertexSet := hx.imp id fun h => h.2
      have hB : x ∈ B'.vertexSet ∨ v ∈ B'.vertexSet := hx'.imp id fun h => h.2
      have hcases : (x ∈ A'.vertexSet ∧ x ∈ B'.vertexSet) ∨ (v ∈ A'.vertexSet ∧ v ∈ B'.vertexSet)
        := by
        rcases hside with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · rcases hB with hB | hB
          · exact Or.inl ⟨h₁, hB⟩
          · exact Or.inr ⟨h₂, hB⟩
        · rcases hA with hA | hA
          · exact Or.inl ⟨hA, h₁⟩
          · exact Or.inr ⟨hA, h₂⟩
      rcases hcases with h | h
      · exact ⟨x, h, contractMap_of_ne hxv⟩
      · exact ⟨v, h, contractMap_self⟩
    · exact ⟨x, ⟨hx.resolve_right fun h => hxu h.1, hx'.resolve_right fun h
      => hxu h.1⟩, contractMap_of_ne hxv⟩
  have hfin := (A' ∩ B').vertexSet_finite
  refine ⟨A₁, B₁, hsep, (ncard_le_ncard hsub (hfin.image _)).trans (ncard_image_le hfin), ?_, ?_,
    ?_, ?_⟩
  · exact fun x hv' hu' => ⟨fun h => h.2.resolve_right fun h' => hu' h'.1, fun h => ⟨hv', Or.inl h⟩⟩
  · exact fun x hv' hu' => ⟨fun h => h.2.resolve_right fun h' => hu' h'.1, fun h => ⟨hv', Or.inl h⟩⟩
  · exact fun f hf => ⟨fun h => h.1, fun h => ⟨h, hf⟩⟩
  · exact fun f hf => ⟨fun h => h.1, fun h => ⟨h, hf⟩⟩

/-- Adjacent vertices of `G/e` are joined by a walk of `G` that may also use `v`, if one of them is
`u`. -/
theorem exists_walk_of_adj (heu : G.Inc e u) (hev : G.Inc e v) {x y : α} (h :
  (contract G e u v hu huv).skeleton.Adj x y) :
    ∃ w : G.skeleton.Walk x y, ∀ z ∈ w.support, z = x ∨ z = y ∨ (z = v ∧ (x = u ∨ y = u)) := by
  obtain ⟨hne, f, ⟨-, hx, h₁⟩, ⟨-, hy, h₂⟩⟩ := h
  have hadjuv : G.skeleton.Adj u v := ⟨huv, e, heu, hev⟩
  rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
  · have hadj : G.skeleton.Adj x y := ⟨hne, f, h₁, h₂⟩
    refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, fun z hz => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    exact hz.imp id Or.inl
  · have hadj : G.skeleton.Adj x v := ⟨hx, f, h₁, h₂⟩
    refine ⟨SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.cons hadjuv.symm SimpleGraph.Walk.nil),
      fun z hz => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · have hadj : G.skeleton.Adj v y := ⟨hy.symm, f, h₁, h₂⟩
    refine ⟨SimpleGraph.Walk.cons hadjuv (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), fun z
      hz => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · exact absurd rfl hne

/-- A walk of `G/e` lifts to a walk of `G` with the same ends. Its only new vertex is `v`, and only
if the walk passes through `u`. -/
theorem exists_walk_lift (heu : G.Inc e u) (hev : G.Inc e v) {a b : α} (p :
  (contract G e u v hu huv).skeleton.Walk a b) :
    ∃ w : G.skeleton.Walk a b, ∀ z ∈ w.support, z ∈ p.support ∨ (z = v ∧ u ∈ p.support) := by
  classical
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, fun z hz => Or.inl hz⟩
  | @cons x y c hadj q ih =>
    obtain ⟨w₁, h₁⟩ := exists_walk_of_adj heu hev hadj
    obtain ⟨w₂, h₂⟩ := ih
    refine ⟨w₁.append w₂, fun z hz => ?_⟩
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with hz | hz
    · rcases h₁ z hz with rfl | rfl | ⟨rfl, rfl | rfl⟩
      · exact Or.inl (by simp)
      · exact Or.inl (by simp)
      · exact Or.inr ⟨rfl, by simp⟩
      · exact Or.inr ⟨rfl, by simp⟩
    · rcases h₂ z hz with h | ⟨h₃, h₄⟩
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨h₃, by simp [h₄]⟩

/-- A walk of `G` projects to a walk of `G/e`. -/
theorem exists_walk_project {a b : α} (w : G.skeleton.Walk a b) (heu : G.Inc e u) (hev : G.Inc e v)
  (hG : G.IsGraph) :
    ∃ p : (contract G e u v hu huv).skeleton.Walk (contractMap u v a) (contractMap u v b),
      ∀ z ∈ p.support, ∃ y ∈ w.support, contractMap u v y = z := by
  classical
  induction w with
  | @nil x =>
    refine ⟨SimpleGraph.Walk.nil, fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact ⟨x, by simp, hz.symm⟩
  | @cons x y c hadj q ih =>
    obtain ⟨p, hp⟩ := ih
    by_cases heq : contractMap u v x = contractMap u v y
    · refine ⟨p.copy heq.symm rfl, fun z hz => ?_⟩
      rw [SimpleGraph.Walk.support_copy] at hz
      obtain ⟨t, ht, rfl⟩ := hp z hz
      exact ⟨t, by simp [ht], rfl⟩
    · have hadj₂ := hadj
      obtain ⟨-, f, h₁, h₂⟩ := hadj₂
      have hfe : f ≠ e := by
        intro he'
        rw [he'] at h₁ h₂
        have hc : ∀ t, G.Inc e t → contractMap u v t = u := fun t ht => by
          rcases end_eq_or hG heu hev huv ht with rfl | rfl
          · exact contractMap_of_ne huv
          · exact contractMap_self
        exact heq ((hc x h₁).trans (hc y h₂).symm)
      have hadj' : (contract G e u v hu huv).skeleton.Adj (contractMap u v x) (contractMap u v y) :=
        ⟨heq, f, contractMap_inc hfe h₁, contractMap_inc hfe h₂⟩
      refine ⟨SimpleGraph.Walk.cons hadj' p, fun z hz => ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨x, by simp, rfl⟩
      · obtain ⟨t, ht, rfl⟩ := hp z hz
        exact ⟨t, by simp [ht], rfl⟩

end GraphMinor.RST94
