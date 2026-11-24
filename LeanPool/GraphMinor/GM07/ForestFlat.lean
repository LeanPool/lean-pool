/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.PullForest
public import LeanPool.GraphMinor.GM07.FlatEdges
public import LeanPool.GraphMinor.GM11.Theorem64
public import LeanPool.GraphMinor.GM11.Section7b

/-!
# Forests are flat

A closed curve in a forest drawn in a surface is null-homotopic (`isFlat_forest`). So two curves in
the forest with the same ends are homotopic. This is used in (4.5) of Graph Minors VII (page 223),
where curves of two forests are compared without following them edge by edge.

The proof peels off a leaf (`exists_forest_leaf`). If `L` is a line that meets a closed set `T` only
in one end `x`, then `T ∪ L` shrinks onto `T` by pulling `L` along itself to `x`, so a closed curve
in `T ∪ L` is homotopic to one in `T` (`IsFlat.union_line_end`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- A simple walk has distinct edges. -/
theorem nodup_edges_of_simple {G : Drawing S} {a b : S} (W : GraphWalk G.toGraph a b)
  (hW : W.IsSimple) : W.edges.Nodup := by
  induction W with
  | nil _ => simp [GraphWalk.edges]
  | @cons a y b e hl r ih =>
    have hnd := List.nodup_cons.mp hW
    refine List.nodup_cons.mpr ⟨fun h => hnd.1 ?_, ih hnd.2⟩
    have hp : a ∈ closure e ∩ G.V := by
      rw [hl.2.2.2]
      exact Or.inl rfl
    exact mem_support_of_mem_closure r h hp.1 hp.2

/-- A subdrawing of a forest is a forest. -/
theorem IsGraphForest.of_subdrawing {G G' : Drawing S} (hG : IsGraphForest G.toGraph)
  (h : G'.IsSubdrawing G) : IsGraphForest G'.toGraph := by
  have hup : ∀ {a b : S} (W : GraphWalk G'.toGraph a b), ∃ W₀ : GraphWalk G.toGraph a b, W₀.edges
    = W.edges := by
    intro a b W
    induction W with
    | nil hv => exact ⟨.nil (h.1 hv), rfl⟩
    | cons hl r ih =>
      obtain ⟨W₀, hW₀⟩ := ih
      exact ⟨.cons ((h.isLink_iff hl.1).mp hl) W₀, by simp [GraphWalk.edges, hW₀]⟩
  intro u W hW
  obtain ⟨W₀, hW₀⟩ := hup W
  have h0 := length_eq_zero_of_trail hG _ _ W₀ rfl (hW₀ ▸ hW.2)
  have hl : W₀.length = W.length := congrArg List.length hW₀
  omega

/-- An edge of a forest has a line as its closure, since a loop is a circuit. -/
theorem edge_line_of_forest {G : Drawing S} (hF : IsGraphForest G.toGraph) {e : Set S}
  (he : e ∈ G.E) : ∃ u v, u ≠ v ∧ closure e ∩ G.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
  rcases G.edge_cond e he with h1 | ⟨u, hcap, -⟩
  · exact h1
  · exfalso
    have huV : u ∈ G.V := (show u ∈ closure e ∩ G.V by rw [hcap]; rfl).2
    have hl : G.toGraph.IsLink e u u := ⟨he, huV, huV, by rw [hcap, pair_eq_singleton]⟩
    have h0 := hF u (.cons hl (.nil huV)) (by simp [GraphWalk.IsSimpleClosed, GraphWalk.support,
      GraphWalk.edges])
    simp [GraphWalk.length, GraphWalk.edges] at h0

/-- A forest with an edge has a leaf: a vertex in the closure of just one edge. -/
theorem exists_forest_leaf {G : Drawing S} (hF : IsGraphForest G.toGraph)
  (hE : G.E.Nonempty) :
    ∃ e ∈ G.E, ∃ y x, x ≠ y ∧ closure e ∩ G.V = {y, x} ∧ (∀ f ∈ G.E, f ≠ e → y ∉ closure f)
      ∧ IsLineWithEnds (closure e) y x := by
  classical
  let P : ℕ → Prop := fun n => ∃ (a b : S) (W : GraphWalk G.toGraph a b), W.IsSimple ∧ W.length = n
  have hbound : ∀ n, P n → n ≤ G.V.ncard := by
    rintro n ⟨a, b, W, hs, rfl⟩
    have h1 : W.support.toFinset ⊆ G.finite_V.toFinset := fun x hx =>
      G.finite_V.mem_toFinset.mpr (W.mem_vertexSet_of_mem_support (List.mem_toFinset.mp hx))
    have h2 := Finset.card_le_card h1
    rw [List.toFinset_card_of_nodup hs, GraphWalk.length_support',
      ← ncard_eq_toFinset_card _ G.finite_V] at h2
    omega
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨u₀, v₀, huv₀, hcap₀, -⟩ := edge_line_of_forest hF he₀
  have huV : u₀ ∈ G.V := (show u₀ ∈ closure e₀ ∩ G.V by rw [hcap₀]; exact .inl rfl).2
  have hvV : v₀ ∈ G.V := (show v₀ ∈ closure e₀ ∩ G.V by rw [hcap₀]; exact .inr rfl).2
  have hP1 : P 1 := ⟨u₀, v₀, .cons ⟨he₀, huV, hvV, hcap₀⟩ (.nil hvV), by
    simpa [GraphWalk.IsSimple, GraphWalk.support] using huv₀, rfl⟩
  have h1 : 1 ≤ G.V.ncard := hbound 1 hP1
  obtain ⟨y, b, W, hW, hl⟩ : P (Nat.findGreatest P G.V.ncard) := Nat.findGreatest_spec h1 hP1
  have hlen : 1 ≤ W.length := hl ▸ Nat.le_findGreatest h1 hP1
  have hmax : ∀ (a' b' : S) (W' : GraphWalk G.toGraph a' b'), W'.IsSimple → W'.length ≤ W.length
    := fun a' b' W' hs' => by
    rw [hl]
    exact Nat.le_findGreatest (hbound _ ⟨a', b', W', hs', rfl⟩) ⟨a', b', W', hs', rfl⟩
  clear_value P
  cases W with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hlen
  | @cons _ x _ e hl' r =>
    have hnd := List.nodup_cons.mp hW
    have hxy : x ≠ y := fun h => hnd.1 (h ▸ r.start_mem_support)
    refine ⟨e, hl'.1, y, x, hxy, hl'.2.2.2, fun f hf hne hyf => ?_, ?_⟩
    · set W₀ : GraphWalk G.toGraph y b := .cons hl' r with hW₀
      obtain ⟨u, v, huv, hcap, hline⟩ := edge_line_of_forest hF hf
      have hyV : y ∈ G.V := hl'.2.1
      have hy' : y ∈ closure f ∩ G.V := ⟨hyf, hyV⟩
      obtain ⟨z, hzy, hcap'⟩ : ∃ z, z ≠ y ∧ closure f ∩ G.V = {y, z} := by
        rw [hcap] at hy'
        rcases hy' with rfl | h
        · exact ⟨v, huv.symm, hcap⟩
        · obtain rfl : y = v := h
          exact ⟨u, huv, by rw [hcap, pair_comm]⟩
      have hzV : z ∈ G.V := (show z ∈ closure f ∩ G.V by rw [hcap']; exact .inr rfl).2
      have hlink : G.toGraph.IsLink f z y := ⟨hf, hzV, hyV, by rw [hcap', pair_comm]⟩
      by_cases hz : z ∈ W₀.support
      · obtain ⟨W', hs, he, -⟩ := GraphWalk.exists_prefix W₀ hW hz
        have hfW : f ∉ W₀.edges := fun h => by
          rcases List.mem_cons.mp h with h1 | h1
          · exact hne h1
          · exact hnd.1 (mem_support_of_mem_closure r h1 hyf hyV)
        have h0 := length_eq_zero_of_trail hF _ _ (GraphWalk.cons hlink W') rfl
          (List.nodup_cons.mpr ⟨fun h => hfW (he f h), nodup_edges_of_simple W' hs⟩)
        simp [GraphWalk.length, GraphWalk.edges] at h0
      · have h1 := hmax z b (.cons hlink W₀) (List.nodup_cons.mpr ⟨hz, hW⟩)
        have h2 : (GraphWalk.cons hlink W₀).length = W₀.length + 1 := rfl
        omega
    · obtain ⟨u, v, huv, hcap, hline⟩ := edge_line_of_forest hF hl'.1
      have hc := hl'.2.2.2
      have hy' : y ∈ ({u, v} : Set S) := hcap ▸ (show y ∈ closure e ∩ G.V by
        rw [hc]
        exact .inl rfl)
      have hx' : x ∈ ({u, v} : Set S) := hcap ▸ (show x ∈ closure e ∩ G.V by
        rw [hc]
        exact .inr rfl)
      rcases hy' with rfl | h
      · rcases hx' with rfl | h'
        · exact absurd rfl hxy
        · obtain rfl : x = v := h'
          exact hline
      · obtain rfl : y = v := h
        rcases hx' with rfl | h'
        · exact hline.symm
        · exact absurd h' hxy

/-- **Adding a line by one end.** Let `T` be closed and flat, and let `L` be a line with `L ∩ T =
{x}`, where `x` is an end of `L`. Then `T ∪ L` is flat. A closed curve in `T ∪ L` is pulled along
`L` to `x`, which gives a homotopic curve in `T`. -/
theorem IsFlat.union_line_end {T L : Set S} {x y : S} (hT : IsClosed T) (hf : IsFlat T)
  (hL : IsLineWithEnds L x y) (hLT : L ∩ T = {x}) (hLc : IsClosed L) : IsFlat (T ∪ L) := by
  classical
  obtain ⟨f, h0, -⟩ := hL
  let u : S → unitInterval := fun z => if h : z ∈ L then f.symm ⟨z, h⟩ else 0
  have hu : ContinuousOn u L := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : L.domRestrict u = f.symm := by
      ext z
      simp [u, Set.domRestrict]
    rw [this]
    exact f.symm.continuous
  have hux : u x = 0 := by
    have hxL : x ∈ L := by
      have : x ∈ L ∩ T := by rw [hLT]; rfl
      exact this.1
    have : f.symm ⟨x, hxL⟩ = 0 := by
      rw [Homeomorph.symm_apply_eq]
      exact Subtype.ext h0.symm
    simp [u, hxL, this]
  let sc : unitInterval × unitInterval → unitInterval := fun p => projIcc 0 1 zero_le_one
    ((1 - p.1.1) * p.2.1)
  have hsc : Continuous sc := continuous_projIcc.comp (by fun_prop)
  intro φ hφ
  let Ψ : Circle × unitInterval → S := fun p => if φ p.1 ∈ L then (f (sc (p.2, u
    (φ p.1)))).1 else φ p.1
  have hA : IsClosed ((φ ⁻¹' L) ×ˢ (univ : Set unitInterval)) := (hLc.preimage φ.continuous).prod
    isClosed_univ
  have hB : IsClosed ((φ ⁻¹' T) ×ˢ (univ : Set unitInterval)) := (hT.preimage φ.continuous).prod
    isClosed_univ
  have hcA : ContinuousOn Ψ ((φ ⁻¹' L) ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : Circle × unitInterval => u (φ p.1)) ((φ ⁻¹' L) ×ˢ univ) :=
      hu.comp (φ.continuous.comp continuous_fst).continuousOn fun p hp => hp.1
    have h2 : ContinuousOn (fun p : Circle × unitInterval => (f (sc (p.2, u (φ p.1)))).1)
      ((φ ⁻¹' L) ×ˢ univ) :=
      (continuous_subtype_val.comp f.continuous).comp_continuousOn (hsc.comp_continuousOn
        (continuous_snd.continuousOn.prodMk h1))
    refine h2.congr fun p hp => ?_
    exact ite_eq_left hp.1
  have hcB : ContinuousOn Ψ ((φ ⁻¹' T) ×ˢ univ) := by
    refine (φ.continuous.comp continuous_fst).continuousOn.congr fun p hp => ?_
    by_cases hpL : φ p.1 ∈ L
    · have hpx : φ p.1 = x := by
        have : φ p.1 ∈ L ∩ T := ⟨hpL, hp.1⟩
        rw [hLT] at this
        exact this
      have hs : sc (p.2, 0) = 0 := by
        ext
        simp [sc]
      change (if φ p.1 ∈ L then _ else _) = φ p.1
      rw [ite_eq_left hpL, hpx, hux, hs, h0]
    · exact ite_eq_right hpL
  have hcov : ((φ ⁻¹' L) ×ˢ (univ : Set unitInterval)) ∪ ((φ ⁻¹' T) ×ˢ univ) = univ := by
    ext p
    simp only [mem_union, mem_prod, mem_preimage, mem_univ, and_true, iff_true]
    rcases hφ ⟨p.1, rfl⟩ with h | h
    · exact .inr h
    · exact .inl h
  have hΨ : Continuous Ψ := by
    rw [← continuousOn_univ, ← hcov]
    exact hcA.union_of_isClosed hcB hA hB
  let ψ : C(Circle × unitInterval, S) := ⟨Ψ, hΨ⟩
  let φ' : C(Circle, S) := ⟨fun c => Ψ (c, 1), by fun_prop⟩
  have hend : range φ' ⊆ T := by
    rintro _ ⟨c, rfl⟩
    change (if φ c ∈ L then _ else _) ∈ T
    by_cases hc : φ c ∈ L
    · have hs : sc (1, u (φ c)) = 0 := by
        ext
        simp [sc]
      rw [ite_eq_left hc, hs, h0]
      have : x ∈ L ∩ T := by rw [hLT]; rfl
      exact this.2
    · rw [ite_eq_right hc]
      exact (hφ ⟨c, rfl⟩).resolve_right hc
  refine null_of_homotopic (subset_univ _) ?_ (hf φ' hend)
  refine ⟨ψ, fun _ => mem_univ _, fun c => ?_, fun c => rfl⟩
  change (if φ c ∈ L then _ else _) = φ c
  by_cases hc : φ c ∈ L
  · have hs : ∀ t, sc (0, t) = t := fun t => by
      ext
      simp [sc]
    rw [ite_eq_left hc, hs]
    have : u (φ c) = f.symm ⟨φ c, hc⟩ := by simp [u, hc]
    rw [this, Homeomorph.apply_symm_apply]
  · exact ite_eq_right hc

/-- **A forest in a Hausdorff space is flat.** -/
theorem isFlat_forest [T2Space S] {G : Drawing S} (hG : IsGraphForest G.toGraph) : IsFlat G.U := by
  classical
  induction hn : G.E.ncard generalizing G with
  | zero =>
    have hfin : G.E.Finite := G.finite_edges
    have hE : G.E = ∅ := (ncard_eq_zero hfin).mp hn
    have hU : G.U = G.V := by
      rw [G.U_eq, hE]
      simp
    rw [hU]
    exact Flat.isFlat (flat_of_finite G.finite_V)
  | succ n ih =>
    have hne : G.E.Nonempty := by
      have hfin : G.E.Finite := G.finite_edges
      rw [← ncard_pos hfin]
      omega
    obtain ⟨e, he, y, x, hxy, hcap, hleaf, hline⟩ := exists_forest_leaf hG hne
    have hsub := deleteEdge_isSubdrawing G e
    have hcard : (G.deleteEdge e).E.ncard = n := by
      rw [deleteEdge_E, ncard_sdiff_singleton_of_mem he]
      omega
    have hfl := ih (IsGraphForest.of_subdrawing hG hsub) hcard
    have hV : (G.deleteEdge e).V = G.V := GM06.deleteEdge_V G e
    let T : Set S := (G.V \ {y}) ∪ ⋃ f ∈ G.E \ {e}, closure f
    have hTc : IsClosed T := ((G.finite_V.subset sdiff_subset).isClosed).union
      (((G.finite_edges.subset sdiff_subset).isClosed_biUnion) fun f _ => isClosed_closure)
    have hTU : T ⊆ (G.deleteEdge e).U := by
      rw [(G.deleteEdge e).U_eq, hV, deleteEdge_E]
      exact union_subset_union_left _ sdiff_subset
    have hyT : y ∉ T := by
      rintro (h | h)
      · exact h.2 rfl
      · obtain ⟨f, hf, hyf⟩ := mem_iUnion₂.mp h
        exact hleaf f hf.1 hf.2 hyf
    have hline' := hline.symm
    have hLT : closure e ∩ T = {x} := by
      ext z
      constructor
      · rintro ⟨hz, hzT⟩
        by_cases hzV : z ∈ G.V
        · have : z ∈ closure e ∩ G.V := ⟨hz, hzV⟩
          rw [hcap] at this
          rcases this with rfl | h
          · exact (hyT hzT).elim
          · exact h
        · exfalso
          rcases hzT with h | h
          · exact hzV h.1
          · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp h
            have h1 : z ∈ f := by rw [← G.closure_diff_V hf.1]; exact ⟨hzf, hzV⟩
            have h2 : z ∈ e := by rw [← G.closure_diff_V he]; exact ⟨hz, hzV⟩
            exact hf.2 (arcComponent_eq hf.1 he h1 h2)
      · rintro rfl
        have hxc : z ∈ closure e ∩ G.V := by rw [hcap]; exact .inr rfl
        exact ⟨hxc.1, .inl ⟨hxc.2, hxy⟩⟩
    have hU : G.U = T ∪ closure e := by
      rw [G.U_eq]
      refine Subset.antisymm (union_subset (fun z hz => ?_) (iUnion₂_subset fun f hf => ?_)) ?_
      · by_cases hzy : z = y
        · exact .inr (hzy ▸ (show y ∈ closure e ∩ G.V by rw [hcap]; exact .inl rfl).1)
        · exact .inl (.inl ⟨hz, hzy⟩)
      · by_cases hfe : f = e
        · exact hfe ▸ subset_union_right
        · exact fun z hz => .inl (.inr (mem_biUnion (show f ∈ G.E \ {e} from ⟨hf, hfe⟩) hz))
      · refine union_subset (union_subset (sdiff_subset.trans subset_union_left) ?_) ?_
        · exact iUnion₂_subset fun f hf z hz => .inr (mem_biUnion hf.1 hz)
        · exact fun z hz => .inr (mem_biUnion he hz)
    rw [hU]
    exact IsFlat.union_line_end hTc (IsFlat.mono hfl hTU) hline' hLT isClosed_closure

end GraphMinor.GM07
