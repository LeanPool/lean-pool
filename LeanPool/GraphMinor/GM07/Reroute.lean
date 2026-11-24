/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.PushForest

/-!
# Changing the edges of a forest one line at a time

Here a forest `H` gets new edges. Each edge is replaced by a line with the same ends, and the new
line is homotopic to the old edge. We show that the result is a forest homotopic to `H`
(`exists_reroute`).

Forests are flat, so it is enough to compare one pair of curves between two boundary vertices
(`forestsHomotopic_of_walks`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- Two forests are homotopic if every walk of either one, between vertices that lie on `bd(Σ)`, is
joined to a walk of the other by homotopic curves. -/
theorem forestsHomotopic_of_walks [T2Space S] {P H : Drawing S} (hP : IsSurfaceForest P)
  (hH : IsSurfaceForest H) (hbd : P.V ∩ bd S = H.V ∩ bd S)
    (hfromP : ∀ {a b : S}, GraphWalk P.toGraph a b → PushJoined P H a b)
      (hfromH : ∀ {a b : S}, GraphWalk H.toGraph a b → PushJoined P H a b) : ForestsHomotopic P H
        := by
  classical
  refine ⟨hP.1, hH.1, hP.2, hH.2, hbd, fun s _ t _ _ => ⟨⟨fun ⟨W, _⟩ => ?_, fun ⟨W, _⟩ => ?_⟩,
    fun W₁ W₂ g c _ _ hg hc => ?_⟩⟩
  · obtain ⟨-, ⟨W'⟩, -⟩ := hfromP W
    obtain ⟨W'', h, -⟩ := GraphWalk.exists_isSimple W'
    exact ⟨W'', h⟩
  · obtain ⟨⟨W'⟩, -, -⟩ := hfromH W
    obtain ⟨W'', h, -⟩ := GraphWalk.exists_isSimple W'
    exact ⟨W'', h⟩
  · obtain ⟨-, -, κ, l, h1, h2, h3⟩ := hfromP W₁
    obtain ⟨g0, g1⟩ := hg.endpoints
    obtain ⟨c0, c1⟩ := hc.endpoints
    let pg : Path s t := ⟨g, g0, g1⟩
    let pc : Path s t := ⟨c, c0, c1⟩
    have hpg : pg.Homotopic κ := IsFlat.flat (isFlat_forest hP.2) pg κ (fun u
      => hg.range_subset_U ⟨u, rfl⟩) h1
    have hpc : l.Homotopic pc := IsFlat.flat (isFlat_forest hH.2) l pc h2 fun u
      => hc.range_subset_U ⟨u, rfl⟩
    exact curves_of_homotopic (hpg.trans (h3.trans hpc))

/-- A line is the closure of the line without its ends. -/
theorem IsLineWithEnds.closure_sdiff [T2Space S] {L : Set S} {u v : S}
  (h : IsLineWithEnds L u v) : closure (L \ {u, v}) = L := by
  obtain ⟨f, rfl, rfl⟩ := id h
  refine Subset.antisymm (closure_minimal sdiff_subset h.isCompact.isClosed) fun z hz => ?_
  have hd : closure (Ioo (0 : unitInterval) 1) = Icc 0 1 := closure_Ioo (by simp)
  let g : unitInterval → S := fun t => (f t).1
  have hg : Continuous g := by fun_prop
  have h1 : g (f.symm ⟨z, hz⟩) ∈ g '' closure (Ioo 0 1) := mem_image_of_mem g (by
    rw [hd]
    exact ⟨unitInterval.nonneg _, unitInterval.le_one _⟩)
  have h2 := image_closure_subset_closure_image hg h1
  have h3 : g (f.symm ⟨z, hz⟩) = z := by simp [g]
  rw [h3] at h2
  refine closure_mono ?_ h2
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨(f t).2, ?_⟩
  rintro (he | he)
  · exact ht.1.ne' (f.injective (Subtype.ext he))
  · exact ht.2.ne (f.injective (Subtype.ext (mem_singleton_iff.mp he)))

theorem mem_left_of_line {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : u ∈ L := by
  obtain ⟨f, rfl, -⟩ := h
  exact (f 0).2

theorem mem_right_of_line {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : v ∈ L := by
  obtain ⟨f, -, rfl⟩ := h
  exact (f 1).2

/-- **Replacing the edges of a forest.** Let `M e` be a line with the same ends as the edge `e`,
homotopic to `e`. If these lines meet only at vertices, and meet `V(H)` and `bd(Σ)` only at the ends
of `e`, then they form a forest homotopic to `H`. -/
theorem exists_reroute [T2Space S] {H : Drawing S} (hH : IsSurfaceForest H) (M : Set S → Set S)
  (hline : ∀ e a b, H.toGraph.IsLink e a b → IsLineWithEnds (M e) a b)
    (hV : ∀ e ∈ H.E, M e ∩ H.V ⊆ closure e) (hmeet : ∀ e ∈ H.E, ∀ f ∈ H.E, e ≠ f → M e ∩ M f ⊆ H.V)
      (hbd : ∀ e ∈ H.E, M e ∩ bd S ⊆ H.V)
    (hhom : ∀ e a b, H.toGraph.IsLink e a b → ∃ κ l : Path a b, (∀ u, κ u ∈ M e) ∧
      (∀ u, l u ∈ closure e) ∧ κ.Homotopic l) :
    ∃ P : Drawing S, P.V = H.V ∧ P.U = H.V ∪ ⋃ e ∈ H.E, M e ∧ IsSurfaceForest P
      ∧ ForestsHomotopic P H ∧ (∀ e' ∈ P.E, ∃ e ∈ H.E, closure e' = M e)
        ∧ ∀ e ∈ H.E, ∃ e' ∈ P.E, closure e' = M e := by
  classical
  have hF := hH.2
  have hends : ∀ e : H.E, ∃ u v, u ≠ v ∧ closure e.1 ∩ H.V = {u, v} := fun e => by
    obtain ⟨u, v, h1, h2, -⟩ := edge_line_of_forest hF e.2
    exact ⟨u, v, h1, h2⟩
  choose u v hne hcap using hends
  have huV : ∀ e, u e ∈ closure e.1 ∩ H.V := fun e => by rw [hcap]; exact .inl rfl
  have hvV : ∀ e, v e ∈ closure e.1 ∩ H.V := fun e => by rw [hcap]; exact .inr rfl
  have hlink : ∀ e : H.E, H.toGraph.IsLink e.1 (u e) (v e) := fun e => ⟨e.2, (huV e).2,
    (hvV e).2, hcap e⟩
  have hlines : ∀ e : H.E, IsLineWithEnds (M e.1) (u e) (v e) := fun e => hline _ _ _ (hlink e)
  have : Finite H.E := H.finite_edges.to_subtype
  obtain ⟨P, hPU, hPV, hPE⟩ := GM12.exists_drawing_of_finite_lines (ι := H.E) H.finite_V (E
    := univ) (toFinite univ) (fun e => M e.1) u v (fun e _ => hlines e) (fun e _ => hne e)
    (fun e _ => by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        have : z ∈ closure e.1 ∩ H.V := ⟨hV e.1 e.2 ⟨h1, h2⟩, h2⟩
        rwa [hcap] at this
      · rintro (rfl | h)
        · exact ⟨mem_left_of_line (hlines e), (huV e).2⟩
        · obtain rfl : z = v e := h
          exact ⟨mem_right_of_line (hlines e), (hvV e).2⟩)
    fun e _ f _ hef => hmeet e.1 e.2 f.1 f.2 fun h => hef (Subtype.ext h)
  have hPeq : ∀ e : H.E, closure (M e.1 \ {u e, v e}) = M e.1 := fun e
    => IsLineWithEnds.closure_sdiff (hlines e)
  have hPlink : ∀ e : H.E, P.toGraph.IsLink (M e.1 \ {u e, v e}) (u e) (v e) := fun e => by
    refine ⟨by rw [hPE]; exact ⟨e, mem_univ _, rfl⟩,
      by rw [hPV]; exact (huV e).2, by rw [hPV]; exact (hvV e).2, ?_⟩
    rw [hPeq, hPV]
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have : z ∈ closure e.1 ∩ H.V := ⟨hV e.1 e.2 ⟨h1, h2⟩, h2⟩
      rwa [hcap] at this
    · rintro (rfl | h)
      · exact ⟨mem_left_of_line (hlines e), (huV e).2⟩
      · obtain rfl : z = v e := h
        exact ⟨mem_right_of_line (hlines e), (hvV e).2⟩
  have hends' : ∀ {e : H.E} {x y : S}, closure e.1 ∩ H.V = {x, y} → (x = u e ∧ y = v e) ∨ (x = v e
    ∧ y = u e) := fun {e x y} h => by
    rw [hcap] at h
    rcases pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1.symm, h2.symm⟩
    · exact .inr ⟨h2.symm, h1.symm⟩
  have hPtoH : ∀ {e' : Set S} {x y : S}, P.toGraph.IsLink e' x y → ∃ e : H.E, e' = M e.1 \
    (closure e.1 ∩ H.V) ∧ H.toGraph.IsLink e.1 x y := by
    rintro e' x y ⟨he', hx, hy, hc⟩
    rw [hPE] at he'
    obtain ⟨e, -, rfl⟩ := he'
    refine ⟨e, by rw [hcap], ?_⟩
    have hc' := hc
    simp only [] at hc'
    rw [hPeq, hPV] at hc'
    have h1 : M e.1 ∩ H.V = closure e.1 ∩ H.V := by
      ext z
      constructor
      · exact fun h => ⟨hV e.1 e.2 h, h.2⟩
      · intro h
        have h2 : z ∈ ({u e, v e} : Set S) := by rw [← hcap]; exact h
        rcases h2 with rfl | h3
        · exact ⟨mem_left_of_line (hlines e), h.2⟩
        · obtain rfl : z = v e := h3
          exact ⟨mem_right_of_line (hlines e), h.2⟩
    refine ⟨e.2, ?_, ?_, ?_⟩
    · rw [hPV] at hx
      exact hx
    · rw [hPV] at hy
      exact hy
    · rw [← h1]
      exact hc'
  have hHtoP : ∀ {e : Set S} {x y : S}, H.toGraph.IsLink e x y → ∃ e' : Set S, P.toGraph.IsLink e'
    x y ∧ closure e' = M e := by
    rintro e x y hl
    let i : H.E := ⟨e, hl.1⟩
    refine ⟨M e \ {u i, v i}, ?_, hPeq i⟩
    rcases hends' (e := i) hl.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hPlink i
    · rw [h1, h2]
      exact (hPlink i).symm
  have hPf : IsGraphForest P.toGraph := by
    have hmap : ∀ {a b : S} (W : GraphWalk P.toGraph a b), ∃ W₀ : GraphWalk H.toGraph a b, W.edges
      = W₀.edges.map fun e => M e \ (closure e ∩ H.V) := by
      intro a b W
      induction W with
      | @nil w h => exact ⟨.nil (show w ∈ H.V from hPV ▸ h), rfl⟩
      | cons hl r ih =>
        obtain ⟨W₀, hW₀⟩ := ih
        obtain ⟨e, rfl, h2⟩ := hPtoH hl
        exact ⟨.cons h2 W₀, by simp [GraphWalk.edges, hW₀]⟩
    intro w W hW
    obtain ⟨W₀, hW₀⟩ := hmap W
    have hnd : W₀.edges.Nodup := by
      have h1 := hW.2
      rw [hW₀] at h1
      exact List.Nodup.of_map _ h1
    have h0 := length_eq_zero_of_trail hF _ _ W₀ rfl hnd
    have hlen : W₀.length = W.length := by
      change W₀.edges.length = W.edges.length
      rw [hW₀, List.length_map]
    omega
  have hPp : P.IsProper := by
    rintro z ⟨hzb, hzU⟩
    rw [hPV]
    rw [hPU] at hzU
    rcases hzU with h | h
    · exact h
    · obtain ⟨e, -, h⟩ := mem_iUnion₂.mp h
      exact hbd e.1 e.2 ⟨h, hzb⟩
  have hbdV : P.V ∩ bd S = H.V ∩ bd S := by rw [hPV]
  have hPm : ∀ {x : S}, x ∈ H.V → x ∈ P.V := fun h => hPV ▸ h
  have hstep : ∀ {e : Set S} {x y : S}, H.toGraph.IsLink e x y → PushJoined P H x y
    := fun {e x y} hl => by
    obtain ⟨e', hl', hc⟩ := hHtoP hl
    obtain ⟨κ, l, h1, h2, h3⟩ := hhom e x y hl
    refine ⟨⟨.cons hl' (.nil (hPm hl.2.2.1))⟩, ⟨.cons hl (.nil hl.2.2.1)⟩, κ, l, fun t => ?_,
      fun t => H.closure_subset_U hl.1 (h2 t), h3⟩
    rw [hPU]
    exact .inr (mem_iUnion₂.mpr ⟨⟨e, hl.1⟩, mem_univ _, h1 t⟩)
  refine ⟨P, hPV, ?_, ⟨hPp, hPf⟩, forestsHomotopic_of_walks ⟨hPp, hPf⟩ hH hbdV ?_ ?_, ?_, ?_⟩
  · rw [hPU]
    congr 1
    ext z
    simp only [mem_iUnion, mem_univ, exists_prop, true_and, Subtype.exists]
  · intro a b W
    induction W with
    | @nil w h => exact PushJoined.refl h (hPV ▸ h)
    | cons hl r ih =>
      obtain ⟨e, -, h2⟩ := hPtoH hl
      exact (hstep h2).trans ih
  · intro a b W
    induction W with
    | @nil w h => exact PushJoined.refl (hPm h) h
    | cons hl r ih => exact (hstep hl).trans ih
  · intro e' he'
    rw [hPE] at he'
    obtain ⟨e, -, rfl⟩ := he'
    exact ⟨e.1, e.2, hPeq e⟩
  · intro e he
    let i : H.E := ⟨e, he⟩
    exact ⟨_, (hPlink i).1, hPeq i⟩

end GraphMinor.GM07
