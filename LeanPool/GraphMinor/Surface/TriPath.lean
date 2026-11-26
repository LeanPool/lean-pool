/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TriLocal

/-!
# Lines in a graph

A line in a graph with both ends at vertices is a path of edges (`IsGraph.exists_subdiv`). We use
this to see a simple drawing inside a triangulation that refines it.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

local notation "𝕀" => unitInterval

variable {X : Type} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
theorem IsLineWithEnds.isPreconnected_self {L : Set X} {u v : X} (hl : IsLineWithEnds L u v) :
  IsPreconnected L :=
  GraphMinor.Surface.IsLineWithEnds.isPreconnected hl

/-- A line in a graph, with its two ends the only vertices on it, is an edge. -/
theorem IsGraph.line_mem {V : Set X} {E : Set (Set X)} (hg : IsGraph V E) {L : Set X} {u v : X}
  (hl : IsLineWithEnds L u v)
    (huv : u ≠ v) (hs : L ⊆ gr V E) (hi : L ∩ V = {u, v}) : L ∈ E := by
  classical
  have hJ : IsPreconnected (L \ {u, v}) := hl.isPreconnected_diff
  have hne : (L \ {u, v}).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    have h2 := hl.subset_closure_diff
    rw [hc, closure_empty] at h2
    exact h2 hl.left_mem
  have hnV : ∀ y ∈ L \ {u, v}, y ∉ V := fun y hy hV => hy.2 (hi ▸ (⟨hy.1, hV⟩ : y ∈ L ∩ V))
  have hcl : ∀ e ∈ E, IsClosed e := fun e he => by
    obtain ⟨p, q, -, hl', -⟩ := hg.edge e he
    exact hl'.isCompact.isClosed
  obtain ⟨x, hx⟩ := hne
  have hxE : x ∈ ⋃₀ E := (hs hx.1).resolve_left (hnV x hx)
  obtain ⟨e, he, hxe⟩ := hxE
  have hR : IsClosed (⋃₀ (E \ {e})) := (hg.fine.subset sdiff_subset).isClosed_sUnion fun f hf
    => hcl f hf.1
  have hJs : L \ {u, v} ⊆ e := by
    by_contra hns
    obtain ⟨y, hy, hye⟩ := not_subset.mp hns
    have hyE : y ∈ ⋃₀ E := (hs hy.1).resolve_left (hnV y hy)
    obtain ⟨f, hf, hyf⟩ := hyE
    have hne' : f ≠ e := fun h' => hye (h' ▸ hyf)
    obtain ⟨z, hz, hz1, ⟨f', hf', hz2⟩⟩ := isPreconnected_closed_iff.mp hJ e _ (hcl e he) hR
      (fun w hw => by
      have hwE : w ∈ ⋃₀ E := (hs hw.1).resolve_left (hnV w hw)
      obtain ⟨g, hg', hwg⟩ := hwE
      by_cases hge : g = e
      · exact .inl (hge ▸ hwg)
      · exact .inr ⟨g, ⟨hg', hge⟩, hwg⟩) ⟨x, hx, hxe⟩ ⟨y, hy, f, ⟨hf, hne'⟩, hyf⟩
    exact hnV z hz (hg.disj e he f' hf'.1 (Ne.symm hf'.2) ⟨hz1, hz2⟩)
  have hLe : L ⊆ e := hl.subset_closure_diff.trans (closure_minimal hJs (hcl e he))
  obtain ⟨p, q, hpq, hle, hie⟩ := hg.edge e he
  have hu : u ∈ L ∩ V := hi ▸ Or.inl rfl
  have hv : v ∈ L ∩ V := hi ▸ Or.inr rfl
  have hu' : u ∈ ({p, q} : Set X) := hie ▸ (⟨hLe hu.1, hu.2⟩ : u ∈ e ∩ V)
  have hv' : v ∈ ({p, q} : Set X) := hie ▸ (⟨hLe hv.1, hv.2⟩ : v ∈ e ∩ V)
  have hp : p ∈ L := by
    rcases hu' with h1 | h1 <;> rcases hv' with h2 | h2
    · exact absurd (h1.trans h2.symm) huv
    · exact h1 ▸ hu.1
    · exact h2 ▸ hv.1
    · exact absurd (h1.trans h2.symm) huv
  have hq : q ∈ L := by
    rcases hu' with h1 | h1 <;> rcases hv' with h2 | h2
    · exact absurd (h1.trans h2.symm) huv
    · exact h2 ▸ hv.1
    · exact h1 ▸ hu.1
    · exact absurd (h1.trans h2.symm) huv
  obtain ⟨b, hb, hr, h0, h1⟩ := hle.exists_arc
  have hhe : Topology.IsEmbedding b := (hb.1.isClosedEmbedding hb.2).isEmbedding
  have hpre : IsPreconnected (b ⁻¹' L) := by
    refine hhe.isInducing.isPreconnected_image.mp ?_
    rw [image_preimage_eq_of_subset (by rw [hr]; exact hLe)]
    exact hl.isPreconnected_self
  have h0m : (0 : 𝕀) ∈ b ⁻¹' L := by
    change b 0 ∈ L
    rwa [h0]
  have h1m : (1 : 𝕀) ∈ b ⁻¹' L := by
    change b 1 ∈ L
    rwa [h1]
  have hall : e ⊆ L := by
    rw [← hr]
    rintro _ ⟨t, rfl⟩
    exact hpre.Icc_subset h0m h1m ⟨t.2.1, t.2.2⟩
  rwa [Subset.antisymm hLe hall]

/-- A line in a graph with both ends at vertices is a path of edges. -/
theorem IsGraph.exists_subdiv {V : Set X} {E : Set (Set X)} (hg : IsGraph V E) (n : ℕ) :
    ∀ {L : Set X} {u v : X}, (L ∩ V).ncard = n → IsLineWithEnds L u v → u ≠ v → u ∈ V → v ∈ V
      → L ⊆ gr V E →
      ∃ Y : Set (Set X), Y ⊆ E ∧ (∀ x ∈ Y, x ⊆ L) ∧ ⋃₀ Y = L ∧ ((L ∩ V) \ {u, v}).ncard + 1
        ≤ Y.ncard ∧
        (∀ w ∈ (L ∩ V) \ {u, v}, {x ∈ Y | w ∈ x}.ncard ≤ 2) ∧ {x ∈ Y | u ∈ x}.ncard = 1
          ∧ {x ∈ Y | v ∈ x}.ncard = 1 := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L u v hn hl huv hu hv hs
  have hfinV := hg.fin
  have hfinE := hg.fine
  have hYf : ∀ {Y : Set (Set X)}, Y ⊆ E → Y.Finite := fun h => hfinE.subset h
  by_cases hbase : (L ∩ V) \ {u, v} = ∅
  · have hi : L ∩ V = {u, v} := by
      refine Subset.antisymm (sdiff_eq_empty.mp hbase) ?_
      rintro y (rfl | rfl)
      · exact ⟨hl.left_mem, hu⟩
      · exact ⟨hl.right_mem, hv⟩
    have hLE := hg.line_mem hl huv hs hi
    refine ⟨{L}, singleton_subset_iff.mpr hLE, by simp, by simp, by simp [hbase],
      by simp [hbase], ?_, ?_⟩
    · have : {x ∈ ({L} : Set (Set X)) | u ∈ x} = {L} := by
        ext x
        constructor
        · exact fun h => h.1
        · rintro rfl
          exact ⟨rfl, hl.left_mem⟩
      rw [this, ncard_singleton]
    · have : {x ∈ ({L} : Set (Set X)) | v ∈ x} = {L} := by
        ext x
        constructor
        · exact fun h => h.1
        · rintro rfl
          exact ⟨rfl, hl.right_mem⟩
      rw [this, ncard_singleton]
  obtain ⟨w, hw⟩ := nonempty_iff_ne_empty.mpr hbase
  obtain ⟨a, ha, hr, h0, h1⟩ := hl.exists_arc
  have hmemL : ∀ t, a t ∈ L := fun t => hr ▸ mem_range_self t
  obtain ⟨tw, htw⟩ : ∃ t, a t = w := by
    have : w ∈ range a := hr ▸ hw.1.1
    exact this
  have hAf : ({t | a t ∈ V ∧ t ≠ 0} : Set 𝕀).Finite :=
    (hfinV.preimage ha.2.injOn).subset fun t ht => ht.1
  have hAne : ({t | a t ∈ V ∧ t ≠ 0} : Set 𝕀).Nonempty := ⟨tw, htw ▸ hw.1.2, fun h' => hw.2 (.inl
    (by rw [← htw, h', h0]))⟩
  obtain ⟨t₀, ht₀, hmin⟩ := exists_min_image _ id hAf hAne
  simp only [id] at hmin
  have htw1 : tw ≠ 1 := fun h' => hw.2 (.inr (by rw [← htw, h', h1]; rfl))
  have htw0 : tw ≠ 0 := fun h' => hw.2 (.inl (by rw [← htw, h', h0]))
  have hle : t₀ ≤ tw := hmin tw ⟨htw ▸ hw.1.2, htw0⟩
  have ht₀1 : t₀ < 1 := lt_of_le_of_ne (unitInterval.le_one t₀) fun h' => by
    rw [h'] at hle
    exact htw1 (le_antisymm (unitInterval.le_one tw) hle)
  have ht₀0 : (0 : 𝕀) < t₀ := lt_of_le_of_ne (unitInterval.nonneg t₀) (Ne.symm ht₀.2)
  set w₀ := a t₀ with hw₀
  let L₁ : Set X := a '' Icc 0 t₀
  let L₂ : Set X := a '' Icc t₀ 1
  have hl₁ : IsLineWithEnds L₁ u w₀ := by
    have h2 := (ha.sub (s := 0) (t := t₀) ht₀0.ne).isLineWithEnds
    rwa [range_subArc _ ht₀0.le, subArc_zero, subArc_one, h0] at h2
  have hl₂ : IsLineWithEnds L₂ w₀ v := by
    have h2 := (ha.sub (s := t₀) (t := 1) ht₀1.ne).isLineWithEnds
    rwa [range_subArc _ ht₀1.le, subArc_zero, subArc_one, h1] at h2
  have hLu : L₁ ∪ L₂ = L := by
    change a '' Icc 0 t₀ ∪ a '' Icc t₀ 1 = L
    rw [← image_union, Icc_union_Icc_eq_Icc ht₀0.le ht₀1.le, ← hr]
    ext x
    simp only [mem_range, mem_image, mem_Icc]
    exact ⟨fun ⟨t, _, ht⟩ => ⟨t, ht⟩, fun ⟨t, ht⟩ => ⟨t, ⟨unitInterval.nonneg t,
      unitInterval.le_one t⟩, ht⟩⟩
  have hs₁ : L₁ ⊆ L := hLu ▸ subset_union_left
  have hs₂ : L₂ ⊆ L := hLu ▸ subset_union_right
  have huL₂ : u ∉ L₂ := by
    rintro ⟨s, hs', he⟩
    have h2 : s = 0 := ha.2 (he.trans h0.symm)
    exact absurd (ht₀0.trans_le hs'.1) (by rw [h2]; exact lt_irrefl _)
  have hvL₁ : v ∉ L₁ := by
    rintro ⟨s, hs', he⟩
    have h2 : s = 1 := ha.2 (he.trans h1.symm)
    exact absurd (hs'.2.trans_lt ht₀1) (by rw [h2]; exact lt_irrefl _)
  have hw₀V : w₀ ∈ V := ht₀.1
  have hw₀u : w₀ ≠ u := fun h' => huL₂ (h' ▸ hl₂.left_mem)
  have hw₀v : w₀ ≠ v := fun h' => hvL₁ (h' ▸ hl₁.right_mem)
  have hi₁ : L₁ ∩ V = {u, w₀} := by
    ext y
    constructor
    · rintro ⟨⟨s, hs', rfl⟩, hV⟩
      by_cases hs0 : s = 0
      · exact .inl (by rw [hs0, h0])
      · have h2 := hmin s ⟨hV, hs0⟩
        exact .inr (by rw [le_antisymm hs'.2 h2]; rfl)
    · rintro (rfl | rfl)
      · exact ⟨hl₁.left_mem, hu⟩
      · exact ⟨hl₁.right_mem, hw₀V⟩
  have hL₁E : L₁ ∈ E := hg.line_mem hl₁ (Ne.symm hw₀u) (hs₁.trans hs) hi₁
  have hlt : (L₂ ∩ V).ncard < n := by
    rw [← hn]
    refine ncard_lt_ncard ⟨inter_subset_inter_left _ hs₂, fun h2 => ?_⟩
      (hfinV.subset inter_subset_right)
    exact huL₂ (h2 ⟨hl.left_mem, hu⟩).1
  obtain ⟨Y₂, h2E, h2s, h2U, h2c, h2d, h2u, h2v⟩ := ih _ hlt rfl hl₂ hw₀v hw₀V hv (hs₂.trans hs)
  have hL₁Y : L₁ ∉ Y₂ := fun h' => huL₂ (h2s L₁ h' hl₁.left_mem)
  have huY : ∀ x ∈ Y₂, u ∉ x := fun x hx h' => huL₂ (h2s x hx h')
  have hIntE : (L ∩ V) \ {u, v} = insert w₀ ((L₂ ∩ V) \ {w₀, v}) := by
    ext y
    constructor
    · rintro ⟨⟨h3, h4⟩, h5⟩
      by_cases hy : y = w₀
      · exact .inl hy
      · refine .inr ⟨⟨?_, h4⟩, ?_⟩
        · rcases (hLu ▸ h3 : y ∈ L₁ ∪ L₂) with h6 | h6
          · have h7 : y ∈ ({u, w₀} : Set X) := hi₁ ▸ ⟨h6, h4⟩
            rcases h7 with h7 | h7
            · exact absurd (.inl h7) h5
            · exact absurd h7 hy
          · exact h6
        · rintro (h6 | h6)
          · exact hy h6
          · exact h5 (.inr h6)
    · rintro (rfl | ⟨⟨h3, h4⟩, h5⟩)
      · exact ⟨⟨hs₁ hl₁.right_mem, hw₀V⟩, by
          rintro (h6 | h6)
          · exact hw₀u h6
          · exact hw₀v h6⟩
      · exact ⟨⟨hs₂ h3, h4⟩, by
          rintro (h6 | h6)
          · exact huL₂ (h6 ▸ h3)
          · exact h5 (.inr h6)⟩
  have hw₀n : w₀ ∉ (L₂ ∩ V) \ {w₀, v} := fun h' => h'.2 (.inl rfl)
  have hIntf : ((L₂ ∩ V) \ {w₀, v}).Finite := hfinV.subset fun y hy => hy.1.2
  refine ⟨insert L₁ Y₂, insert_subset hL₁E h2E, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x (rfl | hx)
    · exact hs₁
    · exact (h2s x hx).trans hs₂
  · rw [sUnion_insert, h2U, hLu]
  · rw [hIntE, ncard_insert_of_notMem hw₀n hIntf, ncard_insert_of_notMem hL₁Y (hYf h2E)]
    omega
  · intro w' hw'
    rw [hIntE] at hw'
    rcases hw' with rfl | hw'
    · have hsub : {x ∈ insert L₁ Y₂ | w₀ ∈ x} ⊆ insert L₁ {x ∈ Y₂ | w₀ ∈ x} := by
        rintro x ⟨rfl | hx, h3⟩
        · exact .inl rfl
        · exact .inr ⟨hx, h3⟩
      refine (ncard_le_ncard hsub ((hYf h2E).insert _ |>.subset (insert_subset_insert fun x hx
        => hx.1))).trans ?_
      exact (ncard_insert_le _ _).trans (by rw [h2u])
    · have hnL₁ : w' ∉ L₁ := fun h3 => by
        have h4 : w' ∈ ({u, w₀} : Set X) := hi₁ ▸ ⟨h3, hw'.1.2⟩
        rcases h4 with h4 | h4
        · exact huL₂ (h4 ▸ hw'.1.1)
        · exact hw'.2 (.inl h4)
      have h3 : {x ∈ insert L₁ Y₂ | w' ∈ x} = {x ∈ Y₂ | w' ∈ x} := by
        ext x
        constructor
        · rintro ⟨rfl | hx, h4⟩
          · exact absurd h4 hnL₁
          · exact ⟨hx, h4⟩
        · exact fun h4 => ⟨.inr h4.1, h4.2⟩
      rw [h3]
      exact h2d w' hw'
  · have h3 : {x ∈ insert L₁ Y₂ | u ∈ x} = {L₁} := by
      ext x
      constructor
      · rintro ⟨rfl | hx, h4⟩
        · rfl
        · exact absurd h4 (huY x hx)
      · rintro rfl
        exact ⟨.inl rfl, hl₁.left_mem⟩
    rw [h3, ncard_singleton]
  · have h3 : {x ∈ insert L₁ Y₂ | v ∈ x} = {x ∈ Y₂ | v ∈ x} := by
      ext x
      constructor
      · rintro ⟨rfl | hx, h4⟩
        · exact absurd h4 hvL₁
        · exact ⟨hx, h4⟩
      · exact fun h4 => ⟨.inr h4.1, h4.2⟩
    rw [h3, h2v]

end GraphMinor.Surface
