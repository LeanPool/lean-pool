/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.DualExists
public import LeanPool.GraphMinor.GM06.RegionCurve
public import LeanPool.GraphMinor.GM07.Section11
public import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.GM14.Section6c
public import LeanPool.GraphMinor.Surface.CutLift

/-!
# From a chain to a normal arc in a disc

(4.1) of Graph Minors VII (page 221) is (3.6) of Graph Minors VI, "stated in different language".
The chains of VI are lists of vertices and
regions. The arcs of VII are lines. Here we go from a chain with distinct ends `x, y` to a proper
`I`-arc from `x` to `y` that meets `G` only in
vertices of the chain (`exists_arc_of_chain`). The line runs inside the regions of the chain, off
`bd(Σ)`, and through the vertices of the chain.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM06

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A closed disc that is all of `S` makes `S` a closed disc space. -/
theorem isClosedDiscSpace_of_univ (hD : IsClosedDisc (univ : Set S)) : IsClosedDiscSpace S := by
  obtain ⟨φ⟩ := hD
  exact ⟨φ.trans (Homeomorph.Set.univ S)⟩

theorem discBd_univ_eq : discBd (univ : Set S) = bd S := by
  simpa [discBd, Homeomorph.Set.univ] using image_bd_homeomorph (Homeomorph.Set.univ S)

/-- A region without `bd(Σ)` is path connected. -/
theorem isPathConnected_region_sdiff_bd (hDS : IsClosedDiscSpace S) (G : Drawing S) {r : Set S}
  (hr : r ∈ G.R) :
    IsPathConnected (r \ bd S) := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hDS
  have ho : IsOpen r := isOpen_region hDS G hr
  have hc : IsPreconnected r := (isPathConnected_region hDS G hr).isConnected.isPreconnected
  have hne : r.Nonempty := (isPathConnected_region hDS G hr).nonempty
  have ho' : IsOpen (r \ bd S) := ho.sdiff (isClosed_bd_of_isClosedDiscSpace hDS)
  exact ho'.isConnected_iff_isPathConnected.mp ⟨open_sdiff_bd_nonempty hDS ho hne,
    isPreconnected_sdiff_bd_of_isOpen hDS ho hc⟩

/-- From a point in the closure of a region there is a curve into the region that leaves `bd(Σ)` at
once. -/
theorem exists_entry (hD : IsClosedDisc (univ : Set S)) {G : Drawing S}
  (hG : G.IsProper) {r : Set S} (hr : r ∈ G.R) {p : S} (hp : p ∈ closure r) :
    ∃ α : C(unitInterval, S), α 0 = p ∧ ∀ t : unitInterval, 0 < (t : ℝ) → α t ∈ r \ bd S := by
  have hDS := isClosedDiscSpace_of_univ hD
  by_cases hpU : p ∈ G.U
  · exact exists_region_entry_path_of_mem_U G hDS hG r hr p hp hpU
  obtain ⟨β, hβ0, hβ⟩ := exists_region_entry_path G hDS hG r hr p hp
  have hdis : Disjoint (range β) G.U := disjoint_left.mpr fun z ⟨t, ht⟩ hz => by
    rcases eq_or_lt_of_le (t.2.1 : (0 : ℝ) ≤ t) with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, hβ0] at ht
      exact hpU (ht ▸ hz)
    · rcases hr with ⟨z₀, -, rfl⟩
      exact (connectedComponentIn_subset _ _ (hβ t h0)).2 (ht ▸ hz)
  have hsub : range β ⊆ r := region_subset_of_isPreconnected G hr (isPreconnected_range
    β.continuous) hdis ⟨β 1, ⟨1, rfl⟩, hβ 1 (by simp)⟩
  have hpr : p ∈ r := hsub ⟨0, hβ0⟩
  by_cases hpb : p ∈ bd S
  · exact exists_curve_of_half_nbhd hD (isOpen_region hDS G hr) (by rwa [discBd_univ_eq]) hpr
      (fun z hz => ⟨hz.1.1, by rw [discBd_univ_eq] at hz; exact hz.2⟩)
  · exact ⟨ContinuousMap.const _ p, rfl, fun _ _ => ⟨hpr, hpb⟩⟩

/-- The set in the surface that a term of a chain stands for: a vertex, or a region without `bd(Σ)`.
-/
def termSet : ChainTerm S → Set S
  | .inl v => {v}
  | .inr r => r \ bd S

theorem isPathConnected_insert_region (hD : IsClosedDisc (univ : Set S)) {G : Drawing S}
  (hG : G.IsProper) {r : Set S} (hr : r ∈ G.R) {v : S} (hv : v ∈ closure r) :
    IsPathConnected ({v} ∪ (r \ bd S)) := by
  have hDS := isClosedDiscSpace_of_univ hD
  obtain ⟨α, h0, h1⟩ := exists_entry hD hG hr hv
  have heq : {v} ∪ (r \ bd S) = range α ∪ (r \ bd S) := by
    apply subset_antisymm
    · rintro z (rfl | hz)
      · exact .inl ⟨0, h0⟩
      · exact .inr hz
    · rintro z (⟨t, rfl⟩ | hz)
      · rcases eq_or_lt_of_le (t.2.1 : (0 : ℝ) ≤ t) with h2 | h2
        · have : t = 0 := Subtype.ext h2.symm
          rw [this, h0]
          exact .inl rfl
        · exact .inr (h1 t h2)
      · exact .inr hz
  rw [heq]
  have hpc : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  have hrange : IsPathConnected (range α) := isPathConnected_range α.continuous
  exact hrange.union (isPathConnected_region_sdiff_bd hDS G hr) ⟨α 1, ⟨1, rfl⟩, h1 1 (by simp)⟩

theorem isPathConnected_termSet_union (hD : IsClosedDisc (univ : Set S)) {G : Drawing S}
  (hG : G.IsProper) {t t' : ChainTerm S} (h : ChainTerm.AreIncident G t t') :
    IsPathConnected (termSet t ∪ termSet t') := by
  rcases t with v | r <;> rcases t' with v' | r'
  · exact h.elim
  · exact isPathConnected_insert_region hD hG h.2.1 h.2.2
  · rw [union_comm]
    exact isPathConnected_insert_region hD hG h.2.1 h.2.2
  · exact h.elim

/-- The sets of the terms of a chain have a path connected union. -/
theorem isPathConnected_chain (hD : IsClosedDisc (univ : Set S)) {G : Drawing S} (hG : G.IsProper) :
    ∀ {A : List (ChainTerm S)}, A ≠ [] → (∀ t ∈ A, t.IsValid G) → A.IsChain
      (ChainTerm.AreIncident G) → IsPathConnected (⋃ t ∈ A, termSet t)
  | [], h, _, _ => (h rfl).elim
  | [t], _, hv, _ => by
    have hDS := isClosedDiscSpace_of_univ hD
    simp only [List.mem_singleton, iUnion_iUnion_eq_left]
    rcases t with v | r
    · exact isPathConnected_singleton v
    · exact isPathConnected_region_sdiff_bd hDS G (hv (.inr r) (by simp))
  | t :: t' :: l, _, hv, hc => by
    rw [List.isChain_cons_cons] at hc
    have ih := isPathConnected_chain hD hG (A := t' :: l) (by simp) (fun u hu => hv u
      (List.mem_cons_of_mem _ hu)) hc.2
    have hsplit : (⋃ u ∈ t :: t' :: l, termSet u) = (termSet t ∪ termSet t') ∪ ⋃ u ∈ t' :: l,
      termSet u := by
      ext z
      simp only [mem_iUnion, List.mem_cons, exists_prop, mem_union]
      constructor
      · rintro ⟨u, rfl | hu, hz⟩
        · exact .inl (.inl hz)
        · exact .inr ⟨u, hu, hz⟩
      · rintro ((h | h) | ⟨u, hu, h⟩)
        · exact ⟨t, .inl rfl, h⟩
        · exact ⟨t', .inr (.inl rfl), h⟩
        · exact ⟨u, .inr hu, h⟩
    rw [hsplit]
    have hne : (termSet t').Nonempty := by
      have hDS := isClosedDiscSpace_of_univ hD
      rcases t' with v | r
      · exact ⟨v, rfl⟩
      · exact (isPathConnected_region_sdiff_bd hDS G (hv (.inr r) (by simp))).nonempty
    obtain ⟨z, hz⟩ := hne
    refine (isPathConnected_termSet_union hD hG hc.1).union ih ⟨z, .inr hz, ?_⟩
    simp only [mem_iUnion, exists_prop]
    exact ⟨t', by simp, hz⟩

/-- An end of a chain is joined to the sets of the terms. -/
theorem exists_end_joined (hD : IsClosedDisc (univ : Set S)) {G : Drawing S}
  (hG : G.IsProper) {A : List (ChainTerm S)} {t : ChainTerm S} (ht : t ∈ A)
    (hv : t.IsValid G) {x : S} (hx : t.MatchesEnd x) : ∃ a ∈ ⋃ u ∈ A, termSet u, JoinedIn
      ({x} ∪ ⋃ u ∈ A, termSet u) x a := by
  have hmem : ∀ z ∈ termSet t, z ∈ ⋃ u ∈ A, termSet u := fun z hz => by
    simp only [mem_iUnion, exists_prop]
    exact ⟨t, ht, hz⟩
  rcases t with v | r
  · obtain rfl : v = x := hx
    exact ⟨v, hmem v rfl, JoinedIn.refl (.inl rfl)⟩
  · obtain ⟨α, h0, h1⟩ := exists_entry hD hG hv (subset_closure hx)
    refine ⟨α 1, hmem _ (h1 1 (by simp)), ⟨⟨α, h0, rfl⟩, fun t => ?_⟩⟩
    rcases eq_or_lt_of_le (t.2.1 : (0 : ℝ) ≤ t) with h2 | h2
    · have : t = 0 := Subtype.ext h2.symm
      change α t ∈ _
      rw [this, h0]
      exact .inl rfl
    · exact .inr (hmem _ (h1 t h2))

/-- A term of a chain that is a vertex in `bd(Σ)` is an end of the chain. -/
theorem inl_mem_bd_eq {G : Drawing S} {x y : S} {A : List (ChainTerm S)}
  (hA : IsXYChain G x y A) {v : S} (hv : Sum.inl v ∈ A) (hb : v ∈ bd S) : v = x ∨ v = y := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem hv
  have hvG : v ∈ G.V := hA.valid _ hv
  have hp : (A[i]).IsPeripheral G := by
    rw [h]
    exact ⟨hvG, hb⟩
  rcases (hA.peripheral_iff ⟨i, hi⟩).mp hp with h0 | h1
  · left
    have h2 : A.head hA.ne_nil = Sum.inl v := by
      rw [List.head_eq_getElem]
      simp only  at h0
      simp only [← h0]
      exact h
    have h3 := hA.head_matches
    rw [h2] at h3
    exact h3
  · right
    have h2 : A.getLast hA.ne_nil = Sum.inl v := by
      rw [List.getLast_eq_getElem]
      simp only  at h1
      have h3 : A.length - 1 = i := by omega
      simp only [h3]
      exact h
    have h3 := hA.last_matches
    rw [h2] at h3
    exact h3

/-- **From a chain to an arc.** A chain between distinct points `x, y` of `bd(Σ)` gives a proper
`I`-arc from `x` to `y` that is `G`-normal, and
whose vertices of `G` other than `x, y` are terms of the chain. -/
theorem exists_arc_of_chain (hD : IsClosedDisc (univ : Set S)) [T2Space S] {G : Drawing S}
  (hG : G.IsProper) {x y : S} {A : List (ChainTerm S)} (hA : IsXYChain G x y A)
    (hx : x ∈ bd S) (hy : y ∈ bd S) (hne : x ≠ y) :
    ∃ F, IsLineWithEnds F x y ∧ F ∩ bd S = {x, y} ∧ G.IsNormal F ∧ ∀ w ∈ F, w ∈ G.V → w ≠ x → w ≠ y
      → .inl w ∈ A := by
  have hmemA : ∀ t ∈ A, t.IsValid G := hA.valid
  have hcon := isPathConnected_chain hD hG hA.ne_nil hA.valid hA.isChain
  obtain ⟨a, ha, hJa⟩ := exists_end_joined hD hG (List.head_mem hA.ne_nil) (hA.valid _
    (List.head_mem hA.ne_nil)) hA.head_matches
  obtain ⟨b, hb, hJb⟩ := exists_end_joined hD hG (List.getLast_mem hA.ne_nil) (hA.valid _
    (List.getLast_mem hA.ne_nil)) hA.last_matches
  let Zc : Set S := ⋃ u ∈ A, termSet u
  let Z : Set S := {x} ∪ Zc ∪ {y}
  have hJ : JoinedIn Z x y := by
    have h1 : JoinedIn Z x a := hJa.mono subset_union_left
    have h2 : JoinedIn Z a b := (hcon.joinedIn a ha b hb).mono ((subset_union_right).trans
      subset_union_left)
    have h3 : JoinedIn Z y b := hJb.mono (union_subset ((subset_union_right))
      ((subset_union_right).trans subset_union_left))
    exact (h1.trans h2).trans h3.symm
  obtain ⟨F, hFZ, hF⟩ := ((joinedIn_iff_eq_or_exists_isLineWithEnds hJ.source_mem hJ.target_mem).mp
    hJ).resolve_left hne
  have hZ : ∀ z ∈ Z, z = x ∨ z = y ∨ (.inl z ∈ A ∧ z ∉ bd S) ∨ (z ∉ G.U ∧ z ∉ bd S) := by
    rintro z ((rfl | hz) | rfl)
    · exact .inl rfl
    · simp only [Zc, mem_iUnion, exists_prop] at hz
      obtain ⟨t, ht, hzt⟩ := hz
      rcases t with v | r
      · obtain rfl : z = v := hzt
        by_cases hzb : z ∈ bd S
        · rcases inl_mem_bd_eq hA ht hzb with h | h
          · exact .inl h
          · exact .inr (.inl h)
        · exact .inr (.inr (.inl ⟨ht, hzb⟩))
      · have hr : r ∈ G.R := hA.valid _ ht
        refine .inr (.inr (.inr ⟨?_, hzt.2⟩))
        rcases hr with ⟨z₀, -, rfl⟩
        exact (connectedComponentIn_subset _ _ hzt.1).2
    · exact .inr (.inl rfl)
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · apply subset_antisymm
    · rintro z ⟨hz, hzb⟩
      rcases hZ z (hFZ hz) with h | h | ⟨-, h⟩ | ⟨-, h⟩
      · exact .inl h
      · exact .inr h
      · exact (h hzb).elim
      · exact (h hzb).elim
    · rintro z (rfl | h)
      · exact ⟨hF.left_mem, hx⟩
      · obtain rfl : z = y := h
        exact ⟨hF.right_mem, hy⟩
  · rintro z ⟨hzF, hzU⟩
    rcases hZ z (hFZ hzF) with rfl | rfl | ⟨h, -⟩ | ⟨h, -⟩
    · exact hG ⟨hx, hzU⟩
    · exact hG ⟨hy, hzU⟩
    · have : ChainTerm.IsValid G (Sum.inl z) := hA.valid _ h
      exact this
    · exact (h hzU).elim
  · intro w hw hV h1 h2
    rcases hZ w (hFZ hw) with h | h | ⟨h, -⟩ | ⟨h, -⟩
    · exact (h1 h).elim
    · exact (h2 h).elim
    · exact h
    · exact (h (G.V_subset_U hV)).elim

/-- Two distinct points cut an `O`-arc into two components. -/
theorem exists_two_comps [T2Space S] {C : Set S} (hC : IsOArc C) {x y : S} (hx : x ∈ C)
  (hy : y ∈ C) (hne : x ≠ y) :
    ∃ C₁ C₂, componentsIn (C \ {x, y}) = {C₁, C₂} ∧ C₁ ≠ C₂ := by
  obtain ⟨A, B, hA, hB, hU, hI⟩ := hC.lines hx hy hne
  have hsub : ∀ {L : Set S}, IsLineWithEnds L x y → closure (L \ {x, y}) ⊆ L := fun hL
    => closure_minimal sdiff_subset hL.isCompact.isClosed
  have hAB : Disjoint (closure (A \ {x, y})) (B \ {x, y}) := disjoint_left.mpr fun z h1 h2 => h2.2
    (hI ▸ ⟨hsub hA h1, h2.1⟩)
  have hBA : Disjoint (A \ {x, y}) (closure (B \ {x, y})) := disjoint_left.mpr fun z h1 h2 => h1.2
    (hI ▸ ⟨h1.1, hsub hB h2⟩)
  refine ⟨A \ {x, y}, B \ {x, y}, ?_, fun e => ?_⟩
  · rw [← componentsIn_union_eq_pair (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hA)
      (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hB) (GM14.IsLineWithEnds.nonempty_sdiff_pair
        hA) (GM14.IsLineWithEnds.nonempty_sdiff_pair hB) hAB hBA, ← union_sdiff_distrib, hU]
  · obtain ⟨z, hz⟩ := GM14.IsLineWithEnds.nonempty_sdiff_pair hA
    exact disjoint_left.mp (hAB.mono_left subset_closure) hz (e ▸ hz)

end GraphMinor.GM07
