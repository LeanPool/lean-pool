/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Graph
public import LeanPool.GraphMinor.GM19.Section6Reroute
public import LeanPool.GraphMinor.GM11.RadialAccess
public import LeanPool.GraphMinor.Surface.EdgeLens
public import LeanPool.GraphMinor.Surface.ArcInPath
public import LeanPool.GraphMinor.Surface.Crossing

/-!
# Regions of a drawing near an edge

The facts about regions that the proof of (6.6) of Graph Minors XIX uses. If a point of an edge lies
in the closure of a region, then so does the whole edge (`edge_subset_closure`). Two vertices in the
closure of a region are joined by a line through the region (`exists_line_in_region`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GM11

local notation "𝕀" => unitInterval

variable {S : Type} [TopologicalSpace S]

theorem region_props [LocallyConnectedSpace S] (G : Drawing S) {r : Set S}
  (hr : r ∈ G.regions) :
    IsOpen r ∧ IsPreconnected r ∧ r.Nonempty ∧ Disjoint r G.U ∧ (∀ A : Set S, IsPreconnected A
      → Disjoint A G.U → (A ∩ r).Nonempty → A ⊆ r) ∧ closure r \ r ⊆ G.U := by
  obtain ⟨x, hx, rfl⟩ := id hr
  have hO : IsOpen G.Uᶜ := G.isClosed_U.isOpen_compl
  have hsub : connectedComponentIn G.Uᶜ x ⊆ G.Uᶜ := connectedComponentIn_subset _ _
  refine ⟨hO.connectedComponentIn, isPreconnected_connectedComponentIn, ⟨x,
    mem_connectedComponentIn hx⟩, Set.disjoint_left.mpr fun y hy hyU => hsub hy hyU, ?_, ?_⟩
  · rintro A hA hd ⟨y, hyA, hyr⟩
    rw [connectedComponentIn_eq hyr]
    exact hA.subset_connectedComponentIn hyA fun z hz hzU => Set.disjoint_left.mp hd hz hzU
  · rintro z ⟨hz, hzr⟩
    by_contra hzU
    have hopen : IsOpen (connectedComponentIn G.Uᶜ z) := hO.connectedComponentIn
    obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hz _ hopen (mem_connectedComponentIn hzU)
    exact hzr ((connectedComponentIn_eq hw₂).trans (connectedComponentIn_eq hw₁).symm ▸
      mem_connectedComponentIn hzU)

variable [T2Space S]

/-- Near a point of an edge, the edge lies in the closure of each region that has the point in its
closure. -/
theorem exists_nhds_edge (hT : IsClosedSurface S) (G : Drawing S) (hl : LoopFree G) {e r : Set S}
  (he : e ∈ G.E) (hr : r ∈ G.regions) {x : S} (hxe : x ∈ e) (hxr : x ∈ closure r) :
    ∃ O, IsOpen O ∧ x ∈ O ∧ e ∩ O ⊆ closure r := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hT
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  obtain ⟨hro, -, -, hrU, hrA, -⟩ := region_props G hr
  obtain ⟨p, q, hpq, hti, hlin⟩ := hl e he
  obtain ⟨a, ha, hrg, ha0, ha1⟩ := hlin.exists_arc
  have hcl : closure e = e ∪ tilde e := by
    rw [tilde]
    exact (union_sdiff_cancel subset_closure).symm
  have hxcl : x ∈ range a := hrg ▸ subset_closure hxe
  obtain ⟨t, rfl⟩ := hxcl
  have hee : Disjoint e (tilde e) := Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy
  have hedV : Disjoint e G.V := Set.disjoint_left.mpr fun y hy hy' => (he.2.1 hy).2 hy'
  have hmid : ∀ s, a s ∈ e ∨ s = 0 ∨ s = 1 := fun s => by
    have h1 : a s ∈ closure e := hrg ▸ mem_range_self s
    rw [hcl] at h1
    rcases h1 with h1 | h1
    · exact .inl h1
    · rw [hti] at h1
      rcases h1 with h1 | h1
      · exact .inr (.inl (ha.2 (h1.trans ha0.symm)))
      · exact .inr (.inr (ha.2 (h1.trans ha1.symm)))
  have hptilde : p ∈ tilde e ∧ q ∈ tilde e := by rw [hti]; simp
  have h0e : a 0 ∉ e := by rw [ha0]; exact hptilde.1.2
  have h1e : a 1 ∉ e := by rw [ha1]; exact hptilde.2.2
  have ht0 : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 fun h => h0e (by
    have : t = 0 := Subtype.ext h.symm
    rwa [this] at hxe)
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => h1e (by
    have : t = 1 := Subtype.ext h
    rwa [this] at hxe)
  let t₁ : 𝕀 := ⟨t / 2, by constructor <;> linarith⟩
  let t₂ : 𝕀 := ⟨(1 + t) / 2, by constructor <;> linarith⟩
  have h1t : t₁ < t := by
    change (t : ℝ) / 2 < t
    linarith
  have ht2 : t < t₂ := by
    change (t : ℝ) < (1 + t) / 2
    linarith
  have h12 : t₁ < t₂ := h1t.trans ht2
  have hL : IsLineWithEnds (a '' Icc t₁ t₂) (a t₁) (a t₂) := by
    have h1 := (ha.sub (ne_of_lt h12)).isLineWithEnds
    rwa [range_subArc a h12.le, subArc_zero, subArc_one] at h1
  have hane : a t₁ ≠ a t₂ := fun h => (ne_of_lt h12) (ha.2 h)
  let Z : Set S := (G.V ∪ ⋃ f ∈ G.E \ {e}, closure f) ∪ (a '' Iic t₁ ∪ a '' Ici t₂)
  have hZ : IsClosed Z := by
    refine IsClosed.union (G.finite_V.isClosed.union ?_) ?_
    · exact (G.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
    · exact (isClosed_Iic.isCompact.image ha.1).isClosed.union (isClosed_Ici.isCompact.image
      ha.1).isClosed
  have hinner : ∀ s, 0 < s → s < 1 → a s ∈ e := fun s h0 h1 => by
    rcases hmid s with h | h | h
    · exact h
    · exact absurd h (ne_of_gt h0)
    · exact absurd h (ne_of_lt h1)
  have hLZ : a '' Icc t₁ t₂ ∩ Z ⊆ {a t₁, a t₂} := by
    rintro _ ⟨⟨s, hs, rfl⟩, hz⟩
    have ht₁ : (t₁ : ℝ) = t / 2 := rfl
    have ht₂ : (t₂ : ℝ) = (1 + t) / 2 := rfl
    have hs1' : (t₁ : ℝ) ≤ s := hs.1
    have hs2' : (s : ℝ) ≤ t₂ := hs.2
    have hs0 : 0 < s := by
      change (0 : ℝ) < s
      linarith
    have hs1 : s < 1 := by
      change (s : ℝ) < 1
      linarith
    have hse := hinner s hs0 hs1
    rcases hz with (hz | hz) | hz | hz
    · exact absurd hz (Set.disjoint_left.mp hedV hse)
    · obtain ⟨f, hf, hsf⟩ := mem_iUnion₂.mp hz
      exact absurd (edge_eq_of_mem G he hf.1 (subset_closure hse) hsf
        (Set.disjoint_left.mp hedV hse)) (fun h => hf.2 h.symm)
    · obtain ⟨w, hw, hwe⟩ := hz
      have := ha.2 hwe
      subst this
      exact .inl (congrArg a (le_antisymm hw hs.1 : w = t₁))
    · obtain ⟨w, hw, hwe⟩ := hz
      have := ha.2 hwe
      subst this
      exact .inr (congrArg a (le_antisymm hs.2 hw : w = t₂))
  obtain ⟨D, A, B, hD, hLD, hDZ, -, -, hbL, hDe, hAc, hBc, hAn, hBn, hAL, hBL, hLA, hLB, -⟩
    := exists_edge_lens hT hL hane hZ hLZ
  have hUZ : G.U ⊆ Z ∪ a '' Icc t₁ t₂ := fun y hy => by
    by_cases hyV : y ∈ G.V
    · exact .inl (.inl (.inl hyV))
    obtain ⟨f, hf, hyf⟩ := exists_edge_of_mem G hy hyV
    by_cases hfe : f = e
    · subst hfe
      obtain ⟨s, rfl⟩ : y ∈ range a := hrg ▸ subset_closure hyf
      rcases le_total s t₁ with h | h
      · exact .inl (.inr (.inl ⟨s, h, rfl⟩))
      rcases le_total t₂ s with h' | h'
      · exact .inl (.inr (.inr ⟨s, h', rfl⟩))
      · exact .inr ⟨s, ⟨h, h'⟩, rfl⟩
    · exact .inl (.inl (.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe⟩, subset_closure hyf⟩)))
  have hsideU : ∀ {C : Set S}, C ⊆ D → Disjoint C (a '' Icc t₁ t₂) → Disjoint C G.U
    := fun {C} hC hdis => Set.disjoint_left.mpr fun y hy hyU => by
    rcases hUZ hyU with h | h
    · apply Set.disjoint_left.mp hdis hy
      rcases hDZ ⟨hC hy, h⟩ with h' | h'
      · exact h' ▸ ⟨t₁, ⟨le_rfl, h12.le⟩, rfl⟩
      · exact h' ▸ ⟨t₂, ⟨h12.le, le_rfl⟩, rfl⟩
    · exact Set.disjoint_left.mp hdis hy h
  have hAsub : A ⊆ D := by rw [hDe]; exact fun y hy => .inl (.inl hy)
  have hBsub : B ⊆ D := by rw [hDe]; exact fun y hy => .inl (.inr hy)
  have hxL : a t ∈ a '' Icc t₁ t₂ := ⟨t, ⟨h1t.le, ht2.le⟩, rfl⟩
  have hxbd : a t ∉ discBd D := fun h => by
    rcases hbL ⟨h, hxL⟩ with h' | h'
    · exact (ne_of_gt h1t) (ha.2 h')
    · exact (ne_of_lt ht2) (ha.2 h')
  have hOopen : IsOpen (discInt D) := hD.isOpen_discInt hman
  have hLU : a '' Icc t₁ t₂ ⊆ G.U := by
    rintro _ ⟨s, -, rfl⟩
    have : closure e ⊆ G.U := G.closure_subset_U he
    exact this (hrg ▸ mem_range_self s)
  refine ⟨discInt D, hOopen, ⟨hLD hxL, hxbd⟩, ?_⟩
  have hmeet : (r ∩ discInt D).Nonempty := by
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hxr _ hOopen ⟨hLD hxL, hxbd⟩
    exact ⟨y, hy2, hy1⟩
  obtain ⟨y, hyr, hyD⟩ := hmeet
  have hyL : y ∉ a '' Icc t₁ t₂ := fun h => Set.disjoint_left.mp hrU hyr (hLU h)
  have hyD' : y ∈ A ∪ B ∪ a '' Icc t₁ t₂ := hDe ▸ hyD.1
  have hLcl : a '' Icc t₁ t₂ ⊆ closure r := by
    rcases hyD' with (hyA | hyB) | h
    · exact hLA.trans (closure_mono (hrA A hAc (hsideU hAsub hAL) ⟨y, hyA, hyr⟩))
    · exact hLB.trans (closure_mono (hrA B hBc (hsideU hBsub hBL) ⟨y, hyB, hyr⟩))
    · exact absurd h hyL
  rintro w ⟨hwe, hwD⟩
  have hwU : w ∈ G.U := by
    have : closure e ⊆ G.U := G.closure_subset_U he
    exact this (subset_closure hwe)
  rcases hUZ hwU with h | h
  · rcases hDZ ⟨hwD.1, h⟩ with h' | h'
    · exact hLcl ⟨t₁, ⟨le_rfl, h12.le⟩, h'.symm⟩
    · exact hLcl ⟨t₂, ⟨h12.le, le_rfl⟩, h'.symm⟩
  · exact hLcl h

/-- **An edge with a point in the closure of a region lies in that closure.** -/
theorem edge_subset_closure (hT : IsClosedSurface S) (G : Drawing S) (hl : LoopFree G) {e r : Set
  S} (he : e ∈ G.E) (hr : r ∈ G.regions) (hne : (e ∩ closure r).Nonempty) : e ⊆ closure r := by
  classical
  choose! O hO hxO hsub using fun x (hx : x ∈ e ∩ closure r) => exists_nhds_edge hT G hl he hr hx.1
    hx.2
  have hc : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  by_contra hn
  obtain ⟨y, hye, hyr⟩ := not_subset.mp hn
  let u : Set S := ⋃ x ∈ e ∩ closure r, O x
  have hu : IsOpen u := isOpen_biUnion fun x hx => hO x hx
  obtain ⟨x, hxe, hxr⟩ := hne
  obtain ⟨z, hze, hzu, hzr⟩ := hc u (closure r)ᶜ hu isClosed_closure.isOpen_compl
    (fun w hw => by
      by_cases h : w ∈ closure r
      · exact .inl (mem_iUnion₂.mpr ⟨w, ⟨hw, h⟩, hxO w ⟨hw, h⟩⟩)
      · exact .inr h)
    ⟨x, hxe, mem_iUnion₂.mpr ⟨x, ⟨hxe, hxr⟩, hxO x ⟨hxe, hxr⟩⟩⟩ ⟨y, hye, hyr⟩
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hzu
  exact hzr (hsub w hw ⟨hze, hzw⟩)

/-- **A line through a region.** Two vertices with an edge each, in the closure of a region, are
joined by a line that runs through the region. It follows from the path of `GM11.exists_access` at
each end. -/
theorem exists_line_in_region (hT : IsClosedSurface S) [Nonempty S] (G : Drawing S) {r : Set S}
  (hr : r ∈ G.regions) {a b : S} (ha : a ∈ G.V) (hb : b ∈ G.V) (hab : a ≠ b)
    (hae : ∃ e ∈ G.E, a ∈ tilde e) (hbe : ∃ e ∈ G.E, b ∈ tilde e) (har : a ∈ closure r)
      (hbr : b ∈ closure r) :
    ∃ L, IsLineWithEnds L a b ∧ L \ {a, b} ⊆ r := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨hro, -, hrn, -, -, -⟩ := region_props G hr
  obtain ⟨γ, hγ⟩ := exists_edgePar G
  have hhalf : ∀ x, (∃ e ∈ G.E, x ∈ tilde e) → (halfEdges G γ x).Nonempty := by
    rintro x ⟨e, he, hx⟩
    have h1 : x ∈ closure e ∩ G.V := GM19.tilde_eq_inter_V G he ▸ hx
    rw [closure_inter_V_eq hγ he] at h1
    rcases h1 with h1 | h1
    · exact ⟨(e, false), he, h1.symm⟩
    · exact ⟨(e, true), he, h1.symm⟩
  have hR : r ∈ G.R := by
    change r ∈ componentsIn (univ \ G.U)
    rw [← compl_eq_univ_sdiff]
    exact hr
  obtain ⟨g₁, hg₁, g₁0, g₁t⟩ := exists_access hT G hγ ha (hhalf a hae) hR har
  obtain ⟨g₂, hg₂, g₂0, g₂t⟩ := exists_access hT G hγ hb (hhalf b hbe) hR hbr
  have hpc : IsPathConnected r := isPathConnected_of_isOpen hT hro (region_props G hr).2.1 hrn
  have h1r : g₁ 1 ∈ r := g₁t 1 (by simp)
  have h2r : g₂ 1 ∈ r := g₂t 1 (by simp)
  let P₁ : Path a (g₁ 1) := ⟨⟨g₁, hg₁⟩, g₁0, rfl⟩
  let P₂ : Path b (g₂ 1) := ⟨⟨g₂, hg₂⟩, g₂0, rfl⟩
  obtain ⟨M, hM⟩ := hpc.joinedIn _ h1r _ h2r
  let P := P₁.trans (M.trans P₂.symm)
  obtain ⟨c, hc, hci, hc0, hc1, hcr⟩ := exists_arc_of_path (γ := P) P.continuous
    (by simpa [P] using hab)
  have hP0 : P 0 = a := P.source
  have hP1 : P 1 = b := P.target
  refine ⟨range c, ?_, ?_⟩
  · have h := IsArcMap.isLineWithEnds (a := c) ⟨hc, hci⟩
    rwa [hc0, hc1, hP0, hP1] at h
  · rintro y ⟨hy, hyn⟩
    have hy' : y ∈ range P := hcr hy
    have hyab : y ≠ a ∧ y ≠ b := by simpa using hyn
    have hrP : range P = range P₁ ∪ (range M ∪ range P₂) := by
      simp only [P, Path.trans_range, Path.symm_range]
    rw [hrP] at hy'
    rcases hy' with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
    · by_cases ht : t = 0
      · subst ht
        exact absurd g₁0 hyab.1
      · exact g₁t t (unitInterval.pos_iff_ne_zero.mpr ht)
    · exact hM t
    · by_cases ht : t = 0
      · subst ht
        exact absurd g₂0 hyab.2
      · exact g₂t t (unitInterval.pos_iff_ne_zero.mpr ht)

end GraphMinor.GM19
