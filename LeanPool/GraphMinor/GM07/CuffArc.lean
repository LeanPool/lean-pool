/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffFinger
public import LeanPool.GraphMinor.GM09.Section9
public import LeanPool.GraphMinor.Surface.Triangulate

/-!
# The `O`-arcs `A'` and `A` of (6.1)

Graph Minors VII, (6.1), page 237: "Let us choose a $G$-normal $O$-arc $A'$ surrounding $C$ with
$|V(G) \cap A'| \le 1$, such that as many vertices and edges of $G$ as possible are included in the
union
of $A'$ with its inside." and then "It follows that we may choose a $G$-normal $O$-arc $A$
surrounding $C$, with $A' - A$ inside $A$, and with $|V(G) \cap A| = 2$."

We phrase this with the closed disc `Δ` of `Σ + CHat` that an `O`-arc bounds. The paper says "The
maximality condition now implies" that `|V(G) ∩ A'| = 1`, and that the region at `A'` has a vertex
outside.
The case that needs care is that all edges on the outer side of this region are loops at the vertex
of `A'`. A loop lies in the closure of the region, so it lies in the disc given by (5.7), and it
bounds
a disc there. If that disc holds `C`, a parallel copy of the loop beats `A'`. If no such disc holds
`C`, then these discs and the region fill `Σ + CHat`, which is then a disc. This is why the count
has edges.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] {T : Type u} [TopologicalSpace T]

/-- A closed disc of `Σ + CHat` around the pasted disc `D`, with a `G`-normal boundary with at most
`r` vertices. -/
def IsCuffDisc (G : Drawing S) (j : S → T) (D : Set T) (r : ℕ) (Δ : Set T) : Prop :=
  IsClosedDisc Δ ∧ D ⊆ Δ ∧ G.IsNormal (j ⁻¹' discBd Δ) ∧ (G.V ∩ j ⁻¹' discBd Δ).ncard ≤ r

/-- The number of vertices and edges of `G` in a set of `Σ + CHat`. -/
noncomputable def cuffCount (G : Drawing S) (j : S → T) (Δ : Set T) : ℕ :=
  (G.V ∩ j ⁻¹' Δ).ncard + {e ∈ G.E | j '' e ⊆ Δ}.ncard

omit [TopologicalSpace T] in
theorem cuffCount_le (G : Drawing S) (j : S → T) (Δ : Set T) : cuffCount G j Δ
  ≤ G.V.ncard + G.E.ncard :=
  add_le_add (ncard_le_ncard inter_subset_left G.finite_V) (ncard_le_ncard
    (sep_subset _ _) G.finite_edges)

omit [TopologicalSpace T] in
theorem cuffCount_lt (G : Drawing S) (j : S → T) {Δ Δ' : Set T} (h : Δ ⊆ Δ') (hnew :
  (∃ x ∈ G.V, j x ∈ Δ' ∧ j x ∉ Δ) ∨ ∃ e ∈ G.E, j '' e ⊆ Δ' ∧ ¬ j '' e ⊆ Δ) : cuffCount G j Δ <
    cuffCount G j Δ' := by
  have h1 : G.V ∩ j ⁻¹' Δ ⊆ G.V ∩ j ⁻¹' Δ' := inter_subset_inter_right _ (preimage_mono h)
  have h2 : {e ∈ G.E | j '' e ⊆ Δ} ⊆ {e ∈ G.E | j '' e ⊆ Δ'} := fun e he => ⟨he.1, he.2.trans h⟩
  have hf1 : (G.V ∩ j ⁻¹' Δ').Finite := G.finite_V.subset inter_subset_left
  have hf2 : {e ∈ G.E | j '' e ⊆ Δ'}.Finite := G.finite_edges.subset (sep_subset _ _)
  rcases hnew with ⟨x, hx, h3, h4⟩ | ⟨e, he, h3, h4⟩
  · have : (G.V ∩ j ⁻¹' Δ).ncard < (G.V ∩ j ⁻¹' Δ').ncard := ncard_lt_ncard ⟨h1, fun h5 => h4
      (h5 ⟨hx, h3⟩).2⟩ hf1
    exact add_lt_add_of_lt_of_le this (ncard_le_ncard h2 hf2)
  · have : {e ∈ G.E | j '' e ⊆ Δ}.ncard < {e ∈ G.E | j '' e ⊆ Δ'}.ncard
      := ncard_lt_ncard ⟨h2, fun h5 => h4 (h5 ⟨he, h3⟩).2⟩ hf2
    exact add_lt_add_of_le_of_lt (ncard_le_ncard h1 hf1) this

omit [TopologicalSpace T] in
/-- A disc with the most vertices and edges, in a family that is not empty. -/
theorem exists_max_count (G : Drawing S) (j : S → T) {P : Set T → Prop} {Δ₀ : Set T}
  (h₀ : P Δ₀) : ∃ Δ, P Δ ∧ ∀ Δ', P Δ' → cuffCount G j Δ' ≤ cuffCount G j Δ := by
  have hne : {n | ∃ Δ, P Δ ∧ cuffCount G j Δ = n}.Nonempty := ⟨_, Δ₀, h₀, rfl⟩
  have hb : BddAbove {n | ∃ Δ, P Δ ∧ cuffCount G j Δ = n} := ⟨G.V.ncard + G.E.ncard, by
    rintro _ ⟨Δ, -, rfl⟩
    exact cuffCount_le G j Δ⟩
  obtain ⟨Δ, hΔ, he⟩ := Nat.sSup_mem hne hb
  exact ⟨Δ, hΔ, fun Δ' hΔ' => by
    rw [he]
    exact le_csSup hb ⟨Δ', hΔ', rfl⟩⟩

section Cap

variable {C : Set S} {j : S → T} {D : Set T}

theorem not_mem_discInt_cap (hc : IsCappedCuff C T j D) (y : S) : j y ∉ discInt D := fun hi => hi.2
  (by
  rw [hc.discBd_eq]
  have h2 : j y ∈ range j ∩ D := ⟨mem_range_self y, hi.1⟩
  rwa [hc.inter_eq] at h2)

theorem discBd_subset_range (hc : IsCappedCuff C T j D) {Δ : Set T} (hDΔ : D ⊆ Δ) : discBd Δ ⊆
  range j := by
  have hman := hc.isSurface.2.2
  have hi : discInt D ⊆ discInt Δ := discInt_mono hman hc.isClosedDisc hDΔ
  intro x hx
  rcases hc.union_eq.ge (mem_univ x) with h | h
  · exact h
  · by_cases hb : x ∈ discBd D
    · rw [hc.discBd_eq] at hb
      exact image_subset_range _ _ hb
    · exact absurd hx (hi ⟨h, hb⟩).2

theorem image_preimage_bd (hc : IsCappedCuff C T j D) {Δ : Set T} (hDΔ : D ⊆ Δ) : j ''
  (j ⁻¹' discBd Δ) = discBd Δ :=
  image_preimage_eq_of_subset (discBd_subset_range hc hDΔ)

theorem isOArc_preimage_bd (hc : IsCappedCuff C T j D) {Δ : Set T} (hΔ : IsClosedDisc Δ)
  (hDΔ : D ⊆ Δ) : IsOArc (j ⁻¹' discBd Δ) :=
  pull_oArc hc.isEmbedding hΔ.isOArc_discBd (discBd_subset_range hc hDΔ)

variable [ConnectedSpace S]

theorem surrounds_of_disc (hS : IsSurface S) (hC : C ∈ cuffs S) (hc : IsCappedCuff C T j D)
  (hns : ¬ IsSphere T) {Δ : Set T} (hΔ : IsClosedDisc Δ) (hDΔ : D ⊆ Δ) : SurroundsCuff
    (j ⁻¹' discBd Δ) C := by
  have hT := hc.isSurface
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have : ConnectedSpace T := hc.connectedSpace hS
  have hO := isOArc_preimage_bd hc hΔ hDΔ
  refine ⟨hC, isPlanarInCappedCuff_of_cap hS hc ⟨Δ, hΔ, ?_⟩, fun hp => ?_⟩
  · rw [image_preimage_bd hc hDΔ]
    exact Surface.discBd_subset _
  · have hnull := (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hO).mp hp
    obtain ⟨E, hE, hbd⟩ := nullHomotopicOArc_bounds_disc hS hO hnull
    obtain ⟨h1, h2⟩ := isClosedDisc_image_of_injOn hE hc.isEmbedding.continuous
      hc.isEmbedding.injective.injOn
    have heq := eq_of_discBd_eq hT hns h1 hΔ (by rw [h2, hbd, image_preimage_bd hc hDΔ])
    obtain ⟨z, hz⟩ := hc.isClosedDisc.nonempty_discInt
    have : z ∈ j '' E := heq ▸ hDΔ hz.1
    obtain ⟨y, -, rfl⟩ := this
    exact not_mem_discInt_cap hc y hz

omit [ConnectedSpace S] in
theorem exists_disc_of_surrounds (hS : IsSurface S) (hc : IsCappedCuff C T j D) {F : Set S}
  (hF : IsOArc F) (hs : SurroundsCuff F C) : ∃ Δ, IsClosedDisc Δ ∧ D ⊆ Δ ∧ discBd Δ = j '' F := by
  have hT := hc.isSurface
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have hman := hT.2.2
  have hO : IsOArc (j '' F) := by
    obtain ⟨f⟩ := id hF
    exact ⟨f.trans (hc.isEmbedding.homeomorphImage F)⟩
  have hnull := (isPlanar_iff_isNullHomotopicOArc_of_isOArc hT hO).mp (hs.2.1.2.2 T j D hc)
  obtain ⟨Δ, hΔ, hbd⟩ := nullHomotopicOArc_bounds_disc hT hO hnull
  refine ⟨Δ, hΔ, ?_, hbd⟩
  have hoff : Disjoint (discInt D) (discBd Δ) := by
    rw [hbd, disjoint_left]
    rintro _ h ⟨y, -, rfl⟩
    exact not_mem_discInt_cap hc y h
  refine disc_subset_of_int_off_bd hman hc.isClosedDisc hΔ hoff ?_
  by_contra hne
  have hdis : ∀ x ∈ Δ, x ∉ discInt D := fun x hx hi => hne ⟨x, hi, hx⟩
  have hr : Δ ⊆ range j := fun x hx => by
    rcases hc.union_eq.ge (mem_univ x) with h | h
    · exact h
    · by_contra hxr
      refine hdis x hx ⟨h, fun hb => hxr ?_⟩
      rw [hc.discBd_eq] at hb
      exact image_subset_range _ _ hb
  have hcl : IsClosedEmbedding j := hc.isEmbedding.continuous.isClosedEmbedding
    hc.isEmbedding.injective
  have : Nonempty S := by
    obtain ⟨φ⟩ := id hF
    exact ⟨(φ 1).1⟩
  obtain ⟨hE, -⟩ := isClosedDisc_preimage hcl hΔ hr
  refine hs.2.2 ⟨_, hE, fun y hy => ?_⟩
  have : j y ∈ discBd Δ := hbd ▸ mem_image_of_mem j hy
  exact Surface.discBd_subset Δ this

/-- The complement of a closed disc in a connected surface is connected, if the boundary of the disc
is off the boundary of the surface. -/
theorem isPreconnected_compl_disc [T2Space T] [PreconnectedSpace T] (hman : ∀ x : T,
  IsManifoldPoint x) {Δ : Set T} (hΔ : IsClosedDisc Δ) (hint : ∀ x ∈ discBd Δ, IsInteriorPoint x) :
    IsPreconnected Δᶜ := by
  classical
  obtain ⟨E, hE, hin, -⟩ := exists_disc_around hman hΔ hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hΔ.isOArc_discBd
  obtain ⟨c, c', hc, hc', hm, hm', hl, hr, hcE, hcb, hcp⟩ := exists_disc_collar hΔ hE hin p
  -- the open annulus between the discs
  let Q : Set T := discInt E \ Δ
  have hQc : IsPreconnected Q := by
    have h1 : IsPreconnected (Ioo (1 : ℝ) 2 ×ˢ (univ : Set ℝ)) := ((convex_Ioo _ _).prod
      convex_univ).isPreconnected
    have h2 : Continuous fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) := by
      fun_prop
    have hmem : ∀ q ∈ Ioo (1 : ℝ) 2 ×ˢ (univ : Set ℝ), ‖(q.1 : ℂ) * Complex.exp
      ((q.2 : ℂ) * Complex.I)‖ = q.1 := fun q hq => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith [hq.1.1])]
    have h3 : ContinuousOn c ((fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp
      ((q.2 : ℂ) * Complex.I)) '' Ioo (1 : ℝ) 2 ×ˢ (univ : Set ℝ)) := hc.mono (by
      rintro _ ⟨q, hq, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [hmem q hq]
      exact hq.1.2.le)
    have h4 := (h1.image _ h2.continuousOn).image _ h3
    convert h4 using 1
    ext x
    constructor
    · rintro ⟨⟨hx, hxb⟩, hxΔ⟩
      refine ⟨c' x, ⟨(‖c' x‖, Complex.arg (c' x)), ⟨⟨?_, ?_⟩, mem_univ _⟩,
        Complex.norm_mul_exp_arg_mul_I _⟩, hr hx⟩
      · by_contra hle
        exact hxΔ (hcE ▸ ⟨c' x, by simpa using not_lt.mp hle, hr hx⟩)
      · have h5 : ‖c' x‖ ≤ 2 := by simpa using hm' hx
        refine lt_of_le_of_ne h5 fun h6 => hxb ?_
        rw [← hcb]
        exact ⟨c' x, by simpa using h6, hr hx⟩
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      have hn := hmem q hq
      set z := (q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) with hz
      have hzb : z ∈ Metric.closedBall (0 : ℂ) 2 := by
        simp only [mem_closedBall_zero_iff]
        rw [hn]
        exact hq.1.2.le
      have hinj := hl.injOn
      refine ⟨⟨hm hzb, fun hb => ?_⟩, fun hxΔ => ?_⟩
      · rw [← hcb] at hb
        obtain ⟨y, hy, he⟩ := hb
        rw [hinj (Metric.sphere_subset_closedBall hy) hzb he] at hy
        have : ‖z‖ = 2 := by simpa using hy
        linarith [hq.1.2]
      · rw [← hcE] at hxΔ
        obtain ⟨y, hy, he⟩ := hxΔ
        have hyb : y ∈ Metric.closedBall (0 : ℂ) 2 := Metric.closedBall_subset_closedBall
          one_le_two hy
        rw [hinj hyb hzb he] at hy
        have : ‖z‖ ≤ 1 := by simpa using hy
        linarith [hq.1.1]
  have hQO : IsOpen Q := (hE.isOpen_discInt hman).inter hΔ.isClosed.isOpen_compl
  have hYO : IsOpen Δᶜ := hΔ.isClosed.isOpen_compl
  have hEi : IsOpen (discInt E) := hE.isOpen_discInt hman
  intro u v hu hv hsub ⟨x, hxY, hxu⟩ ⟨y, hyY, hyv⟩
  by_contra hcon
  have hdis : Δᶜ ∩ (u ∩ v) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro z hz
    exact hcon ⟨z, hz.1, hz.2⟩
  have hdisj : ∀ z, z ∈ Δᶜ → z ∈ u → z ∈ v → False := fun z h1 h2 h3 =>
    (eq_empty_iff_forall_notMem.mp hdis z) ⟨h1, h2, h3⟩
  rcases hQc.subset_or_subset (u := u ∩ Δᶜ) (v := v ∩ Δᶜ) (hu.inter hYO) (hv.inter hYO)
    (disjoint_left.mpr fun z h1 h2 => hdisj z h1.2 h1.1 h2.1) (fun z hz => by
    rcases hsub hz.2 with h | h
    · exact .inl ⟨h, hz.2⟩
    · exact .inr ⟨h, hz.2⟩) with hQu | hQv
  · -- then `v` cannot meet the complement
    have hA : IsOpen (discInt E ∪ (u ∩ Δᶜ)) := hEi.union (hu.inter hYO)
    have hB : IsOpen (v ∩ Δᶜ) := hv.inter hYO
    have hdisAB : Disjoint (discInt E ∪ (u ∩ Δᶜ)) (v ∩ Δᶜ) := by
      rw [disjoint_left]
      rintro z (hz | hz) hz'
      · exact hdisj z hz'.2 (hQu ⟨hz, hz'.2⟩).1 hz'.1
      · exact hdisj z hz.2 hz.1 hz'.1
    have hcov : (univ : Set T) ⊆ (discInt E ∪ (u ∩ Δᶜ)) ∪ (v ∩ Δᶜ) := fun z _ => by
      by_cases hz : z ∈ Δ
      · exact .inl (.inl (hin hz))
      · rcases hsub hz with h | h
        · exact .inl (.inr ⟨h, hz⟩)
        · exact .inr ⟨h, hz⟩
    rcases isPreconnected_univ.subset_or_subset hA hB hdisAB hcov with h | h
    · exact disjoint_left.mp hdisAB (h (mem_univ y)) ⟨hyv, hyY⟩
    · obtain ⟨z, hz⟩ := hE.nonempty_discInt
      exact disjoint_left.mp hdisAB (.inl hz) (h (mem_univ z))
  · have hA : IsOpen (discInt E ∪ (v ∩ Δᶜ)) := hEi.union (hv.inter hYO)
    have hB : IsOpen (u ∩ Δᶜ) := hu.inter hYO
    have hdisAB : Disjoint (discInt E ∪ (v ∩ Δᶜ)) (u ∩ Δᶜ) := by
      rw [disjoint_left]
      rintro z (hz | hz) hz'
      · exact hdisj z hz'.2 hz'.1 (hQv ⟨hz, hz'.2⟩).1
      · exact hdisj z hz.2 hz'.1 hz.1
    have hcov : (univ : Set T) ⊆ (discInt E ∪ (v ∩ Δᶜ)) ∪ (u ∩ Δᶜ) := fun z _ => by
      by_cases hz : z ∈ Δ
      · exact .inl (.inl (hin hz))
      · rcases hsub hz with h | h
        · exact .inr ⟨h, hz⟩
        · exact .inl (.inr ⟨h, hz⟩)
    rcases isPreconnected_univ.subset_or_subset hA hB hdisAB hcov with h | h
    · exact disjoint_left.mp hdisAB (h (mem_univ x)) ⟨hxu, hxY⟩
    · obtain ⟨z, hz⟩ := hE.nonempty_discInt
      exact disjoint_left.mp hdisAB (.inl hz) (h (mem_univ z))

omit [ConnectedSpace S] in
/-- An edge that meets the closure of a region lies in the closure of the region. -/
theorem closure_edge_subset_of_isProper (hS : IsSurface S) [ConnectedSpace S] {G :
  Drawing S} (hG : G.IsProper) {e r : Set S} (he : e ∈ G.E) (hr : r ∈ G.R) (hm :
    (e ∩ closure r).Nonempty) : closure e ⊆ closure r := by
  have : T2Space S := hS.2.1
  obtain ⟨R, tR, i, -, Γ, hR, hRc, hi, -, -, -, hΓU, hΓV, hΓV', hmap⟩
    := exists_capped_drawing hS G hG
  obtain ⟨ℛ, hℛ, hZ, -⟩ := hmap {r} (singleton_subset_iff.mpr hr)
  rw [sUnion_singleton] at hZ
  obtain ⟨𝒜, h𝒜, hc⟩ := isGammaNice_closure_sUnion_regions hR Γ hℛ
  obtain ⟨y, hye, hyr⟩ := hm
  have hoffV : ∀ x ∈ e, i x ∈ Γ.U ∧ i x ∉ Γ.V := fun x hx => by
    have hxU : x ∈ G.U \ G.V := he.2.1 hx
    refine ⟨hΓU ▸ mem_image_of_mem i (.inl hxU.1), fun hv => ?_⟩
    obtain ⟨w, hw, hwe⟩ := hΓV' hv
    rw [hi.injective hwe] at hw
    rcases hw with h | h
    · exact hxU.2 h
    · exact hxU.2 (hG ⟨h, hxU.1⟩)
  have hjy : i y ∈ closure (⋃₀ ℛ) := by
    rw [← hZ]
    exact mem_image_of_mem i hyr
  rw [hc] at hjy
  obtain ⟨a, ha, hya⟩ := hjy
  have hae : i '' e ⊆ a := by
    rcases h𝒜 ha with (⟨v, hv, rfl⟩ | h1) | h1
    · exact absurd (show i y ∈ Γ.V from by
        have : i y = v := hya
        rw [this]
        exact hv) (hoffV y hye).2
    · have hpc : IsPathConnected (i '' e) := he.2.2.1.image hi.continuous
      have hsub : a ∪ i '' e ⊆ Γ.U \ Γ.V := union_subset h1.2.1 (by
        rintro _ ⟨x, hx, rfl⟩
        exact hoffV x hx)
      have hu : a ∪ i '' e = a := h1.2.2.2 _ hsub (h1.2.2.1.union hpc ⟨i y, hya, mem_image_of_mem i
        hye⟩) subset_union_left
      exact hu ▸ subset_union_right
    · obtain ⟨x, -, rfl⟩ := (mem_R_iff Γ).mp h1
      exact absurd (hoffV y hye).1 (connectedComponentIn_subset _ _ hya).2
  refine closure_minimal (fun x hx => ?_) isClosed_closure
  have h1 : i x ∈ ⋃₀ 𝒜 := ⟨a, ha, hae (mem_image_of_mem i hx)⟩
  rw [← hc, ← hZ] at h1
  obtain ⟨w, hw, he'⟩ := h1
  rwa [← hi.injective he']

/-- Each boundary point of a closed disc is a limit of points off the disc, if the boundary is off
the boundary of the surface. -/
theorem discBd_subset_closure_compl [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) {Δ : Set T}
  (hΔ : IsClosedDisc Δ) (hint : ∀ x ∈ discBd Δ, IsInteriorPoint x) : discBd Δ ⊆ closure Δᶜ := by
  classical
  obtain ⟨E, hE, hin, -⟩ := exists_disc_around hman hΔ hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hΔ.isOArc_discBd
  obtain ⟨c, c', hc, hc', hm, hm', hl, hr, hcE, hcb, hcp⟩ := exists_disc_collar hΔ hE hin p
  intro x hx
  obtain ⟨w, hw⟩ : ∃ w : Circle, (p w).1 = x := ⟨p.symm ⟨x, hx⟩, by simp⟩
  have hnw : ‖(w : ℂ)‖ = 1 := Circle.norm_coe w
  let f : ℝ → ℂ := fun t => (t : ℂ) * w
  have hf : Continuous f := by fun_prop
  have hfn : ∀ t ∈ Ioc (1 : ℝ) 2, ‖f t‖ = t := fun t ht => by
    simp only [f]
    rw [norm_mul, hnw, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith [ht.1])]
  let s : Set ℂ := Metric.closedBall 0 2 \ Metric.closedBall 0 1
  have hfs : MapsTo f (Ioc 1 2) s := fun t ht => ⟨by
    simp only [mem_closedBall_zero_iff]
    rw [hfn t ht]
    exact ht.2, by
    simp only [mem_closedBall_zero_iff]
    rw [hfn t ht]
    exact not_le.mpr ht.1⟩
  have h1 : (w : ℂ) ∈ closure s := by
    have h2 : (1 : ℝ) ∈ closure (Ioc (1 : ℝ) 2) := by
      rw [closure_Ioc (by norm_num)]
      exact ⟨le_rfl, by norm_num⟩
    have h3 := map_mem_closure hf h2 hfs
    simpa [f] using h3
  have hsub : s ⊆ Metric.closedBall 0 2 := sdiff_subset
  have hw2 : (w : ℂ) ∈ Metric.closedBall (0 : ℂ) 2 := by
    simp only [mem_closedBall_zero_iff, hnw]
    norm_num
  have h4 : c w ∈ closure (c '' s) := ((hc _ hw2).mono hsub).mem_closure_image h1
  rw [hcp, hw] at h4
  refine closure_mono ?_ h4
  rintro _ ⟨z, hz, rfl⟩ hzΔ
  rw [← hcE] at hzΔ
  obtain ⟨y, hy, he⟩ := hzΔ
  have hyb : y ∈ Metric.closedBall (0 : ℂ) 2 := Metric.closedBall_subset_closedBall one_le_two hy
  rw [hl.injOn hyb hz.1 he] at hy
  exact hz.2 hy

omit [ConnectedSpace S] in
theorem isOpen_image_diff_cap (hc : IsCappedCuff C T j D) {O : Set S}
  (hO : IsOpen O) : ∃ O' : Set T, IsOpen O' ∧ O = j ⁻¹' O' := by
  obtain ⟨O', h1, h2⟩ := hc.isEmbedding.isInducing.isOpen_iff.mp hO
  exact ⟨O', h1, h2.symm⟩

omit [ConnectedSpace S] in
theorem compl_disc_subset_range (hc : IsCappedCuff C T j D) {Δ : Set T}
  (hDΔ : D ⊆ Δ) : Δᶜ ⊆ range j := fun x hx => by
  rcases hc.union_eq.ge (mem_univ x) with h | h
  · exact h
  · exact absurd (hDΔ h) hx

variable [T1Space S]

omit [ConnectedSpace S] [T1Space S] in
theorem region_off_U {G : Drawing S} {r : Set S} (hr : r ∈ G.R) {x : S} (hx : x ∈ r) : x ∉ G.U := by
  obtain ⟨y, -, rfl⟩ := (mem_R_iff G).mp hr
  exact (connectedComponentIn_subset _ _ hx).2

omit [T1Space S] in
/-- **An outer edge is a loop.** Suppose that all vertices on the closure of the region `r` lie in
`Δ`. Then an edge of `G` on the closure of `r` and off `Δ` is a loop at the vertex of the boundary
of `Δ`, and it bounds a disc in the disc `E₀`, which holds the closure of `r`. -/
theorem outer_edge_loop (hS : IsSurface S) (hc : IsCappedCuff C T j D) {G : Drawing S}
  (hG : G.IsProper) {Δ E₀ : Set T} (hΔ : IsClosedDisc Δ) (hcount : (G.V ∩ j ⁻¹' discBd Δ).ncard
    ≤ 1) {r e : Set S} (hr : r ∈ G.R) (hE₀ : IsClosedDisc E₀)
    (hrE : j '' closure r ⊆ E₀) (hvert : ∀ b ∈ G.V, b ∈ closure r → j b ∈ Δ) (he : e ∈ G.E) (hme :
      (e ∩ closure r).Nonempty) (hoff : Disjoint (j '' e) Δ) :
    ∃ a ∈ G.V, j a ∈ discBd Δ ∧ closure e = e ∪ {a} ∧ ∃ B, IsClosedDisc B ∧ discBd B
      = j '' closure e := by
  have hT := hc.isSurface
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have hman := hT.2.2
  have hclr : closure e ⊆ closure r := closure_edge_subset_of_isProper hS hG he hr hme
  have hbdv : ∀ v ∈ closure e, v ∈ G.V → j v ∈ discBd Δ := fun v hv hvV => by
    by_contra hnb
    have hi : j v ∈ discInt Δ := ⟨hvert v hvV (hclr hv), hnb⟩
    have h1 : j v ∈ closure (j '' e) := image_closure_subset_closure_image
      hc.isEmbedding.continuous (mem_image_of_mem j hv)
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp h1 _ (hΔ.isOpen_discInt hman) hi
    exact disjoint_left.mp hoff hz2 hz1.1
  have hu : ∀ {u v : S}, u ∈ G.V → v ∈ G.V → j u ∈ discBd Δ → j v ∈ discBd Δ → u = v
    := fun {u v} hu hv h1 h2 =>
    (ncard_le_one (G.finite_V.subset inter_subset_left)).mp hcount u ⟨hu, h1⟩ v ⟨hv, h2⟩
  obtain ⟨u, hcap, hO⟩ : ∃ u : S, closure e ∩ G.V = {u} ∧ IsOArc (closure e) := by
    rcases G.edge_cond e he with ⟨u, v, huv, hcap, -⟩ | h
    · exfalso
      have h1 : u ∈ closure e ∩ G.V := by
        rw [hcap]
        exact .inl rfl
      have h2 : v ∈ closure e ∩ G.V := by
        rw [hcap]
        exact .inr rfl
      exact huv (hu h1.2 h2.2 (hbdv u h1.1 h1.2) (hbdv v h2.1 h2.2))
    · exact h
  have hu1 : u ∈ closure e ∩ G.V := by
    rw [hcap]
    exact rfl
  refine ⟨u, hu1.2, hbdv u hu1.1 hu1.2, ?_, ?_⟩
  · apply subset_antisymm
    · intro x hx
      by_cases hxV : x ∈ G.V
      · have h2 : x ∈ closure e ∩ G.V := ⟨hx, hxV⟩
        rw [hcap] at h2
        exact .inr h2
      · have h3 : x ∈ closure e \ G.V := ⟨hx, hxV⟩
        rw [GM09.closure_edge_diff_V_eq G he] at h3
        exact .inl h3
    · rintro x (hx | hx)
      · exact subset_closure hx
      · rw [hx]
        exact hu1.1
  · have hO' : IsOArc (j '' closure e) := by
      obtain ⟨f⟩ := id hO
      exact ⟨f.trans (hc.isEmbedding.homeomorphImage _)⟩
    have hsub : j '' closure e ⊆ E₀ := (image_mono hclr).trans hrE
    obtain ⟨B, -, hB, hbd⟩ := nullHomotopicOArcIn_bounds_disc hT hO' hsub
      (isNullHomotopicOArcIn_of_subset_disc hO' subset_rfl hE₀ hsub)
    exact ⟨B, hB, hbd⟩

omit [ConnectedSpace S] [T1Space S] in
/-- **A loop around the cuff.** If the disc of an outer loop holds `D`, then a parallel copy of the
loop bounds a disc with more of `G` than `Δ` has. -/
theorem outer_loop_beats [T2Space S] (hc : IsCappedCuff C T j D) {G : Drawing S}
    {Δ B : Set T} {e : Set S} {a : S} (hΔ : IsClosedDisc Δ) (hDΔ : D ⊆ Δ) (he : e ∈ G.E)
    (hoff : Disjoint (j '' e) Δ) (ha : a ∈ G.V) (haΔ : j a ∈ discBd Δ)
    (hcl : closure e = e ∪ {a}) (hB : IsClosedDisc B) (hbd : discBd B = j '' closure e)
      (hDB : D ⊆ B) (hint : ∀ x ∈ discBd B, IsInteriorPoint x) (hcj : IsClosedEmbedding j) :
    ∃ Δ₂, IsCuffDisc G j D 1 Δ₂ ∧ cuffCount G j Δ < cuffCount G j Δ₂ := by
  classical
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have hman := hT.2.2
  have hii := hcj.injective
  have hsu : Δ ⊆ B := by
    refine disc_subset_of_int_off_bd hman hΔ hB ?_ ?_
    · rw [disjoint_left, hbd, hcl, image_union]
      rintro x hx (h | h)
      · exact disjoint_left.mp hoff h hx.1
      · rw [image_singleton, mem_singleton_iff] at h
        subst h
        exact hx.2 haΔ
    · obtain ⟨z, hz⟩ := hc.isClosedDisc.nonempty_discInt
      exact ⟨z, discInt_mono hman hc.isClosedDisc hDΔ hz, hDB hz.1⟩
  obtain ⟨E, hE, hBE, -⟩ := exists_disc_around hman hB hint isOpen_univ (subset_univ _)
  have hZ : IsClosed (j '' (G.U \ e)) := hcj.isClosedMap _ (isClosed_U_sdiff_edge G he)
  obtain ⟨Δ₂, h1, h2, -, -, h5, -, h7⟩ := exists_disc_push_off hB hE hBE hZ
  have hee : ∀ x ∈ e, j x ∈ B := fun x hx => Surface.discBd_subset B (hbd ▸ mem_image_of_mem j
    (subset_closure hx))
  have hnoZ : ∀ x ∈ e, j x ∉ j '' (G.U \ e) := fun x hx ⟨y, hy, hxy⟩ => hy.2 (hii hxy ▸ hx)
  have hUa : ∀ x ∈ G.U, j x ∈ discBd Δ₂ → x = a := fun x hxU hx => by
    by_cases hxe : x ∈ e
    · exact absurd (h5 ⟨hx, hee x hxe⟩) (hnoZ x hxe)
    · have h8 := h7 ⟨hx, mem_image_of_mem j ⟨hxU, hxe⟩⟩
      rw [hbd, hcl, image_union] at h8
      rcases h8 with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
      · exact absurd (hii hxy ▸ hy) hxe
      · rw [← hii hxy]
        exact hy
  refine ⟨Δ₂, ⟨h1, hDB.trans h2, fun x hx => ?_, ?_⟩, cuffCount_lt G j (hsu.trans h2) (.inr ⟨e,
    he, ?_, ?_⟩)⟩
  · rw [hUa x hx.2 hx.1]
    exact ha
  · have hsub : G.V ∩ j ⁻¹' discBd Δ₂ ⊆ ({a} : Set S) :=
      fun x hx => hUa x (G.V_subset_U hx.1) hx.2
    exact (ncard_le_ncard hsub).trans (by simp)
  · rintro _ ⟨x, hx, rfl⟩
    exact h2 (hee x hx)
  · obtain ⟨x, hx⟩ := he.1
    exact fun h => disjoint_left.mp hoff (mem_image_of_mem j hx) (h (mem_image_of_mem j hx))

omit [T1Space S] in
/-- **The region and its loops fill the surface.** Suppose that the disc `B e` of each outer edge
`e` misses `D`, in the sense that `D` is not inside. Then the region `r` and the discs `B e` hold
every point off `Δ`. In the proof this set
is open, and its closure adds no point off `Δ`, because the only frontier of `r` off `Δ` lies on the
outer edges and those lie in the discs. -/
theorem outer_fills (hS : IsSurface S) (hc : IsCappedCuff C T j D) {G : Drawing S} (hG : G.IsProper)
    {Δ : Set T} {r : Set S} {p : S} (hΔ : IsClosedDisc Δ) (hDΔ : D ⊆ Δ)
    (hn : G.IsNormal (j ⁻¹' discBd Δ))
    (hint : ∀ x ∈ discBd Δ, IsInteriorPoint x) (hr : r ∈ G.R) (hpr : p ∈ r) (hpΔ : j p ∈ discBd Δ)
      (hvert : ∀ b ∈ G.V, b ∈ closure r → j b ∈ Δ) (hcj : IsClosedEmbedding j) {B : Set S
        → Set T} {a : Set S → S}
    (hB : ∀ e ∈ {e ∈ G.E | (e ∩ closure r).Nonempty ∧ Disjoint (j '' e) Δ}, IsClosedDisc (B e)
      ∧ discBd (B e) = j '' closure e ∧ closure e = e ∪ {a e} ∧ j (a e) ∈ discBd Δ ∧ ¬ D ⊆ B e
        ∧ ∀ x ∈ discBd (B e), IsInteriorPoint x) :
    Δᶜ ⊆ j '' r ∪ ⋃ e ∈ {e ∈ G.E | (e ∩ closure r).Nonempty ∧ Disjoint (j '' e) Δ}, B e := by
  classical
  have hT := hc.isSurface
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  have : T2Space T := hT.2.1
  have : ConnectedSpace T := hc.connectedSpace hS
  have hman := hT.2.2
  have hii := hcj.injective
  set 𝓛 : Set (Set S) := {e ∈ G.E | (e ∩ closure r).Nonempty ∧ Disjoint (j '' e) Δ} with h𝓛
  have hfin : 𝓛.Finite := G.finite_edges.subset (sep_subset _ _)
  have hpU : p ∉ G.U := region_off_U hr hpr
  -- the region misses each disc
  have hrB : ∀ e ∈ 𝓛, Disjoint (j '' r) (B e) := fun e he => by
    obtain ⟨hBd, hbd, hcl, haΔ, hDB, -⟩ := hB e he
    have hrpre : IsPreconnected (j '' r) := (region_isPreconnected hr).image _
      hcj.continuous.continuousOn
    have hoffbd : Disjoint (j '' r) (discBd (B e)) := by
      rw [hbd, disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he'⟩
      rw [← hii he'] at hx
      exact region_off_U hr hx (G.closure_subset_U he.1 hy)
    have hIoff : discInt Δ ⊆ (B e)ᶜ := by
      have hd : Disjoint (discInt Δ) (frontier (B e)) := by
        refine Disjoint.mono_right (frontier_disc_subset hman hBd) ?_
        rw [disjoint_left, hbd, hcl, image_union]
        rintro x hx (h | h)
        · exact disjoint_left.mp he.2.2 h hx.1
        · rw [image_singleton, mem_singleton_iff] at h
          subst h
          exact hx.2 haΔ
      rcases inside_or_off hΔ.isPreconnected_discInt hBd.isClosed hd with h | h
      · refine absurd ?_ hDB
        have h3 : Δ ⊆ B e := hΔ.subset_closure_discInt.trans (closure_minimal
          (h.trans interior_subset) hBd.isClosed)
        exact hDΔ.trans h3
      · exact h
    have hp1 : j p ∉ B e := fun hin => by
      by_cases hb : j p ∈ discBd (B e)
      · exact disjoint_left.mp hoffbd (mem_image_of_mem j hpr) hb
      · obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp (hΔ.subset_closure_discInt
          (Surface.discBd_subset Δ hpΔ)) _ (hBd.isOpen_discInt hman) ⟨hin, hb⟩
        exact hIoff hz2 hz1.1
    rcases inside_or_off hrpre hBd.isClosed (hoffbd.mono_right (frontier_disc_subset hman hBd))
      with h | h
    · exact absurd (interior_subset (h (mem_image_of_mem j hpr))) hp1
    · exact disjoint_left.mpr fun x hx hx' => h hx hx'
  -- the set is open
  obtain ⟨O, hO, hrO⟩ := isOpen_image_diff_cap hc (region_isOpen hr)
  have hOr : O \ Δ ⊆ j '' r := fun x hx => by
    obtain ⟨y, rfl⟩ := compl_disc_subset_range hc hDΔ hx.2
    exact ⟨y, hrO ▸ hx.1, rfl⟩
  let u : Set T := (j '' r ∪ ⋃ e ∈ 𝓛, B e) \ Δ
  have huo : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hx | hx, hxΔ⟩
    · have hxO : x ∈ O := by
        obtain ⟨y, hy, rfl⟩ := hx
        have : y ∈ j ⁻¹' O := hrO ▸ hy
        exact this
      exact Filter.mem_of_superset ((hO.sdiff hΔ.isClosed).mem_nhds ⟨hxO,
        hxΔ⟩) fun z hz => ⟨.inl (hOr hz), hz.2⟩
    · obtain ⟨e, he, hxB⟩ := mem_iUnion₂.mp hx
      obtain ⟨hBd, hbd, hcl, haΔ, hDB, hbi⟩ := hB e he
      by_cases hb : x ∈ discBd (B e)
      · obtain ⟨y, hy, rfl⟩ := hbd ▸ hb
        have hye : y ∈ e := by
          rcases hcl ▸ hy with h | h
          · exact h
          · rw [h] at hxΔ
            exact absurd (Surface.discBd_subset Δ haΔ) hxΔ
        obtain ⟨E, hE, hBE, -⟩ := exists_disc_around hman hBd hbi isOpen_univ (subset_univ _)
        have hZc : IsClosed (j '' (G.U \ e)) := hcj.isClosedMap _ (isClosed_U_sdiff_edge G he.1)
        have hW : IsOpen (j '' (G.U \ e) ∪ Δ)ᶜ := (hZc.union hΔ.isClosed).isOpen_compl
        have hyW : j y ∈ (j '' (G.U \ e) ∪ Δ)ᶜ := by
          rintro (⟨z, hz, he'⟩ | h)
          · exact hz.2 (hii he' ▸ hye)
          · exact hxΔ h
        obtain ⟨N, hNo, hyN, hNW, hNp, -⟩ := exists_side_nbhd hman hBd hE hBE hb hW hyW
        have hNr : N \ B e ⊆ j '' r := by
          have hNoff : ∀ z ∈ N, z ∉ Δ := fun z hz h => hNW hz (.inr h)
          have hsubr : N \ B e ⊆ range j := fun z hz => compl_disc_subset_range hc hDΔ
            (hNoff z hz.1)
          have hpre : IsPreconnected (j ⁻¹' (N \ B e)) := by
            rw [← hcj.isInducing.isPreconnected_image, image_preimage_eq_of_subset hsubr]
            exact hNp
          obtain ⟨w, hw, hwN⟩ : (j '' r ∩ N).Nonempty := by
            have hyc : y ∈ closure r := by
              obtain ⟨z, hz1, hz2⟩ := he.2.1
              have : e ∈ G.E := he.1
              exact closure_edge_subset_of_isProper hS hG he.1 hr ⟨z, hz1, hz2⟩ (subset_closure hye)
            obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hyc _ (hNo.preimage hcj.continuous) hyN
            exact ⟨j w, mem_image_of_mem j hw2, hw1⟩
          obtain ⟨w', hw'r, rfl⟩ := hw
          have hsubU : j ⁻¹' (N \ B e) ⊆ G.Uᶜ := fun z hz hzU => by
            by_cases hze : z ∈ e
            · exact hz.2 (Surface.discBd_subset (B e) (hbd ▸ mem_image_of_mem j
                (subset_closure hze)))
            · exact hNW hz.1 (.inl (mem_image_of_mem j ⟨hzU, hze⟩))
          have hw'in : w' ∈ j ⁻¹' (N \ B e) := ⟨hwN, disjoint_left.mp (hrB e he)
            (mem_image_of_mem j hw'r)⟩
          intro z hz
          obtain ⟨t, rfl⟩ := hsubr hz
          obtain ⟨q, -, rfl⟩ := (mem_R_iff G).mp hr
          have h1 : j ⁻¹' (N \ B e) ⊆ connectedComponentIn (univ \ G.U) w'
            := hpre.subset_connectedComponentIn hw'in fun z hz => ⟨mem_univ z, hsubU hz⟩
          rw [connectedComponentIn_eq hw'r]
          exact mem_image_of_mem j (h1 hz)
        refine Filter.mem_of_superset (hNo.mem_nhds hyN) fun z hz => ?_
        have hzΔ : z ∉ Δ := fun h => hNW hz (.inr h)
        by_cases hzB : z ∈ B e
        · exact ⟨.inr (mem_iUnion₂.mpr ⟨e, he, hzB⟩), hzΔ⟩
        · exact ⟨.inl (hNr ⟨hz, hzB⟩), hzΔ⟩
      · refine Filter.mem_of_superset (((hBd.isOpen_discInt hman).sdiff hΔ.isClosed).mem_nhds
          ⟨⟨hxB, hb⟩, hxΔ⟩) fun z hz => ?_
        exact ⟨.inr (mem_iUnion₂.mpr ⟨e, he, hz.1.1⟩), hz.2⟩
  -- it meets the complement of the disc
  have hne : (Δᶜ ∩ u).Nonempty := by
    have hpO : j p ∈ O := by
      have : p ∈ j ⁻¹' O := hrO ▸ hpr
      exact this
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp (discBd_subset_closure_compl hman hΔ hint hpΔ) _ hO
      hpO
    exact ⟨z, hz2, .inl (hOr ⟨hz1, hz2⟩), hz2⟩
  -- no point off the disc is a limit of the set without being in it
  have hcl : closure u ∩ Δᶜ ⊆ u := by
    rintro x ⟨hxc, hxΔ⟩
    have hcu : closure u ⊆ j '' closure r ∪ ⋃ e ∈ 𝓛, B e := by
      refine closure_minimal ?_ ((hcj.isClosedMap _ isClosed_closure).union
        (hfin.isClosed_biUnion fun e he => (hB e he).1.isClosed))
      rintro z ⟨hz | hz, -⟩
      · obtain ⟨y, hy, rfl⟩ := hz
        exact .inl (mem_image_of_mem j (subset_closure hy))
      · exact .inr hz
    rcases hcu hxc with ⟨y, hy, rfl⟩ | h
    · rcases closure_region_subset hr hy with h | hyU
      · exact ⟨.inl (mem_image_of_mem j h), hxΔ⟩
      · by_cases hyV : y ∈ G.V
        · exact absurd (hvert y hyV hy) hxΔ
        · obtain ⟨e, he, hye⟩ := G.exists_edge_of_mem hyU hyV
          have hpc : IsPreconnected (j '' e) := he.2.2.1.isConnected.isPreconnected.image _
            hcj.continuous.continuousOn
          have hdf : Disjoint (j '' e) (frontier Δ) := by
            refine Disjoint.mono_right (frontier_disc_subset hman hΔ) ?_
            rw [disjoint_left]
            rintro _ ⟨z, hz, rfl⟩ hzb
            have hzU : z ∈ G.U \ G.V := he.2.1 hz
            exact hzU.2 (hn ⟨hzb, hzU.1⟩)
          have hee : e ∈ 𝓛 := by
            refine ⟨he, ⟨y, hye, hy⟩, ?_⟩
            rcases inside_or_off hpc hΔ.isClosed hdf with h | h
            · exact absurd (interior_subset (h (mem_image_of_mem j hye))) hxΔ
            · exact disjoint_left.mpr fun z hz hz' => h hz hz'
          obtain ⟨hBd, hbd, -⟩ := hB e hee
          exact ⟨.inr (mem_iUnion₂.mpr ⟨e, hee, Surface.discBd_subset (B e)
            (hbd ▸ mem_image_of_mem j (subset_closure hye))⟩), hxΔ⟩
    · exact ⟨.inr h, hxΔ⟩
  have hfinal := (isPreconnected_compl_disc hman hΔ hint).subset_of_closure_inter_subset huo hne hcl
  exact fun x hx => (hfinal hx).1

omit [T1Space S] in
/-- A set of `𝒜_r(C)` meets no other cuff, if `r` and the number of vertices of the other cuff add
up to less than `α(G)`. -/
theorem off_other_cuffs (hS : IsSurface S) {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c)
  (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {G :
    Drawing S} (hG : G.IsProper) (hC : C ∈ cuffs S) {r : ℕ}
    (hα : ∀ C₁ ∈ cuffs S, C₁ ≠ C → r + (G.V ∩ C₁).ncard < alpha G) {y : S} (hy : y ∈ scriptA G r C)
      (hb : y ∈ bd S) (hyC : y ∉ C) : False := by
  have h1 : y ∈ ⋃₀ cuffs S := by
    rw [sUnion_cuffs]
    exact hb
  obtain ⟨C₁, hC₁, hyC₁⟩ := h1
  have hne : C₁ ≠ C := fun h => hyC (h ▸ hyC₁)
  have h2 := theorem_5_3_proof hS hcyl G hC hC₁ hne.symm (hα C₁ hC₁ hne)
  have h3 : y ∈ scriptA G (G.V ∩ C₁).ncard C₁ := ⟨C₁, isScriptASet_cuff hS habc hm hG hC₁ le_rfl,
    hyC₁⟩
  exact eq_empty_iff_forall_notMem.mp h2 y ⟨hy, h3⟩

omit [T1Space S] in
/-- The boundary of a cuff disc gives a set of `𝒜_r(C)`. -/
theorem IsCuffDisc.isScriptASet (hS : IsSurface S) (hC : C ∈ cuffs S) (hc : IsCappedCuff C T j D)
  (hns : ¬ IsSphere T) {G : Drawing S} {r : ℕ} {Δ : Set T} (hd : IsCuffDisc G j D r Δ) :
    IsScriptASet G r C (j ⁻¹' discBd Δ) := by
  have hO := isOArc_preimage_bd hc hd.1 hd.2.1
  exact ⟨isSolid_of_isOArc hS hO, isConnected_of_isOArc hO, hd.2.2.1,
    surrounds_of_disc hS hC hc hns hd.1 hd.2.1, hd.2.2.2⟩

omit [T1Space S] in
/-- A cuff disc is off the boundary of `Σ + CHat`. -/
theorem IsCuffDisc.disjoint_bd (hS : IsSurface S) {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c)
  (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {G :
    Drawing S} (hG : G.IsProper) (hC : C ∈ cuffs S)
    (hc : IsCappedCuff C T j D) (hbT : bd T = j '' (bd S \ C)) {r : ℕ} (hα : ∀ C₁ ∈ cuffs S, C₁ ≠ C
      → r + (G.V ∩ C₁).ncard < alpha G) {Δ : Set T} (hd : IsCuffDisc G j D r Δ) : Disjoint Δ (bd T)
        := by
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have hns : ¬ IsSphere T := not_isSphere_cap hS habc hm hc
  rw [disjoint_left]
  intro x hx hxb
  by_cases hb : x ∈ discBd Δ
  · obtain ⟨y, hy, rfl⟩ := hbT ▸ hxb
    exact off_other_cuffs hS habc hm hcyl hG hC hα ⟨_, hd.isScriptASet hS hC hc hns, hb⟩ hy.1 hy.2
  · exact hxb (isInteriorPoint_of_mem_discInt hT.2.2 hd.1 ⟨hx, hb⟩)

omit [T1Space S] in
omit [ConnectedSpace S] in
/-- An `O`-arc that surrounds `C` with at most one vertex can not lie outside a disc that has gained
a vertex over a maximal cuff disc. -/
theorem two_le_of_surrounds (hS : IsSurface S) (hc : IsCappedCuff C T j D) {G : Drawing S} {Δ' Δ₁ :
  Set T} (hΔ₁ : IsClosedDisc Δ₁) (hD₁ : D ⊆ Δ₁) (hsub : Δ' ⊆ Δ₁) (hmax : ∀ Δ, IsCuffDisc G j D 1 Δ
    → cuffCount G j Δ ≤ cuffCount G j Δ')
    {b : S} (hbV : b ∈ G.V) (hb₁ : j b ∈ Δ₁) (hb : j b ∉ Δ') {F : Set S} (hn : G.IsNormal F)
      (hF : IsOArc F) (hs : SurroundsCuff F C) (hoff : Disjoint (j '' F) (discInt Δ₁)) : 2 ≤
        (G.V ∩ F).ncard := by
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have hman := hT.2.2
  by_contra hlt
  obtain ⟨E, hE, hDE, hbd⟩ := exists_disc_of_surrounds hS hc hF hs
  have hinj := hc.isEmbedding.injective
  have hsu : Δ₁ ⊆ E := by
    refine disc_subset_of_int_off_bd hman hΔ₁ hE ?_ ?_
    · rw [hbd]
      exact hoff.symm
    · obtain ⟨z, hz⟩ := hc.isClosedDisc.nonempty_discInt
      exact ⟨z, discInt_mono hman hc.isClosedDisc hD₁ hz, hDE hz.1⟩
  have hpre : j ⁻¹' discBd E = F := by
    rw [hbd, preimage_image_eq _ hinj]
  have hd : IsCuffDisc G j D 1 E := ⟨hE, hDE, by rwa [hpre], by
    rw [hpre]
    omega⟩
  have h1 := hmax E hd
  have h2 := cuffCount_lt G j (hsub.trans hsu) (.inl ⟨b, hbV, hsu hb₁, hb⟩)
  omega

/-- **The choice of `A` in (6.1).** There is a disc of `Σ + CHat` around `D` whose boundary has
exactly two vertices of `G`, off the other cuffs, and such that an `O`-arc on the far side that
surrounds `C` has at least two vertices. -/
theorem exists_two_vertex_disc (hS : IsSurface S) {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c)
  (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {G :
    Drawing S} (hG : G.IsProper) (hC : C ∈ cuffs S)
    (hc : IsCappedCuff C T j D) (hbT : bd T = j '' (bd S \ C)) (hsmall : (G.V ∩ C).ncard ≤ 1)
      (hα : 9 ≤ alpha G) (hα₂ : ∀ C₁ ∈ cuffs S, C₁ ≠ C → 2 + (G.V ∩ C₁).ncard < alpha G) {C₁ : Set
        S} (hC₁ : C₁ ∈ cuffs S) (hne : C₁ ≠ C) :
    ∃ Δ, IsCuffDisc G j D 2 Δ ∧ (G.V ∩ j ⁻¹' discBd Δ).ncard = 2 ∧ Disjoint Δ (bd T)
      ∧ ∀ F, G.IsNormal F → IsOArc F → SurroundsCuff F C → Disjoint (j '' F) (discInt Δ) → 2 ≤
        (G.V ∩ F).ncard := by
  classical
  have hT := hc.isSurface
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have : CompactSpace S := hS.1
  have hman := hT.2.2
  have hcj : IsClosedEmbedding j := hc.isEmbedding.continuous.isClosedEmbedding
    hc.isEmbedding.injective
  have hii := hcj.injective
  have hns : ¬ IsSphere T := not_isSphere_cap hS habc hm hc
  have hCsub : C ⊆ bd S := connectedComponentIn_subset_of_cuff hC
  have hpreD : j ⁻¹' discBd D = C := by
    rw [hc.discBd_eq, preimage_image_eq _ hii]
  have hα₁ : ∀ C₁ ∈ cuffs S, C₁ ≠ C → 1 + (G.V ∩ C₁).ncard < alpha G := fun C₁ h1 h2 => by
    have := hα₂ C₁ h1 h2
    omega
  have hD₀ : IsCuffDisc G j D 1 D := ⟨hc.isClosedDisc, subset_rfl, by
    rw [hpreD]
    exact fun x hx => hG ⟨hCsub hx.1, hx.2⟩, by rwa [hpreD]⟩
  obtain ⟨Δ', hd, hmax⟩ := exists_max_count G j hD₀
  have hscr := hd.isScriptASet hS hC hc hns
  have hoff := hd.disjoint_bd hS habc hm hcyl hG hC hc hbT hα₁
  have hint : ∀ x ∈ discBd Δ', IsInteriorPoint x := fun x hx => by
    by_contra h
    exact disjoint_left.mp hoff (Surface.discBd_subset Δ' hx) h
  obtain ⟨hΔ', hDΔ', hn, hcount⟩ := id hd
  have hO := isOArc_preimage_bd hc hΔ' hDΔ'
  have hVf : (G.V ∩ j ⁻¹' discBd Δ').Finite := G.finite_V.subset inter_subset_left
  obtain ⟨p, hpA, hpV⟩ : ∃ p ∈ j ⁻¹' discBd Δ', p ∉ G.V := by
    by_contra hall
    push Not at hall
    obtain ⟨φ⟩ := id hO
    have hfin : (j ⁻¹' discBd Δ').Finite := G.finite_V.subset hall
    refine (isConnected_of_isOArc hO).isPreconnected.infinite_of_nontrivial ⟨φ 1, (φ 1).2,
      φ (Circle.exp Real.pi), (φ _).2, fun h3 => ?_⟩ hfin
    have h4 : (1 : Circle) = Circle.exp Real.pi := φ.injective (Subtype.ext h3)
    have h5 : ((1 : Circle) : ℂ) = (Circle.exp Real.pi : ℂ) := congrArg _ h4
    rw [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_one] at h5
    norm_num at h5
  have hpU : p ∉ G.U := fun h => hpV (hn ⟨hpA, h⟩)
  obtain ⟨r, hr, hpr⟩ := exists_region_of_notMem hpU
  have hpΔ : j p ∈ discBd Δ' := hpA
  have hrA : r ⊆ scriptA G 1 C := region_subset_scriptA hS hr ⟨p, hpr, _, hscr, hpA⟩
  obtain ⟨E₀, hE₀, hrE₀⟩ := (theorem_5_7_proof hS hm habc hG hC (r := 1) (by omega)).2.2 T j D hc
  have hrE : j '' closure r ⊆ E₀ := by
    have h1 : closure r ⊆ j ⁻¹' E₀ := closure_minimal (fun x hx => hrE₀ (mem_image_of_mem j
      (hrA hx))) (hE₀.isClosed.preimage hcj.continuous)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 hx
  have hbdS : ∀ {x : S}, j x ∈ bd T → x ∈ bd S ∧ x ∉ C := fun {x} hx => by
    obtain ⟨y, hy, he⟩ := hbT ▸ hx
    exact hii he ▸ hy
  have hroff : ∀ x ∈ r, j x ∉ bd T := fun x hx h =>
    off_other_cuffs hS habc hm hcyl hG hC hα₁ (hrA hx) (hbdS h).1 (hbdS h).2
  by_cases hcase : ∃ b ∈ G.V, b ∈ closure r ∧ j b ∉ Δ'
  · -- a vertex on the region outside the disc: run a finger to it
    obtain ⟨w, hwV, hwc, hwΔ⟩ := hcase
    have hXc : IsClosed (j ⁻¹' Δ') := hΔ'.isClosed.preimage hcj.continuous
    have hjoin : JoinedIn (r ∪ {w}) p w := by
      have hnw : w ∈ (G.U \ G.V)ᶜ := fun h => h.2 hwV
      have hnp : p ∈ (G.U \ G.V)ᶜ := fun h => hpU h.1
      refine (joinedIn_region_union_pair hS hG hr (subset_closure hpr) hnp hwc hnw).mono ?_
      rintro z (hz | rfl | rfl)
      · exact .inl hz
      · exact .inl hpr
      · exact .inr rfl
    obtain ⟨x, hxX, L, hLZ, hL, hLX⟩ := exists_whisker_line hXc (Surface.discBd_subset Δ' hpΔ) hwΔ
      hjoin
    have hxw : x ≠ w := fun h => hwΔ (h ▸ hxX)
    have hxL : x ∈ L := hL.left_mem
    have hwL : w ∈ L := hL.right_mem
    have hxr : x ∈ r := by
      rcases hLZ hxL with h | h
      · exact h
      · exact absurd h hxw
    have hLU : ∀ z ∈ L, z ∈ G.U → z = w := fun z hz hzU => by
      rcases hLZ hz with h | h
      · exact absurd hzU (region_off_U hr h)
      · exact h
    have hxb : j x ∈ discBd Δ' := by
      by_contra hnb
      have hxi : j x ∈ discInt Δ' := ⟨hxX, hnb⟩
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp (closure_line_diff_ends hL hxL) (j ⁻¹' discInt Δ')
        ((hΔ'.isOpen_discInt hman).preimage hcj.continuous) hxi
      have hzx : z = x := hLX ⟨hz2.1, hz1.1⟩
      exact hz2.2 (.inl hzx)
    have hLA : L ∩ j ⁻¹' discBd Δ' ⊆ {x} := fun z hz => hLX ⟨hz.1, Surface.discBd_subset Δ' hz.2⟩
    have hsubV : G.V ∩ (j ⁻¹' discBd Δ' ∪ L) ⊆ insert w (G.V ∩ j ⁻¹' discBd Δ') := by
      rintro z ⟨hzV, hz | hz⟩
      · exact .inr ⟨hzV, hz⟩
      · exact .inl (hLU z hz (G.V_subset_U hzV))
    have hcard2 : (G.V ∩ (j ⁻¹' discBd Δ' ∪ L)).ncard ≤ 2 := (ncard_le_ncard hsubV
      (hVf.insert w)).trans ((ncard_insert_le _ _).trans (by omega))
    have hscr2 : IsScriptASet G 2 C (j ⁻¹' discBd Δ' ∪ L) := hscr.whisker hS hxb hL hLA (fun z hz
      => by
      rw [hLU z hz.1 hz.2]
      exact hwV) hcard2
    have hLoff : ∀ z ∈ L, j z ∉ bd T := fun z hz h =>
      off_other_cuffs hS habc hm hcyl hG hC hα₂ ⟨_, hscr2, .inr hz⟩ (hbdS h).1 (hbdS h).2
    obtain ⟨e⟩ := (cappedCuff_homeo_model hS hm hC hc).2
    have hZc : IsClosed (j '' G.U) := hcj.isClosedMap _ G.isClosed_U
    obtain ⟨Δ₁, h1, h2, h3, h4, h5, h6⟩ := exists_finger_of_homeo hT e hΔ'
      (image_line hc.isEmbedding hL) (hii.ne hxw) hxb
      (by
        rintro _ ⟨⟨z, hz, rfl⟩, hzΔ⟩
        rw [show z = x from hLX ⟨hz, hzΔ⟩]
        rfl) hwΔ hZc (mem_image_of_mem j (G.V_subset_U hwV))
      (by
        rintro _ ⟨⟨z, hz, rfl⟩, ⟨y, hy, he⟩⟩
        rw [hLU z hz (hii he ▸ hy)]
        rfl)
      (by
        rw [disjoint_left]
        rintro t (ht | ⟨z, hz, rfl⟩) htb
        · exact disjoint_left.mp hoff ht htb
        · exact hLoff z hz htb)
    have hvert₁ : ∀ y ∈ G.U, j y ∈ discBd Δ₁ → y = w ∨ y ∈ G.V ∩ j ⁻¹' discBd Δ' := fun y hy hb
      => by
      rcases h5 ⟨hb, mem_image_of_mem j hy⟩ with ⟨h7, -⟩ | h7
      · exact .inr ⟨hn ⟨h7, hy⟩, h7⟩
      · exact .inl (hii h7)
    have hn₁ : G.IsNormal (j ⁻¹' discBd Δ₁) := fun y hy => by
      rcases hvert₁ y hy.2 hy.1 with rfl | h
      · exact hwV
      · exact h.1
    have hwA : w ∉ G.V ∩ j ⁻¹' discBd Δ' := fun h => hwΔ (Surface.discBd_subset Δ' h.2)
    have hset : G.V ∩ j ⁻¹' discBd Δ₁ = insert w (G.V ∩ j ⁻¹' discBd Δ') := by
      ext y
      constructor
      · rintro ⟨hyV, hy⟩
        exact hvert₁ y (G.V_subset_U hyV) hy
      · rintro (rfl | ⟨hyV, hy⟩)
        · exact ⟨hwV, h3⟩
        · exact ⟨hyV, h4 ⟨hy, mem_image_of_mem j (G.V_subset_U hyV)⟩⟩
    have hcard : (G.V ∩ j ⁻¹' discBd Δ₁).ncard = (G.V ∩ j ⁻¹' discBd Δ').ncard + 1 := by
      rw [hset, ncard_insert_of_notMem hwA hVf]
    have hgain : cuffCount G j Δ' < cuffCount G j Δ₁ := cuffCount_lt G j h2
      (.inl ⟨w, hwV, Surface.discBd_subset Δ₁ h3, hwΔ⟩)
    have hone : (G.V ∩ j ⁻¹' discBd Δ').ncard = 1 := by
      by_contra hne1
      have h0 : (G.V ∩ j ⁻¹' discBd Δ').ncard = 0 := by omega
      have hle := hmax Δ₁ ⟨h1, hDΔ'.trans h2, hn₁, by omega⟩
      omega
    refine ⟨Δ₁, ⟨h1, hDΔ'.trans h2, hn₁, by omega⟩, by omega, h6, fun F hFn hFO hFs hFoff => ?_⟩
    exact two_le_of_surrounds hS hc h1 (hDΔ'.trans h2) h2 hmax hwV (Surface.discBd_subset Δ₁ h3)
      hwΔ hFn hFO hFs hFoff
  · -- no vertex outside: the region and its loops give a contradiction
    exfalso
    push Not at hcase
    have hcl : ∀ e ∈ {e ∈ G.E | (e ∩ closure r).Nonempty ∧ Disjoint (j '' e) Δ'}, ∃ (a : S)
      (B : Set T), IsClosedDisc B ∧ discBd B = j '' closure e ∧ closure e = e ∪ {a}
        ∧ j a ∈ discBd Δ' ∧ a ∈ G.V ∧ ∀ x ∈ discBd B, IsInteriorPoint x := by
      intro e he
      obtain ⟨a, haV, haΔ, hcle, B, hB, hbd⟩ := outer_edge_loop hS hc hG hΔ' hcount hr hE₀ hrE
        hcase he.1 he.2.1 he.2.2
      refine ⟨a, B, hB, hbd, hcle, haΔ, haV, fun x hx => ?_⟩
      by_contra hnot
      obtain ⟨y, hy, rfl⟩ := hbd ▸ hx
      have hb : j y ∈ bd T := hnot
      rw [hcle] at hy
      rcases hy with hy | hy
      · have hyU := he.1.2.1 hy
        exact hyU.2 (hG ⟨(hbdS hb).1, hyU.1⟩)
      · rw [hy] at hb
        exact disjoint_left.mp hoff (Surface.discBd_subset Δ' haΔ) hb
    have : Nonempty S := ⟨p⟩
    choose! a' B hB hbd hcle haΔ haV hbi using hcl
    by_cases hin : ∃ e ∈ {e ∈ G.E | (e ∩ closure r).Nonempty ∧ Disjoint (j '' e) Δ'}, D ⊆ B e
    · obtain ⟨e, he, hDB⟩ := hin
      obtain ⟨Δ₂, h1, h2⟩ := outer_loop_beats hc hΔ' hDΔ' he.1 he.2.2 (haV e he) (haΔ e he)
        (hcle e he) (hB e he) (hbd e he) hDB (hbi e he) hcj
      have := hmax Δ₂ h1
      omega
    · push Not at hin
      have hfill := outer_fills hS hc hG hΔ' hDΔ' hn hint hr hpr hpΔ hcase hcj (B := B) (a
        := a') fun e he => ⟨hB e he, hbd e he, hcle e he, haΔ e he, hin e he, hbi e he⟩
      obtain ⟨y, hy⟩ := (isConnected_of_isOArc ((cuff_statement.{u} S hS).2.2 C₁ hC₁)).nonempty
      have hyb : y ∈ bd S := connectedComponentIn_subset_of_cuff hC₁ hy
      have hyC : y ∉ C := fun h => disjoint_left.mp (cuffs_disjoint hC₁ hC hne) hy h
      have hjb : j y ∈ bd T := hbT ▸ mem_image_of_mem j ⟨hyb, hyC⟩
      rcases hfill (fun h => disjoint_left.mp hoff h hjb) with ⟨z, hz, he'⟩ | h
      · exact hroff z hz (he' ▸ hjb)
      · obtain ⟨e, he, hxB⟩ := mem_iUnion₂.mp h
        by_cases hb : j y ∈ discBd (B e)
        · exact hjb (hbi e he _ hb)
        · exact hjb (isInteriorPoint_of_mem_discInt hman (hB e he) ⟨hxB, hb⟩)

end Cap

end GraphMinor.GM07
