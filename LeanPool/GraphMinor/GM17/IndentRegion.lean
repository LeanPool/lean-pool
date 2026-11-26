/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.IndentDisc
public import LeanPool.GraphMinor.GM17.RegionDegree
public import LeanPool.GraphMinor.GM17.RegionFrontier
public import LeanPool.GraphMinor.GM17.BorderArc
import LeanPool.GraphMinor.GM17.PushNode
import LeanPool.GraphMinor.GM17.CuffOrder
import LeanPool.GraphMinor.Surface.HoleDisc
import LeanPool.GraphMinor.Surface.PushOff

/-!
# The closure of a region, and chords of it

Suppose that the regions of a painting are open discs with `O`-arcs as frontiers, as (8.1) and (8.2)
of Graph Minors XVII say. Then
the closure of a region is a closed disc (`region_disc`). We cap the cuffs and use `closure_disc`. A
chord of it with ends on `bd(Σ)`
is an `I`-arc to which (8.3) applies. The disc of (8.3) contains one of the two parts of the closed
region (`exists_chord_disc`). These facts
replace the sentences of the proofs of (9.3) and (9.4) on pages 184 and 185 that say what lies
around a region.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

theorem region_outside_off (hS : IsSurface S) {Γ : Painting S}
  (hreg : ∀ r ∈ Γ.regions, IsOpen r) {r : Set S}
    (hr : r ∈ Γ.regions) {y : S} (hy : y ∈ closure r \ r) (hyN : y ∉ Γ.N) : y ∈ closure
      (closure r)ᶜ := by
  have ht2 : T2Space S := hS.2.1
  have hyU : y ∈ Γ.U := by
    by_contra hn
    obtain ⟨r', hr', hyr'⟩ := Painting.exists_region (Γ := Γ) hn
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp hy.1 r' (hreg r' hr') hyr'
    exact hy.2 (Painting.region_eq hr hr' hz' hz ▸ hyr')
  rcases Painting.mem_U_iff.mp hyU with h | ⟨d, hd, hyd⟩
  · exact absurd h hyN
  have hdisc := (Γ.cell_disc d hd).1
  refine closure_mono (s := discInt (closure d)) ?_ (hdisc.subset_closure_discInt hyd)
  intro z hz hzr
  obtain ⟨w, hw, hw'⟩ := mem_closure_iff.mp hzr _ (hdisc.isOpen_discInt hS.2.2) hz
  exact disjoint_left.mp (Painting.region_disjoint_closure hr hd) hw' hw.1

theorem region_outside (hS : IsSurface S) {Γ : Painting S}
  (hreg : ∀ r ∈ Γ.regions, IsOpen r) {r : Set S}
    (hr : r ∈ Γ.regions) (hF : IsOArc (closure r \ r)) {y : S} (hy : y ∈ closure r \ r) : y ∈
      closure (closure r)ᶜ := by
  have ht2 : T2Space S := hS.2.1
  by_cases hyN : y ∈ Γ.N
  · obtain ⟨p, hp, hne⟩ := (infinite_of_isOArc hF).exists_notMem_finite (finite_singleton y)
    obtain ⟨A, B, hA, -, hAu, -⟩ := hF.lines hy hp (fun h => hne (h ▸ rfl))
    obtain ⟨q, L, hL, hLA, hLN⟩ := exists_sub_end hA Γ.finite_N
    have hsub : L \ {y, q} ⊆ closure (closure r)ᶜ := fun z hz => by
      refine region_outside_off hS hreg hr (hAu ▸ .inl (hLA hz.1)) fun hzN => ?_
      exact hz.2 (.inl (hLN ⟨hz.1, hzN⟩))
    exact closure_minimal hsub isClosed_closure (hL.subset_closure_diff hL.left_mem)
  · exact region_outside_off hS hreg hr hy hyN

/-- **The closure of a region is a closed disc.** -/
theorem region_disc [ConnectedSpace S] (hS : IsSurface S) {Γ : Painting S}
  (hreg : ∀ r ∈ Γ.regions, IsOpenDisc r) {r : Set S}
    (hr : r ∈ Γ.regions) (hF : IsOArc (closure r \ r)) : IsClosedDisc (closure r) ∧ discBd
      (closure r) = closure r \ r := by
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, hconnT⟩ := exists_capAll S hS
  have hcT : ConnectedSpace T := hconnT inferInstance
  have ht2T : T2Space T := hT.2.1
  have hro : IsOpen r := (hreg r hr).1
  have hreg' : ∀ r ∈ Γ.regions, IsOpen r := fun r hr => (hreg r hr).1
  have hrne : r.Nonempty := arcComponentsIn_nonempty hr
  have : Nonempty S := hrne.to_subtype.map Subtype.val
  have hrsub : ∀ x ∈ r, x ∉ Γ.U := fun x hx => (arcComponentsIn_subset hr hx).2
  have hint : ∀ x ∈ r, x ∉ bd S := fun x hx h => hrsub x hx (Γ.bd_subset h)
  have hYK : ∀ x ∈ r, j x ∉ K := fun x hx h => by
    have h1 : j x ∈ range j ∩ K := ⟨mem_range_self x, h⟩
    rw [hi] at h1
    obtain ⟨y, hy, he⟩ := h1
    exact hint x hx (hj.injective he ▸ hy)
  have hYo : IsOpen (j '' r) := by
    have hcl : IsClosed (K ∪ j '' rᶜ) := hK.union (hj.isClosedMap _ hro.isClosed_compl)
    convert hcl.isOpen_compl using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ (h | ⟨x', hx', he⟩)
      · exact hYK x hx h
      · exact hx' (hj.injective he ▸ hx)
    · intro h
      have hy : y ∈ range j ∪ K := hu ▸ mem_univ y
      rcases hy with ⟨x, rfl⟩ | hy
      · by_contra h3
        exact h (.inr ⟨x, fun hx => h3 ⟨x, hx, rfl⟩, rfl⟩)
      · exact absurd (.inl hy) h
  have hclj : closure (j '' r) = j '' closure r := hj.closure_image_eq r
  have hsT : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  obtain ⟨e⟩ := (hreg r hr).2
  have hod : IsOpenDisc (j '' r) := ⟨hYo, ⟨e.trans (hj.isEmbedding.homeomorphImage r)⟩⟩
  have hdiff : closure (j '' r) \ j '' r = j '' (closure r \ r) := by
    rw [hclj, image_sdiff hj.injective]
  obtain ⟨h1, h2⟩ := closure_disc hsT hod
    (disjoint_left.mpr fun x _ hb => hb (hT.2.2 x))
    (by
      rw [hdiff]
      obtain ⟨φ⟩ := hF
      exact ⟨φ.trans (hj.isEmbedding.homeomorphImage _)⟩)
    (by
      rw [hdiff]
      rintro _ ⟨x, hx, rfl⟩
      refine closure_mono ?_ (image_closure_subset_closure_image hj.continuous (mem_image_of_mem j
        (region_outside hS hreg' hr hF hx)))
      rw [hclj]
      rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', he⟩
      exact hz (hj.injective he ▸ hz'))
  have hsub : closure (j '' r) ⊆ range j := by
    rw [hclj]
    exact image_subset_range _ _
  obtain ⟨h3, h4⟩ := isClosedDisc_preimage hj h1 hsub
  have hp : j ⁻¹' closure (j '' r) = closure r := by
    rw [hclj, preimage_image_eq _ hj.injective]
  rw [hp] at h3 h4
  refine ⟨h3, ?_⟩
  rw [h4, h2, hdiff, preimage_image_eq _ hj.injective]

/-- A closed disc whose boundary misses most of a part of a region swallows that part, once they
overlap. -/
theorem chord_part (hS : IsSurface S) {r F X X' Cx Cx' Δ : Set S} (hΔ : IsClosedDisc Δ)
  (h2 : discBd Δ ∩ r ⊆ F) (hX : IsClosedDisc X) (hXu : X ∪ X' = closure r) (hXi : X ∩ X' = F)
    (hXb : discBd X = Cx ∪ F)
    (hCx' : Cx' ⊆ X') (hC : closure r \ r = Cx ∪ Cx') {w : S} (hwr : w ∈ r) (hwF : w ∉ F)
      (hwX : w ∈ X) (hwΔ : w ∈ discInt Δ) : X ⊆ Δ := by
  have ht2 : T2Space S := hS.2.1
  have hman := hS.2.2
  have hin : discInt X ⊆ r := fun x hx => by
    by_contra h
    have hx' : x ∈ closure r \ r := ⟨hXu ▸ .inl hx.1, h⟩
    rw [hC] at hx'
    rcases hx' with h3 | h3
    · exact hx.2 (hXb ▸ .inl h3)
    · exact hx.2 (hXb ▸ .inr (hXi ▸ ⟨hx.1, hCx' h3⟩))
  have hoff : ∀ x ∈ discInt X, x ∉ F := fun x hx h => hx.2 (hXb ▸ .inr h)
  have hsub : discInt X ⊆ discInt Δ ∪ Δᶜ := fun x hx => by
    by_cases h : x ∈ Δ
    · exact .inl ⟨h, fun h3 => hoff x hx (h2 ⟨h3, hin hx⟩)⟩
    · exact .inr h
  have hwX' : w ∈ discInt X := ⟨hwX, fun h => by
    rw [hXb] at h
    rcases h with h | h
    · have h3 : w ∈ closure r \ r := hC ▸ .inl h
      exact h3.2 hwr
    · exact hwF h⟩
  have hle := hX.isPreconnected_discInt.subset_left_of_subset_union (hΔ.isOpen_discInt hman)
    hΔ.isClosed.isOpen_compl
    (disjoint_left.mpr fun x hx hx' => hx' hx.1) hsub ⟨w, hwX', hwΔ⟩
  exact hX.subset_closure_discInt.trans (closure_minimal (hle.trans sdiff_subset) hΔ.isClosed)

theorem chord_side (hS : IsSurface S) {r C₁ C₂ F Δ₁ Δ₂ Δ : Set S} {a b : S} (hrO : IsOpen r)
    (hcl : closure r \ r = C₁ ∪ C₂) (hF : IsLineWithEnds F a b) (hFr : F \ {a, b} ⊆ r)
      (hd₁ : IsClosedDisc Δ₁) (hd₂ : IsClosedDisc Δ₂)
    (hu : Δ₁ ∪ Δ₂ = closure r) (hi : Δ₁ ∩ Δ₂ = F) (hb₁ : discBd Δ₁ = C₁ ∪ F) (hb₂ : discBd Δ₂
      = C₂ ∪ F) (hΔ : IsClosedDisc Δ)
    (h1 : F ⊆ discBd Δ) (h2 : discBd Δ ∩ r ⊆ F) : Δ₁ ⊆ Δ ∨ Δ₂ ⊆ Δ := by
  have ht2 : T2Space S := hS.2.1
  obtain ⟨z, hz⟩ := line_inner_nonempty hF
  have hzr : z ∈ r := hFr hz
  obtain ⟨w, hwr, hwΔ⟩ := mem_closure_iff.mp (hΔ.subset_closure_discInt (discBd_subset _
    (h1 hz.1))) r hrO hzr
  have hwF : w ∉ F := fun h => hwΔ.2 (h1 h)
  have hwR : w ∈ Δ₁ ∪ Δ₂ := hu ▸ subset_closure hwr
  have hC₁ : C₁ ⊆ Δ₁ := fun x hx => discBd_subset _ (hb₁ ▸ .inl hx)
  have hC₂ : C₂ ⊆ Δ₂ := fun x hx => discBd_subset _ (hb₂ ▸ .inl hx)
  rcases hwR with h | h
  · exact .inl (chord_part hS hΔ h2 hd₁ hu hi hb₁ hC₂ hcl hwr hwF h hwΔ)
  · exact .inr (chord_part hS hΔ h2 hd₂ (by rw [union_comm, hu]) (by rw [inter_comm,
      hi]) hb₂ hC₁ (by rw [hcl, union_comm]) hwr hwF h hwΔ)

/-- A chord of a closed region between two nodes on `bd(Σ)`, with the disc of (8.3). -/
theorem exists_chord_disc [ConnectedSpace S] (hS : IsSurface S) {Γ : Painting S}
    (hreg : ∀ r ∈ Γ.regions, IsOpenDisc r) (hfr : ∀ r ∈ Γ.regions, IsOArc (closure r \ r))
    (h83 : ∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F → (F ∩ Γ.N).ncard = 2 →
        ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧
          Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1)
    {r C₁ C₂ : Set S} {a b : S} (hr : r ∈ Γ.regions) (hC₁ : IsLineWithEnds C₁ a b)
      (hC₂ : IsLineWithEnds C₂ a b)
    (hu : C₁ ∪ C₂ = closure r \ r) (hi : C₁ ∩ C₂ = {a, b}) (haN : a ∈ Γ.N) (hbN : b ∈ Γ.N)
      (hab : a ≠ b)
    (hab' : a ∈ bd S) (hbb : b ∈ bd S) :
    ∃ F Δ₁ Δ₂ Δ, IsLineWithEnds F a b ∧ F \ {a, b} ⊆ r ∧ F ∩ Γ.N = {a, b} ∧ IsClosedDisc Δ₁
      ∧ IsClosedDisc Δ₂ ∧ Δ₁ ∪ Δ₂ = closure r ∧
      Δ₁ ∩ Δ₂ = F ∧ discBd Δ₁ = C₁ ∪ F ∧ discBd Δ₂ = C₂ ∪ F ∧ IsClosedDisc Δ ∧ F ⊆ discBd Δ
        ∧ discBd Δ ⊆ F ∪ bd S ∧ Δ ∩ Γ.N ⊆ F ∧
      {c ∈ Γ.C | c ⊆ Δ}.ncard = 1 ∧ (∀ x ∈ Δ \ F, Δ ∈ 𝓝 x) ∧ (Δ₁ ⊆ Δ ∨ Δ₂ ⊆ Δ) := by
  have ht2 : T2Space S := hS.2.1
  obtain ⟨hdR, hbR⟩ := region_disc hS hreg hr (hfr r hr)
  obtain ⟨F, Δ₁, Δ₂, hF, hFb, hFR, hd₁, hd₂, hu', hi', hb₁, hb₂⟩ :=
    split_disc hdR hC₁ hC₂ hab (hu.trans hbR.symm) hi
  have hFr : F \ {a, b} ⊆ r := fun x hx => by
    by_contra h
    have h3 : x ∈ F ∩ discBd (closure r) := ⟨hx.1, hbR ▸ ⟨hFR hx.1, h⟩⟩
    rw [hFb] at h3
    exact hx.2 h3
  have hrU : ∀ x ∈ r, x ∉ Γ.U := fun x hx => (arcComponentsIn_subset hr hx).2
  have hrb : Disjoint r (bd S) := disjoint_left.mpr fun x hx h => hrU x hx (Γ.bd_subset h)
  have hFend : ∀ x ∈ F, x ∉ r → x = a ∨ x = b := fun x hx h => by_contra fun h3 => h (hFr ⟨hx, h3⟩)
  have hFN : F ∩ Γ.N = {a, b} := by
    refine Subset.antisymm (fun x hx => hFend x hx.1 fun h => hrU x h (Γ.N_subset hx.2)) ?_
    rintro x (rfl | rfl)
    · exact ⟨hF.left_mem, haN⟩
    · exact ⟨hF.right_mem, hbN⟩
  have hFbd : F ∩ bd S = lineEnds F := by
    rw [lineEnds_eq hF]
    refine Subset.antisymm (fun x hx => hFend x hx.1 fun h => disjoint_left.mp hrb h hx.2) ?_
    rintro x (rfl | rfl)
    · exact ⟨hF.left_mem, hab'⟩
    · exact ⟨hF.right_mem, hbb⟩
  obtain ⟨Δ, hΔ, h1, h2, h3, h4⟩ := h83 F ⟨hF.choose⟩
    (fun x hx => (hFN ▸ (show x ∈ ({a, b} : Set S) from hFend x hx.1 fun h
      => hrU x h hx.2) : x ∈ F ∩ Γ.N).2) hFbd
    (by rw [hFN, ncard_pair hab])
  have hFb : F ∩ bd S = {a, b} := by
    rw [← lineEnds_eq hF, hFbd]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnb⟩ := arc_disc_data hS hF hFb hΔ h1 h2
  exact ⟨F, Δ₁, Δ₂, Δ, hF, hFr, hFN, hd₁, hd₂, hu', hi', hb₁, hb₂, hΔ, h1, h2, h3, h4, hnb,
    chord_side hS (hreg r hr).1 hu.symm hF hFr hd₁ hd₂ hu' hi' hb₁ hb₂ hΔ h1 (fun x hx =>
      (h2 hx.1).elim id fun hb => (disjoint_left.mp hrb hx.2 hb).elim)⟩

end GraphMinor.GM17
