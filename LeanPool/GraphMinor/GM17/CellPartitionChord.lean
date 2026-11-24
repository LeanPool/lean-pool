/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CellPartitionFace
public import LeanPool.GraphMinor.GM17.Section5
import LeanPool.GraphMinor.Surface.CutLift

/-!
# Claim (2) of the proof of (11.1)

Claim (2) of the proof of (11.1) of Graph Minors XVII, page 190, says that a circuit of length four
of the graph `H` bounds a region of `H`, which holds one cell. We state it on faces: two different
faces with two common
nodes `u` and `v` have a cell with nodes `{u, v}` and with one gap on each face (`par_faces`). The
proof is the paper's. Chords through the two faces between `u` and `v` make a normal curve, which is
the case split of Claim (1). For two regions it is an
`O`-arc and we use the hypothesis (8.5). For a region and a cuff it is an `I`-arc and we use the
hypothesis (8.3). The two cuffs case cannot occur, as cuffs are disjoint. The disc holds a part of
each face, so a whole line of the face between `u` and `v`.
This line has no other nodes, so it is a gap, and the disc has at most one cell, so the two gaps
belong to one cell.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Painting

variable {S : Type} [TopologicalSpace S] [T2Space S] {Γ : Painting S}

/-- A chord of a closed region between two nodes of its frontier. -/
theorem chord_of_region [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {r C₁ C₂ : Set S} {a
  b : S} (hr : r ∈ Γ.regions) (hC₁ : IsLineWithEnds C₁ a b) (hC₂ : IsLineWithEnds C₂ a b)
    (hu : C₁ ∪ C₂ = closure r \ r) (hi : C₁ ∩ C₂ = {a, b}) (haN : a ∈ Γ.N) (hbN : b ∈ Γ.N)
      (hab : a ≠ b) :
    ∃ F Δ₁ Δ₂, IsLineWithEnds F a b ∧ F \ {a, b} ⊆ r ∧ F ∩ Γ.N = {a, b} ∧ F ∩ Γ.U ⊆ {a, b}
      ∧ F ∩ bd S ⊆ {a, b} ∧ IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ Δ₁ ∪ Δ₂ = closure r ∧
      Δ₁ ∩ Δ₂ = F ∧ discBd Δ₁ = C₁ ∪ F ∧ discBd Δ₂ = C₂ ∪ F := by
  obtain ⟨hdR, hbR⟩ := region_disc hS (fun r hr => (h.hreg r hr).1) hr (h.hreg r hr).2
  obtain ⟨F, Δ₁, Δ₂, hF, hFb, hFR, hd₁, hd₂, hu', hi', hb₁, hb₂⟩ := split_disc hdR hC₁ hC₂ hab
    (hu.trans hbR.symm) hi
  have hFr : F \ {a, b} ⊆ r := fun x hx => by
    by_contra h
    have h3 : x ∈ F ∩ discBd (closure r) := ⟨hx.1, hbR ▸ ⟨hFR hx.1, h⟩⟩
    rw [hFb] at h3
    exact hx.2 h3
  have hrU : ∀ x ∈ r, x ∉ Γ.U := fun x hx => (arcComponentsIn_subset hr hx).2
  have hFend : ∀ x ∈ F, x ∉ r → x = a ∨ x = b := fun x hx h => by_contra fun h3 => h (hFr ⟨hx, h3⟩)
  refine ⟨F, Δ₁, Δ₂, hF, hFr, ?_, fun x hx => hFend x hx.1 fun h => hrU x h hx.2,
    fun x hx => hFend x hx.1 fun h => hrU x h (Γ.bd_subset hx.2), hd₁, hd₂, hu', hi', hb₁, hb₂⟩
  refine Subset.antisymm (fun x hx => hFend x hx.1 fun h => hrU x h (Γ.N_subset hx.2)) ?_
  rintro x (rfl | rfl)
  · exact ⟨hF.left_mem, haN⟩
  · exact ⟨hF.right_mem, hbN⟩

omit [T2Space S] in
/-- A cell off a closed set `F` that meets a closed set `Δ` with `Δ \ F` open lies in `Δ`. -/
theorem cell_in_disc {Δ F c : Set S} (hΔ : IsClosed Δ) (hF : IsClosed F)
  (hnb : ∀ x ∈ Δ \ F, Δ ∈ 𝓝 x) (hc : c ∈ Γ.C) (hcF : Disjoint c F) {x : S} (hx : x ∈ c)
    (hxΔ : x ∈ Δ) : c ⊆ Δ := by
  have hW : IsOpen (Δ \ F) := by
    rw [isOpen_iff_mem_nhds]
    exact fun y hy => Filter.inter_mem (hnb y hy) (hF.isOpen_compl.mem_nhds hy.2)
  have hpc : IsPreconnected c := (arcComponentsIn_isPathConnected hc).isConnected.isPreconnected
  have hsub : c ⊆ (Δ \ F) ∪ Δᶜ := fun y hy => by
    by_cases h : y ∈ Δ
    · exact .inl ⟨h, disjoint_left.mp hcF hy⟩
    · exact .inr h
  have hle := hpc.subset_left_of_subset_union hW hΔ.isOpen_compl (disjoint_left.mpr fun y hy hy'
    => hy' hy.1) hsub ⟨x, hx, hxΔ, disjoint_left.mp hcF hx⟩
  exact hle.trans sdiff_subset

/-- A line of a region's frontier inside a disc that has no other nodes is a gap of a cell inside
the disc. -/
theorem gap_in_disc [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {O C F Δ : Set S} {u v :
  S} (hO : Γ.IsFace O) (hC : IsLineWithEnds C u v) (hCO : C ⊆ O) (hCΔ : C ⊆ Δ) (hΔ : IsClosed Δ)
    (hF : IsClosed F)
    (hnb : ∀ x ∈ Δ \ F, Δ ∈ 𝓝 x) (hN : Δ ∩ Γ.N ⊆ F) (hFN : F ∩ Γ.N = {u, v}) (hFU : F ∩ Γ.U ⊆ Γ.N)
      (huN : u ∈ Γ.N) (hvN : v ∈ Γ.N) : ∃ c, Γ.IsGap c C u v ∧ c ⊆ Δ := by
  have hCN : C ∩ Γ.N = {u, v} := by
    refine Subset.antisymm (fun x hx => hFN ▸ ⟨hN ⟨hCΔ hx.1, hx.2⟩, hx.2⟩) ?_
    rintro x (rfl | rfl)
    · exact ⟨hC.left_mem, huN⟩
    · exact ⟨hC.right_mem, hvN⟩
  have harc : IsArcOf O (Γ.N ∩ O) C := by
    refine ⟨u, v, hC, hCO, ?_⟩
    rw [← hCN]
    ext x
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hCO h.1⟩⟩
  obtain ⟨c, u', v', hG⟩ := arc_face_gap hS h hO harc
  have hG' : Γ.IsGap c C u v := ⟨hG.1, hC, hG.2.2.1, hCN⟩
  obtain ⟨z, hz⟩ := line_inner_nonempty hC
  have hzc : z ∈ c := hG'.mem_cell hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2 (.inr e))
  have hcF : Disjoint c F := disjoint_left.mpr fun x hx hxF => disjoint_left.mp
    (Γ.cell_disjoint_N hG.1) hx (hFU ⟨hxF, Γ.cell_subset_U hG.1 hx⟩)
  exact ⟨c, hG', cell_in_disc hΔ hF hnb hG.1 hcF hzc (hCΔ hz.1)⟩

omit [T2Space S] in
/-- The nodes of a cell in a disc are in the disc, so a cell with two gap ends has just these nodes.
-/
theorem tilde_of_disc {c Δ F : Set S} {u v : S} (hc : c ∈ Γ.C) (hcΔ : c ⊆ Δ) (hΔ : IsClosed Δ)
  (hN : Δ ∩ Γ.N ⊆ F) (hFN : F ∩ Γ.N = {u, v}) (hu : u ∈ tilde c) (hv : v ∈ tilde c) : tilde c
    = {u, v} := by
  refine Subset.antisymm (fun x hx => ?_) ?_
  · have hxN := Γ.tilde_subset_N hc hx
    exact hFN ▸ ⟨hN ⟨closure_minimal hcΔ hΔ hx.1, hxN⟩, hxN⟩
  · rintro x (rfl | rfl)
    · exact hu
    · exact hv

omit [T2Space S] in
theorem Painting.IsGap.left_mem_tilde {c L : Set S} {u v : S} (h : Γ.IsGap c L u v) : u ∈ tilde c :=
  ⟨h.subset_closure h.2.1.left_mem, fun hx => disjoint_left.mp (Γ.cell_disjoint_N h.1) hx
    h.left_mem_N⟩

omit [T2Space S] in
theorem Painting.IsGap.right_mem_tilde {c L : Set S} {u v : S} (h : Γ.IsGap c L u v) : v ∈ tilde c
  :=
  ⟨h.subset_closure h.2.1.right_mem, fun hx => disjoint_left.mp (Γ.cell_disjoint_N h.1) hx
    h.right_mem_N⟩

/-- A disc with a chord of a region on its boundary holds one of the two lines of the frontier, as a
gap of a cell in the disc. -/
theorem side_in_disc [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {r C₁ C₂ F₀ Δ₁ Δ₂ F Δ :
  Set S} {u v : S} (hr : r ∈ Γ.regions) (hC₁ : IsLineWithEnds C₁ u v) (hC₂ : IsLineWithEnds C₂ u v)
    (hu : C₁ ∪ C₂ = closure r \ r) (hF₀ : IsLineWithEnds F₀ u v) (hF₀r : F₀ \ {u, v} ⊆ r)
      (hd₁ : IsClosedDisc Δ₁) (hd₂ : IsClosedDisc Δ₂) (hu' : Δ₁ ∪ Δ₂ = closure r) (hi' : Δ₁ ∩ Δ₂
        = F₀)
    (hb₁ : discBd Δ₁ = C₁ ∪ F₀) (hb₂ : discBd Δ₂ = C₂ ∪ F₀) (hΔ : IsClosedDisc Δ)
      (h1 : F₀ ⊆ discBd Δ) (h2 : discBd Δ ∩ r ⊆ F₀) (hF : IsClosed F) (hnb : ∀ x ∈ Δ \ F, Δ ∈ 𝓝 x)
    (hN : Δ ∩ Γ.N ⊆ F) (hFN : F ∩ Γ.N = {u, v}) (hFU : F ∩ Γ.U ⊆ Γ.N) (huN : u ∈ Γ.N)
      (hvN : v ∈ Γ.N) : ∃ c L, Γ.IsGap c L u v ∧ c ⊆ Δ ∧ L ⊆ closure r \ r := by
  have hO : Γ.IsFace (closure r \ r) := .inl ⟨r, hr, rfl⟩
  have hc₁ : C₁ ⊆ closure r \ r := hu ▸ subset_union_left
  have hc₂ : C₂ ⊆ closure r \ r := hu ▸ subset_union_right
  rcases chord_side hS (h.hopen r hr) hu.symm hF₀ hF₀r hd₁ hd₂ hu' hi' hb₁ hb₂ hΔ h1 h2 with h3 | h3
  · obtain ⟨c, hG, hc⟩ := gap_in_disc hS h hO hC₁ hc₁ (fun x hx => h3 (discBd_subset _
    (hb₁ ▸ .inl hx))) hΔ.isClosed hF hnb hN hFN hFU huN hvN
    exact ⟨c, C₁, hG, hc, hc₁⟩
  · obtain ⟨c, hG, hc⟩ := gap_in_disc hS h hO hC₂ hc₂ (fun x hx => h3 (discBd_subset _
    (hb₂ ▸ .inl hx))) hΔ.isClosed hF hnb hN hFN hFU huN hvN
    exact ⟨c, C₂, hG, hc, hc₂⟩

/-- The hypothesis (8.3) of (11.1). -/
def Hyp83 (Γ : Painting S) : Prop :=
  ∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F → (F ∩ Γ.N).ncard = 2 →
    ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧ Δ ∩ Γ.N ⊆ F
      ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1

/-- The hypothesis (8.5) of (11.1). -/
def Hyp85 (Γ : Painting S) : Prop :=
  ∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.N).ncard = 2 →
    ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard ≤ 1

omit [T2Space S] in
theorem cells_finite (Γ : Painting S) (Δ : Set S) : {c ∈ Γ.C | c ⊆ Δ}.Finite
  := Γ.finite_cells.subset fun _ h => h.1

/-- Claim (2) for two regions, by the hypothesis (8.5). -/
theorem par_regions [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ)
  (h85 : Hyp85 Γ) {r r' : Set S} {u v : S} (hr : r ∈ Γ.regions) (hr' : r' ∈ Γ.regions)
    (hne : r ≠ r')
    (hu : u ∈ closure r \ r) (hv : v ∈ closure r \ r) (hu' : u ∈ closure r' \ r')
      (hv' : v ∈ closure r' \ r') (huN : u ∈ Γ.N) (hvN : v ∈ Γ.N) (huv : u ≠ v) :
    ∃ c L L', Γ.IsGap c L u v ∧ Γ.IsGap c L' u v ∧ L ⊆ closure r \ r ∧ L' ⊆ closure r' \ r'
      ∧ tilde c = {u, v} := by
  have hman := hS.2.2
  obtain ⟨C₁, C₂, hC₁, hC₂, hun, hin⟩ := (h.hreg r hr).2.lines hu hv huv
  obtain ⟨C₁', C₂', hC₁', hC₂', hun', hin'⟩ := (h.hreg r' hr').2.lines hu' hv' huv
  obtain ⟨F₁, Δ₁, Δ₂, hF₁, hF₁r, hF₁N, hF₁U, -, hd₁, hd₂, hu₁, hi₁, hb₁, hb₂⟩
    := chord_of_region hS h hr hC₁ hC₂ hun hin huN hvN huv
  obtain ⟨F₂, Δ₁', Δ₂', hF₂, hF₂r, hF₂N, hF₂U, -, hd₁', hd₂', hu₂, hi₂, hb₁', hb₂'⟩
    := chord_of_region hS h hr' hC₁' hC₂' hun' hin' huN hvN huv
  have hdisj : ∀ x, x ∈ r → x ∈ r' → False := fun x hx hx' => hne (region_eq hr hr' hx hx')
  have hsame : ∀ x ∈ F₂, x ∈ r → x ∈ F₁ := fun x hx hxr => by
    by_cases h3 : x ∈ ({u, v} : Set S)
    · rcases h3 with rfl | rfl
      · exact hF₁.left_mem
      · exact hF₁.right_mem
    · exact (hdisj x hxr (hF₂r ⟨hx, h3⟩)).elim
  have hsame' : ∀ x ∈ F₁, x ∈ r' → x ∈ F₂ := fun x hx hxr => by
    by_cases h3 : x ∈ ({u, v} : Set S)
    · rcases h3 with rfl | rfl
      · exact hF₂.left_mem
      · exact hF₂.right_mem
    · exact (hdisj x (hF₁r ⟨hx, h3⟩) hxr).elim
  have hi : F₁ ∩ F₂ = {u, v} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · by_contra h3
      exact hdisj x (hF₁r ⟨hx.1, h3⟩) (hF₂r ⟨hx.2, h3⟩)
    · rintro x (rfl | rfl)
      · exact ⟨hF₁.left_mem, hF₂.left_mem⟩
      · exact ⟨hF₁.right_mem, hF₂.right_mem⟩
  have hFO : IsOArc (F₁ ∪ F₂) := oArc_of_lines hF₁ hF₂ hi
  have hFN : (F₁ ∪ F₂) ∩ Γ.N = {u, v} := by rw [union_inter_distrib_right, hF₁N, hF₂N, union_self]
  have hUset : (F₁ ∪ F₂) ∩ Γ.U ⊆ {u, v} := by
    rintro x ⟨h3 | h3, h4⟩
    · exact hF₁U ⟨h3, h4⟩
    · exact hF₂U ⟨h3, h4⟩
  have hnode : ({u, v} : Set S) ⊆ Γ.N := by
    rintro x (rfl | rfl)
    · exact huN
    · exact hvN
  have hFU : (F₁ ∪ F₂) ∩ Γ.U ⊆ Γ.N := hUset.trans hnode
  obtain ⟨Δ, hΔ, hb, hN, hcard⟩ := h85 _ hFO hFU (by rw [hFN, ncard_pair huv])
  have hFc : IsClosed (F₁ ∪ F₂) := (GM19.isClosed_of_cuffLine hF₁).union
    (GM19.isClosed_of_cuffLine hF₂)
  have hnb : ∀ x ∈ Δ \ (F₁ ∪ F₂), Δ ∈ 𝓝 x := fun x hx => by
    have hx' : x ∈ discInt Δ := ⟨hx.1, hb ▸ hx.2⟩
    exact Filter.mem_of_superset ((hΔ.isOpen_discInt hman).mem_nhds hx') sdiff_subset
  obtain ⟨c, L, hG, hc, hLO⟩ := side_in_disc hS h hr hC₁ hC₂ hun hF₁ hF₁r hd₁ hd₂ hu₁ hi₁ hb₁ hb₂
    hΔ (hb ▸ subset_union_left)
    (fun x hx => (hb ▸ hx.1 : x ∈ F₁ ∪ F₂).elim id fun h3 => hsame x h3 hx.2) hFc hnb hN hFN hFU
      huN hvN
  obtain ⟨c', L', hG', hc', hLO'⟩ := side_in_disc hS h hr' hC₁' hC₂' hun' hF₂ hF₂r hd₁' hd₂' hu₂
    hi₂ hb₁' hb₂' hΔ (hb ▸ subset_union_right)
    (fun x hx => (hb ▸ hx.1 : x ∈ F₁ ∪ F₂).elim (fun h3 => hsame' x h3 hx.2) id) hFc hnb hN hFN hFU
      huN hvN
  obtain rfl : c = c' := (ncard_le_one (cells_finite Γ Δ)).mp hcard c ⟨hG.1, hc⟩ c' ⟨hG'.1, hc'⟩
  exact ⟨c, L, L', hG, hG', hLO, hLO', tilde_of_disc hG.1 hc hΔ.isClosed hN hFN hG.left_mem_tilde
    hG.right_mem_tilde⟩

/-- Claim (2) for a region and a cuff, by the hypothesis (8.3). -/
theorem par_region_cuff [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ)
  (h83 : Hyp83 Γ) {r Θ : Set S} {u v : S} (hr : r ∈ Γ.regions) (hΘ : Θ ∈ cuffs S)
    (hu : u ∈ closure r \ r) (hv : v ∈ closure r \ r) (hu' : u ∈ Θ) (hv' : v ∈ Θ) (huN : u ∈ Γ.N)
      (hvN : v ∈ Γ.N) (huv : u ≠ v) :
    ∃ c L L', Γ.IsGap c L u v ∧ Γ.IsGap c L' u v ∧ L ⊆ closure r \ r ∧ L' ⊆ Θ ∧ tilde c = {u, v}
      := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hun, hin⟩ := (h.hreg r hr).2.lines hu hv huv
  have hub := cuff_subset hΘ hu'
  have hvb := cuff_subset hΘ hv'
  obtain ⟨F, Δ₁, Δ₂, Δ, hF, hFr, hFN, hd₁, hd₂, hu₁, hi₁, hb₁, hb₂, hΔ, h1, h2, hN, hcard, hnb, -⟩
    :=
    exists_chord_disc hS (fun r hr => (h.hreg r hr).1) (fun r hr => (h.hreg r hr).2) h83 hr hC₁ hC₂
      hun hin huN hvN huv hub hvb
  have hrU : ∀ x ∈ r, x ∉ Γ.U := fun x hx => (arcComponentsIn_subset hr hx).2
  have hFend : ∀ x ∈ F, x ∉ r → x = u ∨ x = v := fun x hx h => by_contra fun h3 => h (hFr ⟨hx, h3⟩)
  have hFU : F ∩ Γ.U ⊆ Γ.N := fun x hx => hFN.ge (hFend x hx.1 fun h3 => hrU x h3 hx.2) |>.2
  have hFb : F ∩ bd S = {u, v} := by
    refine Subset.antisymm (fun x hx => hFend x hx.1 fun h3 => hrU x h3 (Γ.bd_subset hx.2)) ?_
    rintro x (rfl | rfl)
    · exact ⟨hF.left_mem, hub⟩
    · exact ⟨hF.right_mem, hvb⟩
  have hFc : IsClosed F := GM19.isClosed_of_cuffLine hF
  obtain ⟨c, L, hG, hc, hLO⟩ := side_in_disc hS h hr hC₁ hC₂ hun hF hFr hd₁ hd₂ hu₁ hi₁ hb₁ hb₂ hΔ
    h1
    (fun x hx => (h2 hx.1).elim id fun hb => (hrU x hx.2 (Γ.bd_subset hb)).elim) hFc hnb hN hFN hFU
      huN hvN
  obtain ⟨I, I', Θ', hΘ', hI, -, hU, -, hFI, -, -, -⟩ := arc_disc_data hS hF hFb hΔ h1 h2
  have hIΘ' : I ⊆ Θ' := hU ▸ subset_union_left
  obtain rfl : Θ' = Θ := cuff_eq hΘ' hΘ (hIΘ' hI.left_mem) hu'
  obtain ⟨c', hG', hc'⟩ := gap_in_disc hS h (.inr hΘ') hI hIΘ' (fun x hx => discBd_subset _
    (hFI ▸ .inr hx)) hΔ.isClosed hFc hnb hN hFN hFU huN hvN
  obtain rfl : c = c' := (ncard_le_one (cells_finite Γ Δ)).mp hcard.le c ⟨hG.1, hc⟩ c' ⟨hG'.1, hc'⟩
  exact ⟨c, L, I, hG, hG', hLO, hIΘ', tilde_of_disc hG.1 hc hΔ.isClosed hN hFN hG.left_mem_tilde
    hG.right_mem_tilde⟩

/-- **Claim (2) of the proof of (11.1)**, on faces. -/
theorem par_faces [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) (h83 : Hyp83 Γ)
  (h85 : Hyp85 Γ) {O O' : Set S} {u v : S} (hO : Γ.IsFace O) (hO' : Γ.IsFace O') (hne : O ≠ O')
    (hu : u ∈ O) (hv : v ∈ O) (hu' : u ∈ O') (hv' : v ∈ O') (huN : u ∈ Γ.N) (hvN : v ∈ Γ.N)
      (huv : u ≠ v) :
    ∃ c L L', Γ.IsGap c L u v ∧ Γ.IsGap c L' u v ∧ L ⊆ O ∧ L' ⊆ O' ∧ tilde c = {u, v} := by
  rcases hO with ⟨r, hr, rfl⟩ | hO <;> rcases hO' with ⟨r', hr', rfl⟩ | hO'
  · exact par_regions hS h h85 hr hr' (fun e => hne (by rw [e])) hu hv hu' hv' huN hvN huv
  · exact par_region_cuff hS h h83 hr hO' hu hv hu' hv' huN hvN huv
  · obtain ⟨c, L, L', h1, h2, h3, h4, h5⟩ :=
      par_region_cuff hS h h83 hr' hO hu' hv' hu hv huN hvN huv
    exact ⟨c, L', L, h2, h1, h4, h3, h5⟩
  · exact absurd (cuff_eq hO hO' hu hu') hne

end GraphMinor.GM17
