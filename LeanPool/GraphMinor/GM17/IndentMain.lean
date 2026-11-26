/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.IndentRegion
public import LeanPool.GraphMinor.GM17.BorderCells

/-!
# Indenting a border cell

We prove `indentedBorderPainting : IndentedBorderPaintingStatement`, the painting behind the proofs
of (9.3) and (9.4) of Graph Minors
XVII, pages 184 and 185. In both proofs a disc `D` holds a border cell `c₀`, and `D` has a third
node `n` on its boundary, and `indented_of_disc`
then gives the new painting.

For (9.3) the region `r` next to `c₀` has an internal node `n₀`. The paper gets this from (8.3) and
the absence of an internal cell with `cTilde₀ ⊆ cTilde`
(`exists_internal_node`). Then `D` is `cBar₀` together with the part of `rBar` between the side of
`c₀` and two chords through `n₀`.

For (9.4) there is an internal cell `c₃` with `cTilde₃ = {n₁, n₂, n₃}`. The disc in the paper's
sentence "Let $\Delta \subseteq \Sigma$ be the disc bounded by $F_1 \cup F_2 \cup (c_0 \cap
\Theta)$" needs
`c₃` to face `c₀`. We show this: the region `r` on the side of `c₃` between `n₁` and `n₂` has the
side of `c₀` as the rest of its frontier
(`region_between`), by (8.3) and (8.8). So `D = cBar₀ ∪ rBar ∪ cBar₃`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface Painting

variable {S : Type} [TopologicalSpace S]

theorem cell_disjoint_closure {Γ : Painting S} {c d : Set S} (hc : c ∈ Γ.C)
  (hd : d ∈ Γ.C) (hne : c ≠ d) : Disjoint c (closure d) :=
  disjoint_left.mpr fun x hx hx' => by
    by_cases h : x ∈ d
    · exact disjoint_left.mp (arcComponentsIn_disjoint hc hd hne) hx h
    · exact disjoint_left.mp (Γ.cell_disjoint_N hc) hx (Γ.tilde_subset_N hd ⟨hx', h⟩)

theorem line_preconnected {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) : IsPreconnected L :=
  GraphMinor.Surface.IsLineWithEnds.isPreconnected hL

/-- What a border cell looks like. -/
theorem border_data [T2Space S] (hS : IsSurface S) {Γ : Painting S} {Θ c₀ : Set S} {n₁ n₂ : S}
  (hΘ : Θ ∈ cuffs S) (hc₀ : c₀ ∈ Γ.C)
    (hc₀Θ : (c₀ ∩ Θ).Nonempty) (ht : tilde c₀ = {n₁, n₂}) :
    ∃ L₀ n', IsLineWithEnds (closure c₀ ∩ bd S) n₁ n₂ ∧ Γ.IsSide c₀ L₀ n₁ n₂ ∧ discBd (closure c₀)
      = (closure c₀ ∩ bd S) ∪ L₀ ∧
      (closure c₀ ∩ bd S) ∩ L₀ = {n₁, n₂} ∧ n₁ ∈ bd S ∧ n₂ ∈ bd S ∧ closure c₀ ∩ bd S ⊆ Θ ∧ n' ∈
        (closure c₀ ∩ bd S) \ {n₁, n₂} ∧ n' ∈ c₀ ∩ Θ := by
  obtain ⟨w, hwc, hwΘ⟩ := hc₀Θ
  have hΘb : Θ ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hbd : (c₀ ∩ bd S).Nonempty := ⟨w, hwc, hΘb hwΘ⟩
  obtain ⟨u, v, O, ht', hB, hO, hb, hi, hu, hv, -⟩ := Painting.border_side hS hc₀ hbd
  have hmemA : w ∈ closure c₀ ∩ bd S := ⟨subset_closure hwc, hΘb hwΘ⟩
  have hsub : ∀ {a b : S}, IsLineWithEnds (closure c₀ ∩ bd S) a b → closure c₀ ∩ bd S ⊆ Θ := fun hL
    => by
    obtain ⟨x, -, rfl⟩ := hΘ
    rw [connectedComponentIn_eq hwΘ]
    exact (line_preconnected hL).subset_connectedComponentIn hmemA inter_subset_right
  have hnot : w ∉ ({n₁, n₂} : Set S) := fun h => (ht ▸ h : w ∈ tilde c₀).2 hwc
  rw [ht] at ht'
  rcases (pair_eq_pair_iff.mp ht') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨O, w, hB, hO, hb, hi, hu, hv, hsub hB, ⟨hmemA, hnot⟩, hwc, hwΘ⟩
  · exact ⟨O, w, hB.symm, hO.symm, hb, by rw [hi, pair_comm], hv, hu, hsub hB, ⟨hmemA, hnot⟩,
      hwc, hwΘ⟩

/-- A disc `P` along the side of a border cell gives the painting. -/
theorem indented_of_glue [ConnectedSpace S] (hS : IsSurface S) (Γ : Painting S) {P L₀ G Θ c₀ : Set
  S} {n n₁ n₂ n' : S} {R : Set (Set S)}
    (hc₀ : c₀ ∈ Γ.C) (ht : tilde c₀ = {n₁, n₂}) (hA : IsLineWithEnds (closure c₀ ∩ bd S) n₁ n₂)
      (hL₀ : IsLineWithEnds L₀ n₁ n₂)
    (hb₀ : discBd (closure c₀) = (closure c₀ ∩ bd S) ∪ L₀) (hi₀ : (closure c₀ ∩ bd S) ∩ L₀
      = {n₁, n₂})
    (hP : IsClosedDisc P) (hG : IsLineWithEnds G n₁ n₂) (hbP : discBd P = L₀ ∪ G) (hL₀G : L₀ ∩ G
      = {n₁, n₂}) (hPc : P ∩ closure c₀ = L₀)
    (hPb : P ∩ bd S ⊆ {n₁, n₂}) (hPN : P ∩ Γ.N = {n₁, n₂, n}) (hnG : n ∈ G \ {n₁, n₂})
      (hnb : n ∉ bd S)
    (hAG : (closure c₀ ∩ bd S) ∩ G = {n₁, n₂}) (hn'A : n' ∈ (closure c₀ ∩ bd S) \ {n₁, n₂})
      (hn'c : n' ∈ c₀ ∩ Θ) (hAΘ : closure c₀ ∩ bd S ⊆ Θ)
    (hc₀R : c₀ ∈ R) (hRc : ∀ c ∈ Γ.C, c ∈ R → c = c₀ ∨ c ⊆ P) (hRd : ∀ c ∈ Γ.C, c ∉ R
      → Disjoint c P) :
    ∃ Γ' : Painting S, IsIndentedBorderPainting Γ Θ c₀ n₁ n₂ n R Γ' := by
  have ht2 : T2Space S := hS.2.1
  set A := closure c₀ ∩ bd S with hAdef
  have hdc := Γ.isClosedDisc_closure_cell hc₀
  have hL₀b : L₀ ⊆ discBd (closure c₀) := fun x hx => hb₀ ▸ .inr hx
  obtain ⟨hD, hbD⟩ := disc_union (closure c₀) P L₀ n₁ n₂ hdc hP hL₀ (by rw [inter_comm, hPc]) hL₀b
    (fun x hx => hbP ▸ .inl hx)
  have hend : ∀ {x}, x ∈ ({n₁, n₂} : Set S) → x ∈ A ∧ x ∈ L₀ ∧ x ∈ G := fun {x} hx => by
    have h1 : x ∈ A ∩ L₀ := hi₀.symm.subset hx
    have h2 : x ∈ L₀ ∩ G := hL₀G.symm.subset hx
    exact ⟨h1.1, h1.2, h2.2⟩
  have hbD' : discBd (closure c₀ ∪ P) = A ∪ G := by
    rw [hbD, hb₀, hbP]
    ext x
    constructor
    · rintro ⟨((h | h) | (h | h)), hx⟩
      · exact .inl h
      · exact .inl (hend (by_contra fun h3 => hx ⟨h, h3⟩)).1
      · exact .inl (hend (by_contra fun h3 => hx ⟨h, h3⟩)).1
      · exact .inr h
    · rintro (h | h)
      · refine ⟨.inl (.inl h), fun h3 => h3.2 ?_⟩
        exact hi₀ ▸ ⟨h, h3.1⟩
      · refine ⟨.inr (.inr h), fun h3 => h3.2 ?_⟩
        exact hL₀G ▸ ⟨h3.1, h⟩
  have hclN : closure c₀ ∩ Γ.N = {n₁, n₂} := by
    rw [← ht]
    ext x
    constructor
    · rintro ⟨hx, hxN⟩
      exact ⟨hx, fun h => disjoint_left.mp (Γ.cell_disjoint_N hc₀) h hxN⟩
    · intro hx
      exact ⟨hx.1, Γ.tilde_subset_N hc₀ hx⟩
  refine indented_of_disc hS Γ hD hA hG hbD' hAG ?_ ?_ hnG hnb hn'A hn'c hAΘ ?_ ?_
  · refine Subset.antisymm ?_ fun x hx => ⟨.inl hx.1, hx.2⟩
    rintro x ⟨(h | h), hb⟩
    · exact ⟨h, hb⟩
    · exact (hend (hPb ⟨h, hb⟩)).1
  · rw [union_inter_distrib_right, hclN, hPN]
    ext x
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    tauto
  · intro c hc hcR
    rcases hRc c hc hcR with rfl | h
    · exact subset_closure.trans subset_union_left
    · exact h.trans subset_union_right
  · intro c hc hcR
    have hne : c ≠ c₀ := fun h => hcR (h ▸ hc₀R)
    exact disjoint_union_right.mpr ⟨cell_disjoint_closure hc hc₀ hne, hRd c hc hcR⟩

private theorem nodes_of_region_cell_union
    {S : Type}
    [TopologicalSpace S]
    (Γ : Painting S)
    {c₀ : Set S}
    {c₃ : Set S}
    {n₁ : S}
    {n₂ : S}
    {n₃ : S}
    (hc₃ : c₃ ∈ Γ.C)
    (ht₃ : tilde c₃ = {n₁, n₂, n₃})
    (L₀ : Set S)
    (hs₀ : Γ.IsSide c₀ L₀ n₁ n₂)
    (L₃ : Set S)
    (hg₃ : Γ.IsGap c₃ L₃ n₁ n₂)
    (r : Set S)
    (hrU : ∀ x ∈ r, x ∉ Γ.U)
    (hfr' : ∀ x ∈ closure r, x ∉ r → x ∈ L₃ ∨ x ∈ L₀)
    (hc₃out : ∀ x ∈ closure c₃, x ∉ c₃ → x = n₁ ∨ x = n₂ ∨ x = n₃) :
    (closure r ∪ closure c₃) ∩ Γ.N = {n₁, n₂, n₃} := by
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨(h | h), hxN⟩
    · have hxr : x ∉ r := fun h3 => hrU x h3 (Γ.N_subset hxN)
      rcases hfr' x h hxr with h3 | h3
      · rcases (hg₃.2.2.2.le ⟨h3, hxN⟩) with h4 | h4
        · exact .inl h4
        · exact .inr (.inl h4)
      · rcases (hs₀.1.2.2.2.le ⟨h3, hxN⟩) with h4 | h4
        · exact .inl h4
        · exact .inr (.inl h4)
    · have hx3 : x ∉ c₃ := fun h3 => disjoint_left.mp (Γ.cell_disjoint_N hc₃) h3 hxN
      exact hc₃out x h hx3
  · rw [← ht₃]
    intro x hx
    exact ⟨.inr hx.1, Γ.tilde_subset_N hc₃ hx⟩

private theorem cuff_arc_subset_side
    {S : Type}
    [TopologicalSpace S]
    [ConnectedSpace S]
    (hS : IsSurface S)
    (Γ : Painting S)
    (h2 : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b)
    {c₀ : Set S}
    {n₁ : S}
    {n₂ : S}
    [T2Space S]
    [CompactSpace S]
    (hreg' : ∀ r ∈ Γ.regions, IsOpen r)
    (L₀ : Set S)
    (hb₀ : discBd (closure c₀) = closure c₀ ∩ bd S ∪ L₀)
    (L₃ : Set S)
    (r : Set S)
    (hr : r ∈ Γ.regions)
    (C₂ : Set S)
    (hu : L₃ ∪ C₂ = closure r \ r)
    (Δ : Set S)
    (hsd : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ)
    (hC₂Δ : C₂ ⊆ Δ)
    (hC₂N : ∀ x ∈ C₂, x ∈ Γ.N → x = n₁ ∨ x = n₂)
    (huniq : ∀ c ∈ Γ.C, c ⊆ Δ → c = c₀)
    (y : S)
    (hy : y ∈ C₂ \ {n₁, n₂}) :
    y ∈ L₀ := by
  have hyC : y ∈ closure r \ r := hu ▸ .inr hy.1
  have hyN : y ∉ Γ.N := fun h => hy.2 (hC₂N y hy.1 h)
  obtain ⟨L, ⟨c'', u, v, hL, hLr⟩, hyL⟩ := frontier_region hS hreg' h2 hr hyC.1 hyC.2 hyN
  have hyu : y ≠ u := fun e => hyN (hL.1.2.2.2.ge (.inl e) |>.2)
  have hyv : y ≠ v := fun e => hyN (hL.1.2.2.2.ge (.inr e) |>.2)
  have hyc : y ∈ c'' := hL.1.mem_cell hyL hyu hyv
  have hc'' := hL.1.1
  have hec := huniq c'' hc'' ((hsd c'' hc'').resolve_right fun h => h hyc (hC₂Δ hy.1))
  rw [hec] at hL
  have hyb : y ∉ bd S := fun h => disjoint_left.mp hL.2 ⟨hyL, by
    rintro (e | e)
    · exact hyu e
    · exact hyv e⟩ h
  have h5 : y ∈ (closure c₀ ∩ bd S) ∪ L₀ := hb₀ ▸ hL.1.2.2.1 hyL
  rcases h5 with h5 | h5
  · exact absurd h5.2 hyb
  · exact h5

private theorem inner_piece_stays_inside_cut_disc
    {S : Type}
    [TopologicalSpace S]
    (Γ : Painting S)
    {c₃ : Set S}
    {n₁ : S}
    {n₂ : S}
    {n₃ : S}
    (hc₃ : c₃ ∈ Γ.C)
    (hn₃ : n₃ ∈ Γ.N \ bd S)
    [T2Space S]
    (hn₃t : n₃ ∈ tilde c₃)
    (hn₃₁ : n₃ ≠ n₁)
    (hn₃₂ : n₃ ≠ n₂)
    (L₃ : Set S)
    (hg₃ : Γ.IsGap c₃ L₃ n₁ n₂)
    (hL₃ : IsLineWithEnds L₃ n₁ n₂)
    (F : Set S)
    (Δ₁ : Set S)
    (Δ₂ : Set S)
    (Δ : Set S)
    (hFN : F ∩ Γ.N = {n₁, n₂})
    (hb₁ : discBd Δ₁ = L₃ ∪ F)
    (hΔ : IsClosedDisc Δ)
    (h3 : Δ ∩ Γ.N ⊆ F)
    (hside : Δ₁ ⊆ Δ ∨ Δ₂ ⊆ Δ)
    (hsd : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ) :
    Δ₂ ⊆ Δ := by
  rcases hside with h | h
  · exfalso
    obtain ⟨z, hz⟩ := line_inner_nonempty hL₃
    have hz₁ : z ∈ c₃ := hg₃.mem_cell hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2 (.inr e))
    have hzΔ : z ∈ Δ := h (discBd_subset _ (hb₁ ▸ .inl hz.1))
    have hsubc : c₃ ⊆ Δ := (hsd c₃ hc₃).resolve_right fun h5 => h5 hz₁ hzΔ
    have hn₃Δ : n₃ ∈ Δ := closure_minimal hsubc hΔ.isClosed hn₃t.1
    have h5 : n₃ ∈ F ∩ Γ.N := ⟨h3 ⟨hn₃Δ, hn₃.1⟩, hn₃.1⟩
    rw [hFN] at h5
    rcases h5 with h5 | h5
    · exact hn₃₁ h5
    · exact hn₃₂ h5
  · exact h

private theorem joined_region_has_only_boundary_endpoints
    {S : Type}
    [TopologicalSpace S]
    (Γ : Painting S)
    {c₃ : Set S}
    {n₁ : S}
    {n₂ : S}
    {n₃ : S}
    (hint : ¬(c₃ ∩ bd S).Nonempty)
    (hn₃ : n₃ ∈ Γ.N \ bd S)
    (L₀ : Set S)
    (L₃ : Set S)
    (r : Set S)
    (hrb : ∀ x ∈ r, x ∉ bd S)
    (hfr' : ∀ x ∈ closure r, x ∉ r → x ∈ L₃ ∨ x ∈ L₀)
    (hs₀' : ∀ x ∈ L₀, x ∈ bd S → x ∈ ({n₁, n₂} : Set S))
    (hs₃' : ∀ x ∈ L₃, x ∈ bd S → x ∈ ({n₁, n₂} : Set S))
    (hc₃out : ∀ x ∈ closure c₃, x ∉ c₃ → x = n₁ ∨ x = n₂ ∨ x = n₃) :
    (closure r ∪ closure c₃) ∩ bd S ⊆ {n₁, n₂} := by
  rintro x ⟨(h | h), hb⟩
  · rcases hfr' x h (hrb x · hb) with h3 | h3
    · exact hs₃' x h3 hb
    · exact hs₀' x h3 hb
  · by_cases hx : x ∈ c₃
    · exact absurd ⟨x, hx, hb⟩ hint
    · rcases hc₃out x h hx with h3 | h3 | h3
      · exact .inl h3
      · exact .inr h3
      · exact absurd (h3 ▸ hb) hn₃.2

/-- Part (B) of the statement, with the hypotheses that it uses. -/
theorem indented_of_cell [ConnectedSpace S] (hS : IsSurface S) (Γ : Painting S)
    (hreg : ∀ r ∈ Γ.regions, IsOpenDisc r) (hfr : ∀ r ∈ Γ.regions, IsOArc (closure r \ r))
    (h83 : ∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F → (F ∩ Γ.N).ncard = 2 →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧ Δ ∩ Γ.N ⊆ F
        ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1)
    (h2 : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b)
    (h88 : ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ → tilde c₁ ⊆ tilde c₂ → (c₁ ∩ bd S).Nonempty ∧
      (tilde c₂).ncard = 3)
    {Θ c₀ c₃ : Set S} {n₁ n₂ n₃ : S} (hΘ : Θ ∈ cuffs S) (hc₀ : c₀ ∈ Γ.C) (hc₀Θ : (c₀ ∩ Θ).Nonempty)
      (hne : n₁ ≠ n₂) (ht₀ : tilde c₀ = {n₁, n₂})
    (hc₃ : c₃ ∈ Γ.C) (hint : ¬ (c₃ ∩ bd S).Nonempty) (hn₃ : n₃ ∈ Γ.N \ bd S) (ht₃ : tilde c₃
      = {n₁, n₂, n₃}) :
    ∃ Γ' : Painting S, IsIndentedBorderPainting Γ Θ c₀ n₁ n₂ n₃ {c₀, c₃} Γ' := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hreg' : ∀ r ∈ Γ.regions, IsOpen r := fun r hr => (hreg r hr).1
  obtain ⟨L₀, n', hA, hs₀, hb₀, hi₀, hn₁b, hn₂b, hAΘ, hn'A, hn'c⟩ := border_data hS hΘ hc₀ hc₀Θ ht₀
  have hn₁t : n₁ ∈ tilde c₃ := ht₃ ▸ .inl rfl
  have hn₂t : n₂ ∈ tilde c₃ := ht₃ ▸ .inr (.inl rfl)
  have hn₃t : n₃ ∈ tilde c₃ := ht₃ ▸ .inr (.inr rfl)
  have hn₁N : n₁ ∈ Γ.N := Γ.tilde_subset_N hc₃ hn₁t
  have hn₂N : n₂ ∈ Γ.N := Γ.tilde_subset_N hc₃ hn₂t
  have hn₃₁ : n₃ ≠ n₁ := fun h => hn₃.2 (h ▸ hn₁b)
  have hn₃₂ : n₃ ≠ n₂ := fun h => hn₃.2 (h ▸ hn₂b)
  obtain ⟨L₃, hg₃⟩ := exists_gap_pair hc₃ hn₁t hn₂t hne
  have hs₃ : Γ.IsSide c₃ L₃ n₁ n₂ := isSide_of_internal hg₃ hint
  have hL₃ : IsLineWithEnds L₃ n₁ n₂ := hg₃.2.1
  have hL₀ : IsLineWithEnds L₀ n₁ n₂ := hs₀.1.2.1
  have hc₀₃ : c₀ ≠ c₃ := fun h => by
    obtain ⟨w, hw, hw'⟩ := (⟨n', hn'c.1, hn'A.1.2⟩ : (c₀ ∩ bd S).Nonempty)
    exact hint ⟨w, h ▸ hw, hw'⟩
  obtain ⟨St, γ, r, -, -, -, -, -, -, -, hr, -, hL₃r, -⟩ := side_strip hS hreg' hs₃ (A
    := ∅) isClosed_empty (by simp)
  have hrU : ∀ x ∈ r, x ∉ Γ.U := fun x hx => (arcComponentsIn_subset hr hx).2
  have hrb : ∀ x ∈ r, x ∉ bd S := fun x hx h => hrU x hx (Γ.bd_subset h)
  have hL₃C : L₃ ⊆ closure r \ r := fun x hx =>
    ⟨hL₃r hx, fun h => disjoint_left.mp (region_disjoint_closure hr hc₃) h (hg₃.subset_closure hx)⟩
  obtain ⟨C₂, hC₂, hu, hi⟩ := oarc_split (hfr r hr) hL₃ hL₃C
  obtain ⟨hdR, hbR⟩ := region_disc hS hreg hr (hfr r hr)
  obtain ⟨F, Δ₁, Δ₂, Δ, hF, hFr, hFN, -, -, -, -, hb₁, hb₂, hΔ, h1, h2', h3, h4, -, hside⟩ :=
    exists_chord_disc hS hreg hfr h83 hr hL₃ hC₂ hu hi hn₁N hn₂N hne hn₁b hn₂b
  have hFb : F ∩ bd S = {n₁, n₂} := by
    refine Subset.antisymm (fun x hx => by_contra fun h => hrb x (hFr ⟨hx.1, h⟩) hx.2) ?_
    rintro x (rfl | rfl)
    · exact ⟨hF.left_mem, hn₁b⟩
    · exact ⟨hF.right_mem, hn₂b⟩
  have hnorm : Γ.IsNormal F := fun x hx => by
    by_contra h
    have h3' : x ∈ ({n₁, n₂} : Set S) := by_contra fun h4 => hrU x (hFr ⟨hx.1, h4⟩) hx.2
    exact h (hFN.symm.subset h3').2
  obtain ⟨I, -, -, -, hI, -, -, -, -, -, hmeet, hnb⟩ := arc_disc_data hS hF hFb hΔ h1 h2'
  have hsd : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ := fun c hc => cell_side hc hnorm hΔ hnb
  have hsub₂ : Δ₂ ⊆ Δ := by
    exact inner_piece_stays_inside_cut_disc (S := S) Γ (c₃ := c₃) (n₁ := n₁) (n₂ := n₂) (n₃ := n₃)
      hc₃ hn₃ hn₃t hn₃₁ hn₃₂ L₃ hg₃ hL₃ F Δ₁ Δ₂ Δ hFN hb₁ hΔ h3 hside hsd
  have hC₂Δ : C₂ ⊆ Δ := fun x hx => hsub₂ (discBd_subset _ (hb₂ ▸ .inl hx))
  have hC₂N : ∀ x ∈ C₂, x ∈ Γ.N → x = n₁ ∨ x = n₂ := fun x hx hxN => hFN.subset ⟨h3 ⟨hC₂Δ hx, hxN⟩,
    hxN⟩
  have hIb : I ⊆ bd S := fun x hx => (hmeet.symm.subset hx).2
  have hIΔ : I ⊆ Δ := fun x hx => (hmeet.symm.subset hx).1
  obtain ⟨c', hc', hc'Δ, hc'b, -, -⟩ := exists_border_cell hI hIb hIΔ hn₁N hsd
  have htc' : tilde c' ⊆ {n₁, n₂} := fun x hx => by
    have hxN := Γ.tilde_subset_N hc' hx
    exact hFN ▸ (⟨h3 ⟨closure_minimal hc'Δ hΔ.isClosed hx.1, hxN⟩, hxN⟩ : x ∈ F ∩ Γ.N)
  have hc'c₀ : c' = c₀ := by
    by_contra hcne
    have h5 := (h88 c' hc' c₀ hc₀ hcne (ht₀ ▸ htc')).2
    rw [ht₀, ncard_pair hne] at h5
    omega
  have huniq : ∀ c ∈ Γ.C, c ⊆ Δ → c = c₀ := by
    obtain ⟨a, ha⟩ := ncard_eq_one.mp h4
    have hm : c₀ ∈ {c ∈ Γ.C | c ⊆ Δ} := ⟨hc₀, hc'c₀ ▸ hc'Δ⟩
    rw [ha] at hm
    intro c hc hcΔ
    have hm' : c ∈ {c ∈ Γ.C | c ⊆ Δ} := ⟨hc, hcΔ⟩
    rw [ha] at hm'
    exact hm'.trans hm.symm
  have hC₂L₀ : C₂ \ {n₁, n₂} ⊆ L₀ := fun y hy => by
    exact cuff_arc_subset_side (S := S) hS Γ h2 (c₀ := c₀) (n₁ := n₁) (n₂ := n₂) hreg' L₀ hb₀ L₃ r
      hr C₂ hu Δ hsd hC₂Δ hC₂N huniq y hy
  have hclosed : ∀ {L : Set S} {a b : S}, IsLineWithEnds L a b → IsClosed L := fun hL
    => GM19.isClosed_of_cuffLine hL
  have hC₂sub : C₂ ⊆ L₀ := hC₂.subset_closure_diff.trans (closure_minimal hC₂L₀ (hclosed hL₀))
  obtain ⟨y, hy⟩ := line_inner_nonempty hC₂
  have hyL₀ : y ∈ L₀ := hC₂L₀ hy
  obtain ⟨St', γ', r₀, -, -, -, -, -, -, -, hr₀, hsubSt, hL₀r, hnbSt⟩ := side_strip hS hreg' hs₀ (A
    := ∅) isClosed_empty (by simp)
  have hrr : r = r₀ := region_of_strip hc₀ (fun x hx => hs₀.1.subset_closure hx) hsubSt hr₀ hr
    (hnbSt y hyL₀ (fun e => hy.2 (.inl e)) (fun e => hy.2 (.inr e))) ((hu ▸ .inr hy.1 : y ∈ closure
      r \ r).1)
  rw [← hrr] at hL₀r
  have hL₀C : L₀ \ {n₁, n₂} ⊆ C₂ := fun w hw => by
    have hwc := hs₀.1.mem_cell hw.1 (fun e => hw.2 (.inl e)) (fun e => hw.2 (.inr e))
    have hwC : w ∈ closure r \ r :=
      ⟨hL₀r hw.1, fun h => disjoint_left.mp (region_disjoint_closure hr hc₀) h (subset_closure hwc)⟩
    rw [← hu] at hwC
    rcases hwC with h5 | h5
    · have h6 := hg₃.mem_cell h5 (fun e => hw.2 (.inl e)) (fun e => hw.2 (.inr e))
      exact absurd h6 (disjoint_left.mp (arcComponentsIn_disjoint hc₀ hc₃ hc₀₃) hwc)
    · exact h5
  have hEq : C₂ = L₀ := Subset.antisymm hC₂sub (hL₀.subset_closure_diff.trans (closure_minimal hL₀C
    (hclosed hC₂)))
  rw [hEq] at hu hi
  have hinn₃ : ∀ x ∈ L₃, x ∉ ({n₁, n₂} : Set S) → x ∈ c₃ := fun x hx h =>
    hg₃.mem_cell hx (fun e => h (.inl e)) (fun e => h (.inr e))
  have hinn₀ : ∀ x ∈ L₀, x ∉ ({n₁, n₂} : Set S) → x ∈ c₀ := fun x hx h =>
    hs₀.1.mem_cell hx (fun e => h (.inl e)) (fun e => h (.inr e))
  have hend₃ : ∀ {x}, x ∈ ({n₁, n₂} : Set S) → x ∈ L₃ ∧ x ∈ L₀ := fun {x} hx => hi.symm.subset hx
  have hfr' : ∀ x ∈ closure r, x ∉ r → x ∈ L₃ ∨ x ∈ L₀ := fun x hx h => hu.symm.subset ⟨hx, h⟩
  have hcc : ∀ x ∈ closure c₀, x ∈ closure c₃ → x ∈ ({n₁, n₂} : Set S) := fun x hx hx' => by
    by_cases h : x ∈ c₀
    · exact absurd hx' (disjoint_left.mp (cell_disjoint_closure hc₀ hc₃ hc₀₃) h)
    · exact ht₀ ▸ (⟨hx, h⟩ : x ∈ tilde c₀)
  have hL₀cl : ∀ x ∈ L₀, x ∈ closure c₀ := fun x hx => hs₀.1.subset_closure hx
  have hL₃cl : ∀ x ∈ L₃, x ∈ closure c₃ := fun x hx => hg₃.subset_closure hx
  have hrnot : ∀ x ∈ closure c₃, x ∉ r := fun x hx h => disjoint_left.mp
    (region_disjoint_closure hr hc₃) h hx
  have hrnot₀ : ∀ x ∈ closure c₀, x ∉ r := fun x hx h => disjoint_left.mp
    (region_disjoint_closure hr hc₀) h hx
  have hrc₃ : closure r ∩ closure c₃ = L₃ := by
    refine Subset.antisymm ?_ fun x hx => ⟨hL₃r hx, hL₃cl x hx⟩
    rintro x ⟨hx, hx'⟩
    rcases hfr' x hx (hrnot x hx') with h | h
    · exact h
    · exact (hend₃ (hcc x (hL₀cl x h) hx')).1
  have hrc₀ : closure r ∩ closure c₀ = L₀ := by
    refine Subset.antisymm ?_ fun x hx => ⟨hL₀r hx, hL₀cl x hx⟩
    rintro x ⟨hx, hx'⟩
    rcases hfr' x hx (hrnot₀ x hx') with h | h
    · exact (hend₃ (hcc x hx' (hL₃cl x h))).2
    · exact h
  have hd₃ := Γ.isClosedDisc_closure_cell hc₃
  obtain ⟨G, hG, hu₃, hi₃⟩ := oarc_split hd₃.isOArc_discBd hL₃ hg₃.2.2.1
  have hGc : ∀ x ∈ G, x ∈ closure c₃ := fun x hx => discBd_subset _ (hu₃ ▸ .inr hx)
  obtain ⟨hP, hbP⟩ := disc_union (closure r) (closure c₃) L₃ n₁ n₂ hdR hd₃ hL₃ hrc₃
    (hbR ▸ hL₃C) hg₃.2.2.1
  have hbP' : discBd (closure r ∪ closure c₃) = L₀ ∪ G := by
    rw [hbP, hbR, ← hu₃, ← hu]
    ext x
    constructor
    · rintro ⟨((h | h) | (h | h)), hx⟩
      · exact .inl (hend₃ (by_contra fun h3 => hx ⟨h, h3⟩)).2
      · exact .inl h
      · exact .inl (hend₃ (by_contra fun h3 => hx ⟨h, h3⟩)).2
      · exact .inr h
    · rintro (h | h)
      · exact ⟨.inl (.inr h), fun h3 => h3.2 (hi ▸ ⟨h3.1, h⟩)⟩
      · exact ⟨.inr (.inr h), fun h3 => h3.2 (hi₃ ▸ ⟨h3.1, h⟩)⟩
  have hGend : ∀ {x}, x ∈ ({n₁, n₂} : Set S) → x ∈ G := fun {x} hx => (hi₃.symm.subset hx).2
  have hL₀G : L₀ ∩ G = {n₁, n₂} := by
    refine Subset.antisymm (fun x hx => hcc x (hL₀cl x hx.1) (hGc x hx.2)) fun x hx
      => ⟨(hend₃ hx).2, hGend hx⟩
  have hPc : (closure r ∪ closure c₃) ∩ closure c₀ = L₀ := by
    refine Subset.antisymm ?_ fun x hx => ⟨.inl (hL₀r hx), hL₀cl x hx⟩
    rintro x ⟨(h | h), hx⟩
    · exact hrc₀ ▸ ⟨h, hx⟩
    · exact (hend₃ (hcc x hx h)).2
  have hs₀' : ∀ x ∈ L₀, x ∈ bd S → x ∈ ({n₁, n₂} : Set S) := fun x hx hb =>
    by_contra fun h => disjoint_left.mp hs₀.2 ⟨hx, h⟩ hb
  have hs₃' : ∀ x ∈ L₃, x ∈ bd S → x ∈ ({n₁, n₂} : Set S) := fun x hx hb =>
    by_contra fun h => disjoint_left.mp hs₃.2 ⟨hx, h⟩ hb
  have hc₃out : ∀ x ∈ closure c₃, x ∉ c₃ → x = n₁ ∨ x = n₂ ∨ x = n₃ := fun x hx h
    => ht₃.subset ⟨hx, h⟩
  have hPb : (closure r ∪ closure c₃) ∩ bd S ⊆ {n₁, n₂} := by
    exact joined_region_has_only_boundary_endpoints (S := S) Γ (c₃ := c₃) (n₁ := n₁) (n₂ := n₂)
      (n₃ := n₃) hint hn₃ L₀ L₃ r hrb hfr' hs₀' hs₃' hc₃out
  have hPN : (closure r ∪ closure c₃) ∩ Γ.N = {n₁, n₂, n₃} := by
    exact nodes_of_region_cell_union (S := S) Γ (c₀ := c₀) (c₃ := c₃) (n₁ := n₁) (n₂ := n₂) (n₃ :=
      n₃) hc₃ ht₃ L₀ hs₀ L₃ hg₃ r hrU hfr' hc₃out
  have hnG : n₃ ∈ G \ {n₁, n₂} := by
    refine ⟨?_, ?_⟩
    · have h3 : n₃ ∈ L₃ ∪ G := hu₃ ▸ Γ.tilde_subset_discBd hc₃ hn₃t
      rcases h3 with h3 | h3
      · rcases (hg₃.2.2.2.le ⟨h3, hn₃.1⟩) with h4 | h4
        · exact absurd h4 hn₃₁
        · exact absurd h4 hn₃₂
      · exact h3
    · rintro (h | h)
      · exact hn₃₁ h
      · exact hn₃₂ h
  have hAG : (closure c₀ ∩ bd S) ∩ G = {n₁, n₂} := by
    refine Subset.antisymm (fun x hx => hcc x hx.1.1 (hGc x hx.2)) fun x hx => ?_
    exact ⟨(hi₀.symm.subset hx).1, hGend hx⟩
  refine indented_of_glue hS Γ hc₀ ht₀ hA hL₀ hb₀ hi₀ hP hG hbP' hL₀G hPc hPb hPN hnG hn₃.2 hAG
    hn'A hn'c hAΘ (.inl rfl) ?_ ?_
  · rintro c - (rfl | rfl)
    · exact .inl rfl
    · exact .inr (subset_closure.trans subset_union_right)
  · intro c hc hcR
    have hne₀ : c ≠ c₀ := fun h => hcR (.inl h)
    have hne₃ : c ≠ c₃ := fun h => hcR (.inr h)
    have hdis₀ := cell_disjoint_closure hc hc₀ hne₀
    have hdis₃ := cell_disjoint_closure hc hc₃ hne₃
    refine disjoint_union_right.mpr ⟨disjoint_left.mpr fun x hx hxr => ?_, hdis₃⟩
    have hxr' : x ∉ r := fun h => disjoint_left.mp (region_disjoint_closure hr hc) h
      (subset_closure hx)
    rcases hfr' x hxr hxr' with h | h
    · exact disjoint_left.mp hdis₃ hx (hL₃cl x h)
    · exact disjoint_left.mp hdis₀ hx (hL₀cl x h)

private theorem exists_node_between_cuff_ends
    {S : Type}
    [TopologicalSpace S]
    [ConnectedSpace S]
    (hS : IsSurface S)
    (Γ : Painting S)
    (h2 : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b)
    (h88 : ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ → tilde c₁ ⊆ tilde c₂ → (c₁ ∩ bd S).Nonempty ∧ (tilde
      c₂).ncard = 3)
    {r : Set S}
    {c₀ : Set S}
    {L₀ : Set S}
    {C₂ : Set S}
    {n₁ : S}
    {n₂ : S}
    (hc₀ : c₀ ∈ Γ.C)
    (hne : n₁ ≠ n₂)
    (ht₀ : tilde c₀ = {n₁, n₂})
    (hs₀ : Γ.IsSide c₀ L₀ n₁ n₂)
    (hb₀ : discBd (closure c₀) = closure c₀ ∩ bd S ∪ L₀)
    (hn₁b : n₁ ∈ bd S)
    (hn₂b : n₂ ∈ bd S)
    (hr : r ∈ Γ.regions)
    (hC₂ : IsLineWithEnds C₂ n₁ n₂)
    (hu : L₀ ∪ C₂ = closure r \ r)
    (hi : L₀ ∩ C₂ = {n₁, n₂})
    (hno : ¬∃ c ∈ Γ.C, ¬(c ∩ bd S).Nonempty ∧ tilde c₀ ⊆ tilde c)
    [T2Space S]
    [CompactSpace S]
    (hreg' : ∀ r ∈ Γ.regions, IsOpen r)
    (hL₀ : IsLineWithEnds L₀ n₁ n₂)
    (hn₁t : n₁ ∈ tilde c₀)
    (hn₂t : n₂ ∈ tilde c₀)
    (hn₁N : n₁ ∈ Γ.N)
    (hn₂N : n₂ ∈ Γ.N)
    (hrU : ∀ x ∈ r, x ∉ Γ.U)
    (hall : ∀ n₀ ∈ C₂ \ {n₁, n₂}, n₀ ∈ Γ.N → n₀ ∈ bd S) :
    ∃ n ∈ C₂ \ {n₁, n₂}, n ∈ Γ.N := by
  by_contra hnone
  push Not at hnone
  obtain ⟨y, hy⟩ := line_inner_nonempty hC₂
  have hyC : y ∈ closure r \ r := hu ▸ .inr hy.1
  obtain ⟨L, ⟨c', u, v, hL, hLr⟩, hyL⟩ := frontier_region hS hreg' h2 hr hyC.1 hyC.2 (hnone y hy)
  have hends : ∀ {w}, w ∈ L → w ∈ Γ.N → w = n₁ ∨ w = n₂ := fun {w} hw hwN => by
    have hwC : w ∈ closure r \ r := ⟨hLr hw, fun h => hrU w h (Γ.N_subset hwN)⟩
    rw [← hu] at hwC
    rcases hwC with h | h
    · exact hs₀.1.2.2.2.le ⟨h, hwN⟩
    · exact by_contra fun h4 => hnone w ⟨h, h4⟩ hwN
  have huL : u ∈ L ∩ Γ.N := hL.1.2.2.2.ge (.inl rfl)
  have hvL : v ∈ L ∩ Γ.N := hL.1.2.2.2.ge (.inr rfl)
  have hc' := hL.1.1
  have htm : ∀ {w}, w ∈ L ∩ Γ.N → w ∈ tilde c' := fun {w} hw =>
    ⟨hL.1.subset_closure hw.1, fun h => disjoint_left.mp (Γ.cell_disjoint_N hc') h hw.2⟩
  have huv : u ≠ v := hL.1.2.1.ne'
  have hsub : tilde c₀ ⊆ tilde c' := by
    rw [ht₀]
    rintro x (rfl | rfl)
    · rcases hends huL.1 huL.2 with h | h
      · exact h ▸ htm huL
      · rcases hends hvL.1 hvL.2 with h' | h'
        · exact h' ▸ htm hvL
        · exact absurd (h.trans h'.symm) huv
    · rcases hends huL.1 huL.2 with h | h
      · rcases hends hvL.1 hvL.2 with h' | h'
        · exact absurd (h.trans h'.symm) huv
        · exact h' ▸ htm hvL
      · exact h ▸ htm huL
  have hyb : y ∉ bd S := fun h => disjoint_left.mp hL.2
    ⟨hyL, by
      rintro (e | e)
      · exact hnone y hy (e ▸ huL.2)
      · exact hnone y hy (e ▸ hvL.2)⟩ h
  by_cases hce : c' = c₀
  · rw [hce] at hL
    have h5 : y ∈ (closure c₀ ∩ bd S) ∪ L₀ := hb₀ ▸ hL.1.2.2.1 hyL
    rcases h5 with h5 | h5
    · exact hyb h5.2
    · exact hy.2 (hi ▸ ⟨h5, hy.1⟩)
  · have h3 := (h88 c₀ hc₀ c' hc' (Ne.symm hce) hsub).2
    refine hno ⟨c', hc', fun hbord => ?_, hsub⟩
    have h4 := (Γ.border_cell c' hc' hbord).1
    omega

/-- The region next to a border cell has an internal node, by (8.3) and (8.8), when no internal cell
has all nodes of the border cell. The paper states this in the proof of (9.3), page 184.
Three nodes on `bd(Σ)` around the region would give three discs from (8.3) that, with the closed
region, cover the surface, which leaves too few nodes. -/
theorem exists_internal_node [ConnectedSpace S] (hS : IsSurface S) (Γ : Painting S) (h6 : 6
  ≤ Γ.N.ncard)
    (hreg : ∀ r ∈ Γ.regions, IsOpenDisc r) (hfr : ∀ r ∈ Γ.regions, IsOArc (closure r \ r))
    (h83 : ∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F → (F ∩ Γ.N).ncard = 2 →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧ Δ ∩ Γ.N ⊆ F
        ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1)
    (h2 : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b)
    (h88 : ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ → tilde c₁ ⊆ tilde c₂ → (c₁ ∩ bd S).Nonempty ∧
      (tilde c₂).ncard = 3)
    {r c₀ L₀ C₂ : Set S} {n₁ n₂ : S} (hc₀ : c₀ ∈ Γ.C) (hne : n₁ ≠ n₂) (ht₀ : tilde c₀ = {n₁, n₂})
      (hs₀ : Γ.IsSide c₀ L₀ n₁ n₂)
    (hb₀ : discBd (closure c₀) = (closure c₀ ∩ bd S) ∪ L₀) (hn₁b : n₁ ∈ bd S) (hn₂b : n₂ ∈ bd S)
      (hr : r ∈ Γ.regions)
    (hC₂ : IsLineWithEnds C₂ n₁ n₂) (hu : L₀ ∪ C₂ = closure r \ r) (hi : L₀ ∩ C₂ = {n₁, n₂})
    (hno : ¬ ∃ c ∈ Γ.C, ¬ (c ∩ bd S).Nonempty ∧ tilde c₀ ⊆ tilde c) :
    ∃ n₀ ∈ C₂ \ {n₁, n₂}, n₀ ∈ Γ.N ∧ n₀ ∉ bd S := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hreg' : ∀ r ∈ Γ.regions, IsOpen r := fun r hr => (hreg r hr).1
  have hL₀ : IsLineWithEnds L₀ n₁ n₂ := hs₀.1.2.1
  have hn₁t : n₁ ∈ tilde c₀ := ht₀ ▸ .inl rfl
  have hn₂t : n₂ ∈ tilde c₀ := ht₀ ▸ .inr rfl
  have hn₁N : n₁ ∈ Γ.N := Γ.tilde_subset_N hc₀ hn₁t
  have hn₂N : n₂ ∈ Γ.N := Γ.tilde_subset_N hc₀ hn₂t
  have hrU : ∀ x ∈ r, x ∉ Γ.U := fun x hx => (arcComponentsIn_subset hr hx).2
  by_contra hall
  push Not at hall
  have hex : ∃ n ∈ C₂ \ {n₁, n₂}, n ∈ Γ.N := by
    exact exists_node_between_cuff_ends (S := S) hS Γ h2 h88 (r := r) (c₀ := c₀) (L₀ := L₀) (C₂ :=
      C₂) (n₁ := n₁) (n₂ := n₂) hc₀ hne ht₀ hs₀ hb₀ hn₁b hn₂b hr hC₂ hu hi hno hreg' hL₀ hn₁t hn₂t
      hn₁N hn₂N hrU hall
  obtain ⟨n, hn, hnN⟩ := hex
  have hnb : n ∈ bd S := hall n hn hnN
  have hn1 : n ≠ n₁ := fun h => hn.2 (.inl h)
  have hn2 : n ≠ n₂ := fun h => hn.2 (.inr h)
  obtain ⟨S₁, S₂, hS₁, hS₂, hSu, hSi⟩ := hC₂.split hn.1 hn1 hn2
  have hS₁C : S₁ ⊆ C₂ := hSu ▸ subset_union_left
  have hS₂C : S₂ ⊆ C₂ := hSu ▸ subset_union_right
  have hL₀S₂ : L₀ ∩ S₂ = {n₂} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · rcases (hi.subset ⟨hx.1, hS₂C hx.2⟩ : x = n₁ ∨ x = n₂) with h | h
      · have h3 : x ∈ S₁ ∩ S₂ := ⟨h ▸ hS₁.left_mem, hx.2⟩
        rw [hSi] at h3
        exact absurd (h3.symm.trans h) hn1
      · exact h
    · rintro x rfl
      exact ⟨hL₀.right_mem, hS₂.right_mem⟩
  have hL₀S₁ : L₀ ∩ S₁ = {n₁} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · rcases (hi.subset ⟨hx.1, hS₁C hx.2⟩ : x = n₁ ∨ x = n₂) with h | h
      · exact h
      · have h3 : x ∈ S₁ ∩ S₂ := ⟨hx.2, h ▸ hS₂.right_mem⟩
        rw [hSi] at h3
        exact absurd (h3.symm.trans h) hn2
    · rintro x rfl
      exact ⟨hL₀.left_mem, hS₁.left_mem⟩
  have hT₁ : IsLineWithEnds (L₀ ∪ S₂) n₁ n := hL₀.union hS₂.symm hL₀S₂
  have hT₂ : IsLineWithEnds (L₀ ∪ S₁) n₂ n := hL₀.symm.union hS₁ hL₀S₁
  have hu₁ : S₁ ∪ (L₀ ∪ S₂) = closure r \ r := by
    rw [← hu, ← hSu]
    ext x
    simp only [mem_union]
    tauto
  have hu₂ : S₂ ∪ (L₀ ∪ S₁) = closure r \ r := by
    rw [← hu, ← hSu]
    ext x
    simp only [mem_union]
    tauto
  have hi₁ : S₁ ∩ (L₀ ∪ S₂) = {n₁, n} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, (h | h)⟩
      · exact .inl (hL₀S₁ ▸ ⟨h, hx⟩ : x ∈ ({n₁} : Set S))
      · exact .inr (hSi ▸ ⟨hx, h⟩ : x ∈ ({n} : Set S))
    · rintro x (rfl | rfl)
      · exact ⟨hS₁.left_mem, .inl hL₀.left_mem⟩
      · exact ⟨hS₁.right_mem, .inr hS₂.left_mem⟩
  have hi₂ : S₂ ∩ (L₀ ∪ S₁) = {n₂, n} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, (h | h)⟩
      · exact .inl (hL₀S₂ ▸ ⟨h, hx⟩ : x ∈ ({n₂} : Set S))
      · exact .inr (hSi ▸ ⟨h, hx⟩ : x ∈ ({n} : Set S))
    · rintro x (rfl | rfl)
      · exact ⟨hS₂.right_mem, .inl hL₀.right_mem⟩
      · exact ⟨hS₂.left_mem, .inr hS₁.right_mem⟩
  obtain ⟨F1, X₁, X₁', Δ1, -, hF1r, hF1N, -, -, -, -, hbX₁, hbX₁', hΔ1, -, -, h31, -, hnb1, hside1⟩
    :=
    exists_chord_disc hS hreg hfr h83 hr hS₁ hT₁ hu₁ hi₁ hn₁N hnN hn1.symm hn₁b hnb
  obtain ⟨F2, X₂, X₂', Δ2, -, hF2r, hF2N, -, -, -, -, hbX₂, hbX₂', hΔ2, -, -, h32, -, hnb2, hside2⟩
    :=
    exists_chord_disc hS hreg hfr h83 hr hS₂.symm hT₂ hu₂ hi₂ hn₂N hnN hn2.symm hn₂b hnb
  obtain ⟨F0, X₀, X₀', Δ0, -, hF0r, hF0N, -, -, -, -, hbX₀, hbX₀', hΔ0, -, -, h30, -, hnb0, hside0⟩
    :=
    exists_chord_disc hS hreg hfr h83 hr hL₀ hC₂ hu hi hn₁N hn₂N hne hn₁b hn₂b
  have hS₁Δ : S₁ ⊆ Δ1 := by
    rcases hside1 with h | h
    · exact fun x hx => h (discBd_subset _ (hbX₁ ▸ .inl hx))
    · exfalso
      have hm : n₂ ∈ F1 ∩ Γ.N :=
        ⟨h31 ⟨h (discBd_subset _ (hbX₁' ▸ .inl (.inl hL₀.right_mem))), hn₂N⟩, hn₂N⟩
      rw [hF1N] at hm
      rcases hm with hm | hm
      · exact hne hm.symm
      · exact hn2 hm.symm
  have hS₂Δ : S₂ ⊆ Δ2 := by
    rcases hside2 with h | h
    · exact fun x hx => h (discBd_subset _ (hbX₂ ▸ .inl hx))
    · exfalso
      have hm : n₁ ∈ F2 ∩ Γ.N :=
        ⟨h32 ⟨h (discBd_subset _ (hbX₂' ▸ .inl (.inl hL₀.left_mem))), hn₁N⟩, hn₁N⟩
      rw [hF2N] at hm
      rcases hm with hm | hm
      · exact hne hm
      · exact hn1 hm.symm
  have hL₀Δ : L₀ ⊆ Δ0 := by
    rcases hside0 with h | h
    · exact fun x hx => h (discBd_subset _ (hbX₀ ▸ .inl hx))
    · exfalso
      have hm : n ∈ F0 ∩ Γ.N := ⟨h30 ⟨h (discBd_subset _ (hbX₀' ▸ .inl hn.1)), hnN⟩, hnN⟩
      rw [hF0N] at hm
      exact hn.2 hm
  let A₀ : Set S := {n₁, n₂, n}
  have hA₀ : A₀.Finite := by simp [A₀]
  let W : Set S := closure r ∪ Δ0 ∪ Δ1 ∪ Δ2
  have hWc : IsClosed W := ((isClosed_closure.union hΔ0.isClosed).union hΔ1.isClosed).union
    hΔ2.isClosed
  have hrnb : ∀ {x}, x ∈ r → W ∈ 𝓝 x := fun {x} hx =>
    Filter.mem_of_superset ((hreg r hr).1.mem_nhds hx) (fun z hz => .inl (.inl (.inl
      (subset_closure hz))))
  have hcase0 : ∀ {x}, x ∈ Δ0 → x ∉ A₀ → W ∈ 𝓝 x := fun {x} hx hxA => by
    by_cases hF : x ∈ F0
    · exact hrnb (hF0r ⟨hF, fun h => hxA (h.elim .inl fun h' => .inr (.inl h'))⟩)
    · exact Filter.mem_of_superset (hnb0 x ⟨hx, hF⟩) fun z hz => .inl (.inl (.inr hz))
  have hcase1 : ∀ {x}, x ∈ Δ1 → x ∉ A₀ → W ∈ 𝓝 x := fun {x} hx hxA => by
    by_cases hF : x ∈ F1
    · exact hrnb (hF1r ⟨hF, fun h => hxA (h.elim .inl fun h' => .inr (.inr h'))⟩)
    · exact Filter.mem_of_superset (hnb1 x ⟨hx, hF⟩) fun z hz => .inl (.inr hz)
  have hcase2 : ∀ {x}, x ∈ Δ2 → x ∉ A₀ → W ∈ 𝓝 x := fun {x} hx hxA => by
    by_cases hF : x ∈ F2
    · exact hrnb (hF2r ⟨hF, fun h => hxA (h.elim (.inr ∘ .inl) fun h' => .inr (.inr h'))⟩)
    · exact Filter.mem_of_superset (hnb2 x ⟨hx, hF⟩) fun z hz => .inr hz
  have hsplit : ∀ {x}, x ∈ closure r → x ∉ r → x ∈ Δ0 ∨ x ∈ Δ1 ∨ x ∈ Δ2 := fun {x} hx h => by
    have h3 : x ∈ L₀ ∪ C₂ := hu ▸ ⟨hx, h⟩
    rcases h3 with h3 | h3
    · exact .inl (hL₀Δ h3)
    · rw [← hSu] at h3
      rcases h3 with h3 | h3
      · exact .inr (.inl (hS₁Δ h3))
      · exact .inr (.inr (hS₂Δ h3))
  have hnbW : ∀ x ∈ W, x ∉ A₀ → W ∈ 𝓝 x := by
    rintro x (((hx | hx) | hx) | hx) hxA
    · by_cases h : x ∈ r
      · exact hrnb h
      · rcases hsplit hx h with h3 | h3 | h3
        · exact hcase0 h3 hxA
        · exact hcase1 h3 hxA
        · exact hcase2 h3 hxA
    · exact hcase0 hx hxA
    · exact hcase1 hx hxA
    · exact hcase2 hx hxA
  obtain ⟨z, hz⟩ := arcComponentsIn_nonempty hr
  have hzA : z ∉ A₀ := by
    have hzN : z ∉ Γ.N := fun h => hrU z hz (Γ.N_subset h)
    rintro (rfl | rfl | rfl)
    · exact hzN hn₁N
    · exact hzN hn₂N
    · exact hzN hnN
  have hNA : Γ.N ⊆ A₀ := fun y hyN => by
    by_contra hyA
    have hyr : y ∉ r := fun h => hrU y h (Γ.N_subset hyN)
    have hy0 : ∀ {y}, y ∈ Δ0 → y ∈ Γ.N → y ∈ A₀ := fun {y} h h' => by
      rcases (hF0N.subset ⟨h30 ⟨h, h'⟩, h'⟩) with e | e
      · exact .inl e
      · exact .inr (.inl e)
    have hy1 : ∀ {y}, y ∈ Δ1 → y ∈ Γ.N → y ∈ A₀ := fun {y} h h' => by
      rcases (hF1N.subset ⟨h31 ⟨h, h'⟩, h'⟩) with e | e
      · exact .inl e
      · exact .inr (.inr e)
    have hy2 : ∀ {y}, y ∈ Δ2 → y ∈ Γ.N → y ∈ A₀ := fun {y} h h' => by
      rcases (hF2N.subset ⟨h32 ⟨h, h'⟩, h'⟩) with e | e
      · exact .inr (.inl e)
      · exact .inr (.inr e)
    rcases cover_off hS.2.2 hWc hA₀ ⟨z, .inl (.inl (.inl (subset_closure hz))), hzA⟩ hnbW hyA with
      ((h | h) | h) | h
    · rcases hsplit h hyr with h3 | h3 | h3
      · exact hyA (hy0 h3 hyN)
      · exact hyA (hy1 h3 hyN)
      · exact hyA (hy2 h3 hyN)
    · exact hyA (hy0 h hyN)
    · exact hyA (hy1 h hyN)
    · exact hyA (hy2 h hyN)
  have hle : Γ.N.ncard ≤ A₀.ncard := ncard_le_ncard hNA hA₀
  have hle3 : A₀.ncard ≤ 3 := by
    have h1 := ncard_insert_le n₁ ({n₂, n} : Set S)
    have h2 := ncard_pair hn2.symm
    change (insert n₁ {n₂, n} : Set S).ncard ≤ 3
    omega
  omega

/-- Part (A) of the statement, with the hypotheses that it uses. -/
theorem indented_of_region [ConnectedSpace S] (hS : IsSurface S) (Γ : Painting S) (h6 : 6
  ≤ Γ.N.ncard)
    (hreg : ∀ r ∈ Γ.regions, IsOpenDisc r) (hfr : ∀ r ∈ Γ.regions, IsOArc (closure r \ r))
    (h83 : ∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F → (F ∩ Γ.N).ncard = 2 →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧ Δ ∩ Γ.N ⊆ F
        ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1)
    (h2 : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b)
    (h88 : ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ → tilde c₁ ⊆ tilde c₂ → (c₁ ∩ bd S).Nonempty ∧
      (tilde c₂).ncard = 3)
    {Θ c₀ : Set S} {n₁ n₂ : S} (hΘ : Θ ∈ cuffs S) (hc₀ : c₀ ∈ Γ.C) (hc₀Θ : (c₀ ∩ Θ).Nonempty)
      (hne : n₁ ≠ n₂) (ht₀ : tilde c₀ = {n₁, n₂})
    (hno : ¬ ∃ c ∈ Γ.C, ¬ (c ∩ bd S).Nonempty ∧ tilde c₀ ⊆ tilde c) :
    ∃ n₀ ∈ Γ.N \ bd S, ∃ Γ' : Painting S, IsIndentedBorderPainting Γ Θ c₀ n₁ n₂ n₀ {c₀} Γ' := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hreg' : ∀ r ∈ Γ.regions, IsOpen r := fun r hr => (hreg r hr).1
  obtain ⟨L₀, n', hA, hs₀, hb₀, hi₀, hn₁b, hn₂b, hAΘ, hn'A, hn'c⟩ := border_data hS hΘ hc₀ hc₀Θ ht₀
  have hL₀ : IsLineWithEnds L₀ n₁ n₂ := hs₀.1.2.1
  obtain ⟨St, γ, r, -, -, -, -, -, -, -, hr, -, hL₀r, -⟩ := side_strip hS hreg' hs₀ (A
    := ∅) isClosed_empty (by simp)
  have hrU : ∀ x ∈ r, x ∉ Γ.U := fun x hx => (arcComponentsIn_subset hr hx).2
  have hrb : ∀ x ∈ r, x ∉ bd S := fun x hx h => hrU x hx (Γ.bd_subset h)
  have hL₀cl : ∀ x ∈ L₀, x ∈ closure c₀ := fun x hx => hs₀.1.subset_closure hx
  have hL₀C : L₀ ⊆ closure r \ r := fun x hx =>
    ⟨hL₀r hx, fun h => disjoint_left.mp (region_disjoint_closure hr hc₀) h (hL₀cl x hx)⟩
  obtain ⟨C₂, hC₂, hu, hi⟩ := oarc_split (hfr r hr) hL₀ hL₀C
  obtain ⟨n₀, hn₀, hn₀N, hn₀b⟩ := exists_internal_node hS Γ h6 hreg hfr h83 h2 h88 hc₀ hne ht₀ hs₀
    hb₀ hn₁b hn₂b hr hC₂ hu hi hno
  refine ⟨n₀, ⟨hn₀N, hn₀b⟩, ?_⟩
  obtain ⟨hdR, hbR⟩ := region_disc hS hreg hr (hfr r hr)
  have hn01 : n₀ ≠ n₁ := fun h => hn₀.2 (.inl h)
  have hn02 : n₀ ≠ n₂ := fun h => hn₀.2 (.inr h)
  have hn₀L : n₀ ∉ L₀ := fun h => hn₀.2 (hi ▸ ⟨h, hn₀.1⟩)
  obtain ⟨S₁, S₂, hS₁, hS₂, hSu, hSi⟩ := hC₂.split hn₀.1 hn01 hn02
  have hS₁C : S₁ ⊆ C₂ := hSu ▸ subset_union_left
  have hS₂C : S₂ ⊆ C₂ := hSu ▸ subset_union_right
  have hn₁S₂ : n₁ ∉ S₂ := fun h => by
    have h3 : n₁ ∈ S₁ ∩ S₂ := ⟨hS₁.left_mem, h⟩
    rw [hSi] at h3
    exact hn01 h3.symm
  have hn₂S₁ : n₂ ∉ S₁ := fun h => by
    have h3 : n₂ ∈ S₁ ∩ S₂ := ⟨h, hS₂.right_mem⟩
    rw [hSi] at h3
    exact hn02 h3.symm
  have hL₀S₂ : L₀ ∩ S₂ = {n₂} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · rcases (hi.subset ⟨hx.1, hS₂C hx.2⟩ : x = n₁ ∨ x = n₂) with h | h
      · exact absurd (h ▸ hx.2) hn₁S₂
      · exact h
    · rintro x rfl
      exact ⟨hL₀.right_mem, hS₂.right_mem⟩
  have hT₁ : IsLineWithEnds (L₀ ∪ S₂) n₁ n₀ := hL₀.union hS₂.symm hL₀S₂
  have hu₁ : S₁ ∪ (L₀ ∪ S₂) = discBd (closure r) := by
    rw [hbR, ← hu, ← hSu]
    ext x
    simp only [mem_union]
    tauto
  have hi₁ : S₁ ∩ (L₀ ∪ S₂) = {n₁, n₀} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, (h | h)⟩
      · rcases (hi.subset ⟨h, hS₁C hx⟩ : x = n₁ ∨ x = n₂) with h3 | h3
        · exact .inl h3
        · exact absurd (h3 ▸ hx) hn₂S₁
      · exact .inr (hSi ▸ ⟨hx, h⟩ : x ∈ ({n₀} : Set S))
    · rintro x (rfl | rfl)
      · exact ⟨hS₁.left_mem, .inl hL₀.left_mem⟩
      · exact ⟨hS₁.right_mem, .inr hS₂.left_mem⟩
  obtain ⟨G₁, Y₁, Y, hG₁, hG₁b, hG₁R, hY₁, hY, huY, hiY, hbY₁, hbY⟩ := split_disc hdR hS₁ hT₁
    hn01.symm hu₁ hi₁
  have hRb : ∀ {x}, x ∈ S₁ ∨ x ∈ L₀ ∨ x ∈ S₂ → x ∈ discBd (closure r) := fun {x} h => by
    rw [← hu₁]
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  have hG₁e : ∀ {x}, x ∈ G₁ → x ∈ discBd (closure r) → x = n₁ ∨ x = n₀ := fun {x} h h'
    => hG₁b.subset ⟨h, h'⟩
  have hG₁L : G₁ ∩ L₀ = {n₁} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · rcases hG₁e hx.1 (hRb (.inr (.inl hx.2))) with h | h
      · exact h
      · exact absurd (h ▸ hx.2) hn₀L
    · rintro x rfl
      exact ⟨hG₁.left_mem, hL₀.left_mem⟩
  have hV : IsLineWithEnds (G₁ ∪ L₀) n₀ n₂ := hG₁.symm.union hL₀ hG₁L
  have hbYu : S₂ ∪ (G₁ ∪ L₀) = discBd Y := by
    rw [hbY]
    ext x
    simp only [mem_union]
    tauto
  have hiV : S₂ ∩ (G₁ ∪ L₀) = {n₀, n₂} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, (h | h)⟩
      · rcases hG₁e h (hRb (.inr (.inr hx))) with h3 | h3
        · exact absurd (h3 ▸ hx) hn₁S₂
        · exact .inl h3
      · exact .inr (hL₀S₂ ▸ ⟨h, hx⟩ : x ∈ ({n₂} : Set S))
    · rintro x (rfl | rfl)
      · exact ⟨hS₂.left_mem, .inl hG₁.right_mem⟩
      · exact ⟨hS₂.right_mem, .inr hL₀.right_mem⟩
  obtain ⟨G₂, Y₂, P, hG₂, hG₂b, hG₂Y, hY₂, hP, huP, hiP, hbY₂, hbP⟩ := split_disc hY hS₂ hV hn02
    hbYu hiV
  have hPY : P ⊆ Y := huP ▸ subset_union_right
  have hYR : Y ⊆ closure r := huY ▸ subset_union_right
  have hPR : P ⊆ closure r := hPY.trans hYR
  have hYb : ∀ {x}, x ∈ S₂ ∨ x ∈ G₁ ∨ x ∈ L₀ → x ∈ discBd Y := fun {x} h => by
    rw [← hbYu]
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  have hG₂e : ∀ {x}, x ∈ G₂ → x ∈ discBd Y → x = n₀ ∨ x = n₂ := fun {x} h h' => hG₂b.subset ⟨h, h'⟩
  have hGG : G₁ ∩ G₂ = {n₀} := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · rcases hG₂e hx.2 (hYb (.inr (.inl hx.1))) with h | h
      · exact h
      · have h3 := hG₁e hx.1 (hRb (.inr (.inl (h ▸ hL₀.right_mem))))
        rcases h3 with h3 | h3
        · exact absurd (h.symm.trans h3) hne.symm
        · exact h3
    · rintro x rfl
      exact ⟨hG₁.right_mem, hG₂.left_mem⟩
  have hG : IsLineWithEnds (G₁ ∪ G₂) n₁ n₂ := hG₁.union hG₂ hGG
  have hbP' : discBd P = L₀ ∪ (G₁ ∪ G₂) := by
    rw [hbP]
    ext x
    simp only [mem_union]
    tauto
  have hL₀G : L₀ ∩ (G₁ ∪ G₂) = {n₁, n₂} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, (h | h)⟩
      · exact .inl (hG₁L ▸ ⟨h, hx⟩ : x ∈ ({n₁} : Set S))
      · rcases hG₂e h (hYb (.inr (.inr hx))) with h3 | h3
        · exact absurd (h3 ▸ hx) hn₀L
        · exact .inr h3
    · rintro x (rfl | rfl)
      · exact ⟨hL₀.left_mem, .inl hG₁.left_mem⟩
      · exact ⟨hL₀.right_mem, .inr hG₂.right_mem⟩
  have hPC : ∀ x ∈ P, x ∉ r → x ∈ L₀ ∨ x = n₀ := fun x hx hxr => by
    have h3 : x ∈ L₀ ∪ C₂ := hu ▸ ⟨hPR hx, hxr⟩
    rcases h3 with h3 | h3
    · exact .inl h3
    · rw [← hSu] at h3
      rcases h3 with h3 | h3
      · have h4 : x ∈ G₁ := hiY ▸ ⟨discBd_subset _ (hbY₁ ▸ .inl h3), hPY hx⟩
        rcases hG₁e h4 (hRb (.inl h3)) with h5 | h5
        · exact .inl (h5 ▸ hL₀.left_mem)
        · exact .inr h5
      · have h4 : x ∈ G₂ := hiP ▸ ⟨discBd_subset _ (hbY₂ ▸ .inl h3), hx⟩
        rcases hG₂e h4 (hYb (.inl h3)) with h5 | h5
        · exact .inr h5
        · exact .inl (h5 ▸ hL₀.right_mem)
  have hnotcl : n₀ ∉ closure c₀ := fun h => by
    have h3 : n₀ ∈ tilde c₀ := ⟨h, fun h3 => disjoint_left.mp (Γ.cell_disjoint_N hc₀) h3 hn₀N⟩
    rw [ht₀] at h3
    rcases h3 with h3 | h3
    · exact hn01 h3
    · exact hn02 h3
  have hL₀P : L₀ ⊆ P := fun x hx => discBd_subset _ (hbP' ▸ .inl hx)
  have hGP : G₁ ∪ G₂ ⊆ P := fun x hx => discBd_subset _ (hbP' ▸ .inr hx)
  have hPc : P ∩ closure c₀ = L₀ := by
    refine Subset.antisymm ?_ fun x hx => ⟨hL₀P hx, hL₀cl x hx⟩
    rintro x ⟨hx, hx'⟩
    rcases hPC x hx fun h => disjoint_left.mp (region_disjoint_closure hr hc₀) h hx' with h | h
    · exact h
    · exact absurd (h ▸ hx') hnotcl
  have hs₀' : ∀ x ∈ L₀, x ∈ bd S → x ∈ ({n₁, n₂} : Set S) := fun x hx hb =>
    by_contra fun h => disjoint_left.mp hs₀.2 ⟨hx, h⟩ hb
  have hPb : P ∩ bd S ⊆ {n₁, n₂} := by
    rintro x ⟨hx, hb⟩
    rcases hPC x hx (hrb x · hb) with h | h
    · exact hs₀' x h hb
    · exact absurd (h ▸ hb) hn₀b
  have hPN : P ∩ Γ.N = {n₁, n₂, n₀} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, hxN⟩
      rcases hPC x hx (fun h => hrU x h (Γ.N_subset hxN)) with h | h
      · rcases (hs₀.1.2.2.2.le ⟨h, hxN⟩) with h3 | h3
        · exact .inl h3
        · exact .inr (.inl h3)
      · exact .inr (.inr h)
    · rintro x (rfl | rfl | rfl)
      · exact ⟨hL₀P hL₀.left_mem, (hs₀.1.2.2.2.ge (.inl rfl)).2⟩
      · exact ⟨hL₀P hL₀.right_mem, (hs₀.1.2.2.2.ge (.inr rfl)).2⟩
      · exact ⟨hGP (.inl hG₁.right_mem), hn₀N⟩
  have hnG : n₀ ∈ (G₁ ∪ G₂) \ {n₁, n₂} := by
    refine ⟨.inl hG₁.right_mem, ?_⟩
    rintro (h | h)
    · exact hn01 h
    · exact hn02 h
  have hAG : (closure c₀ ∩ bd S) ∩ (G₁ ∪ G₂) = {n₁, n₂} := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · rcases hPC x (hGP hx.2) (hrb x · hx.1.2) with h | h
      · exact hs₀' x h hx.1.2
      · exact absurd (h ▸ hx.1.2) hn₀b
    · exact ⟨(hi₀.symm.subset hx).1, (hL₀G.symm.subset hx).2⟩
  refine indented_of_glue hS Γ hc₀ ht₀ hA hL₀ hb₀ hi₀ hP hG hbP' hL₀G hPc hPb hPN hnG hn₀b hAG hn'A
    hn'c hAΘ rfl ?_ ?_
  · rintro c - rfl
    exact .inl rfl
  · intro c hc hcR
    have hne₀ : c ≠ c₀ := hcR
    refine disjoint_left.mpr fun x hx hxP => ?_
    have hxr : x ∉ r := fun h => disjoint_left.mp (region_disjoint_closure hr hc) h
      (subset_closure hx)
    rcases hPC x hxP hxr with h | h
    · exact disjoint_left.mp (cell_disjoint_closure hc hc₀ hne₀) hx (hL₀cl x h)
    · exact disjoint_left.mp (Γ.cell_disjoint_N hc) hx (h ▸ hn₀N)

/-- **The painting of the proofs of (9.3) and (9.4) of Graph Minors XVII**, pages 184 and 185, kept
in the same surface. -/
theorem indentedBorderPainting : IndentedBorderPaintingStatement := by
  unfold IndentedBorderPaintingStatement
  intro S _ _ hS Γ h6 hreg hfr h2 h83 h88 Θ hΘ c₀ hc₀ hc₀Θ n₁ n₂ hne ht₀
  have ht2 : T2Space S := hS.2.1
  have h2' : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b := fun c hc =>
    (one_lt_ncard (Γ.cell_disc c hc).2.2.1).mp (h2 c hc)
  refine ⟨fun hno => indented_of_region hS Γ h6 hreg hfr h83 h2' h88 hΘ hc₀ hc₀Θ hne ht₀ hno, ?_⟩
  intro c₃ hc₃ hint n₃ hn₃ ht₃
  exact indented_of_cell hS Γ hreg hfr h83 h2' h88 hΘ hc₀ hc₀Θ hne ht₀ hc₃ hint hn₃ ht₃

end GraphMinor.GM17
