/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.ThickForest
public import LeanPool.GraphMinor.GM07.Section3
public import LeanPool.GraphMinor.GM12.Section4FiniteLineDrawing
public import LeanPool.GraphMinor.Surface.Lunes
public import LeanPool.GraphMinor.Surface.DiscPolygon
public import LeanPool.GraphMinor.Surface.TriPath
public import LeanPool.GraphMinor.Surface.EdgeLoop
public import LeanPool.GraphMinor.Surface.CutLift

/-!
# Cutting the boundaries of discs into a matching

Graph Minors VII, (3.4), claim (1) (page 220), takes the boundary of a thin disc around a component
of a forest `H`, and cuts it at
the small pieces where the disc meets `bd(Σ)`. What is left is a set of lines, which form a
matching. This file does the cutting, on
a line (`exists_cut_line`) and on an `O`-arc (`exists_cut_oArc`). It also shows that a disc minus
some points of its boundary is
simply connected (`isSimplyConnected_disc_sdiff`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- A closed disc minus some points of its boundary is simply connected and connected. -/
theorem isSimplyConnected_disc_sdiff [T2Space S] {D B : Set S} (hD : IsClosedDisc D)
  (hB : B ⊆ discBd D) :
    IsSimplyConnectedSubset (D \ B) ∧ IsPreconnected (D \ B) := by
  have hint : discInt D ⊆ D \ B := fun x hx => ⟨hx.1, fun h => hx.2 (hB h)⟩
  refine ⟨⟨fun a ha b hb hab => ?_, fun F hF hFZ => ?_⟩, ?_⟩
  · obtain ⟨h, g, c⟩ := hD.exists_isChart
    have ha' := c.hm ha.1
    have hb' := c.hm hb.1
    have hne : h a ≠ h b := fun e => hab (c.gh.injOn ha.1 hb.1 e)
    have hl := isLineWithEnds_segment hne
    have hsub : segment ℝ (h a) (h b) ⊆ closedBall 0 1 := (convex_closedBall
      (0 : ℂ) 1).segment_subset ha' hb'
    have hline := hl.image_injOn (c.gc.mono hsub) (c.injOn.mono hsub)
    rw [c.gh ha.1, c.gh hb.1] at hline
    refine ⟨_, ?_, hline⟩
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨c.gm (hsub hw), fun hwB => ?_⟩
    by_cases h1 : w = h a
    · rw [h1, c.gh ha.1] at hwB
      exact ha.2 hwB
    by_cases h2 : w = h b
    · rw [h2, c.gh hb.1] at hwB
      exact hb.2 hwB
    have hop : w ∈ openSegment ℝ (h a) (h b) := by
      rw [← insert_endpoints_openSegment] at hw
      rcases hw with e | e | e
      · exact (h1 e).elim
      · exact (h2 e).elim
      · exact e
    have hin : w ∈ interior (closedBall (0 : ℂ) 1) :=
      (strictConvex_closedBall ℝ (0 : ℂ) 1).openSegment_subset ha' hb' hne hop
    rw [interior_closedBall _ one_ne_zero] at hin
    have hs : h (g w) ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem _ (hB hwB)
    rw [c.hg (hsub hw)] at hs
    exact (ne_of_lt (mem_ball_zero_iff.mp hin)) (mem_sphere_zero_iff_norm.mp hs)
  · obtain ⟨Δ, ⟨h1, h2, h3, -, h5, -⟩, -⟩ := disc_oArc D F hD (fun x hx => (hFZ hx).1) hF
    refine ⟨Δ, h2, h3, fun x hx => ⟨h1 hx, fun hxB => ?_⟩⟩
    by_cases hxF : x ∈ F
    · exact (hFZ hxF).2 hxB
    · exact disjoint_left.mp h5 ⟨hx, hxF⟩ (hB hxB)
  · exact hD.isPreconnected_discInt.subset_closure hint fun x hx => hD.subset_closure_discInt hx.1

/-- A connected set in the union of two closed sets, which misses their common part, lies in one of
them. -/
theorem preconnected_side {J A B : Set S} (hJ : IsPreconnected J) (hA : IsClosed A)
  (hB : IsClosed B) (hs : J ⊆ A ∪ B)
    (hd : Disjoint J (A ∩ B)) : J ⊆ A ∨ J ⊆ B := by
  by_contra hn
  push Not at hn
  obtain ⟨⟨x, hx, hxA⟩, ⟨y, hy, hyB⟩⟩ := (by simpa only [not_subset] using hn :
    (∃ x ∈ J, x ∉ A) ∧ ∃ y ∈ J, y ∉ B)
  have h1 := isPreconnected_closed_iff.mp hJ A B hA hB hs ⟨y, hy, (hs hy).resolve_right hyB⟩ ⟨x,
    hx, (hs hx).resolve_left hxA⟩
  obtain ⟨z, hz, h2⟩ := h1
  exact disjoint_left.mp hd hz h2

variable [T2Space S]

omit [T2Space S] in
/-- A line with distinct ends is the closure of the set of its inner points. -/
theorem line_subset_of_inner {ℓ A : Set S} {s t : S} (hl : IsLineWithEnds ℓ s t) (hA : IsClosed A)
  (h : ℓ \ {s, t} ⊆ A) :
    ℓ ⊆ A := by
  exact hl.subset_closure_diff.trans (closure_minimal h hA)

/-- The ordered case of `exists_line_gap`. -/
theorem exists_line_gap_aux {L ℓ L' L'' : Set S} {u v s t : S} (hℓ : IsLineWithEnds ℓ s t)
  (hst : s ≠ t) (hv : v ∉ ℓ)
    (h₁ : IsLineWithEnds L' u s) (h₂ : IsLineWithEnds L'' s v) (hU : L' ∪ L'' = L) (hI : L' ∩ L''
      = {s}) (ht : t ∈ L'')
    (hsub : ℓ ⊆ L) : ∃ L₂, IsLineWithEnds L₂ t v ∧ L' ∪ ℓ ∪ L₂ = L ∧ L' ∩ ℓ = {s} ∧ L₂ ∩ ℓ = {t}
      ∧ Disjoint L' L₂ := by
  obtain ⟨M, L₂, hM, hL₂, hU', hI'⟩ := h₂.split ht hst.symm (fun e => hv (e ▸ hℓ.right_mem))
  have hinner : IsPreconnected (ℓ \ {s, t}) := hℓ.isPreconnected_diff
  have hd : Disjoint (ℓ \ {s, t}) (L' ∩ L'') := by
    rw [hI]
    exact disjoint_left.mpr fun x hx h => hx.2 (.inl h)
  have hs₂ : s ∉ L₂ := fun h => hst (by
    have : s ∈ M ∩ L₂ := ⟨hM.left_mem, h⟩
    rwa [hI'] at this)
  have hnot : ¬ ℓ \ {s, t} ⊆ L' := fun h => by
    have h3 := line_subset_of_inner hℓ h₁.isCompact.isClosed h
    have : t ∈ L' ∩ L'' := ⟨h3 hℓ.right_mem, ht⟩
    rw [hI] at this
    exact hst this.symm
  have h1 := (preconnected_side hinner h₁.isCompact.isClosed h₂.isCompact.isClosed (fun x hx
    => hU ▸ hsub hx.1) hd).resolve_left hnot
  rw [← hU'] at h1
  have hd' : Disjoint (ℓ \ {s, t}) (M ∩ L₂) := by
    rw [hI']
    exact disjoint_left.mpr fun x hx h => hx.2 (.inr h)
  have hMeq : ℓ = M := by
    rcases preconnected_side hinner hM.isCompact.isClosed hL₂.isCompact.isClosed h1 hd' with h2 | h2
    · exact hM.eq_of_subset hℓ.isPreconnected_self (line_subset_of_inner hℓ hM.isCompact.isClosed
        h2) hℓ.left_mem hℓ.right_mem
    · exact (hs₂ (line_subset_of_inner hℓ hL₂.isCompact.isClosed h2 hℓ.left_mem)).elim
  subst hMeq
  have hdis : Disjoint L' L₂ := disjoint_left.mpr fun x h1 h2 => by
    have : x ∈ L' ∩ L'' := ⟨h1, hU' ▸ .inr h2⟩
    rw [hI] at this
    exact hs₂ (mem_singleton_iff.mp this ▸ h2)
  refine ⟨L₂, hL₂, ?_, ?_, ?_, hdis⟩
  · rw [union_assoc, hU', hU]
  · ext x
    constructor
    · rintro ⟨h3, h4⟩
      have : x ∈ L' ∩ L'' := ⟨h3, hU' ▸ .inl h4⟩
      rwa [hI] at this
    · rintro rfl
      exact ⟨h₁.right_mem, hℓ.left_mem⟩
  · rw [inter_comm, hI']

/-- A sub-line `ℓ` of a line `L` cuts `L` into two disjoint lines, one at each end of `L`, when it
misses the ends of `L`. -/
theorem exists_line_gap {L ℓ : Set S} {u v s t : S} (hL : IsLineWithEnds L u v)
  (hℓ : IsLineWithEnds ℓ s t) (hst : s ≠ t) (hsub : ℓ ⊆ L)
    (hu : u ∉ ℓ) (hv : v ∉ ℓ) :
    ∃ x y L₁ L₂, ((x = s ∧ y = t) ∨ (x = t ∧ y = s)) ∧ IsLineWithEnds L₁ u x
      ∧ IsLineWithEnds L₂ y v ∧ L₁ ∪ ℓ ∪ L₂ = L ∧
      L₁ ∩ ℓ = {x} ∧ L₂ ∩ ℓ = {y} ∧ Disjoint L₁ L₂ := by
  obtain ⟨L', L'', h₁, h₂, hU, hI⟩ := hL.split (hsub hℓ.left_mem) (fun e => hu (e ▸ hℓ.left_mem))
    (fun e => hv (e ▸ hℓ.left_mem))
  have ht : t ∈ L' ∪ L'' := hU ▸ hsub hℓ.right_mem
  rcases ht with ht | ht
  · have hU2 : L'' ∪ L' = L := by rw [union_comm, hU]
    have hI2 : L'' ∩ L' = {s} := by rw [inter_comm, hI]
    obtain ⟨L₂, h3, h4, h5, h6, h7⟩ := exists_line_gap_aux hℓ hst hu h₂.symm h₁.symm hU2 hI2 ht hsub
    refine ⟨t, s, L₂, L'', .inr ⟨rfl, rfl⟩, h3.symm, h₂, ?_, h6, ?_, h7.symm⟩
    · rw [← h4]
      ext x
      simp only [mem_union]
      tauto
    · exact h5
  · obtain ⟨L₂, h3, h4, h5, h6, h7⟩ := exists_line_gap_aux hℓ hst hv h₁ h₂ hU hI ht hsub
    exact ⟨s, t, L', L₂, .inl ⟨rfl, rfl⟩, h₁, h3, h4, h5, h6, h7⟩

/-- The result of cutting: lines `𝓐` in `L` with ends in `B`, pairwise disjoint, that cover `L`
apart from the inner points of the lines
`ℓ i` with `i ∈ I`, and that meet each `ℓ i` only at its ends. -/
structure IsCut {ι : Type*} (ℓ : ι → Set S) (s t : ι → S) (I : Finset ι) (L B : Set S) (𝓐 : Set
  (Set S)) : Prop where
  finite : 𝓐.Finite
  line : ∀ A ∈ 𝓐, ∃ a c, IsLineWithEnds A a c ∧ a ≠ c ∧ A ⊆ L ∧ A ∩ B = {a, c}
  disj : ∀ A ∈ 𝓐, ∀ A' ∈ 𝓐, A ≠ A' → Disjoint A A'
  cover : ∀ x ∈ L, (∃ A ∈ 𝓐, x ∈ A) ∨ ∃ i ∈ I, x ∈ ℓ i ∧ x ≠ s i ∧ x ≠ t i
  meet : ∀ A ∈ 𝓐, ∀ i ∈ I, ∀ x ∈ A, x ∈ ℓ i → x = s i ∨ x = t i

/-- The ends of the lines `ℓ i` with `i ∈ I`. -/
def cutEnds {ι : Type*} (s t : ι → S) (I : Finset ι) : Set S := ⋃ i ∈ I, {s i, t i}

/-- **Cutting a line.** A line `L` with sub-lines `ℓ i`, which are disjoint and miss the ends of
`L`, is cut into lines. -/
theorem exists_cut_line {ι : Type*} {ℓ : ι → Set S} {s t : ι → S}
  (hℓ : ∀ i, IsLineWithEnds (ℓ i) (s i) (t i))
    (hst : ∀ i, s i ≠ t i) (hdis : ∀ i j, i ≠ j → Disjoint (ℓ i) (ℓ j)) (n : ℕ) :
    ∀ (I : Finset ι), I.card = n → ∀ (L : Set S) (u v : S), IsLineWithEnds L u v → u ≠ v →
      (∀ i ∈ I, ℓ i ⊆ L ∧ u ∉ ℓ i ∧ v ∉ ℓ i) →
      ∃ 𝓐, IsCut ℓ s t I L ({u, v} ∪ cutEnds s t I) 𝓐 := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro I hI L u v hL huv hsub
  rcases I.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · refine ⟨{L}, ⟨finite_singleton _, ?_, ?_, ?_, ?_⟩⟩
    · rintro A rfl
      refine ⟨u, v, hL, huv, subset_rfl, ?_⟩
      ext x
      simp only [cutEnds, Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty,
        mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl)
        · exact ⟨hL.left_mem, .inl rfl⟩
        · exact ⟨hL.right_mem, .inr rfl⟩
    · rintro A rfl A' rfl h
      exact (h rfl).elim
    · exact fun x hx => .inl ⟨L, rfl, hx⟩
    · exact fun _ _ i hi => by simp at hi
  obtain ⟨hsub₀, hu₀, hv₀⟩ := hsub i₀ hi₀
  obtain ⟨x, y, L₁, L₂, hxy, h₁, h₂, hU, hI₁, hI₂, hD⟩ := exists_line_gap hL (hℓ i₀)
    (hst i₀) hsub₀ hu₀ hv₀
  have hxm : x ∈ ℓ i₀ := by
    have : x ∈ L₁ ∩ ℓ i₀ := hI₁ ▸ rfl
    exact this.2
  have hym : y ∈ ℓ i₀ := by
    have : y ∈ L₂ ∩ ℓ i₀ := hI₂ ▸ rfl
    exact this.2
  have hLin₁ : L₁ ⊆ L := fun z hz => hU ▸ .inl (.inl hz)
  have hLin₂ : L₂ ⊆ L := fun z hz => hU ▸ .inr hz
  let I₁ := (I.erase i₀).filter fun i => ℓ i ⊆ L₁
  let I₂ := (I.erase i₀).filter fun i => ¬ ℓ i ⊆ L₁
  have hmem : ∀ {i}, i ∈ I → i ≠ i₀ → ℓ i ⊆ L₁ ∨ ℓ i ⊆ L₂ := fun {i} hi hne => by
    have h0 : ℓ i ⊆ L₁ ∪ L₂ := fun z hz => by
      have h3 : z ∈ L₁ ∪ ℓ i₀ ∪ L₂ := hU ▸ (hsub i hi).1 hz
      rcases h3 with (h3 | h3) | h3
      · exact .inl h3
      · exact (disjoint_left.mp (hdis i i₀ hne) hz h3).elim
      · exact .inr h3
    exact preconnected_side (hℓ i).isPreconnected_self h₁.isCompact.isClosed h₂.isCompact.isClosed
      h0
      (by rw [disjoint_iff_inter_eq_empty.mp hD]; exact disjoint_empty _)
  have hc₁ : I₁.card < n := by
    have h3 : I₁.card ≤ (I.erase i₀).card := Finset.card_filter_le _ _
    rw [Finset.card_erase_of_mem hi₀] at h3
    have := Finset.card_pos.mpr ⟨i₀, hi₀⟩
    omega
  have hc₂ : I₂.card < n := by
    have h3 : I₂.card ≤ (I.erase i₀).card := Finset.card_filter_le _ _
    rw [Finset.card_erase_of_mem hi₀] at h3
    have := Finset.card_pos.mpr ⟨i₀, hi₀⟩
    omega
  have hmem₁ : ∀ {i}, i ∈ I₁ → i ∈ I ∧ i ≠ i₀ ∧ ℓ i ⊆ L₁ := fun {i} hi => by
    have := Finset.mem_filter.mp hi
    exact ⟨(Finset.mem_erase.mp this.1).2, (Finset.mem_erase.mp this.1).1, this.2⟩
  have hmem₂ : ∀ {i}, i ∈ I₂ → i ∈ I ∧ i ≠ i₀ ∧ ℓ i ⊆ L₂ := fun {i} hi => by
    have := Finset.mem_filter.mp hi
    have h3 := (Finset.mem_erase.mp this.1)
    exact ⟨h3.2, h3.1, (hmem h3.2 h3.1).resolve_left this.2⟩
  have hoff : ∀ {i z}, i ≠ i₀ → z ∈ ℓ i₀ → z ∉ ℓ i := fun {i z} hne h1 h2 => disjoint_left.mp
    (hdis i i₀ hne) h2 h1
  obtain ⟨𝓐₁, c₁⟩ := ih _ hc₁ I₁ rfl L₁ u x h₁ (fun e => hu₀ (e ▸ hxm)) fun i hi => by
    obtain ⟨a1, a2, a3⟩ := hmem₁ hi
    exact ⟨a3, (hsub i a1).2.1, hoff a2 hxm⟩
  obtain ⟨𝓐₂, c₂⟩ := ih _ hc₂ I₂ rfl L₂ y v h₂ (fun e => hv₀ (e ▸ hym)) fun i hi => by
    obtain ⟨a1, a2, a3⟩ := hmem₂ hi
    exact ⟨a3, hoff a2 hym, (hsub i a1).2.2⟩
  have hxy' : ∀ z, z = s i₀ ∨ z = t i₀ → z ∈ L₁ → z = x := fun z hz h1 => by
    have : z ∈ ℓ i₀ := by
      rcases hz with rfl | rfl
      · exact (hℓ i₀).left_mem
      · exact (hℓ i₀).right_mem
    have h2 : z ∈ L₁ ∩ ℓ i₀ := ⟨h1, this⟩
    rwa [hI₁] at h2
  have hyy' : ∀ z, z = s i₀ ∨ z = t i₀ → z ∈ L₂ → z = y := fun z hz h1 => by
    have : z ∈ ℓ i₀ := by
      rcases hz with rfl | rfl
      · exact (hℓ i₀).left_mem
      · exact (hℓ i₀).right_mem
    have h2 : z ∈ L₂ ∩ ℓ i₀ := ⟨h1, this⟩
    rwa [hI₂] at h2
  have hsplit : ∀ i ∈ I, i = i₀ ∨ i ∈ I₁ ∨ i ∈ I₂ := fun i hi => by
    by_cases h : i = i₀
    · exact .inl h
    · refine .inr ?_
      by_cases h2 : ℓ i ⊆ L₁
      · exact .inl (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h, hi⟩, h2⟩)
      · exact .inr (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h, hi⟩, h2⟩)
  have hends : ∀ {i z}, z ∈ ({s i, t i} : Set S) → z ∈ ℓ i := fun {i z} hz => by
    rcases hz with rfl | rfl
    · exact (hℓ i).left_mem
    · exact (hℓ i).right_mem
  have hxB : x = s i₀ ∨ x = t i₀ := by tauto
  have hyB : y = s i₀ ∨ y = t i₀ := by tauto
  have hend₁ : ∀ i ∈ I₁, ∀ z ∈ ({s i, t i} : Set S), z ∈ cutEnds s t I := fun i hi z hz =>
    mem_iUnion₂.mpr ⟨i, (hmem₁ hi).1, hz⟩
  have hend₂ : ∀ i ∈ I₂, ∀ z ∈ ({s i, t i} : Set S), z ∈ cutEnds s t I := fun i hi z hz =>
    mem_iUnion₂.mpr ⟨i, (hmem₂ hi).1, hz⟩
  have hex : x ∈ cutEnds s t I := mem_iUnion₂.mpr ⟨i₀, hi₀, hxB⟩
  have hey : y ∈ cutEnds s t I := mem_iUnion₂.mpr ⟨i₀, hi₀, hyB⟩
  refine ⟨𝓐₁ ∪ 𝓐₂, ⟨c₁.finite.union c₂.finite, ?_, ?_, ?_, ?_⟩⟩
  · rintro A (hA | hA)
    · obtain ⟨a, c, h3, h4, h5, h6⟩ := c₁.line A hA
      refine ⟨a, c, h3, h4, h5.trans hLin₁, ?_⟩
      rw [← h6]
      ext z
      constructor
      · rintro ⟨hz, h7⟩
        refine ⟨hz, ?_⟩
        rcases h7 with (rfl | rfl) | h7
        · exact .inl (.inl rfl)
        · exact (disjoint_left.mp hD (h5 hz) h₂.right_mem).elim
        · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h7
          rcases hsplit i hi with rfl | h8 | h8
          · exact .inl (.inr (hxy' z hzi (h5 hz)))
          · exact .inr (mem_iUnion₂.mpr ⟨i, h8, hzi⟩)
          · exact (disjoint_left.mp hD (h5 hz) ((hmem₂ h8).2.2 (hends hzi))).elim
      · rintro ⟨hz, h7⟩
        refine ⟨hz, ?_⟩
        rcases h7 with (rfl | rfl) | h7
        · exact .inl (.inl rfl)
        · exact .inr hex
        · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h7
          exact .inr (hend₁ i hi z hzi)
    · obtain ⟨a, c, h3, h4, h5, h6⟩ := c₂.line A hA
      refine ⟨a, c, h3, h4, h5.trans hLin₂, ?_⟩
      rw [← h6]
      ext z
      constructor
      · rintro ⟨hz, h7⟩
        refine ⟨hz, ?_⟩
        rcases h7 with (rfl | rfl) | h7
        · exact (disjoint_left.mp hD h₁.left_mem (h5 hz)).elim
        · exact .inl (.inr rfl)
        · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h7
          rcases hsplit i hi with rfl | h8 | h8
          · exact .inl (.inl (hyy' z hzi (h5 hz)))
          · exact (disjoint_left.mp hD ((hmem₁ h8).2.2 (hends hzi)) (h5 hz)).elim
          · exact .inr (mem_iUnion₂.mpr ⟨i, h8, hzi⟩)
      · rintro ⟨hz, h7⟩
        refine ⟨hz, ?_⟩
        rcases h7 with (rfl | rfl) | h7
        · exact .inr hey
        · exact .inl (.inr rfl)
        · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h7
          exact .inr (hend₂ i hi z hzi)
  · have hsubA : ∀ A ∈ 𝓐₁, A ⊆ L₁ := fun A hA => by
      obtain ⟨a, c, -, -, h5, -⟩ := c₁.line A hA
      exact h5
    have hsubB : ∀ A ∈ 𝓐₂, A ⊆ L₂ := fun A hA => by
      obtain ⟨a, c, -, -, h5, -⟩ := c₂.line A hA
      exact h5
    rintro A (hA | hA) A' (hA' | hA') hne
    · exact c₁.disj A hA A' hA' hne
    · exact hD.mono (hsubA A hA) (hsubB A' hA')
    · exact (hD.mono (hsubA A' hA') (hsubB A hA)).symm
    · exact c₂.disj A hA A' hA' hne
  · intro z hz
    have h3 : z ∈ L₁ ∪ ℓ i₀ ∪ L₂ := hU ▸ hz
    have lhs : z ∈ L₁ → (∃ A ∈ 𝓐₁ ∪ 𝓐₂, z ∈ A) ∨ ∃ i ∈ I, z ∈ ℓ i ∧ z ≠ s i ∧ z ≠ t i := fun h4
      => by
      rcases c₁.cover z h4 with ⟨A, hA, h5⟩ | ⟨i, hi, h5⟩
      · exact .inl ⟨A, .inl hA, h5⟩
      · exact .inr ⟨i, (hmem₁ hi).1, h5⟩
    have rhs : z ∈ L₂ → (∃ A ∈ 𝓐₁ ∪ 𝓐₂, z ∈ A) ∨ ∃ i ∈ I, z ∈ ℓ i ∧ z ≠ s i ∧ z ≠ t i := fun h4
      => by
      rcases c₂.cover z h4 with ⟨A, hA, h5⟩ | ⟨i, hi, h5⟩
      · exact .inl ⟨A, .inr hA, h5⟩
      · exact .inr ⟨i, (hmem₂ hi).1, h5⟩
    rcases h3 with (h3 | h3) | h3
    · exact lhs h3
    · by_cases h4 : z = x
      · exact lhs (h4 ▸ h₁.right_mem)
      by_cases h5 : z = y
      · exact rhs (h5 ▸ h₂.left_mem)
      refine .inr ⟨i₀, hi₀, h3, fun e => ?_, fun e => ?_⟩
      · rcases hxy with ⟨h6, h7⟩ | ⟨h6, h7⟩
        · exact h4 (e.trans h6.symm)
        · exact h5 (e.trans h7.symm)
      · rcases hxy with ⟨h6, h7⟩ | ⟨h6, h7⟩
        · exact h5 (e.trans h7.symm)
        · exact h4 (e.trans h6.symm)
    · exact rhs h3
  · rintro A (hA | hA) i hi z hz hzi
    · obtain ⟨a, c, -, -, h5, -⟩ := c₁.line A hA
      rcases hsplit i hi with rfl | h8 | h8
      · have : z ∈ L₁ ∩ ℓ i := ⟨h5 hz, hzi⟩
        rw [hI₁] at this
        exact (mem_singleton_iff.mp this).symm ▸ hxB
      · exact c₁.meet A hA i h8 z hz hzi
      · exact (disjoint_left.mp hD (h5 hz) ((hmem₂ h8).2.2 hzi)).elim
    · obtain ⟨a, c, -, -, h5, -⟩ := c₂.line A hA
      rcases hsplit i hi with rfl | h8 | h8
      · have : z ∈ L₂ ∩ ℓ i := ⟨h5 hz, hzi⟩
        rw [hI₂] at this
        exact (mem_singleton_iff.mp this).symm ▸ hyB
      · exact (disjoint_left.mp hD ((hmem₁ h8).2.2 hzi) (h5 hz)).elim
      · exact c₂.meet A hA i h8 z hz hzi

/-- **Cutting an `O`-arc.** An `O`-arc with disjoint sub-lines `ℓ i` for `i ∈ I`, where `I` is not
empty, is cut into lines. -/
theorem exists_cut_oArc {ι : Type*} {ℓ : ι → Set S} {s t : ι → S}
  (hℓ : ∀ i, IsLineWithEnds (ℓ i) (s i) (t i))
    (hst : ∀ i, s i ≠ t i) (hdis : ∀ i j, i ≠ j → Disjoint (ℓ i) (ℓ j)) {F : Set S}
      (hF : IsOArc F) {I : Finset ι} (hne : I.Nonempty)
    (hsub : ∀ i ∈ I, ℓ i ⊆ F) : ∃ 𝓐, IsCut ℓ s t I F (cutEnds s t I) 𝓐 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  have hm : s i₀ ∈ F := hsub i₀ hi₀ (hℓ i₀).left_mem
  have hm' : t i₀ ∈ F := hsub i₀ hi₀ (hℓ i₀).right_mem
  obtain ⟨A, B, hA, hB, hU, hI⟩ := hF.lines hm hm' (hst i₀)
  have hd : Disjoint (ℓ i₀ \ {s i₀, t i₀}) (A ∩ B) := by
    rw [hI]
    exact disjoint_left.mpr fun x hx h => hx.2 h
  have key : ∃ L, IsLineWithEnds L (s i₀) (t i₀) ∧ L ∪ ℓ i₀ = F ∧ L ∩ ℓ i₀ = {s i₀, t i₀} := by
    rcases preconnected_side (hℓ i₀).isPreconnected_diff hA.isCompact.isClosed hB.isCompact.isClosed
      (fun x hx => hU ▸ hsub i₀ hi₀ hx.1) hd with h | h
    · have e := hA.eq_of_subset (hℓ i₀).isPreconnected_self (line_subset_of_inner
        (hℓ i₀) hA.isCompact.isClosed h)
        (hℓ i₀).left_mem (hℓ i₀).right_mem
      rw [e]
      exact ⟨B, hB, by rw [union_comm, hU], by rw [inter_comm, hI]⟩
    · have e := hB.eq_of_subset (hℓ i₀).isPreconnected_self (line_subset_of_inner
        (hℓ i₀) hB.isCompact.isClosed h)
        (hℓ i₀).left_mem (hℓ i₀).right_mem
      rw [e]
      exact ⟨A, hA, hU, hI⟩
  obtain ⟨L, hL, hLU, hLI⟩ := key
  have hoff : ∀ {i z}, i ≠ i₀ → z ∈ ℓ i₀ → z ∉ ℓ i := fun {i z} hne h1 h2 => disjoint_left.mp
    (hdis i i₀ hne) h2 h1
  obtain ⟨𝓐, c⟩ := exists_cut_line hℓ hst hdis _ (I.erase i₀) rfl L _ _ hL (hst i₀) fun i hi => by
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hi
    refine ⟨fun z hz => ?_, hoff h1 (hℓ i₀).left_mem, hoff h1 (hℓ i₀).right_mem⟩
    have : z ∈ L ∪ ℓ i₀ := hLU ▸ hsub i h2 hz
    exact this.resolve_right (hoff h1 · hz)
  refine ⟨𝓐, ⟨c.finite, fun A hA => ?_, c.disj, fun x hx => ?_, fun A hA i hi x hx hxi => ?_⟩⟩
  · obtain ⟨a, b, h1, h2, h3, h4⟩ := c.line A hA
    refine ⟨a, b, h1, h2, h3.trans (hLU ▸ subset_union_left), ?_⟩
    rw [← h4]
    ext z
    constructor
    · rintro ⟨hz, h5⟩
      refine ⟨hz, ?_⟩
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h5
      by_cases h : i = i₀
      · subst h
        exact .inl hzi
      · exact .inr (mem_iUnion₂.mpr ⟨i, Finset.mem_erase.mpr ⟨h, hi⟩, hzi⟩)
    · rintro ⟨hz, h5⟩
      refine ⟨hz, ?_⟩
      rcases h5 with h5 | h5
      · exact mem_iUnion₂.mpr ⟨i₀, hi₀, h5⟩
      · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp h5
        exact mem_iUnion₂.mpr ⟨i, (Finset.mem_erase.mp hi).2, hzi⟩
  · have h1 : x ∈ L ∪ ℓ i₀ := hLU ▸ hx
    by_cases hx₀ : x ∈ L
    · rcases c.cover x hx₀ with h | ⟨i, hi, h⟩
      · exact .inl h
      · exact .inr ⟨i, (Finset.mem_erase.mp hi).2, h⟩
    · have h2 := h1.resolve_left hx₀
      refine .inr ⟨i₀, hi₀, h2, fun e => hx₀ (e ▸ hL.left_mem), fun e => hx₀ (e ▸ hL.right_mem)⟩
  · by_cases h : i = i₀
    · obtain ⟨a, b, -, -, h3, -⟩ := c.line A hA
      have : x ∈ L ∩ ℓ i₀ := ⟨h3 hx, h ▸ hxi⟩
      rw [hLI] at this
      rw [h]
      exact this
    · exact c.meet A hA i (Finset.mem_erase.mpr ⟨h, hi⟩) x hx hxi

private theorem matching_drawing_has_valency_one
    {S : Type}
    [TopologicalSpace S]
    (𝓑 : Set (Set S)) (V : Set S)
    (hAdisj : ∀ A ∈ 𝓑, ∀ A' ∈ 𝓑, A ≠ A' → Disjoint A A')
    (ea : Set S → S)
    (eb : Set S → S)
    (G : Drawing S)
    (hGV : G.V = V)
    (hGE : G.E = (fun i => id i \ {ea i, eb i}) '' 𝓑)
    (hAclo : ∀ A ∈ 𝓑, closure (A \ {ea A, eb A}) = A)
    (htilde : ∀ A ∈ 𝓑, (tilde (A \ {ea A, eb A})).ncard = 2)
    (hexA : ∀ v ∈ V, ∃ A ∈ 𝓑, v ∈ A) :
    ∀ v ∈ V, vertexValency G v = 1 := by
  intro v hv
  obtain ⟨A, hA, hvA⟩ := hexA v hv
  have h1 : {e ∈ G.E | G.VertexIncident v e ∧ (tilde e).ncard = 2} = {A \ {ea A, eb A}} := by
    ext e
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨h2, ⟨-, -, h3⟩, -⟩
      rw [hGE] at h2
      obtain ⟨A', hA', rfl⟩ := h2
      simp only [id] at h3 ⊢
      rw [hAclo A' hA'] at h3
      by_cases h : A = A'
      · rw [h]
      · exact (disjoint_left.mp (hAdisj A hA A' hA' h) hvA h3).elim
    · rintro rfl
      have hmem : A \ {ea A, eb A} ∈ G.E := hGE ▸ ⟨A, hA, rfl⟩
      refine ⟨hmem, ⟨hGV ▸ hv, .inl hmem, ?_⟩, htilde A hA⟩
      rw [hAclo A hA]
      exact hvA
  have h2 : {e ∈ G.E | G.VertexIncident v e ∧ (tilde e).ncard = 1} = ∅ := by
    ext e
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    rintro h3 - h4
    rw [hGE] at h3
    obtain ⟨A', hA', rfl⟩ := h3
    have := htilde A' hA'
    simp only [id] at h4
    omega
  unfold vertexValency
  rw [h1, h2, ncard_singleton, ncard_empty]

private theorem matching_disc_complement_is_simply_connected_region
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    {Y : Set S}
    {c : S → Set S}
    {ℓ : S → Set S}
    {s : S → S}
    {t : S → S}
    (hd : ∀ y ∈ Y, IsClosedDisc (c y))
    (hop : ∀ y ∈ Y, IsOpen (discInt (c y)))
    (hℓ : ∀ y ∈ Y, IsLineWithEnds (ℓ y) (s y) (t y) ∧ s y ≠ t y ∧ ℓ y ⊆ discBd (c y) ∧ ℓ y ⊆ bd S
      ∧ y ∈ ℓ y ∧ y ≠ s y ∧ y ≠ t y ∧ ∃ O, IsOpen O ∧ ℓ y \ {s y, t y} ⊆ O ∧ O ⊆ c y)
    (hsame : ∀ {u v z : S}, u ∈ Y → v ∈ Y → z ∈ c u → z ∈ c v → c u = c v)
    (I : Set S → Finset Y) (hI : ∀ D i, i ∈ I D → c i.1 = D)
    (𝓐 : ↑(range fun i : Y => c i.1) → Set (Set S))
    (hC : ∀ (D : ↑(range fun i : Y => c i.1)),
      IsCut (fun i : Y => ℓ i.1) (fun i : Y => s i.1) (fun i : Y => t i.1) (I ↑D) (discBd ↑D)
        (cutEnds (fun i : Y => s i.1) (fun i : Y => t i.1) (I ↑D)) (𝓐 D))
    (V : Set S)
    (G : Drawing S)
    (hGU : G.U = V ∪ ⋃ i ∈ (⋃ D, 𝓐 D), id i)
    (hUbd : ∀ z ∈ G.U, ∃ i : Y, z ∈ discBd (c i.1))
    (hyn : ∀ (i : ↑Y), ↑i ∉ G.U) :
    ∀ (y : ↑Y), c ↑y \ G.U ∈ G.R ∧ IsSimplyConnectedSubset (c ↑y \ G.U) := by
  let ℓ' := fun i : Y => ℓ i.1
  let s' := fun i : Y => s i.1
  let t' := fun i : Y => t i.1
  let 𝒟 := range fun i : Y => c i.1
  intro y
  have hDy := hd _ y.2
  have hyc := (hℓ y y.2).2.2.1 |>.trans (GM11.discBd_subset _) (hℓ y y.2).2.2.2.2.1
  have hin : c y.1 ∩ G.U ⊆ discBd (c y.1) := fun z hz => by
    obtain ⟨i, hi⟩ := hUbd z hz.2
    have h1 := hsame y.2 i.2 hz.1 (GM11.discBd_subset _ hi)
    exact h1 ▸ hi
  have hrw : c y.1 \ G.U = c y.1 \ (c y.1 ∩ G.U) := by simp
  have h1 := isSimplyConnected_disc_sdiff hDy hin
  rw [← hrw] at h1
  refine ⟨?_, h1.1⟩
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem (hyn y)
  have hrU : Disjoint r G.U := disjoint_left.mpr fun z h2 h3 => by
    obtain ⟨z', -, rfl⟩ := (mem_R_iff G).mp hr
    exact (connectedComponentIn_subset _ _ h2).2 h3
  have hsub : c y.1 \ G.U ⊆ r := subset_region hr h1.2 (disjoint_left.mpr fun z h2 h3
    => h2.2 h3) ⟨hyc, hyn y⟩ hyr
  obtain ⟨-, -, -, -, -, -, -, hO⟩ := hℓ y y.2
  let D : 𝒟 := ⟨c y.1, y, rfl⟩
  have hOi : ∀ i : Y, ∃ O, IsOpen O ∧ ℓ' i \ {s' i, t' i} ⊆ O ∧ O ⊆ c i.1 := fun i =>
    (hℓ i i.2).2.2.2.2.2.2.2
  choose Ω hΩo hΩs hΩc using hOi
  let W : Set S := discInt (c y.1) ∪ ⋃ i ∈ I D.1, Ω i
  have hWo : IsOpen W := (hop _ y.2).union (isOpen_biUnion fun i _ => hΩo i)
  have hWc : W ⊆ c y.1 := by
    rintro z (hz | hz)
    · exact hz.1
    · obtain ⟨i, hi, h2⟩ := mem_iUnion₂.mp hz
      have := hΩc i h2
      rwa [hI _ _ hi] at this
  have hcovW : c y.1 \ G.U ⊆ W := fun z hz => by
    by_cases h2 : z ∈ discBd (c y.1)
    · refine .inr ?_
      rcases (hC D).cover z h2 with ⟨A, hA, h3⟩ | ⟨i, hi, h3, h4, h5⟩
      · exact (hz.2 (hGU ▸ .inr (mem_iUnion₂.mpr ⟨A, mem_iUnion.mpr ⟨D, hA⟩, h3⟩))).elim
      · refine mem_iUnion₂.mpr ⟨i, hi, hΩs i ⟨h3, ?_⟩⟩
        rintro (h6 | h6)
        · exact h4 h6
        · exact h5 h6
    · exact .inl ⟨hz.1, h2⟩
  have hrc : r ⊆ c y.1 := by
    have hconn : IsPreconnected r := by
      obtain ⟨z', -, rfl⟩ := (mem_R_iff G).mp hr
      exact isPreconnected_connectedComponentIn
    have hs : r ⊆ c y.1 ∪ Wᶜ := fun z hz => by
      by_cases h2 : z ∈ W
      · exact .inl (hWc h2)
      · exact .inr h2
    have hd2 : Disjoint r (c y.1 ∩ Wᶜ) := disjoint_left.mpr fun z h2 h3 =>
      h3.2 (hcovW ⟨h3.1, disjoint_left.mp hrU h2⟩)
    refine (preconnected_side hconn hDy.isClosed hWo.isClosed_compl hs hd2).resolve_right fun h2
      => h2 hyr (hcovW ⟨hyc, hyn y⟩)
  have : r = c y.1 \ G.U := subset_antisymm (fun z hz => ⟨hrc hz, disjoint_left.mp hrU hz⟩) hsub
  exact this ▸ hr

private theorem connected_drawing_subset_of_closed_edge_condition
    {S : Type} [TopologicalSpace S] (H' : Drawing S) {D : Set S} {y : S}
    (hyV : y ∈ H'.V) (hyc : y ∈ D) (hconn : H'.IsConnected)
    (hcl : ∀ e ∈ H'.E, ∀ u ∈ H'.V, u ∈ closure e → u ∈ D → closure e ⊆ D) :
    H'.U ⊆ D := by
  have hlink : ∀ {a b}, ∀ _ : GraphWalk H'.toGraph a b, a ∈ H'.V → a ∈ D → b ∈ D := by
    intro a b W
    induction W with
    | nil _ => exact fun _ h => h
    | @cons x w z e₀ h _ ih =>
      intro hx hxc
      obtain ⟨he, hx', hw', hcap⟩ := h
      have hxw : x ∈ ({x, w} : Set S) ∧ w ∈ ({x, w} : Set S) := ⟨.inl rfl, .inr rfl⟩
      rw [← hcap] at hxw
      exact ih hw' (hcl _ he x hx' hxw.1.1 hxc hxw.2.1)
  have hcy : ∀ v ∈ H'.V, v ∈ D := fun v hv => by
    obtain ⟨W⟩ := hconn.2 y hyV v hv
    exact hlink W hyV hyc
  intro z hz
  by_cases hzV : z ∈ H'.V
  · exact hcy z hzV
  · obtain ⟨e, he, hze⟩ := H'.exists_edge_of_mem hz hzV
    obtain ⟨u, huc, huV⟩ : ∃ u ∈ closure e, u ∈ H'.V := by
      rcases H'.edge_cond e he with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
      · exact ⟨u, (hcap ▸ (Or.inl rfl) : u ∈ closure e ∩ H'.V)⟩
      · exact ⟨u, (hcap ▸ rfl : u ∈ closure e ∩ H'.V)⟩
    exact hcl e he u huV huc (hcy u huV) (subset_closure hze)

/-- **The matching around discs.** Given discs `c y` for `y ∈ Y`, and pieces `ℓ y` of their
boundaries, the lines left when we cut the
boundaries at the `ℓ y` form a matching `G`. It strictly surrounds every drawing `H` with `V(H) ∩
bd(Σ) = Y` that respects the discs:
points of `Y` in one disc are joined in `H`, an edge of `H` that has an end in a disc lies in this
disc, and `H` meets the boundaries of
the discs only in `Y`. -/
theorem exists_matching_of_discs {Y : Set S} (hYf : Y.Finite) {c ℓ : S → Set S} {s t : S → S}
    (hd : ∀ y ∈ Y, IsClosedDisc (c y)) (hop : ∀ y ∈ Y, IsOpen (discInt (c y)))
    (hdis : ∀ u ∈ Y, ∀ v ∈ Y, c u ≠ c v → Disjoint (c u) (c v))
    (hℓ : ∀ y ∈ Y, IsLineWithEnds (ℓ y) (s y) (t y) ∧ s y ≠ t y ∧ ℓ y ⊆ discBd (c y) ∧ ℓ y ⊆ bd S
      ∧ y ∈ ℓ y ∧ y ≠ s y ∧ y ≠ t y ∧
      ∃ O, IsOpen O ∧ ℓ y \ {s y, t y} ⊆ O ∧ O ⊆ c y)
    (hℓd : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → Disjoint (ℓ y) (ℓ y')) (hbd : ∀ y ∈ Y, c y ∩ bd S ⊆ ⋃ y' ∈
      Y, ℓ y') :
    ∃ G : Drawing S, IsMatching G ∧ G.V = (⋃ y ∈ Y, {s y, t y}) ∧ G.U ⊆ ⋃ y ∈ Y, discBd (c y)
      ∧ ∀ H : Drawing S, H.V ∩ bd S = Y →
      (∀ u ∈ Y, ∀ v ∈ Y, c u = c v → Nonempty (GraphWalk H.toGraph u v)) →
      (∀ e ∈ H.E, ∀ u ∈ H.V, ∀ y ∈ Y, u ∈ closure e → u ∈ c y → closure e ⊆ c y) →
      (∀ y ∈ Y, ∀ z ∈ H.U, z ∈ discBd (c y) → z ∈ Y) → MatchingStrictlySurroundsForest G H := by
  classical
  rcases isEmpty_or_nonempty S with hE | hN
  · refine ⟨GM07.emptyDrawing S, ⟨fun x => (hE.false x).elim, fun x => (hE.false x).elim,
      fun x => (hE.false x).elim⟩, ?_, ?_, fun H _ _ _ _ => ⟨⟨?_, ?_⟩, ?_⟩⟩
    · ext x
      exact (hE.false x).elim
    · intro x
      exact (hE.false x).elim
    · ext x
      exact (hE.false x).elim
    · rintro H' - - ⟨x, -⟩
      exact (hE.false x).elim
    · intro x
      exact (hE.false x).elim
  have : Inhabited S := ⟨hN.some⟩
  have hYfin : Y.Finite := hYf
  have : Finite Y := hYfin.to_subtype
  have : Fintype Y := Fintype.ofFinite _
  let ℓ' : Y → Set S := fun i => ℓ i.1
  let s' : Y → S := fun i => s i.1
  let t' : Y → S := fun i => t i.1
  have hℓ' : ∀ i : Y, IsLineWithEnds (ℓ' i) (s' i) (t' i) := fun i => (hℓ i i.2).1
  have hst' : ∀ i : Y, s' i ≠ t' i := fun i => (hℓ i i.2).2.1
  have hdis' : ∀ i j : Y, i ≠ j → Disjoint (ℓ' i) (ℓ' j) := fun i j h =>
    hℓd _ i.2 _ j.2 fun e => h (Subtype.ext e)
  have hsame : ∀ {u v z}, u ∈ Y → v ∈ Y → z ∈ c u → z ∈ c v → c u = c v := fun {u v z} hu hv h1 h2
    => by
    by_contra hn
    exact disjoint_left.mp (hdis u hu v hv hn) h1 h2
  have hℓc : ∀ i : Y, ∀ z ∈ ℓ' i, z ∈ discBd (c i.1) := fun i z hz => (hℓ i i.2).2.2.1 hz
  let 𝒟 : Set (Set S) := range fun i : Y => c i.1
  have h𝒟fin : 𝒟.Finite := finite_range _
  have : Finite 𝒟 := h𝒟fin.to_subtype
  let I : Set S → Finset Y := fun D => Finset.univ.filter fun i => c i.1 = D
  have hcut : ∀ D : 𝒟, ∃ 𝓐, IsCut ℓ' s' t' (I D.1) (discBd D.1) (cutEnds s' t' (I D.1)) 𝓐 := by
    rintro ⟨_, y, rfl⟩
    refine exists_cut_oArc hℓ' hst' hdis' (hd _ y.2).isOArc_discBd ⟨y,
      by simp [I]⟩ fun i hi z hz => ?_
    have := hℓc i z hz
    rwa [(Finset.mem_filter.mp hi).2] at this
  choose 𝓐 hC using hcut
  let 𝓑 : Set (Set S) := ⋃ D, 𝓐 D
  have h𝓑fin : 𝓑.Finite := finite_iUnion fun D => (hC D).finite
  let V : Set S := ⋃ y ∈ Y, {s y, t y}
  have hVfin : V.Finite := hYfin.biUnion fun y _ => by simp
  have hDc : ∀ D : 𝒟, ∃ y : Y, c y.1 = D.1 := fun D => D.2
  have hAsub : ∀ {D A}, A ∈ 𝓐 D → A ⊆ discBd D.1 := fun {D A} hA => by
    obtain ⟨a, b, -, -, h3, -⟩ := (hC D).line A hA
    exact h3
  have hclass : ∀ (D : 𝒟) (i : Y) z, z ∈ discBd D.1 → z ∈ ℓ' i → i ∈ I D.1 := fun D i z h1 h2 => by
    obtain ⟨y, hy⟩ := hDc D
    have h3 : z ∈ c y.1 := hy ▸ GM11.discBd_subset _ h1
    have h4 := hsame i.2 y.2 (GM11.discBd_subset _ (hℓc i z h2)) h3
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h4.trans hy⟩
  have hVend : ∀ {z}, z ∈ V → ∃ i : Y, (z = s' i ∨ z = t' i) ∧ z ∈ ℓ' i := fun {z} hz => by
    obtain ⟨y, hy, h1⟩ := mem_iUnion₂.mp hz
    refine ⟨⟨y, hy⟩, h1, ?_⟩
    rcases h1 with rfl | rfl
    · exact (hℓ' ⟨y, hy⟩).left_mem
    · exact (hℓ' ⟨y, hy⟩).right_mem
  have hAV : ∀ D, ∀ A ∈ 𝓐 D, A ∩ V = A ∩ cutEnds s' t' (I D.1) := fun D A hA => by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨i, h3, h4⟩ := hVend h2
      exact ⟨h1, mem_iUnion₂.mpr ⟨i, hclass D i z (hAsub hA h1) h4, h3⟩⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨i, -, h3⟩ := mem_iUnion₂.mp h2
      exact ⟨h1, mem_iUnion₂.mpr ⟨i.1, i.2, h3⟩⟩
  have hline : ∀ A ∈ 𝓑, ∃ a b, IsLineWithEnds A a b ∧ a ≠ b ∧ A ∩ V = {a, b} := fun A hA => by
    obtain ⟨D, hA⟩ := mem_iUnion.mp hA
    obtain ⟨a, b, h1, h2, -, h4⟩ := (hC D).line A hA
    exact ⟨a, b, h1, h2, by rw [hAV D A hA, h4]⟩
  have hAdisj : ∀ A ∈ 𝓑, ∀ A' ∈ 𝓑, A ≠ A' → Disjoint A A' := fun A hA A' hA' hne => by
    obtain ⟨D, hA⟩ := mem_iUnion.mp hA
    obtain ⟨D', hA'⟩ := mem_iUnion.mp hA'
    by_cases h : D = D'
    · subst h
      exact (hC D).disj A hA A' hA' hne
    · obtain ⟨y, hy⟩ := hDc D
      obtain ⟨y', hy'⟩ := hDc D'
      refine (hdis _ y.2 _ y'.2 fun e => h (Subtype.ext (hy.symm.trans (e.trans hy')))).mono ?_ ?_
      · exact fun z hz => hy ▸ GM11.discBd_subset _ (hAsub hA hz)
      · exact fun z hz => hy' ▸ GM11.discBd_subset _ (hAsub hA' hz)
  choose! ea eb hla hne hVA using hline
  obtain ⟨G, hGU, hGV, hGE⟩ := GM12.exists_drawing_of_finite_lines hVfin h𝓑fin id ea eb hla hne hVA
    fun A hA A' hA' h => by
      change A ∩ A' ⊆ V
      rw [disjoint_iff_inter_eq_empty.mp (hAdisj A hA A' hA' h)]
      exact empty_subset _
  -- Points of `G`.
  have hUVsub : V ⊆ ⋃ i : Y, discBd (c i.1) := fun z hz => by
    obtain ⟨i, -, h⟩ := hVend hz
    exact mem_iUnion.mpr ⟨i, hℓc i z h⟩
  have hUbd : ∀ z ∈ G.U, ∃ i : Y, z ∈ discBd (c i.1) := fun z hz => by
    rw [hGU] at hz
    rcases hz with hz | hz
    · exact mem_iUnion.mp (hUVsub hz)
    · obtain ⟨A, hA, hzA⟩ := mem_iUnion₂.mp hz
      obtain ⟨D, hA⟩ := mem_iUnion.mp hA
      obtain ⟨y, hy⟩ := hDc D
      exact ⟨y, hy ▸ hAsub hA hzA⟩
  have hUℓ : ∀ z ∈ G.U, ∀ i : Y, z ∈ ℓ' i → z = s' i ∨ z = t' i := fun z hz i hzi => by
    rw [hGU] at hz
    rcases hz with hz | hz
    · obtain ⟨k, h1, h2⟩ := hVend hz
      by_cases h : k = i
      · exact h ▸ h1
      · exact (disjoint_left.mp (hdis' k i h) h2 hzi).elim
    · obtain ⟨A, hA, hzA⟩ := mem_iUnion₂.mp hz
      obtain ⟨D, hA⟩ := mem_iUnion.mp hA
      exact (hC D).meet A hA i (hclass D i z (hAsub hA hzA) hzi) z hzA hzi
  have hyn : ∀ i : Y, i.1 ∉ G.U := fun i h => by
    obtain ⟨-, -, -, -, h5, h6, h7, -⟩ := hℓ i i.2
    rcases hUℓ i.1 h i h5 with e | e
    · exact h6 e
    · exact h7 e
  have hUV : ∀ z ∈ G.U, z ∈ bd S → z ∈ V := fun z hz hzb => by
    obtain ⟨i, hi⟩ := hUbd z hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (hbd _ i.2 ⟨GM11.discBd_subset _ hi, hzb⟩)
    exact mem_iUnion₂.mpr ⟨y, hy, hUℓ z hz ⟨y, hy⟩ hzy⟩
  have hVb : ∀ z ∈ V, z ∈ bd S := fun z hz => by
    obtain ⟨i, -, h⟩ := hVend hz
    exact (hℓ i i.2).2.2.2.1 h
  -- The edges of `G`.
  have hAclo : ∀ A ∈ 𝓑, closure (A \ {ea A, eb A}) = A := fun A hA =>
    subset_antisymm (closure_minimal sdiff_subset (hla A hA).isCompact.isClosed)
      (hla A hA).subset_closure_diff
  have htilde : ∀ A ∈ 𝓑, (tilde (A \ {ea A, eb A})).ncard = 2 := fun A hA => by
    have h1 : tilde (A \ {ea A, eb A}) = {ea A, eb A} := by
      unfold tilde
      rw [hAclo A hA]
      ext z
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_and, not_not]
      constructor
      · rintro ⟨h2, h3⟩
        exact h3 h2
      · rintro (rfl | rfl)
        · exact ⟨(hla A hA).left_mem, fun _ => .inl rfl⟩
        · exact ⟨(hla A hA).right_mem, fun _ => .inr rfl⟩
    rw [h1, ncard_pair (hne A hA)]
  have hexA : ∀ v ∈ V, ∃ A ∈ 𝓑, v ∈ A := fun v hv => by
    obtain ⟨i, h1, h2⟩ := hVend hv
    let D : 𝒟 := ⟨c i.1, i, rfl⟩
    rcases (hC D).cover v (hℓc i v h2) with ⟨A, hA, h3⟩ | ⟨k, -, h3, h4, h5⟩
    · exact ⟨A, mem_iUnion.mpr ⟨D, hA⟩, h3⟩
    · have hk : k = i := by
        by_contra h
        exact disjoint_left.mp (hdis' k i h) h3 h2
      rw [hk] at h4 h5
      rcases h1 with h1 | h1
      · exact (h4 h1).elim
      · exact (h5 h1).elim
  have hval : ∀ v ∈ V, vertexValency G v = 1 := by
    exact matching_drawing_has_valency_one (S := S) 𝓑 V hAdisj ea eb G hGV hGE hAclo htilde hexA
  have hmatch : IsMatching G := by
    refine ⟨fun z hz => ?_, ?_, fun v hv => hval v (hGV ▸ hv)⟩
    · rw [hGV]
      exact hUV z hz.2 hz.1
    · rw [hGV]
      exact hVb
  -- The regions of `G`.
  have hreg : ∀ y : Y, c y.1 \ G.U ∈ G.R ∧ IsSimplyConnectedSubset (c y.1 \ G.U) := by
    exact matching_disc_complement_is_simply_connected_region (S := S) (Y := Y) (c := c) (ℓ := ℓ)
      (s := s) (t := t) hd hop hℓ hsame I (fun _ _ hi => (Finset.mem_filter.mp hi).2)
      𝓐 hC V G hGU hUbd hyn
  have hGUsub : G.U ⊆ ⋃ y ∈ Y, discBd (c y) := fun z hz => by
    obtain ⟨i, hi⟩ := hUbd z hz
    exact mem_iUnion₂.mpr ⟨i.1, i.2, hi⟩
  refine ⟨G, hmatch, hGV, hGUsub, fun H hHY hw hcl hbdU => ?_⟩
  have hYm : ∀ z, z ∈ H.V → z ∈ bd S → z ∈ Y := fun z h1 h2 => hHY ▸ (⟨h1, h2⟩ : z ∈ H.V ∩ bd S)
  have hdisj : Disjoint G.U H.U := disjoint_left.mpr fun z h1 h2 => by
    obtain ⟨i, hi⟩ := hUbd z h1
    exact hyn ⟨z, hbdU _ i.2 z h2 hi⟩ h1
  have hyc : ∀ y ∈ Y, y ∈ c y := fun y hy => GM11.discBd_subset _ ((hℓ y hy).2.2.1
    (hℓ y hy).2.2.2.2.1)
  refine ⟨⟨disjoint_iff_inter_eq_empty.mp hdisj, fun H' hsub hconn ⟨y, hyV, hyb⟩ => ?_⟩, ?_⟩
  · have hyY : y ∈ Y := hYm y (hsub.1 hyV) hyb
    let y' : Y := ⟨y, hyY⟩
    obtain ⟨hr, hrs⟩ := hreg y'
    refine ⟨_, hr, hrs, ?_⟩
    intro z hz
    refine ⟨connected_drawing_subset_of_closed_edge_condition H' hyV (hyc y hyY) hconn ?_ hz,
      fun h => disjoint_left.mp hdisj h (hsub.U_subset hz)⟩
    exact fun e he u hu => hcl e (hsub.2 he) u (hsub.1 hu) y hyY
  · rintro a ⟨haV, hab⟩ b ⟨hbV, hbb⟩ - r hr har hbr
    have haY := hYm a haV hab
    have hbY := hYm b hbV hbb
    let a' : Y := ⟨a, haY⟩
    have h1 := (hreg a').1
    have h2 : r = c a \ G.U := region_eq_of_mem hr h1 har ⟨hyc a haY, hyn a'⟩
    have h3 : b ∈ c a := (h2 ▸ hbr : b ∈ c a \ G.U).1
    obtain ⟨W⟩ := hw a haY b hbY (hsame haY hbY h3 (hyc b hbY))
    obtain ⟨W', hs, -, -⟩ := GraphWalk.exists_isSimple W
    exact ⟨W', hs⟩

end GraphMinor.GM07
