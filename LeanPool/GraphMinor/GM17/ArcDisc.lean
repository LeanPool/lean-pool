/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.PasteCuff
public import LeanPool.GraphMinor.Surface.DiscUnion
public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.Surface.ChartCells
public import LeanPool.GraphMinor.Surface.EdgeLoop

/-!
# A disc cut off by an `I`-arc

Let `F` be an `I`-arc of a surface with only its ends on the boundary, and let `Δ` be a closed disc
with `F ⊆ bd(Δ) ⊆ F ∪ bd(Σ)`. Then the
rest of `bd(Δ)` is an arc `I` of one cuff, `Δ` meets `bd(Σ)` exactly in `I`, and `Δ` is a
neighbourhood of each of its points off `F`
(`arc_disc_data`). To see the last claim at a point of `I`, paste a disc on the cuff. Then `Δ` and
the new disc form a larger disc with the point
in its inside. The three statements on such discs in Graph Minors XVII follow.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- A line in an `O`-arc has a complementary line with the same ends. -/
theorem oarc_split [T2Space S] {O L : Set S} {x y : S} (hO : IsOArc O) (hL : IsLineWithEnds L x y)
  (hs : L ⊆ O) :
    ∃ L', IsLineWithEnds L' x y ∧ L ∪ L' = O ∧ L ∩ L' = {x, y} := by
  have hne := hL.ne'
  have hx := hs hL.left_mem
  have hy := hs hL.right_mem
  obtain ⟨A, B, hA, hB, hu, hi⟩ := hO.lines hx hy hne
  have hp := hL.isPreconnected_diff
  have hcA : IsClosed A := hA.isCompact.isClosed
  have hcB : IsClosed B := hB.isCompact.isClosed
  have hcov : L \ {x, y} ⊆ A ∪ B := hu ▸ sdiff_subset.trans hs
  have key : ¬ ((L \ {x, y}) ∩ A).Nonempty ∨ ¬ ((L \ {x, y}) ∩ B).Nonempty := by
    by_contra h
    push Not at h
    obtain ⟨z, hz, hz'⟩ := isPreconnected_closed_iff.mp hp A B hcA hcB hcov h.1 h.2
    rw [hi] at hz'
    exact hz.2 hz'
  have hend : ∀ {P : Set S}, IsLineWithEnds P x y → L \ {x, y} ⊆ P → L = P := fun {P} hP hsub => by
    have hLc : IsPreconnected L := by
      obtain ⟨a, ha, hr, -, -⟩ := hL.exists_arc
      rw [← hr]
      exact isPreconnected_range ha.1
    refine hP.eq_of_subset hLc (fun z hz => ?_) hL.left_mem hL.right_mem
    by_cases h : z ∈ ({x, y} : Set S)
    · rcases h with rfl | rfl
      · exact hP.left_mem
      · exact hP.right_mem
    · exact hsub ⟨hz, h⟩
  rcases key with h | h
  · have h1 : L \ {x, y} ⊆ B := fun z hz => (hcov hz).resolve_left fun hA' => h ⟨z, hz, hA'⟩
    obtain rfl := hend hB h1
    exact ⟨A, hA, by rwa [union_comm], by rwa [inter_comm]⟩
  · have h1 : L \ {x, y} ⊆ A := fun z hz => (hcov hz).resolve_right fun hB' => h ⟨z, hz, hB'⟩
    obtain rfl := hend hA h1
    exact ⟨B, hB, hu, hi⟩

/-- The shape of a disc cut off by an `I`-arc. -/
theorem arc_disc_data {F Δ : Set S} {n₁ n₂ : S} (hS : IsSurface S) (hF : IsLineWithEnds F n₁ n₂)
  (hb : F ∩ bd S = {n₁, n₂}) (hΔ : IsClosedDisc Δ)
    (h1 : F ⊆ discBd Δ) (h2 : discBd Δ ⊆ F ∪ bd S) :
    ∃ I I' Θ, Θ ∈ cuffs S ∧ IsLineWithEnds I n₁ n₂ ∧ IsLineWithEnds I' n₁ n₂ ∧ I ∪ I' = Θ ∧ I ∩ I'
      = {n₁, n₂} ∧ F ∪ I = discBd Δ ∧ F ∩ I = {n₁, n₂} ∧
      Δ ∩ bd S = I ∧ ∀ x ∈ Δ \ F, Δ ∈ 𝓝 x := by
  have ht2 : T2Space S := hS.2.1
  have hman := hS.2.2
  obtain ⟨I, hI, hu, hi⟩ := oarc_split hΔ.isOArc_discBd hF h1
  have hn₁ : n₁ ∈ bd S := (hb ▸ mem_insert _ _ : n₁ ∈ F ∩ bd S).2
  have hn₂ : n₂ ∈ bd S := (hb ▸ mem_insert_of_mem _ rfl : n₂ ∈ F ∩ bd S).2
  have hIb : I ⊆ bd S := fun z hz => by
    by_cases h : z ∈ F
    · have h3 : z ∈ F ∩ I := ⟨h, hz⟩
      rw [hi] at h3
      rcases h3 with rfl | rfl
      · exact hn₁
      · exact hn₂
    · exact (h2 (hu ▸ .inr hz)).resolve_left h
  have hIc : IsPreconnected I := by
    obtain ⟨a, ha, hr, -, -⟩ := hI.exists_arc
    rw [← hr]
    exact isPreconnected_range ha.1
  have hΘ : connectedComponentIn (bd S) n₁ ∈ cuffs S := ⟨n₁, hn₁, rfl⟩
  have hIΘ := hIc.subset_connectedComponentIn hI.left_mem hIb
  obtain ⟨I', hI', hu', hi'⟩ := oarc_split ((cuff_statement.{0} S hS).2.2 _ hΘ) hI hIΘ
  have hsubΔ : discBd Δ ⊆ Δ := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hIΔ : I ⊆ Δ := fun z hz => hsubΔ (hu ▸ .inr hz)
  have hint : ∀ x ∈ Δ, x ∉ discBd Δ → Δ ∈ 𝓝 x := fun x hx hn =>
    Filter.mem_of_superset ((hΔ.isOpen_discInt hman).mem_nhds ⟨hx, hn⟩) sdiff_subset
  have hmeet : Δ ∩ bd S = I := by
    apply subset_antisymm
    · rintro x ⟨hx, hxb⟩
      have hd : x ∈ discBd Δ := by
        by_contra hn
        exact hxb (isInteriorPoint_of_mem_discInt hman hΔ ⟨hx, hn⟩)
      rw [← hu] at hd
      rcases hd with hd | hd
      · have h3 : x ∈ F ∩ bd S := ⟨hd, hxb⟩
        rw [hb] at h3
        rcases h3 with rfl | rfl
        · exact hI.left_mem
        · exact hI.right_mem
      · exact hd
    · exact fun z hz => ⟨hIΔ hz, hIb hz⟩
  refine ⟨I, I', _, hΘ, hI, hI', hu', hi', hu, hi, hmeet, fun x hx => ?_⟩
  by_cases hd : x ∈ discBd Δ
  swap
  · exact hint x hx.1 hd
  have hxI : x ∈ I := by
    rw [← hu] at hd
    exact hd.resolve_left hx.2
  obtain ⟨S', tS', ι, D, hS', hι, hD, hcov, hm, hDb, hbdS⟩ := paste_disc.{0} S _ hS hΘ
  have ht2' : T2Space S' := hS'.2.1
  obtain ⟨hL, -⟩ := IsLineWithEnds.map_of_embedding (L := I) (u := n₁) (v
    := n₂) hι.isEmbedding hI |> fun h => (⟨h, trivial⟩ : _ ∧ True)
  have hD' : ∀ y, ι y ∈ D ↔ y ∈ connectedComponentIn (bd S) n₁ := fun y => by
    constructor
    · intro h
      have h3 : ι y ∈ range ι ∩ D := ⟨mem_range_self y, h⟩
      rw [hm] at h3
      obtain ⟨w, hw, he⟩ := h3
      exact hι.injective he ▸ hw
    · intro h
      have h3 : ι y ∈ range ι ∩ D := hm ▸ mem_image_of_mem _ h
      exact h3.2
  have hAD : ι '' Δ ∩ D = ι '' I := by
    apply subset_antisymm
    · rintro _ ⟨⟨y, hy, rfl⟩, h⟩
      refine mem_image_of_mem _ ?_
      rw [← hmeet]
      exact ⟨hy, connectedComponentIn_subset _ _ ((hD' y).mp h)⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨mem_image_of_mem _ (hIΔ hy), (hD' y).mpr (hIΘ hy)⟩
  obtain ⟨hE, hEb⟩ := disc_union.{0} (ι '' Δ) D (ι '' I) (ι n₁) (ι n₂)
    (image_emb_disc hι.isEmbedding hΔ) hD hL hAD
    (by
      rw [discBd_image hι.isEmbedding, ← hu]
      exact image_mono subset_union_right)
    (by
      rw [hDb]
      exact image_mono hIΘ)
  have hxne : x ≠ n₁ ∧ x ≠ n₂ := by
    constructor
    · rintro rfl
      exact hx.2 hF.left_mem
    · rintro rfl
      exact hx.2 hF.right_mem
  have hxE : ι x ∈ discInt (ι '' Δ ∪ D) := by
    refine ⟨.inl (mem_image_of_mem _ hx.1), fun h => ?_⟩
    rw [hEb] at h
    refine h.2 ⟨mem_image_of_mem _ hxI, ?_⟩
    rintro (h3 | h3)
    · exact hxne.1 (hι.injective h3)
    · exact hxne.2 (hι.injective h3)
  have hopen : IsOpen (ι ⁻¹' discInt (ι '' Δ ∪ D) \ I') :=
    ((hE.isOpen_discInt hS'.2.2).preimage hι.continuous).sdiff hI'.isCompact.isClosed
  have hxI' : x ∉ I' := fun h => by
    have h3 : x ∈ I ∩ I' := ⟨hxI, h⟩
    rw [hi'] at h3
    rcases h3 with h4 | h4
    · exact hxne.1 h4
    · exact hxne.2 h4
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨hxE, hxI'⟩) ?_
  rintro y ⟨⟨h3 | h3, -⟩, hyI'⟩
  · obtain ⟨w, hw, he⟩ := h3
    exact hι.injective he ▸ hw
  · have h4 := (hD' y).mp h3
    rw [← hu'] at h4
    exact hIΔ (h4.resolve_right hyI')

/-- A pair of complementary lines of a circle are the two arcs between two angles. -/
theorem circle_lines [T2Space S] {Θ I I' : Set S} (f : Circle ≃ₜ Θ) {t₁ t₃ : ℝ} (hlt : t₁ < t₃)
  (ht₃ : t₃ < t₁ + 2 * Real.pi)
    (hI : IsLineWithEnds I (GM19.cuffPoint f t₁) (GM19.cuffPoint f t₃)) (hI' : IsLineWithEnds I'
      (GM19.cuffPoint f t₁) (GM19.cuffPoint f t₃)) (hu : I ∪ I' = Θ) :
    GM19.cuffPoint f '' Icc t₁ t₃ ∩ GM19.cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi) ⊆
      {GM19.cuffPoint f t₁, GM19.cuffPoint f t₃} ∧
    ((I ⊆ GM19.cuffPoint f '' Icc t₁ t₃ ∧ I' ⊆ GM19.cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi)) ∨
      (I ⊆ GM19.cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi) ∧ I' ⊆ GM19.cuffPoint f '' Icc t₁ t₃))
        := by
  have hpi := Real.pi_pos
  set n₁ := GM19.cuffPoint f t₁ with e₁
  set n₂ := GM19.cuffPoint f t₃ with e₃
  let A : Set S := GM19.cuffPoint f '' Icc t₁ t₃
  let B : Set S := GM19.cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi)
  have cc := cuffPoint_continuous f
  have hcA : IsClosed A := (isCompact_Icc.image cc).isClosed
  have hcB : IsClosed B := (isCompact_Icc.image cc).isClosed
  have hAB : A ∪ B = Θ := by
    ext x
    constructor
    · rintro (⟨t, -, rfl⟩ | ⟨t, -, rfl⟩) <;> exact cuffPoint_mem f t
    · intro hx
      obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico f t₁ hx
      rcases le_total t t₃ with h | h
      · exact .inl ⟨t, ⟨ht.1, h⟩, rfl⟩
      · exact .inr ⟨t, ⟨h, ht.2.le⟩, rfl⟩
  have hABi : A ∩ B ⊆ {n₁, n₂} := by
    rintro _ ⟨⟨t, ht, rfl⟩, ⟨t', ht', he⟩⟩
    rcases eq_or_lt_of_le ht'.2 with h | h
    · left
      rw [e₁, ← he, h, cuffPoint_add_two_pi]
    · have := cuffPoint_injOn_Ico f t₁ ⟨ht.1, by linarith [ht.2]⟩ ⟨by linarith [ht'.1], h⟩ he.symm
      right
      have h6 : t = t₃ := by linarith [this, ht.2, ht'.1]
      rw [e₃]
      exact congrArg _ h6
  have hend₁ : n₁ ∈ A ∧ n₁ ∈ B := ⟨⟨t₁, ⟨le_rfl, hlt.le⟩, rfl⟩, ⟨t₁ + 2 * Real.pi, ⟨ht₃.le,
    le_rfl⟩, by rw [cuffPoint_add_two_pi]⟩⟩
  have hend₂ : n₂ ∈ A ∧ n₂ ∈ B := ⟨⟨t₃, ⟨hlt.le, le_rfl⟩, rfl⟩, ⟨t₃, ⟨le_rfl, ht₃.le⟩, rfl⟩⟩
  have key : ∀ {L : Set S}, IsLineWithEnds L n₁ n₂ → L ⊆ Θ → L ⊆ A ∨ L ⊆ B := fun {L} hL hs => by
    have hcov : L \ {n₁, n₂} ⊆ A ∪ B := hAB ▸ sdiff_subset.trans hs
    have hsub : ∀ {P : Set S}, n₁ ∈ P → n₂ ∈ P → L \ {n₁, n₂} ⊆ P → L ⊆ P := fun {P} h1 h2 h3 z hz
      => by
      by_cases h : z ∈ ({n₁, n₂} : Set S)
      · rcases h with rfl | rfl
        · exact h1
        · exact h2
      · exact h3 ⟨hz, h⟩
    by_contra hc
    push Not at hc
    have h1 : ((L \ {n₁, n₂}) ∩ A).Nonempty := by
      by_contra h
      exact hc.2 (hsub hend₁.2 hend₂.2 fun z hz => (hcov hz).resolve_left fun hA' => h ⟨z, hz, hA'⟩)
    have h2 : ((L \ {n₁, n₂}) ∩ B).Nonempty := by
      by_contra h
      exact hc.1 (hsub hend₁.1 hend₂.1 fun z hz => (hcov hz).resolve_right fun hB' => h ⟨z, hz,
        hB'⟩)
    obtain ⟨z, hz, hz'⟩ := isPreconnected_closed_iff.mp hL.isPreconnected_diff A B hcA hcB hcov h1
      h2
    exact hz.2 (hABi hz')
  have hmid₁ : ∃ z ∈ A, z ∉ B := by
    refine ⟨GM19.cuffPoint f ((t₁ + t₃) / 2), ⟨_, ⟨by linarith, by linarith⟩, rfl⟩, fun h => ?_⟩
    have h1 := hABi ⟨⟨_, ⟨by linarith, by linarith⟩, rfl⟩, h⟩
    have h3 : ((t₁ + t₃) / 2) ∈ Ico t₁ (t₁ + 2 * Real.pi) := ⟨by linarith, by linarith⟩
    rcases h1 with h1 | h1
    · have := cuffPoint_injOn_Ico f t₁ h3 ⟨le_rfl, by linarith⟩ h1
      linarith
    · have := cuffPoint_injOn_Ico f t₁ h3 ⟨hlt.le, ht₃⟩ h1
      linarith
  have hmid₂ : ∃ z ∈ B, z ∉ A := by
    refine ⟨GM19.cuffPoint f ((t₃ + (t₁ + 2 * Real.pi)) / 2), ⟨_, ⟨by linarith, by linarith⟩,
      rfl⟩, fun h => ?_⟩
    have h1 := hABi ⟨h, ⟨_, ⟨by linarith, by linarith⟩, rfl⟩⟩
    have h3 : ((t₃ + (t₁ + 2 * Real.pi)) / 2) ∈ Ico t₁ (t₁ + 2 * Real.pi)
      := ⟨by linarith, by linarith⟩
    rcases h1 with h1 | h1
    · have := cuffPoint_injOn_Ico f t₁ h3 ⟨le_rfl, by linarith⟩ h1
      linarith
    · have := cuffPoint_injOn_Ico f t₁ h3 ⟨hlt.le, ht₃⟩ h1
      linarith
  have hI1 : I ⊆ Θ := fun z hz => hu ▸ .inl hz
  have hI2 : I' ⊆ Θ := fun z hz => hu ▸ .inr hz
  refine ⟨hABi, ?_⟩
  rcases key hI hI1 with h1 | h1
  · rcases key hI' hI2 with h2 | h2
    · obtain ⟨z, hz, hz'⟩ := hmid₂
      exact absurd ((hu ▸ hAB ▸ .inr hz : z ∈ I ∪ I').elim (fun h => h1 h) fun h => h2 h) hz'
    · exact .inl ⟨h1, h2⟩
  · rcases key hI' hI2 with h2 | h2
    · exact .inr ⟨h1, h2⟩
    · obtain ⟨z, hz, hz'⟩ := hmid₁
      exact absurd ((hu ▸ hAB ▸ .inl hz : z ∈ I ∪ I').elim (fun h => h1 h) fun h => h2 h) hz'

/-- Two complementary lines of an `O`-arc give the circular order of their points. -/
theorem inOrder_of_lines [T2Space S] {Θ I I' : Set S} {n₁ n₂ n m : S} (hO : IsOArc Θ)
  (hI : IsLineWithEnds I n₁ n₂) (hI' : IsLineWithEnds I' n₁ n₂)
    (hu : I ∪ I' = Θ) (hn : n ∈ I) (hm : m ∈ I') : GM19.InOrderOn Θ n₁ n n₂ m := by
  obtain ⟨f⟩ := hO
  have hn₁ : n₁ ∈ Θ := hu ▸ .inl hI.left_mem
  have hn₂ : n₂ ∈ Θ := hu ▸ .inl hI.right_mem
  obtain ⟨t₁, -, rfl⟩ := exists_cuffPoint_mem_Ico f 0 hn₁
  obtain ⟨t₃, ht₃, rfl⟩ := exists_cuffPoint_mem_Ico f t₁ hn₂
  have hlt : t₁ < t₃ := lt_of_le_of_ne ht₃.1 fun h => hI.ne' (by rw [h])
  rcases (circle_lines f hlt ht₃.2 hI hI' hu).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨t₂, ht₂, rfl⟩ := h1 hn
    obtain ⟨t₄, ht₄, rfl⟩ := h2 hm
    exact ⟨f, t₁, t₂, t₃, t₄, ht₂.1, ht₂.2, ht₄.1, ht₄.2, rfl, rfl, rfl, rfl⟩
  · obtain ⟨t₂, ht₂, rfl⟩ := h2 hm
    obtain ⟨t₄, ht₄, rfl⟩ := h1 hn
    have h3 : GM19.InOrderOn Θ (GM19.cuffPoint f t₁) (GM19.cuffPoint f t₂) (GM19.cuffPoint f t₃)
      (GM19.cuffPoint f t₄) :=
      ⟨f, t₁, t₂, t₃, t₄, ht₂.1, ht₂.2, ht₄.1, ht₄.2, rfl, rfl, rfl, rfl⟩
    exact inOrderOn_cyclic3 (inOrderOn_rev h3)

/-- Points in order on an `O`-arc are on the two sides of two of them, for any pair of complementary
lines. -/
theorem mem_of_inOrder [T2Space S] {Θ L L' : Set S} {x₁ x₂ x₃ x₄ : S}
  (h : GM19.InOrderOn Θ x₁ x₂ x₃ x₄) (hL : IsLineWithEnds L x₁ x₃)
    (hL' : IsLineWithEnds L' x₁ x₃) (hu : L ∪ L' = Θ) : (x₂ ∈ L ∧ x₄ ∈ L') ∨ (x₂ ∈ L' ∧ x₄ ∈ L)
      := by
  obtain ⟨f, t₁, t₂, t₃, t₄, h12, h23, h34, h41, rfl, rfl, rfl, rfl⟩ := h
  have hlt : t₁ < t₃ := lt_of_le_of_ne (h12.trans h23) fun h => hL.ne' (by rw [h])
  have ht3 : t₃ < t₁ + 2 * Real.pi := lt_of_le_of_ne (h34.trans h41) fun h => hL.ne'
    (by rw [h, cuffPoint_add_two_pi])
  obtain ⟨hi, hc⟩ := circle_lines f hlt ht3 hL hL' hu
  have hm₂ : GM19.cuffPoint f t₂ ∈ GM19.cuffPoint f '' Icc t₁ t₃ := ⟨t₂, ⟨h12, h23⟩, rfl⟩
  have hm₄ : GM19.cuffPoint f t₄ ∈ GM19.cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi)
    := ⟨t₄, ⟨h34, h41⟩, rfl⟩
  have hun : ∀ z, z ∈ Θ → z ∈ L ∨ z ∈ L' := fun z hz => (hu ▸ hz : z ∈ L ∪ L')
  have hends : ∀ z, z ∈ ({GM19.cuffPoint f t₁, GM19.cuffPoint f t₃} : Set S) → z ∈ L ∧ z ∈ L' := by
    rintro z (rfl | rfl)
    · exact ⟨hL.left_mem, hL'.left_mem⟩
    · exact ⟨hL.right_mem, hL'.right_mem⟩
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · exact (hun _ (cuffPoint_mem f t₂)).elim id fun h => (hends _ (hi ⟨hm₂, h2 h⟩)).1
    · exact (hun _ (cuffPoint_mem f t₄)).elim (fun h => (hends _ (hi ⟨h1 h, hm₄⟩)).2) id
  · right
    constructor
    · exact (hun _ (cuffPoint_mem f t₂)).elim (fun h => (hends _ (hi ⟨hm₂, h1 h⟩)).2) id
    · exact (hun _ (cuffPoint_mem f t₄)).elim id fun h => (hends _ (hi ⟨h2 h, hm₄⟩)).1

/-- In a circular order with `x₁ = x₃`, one of the other two points is also `x₁`. -/
theorem eq_of_inOrder {Θ : Set S} {x x₂ x₄ : S} (h : GM19.InOrderOn Θ x x₂ x x₄) : x₂ = x ∨ x₄ = x
  := by
  obtain ⟨f, t₁, t₂, t₃, t₄, h12, h23, h34, h41, h1, rfl, h3, rfl⟩ := h
  rcases eq_or_lt_of_le (h34.trans h41) with h | h
  · right
    have h5 : t₄ = t₃ := le_antisymm (by linarith) h34
    rw [h5, h3]
  · left
    have h5 := cuffPoint_injOn_Ico f t₁ ⟨h12.trans h23, h⟩ ⟨le_rfl, by linarith [Real.pi_pos]⟩
      (h3.trans h1.symm)
    have h6 : t₂ = t₁ := le_antisymm (by linarith) h12
    rw [h6, h1]

/-- Order with three equal points. -/
theorem inOrder_three {Θ : Set S} (hO : IsOArc Θ) {x b : S} (hx : x ∈ Θ)
  (hb : b ∈ Θ) : GM19.InOrderOn Θ x x x b := by
  obtain ⟨f⟩ := hO
  obtain ⟨t, -, rfl⟩ := exists_cuffPoint_mem_Ico f 0 hx
  obtain ⟨t', ht', rfl⟩ := exists_cuffPoint_mem_Ico f t hb
  exact ⟨f, t, t, t, t', le_rfl, le_rfl, ht'.1, ht'.2.le, rfl, rfl, rfl, rfl⟩

/-- A cell lies inside or outside a disc cut off by an `I`-arc. -/
theorem cell_side [T2Space S] {Γ : Painting S} {F Δ : Set S} {c : Set S} (hc : c ∈ Γ.C)
  (hn : Γ.IsNormal F) (hΔ : IsClosedDisc Δ) (hnb : ∀ x ∈ Δ \ F, Δ ∈ 𝓝 x) :
    c ⊆ Δ ∨ c ⊆ Δᶜ := by
  have hp := (arcComponentsIn_isPathConnected hc).isConnected.isPreconnected
  have hsub : c ⊆ interior Δ ∪ Δᶜ := fun x hx => by
    by_cases h : x ∈ Δ
    · refine .inl (mem_interior_iff_mem_nhds.mpr (hnb x ⟨h, fun hF => ?_⟩))
      exact (arcComponentsIn_subset hc hx).2 (hn ⟨hF, (arcComponentsIn_subset hc hx).1⟩)
    · exact .inr h
  rcases hp.subset_or_subset isOpen_interior hΔ.isClosed.isOpen_compl
    (disjoint_left.mpr fun x hx hx' => hx' (interior_subset hx)) hsub with h | h
  · exact .inl (h.trans interior_subset)
  · exact .inr h

/-- At each end of an arc of the boundary there is a border cell that meets the arc. -/
theorem exists_border_cell [T2Space S] {Γ : Painting S} {I Δ : Set S} {n₁ n₂ : S}
  (hI : IsLineWithEnds I n₁ n₂) (hIb : I ⊆ bd S) (hIΔ : I ⊆ Δ) (hn₁N : n₁ ∈ Γ.N)
    (hside : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ) : ∃ c ∈ Γ.C, c ⊆ Δ ∧ (c ∩ bd S).Nonempty ∧ n₁ ∈ tilde c ∧
      (c ∩ I).Nonempty := by
  have h3 : n₁ ∈ closure (I \ {n₁, n₂}) := hI.subset_closure_diff hI.left_mem
  have hsplit : I \ {n₁, n₂} = (I \ {n₁, n₂}) \ Γ.N ∪ ((I \ {n₁, n₂}) ∩ Γ.N) :=
    (sdiff_union_inter _ _).symm
  rw [hsplit, closure_union] at h3
  have h4 : n₁ ∉ closure ((I \ {n₁, n₂}) ∩ Γ.N) := by
    rw [(Γ.finite_N.subset inter_subset_right).isClosed.closure_eq]
    exact fun h => h.1.2 (mem_insert _ _)
  have h5 := h3.resolve_right h4
  have hcov : (I \ {n₁, n₂}) \ Γ.N ⊆ ⋃₀ {c ∈ Γ.C | (c ∩ I).Nonempty} := by
    intro z hz
    have hzU : z ∈ Γ.U \ Γ.N := ⟨Γ.bd_subset (hIb hz.1.1), hz.2⟩
    obtain ⟨c, hc, hzc⟩ := exists_mem_arcComponentsIn hzU
    exact ⟨c, ⟨hc, z, hzc, hz.1.1⟩, hzc⟩
  have h6 := closure_mono hcov h5
  have hfinite : {c ∈ Γ.C | (c ∩ I).Nonempty}.Finite :=
    Γ.finite_cells.subset fun _ hc => hc.1
  rw [hfinite.closure_sUnion] at h6
  obtain ⟨c, ⟨hc, z, hzc, hzI⟩, hnc⟩ := mem_iUnion₂.mp h6
  exact ⟨c, hc, (hside c hc).resolve_right fun h => h hzc (hIΔ hzI), ⟨z, hzc, hIb hzI⟩, ⟨hnc,
    fun hnc' => (arcComponentsIn_subset hc hnc').2 hn₁N⟩,
    ⟨z, hzc, hzI⟩⟩

/-- The surface part of (6.7) of Graph Minors XVII, page 177. -/
theorem normalIArcDiscPainting : NormalIArcDiscPaintingStatement := by
  unfold NormalIArcDiscPaintingStatement
  intro S _ hcS ht2 hconn hS Γ F Δ Θ n₁ n₂ hnorm hF hb hΘ hn₁ hn₂ hΔ h1 h2
  obtain ⟨I, I', Θ', hΘ', hI, hI', hu', hi', hu, hi, hmeet, hnb⟩ := arc_disc_data hS hF hb hΔ h1 h2
  have hΘeq : Θ' = Θ := cuffs_disjoint_eq hΘ' hΘ (hu' ▸ .inl hI.left_mem) hn₁
  subst hΘeq
  have hcl := hΔ.isClosed
  have hIΘ : I ⊆ Θ' := fun z hz => hu' ▸ .inl hz
  have hΘb : Θ' ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hIΔ : I ⊆ Δ := fun z hz => (hmeet ▸ hz : z ∈ Δ ∩ bd S).1
  refine ⟨?_, ?_, ?_⟩
  · intro c₁ hc₁ hs₁ c₂ hc₂ hs₂ x ⟨hx₁, hx₂⟩
    by_contra hxF
    have hx : x ∈ Δ := closure_minimal hs₁ hcl hx₁.1
    have h3 := mem_closure_iff_nhds.mp hx₂.1 _ (hnb x ⟨hx, hxF⟩)
    obtain ⟨y, hy, hy'⟩ := h3
    exact (cell_side hc₂ hnorm hΔ hnb).resolve_left hs₂ hy' hy
  · obtain ⟨c, hc, h3, h4, h5, -⟩ :=
      exists_border_cell hI (hIΘ.trans hΘb) hIΔ (hnorm ⟨hF.left_mem, Γ.bd_subset (hΘb hn₁)⟩)
        fun c hc => cell_side hc hnorm hΔ hnb
    exact ⟨c, hc, h3, h4, h5⟩
  · rintro n' ⟨⟨hn'N, hn'Δ⟩, hn'b⟩ c hc hcΘ hcΔ m hm
    have hn'I : n' ∈ I := hmeet ▸ ⟨hn'Δ, hn'b⟩
    refine ⟨hIΘ hn'I, ?_⟩
    have hdis : c ⊆ Δᶜ := (cell_side hc hnorm hΔ hnb).resolve_left hcΔ
    obtain ⟨u, v, -, htilde, hL, hdiff, -, -⟩ := Γ.border_cell_exists_ends hc (hcΘ.mono
      (inter_subset_inter_right _ hΘb))
    have hLΘ := (Γ.border_cell_subset_cuff hc hΘ hcΘ).1
    have hsub : (closure c ∩ bd S) \ {u, v} ⊆ I' := by
      intro z hz
      have hzc : z ∈ c := (hdiff ▸ hz : z ∈ c ∩ bd S).1
      have h3 : z ∈ I ∪ I' := hu' ▸ hLΘ hz.1
      exact h3.resolve_left fun h => hdis hzc (hIΔ h)
    have hmL : m ∈ closure c ∩ bd S := by
      have h3 : m ∈ ({u, v} : Set S) := htilde ▸ hm
      rcases h3 with rfl | rfl
      · exact hL.left_mem
      · exact hL.right_mem
    have hmI' : m ∈ I' := closure_minimal hsub hI'.isCompact.isClosed (hL.subset_closure_diff hmL)
    exact inOrder_of_lines ((cuff_statement.{0} S hS).2.2 _ hΘ) hI hI' hu' hn'I hmI'

end GraphMinor.GM17
