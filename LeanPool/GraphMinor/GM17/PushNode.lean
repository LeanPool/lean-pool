/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.FreeLift
public import LeanPool.GraphMinor.GM17.MarkCross
public import LeanPool.GraphMinor.Surface.Wedge

/-!
# The surface part of (5.4) of Graph Minors XVII

See the module docstring of `GraphMinor.GM17.Bigon`. Here we build the disc `G` at a node
(`exists_bigon`) and prove `cutNormalOArc : CutNormalOArcPaintingStatement` by induction on
the number of nodes on the curve.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {Y S T : Type} [TopologicalSpace Y] [TopologicalSpace S] [TopologicalSpace T]

/-- A short piece of a line at one of its ends that misses a finite set. -/
theorem exists_sub_end [T2Space T] {K E : Set T} {y p : T} (hK : IsLineWithEnds K y p)
  (hE : E.Finite) : ∃ q L, IsLineWithEnds L y q ∧ L ⊆ K ∧ L ∩ E ⊆ {y} := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hK.exists_arc
  have hfin : (a ⁻¹' E \ {0}).Finite := (hE.preimage ha.2.injOn).subset sdiff_subset
  have hn : (a ⁻¹' E \ {0})ᶜ ∈ 𝓝 (0 : unitInterval) := hfin.isClosed.isOpen_compl.mem_nhds fun h
    => h.2 rfl
  obtain ⟨u, hu, hs⟩ := exists_Ico_subset_of_mem_nhds hn ⟨1, by simp⟩
  obtain ⟨r, hr, hr'⟩ := exists_between hu
  refine ⟨a r, _, isLine_piece ha hr, image_subset_range _ _, ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, hE'⟩
  have h1 : t ∉ a ⁻¹' E \ {0} := hs ⟨ht.1, ht.2.trans_lt hr'⟩
  have h2 : t = 0 := by
    by_contra h
    exact h1 ⟨hE', h⟩
  exact h2 ▸ rfl

omit [TopologicalSpace T] in
theorem exists_pair_line {ψ : Y → T} {Z : Set T} {a b : T} {X X' : Set Y}
  (h : LiftPair ψ Z a b X X') {y : Y} (hy : ψ y ∈ Z) :
    ∃ K k₀ k₁, IsLineWithEnds K k₀ k₁ ∧ y ∈ K ∧ BijOn ψ K Z ∧ ψ k₀ = a ∧ ψ k₁ = b := by
  obtain ⟨x0, x1, y0, y1, h1, h2, -, h4, h5, h6, h7, h8, h9, h10⟩ := h
  rcases (h4.symm.subset hy : y ∈ X ∪ X') with h | h
  · exact ⟨X, x0, x1, h1, h, h5, h7, h9⟩
  · exact ⟨X', y0, y1, h2, h, h6, h8, h10⟩

omit [TopologicalSpace T] in
/-- Two lines of the preimage of a curve that leave a point on it. -/
theorem exists_two_lines [T2Space Y] {ψ : Y → T} {Z₁ Z₂ : Set T} {u c : T} {X₁ Y₁ X₂ Y₂ : Set Y}
  (h1 : LiftPair ψ Z₁ u c X₁ Y₁) (h2 : LiftPair ψ Z₂ c u X₂ Y₂)
    (hi : Z₁ ∩ Z₂ = {u, c}) (_hne : u ≠ c) {y : Y} (hy : ψ y ∈ Z₁ ∪ Z₂) :
    ∃ K₁ K₂ p₁ p₂, IsLineWithEnds K₁ y p₁ ∧ IsLineWithEnds K₂ y p₂ ∧ InjOn ψ K₁ ∧ InjOn ψ K₂
      ∧ K₁ ⊆ ψ ⁻¹' (Z₁ ∪ Z₂) ∧ K₂ ⊆ ψ ⁻¹' (Z₁ ∪ Z₂) ∧
      (∀ x ∈ K₁, ∀ x' ∈ K₂, ψ x = ψ x' → x = x' ∨ ψ x ∈ ({u, c} : Set T)) ∧ ∀ x ∈ K₁, x ∈ K₂ → x
        = y ∨ ψ x ∈ ({u, c} : Set T) := by
  have hmid : ∀ {Z : Set T} {a b : T}, Z ⊆ Z₁ ∪ Z₂ → (∃ K k₀ k₁, IsLineWithEnds K k₀ k₁ ∧ y ∈ K
    ∧ BijOn ψ K Z ∧ ψ k₀ = a ∧ ψ k₁ = b) → ψ y ≠ a → ψ y ≠ b →
      ∃ K₁ K₂ p₁ p₂, IsLineWithEnds K₁ y p₁ ∧ IsLineWithEnds K₂ y p₂ ∧ InjOn ψ K₁ ∧ InjOn ψ K₂
        ∧ K₁ ⊆ ψ ⁻¹' (Z₁ ∪ Z₂) ∧ K₂ ⊆ ψ ⁻¹' (Z₁ ∪ Z₂) ∧
      (∀ x ∈ K₁, ∀ x' ∈ K₂, ψ x = ψ x' → x = x' ∨ ψ x ∈ ({u, c} : Set T)) ∧ ∀ x ∈ K₁, x ∈ K₂ → x
        = y ∨ ψ x ∈ ({u, c} : Set T) := by
    rintro Z a b hZ ⟨K, k₀, k₁, hK, hyK, hb, h3, h4⟩ ha hb'
    obtain ⟨L₁, L₂, h5, h6, h7, h8⟩ := hK.split hyK (fun h => ha (h ▸ h3)) (fun h => hb' (h ▸ h4))
    have hs₁ : L₁ ⊆ K := h7 ▸ subset_union_left
    have hs₂ : L₂ ⊆ K := h7 ▸ subset_union_right
    refine ⟨L₁, L₂, k₀, k₁, h5.symm, h6, hb.injOn.mono hs₁, hb.injOn.mono hs₂,
      fun x hx => hZ (hb.mapsTo (hs₁ hx)), fun x hx => hZ (hb.mapsTo (hs₂ hx)), ?_, ?_⟩
    · exact fun x hx x' hx' he => .inl (hb.injOn (hs₁ hx) (hs₂ hx') he)
    · intro x hx hx'
      exact .inl (h8.subset ⟨hx, hx'⟩)
  have hcross : ∀ {K₁ K₂ : Set Y}, BijOn ψ K₁ Z₁ → BijOn ψ K₂ Z₂ → (∀ x ∈ K₁, ∀ x' ∈ K₂, ψ x = ψ x'
    → x = x' ∨ ψ x ∈ ({u, c} : Set T)) ∧ ∀ x ∈ K₁, x ∈ K₂ → x = y ∨ ψ x ∈ ({u, c} : Set T) := by
    intro K₁ K₂ h3 h4
    constructor
    · exact fun x hx x' hx' he => .inr (hi ▸ ⟨h3.mapsTo hx, he ▸ h4.mapsTo hx'⟩)
    · exact fun x hx hx' => .inr (hi ▸ ⟨h3.mapsTo hx, h4.mapsTo hx'⟩)
  by_cases hu : ψ y = u
  · have hu₁ : u ∈ Z₁ ∩ Z₂ := hi ▸ mem_insert _ _
    obtain ⟨K, k₀, k₁, hK, hyK, hb, h3, -⟩ := exists_pair_line h1 (hu ▸ hu₁.1 : ψ y ∈ Z₁)
    obtain ⟨K', k₀', k₁', hK', hyK', hb', -, h4⟩ := exists_pair_line h2 (hu ▸ hu₁.2 : ψ y ∈ Z₂)
    have e1 : k₀ = y := hb.injOn hK.left_mem hyK (h3.trans hu.symm)
    have e2 : k₁' = y := hb'.injOn hK'.right_mem hyK' (h4.trans hu.symm)
    subst e1
    obtain ⟨hc1, hc2⟩ := hcross hb hb'
    exact ⟨K, K', k₁, k₀', hK, e2 ▸ hK'.symm, hb.injOn, hb'.injOn,
      fun x hx => .inl (hb.mapsTo hx), fun x hx => .inr (hb'.mapsTo hx), hc1, hc2⟩
  by_cases hc : ψ y = c
  · have hu₁ : c ∈ Z₁ ∩ Z₂ := hi ▸ mem_insert_of_mem _ rfl
    obtain ⟨K, k₀, k₁, hK, hyK, hb, -, h3⟩ := exists_pair_line h1 (hc ▸ hu₁.1 : ψ y ∈ Z₁)
    obtain ⟨K', k₀', k₁', hK', hyK', hb', h4, -⟩ := exists_pair_line h2 (hc ▸ hu₁.2 : ψ y ∈ Z₂)
    have e1 : k₁ = y := hb.injOn hK.right_mem hyK (h3.trans hc.symm)
    have e2 : k₀' = y := hb'.injOn hK'.left_mem hyK' (h4.trans hc.symm)
    subst e1
    obtain ⟨hc1, hc2⟩ := hcross hb hb'
    exact ⟨K, K', k₀, k₁', hK.symm, e2 ▸ hK', hb.injOn, hb'.injOn,
      fun x hx => .inl (hb.mapsTo hx), fun x hx => .inr (hb'.mapsTo hx), hc1, hc2⟩
  rcases hy with hy | hy
  · exact hmid subset_union_left (exists_pair_line h1 hy) hu hc
  · exact hmid subset_union_right (exists_pair_line h2 hy) hc hu

theorem line_image [T2Space T] {L : Set Y} {u v : Y} {f : Y → T} (hc : Continuous f)
  (hi : InjOn f L) (hL : IsLineWithEnds L u v) : IsLineWithEnds (f '' L) (f u) (f v) :=
  hL.image_under_injOn hc.continuousOn hi

/-- At a node on a normal curve there is a thin disc with a line of the curve around the node on its
boundary, which meets the paint only at the node. -/
theorem exists_bigon [CompactSpace S] [T2Space S] [ConnectedSpace S] (hS : IsSurface S) {Γ :
  Painting S} {F : Set S} (hO : IsOArc F) (hnorm : Γ.IsNormal F)
    (hint : ∀ c ∈ Γ.C, Γ.IsInternalCell c → Disjoint (tilde c) F) {n : S} (hnF : n ∈ F)
      (hnU : n ∈ Γ.U) :
    ∃ G L₀ L₁ u v, IsClosedDisc G ∧ IsLineWithEnds L₀ u v ∧ IsLineWithEnds L₁ u v ∧ discBd G
      = L₀ ∪ L₁ ∧ L₀ ∩ L₁ = {u, v} ∧ G ∩ F = L₀ ∧ G ∩ Γ.U ⊆ {n} ∧ n ∈ L₀ ∧ n ≠ u ∧ n ≠ v := by
  classical
  obtain ⟨T, tT, j, cap, hT, hTc, hj, hcap, hcov⟩ := exists_cap_discs _ S hS rfl
  have hcT : CompactSpace T := hT.1
  have ht2T : T2Space T := hT.2.1
  have hTs : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  have hOt : IsOArc (j '' F) := by
    obtain ⟨φ⟩ := id hO
    exact ⟨φ.trans (hj.isEmbedding.homeomorphImage _)⟩
  have hFc : IsClosed (j '' F) := by
    obtain ⟨φ⟩ := id hOt
    have hc : IsCompact (j '' F) := by
      rw [isCompact_iff_compactSpace]
      exact φ.compactSpace
    exact hc.isClosed
  have hd : Disjoint (j '' F) (bd T) := disjoint_left.mpr fun x _ h => h (hT.2.2 x)
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, -, Z₁, Z₂, u, c, X₁, Y₁, X₂, Y₂, h7, h8, hi, hun, huc, -, -⟩
    := exists_cut_loop hTs hOt hd
  have hcY : CompactSpace Y := hY.1
  have hnN : n ∈ Γ.N := hnorm ⟨hnF, hnU⟩
  obtain ⟨yHat, hyHat, hyHatZ⟩ := exists_free_lift hS hnorm hint hnF hnN hj hcap hψ hFc
  let A : Set T := j '' Γ.U ∪ ⋃ C ∈ cuffs S, cap C
  have hfinC := (cuff_statement.{0} S hS).2.1
  have hAc : IsClosed A := (hj.isClosedMap _ Γ.isClosed_U).union (hfinC.isClosed_biUnion fun C hC
    => (hcap C hC).1.isClosed)
  have hAF : A ∩ j '' F ⊆ j '' (F ∩ Γ.N) := by
    rintro _ ⟨h1 | h1, ⟨x, hx, rfl⟩⟩
    · obtain ⟨z, hz, he⟩ := h1
      obtain rfl := hj.injective he
      exact mem_image_of_mem _ ⟨hx, hnorm ⟨hx, hz⟩⟩
    · obtain ⟨C, hC, hw⟩ := mem_iUnion₂.mp h1
      obtain ⟨y, hy, he⟩ := ((hcap C hC).2.2 ▸ ⟨⟨x, rfl⟩, hw⟩ : j x ∈ j '' C)
      obtain rfl := hj.injective he
      have hb : y ∈ bd S := by
        obtain ⟨p, -, rfl⟩ := hC
        exact connectedComponentIn_subset _ _ hy
      exact mem_image_of_mem _ ⟨hx, hnorm ⟨hx, Γ.bd_subset hb⟩⟩
  let E : Set Y := ψ ⁻¹' (j '' (F ∩ Γ.N) ∪ {u, c})
  have hEfin : E.Finite := by
    refine Set.Finite.preimage' (((Γ.finite_N.subset inter_subset_right).image _).union
      (by simp)) fun b hb => ?_
    have hbF : b ∈ j '' F := by
      rcases hb with ⟨x, hx, rfl⟩ | hb
      · exact mem_image_of_mem _ hx.1
      · rw [← hun]
        exact .inl ((hi ▸ hb : b ∈ Z₁ ∩ Z₂).1)
    exact Set.finite_of_encard_le_coe (k := 2) (cut_encard_le hψ hbF)
  have hyHatF : ψ yHat ∈ Z₁ ∪ Z₂ := hun ▸ hyHat ▸ mem_image_of_mem _ hnF
  obtain ⟨K₁, K₂, p₁, p₂, hK₁, hK₂, hi₁, hi₂, hs₁, hs₂, hcr, hcr'⟩ := exists_two_lines h7 h8 hi huc
    hyHatF
  obtain ⟨q₁, L₁, hl₁, hsL₁, hE₁⟩ := exists_sub_end hK₁ hEfin
  obtain ⟨q₂, L₂, hl₂, hsL₂, hE₂⟩ := exists_sub_end hK₂ hEfin
  have huE : ∀ {x}, ψ x ∈ ({u, c} : Set T) → x ∈ E := fun h => .inr h
  have h12 : L₁ ∩ L₂ = {yHat} := by
    apply subset_antisymm
    · rintro x ⟨hx, hx'⟩
      rcases hcr' x (hsL₁ hx) (hsL₂ hx') with h | h
      · exact h
      · exact hE₁ ⟨hx, huE h⟩
    · rintro _ rfl
      exact ⟨hl₁.left_mem, hl₂.left_mem⟩
  have hL := hl₁.symm.union hl₂ h12
  set L := L₁ ∪ L₂ with hLdef
  have hLinj : InjOn ψ L := by
    have hcross : ∀ x ∈ L₁, ∀ x' ∈ L₂, ψ x = ψ x' → x = x' := fun x hx x' hx' he => by
      rcases hcr x (hsL₁ hx) x' (hsL₂ hx') he with h | h
      · exact h
      · have h1 : x = yHat := hE₁ ⟨hx, huE h⟩
        have h2 : x' = yHat := hE₂ ⟨hx', huE (he ▸ h)⟩
        exact h1.trans h2.symm
    rintro x (hx | hx) x' (hx' | hx') he
    · exact hi₁ (hsL₁ hx) (hsL₁ hx') he
    · exact hcross x hx x' hx' he
    · exact (hcross x' hx' x hx he.symm).symm
    · exact hi₂ (hsL₂ hx) (hsL₂ hx') he
  have hLF : L ⊆ ψ ⁻¹' (j '' F) := by
    rw [← hun]
    rintro x (hx | hx)
    · exact hs₁ (hsL₁ hx)
    · exact hs₂ (hsL₂ hx)
  have hLE : L ∩ E ⊆ {yHat} := by
    rintro x ⟨hx | hx, hxE⟩
    · exact hE₁ ⟨hx, hxE⟩
    · exact hE₂ ⟨hx, hxE⟩
  have hLb : L ⊆ bd Y := hLF.trans hψ.2.2.2.2
  let Z₀ : Set Y := closure (ψ ⁻¹' (A \ j '' F))
  let Z : Set Y := Z₀ ∪ ψ ⁻¹' (j '' (F ∩ Γ.N) \ {j n})
  have hZc : IsClosed Z := isClosed_closure.union ((((Γ.finite_N.subset inter_subset_right).image
    j).subset sdiff_subset).isClosed.preimage hψ.1)
  have hZ₀ : ∀ {x}, x ∈ Z₀ → ψ x ∈ A := fun {x} hx => by
    have h1 := hψ.1.closure_preimage_subset _ hx
    exact closure_minimal sdiff_subset hAc h1
  have hZL : Z ∩ L ⊆ {q₁, q₂} := by
    rintro x ⟨hx | hx, hxL⟩
    · have h1 : ψ x ∈ j '' (F ∩ Γ.N) := hAF ⟨hZ₀ hx, hLF hxL⟩
      obtain rfl : x = yHat := hLE ⟨hxL, .inl h1⟩
      exact absurd hx hyHatZ
    · obtain rfl : x = yHat := hLE ⟨hxL, .inl hx.1⟩
      exact absurd hyHat hx.2
  obtain ⟨D, hD, hLD, hDZ, hDb⟩ := exists_wedge hY hL hLb hZc hZL
  have hq₁ : q₁ ≠ yHat := hl₁.ne'.symm
  have hq₂ : q₂ ≠ yHat := hl₂.ne'.symm
  have hDinj : InjOn ψ D := by
    intro y hy y' hy' he
    by_cases hF : ψ y ∈ j '' F
    · have h1 : y ∈ L := hDb ▸ ⟨hy, hψ.2.2.2.2 hF⟩
      have h2 : y' ∈ L := hDb ▸ ⟨hy', hψ.2.2.2.2 (show ψ y' ∈ _ from he ▸ hF)⟩
      exact hLinj h1 h2
        he
    · have hy'F : ψ y' ∉ j '' F := he ▸ hF
      exact hψ.2.2.1 hF hy'F he
  have hneY : Nonempty Y := ⟨yHat⟩
  obtain ⟨hGt, hGb⟩ := isClosedDisc_image_injOn hD hD.isCompact hψ.1.continuousOn hDinj
  have hq : ∀ {y}, y ∈ ({q₁, q₂} : Set Y) → y ∈ L := by
    rintro y (rfl | rfl)
    · exact hL.left_mem
    · exact hL.right_mem
  have hqE : ∀ {y}, y ∈ ({q₁, q₂} : Set Y) → ψ y ∉ j '' (F ∩ Γ.N) := by
    rintro y hy h
    have h1 : y = yHat := hLE ⟨hq hy, .inl h⟩
    rcases hy with rfl | rfl
    · exact hq₁ h1
    · exact hq₂ h1
  have hGA : ψ '' D ∩ A ⊆ {j n} := by
    rintro _ ⟨⟨y, hy, rfl⟩, hyA⟩
    by_cases hF : ψ y ∈ j '' F
    · by_contra hne
      have h1 : ψ y ∈ j '' (F ∩ Γ.N) := hAF ⟨hyA, hF⟩
      have h2 : y ∈ ({q₁, q₂} : Set Y) := hDZ ⟨hy, .inr ⟨h1, hne⟩⟩
      exact hqE h2 h1
    · have h2 : y ∈ ({q₁, q₂} : Set Y) := hDZ ⟨hy, .inl (subset_closure ⟨hyA, hF⟩)⟩
      exact absurd (hLF (hq h2)) hF
  have hGr : ψ '' D ⊆ range j := by
    intro z hz
    rcases (hcov ▸ mem_univ z : z ∈ range j ∪ ⋃ C ∈ cuffs S, cap C) with h | h
    · exact h
    · have h1 := hGA ⟨hz, .inr h⟩
      rw [mem_singleton_iff.mp h1]
      exact mem_range_self n
  have hneS : Nonempty S := ⟨n⟩
  obtain ⟨hG, hGbd⟩ := isClosedDisc_preimage hj hGt hGr
  obtain ⟨L', hL', hun', hin'⟩ := oarc_split hD.isOArc_discBd hL hLD
  have hD' : discBd D ⊆ D := discBd_subset D
  have hsL : L ⊆ D := hLD.trans hD'
  have hsL' : L' ⊆ D := (hun' ▸ subset_union_right).trans hD'
  have hl0 := line_image hψ.1 (hDinj.mono hsL) hL
  have hl1 := line_image hψ.1 (hDinj.mono hsL') hL'
  obtain ⟨u₀, v₀, hu₀, hv₀, hlA⟩ := hl0.pull hj.isEmbedding ((image_mono hsL).trans hGr)
  obtain ⟨u₁, v₁, hu₁, hv₁, hlB⟩ := hl1.pull hj.isEmbedding ((image_mono hsL').trans hGr)
  obtain rfl : u₁ = u₀ := hj.injective (hu₁.trans hu₀.symm)
  obtain rfl : v₁ = v₀ := hj.injective (hv₁.trans hv₀.symm)
  have hnL : yHat ∈ L := .inl hl₁.left_mem
  refine ⟨_, _, _, u₁, v₁, hG, hlA, hlB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hGbd, hGb, ← hun', image_union, preimage_union]
  · ext x
    constructor
    · rintro ⟨⟨y, hy, he⟩, ⟨y', hy', he'⟩⟩
      have h1 : y = y' := hDinj (hsL hy) (hsL' hy') (he.trans he'.symm)
      have h2 : y ∈ L ∩ L' := ⟨hy, h1 ▸ hy'⟩
      rw [hin'] at h2
      rcases h2 with rfl | rfl
      · exact .inl (hj.injective (he.symm.trans hu₁.symm))
      · exact .inr (hj.injective (he.symm.trans hv₁.symm))
    · rintro (rfl | rfl)
      · exact ⟨⟨_, hL.left_mem, hu₀.symm⟩, ⟨_, hL'.left_mem, hu₀.symm⟩⟩
      · exact ⟨⟨_, hL.right_mem, hv₀.symm⟩, ⟨_, hL'.right_mem, hv₀.symm⟩⟩
  · ext x
    constructor
    · rintro ⟨⟨y, hy, he⟩,
        hxF⟩
      have hyF : ψ y ∈ j '' F := he.symm ▸ mem_image_of_mem j hxF
      have h1 : y ∈ L := hDb ▸ ⟨hy, hψ.2.2.2.2 hyF⟩
      exact ⟨y, h1, he⟩
    · rintro ⟨y, hy, he⟩
      refine ⟨⟨y, hsL hy, he⟩, ?_⟩
      have h1 := hLF hy
      rw [mem_preimage, he] at h1
      exact hj.injective.mem_set_image.mp h1
  · rintro x ⟨hx, hxU⟩
    exact hj.injective (hGA ⟨hx, .inl (mem_image_of_mem _ hxU)⟩)
  · exact ⟨yHat, hnL, hyHat⟩
  · rintro rfl
    have h1 : ψ q₁ = ψ yHat := hu₀.symm.trans hyHat.symm
    exact hq₁ (hLinj hL.left_mem hnL h1)
  · rintro rfl
    have h1 : ψ q₂ = ψ yHat := hv₀.symm.trans hyHat.symm
    exact hq₂ (hLinj hL.right_mem hnL h1)

/-- The conclusion for a curve follows from the conclusion for the curve with a line swapped. -/
theorem conclusion_flip [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {Γ : Painting S} {G L₀ L₁ R
  : Set S} {u v n : S} (hG : IsClosedDisc G) (hL₀ : IsLineWithEnds L₀ u v)
    (hL₁ : IsLineWithEnds L₁ u v) (hR : IsLineWithEnds R u v) (hbG : discBd G = L₀ ∪ L₁)
      (h01 : L₀ ∩ L₁ = {u, v}) (h0R : L₀ ∩ R = {u, v}) (h1R : L₁ ∩ R = {u, v})
    (hGR : G ∩ R = {u, v}) (hGU : G ∩ Γ.U ⊆ {n}) (hnN : n ∈ Γ.N) (h : OArcConclusion S Γ
      (L₁ ∪ R)) : OArcConclusion S Γ (L₀ ∪ R) := by
  have hd : ∀ c ∈ Γ.C, Disjoint c G := fun c hc => disjoint_left.mpr fun x hx hxG => by
    have h1 := arcComponentsIn_subset hc hx
    have h2 : x = n := hGU ⟨hxG, h1.1⟩
    exact h1.2 (h2 ▸ hnN)
  have hflip : ∀ I : Set (Set S), (∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = L₁ ∪ R
    ∧ {c ∈ Γ.C | c ⊆ Δ} = I) →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = L₀ ∪ R ∧ {c ∈ Γ.C | c ⊆ Δ} = I := by
    rintro I ⟨Δ', h1, h2, rfl⟩
    obtain ⟨Δ, h3, h4, h5⟩ := flip_disc hman hG hL₀ hL₁ hR hbG h01 h0R h1R hGR h1 h2
    refine ⟨Δ, h3, h4, ?_⟩
    ext c
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨hc, (h5 c (hd c hc)).mp hs⟩
    · rintro ⟨hc, hs⟩
      exact ⟨hc, (h5 c (hd c hc)).mpr hs⟩
  rcases h with h | ⟨I₁, I₂, h1, h2, h3, h4, h5⟩
  · exact .inl h
  · exact .inr ⟨I₁, I₂, h1, h2, h3, h4.imp (hflip _) id, h5.imp (hflip _) id⟩

theorem conclusion_induct [CompactSpace S] [T2Space S] [ConnectedSpace S]
  (hS : IsSurface S) {Γ : Painting S} (k : ℕ) : ∀ F : Set S, IsOArc F → Γ.IsNormal F →
    (∀ c ∈ Γ.C, Γ.IsInternalCell c → Disjoint (tilde c) F) → (F ∩ Γ.U).ncard = k
      → OArcConclusion S Γ F := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro F hO hnorm hint hk
    have hfin : (F ∩ Γ.U).Finite := Γ.finite_N.subset hnorm
    by_cases hk0 : k = 0
    · have he : F ∩ Γ.U = ∅ := (Set.ncard_eq_zero hfin).mp (hk.trans hk0)
      exact cut_off_paint hS hO (disjoint_iff_inter_eq_empty.mpr he)
    obtain ⟨n, hnF, hnU⟩ := (Set.ncard_pos hfin).mp (by omega)
    have hman := hS.2.2
    have hnN : n ∈ Γ.N := hnorm ⟨hnF, hnU⟩
    obtain ⟨G, L₀, L₁, u, v, hG, hl₀, hl₁, hbG, h01, hGF, hGU, hnL, hnu, hnv⟩
      := exists_bigon hS hO hnorm hint hnF hnU
    have hsF : L₀ ⊆ F := hGF ▸ inter_subset_right
    obtain ⟨R, hR, hun, h0R⟩ := oarc_split hO hl₀ hsF
    have hRF : R ⊆ F := hun ▸ subset_union_right
    have hsG : L₁ ⊆ G := (hbG ▸ subset_union_right).trans (discBd_subset G)
    have hsG₀ : L₀ ⊆ G := (hbG ▸ subset_union_left).trans (discBd_subset G)
    have hGR : G ∩ R = {u, v} := by
      apply subset_antisymm
      · rintro x ⟨hx, hxR⟩
        have h1 : x ∈ L₀ := hGF ▸ ⟨hx, hRF hxR⟩
        exact h0R ▸ ⟨h1, hxR⟩
      · rw [← h0R]
        exact fun x hx => ⟨hsG₀ hx.1, hx.2⟩
    have h1R : L₁ ∩ R = {u, v} := by
      apply subset_antisymm
      · exact fun x hx => hGR ▸ ⟨hsG hx.1, hx.2⟩
      · rintro x (rfl | rfl)
        · exact ⟨hl₁.left_mem, hR.left_mem⟩
        · exact ⟨hl₁.right_mem, hR.right_mem⟩
    have hF' : IsOArc (L₁ ∪ R) := oArc_of_lines hl₁ hR h1R
    have hnL₁ : n ∉ L₁ := fun h => by
      rcases (h01 ▸ ⟨hnL, h⟩ : n ∈ ({u, v} : Set S)) with h | h
      · exact hnu h
      · exact hnv h
    have hnR : n ∉ R := fun h => by
      rcases (h0R ▸ ⟨hnL, h⟩ : n ∈ ({u, v} : Set S)) with h | h
      · exact hnu h
      · exact hnv h
    have hsub : (L₁ ∪ R) ∩ Γ.U ⊆ (F ∩ Γ.U) \ {n} := by
      rintro x ⟨hx | hx, hxU⟩
      · have h1 : x = n := hGU ⟨hsG hx, hxU⟩
        exact absurd hx (h1 ▸ hnL₁)
      · exact ⟨⟨hRF hx, hxU⟩, fun h => hnR ((mem_singleton_iff.mp h) ▸ hx)⟩
    have hnorm' : Γ.IsNormal (L₁ ∪ R) := fun x hx => hnorm (hsub hx).1
    have hint' : ∀ c ∈ Γ.C, Γ.IsInternalCell c → Disjoint (tilde c) (L₁ ∪ R) := fun c hc hi
      => disjoint_left.mpr fun x hx hxF => by
      have hxU : x ∈ Γ.U := closure_minimal (fun z hz => (arcComponentsIn_subset hc hz).1)
        Γ.isClosed_U hx.1
      exact disjoint_left.mp (hint c hc hi) hx (hsub ⟨hxF, hxU⟩).1.1
    have hcard : ((L₁ ∪ R) ∩ Γ.U).ncard < k := by
      have h1 := Set.ncard_le_ncard hsub (hfin.subset sdiff_subset)
      rw [Set.ncard_sdiff_singleton_of_mem (show n ∈ F ∩ Γ.U from ⟨hnF, hnU⟩), hk] at h1
      omega
    have h2 := ih _ hcard _ hF' hnorm' hint' rfl
    rw [← hun]
    exact conclusion_flip hman hG hl₀ hl₁ hR hbG h01 h0R h1R hGR hGU hnN h2

/-- The surface part of (5.4) of Graph Minors XVII, page 173. -/
theorem cutNormalOArc : CutNormalOArcPaintingStatement := by
  unfold CutNormalOArcPaintingStatement
  intro S _ hcS ht2 hconn hS Γ F hnorm hO hint
  exact conclusion_induct hS _ F hO hnorm hint rfl

end GraphMinor.GM17
