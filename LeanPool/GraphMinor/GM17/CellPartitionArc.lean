/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.RegionTools
public import LeanPool.GraphMinor.GM17.ThreeNodeReplace
public import LeanPool.GraphMinor.GM17.IndentMain

/-!
# Arcs of an `O`-arc between marked points

Let `A` be a finite set of marks on an `O`-arc `O`, with at least two marks. The arcs of `O` are the
lines of `O` with ends in `A` and no other marks (`IsArcOf`). In
the graph `H` of the proof of (11.1) of Graph Minors XVII, page 190, a region of `H` meets the
boundary of a region of the painting in one such arc. We
show that two arcs that share a point off `A` are equal, that there are finitely many, and that each
mark lies on exactly two of them.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

local notation "𝕀" => unitInterval

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- A line of `O` with ends in `A` and no other points of `A`. -/
def IsArcOf (O A L : Set X) : Prop := ∃ a b, IsLineWithEnds L a b ∧ L ⊆ O ∧ L ∩ A = {a, b}

omit [T2Space X] in
theorem IsArcOf.subset {O A L : Set X} (h : IsArcOf O A L) : L ⊆ O := by
  obtain ⟨a, b, -, h, -⟩ := h
  exact h

theorem arc_sub_of_inner {O L L' : Set X} {a b a' b' z : X} (hO : IsOArc O)
  (hL : IsLineWithEnds L a b) (hL' : IsLineWithEnds L' a' b') (hLO : L ⊆ O)
    (hL'O : L' ⊆ O) (hA : ∀ x ∈ L', x ∉ ({a', b'} : Set X) → x ∉ ({a, b} : Set X))
      (hz : z ∈ L \ {a, b}) (hz' : z ∈ L' \ {a', b'}) : L' ⊆ L := by
  obtain ⟨M, hM, hu, hi⟩ := oarc_split hO hL hLO
  have hY : O \ {a, b} = (L ∪ M) \ {a, b} := by rw [hu]
  have hcomp := inner_mem_comps hL hM hY hi
  obtain ⟨x, -, hx⟩ := hcomp
  have hpc : IsPreconnected (L' \ {a', b'}) := (GM11.isPathConnected_sdiff_pair
    hL').isConnected.isPreconnected
  have hsub : L' \ {a', b'} ⊆ O \ {a, b} := fun w hw => ⟨hL'O hw.1, hA w hw.1 hw.2⟩
  have hzO : z ∈ connectedComponentIn (O \ {a, b}) x := by rw [hx]; exact hz
  have hle : L' \ {a', b'} ⊆ L \ {a, b} := by
    rw [← hx, connectedComponentIn_eq hzO]
    exact hpc.subset_connectedComponentIn hz' hsub
  exact hL'.subset_closure_diff.trans (closure_minimal (hle.trans sdiff_subset)
    (GM19.isClosed_of_cuffLine hL))

/-- Two arcs that share a point off the marks are equal. -/
theorem arcOf_eq {O A L L' : Set X} {z : X} (hO : IsOArc O) (h : IsArcOf O A L)
  (h' : IsArcOf O A L') (hz : z ∈ L) (hz' : z ∈ L') (hzA : z ∉ A) : L = L' := by
  obtain ⟨a, b, hL, hLO, hLA⟩ := h
  obtain ⟨a', b', hL', hL'O, hL'A⟩ := h'
  have hend : ∀ {L a b}, L ∩ A = {a, b} → ∀ x, x ∈ ({a, b} : Set X) → x ∈ A := fun h x hx =>
    (h.symm.subset hx).2
  have hzn : z ∉ ({a, b} : Set X) := fun h3 => hzA (hend hLA z h3)
  have hzn' : z ∉ ({a', b'} : Set X) := fun h3 => hzA (hend hL'A z h3)
  refine Subset.antisymm (arc_sub_of_inner hO hL' hL hL'O hLO ?_ ⟨hz', hzn'⟩ ⟨hz,
    hzn⟩) (arc_sub_of_inner hO hL hL' hLO hL'O ?_ ⟨hz, hzn⟩ ⟨hz', hzn'⟩)
  · intro x hx hn h3
    exact hn (hLA.subset ⟨hx, hend hL'A x h3⟩)
  · intro x hx hn h3
    exact hn (hL'A.subset ⟨hx, hend hLA x h3⟩)

theorem arcOf_family {O A : Set X} {x y : X} (hO : IsOArc O) (hA : A.Finite) (hAO : A ⊆ O)
  (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    {L | IsArcOf O A L}.Finite ∧ ⋃₀ {L | IsArcOf O A L} = O := by
  obtain ⟨𝓕, hf, hF, hu⟩ := exists_gaps_oarc hO hA hAO hx hy hxy
  have harc : ∀ F ∈ 𝓕, IsArcOf O A F := fun F hFm => by
    obtain ⟨a, -, b, -, h1, h2, h3⟩ := hF F hFm
    exact ⟨a, b, h1, h2, h3⟩
  constructor
  · refine hf.subset fun L hL => ?_
    obtain ⟨a, b, hl, hLO, hLA⟩ := id hL
    obtain ⟨z, hz⟩ := line_inner_nonempty hl
    have hzO : z ∈ ⋃₀ 𝓕 := hu ▸ hLO hz.1
    obtain ⟨F, hFm, hzF⟩ := hzO
    have hzA : z ∉ A := fun h => hz.2 (hLA.subset ⟨hz.1, h⟩)
    rw [arcOf_eq hO hL (harc F hFm) hz.1 hzF hzA]
    exact hFm
  · refine Subset.antisymm (sUnion_subset fun L hL => hL.subset) ?_
    exact hu.ge.trans (sUnion_subset_sUnion harc)

omit [T2Space X] in
/-- Two connected subsets of a line that both contain its first point and another point share a
point off any finite set. -/
theorem lines_overlap {B L L' E : Set X} {x y z z' : X} (hB : IsLineWithEnds B x y)
  (hL : IsPreconnected L) (hL' : IsPreconnected L') (hLB : L ⊆ B) (hL'B : L' ⊆ B)
    (hx : x ∈ L) (hx' : x ∈ L') (hz : z ∈ L) (hz' : z' ∈ L') (hzx : z ≠ x) (hzx' : z' ≠ x)
      (hE : E.Finite) : ∃ p, p ∈ L ∧ p ∈ L' ∧ p ∉ E := by
  obtain ⟨f, hf0, -⟩ := hB
  let g : B → ℝ := fun p => (f.symm p : ℝ)
  have hgc : Continuous g := continuous_subtype_val.comp f.symm.continuous
  have hinj : Function.Injective g := fun p q h => f.symm.injective (Subtype.ext h)
  have hval : ∀ {T : Set X}, T ⊆ B → Subtype.val '' (Subtype.val ⁻¹' T : Set B) = T := fun {T} hT
    => by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hT]
  have hpc : ∀ {T : Set X}, IsPreconnected T → T ⊆ B → IsPreconnected (g ''
    (Subtype.val ⁻¹' T : Set B)) := fun {T} hT hTB => by
    refine IsPreconnected.image ?_ g hgc.continuousOn
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hval hTB]
    exact hT
  have hx0 : g ⟨x, hLB hx⟩ = 0 := by
    have h : (⟨x, hLB hx⟩ : B) = f 0 := Subtype.ext hf0.symm
    simp [g, h]
  have hpos : ∀ {w : X} (hw : w ∈ B), w ≠ x → 0 < g ⟨w, hw⟩ := fun {w} hw hne => by
    refine lt_of_le_of_ne (f.symm _).2.1 fun h => hne ?_
    have h3 := hinj (h.symm.trans hx0.symm)
    exact congrArg Subtype.val h3
  have hIcc : ∀ {T : Set X} {w : X}, IsPreconnected T → (hTB : T ⊆ B) → x ∈ T
    → ∀ hw : w ∈ T, Set.Icc 0 (g ⟨w, hTB hw⟩) ⊆ g '' (Subtype.val ⁻¹' T : Set B)
      := fun {T} {w} hT hTB hxT hw =>
    (hpc hT hTB).Icc_subset ⟨⟨x, hTB hxT⟩, hxT, hx0⟩ ⟨⟨w, hTB hw⟩, hw, rfl⟩
  have hs := lt_min (hpos (hLB hz) hzx) (hpos (hL'B hz') hzx')
  set s := min (g ⟨z, hLB hz⟩) (g ⟨z', hL'B hz'⟩) with hsdef
  have hE' : (g '' (Subtype.val ⁻¹' E : Set B)).Finite := (hE.preimage
    Subtype.val_injective.injOn).image g
  obtain ⟨t, ht, htE⟩ := ((Set.Icc_infinite hs).sdiff hE').nonempty
  obtain ⟨p, hp, hpt⟩ := hIcc hL hLB hx hz ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  obtain ⟨p', hp', hpt'⟩ := hIcc hL' hL'B hx' hz' ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  obtain rfl : p = p' := hinj (hpt.trans hpt'.symm)
  exact ⟨p.1, hp, hp', fun h => htE ⟨p, h, hpt⟩⟩

theorem IsArcOf.isClosed {O A L : Set X} (h : IsArcOf O A L) : IsClosed L := by
  obtain ⟨a, b, h, -, -⟩ := h
  exact GM19.isClosed_of_cuffLine h

/-- Each mark on an `O`-arc with at least two marks lies on exactly two arcs. The arcs off the mark
have closed union, so the arcs at the mark cover a neighbourhood of it. One arc alone cannot do
this, by the other line of `O` between its ends. Two more arcs at the mark would lie in that other
line and overlap there. -/
theorem arcs_at_mark {O A : Set X} {x y a : X} (hO : IsOArc O) (hA : A.Finite) (hAO : A ⊆ O)
  (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) (ha : a ∈ A) :
    {L | IsArcOf O A L ∧ a ∈ L}.ncard = 2 := by
  obtain ⟨hfin, hcov⟩ := arcOf_family hO hA hAO hx hy hxy
  have haO : a ∈ ⋃₀ {L | IsArcOf O A L} := by rw [hcov]; exact hAO ha
  obtain ⟨L, hLa, haL⟩ := haO
  obtain ⟨b, hL⟩ : ∃ b, IsLineWithEnds L a b ∧ L ∩ A = {a, b} := by
    obtain ⟨u, v, h1, -, h3⟩ := id hLa
    rcases (h3 ▸ (⟨haL, ha⟩ : a ∈ L ∩ A) : a ∈ ({u, v} : Set X)) with rfl | rfl
    · exact ⟨v, h1, h3⟩
    · exact ⟨u, h1.symm, by rw [h3, pair_comm]⟩
  obtain ⟨hLl, hLA⟩ := hL
  have hLO := hLa.subset
  obtain ⟨M, hM, hu, hi⟩ := oarc_split hO hLl hLO
  have hinM : ∀ {L'}, IsArcOf O A L' → L' ≠ L → L' ⊆ M := fun {L'} h' hne => by
    obtain ⟨u, v, hl, hl', hlA⟩ := id h'
    refine hl.subset_closure_diff.trans (closure_minimal (fun w hw => ?_)
      (GM19.isClosed_of_cuffLine hM))
    have hwA : w ∉ A := fun h => hw.2 (hlA.subset ⟨hw.1, h⟩)
    have hwO : w ∈ L ∪ M := hu ▸ hl' hw.1
    rcases hwO with h | h
    · exact absurd (arcOf_eq hO h' hLa hw.1 h hwA) hne
    · exact h
  have hsecond : ∃ L', IsArcOf O A L' ∧ a ∈ L' ∧ L' ≠ L := by
    by_contra hno
    push Not at hno
    let T := ⋃₀ {L' | IsArcOf O A L' ∧ a ∉ L'}
    have hTfin : {L' | IsArcOf O A L' ∧ a ∉ L'}.Finite := hfin.subset fun _ h => h.1
    have hTc : IsClosed T := hTfin.isClosed_sUnion fun L' h => h.1.isClosed
    have hMT : M ⊆ T := hM.subset_closure_diff.trans (closure_minimal (fun w hw => ?_) hTc)
    · exact (hMT hM.left_mem).elim fun L' h => h.1.2 h.2
    · have hwO : w ∈ ⋃₀ {L | IsArcOf O A L} := by rw [hcov]; exact hu ▸ .inr hw.1
      obtain ⟨L', hL', hwL'⟩ := hwO
      have hane : a ∉ L' := fun h => by
        have hLL := hno L' hL' h
        rw [hLL] at hwL'
        exact hw.2 (hi.subset ⟨hwL', hw.1⟩)
      exact ⟨L', ⟨hL', hane⟩, hwL'⟩
  obtain ⟨L', hL', haL', hne⟩ := hsecond
  have hset : {L | IsArcOf O A L ∧ a ∈ L} = {L, L'} := by
    ext L₃
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h3, ha3⟩
      by_contra hno
      push Not at hno
      have hother : ∀ {L₄}, IsArcOf O A L₄ → ∃ z ∈ L₄, z ≠ a ∧ IsPreconnected L₄ := fun {L₄} h₄
        => by
        obtain ⟨u, v, hl, -, -⟩ := id h₄
        by_cases h : u = a
        · exact ⟨v, hl.right_mem, fun e => hl.ne' (h.trans e.symm), line_preconnected hl⟩
        · exact ⟨u, hl.left_mem, h, line_preconnected hl⟩
      obtain ⟨z, hz, hza, hpc⟩ := hother hL'
      obtain ⟨z', hz', hza', hpc'⟩ := hother h3
      obtain ⟨p, hp, hp', hpA⟩ := lines_overlap hM hpc hpc' (hinM hL' hne)
        (hinM h3 hno.1) haL' ha3 hz hz' hza hza' hA
      exact hno.2 (arcOf_eq hO h3 hL' hp' hp hpA)
    · rintro (rfl | rfl)
      · exact ⟨hLa, haL⟩
      · exact ⟨hL', haL'⟩
  rw [hset, ncard_pair hne.symm]

omit [T2Space X] in
/-- A property of closed sets of a finite family with connected union is constant if it agrees on
any two sets that meet. -/
theorem arcs_agree {𝓑 : Set (Set X)} {p : Set X → Prop} (hf : 𝓑.Finite) (hB : IsPreconnected
  (⋃₀ 𝓑)) (hcl : ∀ L ∈ 𝓑, IsClosed L) (hag : ∀ L ∈ 𝓑, ∀ L' ∈ 𝓑, (L ∩ L').Nonempty → (p L ↔ p L'))
    {L L' : Set X} (hL : L ∈ 𝓑) (hL' : L' ∈ 𝓑) (hn : L.Nonempty) (hn' : L'.Nonempty) : p L ↔ p L'
      := by
  by_contra hne
  have key : ∀ {M M' : Set X}, M ∈ 𝓑 → M' ∈ 𝓑 → M.Nonempty → M'.Nonempty → p M → ¬ p M' → False
    := fun {M M'} hM hM' hnM hnM' h1 h2 => by
    have hfin : {K | K ∈ 𝓑 ∧ p K}.Finite := hf.subset fun _ h => h.1
    have hfin' : {K | K ∈ 𝓑 ∧ ¬ p K}.Finite := hf.subset fun _ h => h.1
    have hcT := hfin.isClosed_sUnion fun K h => hcl K h.1
    have hcT' := hfin'.isClosed_sUnion fun K h => hcl K h.1
    have hsub : ⋃₀ 𝓑 ⊆ ⋃₀ {K | K ∈ 𝓑 ∧ p K} ∪ ⋃₀ {K | K ∈ 𝓑 ∧ ¬ p K} := fun x ⟨K, hK, hx⟩ => by
      by_cases hp : p K
      · exact .inl ⟨K, ⟨hK, hp⟩, hx⟩
      · exact .inr ⟨K, ⟨hK, hp⟩, hx⟩
    obtain ⟨x, hx⟩ := hnM
    obtain ⟨y, hy⟩ := hnM'
    obtain ⟨z, -, ⟨K₁, h₁, hz₁⟩, ⟨K₂, h₂, hz₂⟩⟩ := isPreconnected_closed_iff.mp hB _ _ hcT hcT'
      hsub ⟨x, ⟨M, hM, hx⟩, ⟨M, ⟨hM, h1⟩, hx⟩⟩ ⟨y, ⟨M', hM', hy⟩, ⟨M', ⟨hM', h2⟩, hy⟩⟩
    exact h₂.2 ((hag K₁ h₁.1 K₂ h₂.1 ⟨z, hz₁, hz₂⟩).mp h₁.2)
  by_cases hp : p L
  · exact key hL hL' hn hn' hp fun h => hne (iff_of_true hp h)
  · exact key hL' hL hn' hn (by
      by_contra h
      exact hne (iff_of_false hp h)) hp

/-- An arc of an `O`-arc with marks `u` and `v` lies in one of the two lines between them. -/
theorem arc_sub_line {O A L C₁ C₂ : Set X} {u v : X} (hO : IsOArc O) (hu : u ∈ A) (hv : v ∈ A)
  (hC₁ : IsLineWithEnds C₁ u v) (hC₂ : IsLineWithEnds C₂ u v) (hun : C₁ ∪ C₂ = O)
    (hL : IsArcOf O A L) : L ⊆ C₁ ∨ L ⊆ C₂ := by
  obtain ⟨a, b, hl, hlO, hlA⟩ := id hL
  obtain ⟨z, hz⟩ := line_inner_nonempty hl
  have hzA : z ∉ A := fun h => hz.2 (hlA.subset ⟨hz.1, h⟩)
  have hzu : z ∉ ({u, v} : Set X) := by
    rintro (rfl | rfl)
    · exact hzA hu
    · exact hzA hv
  have hoff : ∀ x ∈ L, x ∉ ({a, b} : Set X) → x ∉ ({u, v} : Set X) := fun x hx hn h => by
    refine hn (hlA.subset ⟨hx, ?_⟩)
    rcases h with rfl | rfl
    · exact hu
    · exact hv
  rcases (hun ▸ hlO hz.1 : z ∈ C₁ ∪ C₂) with h | h
  · exact .inl (arc_sub_of_inner hO hC₁ hl (hun ▸ subset_union_left) hlO hoff ⟨h, hzu⟩ hz)
  · exact .inr (arc_sub_of_inner hO hC₂ hl (hun ▸ subset_union_right) hlO hoff ⟨h, hzu⟩ hz)

/-- The arcs inside a line between two marks cover it. -/
theorem arcs_cover_line {O A C₁ C₂ : Set X} {u v : X} (hO : IsOArc O) (hA : A.Finite) (hAO : A ⊆ O)
  (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) (hC₁ : IsLineWithEnds C₁ u v)
    (hC₂ : IsLineWithEnds C₂ u v)
    (hun : C₁ ∪ C₂ = O) (hin : C₁ ∩ C₂ = {u, v}) : ⋃₀ {L | IsArcOf O A L ∧ L ⊆ C₁} = C₁ := by
  obtain ⟨hfin, hcov⟩ := arcOf_family hO hA hAO hu hv huv
  refine Subset.antisymm (sUnion_subset fun L h => h.2) ?_
  have hCfin : {L | IsArcOf O A L ∧ L ⊆ C₁}.Finite := hfin.subset fun _ h => h.1
  have hcl := hCfin.isClosed_sUnion fun L h => h.1.isClosed
  refine hC₁.subset_closure_diff.trans (closure_minimal (fun x hx => ?_) hcl)
  have hxO : x ∈ ⋃₀ {L | IsArcOf O A L} := by
    rw [hcov]
    exact hun ▸ .inl hx.1
  obtain ⟨L, hL, hxL⟩ := hxO
  rcases arc_sub_line hO hu hv hC₁ hC₂ hun hL with h | h
  · exact ⟨L, ⟨hL, h⟩, hxL⟩
  · exact (hx.2 (hin.subset ⟨hx.1, h hxL⟩)).elim

end GraphMinor.GM17
