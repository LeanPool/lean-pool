/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section11d
public import LeanPool.GraphMinor.GM19.SideDisc
public import LeanPool.GraphMinor.GM19.SideShape
import LeanPool.GraphMinor.GM19.Section6Cuff

/-!
# Graph Minors XIX, Section 11: the bites of a flaw and the cuff

Here is what the proof of (11.1) uses of a disjoint feast, one bite at a time. A bite misses the
other cuffs (`IsSideSetting.disjoint_cuff_ins`), so each `ins(F)` is a chord disc of the
closed disc of the cuff (`IsBiteShape.isChordDisc`). If `I(F)` missed the closure of the side, then
`F` could be dropped from the feast (`IsSideSetting.biteArc_meets_side`). So each long side other
than
`S` keeps one piece when the arcs `I(F)` are taken out (`IsSideSetting.keep_of_meets`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

namespace TangleDatum

variable {D : TangleDatum cap χ}

variable (hS : IsSurface S)
include hS

omit hS in
omit [T2Space Shat] in
omit [T2Space S] in
omit hS in
/-- The closure of the region of `r` without the region is the cuff. -/
theorem closure_region_sdiff {r : Shat} {Θ : Set S} (hΘ : Θ ∈ cuffs S)
  (hreg : D.rad.regionOf r = cap.cuffDisc Θ) :
    closure (D.rad.regionOf r) \ D.rad.regionOf r = cap.emb '' Θ := by
  rw [hreg, cap.closure_cuffDisc hΘ]
  ext x
  constructor
  · rintro ⟨hx | hx, hn⟩
    · exact absurd hx hn
    · exact hx
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Or.inr (mem_image_of_mem _ hy), fun hd ↦ cap.notMem_range hΘ hd (mem_range_self y)⟩

omit [T2Space S] [T2Space Shat] in
omit hS in
/-- A point of `Σ` on the chord of a bite is an end of the chord. -/
theorem IsBiteShape.Β_range {r Θ F v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di
  Do) {x : S} (hx : cap.emb x ∈ Β) : cap.emb x ∈ Β ∩ L := by
  have hin : cap.emb x ∈ cap.emb '' Θ := by
    have := h.Β_E hx
    rw [cap.closure_cuffDisc h.cuff] at this
    rcases this with h' | h'
    · exact absurd (mem_range_self x) (cap.notMem_range h.cuff h')
    · exact h'
  have : cap.emb x ∈ Β ∩ cap.emb '' Θ := ⟨hx, hin⟩
  rw [h.meet] at this
  rw [h.Β_L]
  exact this

omit [T2Space S] [T2Space Shat] in
omit hS in
/-- The circuit and the line of a bite have the same points in `Σ`. -/
theorem IsBiteShape.preimage_U {r Θ F v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A'
  Di Do) : cap.emb ⁻¹' F.U = cap.emb ⁻¹' L := by
  ext x
  constructor
  · intro hx
    change cap.emb x ∈ F.U at hx
    rw [h.F_eq] at hx
    rcases hx with hx | hx
    · exact (h.Β_range hx).2
    · exact hx
  · intro hx
    change cap.emb x ∈ F.U
    rw [h.F_eq]
    exact Or.inr hx

omit [T2Space S] in
omit hS in
/-- **The arc and its complement in the cuff.** -/
theorem IsBiteShape.cuff_mem_A' {r Θ F v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂ Β L A
  A' Di Do) {x : S} (hx : x ∈ Θ) :
    x ∈ cap.emb ⁻¹' A' ↔ x ∉ cap.emb ⁻¹' D.biteArc r F := by
  rw [mem_preimage, mem_preimage, h.biteArc_eq]
  constructor
  · rintro hA' (hA | hend)
    · have h₁ : cap.emb x ∈ Di := Surface.discBd_subset _ (h.bd_i ▸ Or.inl hA)
      have h₂ : cap.emb x ∈ Do := Surface.discBd_subset _ (h.bd_o ▸ Or.inl hA')
      have h₃ : cap.emb x ∈ Β := h.inter ▸ ⟨h₁, h₂⟩
      exact (h.A_sub hA).2 (h.meet ▸ ⟨h₃, mem_image_of_mem _ hx⟩)
    · exact (h.A'_sub hA').2 hend
  · intro hn
    rcases h.cover ⟨mem_image_of_mem _ hx, fun he ↦ hn (Or.inr he)⟩ with h' | h'
    · exact absurd (Or.inl h') hn
    · exact h'

omit [T2Space S] hS in
omit [T2Space Shat] in
/-- The complement of the arc is connected. -/
theorem IsBiteShape.isPreconnected_A' {r Θ F v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂ Β
  L A A' Di Do) : IsPreconnected (cap.emb ⁻¹' A') := by
  rw [← cap.isEmbedding.isInducing.isPreconnected_image, image_preimage_eq_of_subset fun x hx ↦
    image_subset_range _ _ (h.A'_sub hx).1]
  exact h.A'_conn

omit [T2Space S] in
omit hS in
/-- A bite whose arc is all of `ins(F)` on the cuff is a chord disc of the closed disc of the cuff.
-/
theorem IsBiteShape.isChordDisc {r Θ F v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂ Β L A
  A' Di Do)
    (ha : D.biteArc r F = D.ins F ∩ (closure (D.rad.regionOf r) \ D.rad.regionOf r)) :
    IsChordDisc (closure (cap.cuffDisc Θ)) (D.ins F) Β (cap.emb v₁) (cap.emb v₂) := by
  have : ConnectedSpace Shat := cap.connected
  have hT := cap.isClosedSurface
  have hi := D.ins_spec h.circuit h.lt
  have hbd : discBd (D.ins F) = F.U := hi.2.2.2.1
  have hEb : discBd (closure (cap.cuffDisc Θ)) = cap.emb '' Θ := cap.cuffDisc_bd Θ h.cuff
  have hdE : cap.cuffDisc Θ = discInt (closure (cap.cuffDisc Θ)) := cap.cuffDisc_eq_discInt
    h.cuff
  refine ⟨hi.2.2.1, fun he ↦ h.ne (cap.isEmbedding.injective he), h.line,
    hbd ▸ h.Β_F, h.Β_E, ?_, ?_, ?_⟩
  · rw [hEb]
    exact h.meet
  · rw [← hdE, hbd]
    exact fun x hx ↦ h.F_disc x hx.2 hx.1
  · rintro x ⟨hxE, hxb⟩ hxΒ
    rw [hEb] at hxE
    rw [hbd] at hxb
    have hxI : x ∈ D.biteArc r F := by
      rw [ha, closure_region_sdiff h.cuff h.reg]
      exact ⟨D.U_subset_ins h.circuit h.lt hxb, hxE⟩
    rw [h.biteArc_eq] at hxI
    rcases hxI with hA | hend
    · refine ⟨discInt Di, fun y hy ↦ h.in_E hy, fun y hy ↦ discInt_subset _ (h.in_ins hy),
        h.di.nonempty_discInt, h.di.isPreconnected_discInt, ?_⟩
      rw [closure_discInt h.di]
      exact Surface.discBd_subset _ (h.bd_i ▸ Or.inl hA)
    · exact absurd (h.meet.symm ▸ hend : x ∈ Β ∩ cap.emb '' Θ).1 hxΒ

end TangleDatum

namespace TangleDatum.IsSideSetting

variable {D : TangleDatum cap χ} {side Θ : Set S} {r : Shat} {N : ℕ} (X : D.IsSideSetting side Θ r
  N)
include X

/-- **A bite misses the other cuffs.** A vertex of the bite on another cuff would bring the two
poles too close together. -/
theorem disjoint_cuff_ins (hS : IsSurface S) (hgt : ((N + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad)
  {F : Drawing Shat} (hc : F.E.ncard ≤ 2 * N) {v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂
    Β L A A' Di Do) {Θ' : Set S}
    (hΘ' : Θ' ∈ cuffs S) (hne : Θ' ≠ Θ) : Disjoint (closure (cap.cuffDisc Θ')) (D.ins F) := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨p, hp, hpd, hreg'⟩ := D.rad.exists_pole hΘ'
  have hrd : r ∈ cap.cuffDisc Θ := by
    rw [← h.reg]
    exact (D.rad.regionOf_mem h.pole.1).2
  have hEE : Disjoint (closure (cap.cuffDisc Θ')) (closure (cap.cuffDisc Θ))
    := cap.cuffDisc_disjoint _ hΘ' _ h.cuff hne
  have hri : r ∈ D.ins F := D.U_subset_ins h.circuit h.lt (F.V_subset_U h.r_mem)
  have huniq : ∀ q ∈ D.rad.poles, q ∈ D.ins F → q = r := fun q hq hqi ↦ by
    by_contra hn
    have h₁ := vDist_le_of_ins X.rep_gt h.circuit hc hq h.pole hn hqi hri
    have h₂ := X.far q hq r h.pole hn
    omega
  have hpr : p ≠ r := by
    rintro rfl
    exact disjoint_left.1 hEE (subset_closure hpd) (subset_closure hrd)
  have hpi : p ∉ D.ins F := fun hi ↦ hpr (huniq p hp hi)
  have hcover := U_subset_of_one_pole h.circuit.1 h.reg hrd fun q hq hqF ↦ huniq q hq
    (D.U_subset_ins h.circuit h.lt (F.V_subset_U hqF))
  have hdis : Disjoint (cap.cuffDisc Θ') F.U := disjoint_left.2 fun x hx hxF ↦ by
    rcases hcover hxF with h' | h'
    · exact cap.notMem_range hΘ' hx h'
    · exact disjoint_left.1 hEE (subset_closure hx) (subset_closure h')
  refine disjoint_left.2 fun x hx hxi ↦ ?_
  have hxF := D.cuff_inter_ins_of_disjoint h.circuit h.lt hp hpi hreg' hdis hx hxi
  rw [cap.closure_cuffDisc hΘ'] at hx
  rcases hx with hx | ⟨v, hv, rfl⟩
  · exact disjoint_left.1 hdis hx hxF
  · obtain ⟨hvV, hvF, -⟩ := D.rad.bd_point h.circuit.1 (cuff_subset_bd ⟨Θ', hΘ'⟩ hv) hxF
    have hm₁ : cap.emb v₁ ∈ Β := (h.meet ▸ mem_insert _ _ : cap.emb v₁ ∈ Β ∩ cap.emb '' Θ).1
    obtain ⟨-, hv₁F, -⟩ := D.rad.bd_point h.circuit.1 (cuff_subset_bd ⟨Θ, h.cuff⟩ h.v₁_cuff)
      (h.Β_F hm₁)
    have hd := D.rad.dist_le_of_two_cuffs hS X.h3 h.circuit h.cuff hΘ' hne.symm h.v₁_cuff hv
      h.v₁_mem hvV hv₁F hvF
    revert hd hgt
    generalize Painting.dist D.rad = d
    cases d using ENat.recTopCoe with
    | top =>
      intro _ hd
      simp at hd
    | coe d =>
      intro hgt hd
      norm_cast at hd hgt
      omega

/-- **Each bite of a least feast reaches the closure of the side.** Otherwise the feast keeps its
properties without `F`: the arcs of `ℱ` are disjoint, so a short side touching
`S` lies in one arc, and it is not `I(F)`, since `I(F)` is closed and misses the closure of `S`. -/
theorem biteArc_meets_side (hS : IsSurface S) {ω : List β} {ℱ : Set (Drawing Shat)}
  (hfe : D.IsDisjointFeast r side ω ℱ) (hsm : ∀ F ∈ ℱ, F.E.ncard ≤ 2 * N)
    (hmin : ∀ F ∈ ℱ, ¬ D.IsFeast r side ω (ℱ \ {F})) {F : Drawing Shat} (hF : F ∈ ℱ) :
      (cap.emb ⁻¹' D.biteArc r F ∩ closure side).Nonempty := by
  classical
  by_contra hno
  rw [not_nonempty_iff_eq_empty] at hno
  have hf := hfe.finite_bites
  have hsh : ∀ G ∈ ℱ, ∃ v₁ v₂ Β L A A' Di Do, D.IsBiteShape r Θ G v₁ v₂ Β L A A' Di Do
    := fun G hG ↦ X.shape hS (hfe.all_bites G hG) (hsm G hG)
  have hcl : ∀ G ∈ ℱ, IsClosed (cap.emb ⁻¹' D.biteArc r G) := fun G hG ↦ by
    obtain ⟨_, _, _, _, _, _, _, _, s⟩ := hsh G hG
    exact (s.isLine_biteArc |> isClosed_of_cuffLine).preimage cap.isEmbedding.continuous
  have hdisj : ∀ G ∈ ℱ, ∀ G' ∈ ℱ, G ≠ G' → Disjoint (cap.emb ⁻¹' D.biteArc r G)
    (cap.emb ⁻¹' D.biteArc r G') := fun G hG G' hG' hne ↦ by
    obtain ⟨_, _, _, _, _, _, _, _, s⟩ := hsh G hG
    obtain ⟨_, _, _, _, _, _, _, _, s'⟩ := hsh G' hG'
    refine disjoint_left.2 fun x hx hx' ↦ ?_
    have : cap.emb x ∈ D.ins G ∩ D.ins G' := ⟨(s.biteArc_subset hx).1,
      (s'.biteArc_subset hx').1⟩
    rw [hfe.ins_inter G hG G' hG' hne] at this
    exact D.pole_notMem_range X.pole (this ▸ mem_range_self x)
  have hrest : IsClosed (⋃ G ∈ ℱ \ {F}, cap.emb ⁻¹' D.biteArc r G) :=
    (hf.subset sdiff_subset).isClosed_biUnion fun G hG ↦ hcl G hG.1
  have hshort : ∀ s ∈ χ.Φ.shortSides, (closure s ∩ closure side).Nonempty
    → cap.emb '' s ⊆ D.feastArcUnion r (ℱ \ {F}) := by
    intro s hs hne
    have hsub := hfe.includes_short_sides s hs hne
    have hsS : s ⊆ cap.emb ⁻¹' D.biteArc r F ∪ ⋃ G ∈ ℱ \ {F}, cap.emb ⁻¹' D.biteArc r G
      := fun x hx ↦ by
      obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.1 (hsub (mem_image_of_mem _ hx))
      by_cases he : G = F
      · exact Or.inl (he ▸ hxG)
      · exact Or.inr (mem_biUnion ⟨hG, he⟩ hxG)
    have hconn : IsPreconnected s := hs.1.2.2.1.isConnected.isPreconnected
    have hemp : s ∩ ((cap.emb ⁻¹' D.biteArc r F) ∩ ⋃ G ∈ ℱ \ {F}, cap.emb ⁻¹' D.biteArc r G) = ∅
      := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨-, hx₁, hx₂⟩
      obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.1 hx₂
      exact disjoint_left.1 (hdisj F hF G hG.1 (fun he ↦ hG.2 he.symm)) hx₁ hxG
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hconn _ _ (hcl F hF) hrest hsS hemp with
      hA | hB
    · exfalso
      obtain ⟨a, ha₁, ha₂⟩ := hne
      have : a ∈ cap.emb ⁻¹' D.biteArc r F := closure_minimal hA (hcl F hF) ha₁
      have hm : a ∈ cap.emb ⁻¹' D.biteArc r F ∩ closure side := ⟨this, ha₂⟩
      rw [hno] at hm
      exact hm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.1 (hB hx)
      exact mem_biUnion hG hxG
  refine hmin F hF ⟨hf.subset sdiff_subset, fun G hG ↦ hfe.all_bites G hG.1,
    (ncard_le_ncard sdiff_subset hf).trans hfe.card_le, hshort, ?_⟩
  have heq : side \ cap.emb ⁻¹' D.feastArcUnion r (ℱ \ {F}) = side \ cap.emb ⁻¹' D.feastArcUnion r
    ℱ := by
    ext x
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, fun h₃ ↦ h₂ ?_⟩
      obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.1 h₃
      refine mem_biUnion (⟨hG, ?_⟩ : G ∈ ℱ \ {F}) hxG
      intro he
      rw [mem_singleton_iff.1 he] at hxG
      have hm : x ∈ cap.emb ⁻¹' D.biteArc r F ∩ closure side := ⟨hxG, subset_closure h₁⟩
      rw [hno] at hm
      exact hm
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, fun h₃ ↦ h₂ ?_⟩
      obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.1 h₃
      exact mem_biUnion hG.1 hxG
  rw [heq]
  exact hfe.component_omits

/-- **A long side other than `S` keeps one piece.** Each arc `I(F)` holds a point of the closure of
`S`, which is off the other side, so taking out the arcs one at a time leaves
a connected part of the side. -/
theorem keep_of_meets (hS : IsSurface S) {ℱ : Finset (Drawing Shat)} {s : Set S} (hsΘ : s ⊆ Θ)
  (hc : IsPathConnected s) (hdis : Disjoint (closure side) s)
    (hshape : ∀ F ∈ ℱ, ∃ A' : Set Shat, IsPreconnected (cap.emb ⁻¹' A') ∧ ∀ x ∈ Θ,
      (x ∈ cap.emb ⁻¹' A' ↔ x ∉ cap.emb ⁻¹' D.biteArc r F) ∧ cap.emb ⁻¹' A' ⊆ Θ)
    (hm : ∀ F ∈ ℱ, (cap.emb ⁻¹' D.biteArc r F ∩ closure side).Nonempty) :
    s \ (⋃ F ∈ ℱ, cap.emb ⁻¹' D.biteArc r F) = ∅ ∨ IsPathConnected (s \ ⋃ F ∈ ℱ, cap.emb ⁻¹'
      D.biteArc r F) := by
  classical
  have hO : IsOArc Θ := ⟨cuffPar hS ⟨Θ, X.cuff⟩⟩
  induction ℱ using Finset.induction_on with
  | empty =>
    right
    simpa using hc
  | insert F ℱ hF ih =>
    have ih' := ih (fun G hG ↦ hshape G (Finset.mem_insert_of_mem hG)) fun G hG ↦ hm G
      (Finset.mem_insert_of_mem hG)
    obtain ⟨A', hconn, hA'⟩ := hshape F (Finset.mem_insert_self _ _)
    obtain ⟨w, hw₁, hw₂⟩ := hm F (Finset.mem_insert_self _ _)
    set P := s \ ⋃ G ∈ ℱ, cap.emb ⁻¹' D.biteArc r G with hP
    have hQsub : cap.emb ⁻¹' A' ⊆ Θ := fun x hx ↦ by
      obtain ⟨z, hz⟩ : Θ.Nonempty := ⟨_, (cuffPar hS ⟨Θ, X.cuff⟩ 1).2⟩
      exact (hA' z hz).2 hx
    have hset : s \ (⋃ G ∈ insert F ℱ, cap.emb ⁻¹' D.biteArc r G) = P ∩ cap.emb ⁻¹' A' := by
      ext x
      simp only [hP, mem_sdiff, mem_inter_iff, mem_iUnion₂, Finset.mem_insert, exists_prop,
        not_exists, not_and, forall_eq_or_imp]
      constructor
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨⟨h₁, h₃⟩, (hA' x (hsΘ h₁)).1.2 h₂⟩
      · rintro ⟨⟨h₁, h₃⟩, h₂⟩
        exact ⟨h₁, (hA' x (hsΘ h₁)).1.1 h₂, h₃⟩
    rw [hset]
    rcases ih' with h' | h'
    · left
      rw [h', empty_inter]
    · refine oArc_inter_isPathConnected hO (w := w) (?_) (fun x hx ↦ ⟨hsΘ hx.1,
        ?_⟩) (fun x hx ↦ ⟨hQsub hx, ?_⟩) h'.isConnected.isPreconnected hconn
      · have hws : w ∈ closure Θ := closure_mono X.side_cuff hw₂
        rwa [(isClosed_cuff hS ⟨Θ, X.cuff⟩).closure_eq] at hws
      · rintro rfl
        exact disjoint_left.1 hdis hw₂ hx.1
      · rintro rfl
        exact (hA' x (hQsub hx)).1.1 hx hw₁

end TangleDatum.IsSideSetting

end GraphMinor.GM19
