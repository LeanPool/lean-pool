/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutIArc
public import LeanPool.GraphMinor.Surface.ModelCriterion
import LeanPool.GraphMinor.GM11.Ties

/-!
# Cutting a Möbius band or an annulus along a line

We show that cutting a surface homeomorphic to `SurfaceModel 0 1 1` along a line with ends on the
boundary gives either a closed disc or two components (`exists_cut_band`). This repeats the case of
a
connected cut in `cutIArc`, and keeps the model that the word gives. A closed curve that misses the
line of a cut with the disc as result is null-homotopic (`null_of_cut`).
-/

public section

namespace GraphMinor.GM12

open Set Topology Function GraphMinor.Surface

universe u

local notation "𝕀" => unitInterval

/-- A connected cut of the band is a closed disc. -/
theorem exists_cut_band {S : Type u} [TopologicalSpace S] [ConnectedSpace S] {F : Set S} {s t : S}
    (hS : IsSurface S) (hst : s ≠ t) (hF : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t)
    (hM : Nonempty (S ≃ₜ SurfaceModel 0 1 1)) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y
      ∧ IsCutting ψ F ∧
      ∃ X X' : Set Y, X ∪ X' = ψ ⁻¹' F ∧ Disjoint X X' ∧ IsLine X ∧ IsLine X' ∧
        (Nonempty (Y ≃ₜ ClosedUnitDisc) ∨ ∃ W₁ W₂ : Set Y, X ⊆ W₁ ∧ X' ⊆ W₂ ∧ IsClopen W₁ ∧
          IsClopen W₂ ∧ W₁ ∪ W₂ = univ ∧ Disjoint W₁ W₂) := by
  have hcS : CompactSpace S := hS.1
  have ht2 : T2Space S := hS.2.1
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hst hF hl
  have hcY : CompactSpace Y := hY.1
  refine ⟨Y, tY, t2Y, ψ, hY, hψ, ?_⟩
  have hFc : IsClosed F := hl.isCompact.isClosed
  have hPc := hP
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, b1, b2, h7, h8, h9, h10⟩ := hP
  have hline₁ : IsLine X := by
    obtain ⟨f, -⟩ := l1
    exact ⟨f⟩
  have hline₂ : IsLine X' := by
    obtain ⟨f, -⟩ := l2
    exact ⟨f⟩
  refine ⟨X, X', hun, hd, hline₁, hline₂, ?_⟩
  obtain ⟨a₀, ξ, η, L, ha0, ha1, himξ, himη, hiξ, hiη⟩ := exists_arcLift hPc hψ
  have hXb : X ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
  have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
  have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
  have hex : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hx : ξ 0 ∈ X := himξ ▸ ⟨0, hex, rfl⟩
  have hy : η 0 ∈ X' := himη ▸ ⟨0, hex, rfl⟩
  have hξm : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ X := fun u hu => himξ ▸ ⟨u, hu, rfl⟩
  have hηm : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ X' := fun u hu => himη ▸ ⟨u, hu, rfl⟩
  have hdcuff := cuff_statement.{u} Y hY
  obtain ⟨eM⟩ := hM
  have hcrit := modelCriterion.2
  rcases cut_comps hψ hY pX pX' hun hx hy with hYc | ⟨W₁, W₂, -, -, hX₁, hX₂, hW₁, hW₂, hU, hdW, -,
    -⟩
  · left
    obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{u} Y hY hYc
    have hC : connectedComponentIn (bd Y) (ξ 0) ∈ cuffs Y := ⟨_, hXb hx, rfl⟩
    have hC' : connectedComponentIn (bd Y) (η 0) ∈ cuffs Y := ⟨_, hXb' hy, rfl⟩
    have hXC := pX.subset_connectedComponentIn hx hXb
    have hXC' := pX'.subset_connectedComponentIn hy hXb'
    by_cases hCC : connectedComponentIn (bd Y) (ξ 0) = connectedComponentIn (bd Y) (η 0)
    · have hη₀ : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ connectedComponentIn (bd Y) (ξ 0) := fun u hu
        => hCC ▸ hXC' (hηm u hu)
      obtain ⟨i, hi, φ, g, hg, hs⟩ := exists_one_hole e hC
      obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ := orient_lift L φ
        (fun u hu => hXC (hξm u hu)) hiξ hiη
      obtain ⟨hN, hLf⟩ := erase_facts c i
      have hξ' : ∀ u ∈ Icc (0 : ℝ) 1, ξ' u ∈ X := fun u hu => by
        rw [← himξ, ← hxim]
        exact ⟨u, hu, rfl⟩
      have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by
        rw [← himη, ← heim]
        exact ⟨u, hu, rfl⟩
      obtain ⟨σ, g', hp, -, p, q, hpq, e1, e2, e3⟩ := arc_one_aux hY L' hψ.1 hψ.2.1 hC φ hi hLf hg
        hs hmc hmm hmξ
        (fun u hu => hCC ▸ hXC' (hη' u hu)) hix hie (fun u hu v hv he => Set.disjoint_left.mp hd
          (hξ' u hu) (he ▸ hη' v hv))
      have hn := nf_blkB (a := a) (b := b) (c := c) hi hN hLf σ
      have hlen := length_erase_range hi
      have : Nonempty S := ⟨s⟩
      cases σ with
      | false =>
        obtain ⟨w, h5, h6⟩ := hn.1 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen, show c - 1 + 2 = c + 1 by omega] at e'
        have := (hcrit _ _ _ _ _ _).mp ⟨e'.symm.trans eM⟩
        omega
      | true =>
        obtain ⟨w, h5, h6⟩ := hn.2 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        rw [hlen, show c - 1 + 1 = c by omega] at e'
        have h := (hcrit _ _ _ _ _ _).mp ⟨e'.symm.trans eM⟩
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        have hc : c = 1 := by omega
        subst ha hb hc
        obtain ⟨d⟩ := nonempty_disc_homeo
        exact ⟨e.trans d⟩
    · have hdis := cuffs_disjoint hC hC' hCC
      obtain ⟨i, hi, j, hj, hij, φ, φ', g, hg, hs, hs'⟩ := exists_two_holes e hC hC' hCC
      obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ := orient_lift L φ
        (fun u hu => hXC (hξm u hu)) hiξ hiη
      obtain ⟨hN, hLf⟩ := erase_erase_facts c i j
      have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu => by
        rw [← himη, ← heim]
        exact ⟨u, hu, rfl⟩
      obtain ⟨σ, g', hp, -⟩ := arc_two_aux hY L' hψ.1 hψ.2.1 hC hC' (hdcuff.2.2 _
        hC).isCompact.isClosed
        (hdcuff.2.2 _ hC').isCompact.isClosed hdis φ φ' hij hi hj hLf hg hs hs' hmc hmm hmξ
          (fun u hu => hXC' (hη' u hu)) hix hie
      have hn := nf_blkA (a := a) (b := b) (c := c) hij hi hj hN hLf σ
      have hlen := length_erase_erase hij hi hj
      have : Nonempty S := ⟨s⟩
      cases σ with
      | false =>
        obtain ⟨w, h5, h6⟩ := hn.1 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        have h := (hcrit _ _ _ _ _ _).mp ⟨e'.symm.trans eM⟩
        omega
      | true =>
        obtain ⟨w, h5, h6⟩ := hn.2 rfl
        obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
        have h := (hcrit _ _ _ _ _ _).mp ⟨e'.symm.trans eM⟩
        omega
  · exact .inr ⟨W₁, W₂, hX₁, hX₂, hW₁, hW₂, hU, hdW⟩

/-- Cutting an annulus along a line between its two cuffs gives a closed disc. -/
theorem exists_cut_annulus {S : Type u} [TopologicalSpace S] [ConnectedSpace S] {F : Set S} {s t :
  S}
    (hS : IsSurface S) (hst : s ≠ t) (hF : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t)
    (hM : Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (hne : connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (ψ : Y → S), IsSurface Y ∧ IsCutting ψ F ∧
      Nonempty (Y ≃ₜ ClosedUnitDisc) := by
  obtain ⟨Y, tY, ψ, hY, hψ, h1, -, -⟩ := cutIArc S F s t hS inferInstance hst hF hl
  obtain ⟨-, a, b, c, ⟨e₁⟩, ⟨e₂⟩⟩ := h1 hne
  obtain ⟨eM⟩ := hM
  have h := modelCriterion.2 _ _ _ _ _ _ |>.mp ⟨e₁.symm.trans eM⟩
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  have hc : c = 1 := by omega
  subst ha hb hc
  obtain ⟨d⟩ := nonempty_disc_homeo
  exact ⟨Y, tY, ψ, hY, hψ, ⟨e₂.trans d⟩⟩

/-- A closed curve that misses the line of a cut whose result is a closed disc is null-homotopic. -/
theorem null_of_cut {S Y : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace Y]
  [CompactSpace Y]
    {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F) (e : Y ≃ₜ ClosedUnitDisc) (c : C(Circle, S))
    (hc : ∀ x, c x ∉ F) : ClosedCurveIsNullHomotopicIn univ c := by
  classical
  have hsurj := hψ.2.1
  have hlift : ∀ x, ∃ y, ψ y = c x := fun x => hsurj _
  choose l hl using hlift
  have hunique : ∀ x y, ψ y = c x → y = l x := fun x y hy =>
    hψ.2.2.1 (show y ∈ ψ ⁻¹' Fᶜ by simpa [hy] using hc x)
      (show l x ∈ ψ ⁻¹' Fᶜ by simpa [hl x] using hc x) (hy.trans (hl x).symm)
  have hlc : Continuous l := by
    rw [continuous_iff_isClosed]
    intro K hK
    have he : l ⁻¹' K = c ⁻¹' (ψ '' K) := by
      ext x
      constructor
      · intro hx
        exact ⟨l x, hx, hl x⟩
      · rintro ⟨y, hy, he⟩
        change l x ∈ K
        rw [← hunique x y he]
        exact hy
    rw [he]
    exact (hK.isCompact.image hψ.1).isClosed.preimage c.continuous
  have hcv : Convex ℝ ClosedUnitDisc := convex_closedBall 0 1
  have h0 : (0 : EuclideanPlane) ∈ ClosedUnitDisc := by simp [ClosedUnitDisc]
  let H : Circle × 𝕀 → ClosedUnitDisc := fun p => ⟨(1 - p.2.1) • (e (l p.1)).1, by
    have := hcv h0 (e (l p.1)).2 p.2.2.1 (sub_nonneg.mpr p.2.2.2) (by ring)
    simpa using this⟩
  have hH : Continuous H := by
    refine Continuous.subtype_mk ?_ _
    have : Continuous fun p : Circle × 𝕀 => (e (l p.1)).1 :=
      continuous_subtype_val.comp (e.continuous.comp (hlc.comp continuous_fst))
    fun_prop
  let z₀ : Y := e.symm ⟨0, h0⟩
  refine ⟨ψ z₀, mem_univ _, ⟨⟨fun p => ψ (e.symm (H p)), hψ.1.comp (e.symm.continuous.comp hH)⟩,
    fun _ => mem_univ _, ?_, ?_⟩⟩
  · intro x
    change ψ (e.symm (H (x, 0))) = c x
    have : H (x, 0) = e (l x) := Subtype.ext (by simp [H])
    rw [this, e.symm_apply_apply, hl]
  · intro x
    change ψ (e.symm (H (x, 1))) = ψ z₀
    have : H (x, 1) = ⟨0, h0⟩ := Subtype.ext (by simp [H])
    rw [this]

/-- A connected set off the cut line that holds every boundary point off the line rules out a cut
with two components. The side that the set misses would have boundary only on one lift of the line,
which is a line, but its boundary includes an `O`-arc. -/
theorem no_split {S Y : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] (hY : IsSurface Y) {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F)
      (hF : IsClosed F)
    {X X' : Set Y} (hu : X ∪ X' = ψ ⁻¹' F) (hl : IsLine X) (hl' : IsLine X')
    {W₁ W₂ : Set Y} (hX₁ : X ⊆ W₁) (hX₂ : X' ⊆ W₂) (hW₁ : IsClopen W₁) (hW₂ : IsClopen W₂)
    (hU : W₁ ∪ W₂ = univ) (hdW : Disjoint W₁ W₂) {G : Set S} (hG : IsPreconnected G)
    (hGF : Disjoint G F) (hbd : bd S \ F ⊆ G) : False := by
  have hcuff := cuff_statement.{u} Y hY
  have hinj : ∀ {y y' : Y}, ψ y = ψ y' → ψ y ∉ F → y = y' := fun {y y'} he hn =>
    hψ.2.2.1 (show y ∈ ψ ⁻¹' Fᶜ from hn) (show y' ∈ ψ ⁻¹' Fᶜ from fun hm => hn (he.symm ▸ hm)) he
  have key : ∀ {Z Z' W W' : Set Y}, IsLine Z' → Z' ⊆ W' → Z ⊆ W → Z ∪ Z' = ψ ⁻¹' F → IsClopen W' →
      Disjoint W W' → W ∪ W' = univ → G ⊆ ψ '' W → False := by
    intro Z Z' W W' hL hZ' hZ hun hcl hdj hcov hGW
    obtain ⟨f⟩ := id hL
    have hy₀ := (f 0).2
    have hbdZ : Z' ⊆ bd Y := fun z hz => hψ.2.2.2.2 (hun ▸ Or.inr hz)
    have hC : connectedComponentIn (bd Y) (f 0).1 ∈ cuffs Y := ⟨_, hbdZ hy₀, rfl⟩
    have hsub : connectedComponentIn (bd Y) (f 0).1 ⊆ W' :=
      isPreconnected_connectedComponentIn.subset_isClopen hcl
        ⟨_, mem_connectedComponentIn (hbdZ hy₀), hZ' hy₀⟩
    refine GM11.not_isOArc_of_subset_line hL (hcuff.2.2 _ hC) fun y hy => ?_
    by_contra hn
    have hyW := hsub hy
    have hyF : ψ y ∉ F := by
      intro hm
      have : y ∈ Z ∪ Z' := hun ▸ hm
      rcases this with h | h
      · exact Set.disjoint_left.mp hdj (hZ h) hyW
      · exact hn h
    have hb := bd_of_bd hψ hF (connectedComponentIn_subset _ _ hy) hyF
    obtain ⟨y', hy', he⟩ := hGW (hbd ⟨hb, hyF⟩)
    have := hinj he (he ▸ hyF)
    subst this
    exact Set.disjoint_left.mp hdj hy' hyW
  have hclo : ∀ {W : Set Y}, IsClopen W → IsClosed (ψ '' W) := fun hW =>
    (hW.1.isCompact.image hψ.1).isClosed
  by_cases h₁ : G ⊆ ψ '' W₁
  · exact key hl' hX₂ hX₁ hu hW₂ hdW hU h₁
  by_cases h₂ : G ⊆ ψ '' W₂
  · exact key hl hX₁ hX₂ (by rwa [Set.union_comm]) hW₁ hdW.symm (by rwa [Set.union_comm]) h₂
  obtain ⟨a, ha, ha'⟩ := not_subset.mp h₁
  obtain ⟨b, hb, hb'⟩ := not_subset.mp h₂
  have hcover : G ⊆ ψ '' W₁ ∪ ψ '' W₂ := by
    intro x _
    obtain ⟨y, rfl⟩ := hψ.2.1 x
    have : y ∈ W₁ ∪ W₂ := hU ▸ mem_univ y
    exact this.imp (mem_image_of_mem _) (mem_image_of_mem _)
  obtain ⟨z, hz, ⟨y₁, h₁', rfl⟩, ⟨y₂, h₂', he⟩⟩ := isPreconnected_closed_iff.mp hG _ _ (hclo hW₁)
    (hclo hW₂)
    hcover ⟨b, hb, (hcover hb).resolve_right hb'⟩ ⟨a, ha, (hcover ha).resolve_left ha'⟩
  have hn : ψ y₁ ∉ F := Set.disjoint_left.mp hGF hz
  have := hinj he.symm hn
  subst this
  exact Set.disjoint_left.mp hdW h₁' h₂'

end GraphMinor.GM12
