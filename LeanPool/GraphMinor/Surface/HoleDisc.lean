/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.SideCut
public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.Surface.Ring
public import LeanPool.GraphMinor.Surface.ModelCriterion
public import LeanPool.GraphMinor.Surface.DiscsInSurface
public import LeanPool.GraphMinor.Surface.Disc

/-!
# The closure of an open disc

The operations of adding a crosscap or a handle remove an open disc `Λ` from a surface, and they say
nothing about its closure. Here we show that the closure is a closed disc, if the frontier of `Λ` is
an `O`-arc with points outside the closure of `Λ` arbitrarily near each of its points
(`closure_disc`).

By `side_manifold`, the closure of `Λ` is a surface with the frontier as its boundary, so by the
classification it has a model with one hole. To see that this model is a disc, we paste a disc on
the hole. The result is the union of a closed disc around the pasted disc and a closed disc in `Λ`,
which exists by Epstein's theorem. So the result is a sphere, and the classification says that the
model is a disc (`model_genus_zero`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

theorem cuffs_eq_of_isConnected {Y : Type u} [TopologicalSpace Y] (h : IsConnected
  (bd Y)) : cuffs Y = {bd Y} := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h.2.connectedComponentIn hx
  · rintro rfl
    obtain ⟨x, hx⟩ := h.1
    exact ⟨x, hx, h.2.connectedComponentIn hx⟩

/-- A model with one hole has one cuff, which is its whole boundary. -/
theorem model_one_cuff (a b : ℕ) : ∃ C, IsCuff C ∧ bd (SurfaceModel a b 1) = C := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b 1
  have := ht
  have h1 := ncard_cuffs hf
  obtain ⟨C, hC⟩ := Set.ncard_eq_one.mp h1
  refine ⟨C, (show C ∈ cuffs (SurfaceModel a b 1) by rw [hC]; exact mem_singleton C), ?_⟩
  ext x
  constructor
  · intro hx
    have h2 : connectedComponentIn (bd (SurfaceModel a b 1)) x ∈ cuffs (SurfaceModel a b 1)
      := ⟨x, hx, rfl⟩
    rw [hC] at h2
    rw [← mem_singleton_iff.mp h2]
    exact mem_connectedComponentIn hx
  · intro hx
    have h2 : C ∈ cuffs (SurfaceModel a b 1) := hC ▸ mem_singleton C
    obtain ⟨y, hy, rfl⟩ := h2
    exact connectedComponentIn_subset _ _ hx

/-- The model without holes and without handles and cross-caps is a sphere. -/
theorem isSphere_model : IsSphere (SurfaceModel 0 0 0) := by
  have hS := (isSurface_model 0 0 1).1
  have ht2 := hS.2.1
  obtain ⟨C, hC, hb⟩ := model_one_cuff 0 0
  obtain ⟨S', tS', ι, Δ, hS', hι, hΔ, hu, hm, hdb, -⟩ := paste_disc.{0} _ C hS hC
  obtain ⟨-, ⟨e⟩⟩ := paste_model hS hC hS' hι hΔ hu hm hdb (Homeomorph.refl _)
  obtain ⟨d⟩ := nonempty_disc_homeo
  have ht2' : T2Space S' := hS'.2.1
  have hcS' : CompactSpace S' := hS'.1
  have hr : IsClosedDisc (range ι) := ⟨d.symm.trans hι.isEmbedding.toHomeomorph⟩
  have hrb : discBd (range ι) = ι '' C := by
    have h1 := image_bd_homeomorph hι.isEmbedding.toHomeomorph
    rw [discBd, ← h1, image_image, hb]
    rfl
  obtain ⟨T, hTc, hTi, hTr⟩ := exists_sphere_map hr hΔ (hrb.trans hdb.symm) (hm.trans hrb.symm)
  rw [hu] at hTr
  let E : OnePoint EuclideanPlane ≃ₜ S' := hTc.homeoOfEquivCompactToT2 (f
    := Equiv.ofBijective T ⟨hTi, range_eq_univ.mp hTr⟩)
  have e1 : (0 - 1 : ℕ) = 0 := rfl
  exact ⟨(E.trans e).symm⟩

/-- A model with one hole whose interior is an open disc is a closed disc. -/
theorem model_genus_zero {p q : ℕ} {Λ : Set (SurfaceModel p q 1)} (hΛ : IsOpenDisc Λ) (hb : Λ = (bd
  (SurfaceModel p q 1))ᶜ) : p = 0 ∧ q = 0 := by
  have hS := (isSurface_model p q 1).1
  have ht2 := hS.2.1
  obtain ⟨C, hC, hbC⟩ := model_one_cuff p q
  obtain ⟨S', tS', ι, Δ, hS', hι, hΔ, hu, hm, hdb, hbS⟩ := paste_disc.{0} _ C hS hC
  obtain ⟨-, ⟨e⟩⟩ := paste_model hS hC hS' hι hΔ hu hm hdb (Homeomorph.refl _)
  have ht2' : T2Space S' := hS'.2.1
  have hcS' : ConnectedSpace S' := by
    have := (isSurface_model p q (1 - 1)).2
    exact e.symm.surjective.connectedSpace e.symm.continuous
  have hbd : bd S' = ∅ := by
    rw [hbS, ← hbC, sdiff_self, image_empty]
  have hint : ∀ x : S', IsInteriorPoint x := fun x => by
    by_contra h
    have h1 : x ∈ bd S' := h
    rw [hbd] at h1
    exact h1
  obtain ⟨Δ', hΔ', hsub, -, hmeet⟩ := exists_ring hS' hΔ (fun x _ => hint x) isClosed_empty
    (by simp)
  simp only [inter_empty] at hmeet
  have hF : discBd Δ' ⊆ ι '' Λ := fun x hx => by
    have h1 : x ∉ Δ := fun h => (show x ∈ (∅ : Set S') from hmeet ▸ ⟨hx, h⟩)
    rcases (hu ▸ mem_univ x : x ∈ range ι ∪ Δ) with ⟨g, rfl⟩ | h2
    · refine ⟨g, ?_, rfl⟩
      rw [hb, hbC]
      exact fun hg => h1 (hm ▸ (⟨g, hg, rfl⟩ : ι g ∈ ι '' C) : ι g ∈ range ι ∩ Δ).2
    · exact absurd h2 h1
  have hZΔ : ι '' Λ = Δᶜ := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩ h2
      have h3 : ι g ∈ ι '' C := hm ▸ ⟨⟨g, rfl⟩, h2⟩
      obtain ⟨g', hg', he⟩ := h3
      rw [hb, hbC] at hg
      exact hg (hι.injective he ▸ hg')
    · intro h1
      rcases (hu ▸ mem_univ x : x ∈ range ι ∪ Δ) with ⟨g, rfl⟩ | h2
      · refine ⟨g, ?_, rfl⟩
        rw [hb, hbC]
        exact fun hg => h1 (hm ▸ (⟨g, hg, rfl⟩ : ι g ∈ ι '' C) : ι g ∈ range ι ∩ Δ).2
      · exact absurd h2 h1
  have hZ : IsOpenDisc (ι '' Λ) := by
    refine ⟨hZΔ ▸ hΔ.isClosed.isOpen_compl, ?_⟩
    obtain ⟨-, ⟨φ⟩⟩ := hΛ
    exact ⟨φ.trans (hι.isEmbedding.homeomorphImage Λ)⟩
  have hO := hΔ'.isOArc_discBd
  have hdis : Disjoint (discBd Δ') (bd S') := by
    rw [hbd]
    exact disjoint_empty _
  have hnull : IsNullHomotopicOArcIn (ι '' Λ) (discBd Δ') := by
    obtain ⟨φ⟩ := hO
    refine ⟨φ, (IsOpenDisc.isSimplyConnectedSet hZ).2 _ ?_⟩
    rintro _ ⟨w, rfl⟩
    exact hF (φ w).2
  obtain ⟨D, hDZ, hD, hDb⟩ := epstein_first hS' hO hF hdis hnull
  have hsph : IsSphere S' := by
    by_contra hn
    have h1 := (epstein.{0} S' _ _ hS' hcS' hO hF hdis).2.2 D Δ' hD hΔ' hDb rfl hn
    obtain ⟨φ⟩ := hΔ.isOArc_discBd
    have h2 : (φ 1).1 ∈ Δ := discBd_subset Δ (φ 1).2
    have h3 : (φ 1).1 ∈ Δᶜ := hZΔ ▸ hDZ (h1 ▸ hsub h2)
    exact h3 h2
  obtain ⟨E⟩ := hsph
  obtain ⟨E'⟩ := isSphere_model
  have h1 := (modelCriterion.2 p q (1 - 1) 0 0 0).mp ⟨(e.symm.trans E).trans E'.symm⟩
  omega

theorem isOpenEmbedding_inclusion {S : Type u} [TopologicalSpace S] {A B : Set S} (h : A ⊆ B)
  (hA : IsOpen A) : IsOpenEmbedding (inclusion h) :=
  ⟨.inclusion h, by rw [range_inclusion]; exact hA.preimage continuous_subtype_val⟩

/-- In a surface without boundary, the boundary points of a subset are the points of the subset in
the closure of its complement. One direction is invariance of domain. -/
theorem bd_subset_iff {S : Type u} [TopologicalSpace S] (hint : ∀ x : S, IsInteriorPoint x) {X :
  Set S} (x : ↥X) :
    x ∈ bd ↥X ↔ x.1 ∈ closure Xᶜ := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  constructor
  · intro hx
    by_contra h
    apply hx
    have hW : IsOpen (closure Xᶜ)ᶜ := isClosed_closure.isOpen_compl
    have hsub : (closure Xᶜ)ᶜ ⊆ X := fun z hz => by
      by_contra h'
      exact hz (subset_closure h')
    have h1 : IsInteriorPoint (⟨x.1, h⟩ : ↥(closure Xᶜ)ᶜ) := (isInteriorPoint_sub hW).mpr (hint _)
    exact isInteriorPoint_of_isOpenEmbedding (isOpenEmbedding_inclusion hsub hW) h1
  · intro hx hin
    obtain ⟨U, h', g, c, -, h0⟩ := hin.exists_ballChart isOpen_univ (mem_univ _) one_pos
    have h1 : IsOpen ((Subtype.val ∘ g) '' Metric.ball 0 1) :=
      isOpen_image_of_manifold Metric.isOpen_ball (continuous_subtype_val.comp_continuousOn c.gc)
        (fun a ha b hb he => by
        have := Subtype.ext he
        have h2 := congrArg h' this
        rwa [c.hg ha, c.hg hb] at h2) fun _ _ => hman _
    have h2 : x.1 ∈ (Subtype.val ∘ g) '' Metric.ball 0 1 := ⟨0, Metric.mem_ball_self one_pos, by
      simp [h0]⟩
    obtain ⟨y, hy, hy'⟩ := mem_closure_iff.mp hx _ h1 h2
    obtain ⟨z, -, rfl⟩ := hy
    exact hy' (g z).2

/-- **The closure of an open disc is a closed disc**, if its frontier is an `O`-arc off the boundary
and the outside of the closure comes near every point of the frontier. The complement of the open
disc is then a surface near the frontier. -/
theorem closure_disc {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
  (hS : IsSurface S) {Λ : Set S} (hΛ : IsOpenDisc Λ) (hbd : Disjoint (closure Λ) (bd S))
    (hF : IsOArc (closure Λ \ Λ)) (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ) :
    IsClosedDisc (closure Λ) ∧ discBd (closure Λ) = closure Λ \ Λ := by
  have ht2 := hS.2.1
  have hcS := hS.1
  have hΛo : IsOpen Λ := hΛ.1
  have hsub : Λ ⊆ closure Λ := subset_closure
  have hm : closure Λ ∩ Λᶜ = (closure Λ \ Λ) ∪ ∅ := by
    rw [union_empty]
    rfl
  have hside := @side_manifold S _ _ hS (closure Λ) Λᶜ (closure Λ \ Λ) ∅ isClosed_closure
    hΛo.isClosed_compl (by
      rw [eq_univ_iff_forall]
      intro z
      by_cases hz : z ∈ Λ
      · exact .inl (hsub hz)
      · exact .inr hz) hF (hbd.mono_left sdiff_subset) sdiff_subset isClosed_empty hm
          (disjoint_empty _)
    (fun x hx => by
      have : closure Λ \ Λᶜ = Λ := by
        ext z
        simp only [mem_sdiff, mem_compl_iff, not_not]
        exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
      rw [this]
      exact hx.1)
    (fun x hx => by
      have : Λᶜ \ closure Λ = (closure Λ)ᶜ := by
        ext z
        simp only [mem_sdiff, mem_compl_iff]
        exact ⟨fun h => h.2, fun h => ⟨fun h' => h (hsub h'), h⟩⟩
      rw [this]
      exact hout x hx)
  have hopen : IsOpenEmbedding (inclusion hsub) := isOpenEmbedding_inclusion hsub hΛo
  have hG : IsSurface ↥(closure Λ) := by
    refine ⟨isCompact_iff_compactSpace.mp isClosed_closure.isCompact, inferInstance, fun x => ?_⟩
    by_cases hx : x.1 ∈ Λ
    · exact isManifoldPoint_of_isOpenEmbedding hopen (x := ⟨x.1, hx⟩) (isManifoldPoint_sub hΛo
        (hS.2.2 x.1))
    · exact (hside ⟨x.2, hx⟩).1
  have hbG : bd ↥(closure Λ) = Subtype.val ⁻¹' (closure Λ \ Λ) := by
    ext x
    constructor
    · intro hx
      refine ⟨x.2, fun h => hx ?_⟩
      have h1 : IsInteriorPoint (⟨x.1, h⟩ : Λ) := by
        refine (isInteriorPoint_sub hΛo).mpr ?_
        by_contra h2
        exact Set.disjoint_left.mp hbd x.2 h2
      exact isInteriorPoint_of_isOpenEmbedding hopen h1
    · exact fun hx => (hside hx).2
  have hval : IsEmbedding (Subtype.val : ↥(closure Λ) → S) := IsEmbedding.subtypeVal
  have himg : Subtype.val '' bd ↥(closure Λ) = closure Λ \ Λ := by
    rw [hbG, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr sdiff_subset
  have hconn : ConnectedSpace ↥(closure Λ) := isConnected_iff_connectedSpace.mp
    (IsOpenDisc.isPathConnected hΛ).isConnected.closure
  have hbc : IsConnected (bd ↥(closure Λ)) := by
    obtain ⟨φ⟩ := id hF
    refine ⟨?_, ?_⟩
    · have h1 : (φ 1).1 ∈ Subtype.val '' bd ↥(closure Λ) := by
        rw [himg]
        exact (φ 1).2
      obtain ⟨y, hy, -⟩ := h1
      exact ⟨y, hy⟩
    · refine hval.isInducing.isPreconnected_image.mp ?_
      rw [himg]
      exact hF.isPreconnected
  obtain ⟨p, q, c, ⟨e⟩⟩ := classification.{u} _ hG hconn
  obtain ⟨ht, f, hf⟩ := presents_ew p q c
  have := ht
  have hc1 : c = 1 := by
    rw [← ncard_cuffs hf, ← ncard_cuffs_congr e, cuffs_eq_of_isConnected hbc, ncard_singleton]
  subst hc1
  have hΛ₀ : IsOpenDisc (e '' (Subtype.val ⁻¹' Λ)) := by
    refine ⟨e.isOpenMap _ (hΛo.preimage continuous_subtype_val), ?_⟩
    obtain ⟨-, ⟨φ⟩⟩ := hΛ
    have h1 : Subtype.val '' (Subtype.val ⁻¹' Λ : Set ↥(closure Λ)) = Λ := by
      rw [Subtype.image_preimage_coe]
      exact inter_eq_right.mpr hsub
    exact ⟨φ.trans ((Homeomorph.setCongr h1.symm).trans ((hval.homeomorphImage _).symm.trans
      (e.image _)))⟩
  have hb₀ : e '' (Subtype.val ⁻¹' Λ) = (bd (SurfaceModel p q 1))ᶜ := by
    rw [← image_bd_homeomorph e, ← image_compl_eq e.bijective, hbG]
    congr 1
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_sdiff, not_and, not_not]
    exact ⟨fun h _ => h, fun h => h x.2⟩
  obtain ⟨rfl, rfl⟩ := model_genus_zero hΛ₀ hb₀
  obtain ⟨d⟩ := nonempty_disc_homeo
  exact ⟨⟨(e.trans d).symm⟩, himg⟩

end GraphMinor.Surface
