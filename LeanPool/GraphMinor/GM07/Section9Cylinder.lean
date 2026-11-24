/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section9DiscSphere
import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Section8
import LeanPool.GraphMinor.GM07.CuffForest
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.GM12.Section2ChordGap
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.GM12.Section3NormalPuncturedPaths
import LeanPool.GraphMinor.GM12.Section3BoundaryLinked
import LeanPool.GraphMinor.GM12.Section3CandidateExistence
import LeanPool.GraphMinor.GM12.Section3Alpha
import LeanPool.GraphMinor.GM12.Section3NearPlanarCircle
import LeanPool.GraphMinor.GM12.Section3LoopCuffClassification
import LeanPool.GraphMinor.GM12.Section3ThetaSurrounding

/-!
# Proof of Graph Minors VII, (9.3) (pages 244–245)

This file proves the two claims about the punctured cylinder used for (9.3)
on pages 244–245:
- `lemma_9_3_obs`: every `G`-normal `[0, 1]`-arc `R` meeting `F_j` and `barI_j` (`j = 1, 2`)
  contains at least `r` vertices of `G`.
- `lemma_9_3_claim_1`: Claim 1 ("$G$ is boundary-linked in $\Sigma'$", page 244).
- `lemma_9_3_claim_2`: Claim 2 ("As a drawing in $\Sigma'$, $G$ satisfies $\alpha(G) \ge r$",
  page 245).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12

universe u

/-- If a preconnected set `s` is covered by two closed sets `A, B` and meets both `A` and `B`, then
`s` meets `A ∩ B`. -/
theorem preconnected_inter_nonempty_of_closed_cover {X : Type*} [TopologicalSpace X]
    {s A B : Set X} (hs : IsPreconnected s) (hA : IsClosed A) (hB : IsClosed B)
    (hsub : s ⊆ A ∪ B) (ha : (s ∩ A).Nonempty) (hb : (s ∩ B).Nonempty) :
    (s ∩ (A ∩ B)).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have h1 : (s ∩ Bᶜ).Nonempty := ⟨x, hx.1, fun hxB => by
    have : x ∈ s ∩ (A ∩ B) := ⟨hx.1, hx.2, hxB⟩
    rwa [h] at this⟩
  have h2 : (s ∩ Aᶜ).Nonempty := ⟨y, hy.1, fun hyA => by
    have : y ∈ s ∩ (A ∩ B) := ⟨hy.1, hyA, hy.2⟩
    rwa [h] at this⟩
  have hcov : s ⊆ Bᶜ ∪ Aᶜ := fun z hz => by
    by_contra hnz
    rw [mem_union, mem_compl_iff, mem_compl_iff, not_or, not_not, not_not] at hnz
    have : z ∈ s ∩ (A ∩ B) := ⟨hz, hnz.2, hnz.1⟩
    rwa [h] at this
  obtain ⟨z, hz, hzB, hzA⟩ := hs Bᶜ Aᶜ hB.isOpen_compl hA.isOpen_compl hcov h1 h2
  rcases hsub hz with hzA' | hzB'
  · exact hzA hzA'
  · exact hzB hzB'

/-- Every walk in a subdrawing `D` of `G` from a closed set `A` to a closed set `B` with
`A ∪ B = univ` and `A ∩ B ⊆ F` (where `F` is `G`-normal) contains a vertex in `D.V ∩ (G.V ∩ F)`. -/
theorem walk_meets_of_closed_cover {S : Type u} [TopologicalSpace S]
    {D G : Drawing S} (hsub : D.IsSubdrawing G) {F A B : Set S}
    (hnorm : G.IsNormal F) (hA : IsClosed A) (hB : IsClosed B)
    (hcov : A ∪ B = univ) (hAB : A ∩ B ⊆ F)
    {u v : S} (W : GraphWalk D.toGraph u v) (hu : u ∈ A) (hv : v ∈ B) :
    ∃ z ∈ D.V, z ∈ G.V ∩ F := by
  induction W with
  | @nil a ha =>
    exact ⟨a, ha, hsub.1 ha, hAB ⟨hu, hv⟩⟩
  | @cons a b c e hlink rest ih =>
    rcases (hcov ▸ mem_univ b : b ∈ A ∪ B) with hbA | hbB
    · exact ih hbA hv
    · have he : e ∈ D.E := hlink.1
      have ha_cl : a ∈ closure e := by
        have hmem : a ∈ ({a, b} : Set S) := mem_insert a {b}
        rw [← hlink.2.2.2] at hmem
        exact hmem.1
      have hb_cl : b ∈ closure e := by
        have hmem : b ∈ ({a, b} : Set S) := mem_insert_of_mem a rfl
        rw [← hlink.2.2.2] at hmem
        exact hmem.1
      have hpc : IsPreconnected (closure e) := by
        rcases D.edge_cond e he with ⟨_, _, _, _, hL⟩ | ⟨_, _, hO⟩
        · exact (IsLineWithEnds.isConnected hL).2
        · exact hO.isPreconnected
      obtain ⟨z, hze, hzAB⟩ := preconnected_inter_nonempty_of_closed_cover hpc hA hB
        (fun x _ => hcov ▸ mem_univ x) ⟨a, ha_cl, hu⟩ ⟨b, hb_cl, hbB⟩
      have hzF : z ∈ F := hAB hzAB
      have hzDU : z ∈ D.U := D.closure_subset_U he hze
      have hzGU : z ∈ G.U := G.closure_subset_U (hsub.2 he) hze
      have hzGV : z ∈ G.V := hnorm ⟨hzF, hzGU⟩
      have hzDV : z ∈ D.V := mem_V_of_subdrawing hsub hzDU hzGV
      exact ⟨z, hzDV, hzGV, hzF⟩

/-- If `A` and `B` are closed sets covering `S` with `A ∩ B ⊆ F` for a `G`-normal set `F`, and
`X ⊆ A`, `Y ⊆ B`, then `maxDisjointPaths G X Y ≤ (G.V ∩ F).ncard`. -/
theorem maxDisjointPaths_le_of_closed_cover {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {X Y F A B : Set S}
    (hnorm : G.IsNormal F) (hA : IsClosed A) (hB : IsClosed B)
    (hcov : A ∪ B = univ) (hAB : A ∩ B ⊆ F) (hX : X ⊆ A) (hY : Y ⊆ B) :
    maxDisjointPaths G X Y ≤ (G.V ∩ F).ncard := by
  classical
  have hne : {k : ℕ | HasDisjointPathsBetween G X Y k}.Nonempty :=
    ⟨0, hasDisjointPathsBetween_zero G X Y⟩
  refine csSup_le hne fun k hk => ?_
  obtain ⟨P, s, t, hP, hdisj⟩ := hk
  have hex : ∀ i : Fin k, ∃ z ∈ (P i).V, z ∈ G.V ∩ F := fun i => by
    obtain ⟨hsub, hsX, htY, W, _, _, _⟩ := hP i
    exact walk_meets_of_closed_cover hsub hnorm hA hB hcov hAB W (hX hsX) (hY htY)
  choose z hzPV hzVF using hex
  have hinj : Injective z := fun i j hij => by
    by_contra hne
    exact disjoint_left.mp (hdisj i j hne) (hzPV i) (hij ▸ hzPV j)
  have hcard : (range z).ncard = k := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_fin]
  rw [← hcard]
  exact Set.ncard_le_ncard (range_subset_iff.mpr hzVF) (G.finite_V.inter_of_left F)

private theorem inner_disc_lies_inside_outer_disc
    {S : Type u}
    {F₂ : Set S}
    (Y : Type u)
    [TopologicalSpace Y]
    (j₁ : S → Y)
    (E₁_Y : Set Y)
    (hj₁F₂_in_E₁ : j₁ '' F₂ ⊆ discInt E₁_Y)
    (E₂_Y : Set Y)
    (hE₂_Y_sub : E₂_Y ⊆ E₁_Y)
    (hE₂_Y_disj_bd : Disjoint (E₂_Y \ j₁ '' F₂) (discBd E₁_Y)) :
    E₂_Y ⊆ discInt E₁_Y := by
  intro y hy
  by_cases hyF₂ : y ∈ j₁ '' F₂
  · exact hj₁F₂_in_E₁ hyF₂
  · exact ⟨hE₂_Y_sub hy, disjoint_left.mp hE₂_Y_disj_bd ⟨hy, hyF₂⟩⟩

private theorem first_cap_lies_inside_inner_disc
    {S : Type u}
    [TopologicalSpace S]
    {C₁ : Set S}
    {C₂ : Set S}
    {F₂ : Set S}
    (hbd₂ : Disjoint F₂ (bd S))
    [T2Space S]
    [CompactSpace S]
    (hbdS : bd S = C₁ ∪ C₂)
    (hSurr₂ : SurroundsCuff F₂ C₁)
    (Y : Type u)
    [TopologicalSpace Y]
    (j₁ : S → Y)
    (D₁' : Set Y)
    (hcap₁ : IsCappedCuff C₁ Y j₁ D₁')
    (hY : IsSurface Y)
    [T2Space Y]
    (hj₁ : IsEmbedding j₁)
    (E₂_Y : Set Y)
    (hE₂_Y : IsClosedDisc E₂_Y)
    (hbE₂_Y : discBd E₂_Y = j₁ '' F₂) :
    D₁' ⊆ discInt E₂_Y := by
  have hdis_int : Disjoint (discInt D₁') (discBd E₂_Y) := by
    rw [hbE₂_Y, disjoint_left]
    rintro y hyI ⟨x, hxF₂, rfl⟩
    have hj₁x : j₁ x ∈ range j₁ ∩ D₁' := ⟨mem_range_self x, hyI.1⟩
    rw [hcap₁.inter_eq, ← hcap₁.discBd_eq] at hj₁x
    exact hyI.2 hj₁x
  rcases hE₂_Y.side hY.2.2 hcap₁.isClosedDisc.isPreconnected_discInt hdis_int with hin | hout
  · have hD₁'_sub : D₁' ⊆ E₂_Y := by
      apply hcap₁.isClosedDisc.subset_closure_discInt.trans
      rw [← hE₂_Y.isClosed.closure_eq]
      exact closure_mono (hin.trans (discInt_subset E₂_Y))
    intro y hy
    refine ⟨hD₁'_sub hy, ?_⟩
    rw [hbE₂_Y]
    rintro ⟨x, hxF₂, rfl⟩
    have hj₁x : j₁ x ∈ range j₁ ∩ D₁' := ⟨mem_range_self x, hy⟩
    rw [hcap₁.inter_eq] at hj₁x
    obtain ⟨c, hc, hcj⟩ := hj₁x
    exact disjoint_left.mp hbd₂ hxF₂ (hbdS ▸ hj₁.injective hcj ▸ Or.inl hc)
  · exfalso
    have hE₂_range : E₂_Y ⊆ range j₁ := by
      intro y hy
      rcases hcap₁.union_eq ▸ mem_univ y with hyR | hyD
      · exact hyR
      · by_cases hyb : y ∈ discBd D₁'
        · rw [hcap₁.discBd_eq] at hyb
          exact image_subset_range _ _ hyb
        · exact (disjoint_left.mp hout ⟨hyD, hyb⟩ hy).elim
    have hplan₂ : IsPlanar F₂ := by
      refine ⟨j₁ ⁻¹' E₂_Y, ?_, fun x hx => Surface.discBd_subset E₂_Y
        (hbE₂_Y ▸ mem_image_of_mem j₁ hx)⟩
      have himg : j₁ '' (j₁ ⁻¹' E₂_Y) = E₂_Y := image_preimage_eq_of_subset hE₂_range
      obtain ⟨φD⟩ := hE₂_Y
      exact ⟨(φD.trans (Homeomorph.setCongr himg.symm)).trans
        (hj₁.isEmbedding.homeomorphImage (j₁ ⁻¹' E₂_Y)).symm⟩
    exact hSurr₂.2.2 hplan₂

private theorem outer_disc_avoids_remaining_cuff
    {S : Type u}
    [TopologicalSpace S]
    {C₁ : Set S}
    {C₂ : Set S}
    {F₁ : Set S}
    (hbd₁ : Disjoint F₁ (bd S))
    (hbdS : bd S = C₁ ∪ C₂)
    (Y : Type u)
    [TopologicalSpace Y]
    (j₁ : S → Y)
    (hbdY' : bd Y = j₁ '' C₂)
    (hj₁ : IsEmbedding j₁)
    (hDiscY : IsClosedDisc (univ : Set Y))
    (hdiscBd_univ_Y : discBd (univ : Set Y) = bd Y)
    (E₁_Y : Set Y)
    (hE₁_Y : IsClosedDisc E₁_Y)
    (hbE₁_Y : discBd E₁_Y = j₁ '' F₁)
    (hj₁F₁_oarc : IsOArc (j₁ '' F₁)) :
    Disjoint E₁_Y (bd Y) := by
  obtain ⟨E₁_Y', ⟨-, hE₁_Y', hbE₁_Y', -, hE₁_Y'_disj_bd, -⟩, huniq⟩ :=
    disc_oArc univ (j₁ '' F₁) hDiscY (subset_univ _) hj₁F₁_oarc
  have hE₁_eq : E₁_Y = E₁_Y' := huniq E₁_Y (subset_univ _) hE₁_Y hbE₁_Y
  rw [← hdiscBd_univ_Y, disjoint_left]
  intro y hyE₁ hybd
  by_cases hyF₁ : y ∈ j₁ '' F₁
  · obtain ⟨x, hxF₁, rfl⟩ := hyF₁
    rw [hdiscBd_univ_Y, hbdY'] at hybd
    obtain ⟨c, hc, hcj⟩ := hybd
    exact disjoint_left.mp hbd₁ hxF₁ (hbdS ▸ hj₁.injective hcj ▸ Or.inr hc)
  · exact disjoint_left.mp hE₁_Y'_disj_bd ⟨hE₁_eq ▸ hyE₁, hyF₁⟩ hybd

private theorem cap_discs_and_embedding_cover
    {S : Type u}
    [TopologicalSpace S]
    {C₁ : Set S}
    {C₂ : Set S}
    (Y : Type u)
    [TopologicalSpace Y]
    (j₁ : S → Y)
    (D₁' : Set Y)
    (hcap₁ : IsCappedCuff C₁ Y j₁ D₁')
    (Z : Type u)
    [TopologicalSpace Z]
    (j₂ : Y → Z)
    (D₂ : Set Z)
    (hcap₂ : IsCappedCuff (j₁ '' C₂) Z j₂ D₂) :
    let j : S → Z := j₂ ∘ j₁
    let D₁ : Set Z := j₂ '' D₁'
    range j ∪ D₁ ∪ D₂ = univ := by
  intro j D₁
  refine eq_univ_of_forall fun z => ?_
  rcases (hcap₂.union_eq ▸ mem_univ z : z ∈ range j₂ ∪ D₂) with ⟨y, rfl⟩ | hzD₂
  · rcases (hcap₁.union_eq ▸ mem_univ y : y ∈ range j₁ ∪ D₁') with ⟨c, rfl⟩ | hyD₁'
    · exact Or.inl (Or.inl ⟨c, rfl⟩)
    · exact Or.inl (Or.inr ⟨y, hyD₁', rfl⟩)
  · exact Or.inr hzD₂

private theorem cylinder_range_is_disc_complement
    {S : Type u}
    {C₁ : Set S}
    {C₂ : Set S}
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ D₂ : Set Z)
    [T2Space Z]
    (hCS_Z : IsClosedSurface Z) :
    (discBd D₁ = j '' C₁) →
    (discBd D₂ = j '' C₂) →
    (range j ∪ D₁ ∪ D₂ = univ) →
    (range j ∩ D₁ = j '' C₁) →
    (range j ∩ D₂ = j '' C₂) →
    (∀ (i : Fin 2), IsClosedDisc (![D₁, D₂] i)) →
    (Pairwise fun i k => Disjoint (![D₁, D₂] i) (![D₁, D₂] k)) →
    range j = discComplement ![D₁, D₂] := by
  intro hbD₁_eq hbD₂_eq hunion hinter₁ hinter₂ hP₂ hP₂_disj
  ext z
  rw [mem_discComplement_iff hCS_Z ![D₁, D₂] hP₂ hP₂_disj]
  constructor
  · intro hz i hzi
    fin_cases i
    · have hzC₁ : z ∈ j '' C₁ := hinter₁ ▸ ⟨hz, hzi.1⟩
      exact hzi.2 (hbD₁_eq ▸ hzC₁)
    · have hzC₂ : z ∈ j '' C₂ := hinter₂ ▸ ⟨hz, hzi.1⟩
      exact hzi.2 (hbD₂_eq ▸ hzC₂)
  · intro hnot
    rcases (hunion ▸ mem_univ z : z ∈ range j ∪ D₁ ∪ D₂) with (hzR | hzD₁) | hzD₂
    · exact hzR
    · have hzb : z ∈ discBd D₁ := by
        by_contra hnb
        exact hnot 0 ⟨hzD₁, hnb⟩
      rw [hbD₁_eq] at hzb
      exact image_subset_range _ _ hzb
    · have hzb : z ∈ discBd D₂ := by
        by_contra hnb
        exact hnot 1 ⟨hzD₂, hnb⟩
      rw [hbD₂_eq] at hzb
      exact image_subset_range _ _ hzb

private theorem second_cap_lies_inside_outer_complement
    (Y : Type u)
    (E₁_Y : Set Y)
    (Z : Type u)
    [TopologicalSpace Z]
    (j₂ : Y → Z)
    (D₂ : Set Z) :
    let E₁ : Set Z := j₂ '' E₁_Y
    (Disjoint E₁ D₂) →
    ∀ (E₁' : Set Z),
    (discInt E₁' = (j₂ '' E₁_Y)ᶜ) →
    D₂ ⊆ discInt E₁' := by
  intro E₁ hE₁_disj_D₂ E₁' hE₁'_int
  rw [hE₁'_int]
  exact fun z hzD₂ hzE₁ => disjoint_left.mp hE₁_disj_D₂ hzE₁ hzD₂

private theorem disc_complements_reverse_containment
    (Y : Type u)
    (E₁_Y : Set Y)
    (E₂_Y : Set Y)
    (Z : Type u)
    [TopologicalSpace Z]
    (j₂ : Y → Z) :
    let E₁ : Set Z := j₂ '' E₁_Y
    let E₂ : Set Z := j₂ '' E₂_Y
    (E₂ ⊆ discInt E₁) →
    ∀ (E₁' : Set Z),
    (E₁' = (discInt (j₂ '' E₁_Y))ᶜ) →
    ∀ (E₂' : Set Z),
    (discInt E₂' = (j₂ '' E₂_Y)ᶜ) →
    E₁' ⊆ discInt E₂' := by
  intro E₁ E₂ hE₂_in_E₁ E₁' hE₁'_compl E₂' hE₂'_int
  rw [hE₁'_compl, hE₂'_int]
  exact compl_subset_compl.mpr hE₂_in_E₁

/-- Capping both cuffs `C₁, C₂` of a cylinder `S : Type u` yields a sphere `Z : Type u` and nested
closed discs `D₁ ⊆ discInt E₂`, `E₂ ⊆ discInt E₁`, `Disjoint E₁ D₂` (with complementary closed discs
`E₁' = (discInt E₁)ᶜ` and `E₂' = (discInt E₂)ᶜ` satisfying `D₂ ⊆ discInt E₁'`, `E₁' ⊆ discInt E₂'`,
`Disjoint E₂' D₁`) bounded by `j '' C₁`, `j '' F₂`, `j '' F₁`, and `j '' C₂`. -/
theorem exists_sphere_cap_and_nested_discs {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (he : Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {C₁ C₂ F₁ F₂ : Set S} (hcuffs : cuffs S = {C₁, C₂}) (hne : C₁ ≠ C₂)
    (hOrd : CylinderOArcsInOrder C₁ F₂ F₁ C₂)
    (hInside₁₂ : ∀ x ∈ F₂, IsPointInsideSurroundingOArc C₁ F₁ x)
    (hbd₁ : Disjoint F₁ (bd S)) (hbd₂ : Disjoint F₂ (bd S)) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : Z ≃ₜ SurfaceModel 0 0 0)
      (j : S → Z) (D₁ D₂ E₁ E₂ E₁' E₂' : Set Z),
      IsClosedSurface Z ∧ IsSphere Z ∧ ConnectedSpace Z ∧ IsClosedEmbedding j ∧
      IsClosedDisc D₁ ∧ IsClosedDisc D₂ ∧ Disjoint D₁ D₂ ∧
      discBd D₁ = j '' C₁ ∧ discBd D₂ = j '' C₂ ∧
      range j ∪ D₁ ∪ D₂ = univ ∧ range j ∩ D₁ = j '' C₁ ∧ range j ∩ D₂ = j '' C₂ ∧
      range j = discComplement ![D₁, D₂] ∧
      IsClosedDisc E₁ ∧ discBd E₁ = j '' F₁ ∧
      IsClosedDisc E₂ ∧ discBd E₂ = j '' F₂ ∧
      IsClosedDisc E₁' ∧ discBd E₁' = j '' F₁ ∧ E₁' = (discInt E₁)ᶜ ∧ discInt E₁' = E₁ᶜ ∧
      IsClosedDisc E₂' ∧ discBd E₂' = j '' F₂ ∧ E₂' = (discInt E₂)ᶜ ∧ discInt E₂' = E₂ᶜ ∧
      D₁ ⊆ discInt E₂ ∧ E₂ ⊆ discInt E₁ ∧ Disjoint E₁ D₂ ∧
      D₂ ⊆ discInt E₁' ∧ E₁' ⊆ discInt E₂' ∧ Disjoint E₂' D₁ := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  obtain ⟨e₀⟩ := he
  have : ConnectedSpace S := by
    have := (isSurface_model 0 0 2).2
    exact e₀.symm.surjective.connectedSpace e₀.symm.continuous
  have hC₁ : C₁ ∈ cuffs S := by rw [hcuffs]; simp
  have hC₂ : C₂ ∈ cuffs S := by rw [hcuffs]; simp
  have hdis : Disjoint C₁ C₂ := cuffs_disjoint hC₁ hC₂ hne
  have hbdS : bd S = C₁ ∪ C₂ := by rw [← sUnion_cuffs, hcuffs, sUnion_pair]
  have hO₁ : IsOArc F₁ := hOrd.2.2.2.1
  have hO₂ : IsOArc F₂ := hOrd.2.2.2.2.1
  have hDisj₁₂ : Disjoint F₁ F₂ := hOrd.2.2.2.2.2.1
  have hSurr₂ : SurroundsCuff F₂ C₁ := hOrd.2.2.2.2.2.2.2.2.1
  have hSurr₁ : SurroundsCuff F₁ C₁ := hOrd.2.2.2.2.2.2.2.2.2.1
  -- Step 1: Cap C₁ to obtain a closed disc Y
  obtain ⟨Y, tY, j₁, D₁', hcap₁, hbdY⟩ := exists_cappedCuff hS hC₁
  obtain ⟨-, ⟨e₁⟩⟩ := cappedCuff_homeo_model hS ⟨e₀⟩ hC₁ hcap₁
  have hY : IsSurface Y := hcap₁.isSurface
  have : T2Space Y := hY.2.1
  have : CompactSpace Y := hY.1
  have : ConnectedSpace Y := by
    have := (isSurface_model 0 0 1).2
    exact e₁.symm.surjective.connectedSpace e₁.symm.continuous
  have hbdY' : bd Y = j₁ '' C₂ := by
    rw [hbdY, hbdS, union_sdiff_left, sdiff_eq_left.mpr hdis.symm]
  have hj₁ := hcap₁.isEmbedding
  have hj₁_ce : IsClosedEmbedding j₁ := hj₁.continuous.isClosedEmbedding hj₁.injective
  obtain ⟨eD₀⟩ := nonempty_disc_homeo
  have hDiscY : IsClosedDisc (univ : Set Y) :=
    ⟨eD₀.symm.trans (e₁.symm.trans (Homeomorph.Set.univ Y).symm)⟩
  have hdiscBd_univ_Y : discBd (univ : Set Y) = bd Y := by
    simpa [discBd, Homeomorph.Set.univ] using image_bd_homeomorph (Homeomorph.Set.univ Y)
  -- Step 2: Construct E₁_Y and E₂_Y in Y
  obtain ⟨x₀, hx₀⟩ : F₂.Nonempty := hO₂.elim fun φ => ⟨(φ 1).1, (φ 1).2⟩
  have hx₀_in₁ : IsPointInsideNullOArc (j₁ '' F₁) (j₁ x₀) :=
    (hInside₁₂ x₀ hx₀).2.2.2 Y j₁ D₁' hcap₁
  obtain ⟨_, E₁_Y, hE₁_Y, hbE₁_Y, hj₁x₀_in⟩ := hx₀_in₁
  have hj₁F₁_oarc : IsOArc (j₁ '' F₁) := hbE₁_Y ▸ hE₁_Y.isOArc_discBd
  have hj₁F₂_oarc : IsOArc (j₁ '' F₂) := ⟨(Classical.choice hO₂).trans (hj₁.homeomorphImage F₂)⟩
  have hj₁_disj₁₂ : Disjoint (j₁ '' F₂) (j₁ '' F₁) :=
    (disjoint_image_iff hj₁.injective).mpr hDisj₁₂.symm
  have hj₁F₂_in_E₁ : j₁ '' F₂ ⊆ discInt E₁_Y := by
    rcases hE₁_Y.side hY.2.2 hj₁F₂_oarc.isPreconnected (hbE₁_Y.symm ▸ hj₁_disj₁₂) with hin | hout
    · exact hin
    · exact (disjoint_left.mp hout (mem_image_of_mem j₁ hx₀) hj₁x₀_in.1).elim
  obtain ⟨E₂_Y, ⟨hE₂_Y_sub, hE₂_Y, hbE₂_Y, -, hE₂_Y_disj_bd, -⟩, -⟩ :=
    disc_oArc E₁_Y (j₁ '' F₂) hE₁_Y (hj₁F₂_in_E₁.trans (discInt_subset E₁_Y)) hj₁F₂_oarc
  have hE₂_Y_in_E₁ : E₂_Y ⊆ discInt E₁_Y := by
    exact inner_disc_lies_inside_outer_disc (S := S) (F₂ := F₂) Y j₁ E₁_Y hj₁F₂_in_E₁ E₂_Y
      hE₂_Y_sub hE₂_Y_disj_bd
  -- D₁' ⊆ discInt E₂_Y
  have hD₁'_in_E₂ : D₁' ⊆ discInt E₂_Y := by
    exact first_cap_lies_inside_inner_disc (S := S) (C₁ := C₁) (C₂ := C₂) (F₂ := F₂) hbd₂ hbdS
      hSurr₂ Y j₁ D₁' hcap₁ hY hj₁ E₂_Y hE₂_Y hbE₂_Y
  -- E₁_Y is disjoint from bd Y
  have hE₁_Y_disj_bdY : Disjoint E₁_Y (bd Y) := by
    exact outer_disc_avoids_remaining_cuff (S := S) (C₁ := C₁) (C₂ := C₂) (F₁ := F₁) hbd₁ hbdS Y
      j₁ hbdY' hj₁ hDiscY hdiscBd_univ_Y E₁_Y hE₁_Y hbE₁_Y hj₁F₁_oarc
  -- Step 3: Cap bd Y = j₁ '' C₂ to obtain a sphere Z : Type u
  have hC₂Y : j₁ '' C₂ ∈ cuffs Y := by
    obtain ⟨x, hx, hxe⟩ := hC₂
    have hp : IsPreconnected C₂ := hxe ▸ isPreconnected_connectedComponentIn
    have hxC : x ∈ C₂ := hxe ▸ mem_connectedComponentIn hx
    have hbp : IsPreconnected (bd Y) := hbdY' ▸ hp.image _ hj₁.continuous.continuousOn
    have hy : j₁ x ∈ bd Y := hbdY' ▸ mem_image_of_mem _ hxC
    refine ⟨j₁ x, hy, ?_⟩
    rw [hbp.connectedComponentIn hy, hbdY']
  obtain ⟨Z, tZ, j₂, D₂, hcap₂, hbdZ⟩ := exists_cappedCuff hY hC₂Y
  obtain ⟨-, ⟨e₂⟩⟩ := cappedCuff_homeo_model hY ⟨e₁⟩ hC₂Y hcap₂
  have hZ : IsSurface Z := hcap₂.isSurface
  have : T2Space Z := hZ.2.1
  have : CompactSpace Z := hZ.1
  obtain ⟨s₀⟩ := isSphere_model_zero
  have hSphZ : IsSphere Z := ⟨e₂.trans s₀⟩
  obtain ⟨_, hCS_Z, hconnZ, _⟩ := closedSurface_and_connected_of_isSphere hZ hSphZ
  have : ConnectedSpace Z := hconnZ
  have hj₂ := hcap₂.isEmbedding
  let j : S → Z := j₂ ∘ j₁
  have hjc : Continuous j := hj₂.continuous.comp hj₁.continuous
  have hji : Injective j := hj₂.injective.comp hj₁.injective
  have hj : IsClosedEmbedding j := hjc.isClosedEmbedding hji
  let D₁ : Set Z := j₂ '' D₁'
  obtain ⟨hD₁, hbD₁⟩ := isClosedDisc_image hcap₁.isClosedDisc hj₂.continuous.continuousOn
    hj₂.injective.injOn
  have hD₂ : IsClosedDisc D₂ := hcap₂.isClosedDisc
  have hbD₁_eq : discBd D₁ = j '' C₁ := by
    rw [hbD₁, hcap₁.discBd_eq, image_image]
    rfl
  have hbD₂_eq : discBd D₂ = j '' C₂ := by
    rw [hcap₂.discBd_eq, image_image]
    rfl
  have hm₁ : ∀ {y}, y ∈ D₁' → ∀ c, j₁ c = y → c ∈ C₁ := fun {y} hy c hc => by
    have h3 : y ∈ range j₁ ∩ D₁' := ⟨⟨c, hc⟩, hy⟩
    rw [hcap₁.inter_eq] at h3
    obtain ⟨c', hc', he⟩ := h3
    exact hj₁.injective (he.trans hc.symm) ▸ hc'
  have hm₂ : ∀ {y}, j₂ y ∈ D₂ → ∃ c ∈ C₂, j₁ c = y := fun {y} hy => by
    have h3 : j₂ y ∈ range j₂ ∩ D₂ := ⟨⟨y, rfl⟩, hy⟩
    rw [hcap₂.inter_eq] at h3
    obtain ⟨y', ⟨c, hc, rfl⟩, he⟩ := h3
    exact ⟨c, hc, hj₂.injective he⟩
  have hD₁D₂_disj : Disjoint D₁ D₂ := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ hz
    obtain ⟨c, hc, rfl⟩ := hm₂ hz
    exact disjoint_left.mp hdis (hm₁ hy c rfl) hc
  have hunion : range j ∪ D₁ ∪ D₂ = univ := by
    exact cap_discs_and_embedding_cover (S := S) (C₁ := C₁) (C₂ := C₂) Y j₁ D₁' hcap₁ Z j₂ D₂
      hcap₂
  have hinter₁ : range j ∩ D₁ = j '' C₁ := by
    ext z
    constructor
    · rintro ⟨⟨c, rfl⟩, y, hy, he⟩
      exact ⟨c, hm₁ hy c (hj₂.injective he).symm, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨mem_range_self c, j₁ c, ?_, rfl⟩
      have h3 : j₁ c ∈ range j₁ ∩ D₁' := by
        rw [hcap₁.inter_eq]
        exact ⟨c, hc, rfl⟩
      exact h3.2
  have hinter₂ : range j ∩ D₂ = j '' C₂ := by
    ext z
    constructor
    · rintro ⟨⟨c, rfl⟩, hz⟩
      obtain ⟨c', hc', he'⟩ := hm₂ hz
      exact ⟨c, hj₁.injective he' ▸ hc', rfl⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨mem_range_self c, ?_⟩
      have h3 : j₂ (j₁ c) ∈ range j₂ ∩ D₂ := by
        rw [hcap₂.inter_eq]
        exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact h3.2
  have hP₂ : ∀ i : Fin 2, IsClosedDisc (![D₁, D₂] i) := fun i => by
    fin_cases i
    · exact hD₁
    · exact hD₂
  have hP₂_disj : Pairwise (fun i k : Fin 2 => Disjoint (![D₁, D₂] i) (![D₁, D₂] k)) := fun i k hik
    => by
    fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact hD₁D₂_disj
    · exact hD₁D₂_disj.symm
    · exact (hik rfl).elim
  have hrange_eq : range j = discComplement ![D₁, D₂] := by
    exact cylinder_range_is_disc_complement (S := S) (C₁ := C₁) (C₂ := C₂) Z j D₁ D₂ hCS_Z hbD₁_eq
      hbD₂_eq hunion hinter₁ hinter₂ hP₂ hP₂_disj
  -- Step 4: Push E₁_Y and E₂_Y to Z and take complementary discs E₁', E₂'
  let E₁ : Set Z := j₂ '' E₁_Y
  let E₂ : Set Z := j₂ '' E₂_Y
  obtain ⟨hE₁, hbE₁⟩ := isClosedDisc_image hE₁_Y hj₂.continuous.continuousOn hj₂.injective.injOn
  obtain ⟨hE₂, hbE₂⟩ := isClosedDisc_image hE₂_Y hj₂.continuous.continuousOn hj₂.injective.injOn
  have hbE₁_eq : discBd E₁ = j '' F₁ := by
    rw [hbE₁, hbE₁_Y, image_image]
    rfl
  have hbE₂_eq : discBd E₂ = j '' F₂ := by
    rw [hbE₂, hbE₂_Y, image_image]
    rfl
  have hD₁_in_E₂ : D₁ ⊆ discInt E₂ := by
    rintro _ ⟨y, hyD₁', rfl⟩
    have hy_in := hD₁'_in_E₂ hyD₁'
    refine ⟨⟨y, hy_in.1, rfl⟩, ?_⟩
    rw [hbE₂]
    rintro ⟨y', hy', heq⟩
    exact hy_in.2 (hj₂.injective heq ▸ hy')
  have hE₂_in_E₁ : E₂ ⊆ discInt E₁ := by
    rintro _ ⟨y, hyE₂, rfl⟩
    have hy_in := hE₂_Y_in_E₁ hyE₂
    refine ⟨⟨y, hy_in.1, rfl⟩, ?_⟩
    rw [hbE₁]
    rintro ⟨y', hy', heq⟩
    exact hy_in.2 (hj₂.injective heq ▸ hy')
  have hE₁_disj_D₂ : Disjoint E₁ D₂ := by
    rw [disjoint_left]
    rintro _ ⟨y, hyE₁, rfl⟩ hzD₂
    have hj₂y : j₂ y ∈ range j₂ ∩ D₂ := ⟨mem_range_self y, hzD₂⟩
    rw [hcap₂.inter_eq, ← hbdY'] at hj₂y
    obtain ⟨y', hy'bd, heq⟩ := hj₂y
    exact disjoint_left.mp hE₁_Y_disj_bdY hyE₁ (hj₂.injective heq ▸ hy'bd)
  obtain ⟨E₁', hE₁', hbE₁'_eq, hE₁'_compl, hE₁'_int⟩ := exists_compl_disc_in_sphere hSphZ hE₁
  rw [hbE₁_eq] at hbE₁'_eq
  obtain ⟨E₂', hE₂', hbE₂'_eq, hE₂'_compl, hE₂'_int⟩ := exists_compl_disc_in_sphere hSphZ hE₂
  rw [hbE₂_eq] at hbE₂'_eq
  have hD₂_in_E₁' : D₂ ⊆ discInt E₁' := by
    exact second_cap_lies_inside_outer_complement Y E₁_Y Z j₂ D₂ hE₁_disj_D₂ E₁' hE₁'_int
  have hE₁'_in_E₂' : E₁' ⊆ discInt E₂' := by
    exact disc_complements_reverse_containment Y E₁_Y E₂_Y Z j₂ hE₂_in_E₁ E₁' hE₁'_compl E₂'
      hE₂'_int
  have hE₂'_disj_D₁ : Disjoint E₂' D₁ := by
    rw [hE₂'_compl, disjoint_compl_left_iff_subset]
    exact hD₁_in_E₂
  exact ⟨Z, tZ, e₂, j, D₁, D₂, E₁, E₂, E₁', E₂', hCS_Z, hSphZ, hconnZ, hj, hD₁, hD₂, hD₁D₂_disj,
    hbD₁_eq, hbD₂_eq, hunion, hinter₁, hinter₂, hrange_eq, hE₁, hbE₁_eq, hE₂, hbE₂_eq,
    hE₁', hbE₁'_eq, hE₁'_compl, hE₁'_int, hE₂', hbE₂'_eq, hE₂'_compl, hE₂'_int,
    hD₁_in_E₂, hE₂_in_E₁, hE₁_disj_D₂, hD₂_in_E₁', hE₁'_in_E₂', hE₂'_disj_D₁⟩

/-- Every `[0, 1]`-arc with ends (`IsLineWithEnds`) is a `[0, 1]`-arc (`IsLine`). -/
theorem IsLineWithEnds.isLine {S : Type*} [TopologicalSpace S] {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) : IsLine L := by
  obtain ⟨f, _, _⟩ := hL
  exact ⟨f⟩

/-- Every `[0, 1]`-arc (`IsLine`) in a space is path-connected. -/
theorem IsLine.isPathConnected {S : Type*} [TopologicalSpace S] {L : Set S} (hL : IsLine L) :
    IsPathConnected L := by
  obtain ⟨f⟩ := hL
  have hI : IsPathConnected (univ : Set unitInterval) := isPathConnected_univ
  have himg : (Subtype.val ∘ f) '' univ = L := by
    ext x
    constructor
    · rintro ⟨t, _, rfl⟩
      exact (f t).2
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, mem_univ _, congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)⟩
  rw [← himg]
  exact hI.image (continuous_subtype_val.comp f.continuous)

/-- Every closed disc in a topological space is preconnected. -/
theorem _root_.GraphMinor.Surface.IsClosedDisc.isPreconnected {X : Type*} [TopologicalSpace X] {D :
  Set X}
    (hD : IsClosedDisc D) : IsPreconnected D :=
  IsPreconnected.subset_closure hD.isPreconnected_discInt (discInt_subset D)
    hD.subset_closure_discInt

private theorem minimal_line_meets_first_boundary_at_end
    {S : Type u}
    [TopologicalSpace S]
    {F₁ : Set S}
    {F₂ : Set S}
    (hDisj : Disjoint F₁ F₂)
    (g₁ : unitInterval → S) :
    ∀ (a : ↑unitInterval),
    ∀ (b : ↑unitInterval),
    (g₁ a ∈ F₂) →
    (g₁ b ∈ F₁) →
    let I : Set S := g₁ '' Icc a b
    let u : S := g₁ a
    let v : S := g₁ b
    (Disjoint (I \ {u, v}) (F₁ ∪ F₂)) →
    ∀ (f : ↑unitInterval ≃ₜ ↑I),
    (↑(f 0) = u) →
    (↑(f 1) = v) →
    let g : ↑unitInterval → S := fun t => ↑(f t)
    (Injective g) →
    ∀ (t : ↑unitInterval), g t ∈ F₁ ↔ t = 1 := by
  intro a b haF₂ hbF₁ I u v hI_disj f hf0 hf1 g hg_inj t
  constructor
  · intro htF₁
    by_contra ht1
    have ht0 : t ≠ 0 := by
      intro ht0
      have hgu : g t = u := ht0 ▸ hf0
      exact disjoint_left.mp hDisj htF₁ (hgu ▸ haF₂)
    have hgt_uv : g t ∉ ({u, v} : Set S) := by
      rintro (hgu | hgv)
      · exact ht0 (hg_inj (hgu.trans hf0.symm))
      · exact ht1 (hg_inj (hgv.trans hf1.symm))
    exact disjoint_left.mp hI_disj ⟨(f t).2, hgt_uv⟩ (Or.inl htF₁)
  · rintro rfl
    change (f 1).1 ∈ F₁
    rwa [hf1]

private theorem minimal_line_meets_second_boundary_at_end
    {S : Type u}
    [TopologicalSpace S]
    {F₁ : Set S}
    {F₂ : Set S}
    (hDisj : Disjoint F₁ F₂)
    (g₁ : unitInterval → S) :
    ∀ (a : ↑unitInterval),
    ∀ (b : ↑unitInterval),
    (g₁ a ∈ F₂) →
    (g₁ b ∈ F₁) →
    let I : Set S := g₁ '' Icc a b
    let u : S := g₁ a
    let v : S := g₁ b
    (Disjoint (I \ {u, v}) (F₁ ∪ F₂)) →
    ∀ (f : ↑unitInterval ≃ₜ ↑I),
    (↑(f 0) = u) →
    (↑(f 1) = v) →
    let g : ↑unitInterval → S := fun t => ↑(f t)
    (Injective g) →
    ∀ (t : ↑unitInterval), g t ∈ F₂ ↔ t = 0 := by
  intro a b haF₂ hbF₁ I u v hI_disj f hf0 hf1 g hg_inj t
  constructor
  · intro htF₂
    by_contra ht0
    have ht1 : t ≠ 1 := by
      intro ht1
      have hgv : g t = v := ht1 ▸ hf1
      exact disjoint_left.mp hDisj (hgv ▸ hbF₁) htF₂
    have hgt_uv : g t ∉ ({u, v} : Set S) := by
      rintro (hgu | hgv)
      · exact ht0 (hg_inj (hgu.trans hf0.symm))
      · exact ht1 (hg_inj (hgv.trans hf1.symm))
    exact disjoint_left.mp hI_disj ⟨(f t).2, hgt_uv⟩ (Or.inr htF₂)
  · rintro rfl
    change (f 0).1 ∈ F₂
    rwa [hf0]

private theorem parametrization_maps_vertex_times_to_vertices
    {S : Type u}
    [TopologicalSpace S]
    (G : Drawing S)
    (I : Set S)
    (g : ↑unitInterval → S)
    (hg_range : range g = I) :
    let T_V : Set ↑unitInterval := g ⁻¹' G.V
    g '' T_V = G.V ∩ I := by
  intro T_V
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht, hg_range ▸ mem_range_self t⟩
  · rintro ⟨hxV, hxI⟩
    rw [← hg_range] at hxI
    obtain ⟨t, rfl⟩ := hxI
    exact ⟨t, hxV, rfl⟩

private theorem vertex_time_before_split_iff_index_lt {m r : ℕ} (hr : 1 ≤ r)
    (hm : r < m) (emb : Fin m ↪o unitInterval) (t₀ : unitInterval)
    (ha : emb ⟨r - 1, by omega⟩ < t₀) (hb : t₀ < emb ⟨r, hm⟩) :
    ∀ i : Fin m, emb i ≤ t₀ ↔ i.val < r := by
  intro i
  constructor
  · intro hle
    by_contra hge
    have hi : (⟨r, hm⟩ : Fin m) ≤ i := by
      change r ≤ i.val
      omega
    exact (not_le_of_gt hb) ((emb.monotone hi).trans hle)
  · intro hlt
    have hi : i ≤ (⟨r - 1, by omega⟩ : Fin m) := by
      change i.val ≤ r - 1
      omega
    exact (emb.monotone hi).trans ha.le

private theorem split_time_is_between_vertices {m r : ℕ} (hr : 1 ≤ r)
    (hm : r < m) (emb : Fin m ↪o unitInterval) (t₀ : unitInterval)
    (ha : emb ⟨r - 1, by omega⟩ < t₀) (hb : t₀ < emb ⟨r, hm⟩) :
    t₀ ∉ range emb := by
  rintro ⟨i, hi⟩
  by_cases hir : i.val < r
  · have hle : i ≤ (⟨r - 1, by omega⟩ : Fin m) := by
      change i.val ≤ r - 1
      omega
    exact (lt_of_le_of_lt (emb.monotone hle) ha).ne hi
  · have hle : (⟨r, hm⟩ : Fin m) ≤ i := by
      change r ≤ i.val
      omega
    exact (lt_of_lt_of_le hb (emb.monotone hle)).ne' hi

private theorem line_halves_cover_line
    {S : Type u}
    (I : Set S)
    (g : ↑unitInterval → S)
    (hg_range : range g = I)
    (t₀ : ↑unitInterval) :
    let barI₁ : Set S := g '' Icc 0 t₀
    let barI₂ : Set S := g '' Icc t₀ 1
    barI₁ ∪ barI₂ = I := by
  intro barI₁ barI₂
  rw [← hg_range, ← image_union]
  ext x
  constructor
  · rintro ⟨t, _, rfl⟩
    exact mem_range_self t
  · rintro ⟨t, rfl⟩
    rcases le_total t t₀ with hle | hge
    · exact ⟨t, Or.inl ⟨t.2.1, hle⟩, rfl⟩
    · exact ⟨t, Or.inr ⟨hge, t.2.2⟩, rfl⟩

private theorem upper_vertex_times_biject_later_indices {m r : ℕ} (hrm : r ≤ m)
    (T_V : Set unitInterval) (emb : Fin m ↪o unitInterval)
    (hemb_mem : ∀ i, emb i ∈ T_V) (hemb_range : range emb = T_V)
    (t₀ : unitInterval) (hemb_le_t₀_iff : ∀ i : Fin m, emb i ≤ t₀ ↔ i.val < r)
    (ht₀_notMem_TV : t₀ ∉ T_V) (φ₂ : Fin (m - r) → ↥(T_V ∩ Ici t₀))
    (hφ₂ : ∀ j, (φ₂ j).val = emb ⟨r + j.val, by omega⟩) : Bijective φ₂ := by
  refine ⟨fun j₁ j₂ h => ?_, fun ⟨t, htV, ht_ge⟩ => ?_⟩
  · have hval : (φ₂ j₁).val = (φ₂ j₂).val := congrArg Subtype.val h
    rw [hφ₂, hφ₂] at hval
    have heq : r + j₁.val = r + j₂.val := Fin.mk.inj (emb.injective hval)
    exact Fin.ext (by omega)
  · rw [← hemb_range] at htV
    obtain ⟨i, rfl⟩ := htV
    have hir : ¬ (i.val < r) := fun hlt => by
      have hle : emb i ≤ t₀ := (hemb_le_t₀_iff i).mpr hlt
      exact ht₀_notMem_TV (le_antisymm hle ht_ge ▸ hemb_mem i)
    have hidx : (⟨r + (i.val - r), by omega⟩ : Fin m) = i := Fin.ext (by dsimp; omega)
    refine ⟨⟨i.val - r, by omega⟩, Subtype.ext ?_⟩
    rw [hφ₂]
    exact congrArg emb hidx

/-- In the proof of (9.3) (page 244):
"Choose a $G$-normal $[0, 1]$-arc $I$ with $I \cap F_1 \ne \emptyset \ne I \cap F_2$ and with
$|V(G) \cap I|$ minimum. Choose $z \in I - U(G)$ such that the two components of $I - \{z\}$ both
contain at least $r$ vertices.. Let $I_1, I_2$ be the two components of $I - \{z\}$, numbered so
that $I_j$ meets $F_{3-j} \ (j = 1, 2)$." -/
theorem exists_minimal_line_and_split {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {F₁ F₂ : Set S} (hO₁ : IsOArc F₁) (hO₂ : IsOArc F₂) (hDisj : Disjoint F₁ F₂)
    {r : ℕ} (hr : 1 ≤ r)
    (hex : ∃ F : Set S, G.IsNormal F ∧ IsLine F ∧ (F ∩ F₁).Nonempty ∧ (F ∩ F₂).Nonempty)
    (hLine : ∀ F : Set S, G.IsNormal F → IsLine F → (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      2 * r ≤ (G.V ∩ F).ncard) :
    ∃ (I barI₁ barI₂ : Set S) (u v z : S) (m : ℕ),
      IsLineWithEnds I u v ∧ u ∈ F₂ ∧ v ∈ F₁ ∧
      Disjoint (I \ {u, v}) (F₁ ∪ F₂) ∧
      G.IsNormal I ∧ G.IsNormal barI₁ ∧ G.IsNormal barI₂ ∧
      IsLineWithEnds barI₁ u z ∧ IsLineWithEnds barI₂ z v ∧
      barI₁ ⊆ I ∧ barI₂ ⊆ I ∧ barI₁ ∪ barI₂ = I ∧
      z ∈ I \ (G.U ∪ {u, v}) ∧
      u ∈ barI₁ ∩ F₂ ∧ Disjoint barI₁ F₁ ∧
      v ∈ barI₂ ∩ F₁ ∧ Disjoint barI₂ F₂ ∧
      2 * r ≤ m ∧
      (G.V ∩ I).ncard = m ∧ (G.V ∩ barI₁).ncard = r ∧ (G.V ∩ barI₂).ncard = m - r ∧
      (∀ F : Set S, G.IsNormal F → IsLine F → (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
        m ≤ (G.V ∩ F).ncard) := by
  classical
  let S_lines : Set ℕ :=
    {n : ℕ | ∃ F : Set S, G.IsNormal F ∧ IsLine F ∧ (F ∩ F₁).Nonempty ∧ (F ∩ F₂).Nonempty ∧
      (G.V ∩ F).ncard = n}
  have hS_ne : S_lines.Nonempty := by
    obtain ⟨F, hFn, hFl, hF1, hF2⟩ := hex
    exact ⟨(G.V ∩ F).ncard, F, hFn, hFl, hF1, hF2, rfl⟩
  let m : ℕ := sInf S_lines
  obtain ⟨I₀, hI₀_norm, hI₀_line, ⟨v₀, hv₀I₀, hv₀F₁⟩, ⟨u₀, hu₀I₀, hu₀F₂⟩, hm_eq⟩ :=
    Nat.sInf_mem hS_ne
  have hmin : ∀ F : Set S, G.IsNormal F → IsLine F → (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      m ≤ (G.V ∩ F).ncard := fun F hFn hFl h1 h2 =>
    Nat.sInf_le ⟨F, hFn, hFl, h1, h2, rfl⟩
  have h2r : 2 * r ≤ m := by
    change 2 * r ≤ sInf S_lines
    rw [← hm_eq]
    exact hLine I₀ hI₀_norm hI₀_line ⟨v₀, hv₀I₀, hv₀F₁⟩ ⟨u₀, hu₀I₀, hu₀F₂⟩
  have hu₀v₀_ne : u₀ ≠ v₀ := fun heq => disjoint_left.mp hDisj hv₀F₁ (heq ▸ hu₀F₂)
  have hjI₀ : JoinedIn I₀ u₀ v₀ := (IsLine.isPathConnected hI₀_line).joinedIn u₀ hu₀I₀ v₀ hv₀I₀
  obtain ⟨I₁, hI₁_sub, f₁, hf₁0, hf₁1⟩ :=
    (joinedIn_iff_eq_or_exists_isLineWithEnds hu₀I₀ hv₀I₀).mp hjI₀ |>.resolve_left hu₀v₀_ne
  let g₁ : unitInterval → S := fun t => (f₁ t).1
  have hg₁_cont : Continuous g₁ := continuous_subtype_val.comp f₁.continuous
  have hg₁_inj : Injective g₁ := fun a b h => f₁.injective (Subtype.ext h)
  have hF₂_cl : IsClosed (g₁ ⁻¹' F₂) := (IsOArc.isSolid hO₂).2.preimage hg₁_cont
  have hF₁_cl : IsClosed (g₁ ⁻¹' F₁) := (IsOArc.isSolid hO₁).2.preimage hg₁_cont
  have h0F₂ : g₁ 0 ∈ F₂ := by
    change (f₁ 0).1 ∈ F₂
    rwa [hf₁0]
  have h1F₁ : g₁ 1 ∈ F₁ := by
    change (f₁ 1).1 ∈ F₁
    rwa [hf₁1]
  obtain ⟨a, b, hab, haF₂, hbF₁, hgap⟩ :=
    exists_parameter_gap hF₂_cl hF₁_cl hDisj.symm h0F₂ h1F₁
  let I : Set S := g₁ '' Icc a b
  let u : S := g₁ a
  let v : S := g₁ b
  have hI_ends : IsLineWithEnds I u v := isLine_piece hg₁_cont hg₁_inj hab
  have hI_sub : I ⊆ I₀ := (image_subset_range g₁ _).trans (by
    rintro _ ⟨t, rfl⟩
    exact hI₁_sub (f₁ t).2)
  have hI_norm : G.IsNormal I := fun x hx => hI₀_norm ⟨hI_sub hx.1, hx.2⟩
  have hI_line : IsLine I := IsLineWithEnds.isLine hI_ends
  have huI : u ∈ I := ⟨a, left_mem_Icc.mpr hab.le, rfl⟩
  have hvI : v ∈ I := ⟨b, right_mem_Icc.mpr hab.le, rfl⟩
  have hI_disj : Disjoint (I \ {u, v}) (F₁ ∪ F₂) := by
    rw [disjoint_left]
    rintro _ ⟨⟨t, ht, rfl⟩, hnot_uv⟩ htF
    have hta : a < t := lt_of_le_of_ne ht.1 (fun heq => hnot_uv (Or.inl (congrArg g₁ heq.symm)))
    have htb : t < b := lt_of_le_of_ne ht.2 (fun heq => hnot_uv (Or.inr (congrArg g₁ heq)))
    exact hgap t ⟨hta, htb⟩ (union_comm F₁ F₂ ▸ htF)
  have hI_ncard : (G.V ∩ I).ncard = m := by
    apply le_antisymm
    · change (G.V ∩ I).ncard ≤ sInf S_lines
      rw [← hm_eq]
      exact Set.ncard_le_ncard (inter_subset_inter_right G.V hI_sub) (G.finite_V.inter_of_left I₀)
    · exact hmin I hI_norm hI_line ⟨v, hvI, hbF₁⟩ ⟨u, huI, haF₂⟩
  -- Parameterize I by f : unitInterval ≃ₜ I
  obtain ⟨f, hf0, hf1⟩ := id hI_ends
  let g : unitInterval → S := fun t => (f t).1
  have hg_cont : Continuous g := continuous_subtype_val.comp f.continuous
  have hg_inj : Injective g := fun s t h => f.injective (Subtype.ext h)
  have hg_range : range g = I := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (f t).2
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)⟩
  have hg_F₁_iff : ∀ t : unitInterval, g t ∈ F₁ ↔ t = 1 := by
    exact minimal_line_meets_first_boundary_at_end (S := S) (F₁ := F₁) (F₂ := F₂) hDisj g₁ a b
      haF₂ hbF₁    hI_disj f hf0 hf1  hg_inj
  have hg_F₂_iff : ∀ t : unitInterval, g t ∈ F₂ ↔ t = 0 := by
    exact minimal_line_meets_second_boundary_at_end (S := S) (F₁ := F₁) (F₂ := F₂) hDisj g₁ a b
      haF₂ hbF₁    hI_disj f hf0 hf1  hg_inj
  -- Order the m vertices of G on I along unitInterval
  let T_V : Set unitInterval := g ⁻¹' G.V
  have hTV_fin : T_V.Finite := G.finite_V.preimage hg_inj.injOn
  have hTV_img : g '' T_V = G.V ∩ I := by
    exact parametrization_maps_vertex_times_to_vertices (S := S) G I g hg_range
  have hTV_ncard : T_V.ncard = m := by
    rw [← ncard_image_of_injective T_V hg_inj, hTV_img, hI_ncard]
  let L : Finset unitInterval := hTV_fin.toFinset
  have hL_card : L.card = m := by
    rw [← hTV_ncard, Set.ncard_eq_toFinset_card T_V hTV_fin]
  let emb : Fin m ↪o unitInterval := L.orderEmbOfFin hL_card
  have hemb_mem : ∀ i : Fin m, emb i ∈ T_V := fun i =>
    (hTV_fin.mem_toFinset).mp (L.orderEmbOfFin_mem hL_card i)
  have hemb_range : range emb = T_V := by
    rw [Finset.range_orderEmbOfFin L hL_card, Finite.coe_toFinset]
  let i_a : Fin m := ⟨r - 1, by omega⟩
  let i_b : Fin m := ⟨r, by omega⟩
  have hia_lt_ib : i_a < i_b := by
    change r - 1 < r
    omega
  let t_a : unitInterval := emb i_a
  let t_b : unitInterval := emb i_b
  have hta_lt_tb : (t_a : ℝ) < (t_b : ℝ) := emb.strictMono hia_lt_ib
  let t₀ : unitInterval :=
    ⟨((t_a : ℝ) + (t_b : ℝ)) / 2, ⟨by linarith [t_a.2.1, t_b.2.1], by linarith [t_a.2.2, t_b.2.2]⟩⟩
  have hta_lt_t₀ : t_a < t₀ := by
    change (t_a : ℝ) < ((t_a : ℝ) + (t_b : ℝ)) / 2
    linarith
  have ht₀_lt_tb : t₀ < t_b := by
    change ((t_a : ℝ) + (t_b : ℝ)) / 2 < (t_b : ℝ)
    linarith
  have ht₀_pos : (0 : unitInterval) < t₀ := lt_of_le_of_lt t_a.2.1 hta_lt_t₀
  have ht₀_lt_one : t₀ < (1 : unitInterval) := lt_of_lt_of_le ht₀_lt_tb t_b.2.2
  have hemb_le_t₀_iff : ∀ i : Fin m, emb i ≤ t₀ ↔ i.1 < r := by
    exact vertex_time_before_split_iff_index_lt hr (by omega) emb t₀ hta_lt_t₀ ht₀_lt_tb
  have ht₀_notMem_TV : t₀ ∉ T_V := by
    rw [← hemb_range]
    exact split_time_is_between_vertices hr (by omega) emb t₀ hta_lt_t₀ ht₀_lt_tb
  let z : S := g t₀
  let barI₁ : Set S := g '' Icc 0 t₀
  let barI₂ : Set S := g '' Icc t₀ 1
  have hg0 : g 0 = u := hf0
  have hg1 : g 1 = v := hf1
  have hbarI₁_ends : IsLineWithEnds barI₁ u z := by
    have h := isLine_piece hg_cont hg_inj ht₀_pos
    rwa [hg0] at h
  have hbarI₂_ends : IsLineWithEnds barI₂ z v := by
    have h := isLine_piece hg_cont hg_inj ht₀_lt_one
    rwa [hg1] at h
  have hbarI₁_sub : barI₁ ⊆ I := by
    rw [← hg_range]
    exact image_subset_range g _
  have hbarI₂_sub : barI₂ ⊆ I := by
    rw [← hg_range]
    exact image_subset_range g _
  have hbar_union : barI₁ ∪ barI₂ = I := by
    exact line_halves_cover_line (S := S) I g hg_range t₀
  have hz_mem : z ∈ I \ (G.U ∪ {u, v}) := by
    refine ⟨(f t₀).2, ?_⟩
    rintro (hzU | hzu | hzv)
    · exact ht₀_notMem_TV (hI_norm ⟨(f t₀).2, hzU⟩)
    · exact ht₀_pos.ne' (hg_inj (hzu.trans hf0.symm))
    · exact ht₀_lt_one.ne (hg_inj (hzv.trans hf1.symm))
  have hbarI₁_disj_F₁ : Disjoint barI₁ F₁ := by
    rw [disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ htF₁
    rw [hg_F₁_iff] at htF₁
    exact ht₀_lt_one.not_ge (htF₁ ▸ ht.2)
  have hbarI₂_disj_F₂ : Disjoint barI₂ F₂ := by
    rw [disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ htF₂
    rw [hg_F₂_iff] at htF₂
    exact ht₀_pos.not_ge (htF₂ ▸ ht.1)
  -- Count vertices in barI₁ and barI₂
  have hbarI₁_V_eq : G.V ∩ barI₁ = g '' (T_V ∩ Iic t₀) := by
    ext x
    constructor
    · rintro ⟨hxV, t, ht, rfl⟩
      exact ⟨t, ⟨hxV, ht.2⟩, rfl⟩
    · rintro ⟨t, ⟨htV, ht⟩, rfl⟩
      exact ⟨htV, t, ⟨t.2.1, ht⟩, rfl⟩
  have hbarI₂_V_eq : G.V ∩ barI₂ = g '' (T_V ∩ Ici t₀) := by
    ext x
    constructor
    · rintro ⟨hxV, t, ht, rfl⟩
      exact ⟨t, ⟨hxV, ht.1⟩, rfl⟩
    · rintro ⟨t, ⟨htV, ht⟩, rfl⟩
      exact ⟨htV, t, ⟨ht, t.2.2⟩, rfl⟩
  let φ₁ : Fin r → ↥(T_V ∩ Iic t₀) := fun j =>
    ⟨emb ⟨j.1, by omega⟩, hemb_mem ⟨j.1, by omega⟩, (hemb_le_t₀_iff ⟨j.1, by omega⟩).mpr j.2⟩
  have hφ₁_bij : Bijective φ₁ := by
    refine ⟨fun j₁ j₂ h => ?_, fun ⟨t, htV, ht_le⟩ => ?_⟩
    · have hval : (φ₁ j₁).1 = (φ₁ j₂).1 := congrArg Subtype.val h
      exact Fin.ext (Fin.mk.inj (emb.injective hval))
    · rw [← hemb_range] at htV
      obtain ⟨i, rfl⟩ := htV
      have hir : i.1 < r := (hemb_le_t₀_iff i).mp ht_le
      exact ⟨⟨i.1, hir⟩, rfl⟩
  have hbarI₁_ncard : (G.V ∩ barI₁).ncard = r := by
    rw [hbarI₁_V_eq, ncard_image_of_injective _ hg_inj, ← Nat.card_coe_set_eq,
      ← Nat.card_congr (Equiv.ofBijective φ₁ hφ₁_bij), Nat.card_fin]
  let φ₂ : Fin (m - r) → ↥(T_V ∩ Ici t₀) := fun j =>
    ⟨emb ⟨r + j.1, by omega⟩, hemb_mem ⟨r + j.1, by omega⟩, by
      have hnot : ¬ (emb ⟨r + j.1, by omega⟩ ≤ t₀) := by
        rw [hemb_le_t₀_iff]
        change ¬ (r + j.1 < r)
        omega
      exact le_of_not_ge hnot⟩
  have hφ₂_bij : Bijective φ₂ := by
    exact upper_vertex_times_biject_later_indices (by omega) T_V emb hemb_mem hemb_range t₀
      hemb_le_t₀_iff ht₀_notMem_TV φ₂ (fun _ => rfl)
  have hbarI₂_ncard : (G.V ∩ barI₂).ncard = m - r := by
    rw [hbarI₂_V_eq, ncard_image_of_injective _ hg_inj, ← Nat.card_coe_set_eq,
      ← Nat.card_congr (Equiv.ofBijective φ₂ hφ₂_bij), Nat.card_fin]
  refine ⟨I, barI₁, barI₂, u, v, z, m, hI_ends, haF₂, hbF₁, hI_disj,
    hI_norm, fun x hx => hI_norm ⟨hbarI₁_sub hx.1, hx.2⟩, fun x hx => hI_norm ⟨hbarI₂_sub hx.1,
      hx.2⟩,
    hbarI₁_ends, hbarI₂_ends, hbarI₁_sub, hbarI₂_sub, hbar_union, hz_mem,
    ⟨hbarI₁_ends.left_mem, haF₂⟩, hbarI₁_disj_F₁,
    ⟨hbarI₂_ends.right_mem, hbF₁⟩, hbarI₂_disj_F₂,
    h2r, hI_ncard, hbarI₁_ncard, hbarI₂_ncard, hmin⟩

/-- **Graph Minors VII, (9.3), Observation** (page 244):
"It follows from the choice of $I$ that $|V(G) \cap R| \ge r$ for every $G$-normal $[0, 1]$-arc $R$
which for some $j$ ($j = 1$ or $2$) meets both $F_j$ and $I_j$." -/
theorem lemma_9_3_obs {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {F₁ F₂ barI₁ barI₂ : Set S} {u v z : S} {r m : ℕ}
    (hDisj : Disjoint F₁ F₂)
    (hbarI₁_norm : G.IsNormal barI₁) (hbarI₂_norm : G.IsNormal barI₂)
    (hbarI₁_ends : IsLineWithEnds barI₁ u z) (hbarI₂_ends : IsLineWithEnds barI₂ z v)
    (hu : u ∈ barI₁ ∩ F₂) (hv : v ∈ barI₂ ∩ F₁)
    (h2r : 2 * r ≤ m)
    (hbarI₁_ncard : (G.V ∩ barI₁).ncard = r) (hbarI₂_ncard : (G.V ∩ barI₂).ncard = m - r)
    (hmin : ∀ F : Set S, G.IsNormal F → IsLine F → (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      m ≤ (G.V ∩ F).ncard)
    {R : Set S} (hR_norm : G.IsNormal R) (hR_line : IsLine R)
    (hmeets : ((R ∩ F₁).Nonempty ∧ (R ∩ barI₁).Nonempty) ∨
      ((R ∩ F₂).Nonempty ∧ (R ∩ barI₂).Nonempty)) :
    r ≤ (G.V ∩ R).ncard := by
  have hR_pc : IsPathConnected R := IsLine.isPathConnected hR_line
  rcases hmeets with ⟨⟨a, haR, haF₁⟩, hR_barI₁⟩ | ⟨⟨a, haR, haF₂⟩, hR_barI₂⟩
  · have hbarI₁_pc : IsPathConnected barI₁ := IsLine.isPathConnected (IsLineWithEnds.isLine
      hbarI₁_ends)
    have hunion_pc : IsPathConnected (R ∪ barI₁) := hR_pc.union hbarI₁_pc hR_barI₁
    have hau_ne : a ≠ u := fun heq => disjoint_left.mp hDisj haF₁ (heq ▸ hu.2)
    have hj : JoinedIn (R ∪ barI₁) a u := hunion_pc.joinedIn a (Or.inl haR) u (Or.inr hu.1)
    have hL_ex := ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := R ∪ barI₁) (Or.inl haR)
      (Or.inr hu.1)).mp hj).resolve_left hau_ne
    obtain ⟨L, hL_sub, hL_ends⟩ := hL_ex
    have hL_norm : G.IsNormal L := fun x hx => by
      rcases hL_sub hx.1 with hxR | hxI₁
      · exact hR_norm ⟨hxR, hx.2⟩
      · exact hbarI₁_norm ⟨hxI₁, hx.2⟩
    have hm_le : m ≤ (G.V ∩ L).ncard :=
      hmin L hL_norm (IsLineWithEnds.isLine hL_ends) ⟨a, hL_ends.left_mem, haF₁⟩ ⟨u,
        hL_ends.right_mem, hu.2⟩
    have hsub_V : G.V ∩ L ⊆ (G.V ∩ R) ∪ (G.V ∩ barI₁) := fun x hx => by
      rcases hL_sub hx.2 with hxR | hxI₁
      · exact Or.inl ⟨hx.1, hxR⟩
      · exact Or.inr ⟨hx.1, hxI₁⟩
    have hle_sum : (G.V ∩ L).ncard ≤ (G.V ∩ R).ncard + (G.V ∩ barI₁).ncard :=
      (Set.ncard_le_ncard hsub_V ((G.finite_V.inter_of_left R).union (G.finite_V.inter_of_left
        barI₁))).trans
        (Set.ncard_union_le _ _)
    omega
  · have hbarI₂_pc : IsPathConnected barI₂ := IsLine.isPathConnected (IsLineWithEnds.isLine
      hbarI₂_ends)
    have hunion_pc : IsPathConnected (R ∪ barI₂) := hR_pc.union hbarI₂_pc hR_barI₂
    have hav_ne : a ≠ v := fun heq => disjoint_left.mp hDisj (heq ▸ hv.2) haF₂
    have hj : JoinedIn (R ∪ barI₂) a v := hunion_pc.joinedIn a (Or.inl haR) v (Or.inr hv.1)
    have hL_ex := ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := R ∪ barI₂) (Or.inl haR)
      (Or.inr hv.1)).mp hj).resolve_left hav_ne
    obtain ⟨L, hL_sub, hL_ends⟩ := hL_ex
    have hL_norm : G.IsNormal L := fun x hx => by
      rcases hL_sub hx.1 with hxR | hxI₂
      · exact hR_norm ⟨hxR, hx.2⟩
      · exact hbarI₂_norm ⟨hxI₂, hx.2⟩
    have hm_le : m ≤ (G.V ∩ L).ncard :=
      hmin L hL_norm (IsLineWithEnds.isLine hL_ends) ⟨v, hL_ends.right_mem, hv.2⟩ ⟨a,
        hL_ends.left_mem, haF₂⟩
    have hsub_V : G.V ∩ L ⊆ (G.V ∩ R) ∪ (G.V ∩ barI₂) := fun x hx => by
      rcases hL_sub hx.2 with hxR | hxI₂
      · exact Or.inl ⟨hx.1, hxR⟩
      · exact Or.inr ⟨hx.1, hxI₂⟩
    have hle_sum : (G.V ∩ L).ncard ≤ (G.V ∩ R).ncard + (G.V ∩ barI₂).ncard :=
      (Set.ncard_le_ncard hsub_V ((G.finite_V.inter_of_left R).union (G.finite_V.inter_of_left
        barI₂))).trans
        (Set.ncard_union_le _ _)
    omega

/-- Any `G`-normal arc-connected set `K ⊆ S` meeting `F₁` and `F₂ ∪ barI₁` (or meeting `F₂` and
`F₁ ∪ barI₂`) contains a `G`-normal `[0, 1]`-arc `R ⊆ K` with `r ≤ (G.V ∩ R).ncard ≤ (G.V ∩
K).ncard`. -/
theorem ncard_ge_of_arcConnected_meets {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {F₁ F₂ barI₁ barI₂ : Set S} {u v z : S} {r m : ℕ}
    (hDisj : Disjoint F₁ F₂)
    (hbarI₁_norm : G.IsNormal barI₁) (hbarI₂_norm : G.IsNormal barI₂)
    (hbarI₁_ends : IsLineWithEnds barI₁ u z) (hbarI₂_ends : IsLineWithEnds barI₂ z v)
    (hu : u ∈ barI₁ ∩ F₂) (hbarI₁_disj : Disjoint barI₁ F₁)
    (hv : v ∈ barI₂ ∩ F₁) (hbarI₂_disj : Disjoint barI₂ F₂)
    (h2r : 2 * r ≤ m)
    (hbarI₁_ncard : (G.V ∩ barI₁).ncard = r) (hbarI₂_ncard : (G.V ∩ barI₂).ncard = m - r)
    (hmin : ∀ F : Set S, G.IsNormal F → IsLine F → (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      m ≤ (G.V ∩ F).ncard)
    {K : Set S} (hK_norm : G.IsNormal K) (hK_arc : IsArcConnected K)
    (hmeets : ((K ∩ F₁).Nonempty ∧ (K ∩ (F₂ ∪ barI₁)).Nonempty) ∨
      ((K ∩ F₂).Nonempty ∧ (K ∩ (F₁ ∪ barI₂)).Nonempty)) :
    r ≤ (G.V ∩ K).ncard := by
  rcases hmeets with ⟨⟨a, haK, haF₁⟩, ⟨b, hbK, hb_or⟩⟩ | ⟨⟨a, haK, haF₂⟩, ⟨b, hbK, hb_or⟩⟩
  · have hab : a ≠ b := by
      rintro rfl
      rcases hb_or with haF₂ | haI₁
      · exact disjoint_left.mp hDisj haF₁ haF₂
      · exact disjoint_left.mp hbarI₁_disj haI₁ haF₁
    obtain ⟨R, hRK, hR_ends⟩ := hK_arc a haK b hbK hab
    have hR_norm : G.IsNormal R := fun x hx => hK_norm ⟨hRK hx.1, hx.2⟩
    have hR_le : (G.V ∩ R).ncard ≤ (G.V ∩ K).ncard :=
      Set.ncard_le_ncard (inter_subset_inter_right G.V hRK) (G.finite_V.inter_of_left K)
    rcases hb_or with hbF₂ | hbI₁
    · have hm_le := hmin R hR_norm (IsLineWithEnds.isLine hR_ends) ⟨a, hR_ends.left_mem, haF₁⟩ ⟨b,
        hR_ends.right_mem, hbF₂⟩
      omega
    · have hr_le := lemma_9_3_obs G hDisj hbarI₁_norm hbarI₂_norm hbarI₁_ends hbarI₂_ends
        hu hv h2r hbarI₁_ncard hbarI₂_ncard hmin hR_norm (IsLineWithEnds.isLine hR_ends)
        (Or.inl ⟨⟨a, hR_ends.left_mem, haF₁⟩, ⟨b, hR_ends.right_mem, hbI₁⟩⟩)
      omega
  · have hab : a ≠ b := by
      rintro rfl
      rcases hb_or with haF₁ | haI₂
      · exact disjoint_left.mp hDisj haF₁ haF₂
      · exact disjoint_left.mp hbarI₂_disj haI₂ haF₂
    obtain ⟨R, hRK, hR_ends⟩ := hK_arc a haK b hbK hab
    have hR_norm : G.IsNormal R := fun x hx => hK_norm ⟨hRK hx.1, hx.2⟩
    have hR_le : (G.V ∩ R).ncard ≤ (G.V ∩ K).ncard :=
      Set.ncard_le_ncard (inter_subset_inter_right G.V hRK) (G.finite_V.inter_of_left K)
    rcases hb_or with hbF₁ | hbI₂
    · have hm_le := hmin R hR_norm (IsLineWithEnds.isLine hR_ends) ⟨b, hR_ends.right_mem, hbF₁⟩ ⟨a,
        hR_ends.left_mem, haF₂⟩
      omega
    · have hr_le := lemma_9_3_obs G hDisj hbarI₁_norm hbarI₂_norm hbarI₁_ends hbarI₂_ends
        hu hv h2r hbarI₁_ncard hbarI₂_ncard hmin hR_norm (IsLineWithEnds.isLine hR_ends)
        (Or.inr ⟨⟨a, hR_ends.left_mem, haF₂⟩, ⟨b, hR_ends.right_mem, hbI₂⟩⟩)
      omega

/-- Helper lemma for Claims 1 and 2 of (9.3): if `j '' K` (where `K ⊆ S` is preconnected) meets
`E₁'` and `E₂ ∪ j '' barI₁`, then `K` meets `F₁` and `F₂ ∪ barI₁`; symmetrically, if `j '' K` meets
`E₂` and `E₁' ∪ j '' barI₂`, then `K` meets `F₂` and `F₁ ∪ barI₂`. -/
theorem meets_F₁_or_F₂_of_meets_E {S Z : Type u} [TopologicalSpace S] [TopologicalSpace Z] [T2Space
  Z]
    {j : S → Z} (hj : IsClosedEmbedding j)
    {F₁ F₂ barI₁ barI₂ : Set S} {E₁ E₂ E₁' E₂' : Set Z}
    (hE₁ : IsClosedDisc E₁) (hbE₁ : discBd E₁ = j '' F₁)
    (hE₂ : IsClosedDisc E₂) (hbE₂ : discBd E₂ = j '' F₂)
    (hE₁' : IsClosedDisc E₁') (hE₁'_compl : E₁' = (discInt E₁)ᶜ)
    (hE₂' : IsClosedDisc E₂') (hE₂'_compl : E₂' = (discInt E₂)ᶜ)
    (hE₂_in_E₁ : E₂ ⊆ discInt E₁) (hE₁'_in_E₂' : E₁' ⊆ discInt E₂')
    (hbarI₁_in_E₁ : j '' barI₁ ⊆ discInt E₁)
    (hbarI₂_in_E₂' : j '' barI₂ ⊆ discInt E₂')
    {K : Set S} (hK_pc : IsPreconnected K) :
    (((j '' K ∩ E₁').Nonempty ∧ (j '' K ∩ (E₂ ∪ j '' barI₁)).Nonempty) →
      (K ∩ F₁).Nonempty ∧ (K ∩ (F₂ ∪ barI₁)).Nonempty) ∧
    (((j '' K ∩ E₂).Nonempty ∧ (j '' K ∩ (E₁' ∪ j '' barI₂)).Nonempty) →
      (K ∩ F₂).Nonempty ∧ (K ∩ (F₁ ∪ barI₂)).Nonempty) := by
  have hjK_pc : IsPreconnected (j '' K) := hK_pc.image j hj.continuous.continuousOn
  have hcov₁ : E₁ ∪ E₁' = univ := by
    rw [hE₁'_compl]
    apply eq_univ_of_forall
    intro w
    by_cases hw : w ∈ E₁
    · exact Or.inl hw
    · exact Or.inr fun h => hw h.1
  have hinter₁ : E₁ ∩ E₁' = j '' F₁ := by
    rw [← hbE₁, hE₁'_compl]
    ext w
    simp only [mem_inter_iff, mem_compl_iff, discInt, mem_sdiff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun h => ⟨Surface.discBd_subset E₁ h, fun _ => h⟩⟩
  have hcov₂ : E₂ ∪ E₂' = univ := by
    rw [hE₂'_compl]
    apply eq_univ_of_forall
    intro w
    by_cases hw : w ∈ E₂
    · exact Or.inl hw
    · exact Or.inr fun h => hw h.1
  have hinter₂ : E₂ ∩ E₂' = j '' F₂ := by
    rw [← hbE₂, hE₂'_compl]
    ext w
    simp only [mem_inter_iff, mem_compl_iff, discInt, mem_sdiff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun h => ⟨Surface.discBd_subset E₂ h, fun _ => h⟩⟩
  constructor
  · rintro ⟨⟨w₁, hw₁K, hw₁E₁'⟩, ⟨w₂, hw₂K, hw₂_or⟩⟩
    have hw₂E₁ : w₂ ∈ E₁ := by
      rcases hw₂_or with hw₂E₂ | hw₂I₁
      · exact (hE₂_in_E₁ hw₂E₂).1
      · exact (hbarI₁_in_E₁ hw₂I₁).1
    obtain ⟨_, ⟨x₁, hx₁K, rfl⟩, hx₁_in⟩ := preconnected_inter_nonempty_of_closed_cover hjK_pc
      hE₁.isClosed hE₁'.isClosed (fun w _ => hcov₁ ▸ mem_univ w) ⟨w₂, hw₂K, hw₂E₁⟩ ⟨w₁, hw₁K,
        hw₁E₁'⟩
    rw [hinter₁] at hx₁_in
    obtain ⟨x₁', hx₁'F₁, hx₁'_eq⟩ := hx₁_in
    have hx₁F₁ : x₁ ∈ F₁ := hj.injective hx₁'_eq ▸ hx₁'F₁
    refine ⟨⟨x₁, hx₁K, hx₁F₁⟩, ?_⟩
    rcases hw₂_or with hw₂E₂ | ⟨x₂, hx₂I₁, rfl⟩
    · have hw₁E₂' : w₁ ∈ E₂' := (hE₁'_in_E₂' hw₁E₁').1
      obtain ⟨_, ⟨x₂, hx₂K, rfl⟩, hx₂_in⟩ := preconnected_inter_nonempty_of_closed_cover hjK_pc
        hE₂.isClosed hE₂'.isClosed (fun w _ => hcov₂ ▸ mem_univ w) ⟨w₂, hw₂K, hw₂E₂⟩ ⟨w₁, hw₁K,
          hw₁E₂'⟩
      rw [hinter₂] at hx₂_in
      obtain ⟨x₂', hx₂'F₂, hx₂'_eq⟩ := hx₂_in
      exact ⟨x₂, hx₂K, Or.inl (hj.injective hx₂'_eq ▸ hx₂'F₂)⟩
    · obtain ⟨x₂', hx₂'K, hx₂'_eq⟩ := hw₂K
      exact ⟨x₂', hx₂'K, Or.inr (hj.injective hx₂'_eq.symm ▸ hx₂I₁)⟩
  · rintro ⟨⟨w₁, hw₁K, hw₁E₂⟩, ⟨w₂, hw₂K, hw₂_or⟩⟩
    have hw₂E₂' : w₂ ∈ E₂' := by
      rcases hw₂_or with hw₂E₁' | hw₂I₂
      · exact (hE₁'_in_E₂' hw₂E₁').1
      · exact (hbarI₂_in_E₂' hw₂I₂).1
    obtain ⟨_, ⟨x₁, hx₁K, rfl⟩, hx₁_in⟩ := preconnected_inter_nonempty_of_closed_cover hjK_pc
      hE₂.isClosed hE₂'.isClosed (fun w _ => hcov₂ ▸ mem_univ w) ⟨w₁, hw₁K, hw₁E₂⟩ ⟨w₂, hw₂K,
        hw₂E₂'⟩
    rw [hinter₂] at hx₁_in
    obtain ⟨x₁', hx₁'F₂, hx₁'_eq⟩ := hx₁_in
    have hx₁F₂ : x₁ ∈ F₂ := hj.injective hx₁'_eq ▸ hx₁'F₂
    refine ⟨⟨x₁, hx₁K, hx₁F₂⟩, ?_⟩
    rcases hw₂_or with hw₂E₁' | ⟨x₂, hx₂I₂, rfl⟩
    · have hw₁E₁ : w₁ ∈ E₁ := (hE₂_in_E₁ hw₁E₂).1
      obtain ⟨_, ⟨x₂, hx₂K, rfl⟩, hx₂_in⟩ := preconnected_inter_nonempty_of_closed_cover hjK_pc
        hE₁.isClosed hE₁'.isClosed (fun w _ => hcov₁ ▸ mem_univ w) ⟨w₁, hw₁K, hw₁E₁⟩ ⟨w₂, hw₂K,
          hw₂E₁'⟩
      rw [hinter₁] at hx₂_in
      obtain ⟨x₂', hx₂'F₁, hx₂'_eq⟩ := hx₂_in
      exact ⟨x₂, hx₂K, Or.inl (hj.injective hx₂'_eq ▸ hx₂'F₁)⟩
    · obtain ⟨x₂', hx₂'K, hx₂'_eq⟩ := hw₂K
      exact ⟨x₂', hx₂'K, Or.inr (hj.injective hx₂'_eq.symm ▸ hx₂I₂)⟩

/-- If a closed disc `D ⊆ Z` with `discBd D ⊆ discComplement P` separates `P 0` and `P 2` (or `P 1`
and `P 2`), then `discBd D` meets `E₂ ∪ j '' barI₁` (respectively `E₁' ∪ j '' barI₂`). -/
theorem discBd_meets_K₁_or_K₂ {S Z : Type u} [TopologicalSpace S] [TopologicalSpace Z] [T2Space Z]
    (hCS_Z : IsClosedSurface Z) (hSphZ : IsSphere Z) {j : S → Z} (hj : IsClosedEmbedding j)
    {F₁ F₂ barI₁ barI₂ : Set S} {u v z : S}
    (hbarI₁_ends : IsLineWithEnds barI₁ u z) (hbarI₂_ends : IsLineWithEnds barI₂ z v)
    (hu : u ∈ barI₁ ∩ F₂) (hv : v ∈ barI₂ ∩ F₁)
    {D₁ D₂ D₃ E₂ E₁' : Set Z}
    (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂) (hD₃ : IsClosedDisc D₃)
    (hE₂ : IsClosedDisc E₂) (hbE₂ : discBd E₂ = j '' F₂)
    (hE₁' : IsClosedDisc E₁') (hbE₁' : discBd E₁' = j '' F₁)
    (hD₁_in_E₂ : D₁ ⊆ discInt E₂) (hD₂_in_E₁' : D₂ ⊆ discInt E₁')
    (hjz_D₃ : j z ∈ discInt D₃)
    {D : Set Z} (hD : IsClosedDisc D)
    (hbd_sub : discBd D ⊆ discComplement ![D₁, D₂, D₃]) :
    ((D₁ ⊆ D ∧ ¬ D₃ ⊆ D) ∨ (¬ D₁ ⊆ D ∧ D₃ ⊆ D) →
      (discBd D ∩ (E₂ ∪ j '' barI₁)).Nonempty) ∧
    ((D₂ ⊆ D ∧ ¬ D₃ ⊆ D) ∨ (¬ D₂ ⊆ D ∧ D₃ ⊆ D) →
      (discBd D ∩ (E₁' ∪ j '' barI₂)).Nonempty) := by
  have hmanZ : ∀ x : Z, IsManifoldPoint x := fun x => (hCS_Z.2.2 x).isManifoldPoint
  let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
  have hP : ∀ i, IsClosedDisc (P i) := fun i => by
    fin_cases i
    · exact hD₁
    · exact hD₂
    · exact hD₃
  obtain ⟨D', hD', hbD', hD'_compl, _⟩ := exists_compl_disc_in_sphere hSphZ hD
  have hcov : D ∪ D' = univ := by
    rw [hD'_compl]
    apply eq_univ_of_forall
    intro w
    by_cases hw : w ∈ D
    · exact Or.inl hw
    · exact Or.inr fun h => hw h.1
  have hinter : D ∩ D' = discBd D := by
    rw [hD'_compl]
    ext w
    simp only [mem_inter_iff, mem_compl_iff, discInt, mem_sdiff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun h => ⟨Surface.discBd_subset D h, fun _ => h⟩⟩
  have hdisj_int : ∀ i : Fin 3, Disjoint (discInt (P i)) (discBd D) := by
    intro i
    rw [disjoint_left]
    intro w hwI hwB
    exact hwI.2 (discComplement_inter_disc_subset_boundary hCS_Z P hP i ⟨hbd_sub hwB, hwI.1⟩)
  have hpt_in_D' : ∀ (i : Fin 3) (q : Z), q ∈ discInt (P i) → ¬ P i ⊆ D → q ∈ D' := by
    intro i q hq hnot
    rw [hD'_compl]
    intro hqD
    rcases hD.side hmanZ (hP i).isPreconnected_discInt (hdisj_int i) with hin | hout
    · apply hnot
      apply (hP i).subset_closure_discInt.trans
      rw [← hD.isClosed.closure_eq]
      exact closure_mono (hin.trans (discInt_subset D))
    · exact disjoint_left.mp hout hq hqD.1
  obtain ⟨p₁, hp₁⟩ := hD₁.nonempty_discInt
  obtain ⟨p₂, hp₂⟩ := hD₂.nonempty_discInt
  have hp₁_E₂ : p₁ ∈ E₂ := (hD₁_in_E₂ hp₁.1).1
  have hp₂_E₁' : p₂ ∈ E₁' := (hD₂_in_E₁' hp₂.1).1
  have hjz_I₁ : j z ∈ j '' barI₁ := mem_image_of_mem j hbarI₁_ends.right_mem
  have hjz_I₂ : j z ∈ j '' barI₂ := mem_image_of_mem j hbarI₂_ends.left_mem
  have hK₁_pc : IsPreconnected (E₂ ∪ j '' barI₁) := by
    have h1 : IsPreconnected E₂ := hE₂.isPreconnected
    have h2 : IsPreconnected (j '' barI₁) :=
      (IsLineWithEnds.isConnected hbarI₁_ends).2.image j hj.continuous.continuousOn
    exact h1.union (j u) (Surface.discBd_subset E₂ (hbE₂.symm ▸ mem_image_of_mem j hu.2))
      (mem_image_of_mem j hu.1) h2
  have hK₂_pc : IsPreconnected (E₁' ∪ j '' barI₂) := by
    have h1 : IsPreconnected E₁' := hE₁'.isPreconnected
    have h2 : IsPreconnected (j '' barI₂) :=
      (IsLineWithEnds.isConnected hbarI₂_ends).2.image j hj.continuous.continuousOn
    exact h1.union (j v) (Surface.discBd_subset E₁' (hbE₁'.symm ▸ mem_image_of_mem j hv.2))
      (mem_image_of_mem j hv.1) h2
  constructor
  · intro hsep
    have hne_D : ((E₂ ∪ j '' barI₁) ∩ D).Nonempty := by
      rcases hsep with ⟨h1, _⟩ | ⟨_, h3⟩
      · exact ⟨p₁, Or.inl hp₁_E₂, h1 hp₁.1⟩
      · exact ⟨j z, Or.inr hjz_I₁, h3 hjz_D₃.1⟩
    have hne_D' : ((E₂ ∪ j '' barI₁) ∩ D').Nonempty := by
      rcases hsep with ⟨_, h3⟩ | ⟨h1, _⟩
      · exact ⟨j z, Or.inr hjz_I₁, hpt_in_D' 2 (j z) hjz_D₃ h3⟩
      · exact ⟨p₁, Or.inl hp₁_E₂, hpt_in_D' 0 p₁ hp₁ h1⟩
    obtain ⟨w, hwK₁, hwDD'⟩ := preconnected_inter_nonempty_of_closed_cover hK₁_pc
      hD.isClosed hD'.isClosed (fun w _ => hcov ▸ mem_univ w) hne_D hne_D'
    exact ⟨w, hinter ▸ hwDD', hwK₁⟩
  · intro hsep
    have hne_D : ((E₁' ∪ j '' barI₂) ∩ D).Nonempty := by
      rcases hsep with ⟨h2, _⟩ | ⟨_, h3⟩
      · exact ⟨p₂, Or.inl hp₂_E₁', h2 hp₂.1⟩
      · exact ⟨j z, Or.inr hjz_I₂, h3 hjz_D₃.1⟩
    have hne_D' : ((E₁' ∪ j '' barI₂) ∩ D').Nonempty := by
      rcases hsep with ⟨_, h3⟩ | ⟨h2, _⟩
      · exact ⟨j z, Or.inr hjz_I₂, hpt_in_D' 2 (j z) hjz_D₃ h3⟩
      · exact ⟨p₂, Or.inl hp₂_E₁', hpt_in_D' 1 p₂ hp₂ h2⟩
    obtain ⟨w, hwK₂, hwDD'⟩ := preconnected_inter_nonempty_of_closed_cover hK₂_pc
      hD.isClosed hD'.isClosed (fun w _ => hcov ▸ mem_univ w) hne_D hne_D'
    exact ⟨w, hinter ▸ hwDD', hwK₂⟩

private theorem two_cuff_complement_lies_in_embedding_range
    {S : Type u}
    {Z : Type u}
    [TopologicalSpace Z]
    [T2Space Z]
    (hCS_Z : IsClosedSurface Z)
    {j : S → Z}
    {D₁ : Set Z}
    {D₂ : Set Z}
    {D₃ : Set Z}
    (hP_disj : Pairwise fun i k => Disjoint (![D₁, D₂, D₃] i) (![D₁, D₂, D₃] k))
    (hrange_eq : range j = discComplement ![D₁, D₂]) :
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    (∀ (i : Fin 3), IsClosedDisc (P i)) →
    (∀ (i : Fin 2), IsClosedDisc (![D₁, D₂] i)) →
    (Pairwise fun i k => Disjoint (![D₁, D₂] i) (![D₁, D₂] k)) →
    discComplement P ⊆ range j := by
  intro P hP hP₂ hP₂_disj
  rw [hrange_eq]
  intro w hw
  rw [mem_discComplement_iff hCS_Z P hP hP_disj] at hw
  rw [mem_discComplement_iff hCS_Z ![D₁, D₂] hP₂ hP₂_disj]
  intro i
  fin_cases i
  · exact hw 0
  · exact hw 1

/-- **Graph Minors VII, (9.3), Claim 1** (pages 244–245):
"*Claim 1.* *$G$ is boundary-linked in $\Sigma'$.*" -/
theorem lemma_9_3_claim_1 {S Z : Type u} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace Z] [T2Space Z]
    (hCS_Z : IsClosedSurface Z) (hSphZ : IsSphere Z) {j : S → Z} (hj : IsClosedEmbedding j)
    (G : Drawing S) {C₁ C₂ F₁ F₂ barI₁ barI₂ : Set S} {u v z : S} {r m : ℕ}
    (hDisj : Disjoint F₁ F₂)
    (hbarI₁_norm : G.IsNormal barI₁) (hbarI₂_norm : G.IsNormal barI₂)
    (hbarI₁_ends : IsLineWithEnds barI₁ u z) (hbarI₂_ends : IsLineWithEnds barI₂ z v)
    (hu : u ∈ barI₁ ∩ F₂) (hbarI₁_disj : Disjoint barI₁ F₁)
    (hv : v ∈ barI₂ ∩ F₁) (hbarI₂_disj : Disjoint barI₂ F₂)
    (h2r : 2 * r ≤ m)
    (hbarI₁_ncard : (G.V ∩ barI₁).ncard = r) (hbarI₂_ncard : (G.V ∩ barI₂).ncard = m - r)
    (hmin : ∀ F : Set S, G.IsNormal F → IsLine F → (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      m ≤ (G.V ∩ F).ncard)
    {D₁ D₂ D₃ E₁ E₂ E₁' E₂' : Set Z}
    (hD₁ : IsClosedDisc D₁) (hbD₁ : discBd D₁ = j '' C₁)
    (hD₂ : IsClosedDisc D₂) (hbD₂ : discBd D₂ = j '' C₂)
    (hD₃ : IsClosedDisc D₃) (hD₃_disj_V : Disjoint (j '' G.V) (discBd D₃))
    (hP_disj : Pairwise (fun i k : Fin 3 => Disjoint (![D₁, D₂, D₃] i) (![D₁, D₂, D₃] k)))
    (havoid : ∀ i : Fin 3, (embedDrawing hj G).U ∩ ![D₁, D₂, D₃] i =
      (embedDrawing hj G).V ∩ discBd (![D₁, D₂, D₃] i))
    (hrange_eq : range j = discComplement ![D₁, D₂])
    (hE₁ : IsClosedDisc E₁) (hbE₁ : discBd E₁ = j '' F₁)
    (hE₂ : IsClosedDisc E₂) (hbE₂ : discBd E₂ = j '' F₂)
    (hE₁' : IsClosedDisc E₁') (hbE₁' : discBd E₁' = j '' F₁) (hE₁'_compl : E₁' = (discInt E₁)ᶜ)
    (hE₂' : IsClosedDisc E₂') (hE₂'_compl : E₂' = (discInt E₂)ᶜ)
    (hD₁_in_E₂ : D₁ ⊆ discInt E₂) (hE₂_in_E₁ : E₂ ⊆ discInt E₁)
    (hD₂_in_E₁' : D₂ ⊆ discInt E₁') (hE₁'_in_E₂' : E₁' ⊆ discInt E₂')
    (hbarI₁_in_E₁ : j '' barI₁ ⊆ discInt E₁) (hbarI₂_in_E₂' : j '' barI₂ ⊆ discInt E₂')
    (hjz_D₃ : j z ∈ discInt D₃)
    (hC₁_lt_r : (G.V ∩ C₁).ncard < r) (hC₂_lt_r : (G.V ∩ C₂).ncard < r)
    (hkC₁ : (G.V ∩ C₁).ncard ≤ maxDisjointPaths G F₁ C₁)
    (hkC₂ : (G.V ∩ C₂).ncard ≤ maxDisjointPaths G F₂ C₂) :
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    let hP : ∀ i, IsClosedDisc (P i) := fun i => by
      fin_cases i
      · exact hD₁
      · exact hD₂
      · exact hD₃
    IsBoundaryLinked (drawingInSubspace (embedDrawing hj G) (discComplement P)
      (drawing_support_subset_discComplement hCS_Z (embedDrawing hj G) P hP hP_disj havoid)) := by
  intro P hP
  have hmanZ : ∀ x : Z, IsManifoldPoint x := fun x => (hCS_Z.2.2 x).isManifoldPoint
  let Γ := embedDrawing hj G
  have hP₂ : ∀ i : Fin 2, IsClosedDisc (![D₁, D₂] i) := fun i => by
    fin_cases i
    · exact hD₁
    · exact hD₂
  have hP₂_disj : Pairwise (fun i k : Fin 2 => Disjoint (![D₁, D₂] i) (![D₁, D₂] k)) := fun i k hik
    => by
    fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact hP_disj (by decide : (0 : Fin 3) ≠ 1)
    · exact hP_disj (by decide : (1 : Fin 3) ≠ 0)
    · exact (hik rfl).elim
  have hC_sub_range : discComplement P ⊆ range j := by
    exact two_cuff_complement_lies_in_embedding_range (S := S) (Z := Z) hCS_Z (j := j) (D₁ := D₁)
      (D₂ := D₂) (D₃ := D₃) hP_disj hrange_eq  hP hP₂ hP₂_disj
  apply drawingInDiscComplement_isBoundaryLinked hCS_Z Γ P hP hP_disj havoid
  intro F_Z hFZ_norm hFZ_oarc hFZ_sub D hD hbdD i hone
  have hFZ_range : F_Z ⊆ range j := hFZ_sub.trans hC_sub_range
  let F : Set S := j ⁻¹' F_Z
  have hjF_eq : j '' F = F_Z := image_preimage_eq_iff.mpr hFZ_range
  have hF_norm : G.IsNormal F := by
    rintro x ⟨hxF, hxU⟩
    have hjx : j x ∈ F_Z ∩ Γ.U := ⟨hxF, ⟨x, hxU, rfl⟩⟩
    obtain ⟨y, hyV, hyx⟩ := hFZ_norm hjx
    exact hj.injective hyx ▸ hyV
  have hF_oarc : IsOArc F := by
    obtain ⟨φ⟩ := hFZ_oarc
    exact ⟨φ.trans ((Homeomorph.setCongr hjF_eq.symm).trans (hj.isEmbedding.homeomorphImage
      F).symm)⟩
  have hF_arc : IsArcConnected F := IsOArc.isArcConnected hF_oarc
  have hF_pc : IsPreconnected F := hF_oarc.isPreconnected
  have hVF_eq : (Γ.V ∩ F_Z).ncard = (G.V ∩ F).ncard := by
    have himg : Γ.V ∩ F_Z = j '' (G.V ∩ F) := by
      ext w
      constructor
      · rintro ⟨⟨x, hxV, rfl⟩, hwF⟩
        exact ⟨x, ⟨hxV, hwF⟩, rfl⟩
      · rintro ⟨x, ⟨hxV, hxF⟩, rfl⟩
        exact ⟨⟨x, hxV, rfl⟩, hxF⟩
    rw [himg, ncard_image_of_injective _ hj.injective]
  rw [hVF_eq]
  obtain ⟨D', hD', hbD', hD'_compl, _⟩ := exists_compl_disc_in_sphere hSphZ hD
  have hcov_S : (j ⁻¹' D') ∪ (j ⁻¹' D) = univ := by
    ext x
    simp only [mem_union, mem_preimage, hD'_compl, mem_compl_iff, discInt, mem_sdiff, not_and,
      not_not, mem_univ, iff_true]
    by_cases hx : j x ∈ D
    · exact Or.inr hx
    · exact Or.inl fun h => (hx h).elim
  have hinter_S : (j ⁻¹' D') ∩ (j ⁻¹' D) ⊆ F := by
    intro x ⟨hxD', hxD⟩
    rw [mem_preimage, hD'_compl, mem_compl_iff, discInt, mem_sdiff, not_and, not_not] at hxD'
    change j x ∈ F_Z
    rw [← hbdD]
    exact hxD' hxD
  have hmeets_E := meets_F₁_or_F₂_of_meets_E hj hE₁ hbE₁ hE₂ hbE₂ hE₁' hE₁'_compl hE₂' hE₂'_compl
    hE₂_in_E₁ hE₁'_in_E₂' hbarI₁_in_E₁ hbarI₂_in_E₂' hF_pc
  have hmeets_K := discBd_meets_K₁_or_K₂ hCS_Z hSphZ hj hbarI₁_ends hbarI₂_ends hu hv
    hD₁ hD₂ hD₃ hE₂ hbE₂ hE₁' hbE₁' hD₁_in_E₂ hD₂_in_E₁' hjz_D₃
    hD (hbdD ▸ hFZ_sub)
  fin_cases i
  · -- Case i = 0 (D₁)
    change (Γ.V ∩ discBd (P 0)).ncard ≤ (G.V ∩ F).ncard
    have hVC₁_eq : (Γ.V ∩ discBd (P 0)).ncard = (G.V ∩ C₁).ncard := by
      change (j '' G.V ∩ discBd D₁).ncard = (G.V ∩ C₁).ncard
      rw [hbD₁, ← image_inter hj.injective, ncard_image_of_injective _ hj.injective]
    rw [hVC₁_eq]
    have hD₁_sub : D₁ ⊆ D := (hone 0).mpr rfl
    have hD₂_not : ¬ D₂ ⊆ D := fun h => by have := (hone 1).mp h; revert this; decide
    have hD₃_not : ¬ D₃ ⊆ D := fun h => by have := (hone 2).mp h; revert this; decide
    have hK₁_ne : (j '' F ∩ (E₂ ∪ j '' barI₁)).Nonempty := by
      rw [hjF_eq, ← hbdD]
      exact hmeets_K.1 (Or.inl ⟨hD₁_sub, hD₃_not⟩)
    by_cases hFE₁' : (j '' F ∩ E₁').Nonempty
    · have hr_le := ncard_ge_of_arcConnected_meets G hDisj hbarI₁_norm hbarI₂_norm
        hbarI₁_ends hbarI₂_ends hu hbarI₁_disj hv hbarI₂_disj h2r hbarI₁_ncard hbarI₂_ncard hmin
        hF_norm hF_arc (Or.inl (hmeets_E.1 ⟨hFE₁', hK₁_ne⟩))
      omega
    · have hdisj_E₁' : Disjoint E₁' (discBd D) := by
        rw [hbdD, ← hjF_eq, disjoint_left]
        intro w hwE₁' hwF
        exact hFE₁' ⟨w, hwF, hwE₁'⟩
      have hdisj_D : Disjoint E₁' D := by
        rcases hD.side hmanZ hE₁'.isPreconnected hdisj_E₁' with hin | hout
        · exfalso
          apply hD₂_not
          intro w hwD₂
          exact (hin (hD₂_in_E₁' hwD₂).1).1
        · exact hout
      have hF₁_in_D' : F₁ ⊆ j ⁻¹' D' := by
        intro x hxF₁
        rw [mem_preimage, hD'_compl]
        intro hxD
        have hjx_E₁' : j x ∈ E₁' :=
          Surface.discBd_subset E₁' (hbE₁'.symm ▸ mem_image_of_mem j hxF₁)
        exact disjoint_left.mp hdisj_D hjx_E₁' hxD.1
      have hC₁_in_D : C₁ ⊆ j ⁻¹' D := fun x hx =>
        hD₁_sub (Surface.discBd_subset D₁ (hbD₁.symm ▸ mem_image_of_mem j hx))
      have hk_le := maxDisjointPaths_le_of_closed_cover G hF_norm
        (hD'.isClosed.preimage hj.continuous) (hD.isClosed.preimage hj.continuous)
        hcov_S hinter_S hF₁_in_D' hC₁_in_D
      exact hkC₁.trans hk_le
  · -- Case i = 1 (D₂)
    change (Γ.V ∩ discBd (P 1)).ncard ≤ (G.V ∩ F).ncard
    have hVC₂_eq : (Γ.V ∩ discBd (P 1)).ncard = (G.V ∩ C₂).ncard := by
      change (j '' G.V ∩ discBd D₂).ncard = (G.V ∩ C₂).ncard
      rw [hbD₂, ← image_inter hj.injective, ncard_image_of_injective _ hj.injective]
    rw [hVC₂_eq]
    have hD₁_not : ¬ D₁ ⊆ D := fun h => by have := (hone 0).mp h; revert this; decide
    have hD₂_sub : D₂ ⊆ D := (hone 1).mpr rfl
    have hD₃_not : ¬ D₃ ⊆ D := fun h => by have := (hone 2).mp h; revert this; decide
    have hK₂_ne : (j '' F ∩ (E₁' ∪ j '' barI₂)).Nonempty := by
      rw [hjF_eq, ← hbdD]
      exact hmeets_K.2 (Or.inl ⟨hD₂_sub, hD₃_not⟩)
    by_cases hFE₂ : (j '' F ∩ E₂).Nonempty
    · have hr_le := ncard_ge_of_arcConnected_meets G hDisj hbarI₁_norm hbarI₂_norm
        hbarI₁_ends hbarI₂_ends hu hbarI₁_disj hv hbarI₂_disj h2r hbarI₁_ncard hbarI₂_ncard hmin
        hF_norm hF_arc (Or.inr (hmeets_E.2 ⟨hFE₂, hK₂_ne⟩))
      omega
    · have hdisj_E₂ : Disjoint E₂ (discBd D) := by
        rw [hbdD, ← hjF_eq, disjoint_left]
        intro w hwE₂ hwF
        exact hFE₂ ⟨w, hwF, hwE₂⟩
      have hdisj_D : Disjoint E₂ D := by
        rcases hD.side hmanZ hE₂.isPreconnected hdisj_E₂ with hin | hout
        · exfalso
          apply hD₁_not
          intro w hwD₁
          exact (hin (hD₁_in_E₂ hwD₁).1).1
        · exact hout
      have hF₂_in_D' : F₂ ⊆ j ⁻¹' D' := by
        intro x hxF₂
        rw [mem_preimage, hD'_compl]
        intro hxD
        have hjx_E₂ : j x ∈ E₂ :=
          Surface.discBd_subset E₂ (hbE₂.symm ▸ mem_image_of_mem j hxF₂)
        exact disjoint_left.mp hdisj_D hjx_E₂ hxD.1
      have hC₂_in_D : C₂ ⊆ j ⁻¹' D := fun x hx =>
        hD₂_sub (Surface.discBd_subset D₂ (hbD₂.symm ▸ mem_image_of_mem j hx))
      have hk_le := maxDisjointPaths_le_of_closed_cover G hF_norm
        (hD'.isClosed.preimage hj.continuous) (hD.isClosed.preimage hj.continuous)
        hcov_S hinter_S hF₂_in_D' hC₂_in_D
      exact hkC₂.trans hk_le
  · -- Case i = 2 (D₃)
    change (Γ.V ∩ discBd (P 2)).ncard ≤ (G.V ∩ F).ncard
    have hVD₃_empty : Γ.V ∩ discBd (P 2) = ∅ := hD₃_disj_V.inter_eq
    rw [hVD₃_empty, Set.ncard_empty]
    exact Nat.zero_le _

private theorem two_cuffs_supply_discs_inside_candidate
    {Z : Type u}
    [TopologicalSpace Z]
    [T2Space Z]
    (hCS_Z : IsClosedSurface Z)
    (hSphZ : IsSphere Z)
    {D₁ : Set Z}
    {D₂ : Set Z}
    {D₃ : Set Z}
    (Γ : Drawing Z)
    (hP_disj : Pairwise fun i k => Disjoint (![D₁, D₂, D₃] i) (![D₁, D₂, D₃] k)) :
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    (∀ (i : Fin 3), IsClosedDisc (P i)) →
    let C_sub : Set Z := discComplement P
    let S' : Type u := ↥C_sub
    (IsSurface S') →
    ∀ [T2Space S'],
    ∀ [ConnectedSpace S'],
    ∀ (hUC_G : Γ.U ⊆ C_sub),
    let G'_draw : Drawing ↥C_sub := drawingInSubspace Γ C_sub hUC_G
    ((cuffs S').Nonempty) →
    ∀ (X' : Set ↥C_sub),
    (IsSchismatic X') →
    (G'_draw.IsNormal X') →
    ∃ B₁ B₂ K₁ K₂, B₁ ⊆ X' ∧ B₂ ⊆ X' ∧ IsOArc B₁ ∧ IsOArc B₂ ∧ SurroundsCuff B₁ K₁ ∧ SurroundsCuff
      B₂ K₂ ∧ K₁ ≠ K₂ := by
  intro P hP C_sub S' hS' _ _ hUC_G G'_draw hcuffs_ne X' hX'_sch hX'_norm
  classical
  rcases hX'_sch.1 with hO | hX1 | hX2 | hX3
  · exfalso
    have hval_oarc : IsOArc ((Subtype.val : S' → Z) '' X') := by
      obtain ⟨φ⟩ := hO
      exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage X')⟩
    obtain ⟨M₁, M₂, -, hM₁, hM₂, hbM₁, hbM₂, hcupM, hcapM, -, -⟩ :=
      sphere_disc Z hSphZ _ hval_oarc
    have hdisj_idx : ∀ k : Fin 3, ¬ (P k ⊆ M₁ ∧ P k ⊆ M₂) := by
      intro k ⟨hk1, hk2⟩
      obtain ⟨q, hq⟩ := (hP k).nonempty_discInt
      have hq_cap : q ∈ M₁ ∩ M₂ := ⟨hk1 hq.1, hk2 hq.1⟩
      rw [hcapM] at hq_cap
      obtain ⟨y, _, rfl⟩ := hq_cap
      exact hq.2 (discComplement_inter_disc_subset_boundary hCS_Z P hP k ⟨y.2, hq.1⟩)
    have hone_M : (∀ i k : Fin 3, P i ⊆ M₁ → P k ⊆ M₁ → i = k) ∨
        (∀ i k : Fin 3, P i ⊆ M₂ → P k ⊆ M₂ → i = k) := by
      by_contra hnot
      push Not at hnot
      obtain ⟨⟨i₁, k₁, hi₁, hk₁, hne₁⟩, ⟨i₂, k₂, hi₂, hk₂, hne₂⟩⟩ := hnot
      have hcard₁ : 2 ≤ (Finset.univ.filter (fun i : Fin 3 => P i ⊆ M₁)).card :=
        Finset.one_lt_card.mpr ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁⟩,
          k₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₁⟩, hne₁⟩
      have hcard₂ : 2 ≤ (Finset.univ.filter (fun i : Fin 3 => P i ⊆ M₂)).card :=
        Finset.one_lt_card.mpr ⟨i₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₂⟩,
          k₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₂⟩, hne₂⟩
      have hdisj_fin : Disjoint (Finset.univ.filter (fun i : Fin 3 => P i ⊆ M₁))
          (Finset.univ.filter (fun i : Fin 3 => P i ⊆ M₂)) := by
        rw [Finset.disjoint_left]
        intro k hkM₁ hkM₂
        exact hdisj_idx k ⟨(Finset.mem_filter.mp hkM₁).2, (Finset.mem_filter.mp hkM₂).2⟩
      have hle3 : (Finset.univ.filter (fun i : Fin 3 => P i ⊆ M₁) ∪
          Finset.univ.filter (fun i : Fin 3 => P i ⊆ M₂)).card ≤ Fintype.card (Fin 3) :=
        Finset.card_le_univ _
      rw [Finset.card_union_of_disjoint hdisj_fin, Fintype.card_fin] at hle3
      omega
    rcases hone_M with hone₁ | hone₂
    · exact hX'_sch.2.1 (isNearPlanar_of_bounds_disc_including_at_most_one hCS_Z P hP hP_disj
        hM₁ hbM₁ hone₁)
    · exact hX'_sch.2.1 (isNearPlanar_of_bounds_disc_including_at_most_one hCS_Z P hP hP_disj
        hM₂ hbM₂ hone₂)
  · obtain ⟨B₁, B₂, P_line, a, b, hB₁, hB₂, hdisB, hP_line, ha, hb, hPB₁, hPB₂, rfl⟩ := hX1
    obtain ⟨K₁, K₂, hs₁, hs₂, hneK⟩ :=
      surrounding_cuffs_of_schismatic_x1 hS' hcuffs_ne hB₁ hB₂ hdisB hP_line ha hb hPB₁ hPB₂
        hX'_sch
    exact ⟨B₁, B₂, K₁, K₂, subset_union_left.trans subset_union_left,
      subset_union_right.trans subset_union_left, hB₁, hB₂, hs₁, hs₂, hneK⟩
  · obtain ⟨B₁, B₂, a, hB₁, hB₂, hcapB, rfl⟩ := hX2
    obtain ⟨K₁, K₂, hs₁, hs₂, hneK⟩ :=
      surrounding_cuffs_of_schismatic_x2 hS' hcuffs_ne hB₁ hB₂ hcapB hX'_sch
    exact ⟨B₁, B₂, K₁, K₂, subset_union_left, subset_union_right, hB₁, hB₂, hs₁, hs₂, hneK⟩
  · obtain ⟨P₁, P₂, P₃, a, b, hab, hP₁, hP₂, hP₃, h12, h13, h23, rfl⟩ := hX3
    obtain ⟨K₁, K₂, _, hs₁, hs₂, _, hne12, _, _⟩ :=
      surrounding_pairs_of_schismatic_theta hS' hcuffs_ne hab hP₁ hP₂ hP₃ h12 h13 h23 hX'_sch
    exact ⟨P₁ ∪ P₂, P₁ ∪ P₃, K₁, K₂, subset_union_left,
      union_subset (subset_union_left.trans subset_union_left) subset_union_right,
      isOArc_union_of_lines_inter_eq_ends hP₁ hP₂ h12,
      isOArc_union_of_lines_inter_eq_ends hP₁ hP₃ h13, hs₁, hs₂, hne12⟩

private theorem pullback_candidate_is_arc_connected
    {S : Type u}
    {Z : Type u}
    [TopologicalSpace S]
    [TopologicalSpace Z]
    {j : S → Z}
    (hj : IsClosedEmbedding j)
    (C_sub : Set Z)
    (X' : Set ↥C_sub) :
    let X : Set S := unliftEdge j C_sub X'
    (Subtype.val '' X' ⊆ range j) →
    (IsArcConnected X') →
    IsArcConnected X := by
  intro X hX'_val_range hX'_arc a ⟨a', ha', hja⟩ b ⟨b', hb', hjb⟩ hab
  have ha'b' : a' ≠ b' := fun h =>
    hab (hj.injective (hja.symm.trans ((congrArg Subtype.val h).trans hjb)))
  obtain ⟨R', hR'_sub, fR, hfR0, hfR1⟩ := hX'_arc a' ha' b' hb' ha'b'
  let R : Set S := unliftEdge j C_sub R'
  have hR_sub : R ⊆ X := fun x ⟨y, hy, hyx⟩ => ⟨y, hR'_sub hy, hyx⟩
  have hR'_range : (Subtype.val : ↥C_sub → Z) '' R' ⊆ range j :=
    (image_mono hR'_sub).trans hX'_val_range
  let eR : R' ≃ₜ R := unliftEdgeHomeomorph hj.isEmbedding hR'_range
  have hjeR : ∀ y : R', j (eR y).1 = y.1.1 := fun y =>
    congrArg Subtype.val ((hj.isEmbedding.homeomorphImage R).apply_symm_apply
      ⟨y.1.1, (image_unliftEdge_of_subset hR'_range).symm ▸ ⟨y.1, y.2, rfl⟩⟩)
  let φ : unitInterval ≃ₜ R := fR.trans eR
  have hφ0 : (φ 0).1 = a := hj.injective (by
    change j (eR (fR 0)).1 = j a
    rw [hjeR, hfR0, hja])
  have hφ1 : (φ 1).1 = b := hj.injective (by
    change j (eR (fR 1)).1 = j b
    rw [hjeR, hfR1, hjb])
  exact ⟨R, hR_sub, φ, hφ0, hφ1⟩

private theorem pullback_candidate_is_preconnected
    {S : Type u}
    {Z : Type u}
    [TopologicalSpace S]
    [TopologicalSpace Z]
    {j : S → Z}
    (hj : IsClosedEmbedding j)
    (C_sub : Set Z) :
    ∀ (X' : Set ↥C_sub),
    let X : Set S := unliftEdge j C_sub X'
    (Subtype.val '' X' ⊆ range j) →
    (IsConnected X') →
    IsPreconnected X := by
  intro X' X hX'_val_range hX'_conn
  let e := unliftEdgeHomeomorph hj.isEmbedding hX'_val_range
  have himg : (Subtype.val ∘ e) '' univ = X := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact (e y).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, mem_univ _, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  have : ConnectedSpace X' := Subtype.connectedSpace hX'_conn
  rw [← himg]
  exact isPreconnected_univ.image _ (continuous_subtype_val.comp e.continuous).continuousOn

private theorem pullback_candidate_meets_first_barrier
    {S : Type u}
    {Z : Type u}
    [TopologicalSpace Z]
    {j : S → Z}
    {barI₁ : Set S}
    {barI₂ : Set S}
    {D₁ : Set Z}
    {D₂ : Set Z}
    {D₃ : Set Z}
    {E₂ : Set Z}
    {E₁' : Set Z}
    (C_sub : Set Z) :
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    ∀ (X' : Set ↥C_sub),
    ∀ (B₁ : Set ↥C_sub),
    ∀ (B₂ : Set ↥C_sub),
    (B₁ ⊆ X') →
    (B₂ ⊆ X') →
    ∀ (i₁ : Fin 3),
    ∀ (i₂ : Fin 3),
    (i₁ ≠ i₂) →
    let X : Set S := unliftEdge j C_sub X'
    (j '' X = Subtype.val '' X') →
    ∀ (D_B₁ : Set Z),
    (discBd D_B₁ = Subtype.val '' B₁) →
    (∀ (j : Fin 3), P j ⊆ D_B₁ ↔ j = i₁) →
    ∀ (D_B₂ : Set Z),
    (discBd D_B₂ = Subtype.val '' B₂) →
    (∀ (j : Fin 3), P j ⊆ D_B₂ ↔ j = i₂) →
    ((D₁ ⊆ D_B₁ ∧ ¬D₃ ⊆ D_B₁ ∨ ¬D₁ ⊆ D_B₁ ∧ D₃ ⊆ D_B₁ → (discBd D_B₁ ∩ (E₂ ∪ j ''
      barI₁)).Nonempty) ∧ (D₂ ⊆ D_B₁ ∧ ¬D₃ ⊆ D_B₁ ∨ ¬D₂ ⊆ D_B₁ ∧ D₃ ⊆ D_B₁ → (discBd D_B₁ ∩ (E₁' ∪
      j '' barI₂)).Nonempty)) →
    ((D₁ ⊆ D_B₂ ∧ ¬D₃ ⊆ D_B₂ ∨ ¬D₁ ⊆ D_B₂ ∧ D₃ ⊆ D_B₂ → (discBd D_B₂ ∩ (E₂ ∪ j ''
      barI₁)).Nonempty) ∧ (D₂ ⊆ D_B₂ ∧ ¬D₃ ⊆ D_B₂ ∨ ¬D₂ ⊆ D_B₂ ∧ D₃ ⊆ D_B₂ → (discBd D_B₂ ∩ (E₁' ∪
      j '' barI₂ )).Nonempty)) →
    (j '' X ∩ (E₂ ∪ j '' barI₁)).Nonempty := by
  intro P X' B₁ B₂ hB₁_sub hB₂_sub i₁ i₂ hi₁i₂_ne X hjX_eq D_B₁ hbdB₁ honeB₁
    D_B₂ hbdB₂ honeB₂ hDB₁_K hDB₂_K
  rw [hjX_eq]
  have h02 : (i₁ = 0 ∨ i₁ = 2) ∨ (i₂ = 0 ∨ i₂ = 2) := by
    fin_cases i₁ <;> fin_cases i₂ <;> first | exact (hi₁i₂_ne rfl).elim | decide
  rcases h02 with hi₁ | hi₂
  · have hne : (discBd D_B₁ ∩ (E₂ ∪ j '' barI₁)).Nonempty := by
      apply hDB₁_K.1
      rcases hi₁ with rfl | rfl
      · exact Or.inl ⟨(honeB₁ 0).mpr rfl, fun h => by have := (honeB₁ 2).mp h; revert this; decide⟩
      · exact Or.inr ⟨fun h => by have := (honeB₁ 0).mp h; revert this; decide, (honeB₁ 2).mpr rfl⟩
    rw [hbdB₁] at hne
    exact hne.mono (inter_subset_inter_left _ (image_mono hB₁_sub))
  · have hne : (discBd D_B₂ ∩ (E₂ ∪ j '' barI₁)).Nonempty := by
      apply hDB₂_K.1
      rcases hi₂ with rfl | rfl
      · exact Or.inl ⟨(honeB₂ 0).mpr rfl, fun h => by have := (honeB₂ 2).mp h; revert this; decide⟩
      · exact Or.inr ⟨fun h => by have := (honeB₂ 0).mp h; revert this; decide, (honeB₂ 2).mpr rfl⟩
    rw [hbdB₂] at hne
    exact hne.mono (inter_subset_inter_left _ (image_mono hB₂_sub))

private theorem pullback_candidate_meets_second_barrier
    {S : Type u}
    {Z : Type u}
    [TopologicalSpace Z]
    {j : S → Z}
    {barI₁ : Set S}
    {barI₂ : Set S}
    {D₁ : Set Z}
    {D₂ : Set Z}
    {D₃ : Set Z}
    {E₂ : Set Z}
    {E₁' : Set Z}
    (C_sub : Set Z) :
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    ∀ (X' : Set ↥C_sub),
    ∀ (B₁ : Set ↥C_sub),
    ∀ (B₂ : Set ↥C_sub),
    (B₁ ⊆ X') →
    (B₂ ⊆ X') →
    ∀ (i₁ : Fin 3),
    ∀ (i₂ : Fin 3),
    (i₁ ≠ i₂) →
    let X : Set S := unliftEdge j C_sub X'
    (j '' X = Subtype.val '' X') →
    ∀ (D_B₁ : Set Z),
    (discBd D_B₁ = Subtype.val '' B₁) →
    (∀ (j : Fin 3), P j ⊆ D_B₁ ↔ j = i₁) →
    ∀ (D_B₂ : Set Z),
    (discBd D_B₂ = Subtype.val '' B₂) →
    (∀ (j : Fin 3), P j ⊆ D_B₂ ↔ j = i₂) →
    ((D₁ ⊆ D_B₁ ∧ ¬D₃ ⊆ D_B₁ ∨ ¬D₁ ⊆ D_B₁ ∧ D₃ ⊆ D_B₁ → (discBd D_B₁ ∩ (E₂ ∪ j ''
      barI₁)).Nonempty) ∧ (D₂ ⊆ D_B₁ ∧ ¬D₃ ⊆ D_B₁ ∨ ¬D₂ ⊆ D_B₁ ∧ D₃ ⊆ D_B₁ → (discBd D_B₁ ∩ (E₁' ∪
      j '' barI₂)).Nonempty)) →
    ((D₁ ⊆ D_B₂ ∧ ¬D₃ ⊆ D_B₂ ∨ ¬D₁ ⊆ D_B₂ ∧ D₃ ⊆ D_B₂ → (discBd D_B₂ ∩ (E₂ ∪ j ''
      barI₁)).Nonempty) ∧ (D₂ ⊆ D_B₂ ∧ ¬D₃ ⊆ D_B₂ ∨ ¬D₂ ⊆ D_B₂ ∧ D₃ ⊆ D_B₂ → (discBd D_B₂ ∩ (E₁' ∪
      j '' barI₂ )).Nonempty)) →
    (j '' X ∩ (E₁' ∪ j '' barI₂)).Nonempty := by
  intro P X' B₁ B₂ hB₁_sub hB₂_sub i₁ i₂ hi₁i₂_ne X hjX_eq D_B₁ hbdB₁ honeB₁
    D_B₂ hbdB₂ honeB₂ hDB₁_K hDB₂_K
  rw [hjX_eq]
  have h12 : (i₁ = 1 ∨ i₁ = 2) ∨ (i₂ = 1 ∨ i₂ = 2) := by
    fin_cases i₁ <;> fin_cases i₂ <;> first | exact (hi₁i₂_ne rfl).elim | decide
  rcases h12 with hi₁ | hi₂
  · have hne : (discBd D_B₁ ∩ (E₁' ∪ j '' barI₂)).Nonempty := by
      apply hDB₁_K.2
      rcases hi₁ with rfl | rfl
      · exact Or.inl ⟨(honeB₁ 1).mpr rfl, fun h => by have := (honeB₁ 2).mp h; revert this; decide⟩
      · exact Or.inr ⟨fun h => by have := (honeB₁ 1).mp h; revert this; decide, (honeB₁ 2).mpr rfl⟩
    rw [hbdB₁] at hne
    exact hne.mono (inter_subset_inter_left _ (image_mono hB₁_sub))
  · have hne : (discBd D_B₂ ∩ (E₁' ∪ j '' barI₂)).Nonempty := by
      apply hDB₂_K.2
      rcases hi₂ with rfl | rfl
      · exact Or.inl ⟨(honeB₂ 1).mpr rfl, fun h => by have := (honeB₂ 2).mp h; revert this; decide⟩
      · exact Or.inr ⟨fun h => by have := (honeB₂ 1).mp h; revert this; decide, (honeB₂ 2).mpr rfl⟩
    rw [hbdB₂] at hne
    exact hne.mono (inter_subset_inter_left _ (image_mono hB₂_sub))

private theorem one_candidate_disc_surrounds_original_cuff
    {Z : Type u}
    [TopologicalSpace Z]
    (P : Fin 3 → Set Z)
    (C_sub : Set Z)
    (X' : Set ↥C_sub)
    (B₁ : Set ↥C_sub)
    (B₂ : Set ↥C_sub)
    (hB₁_sub : B₁ ⊆ X')
    (hB₂_sub : B₂ ⊆ X')
    (i₁ : Fin 3)
    (i₂ : Fin 3)
    (hi₁i₂_ne : i₁ ≠ i₂)
    (D_B₁ : Set Z)
    (hDB₁ : IsClosedDisc D_B₁)
    (hbdB₁ : discBd D_B₁ = Subtype.val '' B₁)
    (honeB₁ : ∀ (j : Fin 3), P j ⊆ D_B₁ ↔ j = i₁)
    (D_B₂ : Set Z)
    (hDB₂ : IsClosedDisc D_B₂)
    (hbdB₂ : discBd D_B₂ = Subtype.val '' B₂)
    (honeB₂ : ∀ (j : Fin 3), P j ⊆ D_B₂ ↔ j = i₂) :
    ∃ B₀ D₀ i₀, B₀ ⊆ X' ∧ IsClosedDisc D₀ ∧ discBd D₀ = Subtype.val '' B₀ ∧ (∀ (k : Fin 3), P k ⊆
      D₀ ↔ k = i₀) ∧ (i₀ = 0 ∨ i₀ = 1) := by
  have h01 : (i₁ = 0 ∨ i₁ = 1) ∨ (i₂ = 0 ∨ i₂ = 1) := by
    fin_cases i₁ <;> fin_cases i₂ <;> first | exact (hi₁i₂_ne rfl).elim | decide
  rcases h01 with hi₁ | hi₂
  · exact ⟨B₁, D_B₁, i₁, hB₁_sub, hDB₁, hbdB₁, honeB₁, hi₁⟩
  · exact ⟨B₂, D_B₂, i₂, hB₂_sub, hDB₂, hbdB₂, honeB₂, hi₂⟩

private theorem pulled_disc_sides_cover_cylinder
    {S : Type u}
    {Z : Type u}
    [TopologicalSpace Z]
    {j : S → Z}
    (D₀ : Set Z)
    (D₀' : Set Z)
    (hD₀'_compl : D₀' = (discInt D₀)ᶜ) :
    j ⁻¹' D₀ ∪ j ⁻¹' D₀' = univ ∧ j ⁻¹' D₀' ∪ j ⁻¹' D₀ = univ := by
  have h1 : (j ⁻¹' D₀) ∪ (j ⁻¹' D₀') = univ := by
    ext x
    simp only [mem_union, mem_preimage, hD₀'_compl, mem_compl_iff, discInt, mem_sdiff,
      not_and, not_not, mem_univ, iff_true]
    by_cases hx : j x ∈ D₀
    · exact Or.inl hx
    · exact Or.inr fun h => (hx h).elim
  exact ⟨h1, union_comm (j ⁻¹' D₀) (j ⁻¹' D₀') ▸ h1⟩

private theorem pulled_disc_sides_meet_along_candidate
    {S : Type u}
    {Z : Type u}
    [TopologicalSpace S]
    [TopologicalSpace Z]
    {j : S → Z}
    (hj : IsClosedEmbedding j)
    (D₀ : Set Z)
    (A : Set S)
    (hjA_eq : j '' A = discBd D₀)
    (D₀' : Set Z)
    (hD₀'_compl : D₀' = (discInt D₀)ᶜ) :
    j ⁻¹' D₀ ∩ j ⁻¹' D₀' ⊆ A ∧ j ⁻¹' D₀' ∩ j ⁻¹' D₀ ⊆ A := by
  have h1 : (j ⁻¹' D₀) ∩ (j ⁻¹' D₀') ⊆ A := by
    intro x ⟨hxD₀, hxD₀'⟩
    rw [mem_preimage, hD₀'_compl, mem_compl_iff, discInt, mem_sdiff, not_and,
      not_not] at hxD₀'
    have hjx_A : j x ∈ j '' A := hjA_eq ▸ hxD₀' hxD₀
    obtain ⟨x', hx'A, hx'_eq⟩ := hjx_A
    exact hj.injective hx'_eq ▸ hx'A
  exact ⟨h1, inter_comm (j ⁻¹' D₀) (j ⁻¹' D₀') ▸ h1⟩

/-- **Graph Minors VII, (9.3), Claim 2** (page 245):
"*Claim 2. As a drawing in $\Sigma'$, $G$ satisfies $\alpha(G) \ge r$.*" -/
theorem lemma_9_3_claim_2 {S Z : Type u} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z]
    (hCS_Z : IsClosedSurface Z) (hSphZ : IsSphere Z) {j : S → Z} (hj : IsClosedEmbedding j)
    (G : Drawing S) {F₁ F₂ barI₁ barI₂ : Set S} {u v z : S} {r m : ℕ}
    (hDisj : Disjoint F₁ F₂)
    (hbarI₁_norm : G.IsNormal barI₁) (hbarI₂_norm : G.IsNormal barI₂)
    (hbarI₁_ends : IsLineWithEnds barI₁ u z) (hbarI₂_ends : IsLineWithEnds barI₂ z v)
    (hu : u ∈ barI₁ ∩ F₂) (hbarI₁_disj : Disjoint barI₁ F₁)
    (hv : v ∈ barI₂ ∩ F₁) (hbarI₂_disj : Disjoint barI₂ F₂)
    (h2r : 2 * r ≤ m)
    (hbarI₁_ncard : (G.V ∩ barI₁).ncard = r) (hbarI₂_ncard : (G.V ∩ barI₂).ncard = m - r)
    (hmin : ∀ F : Set S, G.IsNormal F → IsLine F → (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      m ≤ (G.V ∩ F).ncard)
    {D₁ D₂ D₃ E₁ E₂ E₁' E₂' : Set Z}
    (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂) (hD₃ : IsClosedDisc D₃)
    (hP_disj : Pairwise (fun i k : Fin 3 => Disjoint (![D₁, D₂, D₃] i) (![D₁, D₂, D₃] k)))
    (havoid : ∀ i : Fin 3, (embedDrawing hj G).U ∩ ![D₁, D₂, D₃] i =
      (embedDrawing hj G).V ∩ discBd (![D₁, D₂, D₃] i))
    (hrange_eq : range j = discComplement ![D₁, D₂])
    (hE₁ : IsClosedDisc E₁) (hbE₁ : discBd E₁ = j '' F₁)
    (hE₂ : IsClosedDisc E₂) (hbE₂ : discBd E₂ = j '' F₂)
    (hE₁' : IsClosedDisc E₁') (hbE₁' : discBd E₁' = j '' F₁) (hE₁'_compl : E₁' = (discInt E₁)ᶜ)
    (hE₂' : IsClosedDisc E₂') (hE₂'_compl : E₂' = (discInt E₂)ᶜ)
    (hD₁_in_E₂ : D₁ ⊆ discInt E₂) (hE₂_in_E₁ : E₂ ⊆ discInt E₁)
    (hD₂_in_E₁' : D₂ ⊆ discInt E₁') (hE₁'_in_E₂' : E₁' ⊆ discInt E₂')
    (hbarI₁_in_E₁ : j '' barI₁ ⊆ discInt E₁) (hbarI₂_in_E₂' : j '' barI₂ ⊆ discInt E₂')
    (hjz_D₃ : j z ∈ discInt D₃)
    (hk12 : r ≤ maxDisjointPaths G F₁ F₂) :
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    let hP : ∀ i, IsClosedDisc (P i) := fun i => by
      fin_cases i
      · exact hD₁
      · exact hD₂
      · exact hD₃
    r ≤ alpha (drawingInSubspace (embedDrawing hj G) (discComplement P)
      (drawing_support_subset_discComplement hCS_Z (embedDrawing hj G) P hP hP_disj havoid)) := by
  classical
  intro P hP
  have hmanZ : ∀ x : Z, IsManifoldPoint x := fun x => (hCS_Z.2.2 x).isManifoldPoint
  let Γ := embedDrawing hj G
  let C_sub := discComplement P
  let S' : Type u := ↥C_sub
  have hS' : IsSurface S' := discComplement_isSurface hCS_Z P hP hP_disj
  have : T2Space S' := hS'.2.1
  have : ConnectedSpace S' := Subtype.connectedSpace (discComplement_isConnected hCS_Z P hP hP_disj)
  have hUC_G := drawing_support_subset_discComplement hCS_Z Γ P hP hP_disj havoid
  let G'_draw := drawingInSubspace Γ C_sub hUC_G
  have hcuffs_eq := discComplement_cuffs_eq hCS_Z P hP hP_disj
  have hcuffs_ne : (cuffs S').Nonempty := by
    rw [hcuffs_eq]
    exact ⟨_, 0, rfl⟩
  have hbd_ne : bd S' ≠ ∅ := by
    rw [← sUnion_cuffs]
    obtain ⟨C₀, hC₀⟩ := hcuffs_ne
    obtain ⟨x₀, hx₀⟩ := isOArc_nonempty (cuff_isOArc hS' hC₀)
    exact nonempty_iff_ne_empty.mp ⟨x₀, C₀, hC₀, hx₀⟩
  have hnsS' : ¬ IsSphere S' := not_isSphere_of_bd_ne_empty hbd_ne
  have hex_cand : ∃ X', IsAlphaCandidate G'_draw X' :=
    exists_alphaCandidate_of_two_prescribed_cuffs hCS_Z Γ P hP hP_disj
      (Or.inr (by simp)) havoid (by decide : (0 : Fin 3) ≠ 1)
  have h51 : GM07Theorem51Statement.{u} := fun M _ hM _ X hX_solid hX_ne =>
    @theorem_5_1_proof M _ hM _ X hX_solid hX_ne
  have hP₂ : ∀ i : Fin 2, IsClosedDisc (![D₁, D₂] i) := fun i => by
    fin_cases i
    · exact hD₁
    · exact hD₂
  have hP₂_disj : Pairwise (fun i k : Fin 2 => Disjoint (![D₁, D₂] i) (![D₁, D₂] k)) := fun i k hik
    => by
    fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact hP_disj (by decide : (0 : Fin 3) ≠ 1)
    · exact hP_disj (by decide : (1 : Fin 3) ≠ 0)
    · exact (hik rfl).elim
  have hC_sub_range : C_sub ⊆ range j := by
    rw [hrange_eq]
    intro w hw
    rw [mem_discComplement_iff hCS_Z P hP hP_disj] at hw
    rw [mem_discComplement_iff hCS_Z ![D₁, D₂] hP₂ hP₂_disj]
    intro i
    fin_cases i
    · exact hw 0
    · exact hw 1
  apply alpha_ge_of_schismatic_counts G'_draw hex_cand (exists_schismatic_of_isAlphaCandidate hS'
    hnsS' G'_draw)
  intro X' hX'_sch hX'_norm
  -- Step 1: Extract two O-arcs B₁, B₂ ⊆ X' surrounding distinct cuffs of S'
  have hex_two_cuffs : ∃ (B₁ B₂ : Set S') (K₁ K₂ : Set S'),
      B₁ ⊆ X' ∧ B₂ ⊆ X' ∧ IsOArc B₁ ∧ IsOArc B₂ ∧
      SurroundsCuff B₁ K₁ ∧ SurroundsCuff B₂ K₂ ∧ K₁ ≠ K₂ := by
    exact two_cuffs_supply_discs_inside_candidate hCS_Z hSphZ (D₁ := D₁) (D₂ := D₂) (D₃ := D₃)
      Γ hP_disj hP hS' hUC_G hcuffs_ne X' hX'_sch hX'_norm
  obtain ⟨B₁, B₂, K₁, K₂, hB₁_sub, hB₂_sub, hB₁_oarc, hB₂_oarc, hs₁, hs₂, hK₁K₂_ne⟩ := hex_two_cuffs
  have hK₁_mem : K₁ ∈ cuffs S' := hs₁.1
  have hK₂_mem : K₂ ∈ cuffs S' := hs₂.1
  rw [hcuffs_eq] at hK₁_mem hK₂_mem
  obtain ⟨i₁, rfl⟩ := hK₁_mem
  obtain ⟨i₂, rfl⟩ := hK₂_mem
  have hi₁i₂_ne : i₁ ≠ i₂ := by
    rintro rfl
    exact hK₁K₂_ne rfl
  -- Step 2: Pull X' back to S as X := unliftEdge j C_sub X'
  let X : Set S := unliftEdge j C_sub X'
  have hX'_val_range : (Subtype.val : S' → Z) '' X' ⊆ range j :=
    (image_subset_iff.mpr fun y _ => y.2).trans hC_sub_range
  have hjX_eq : j '' X = (Subtype.val : S' → Z) '' X' :=
    image_unliftEdge_of_subset hX'_val_range
  obtain ⟨hX'_sol, hX'_conn⟩ := hX'_sch.isSolid_and_isConnected hS'
  have hX'_arc : IsArcConnected X' := theorem_11_4_proof hS' hX'_conn hX'_sol.1
  have hX_arc : IsArcConnected X := by
    exact pullback_candidate_is_arc_connected (S := S) (Z := Z) (j := j) hj C_sub X'
      hX'_val_range hX'_arc
  have hX_pre : IsPreconnected X := by
    exact pullback_candidate_is_preconnected (S := S) (Z := Z) (j := j) hj C_sub X'
      hX'_val_range hX'_conn
  have hX_norm : G.IsNormal X :=
    drawingInSubspace_embedDrawing_isNormal_unliftEdge hj G C_sub hUC_G hX'_norm
  have hVX_eq : (X' ∩ G'_draw.V).ncard = (G.V ∩ X).ncard := by
    rw [inter_comm, drawingInSubspace_embedDrawing_V_inter_unliftEdge_ncard hj G C_sub hUC_G X']
  rw [hVX_eq]
  have hmeets_E := meets_F₁_or_F₂_of_meets_E hj hE₁ hbE₁ hE₂ hbE₂ hE₁' hE₁'_compl hE₂' hE₂'_compl
    hE₂_in_E₁ hE₁'_in_E₂' hbarI₁_in_E₁ hbarI₂_in_E₂' hX_pre
  -- Step 3: For each surrounding circle B_m, obtain the disc D_m in Z
  obtain ⟨D_B₁, hDB₁, hbdB₁, honeB₁⟩ :=
    surrounding_bounds_disc_including_exactly_one hCS_Z P hP hP_disj i₁ hB₁_oarc hs₁
  obtain ⟨D_B₂, hDB₂, hbdB₂, honeB₂⟩ :=
    surrounding_bounds_disc_including_exactly_one hCS_Z P hP hP_disj i₂ hB₂_oarc hs₂
  have hbdB₁_sub : discBd D_B₁ ⊆ C_sub := by rw [hbdB₁]; rintro _ ⟨y, _, rfl⟩; exact y.2
  have hbdB₂_sub : discBd D_B₂ ⊆ C_sub := by rw [hbdB₂]; rintro _ ⟨y, _, rfl⟩; exact y.2
  have hDB₁_K := discBd_meets_K₁_or_K₂ hCS_Z hSphZ hj hbarI₁_ends hbarI₂_ends hu hv
    hD₁ hD₂ hD₃ hE₂ hbE₂ hE₁' hbE₁' hD₁_in_E₂ hD₂_in_E₁' hjz_D₃ hDB₁ hbdB₁_sub
  have hDB₂_K := discBd_meets_K₁_or_K₂ hCS_Z hSphZ hj hbarI₁_ends hbarI₂_ends hu hv
    hD₁ hD₂ hD₃ hE₂ hbE₂ hE₁' hbE₁' hD₁_in_E₂ hD₂_in_E₁' hjz_D₃ hDB₂ hbdB₂_sub
  have hX_meets_K₁ : (j '' X ∩ (E₂ ∪ j '' barI₁)).Nonempty := by
    exact pullback_candidate_meets_first_barrier (S := S) (Z := Z) (j := j) (barI₁ := barI₁)
      (barI₂ := barI₂) (D₁ := D₁) (D₂ := D₂) (D₃ := D₃) (E₂ := E₂) (E₁' := E₁') C_sub X' B₁
      B₂ hB₁_sub hB₂_sub i₁ i₂ hi₁i₂_ne hjX_eq D_B₁ hbdB₁ honeB₁ D_B₂ hbdB₂
      honeB₂ hDB₁_K hDB₂_K
  have hX_meets_K₂ : (j '' X ∩ (E₁' ∪ j '' barI₂)).Nonempty := by
    exact pullback_candidate_meets_second_barrier (S := S) (Z := Z) (j := j) (barI₁ := barI₁)
      (barI₂ := barI₂) (D₁ := D₁) (D₂ := D₂) (D₃ := D₃) (E₂ := E₂) (E₁' := E₁') C_sub X' B₁
      B₂ hB₁_sub hB₂_sub i₁ i₂ hi₁i₂_ne hjX_eq D_B₁ hbdB₁ honeB₁ D_B₂ hbdB₂
      honeB₂ hDB₁_K hDB₂_K
  -- Step 4: Case split on whether j '' X meets E₁' or E₂
  by_cases hXE₁' : (j '' X ∩ E₁').Nonempty
  · exact ncard_ge_of_arcConnected_meets G hDisj hbarI₁_norm hbarI₂_norm
      hbarI₁_ends hbarI₂_ends hu hbarI₁_disj hv hbarI₂_disj h2r hbarI₁_ncard hbarI₂_ncard hmin
      hX_norm hX_arc (Or.inl (hmeets_E.1 ⟨hXE₁', hX_meets_K₁⟩))
  · by_cases hXE₂ : (j '' X ∩ E₂).Nonempty
    · exact ncard_ge_of_arcConnected_meets G hDisj hbarI₁_norm hbarI₂_norm
        hbarI₁_ends hbarI₂_ends hu hbarI₁_disj hv hbarI₂_disj h2r hbarI₁_ncard hbarI₂_ncard hmin
        hX_norm hX_arc (Or.inr (hmeets_E.2 ⟨hXE₂, hX_meets_K₂⟩))
    · -- Neither E₁' nor E₂ meets j '' X; take the circle B₀ ⊆ X' surrounding P 0 or P 1
      have hex_B₀ : ∃ (B₀ : Set S') (D₀ : Set Z) (i₀ : Fin 3),
          B₀ ⊆ X' ∧ IsClosedDisc D₀ ∧ discBd D₀ = (Subtype.val : S' → Z) '' B₀ ∧
          (∀ k, P k ⊆ D₀ ↔ k = i₀) ∧ (i₀ = 0 ∨ i₀ = 1) := by
        exact one_candidate_disc_surrounds_original_cuff (Z := Z) P C_sub X' B₁ B₂
          hB₁_sub hB₂_sub i₁ i₂ hi₁i₂_ne D_B₁ hDB₁ hbdB₁ honeB₁ D_B₂ hDB₂ hbdB₂ honeB₂
      obtain ⟨B₀, D₀, i₀, hB₀_sub, hD₀, hbdD₀, honeD₀, hi₀⟩ := hex_B₀
      let A : Set S := unliftEdge j C_sub B₀
      have hA_sub_X : A ⊆ X := fun x ⟨y, hy, hyx⟩ => ⟨y, hB₀_sub hy, hyx⟩
      have hA_norm : G.IsNormal A := fun x hx => hX_norm ⟨hA_sub_X hx.1, hx.2⟩
      have hB₀_val_range : (Subtype.val : S' → Z) '' B₀ ⊆ range j :=
        (image_mono hB₀_sub).trans hX'_val_range
      have hjA_eq : j '' A = discBd D₀ := by
        rw [hbdD₀, image_unliftEdge_of_subset hB₀_val_range]
      have hbdD₀_disj_E₁' : Disjoint E₁' (discBd D₀) := by
        rw [← hjA_eq, disjoint_left]
        intro w hwE₁' hwA
        exact hXE₁' ⟨w, image_mono hA_sub_X hwA, hwE₁'⟩
      have hbdD₀_disj_E₂ : Disjoint E₂ (discBd D₀) := by
        rw [← hjA_eq, disjoint_left]
        intro w hwE₂ hwA
        exact hXE₂ ⟨w, image_mono hA_sub_X hwA, hwE₂⟩
      obtain ⟨D₀', hD₀', _, hD₀'_compl, _⟩ := exists_compl_disc_in_sphere hSphZ hD₀
      have hcover_candidate_disc : (j ⁻¹' D₀) ∪ (j ⁻¹' D₀') = univ ∧ (j ⁻¹' D₀') ∪ (j ⁻¹' D₀)
        = univ := by
        exact pulled_disc_sides_cover_cylinder (S := S) (Z := Z) (j := j) D₀ D₀' hD₀'_compl
      have hinter_candidate_disc : (j ⁻¹' D₀) ∩ (j ⁻¹' D₀') ⊆ A ∧ (j ⁻¹' D₀') ∩ (j ⁻¹' D₀) ⊆ A := by
        exact pulled_disc_sides_meet_along_candidate (S := S) (Z := Z) (j := j) hj D₀ A hjA_eq D₀'
          hD₀'_compl
      obtain ⟨p₁, hp₁⟩ := hD₁.nonempty_discInt
      obtain ⟨p₂, hp₂⟩ := hD₂.nonempty_discInt
      have hp₁_E₂ : p₁ ∈ E₂ := (hD₁_in_E₂ hp₁.1).1
      have hp₂_E₁' : p₂ ∈ E₁' := (hD₂_in_E₁' hp₂.1).1
      have hVA_le : (G.V ∩ A).ncard ≤ (G.V ∩ X).ncard :=
        Set.ncard_le_ncard (inter_subset_inter_right G.V hA_sub_X) (G.finite_V.inter_of_left X)
      rcases hi₀ with rfl | rfl
      · -- i₀ = 0: D₁ ⊆ D₀ and ¬ D₂ ⊆ D₀
        have hp₁_D₀ : p₁ ∈ D₀ := (honeD₀ 0).mpr rfl hp₁.1
        have hD₂_not : ¬ D₂ ⊆ D₀ := fun h => by have := (honeD₀ 1).mp h; revert this; decide
        have hE₂_in_D₀ : E₂ ⊆ discInt D₀ := by
          rcases hD₀.side hmanZ hE₂.isPreconnected hbdD₀_disj_E₂ with hin | hout
          · exact hin
          · exact (disjoint_left.mp hout hp₁_E₂ hp₁_D₀).elim
        have hE₁'_in_D₀' : E₁' ⊆ D₀' := by
          rcases hD₀.side hmanZ hE₁'.isPreconnected hbdD₀_disj_E₁' with hin | hout
          · exfalso
            apply hD₂_not
            intro w hwD₂
            exact (hin (hD₂_in_E₁' hwD₂).1).1
          · rw [hD₀'_compl]
            intro w hwE₁' hwD₀
            exact disjoint_left.mp hout hwE₁' hwD₀.1
        have hF₁_in_D₀' : F₁ ⊆ j ⁻¹' D₀' := fun x hx =>
          hE₁'_in_D₀' (Surface.discBd_subset E₁' (hbE₁'.symm ▸ mem_image_of_mem j hx))
        have hF₂_in_D₀ : F₂ ⊆ j ⁻¹' D₀ := fun x hx =>
          (hE₂_in_D₀ (Surface.discBd_subset E₂ (hbE₂.symm ▸ mem_image_of_mem j hx))).1
        have hk_le := maxDisjointPaths_le_of_closed_cover G hA_norm
          (hD₀'.isClosed.preimage hj.continuous) (hD₀.isClosed.preimage hj.continuous)
          hcover_candidate_disc.2 hinter_candidate_disc.2 hF₁_in_D₀' hF₂_in_D₀
        exact (hk12.trans hk_le).trans hVA_le
      · -- i₀ = 1: D₂ ⊆ D₀ and ¬ D₁ ⊆ D₀
        have hp₂_D₀ : p₂ ∈ D₀ := (honeD₀ 1).mpr rfl hp₂.1
        have hD₁_not : ¬ D₁ ⊆ D₀ := fun h => by have := (honeD₀ 0).mp h; revert this; decide
        have hE₁'_in_D₀ : E₁' ⊆ discInt D₀ := by
          rcases hD₀.side hmanZ hE₁'.isPreconnected hbdD₀_disj_E₁' with hin | hout
          · exact hin
          · exact (disjoint_left.mp hout hp₂_E₁' hp₂_D₀).elim
        have hE₂_in_D₀' : E₂ ⊆ D₀' := by
          rcases hD₀.side hmanZ hE₂.isPreconnected hbdD₀_disj_E₂ with hin | hout
          · exfalso
            apply hD₁_not
            intro w hwD₁
            exact (hin (hD₁_in_E₂ hwD₁).1).1
          · rw [hD₀'_compl]
            intro w hwE₂ hwD₀
            exact disjoint_left.mp hout hwE₂ hwD₀.1
        have hF₁_in_D₀ : F₁ ⊆ j ⁻¹' D₀ := fun x hx =>
          (hE₁'_in_D₀ (Surface.discBd_subset E₁' (hbE₁'.symm ▸ mem_image_of_mem j hx))).1
        have hF₂_in_D₀' : F₂ ⊆ j ⁻¹' D₀' := fun x hx =>
          hE₂_in_D₀' (Surface.discBd_subset E₂ (hbE₂.symm ▸ mem_image_of_mem j hx))
        have hk_le := maxDisjointPaths_le_of_closed_cover G hA_norm
          (hD₀.isClosed.preimage hj.continuous) (hD₀'.isClosed.preimage hj.continuous)
          hcover_candidate_disc.1 hinter_candidate_disc.1 hF₁_in_D₀ hF₂_in_D₀'
        exact (hk12.trans hk_le).trans hVA_le

end GraphMinor.GM07
