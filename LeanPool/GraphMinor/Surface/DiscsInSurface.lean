/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Disc

/-!
# Closed discs in a surface

* `isOpen_image_of_manifold`: invariance of domain in a surface. So a closed disc of a surface minus
  its boundary is open (`IsChart.isOpen_image_ball`).
* `exists_sphere_map`: two closed discs that meet exactly in their common boundary form a sphere.
* `eq_of_discBd_eq`: in a connected surface that is not a sphere, a closed disc is determined by its
  boundary. Otherwise the two discs form a sphere that is open and closed in the surface.
* `isNullHomotopicOArcIn_of_subset_disc`: an `O`-arc in a closed disc inside `Z` is null-homotopic
  in `Z`.

The last two results are two of the three parts of `EpsteinStatement`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric OnePoint

universe u

variable {S : Type u} [TopologicalSpace S]

/-- **Invariance of domain in a surface.** A continuous injective map from an open set of `ℂ` to
manifold points has open image. -/
theorem isOpen_image_of_manifold {M : Set ℂ} {ρ : ℂ → S} (hM : IsOpen M) (hc : ContinuousOn ρ M)
    (hi : InjOn ρ M) (hman : ∀ z ∈ M, IsManifoldPoint (ρ z)) : IsOpen (ρ '' M) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨U, O, j, k, hU, -, hxU, hj, -, -, -, hl, -⟩ := (hman z hz).exists_chart
  have hM' : IsOpen (M ∩ ρ ⁻¹' U) := hc.isOpen_inter_preimage hM hU
  have hG : ContinuousOn (j ∘ ρ) (M ∩ ρ ⁻¹' U) :=
    hj.comp (hc.mono inter_subset_left) fun w hw => hw.2
  have hGi : InjOn (j ∘ ρ) (M ∩ ρ ⁻¹' U) := fun w hw w' hw' he =>
    hi hw.1 hw'.1 (hl.injOn hw.2 hw'.2 he)
  have hopen := isOpen_image_of_injOn hM' hG hGi
  refine ⟨U ∩ j ⁻¹' ((j ∘ ρ) '' (M ∩ ρ ⁻¹' U)), ?_, hj.isOpen_inter_preimage hU hopen,
    hxU, ⟨z, ⟨hz, hxU⟩, rfl⟩⟩
  rintro y ⟨hyU, w, hw, he⟩
  exact ⟨w, hw.1, hl.injOn hw.2 hyU he⟩

/-- A closed disc of a surface minus its boundary is open. -/
theorem IsChart.isOpen_image_ball {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g)
    (hman : ∀ x : S, IsManifoldPoint x) : IsOpen (g '' ball 0 1) :=
  isOpen_image_of_manifold isOpen_ball (c.gc.mono ball_subset_closedBall)
    (c.injOn.mono ball_subset_closedBall) fun _ _ => hman _

/-- A closed disc minus its boundary is the image of the open ball, and it misses the boundary. -/
theorem IsChart.union_ball {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) :
    g '' ball 0 1 ∪ discBd D = D ∧ Disjoint (g '' ball 0 1) (discBd D) := by
  constructor
  · rw [← c.g_sphere, ← image_union, ball_union_sphere, c.g_closedBall]
  · rw [← c.g_sphere, Set.disjoint_iff_inter_eq_empty,
      ← c.g_inter ball_subset_closedBall sphere_subset_closedBall]
    have : ball (0 : ℂ) 1 ∩ sphere 0 1 = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_sphere_zero_iff_norm, mem_empty_iff_false,
        iff_false, not_and]
      exact fun h1 h2 => h1.ne h2
    rw [this, image_empty]

/-- Two closed discs that meet exactly in their common boundary are the image of a sphere. -/
theorem exists_sphere_map {Δ₁ Δ₂ : Set S} (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂)
    (hb : discBd Δ₁ = discBd Δ₂) (hm : Δ₁ ∩ Δ₂ = discBd Δ₁) :
    ∃ T : OnePoint EuclideanPlane → S, Continuous T ∧ Function.Injective T ∧
      range T = Δ₁ ∪ Δ₂ := by
  classical
  obtain ⟨h₁', g₁, c₁⟩ := h₁.exists_isChart
  obtain ⟨h₂', g₂, c₂⟩ := h₂.exists_isChart
  obtain ⟨φ₀⟩ := oArc_sphere
  have hA : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  have hg₁s : MapsTo g₁ (sphere 0 1) (discBd Δ₁) := fun z hz => c₁.g_sphere ▸ mem_image_of_mem g₁ hz
  have hg₂s : MapsTo g₂ (sphere 0 1) (discBd Δ₂) := fun z hz => c₂.g_sphere ▸ mem_image_of_mem g₂ hz
  have hsub₁ := discBd_subset Δ₁
  have hsub₂ := discBd_subset Δ₂
  have hh₁s : MapsTo h₁' (discBd Δ₁) (sphere 0 1) := fun x hx => c₁.bd ▸ mem_image_of_mem h₁' hx
  have hh₂s : MapsTo h₂' (discBd Δ₂) (sphere 0 1) := fun x hx => c₂.bd ▸ mem_image_of_mem h₂' hx
  let β : ℂ → ℂ := fun z => h₂' (g₁ z⁻¹)
  let γ : ℂ → ℂ := fun w => (h₁' (g₂ w))⁻¹
  have hinv : ContinuousOn (fun z : ℂ => z⁻¹) (sphere 0 1) :=
    continuousOn_id.inv₀ fun z hz => ne_zero_of_sphere hz
  have m : BdMatch (sphere 0 1) (sphere 0 1) β γ := by
    refine ⟨fun z hz => hh₂s (hb ▸ hg₁s (inv_mem_sphere hz)), fun w hw =>
      inv_mem_sphere (hh₁s (hb ▸ hg₂s hw)), fun z hz => ?_, fun w hw => ?_, ?_, ?_⟩
    · change (h₁' (g₂ (h₂' (g₁ z⁻¹))))⁻¹ = z
      have h1 : g₁ z⁻¹ ∈ Δ₂ := hsub₂ (hb ▸ hg₁s (inv_mem_sphere hz))
      rw [c₂.gh h1, c₁.hg (hA (inv_mem_sphere hz)), inv_inv]
    · change h₂' (g₁ (h₁' (g₂ w))⁻¹⁻¹) = w
      have h1 : g₂ w ∈ Δ₁ := hsub₁ (hb.symm ▸ hg₂s hw)
      rw [inv_inv, c₁.gh h1, c₂.hg (hA hw)]
    · refine c₂.hc.comp ((c₁.gc.mono hA).comp hinv fun z hz => inv_mem_sphere hz) fun z hz => ?_
      exact hsub₂ (hb ▸ hg₁s (inv_mem_sphere hz))
    · exact ((c₁.hc.comp (c₂.gc.mono hA) fun w hw => hsub₁ (hb.symm ▸ hg₂s hw)).inv₀ fun w hw =>
        ne_zero_of_sphere (hh₁s (hb ▸ hg₂s hw)))
  obtain ⟨ψ, χ, m', hψ⟩ := exists_bdMatch_closedInner ⟨φ₀⟩ ⟨φ₀⟩ m
  rw [closedInner_sphere] at m'
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := id m'
  let G₂ : ℂ → S := g₂ ∘ ψ
  have hG₂c : ContinuousOn G₂ (closedBall 0 1) := c₂.gc.comp n5 n1
  have hG₂s : ∀ z ∈ sphere (0 : ℂ) 1, G₂ z = g₁ z⁻¹ := fun z hz => by
    change g₂ (ψ z) = g₁ z⁻¹
    rw [hψ hz]
    exact c₂.gh (hsub₂ (hb ▸ hg₁s (inv_mem_sphere hz)))
  have hG₂i : InjOn G₂ (closedBall 0 1) := fun z hz w hw he => by
    have h1 := c₂.injOn (n1 hz) (n1 hw) he
    exact n3.injOn hz hw h1
  have hsph : Continuous sph := isOpenEmbedding_sph.continuous
  obtain ⟨s₁, hs₁c, hs₁l⟩ := exists_inv_of_compact (isCompact_closedBall (0 : ℂ) 1) hsph
    isOpenEmbedding_sph.injective.injOn
  obtain ⟨s₂, hs₂c, hs₂l⟩ := exists_inv_of_compact (isCompact_closedBall (0 : ℂ) 1) continuous_rsph
    rsph_injective.injOn
  let D₁ := sph '' closedBall 0 1
  let D₂ := rsph '' closedBall 0 1
  have hD₁cl : IsClosed D₁ := ((isCompact_closedBall (0 : ℂ) 1).image hsph).isClosed
  have hD₂cl : IsClosed D₂ := ((isCompact_closedBall (0 : ℂ) 1).image continuous_rsph).isClosed
  let T : OnePoint EuclideanPlane → S := fun p => if p ∈ D₁ then g₁ (s₁ p) else G₂ (s₂ p)
  have hT₁ : ∀ z ∈ closedBall (0 : ℂ) 1, T (sph z) = g₁ z := fun z hz => by
    have h1 : sph z ∈ D₁ := mem_image_of_mem sph hz
    simp only [T, h1, ite_true]
    rw [hs₁l hz]
  have hT₂ : ∀ z ∈ closedBall (0 : ℂ) 1, T (rsph z) = G₂ z := fun z hz => by
    by_cases h1 : rsph z ∈ D₁
    · have h2 : rsph z ∈ sph '' sphere 0 1 := by
        rw [← meet_sph]
        exact ⟨h1, z, hz, rfl⟩
      rw [← rsph_sphere] at h2
      obtain ⟨w, hw, he⟩ := h2
      obtain rfl := rsph_injective he
      rw [rsph_of_ne (ne_zero_of_sphere hw), hT₁ _ (hA (inv_mem_sphere hw)), hG₂s w hw]
    · simp only [T, h1, ite_false]
      rw [hs₂l hz]
  have hTc : Continuous T := by
    have hon₁ : ContinuousOn T D₁ := by
      refine (c₁.gc.comp hs₁c ?_).congr ?_
      · rintro _ ⟨z, hz, rfl⟩
        show s₁ (sph z) ∈ closedBall 0 1
        rwa [hs₁l hz]
      · rintro _ ⟨z, hz, rfl⟩
        change T (sph z) = g₁ (s₁ (sph z))
        rw [hT₁ z hz, hs₁l hz]
    have hon₂ : ContinuousOn T D₂ := by
      refine (hG₂c.comp hs₂c ?_).congr ?_
      · rintro _ ⟨z, hz, rfl⟩
        show s₂ (rsph z) ∈ closedBall 0 1
        rwa [hs₂l hz]
      · rintro _ ⟨z, hz, rfl⟩
        change T (rsph z) = G₂ (s₂ (rsph z))
        rw [hT₂ z hz, hs₂l hz]
    have h1 := hon₁.union_of_isClosed hon₂ hD₁cl hD₂cl
    rw [show D₁ ∪ D₂ = univ from cover_sph, continuousOn_univ] at h1
    exact h1
  have hcross : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ w ∈ closedBall (0 : ℂ) 1, g₁ z = G₂ w →
      sph z = rsph w := by
    intro z hz w hw he
    have hmem : g₁ z ∈ Δ₁ ∩ Δ₂ := ⟨c₁.gm hz, by rw [he]; exact c₂.gm (n1 hw)⟩
    rw [hm] at hmem
    have hzs : z ∈ sphere (0 : ℂ) 1 := by
      rw [← c₁.g_sphere] at hmem
      obtain ⟨v, hv, hve⟩ := hmem
      obtain rfl := c₁.injOn (hA hv) hz hve
      exact hv
    have hws : w ∈ sphere (0 : ℂ) 1 := by
      rw [hb, he, ← c₂.g_sphere] at hmem
      obtain ⟨v, hv, hve⟩ := hmem
      have h3 : v = ψ w := c₂.injOn (hA hv) (n1 hw) hve
      have h4 : sphere (0 : ℂ) 1 = ψ '' sphere 0 1 := by
        rw [hψ.image_eq, m.image_eq]
      rw [h3, h4] at hv
      obtain ⟨v', hv', hve'⟩ := hv
      obtain rfl := n3.injOn (hA hv') hw hve'
      exact hv'
    rw [hG₂s w hws] at he
    have h5 := c₁.injOn hz (hA (inv_mem_sphere hws)) he
    rw [rsph_of_ne (ne_zero_of_sphere hws), h5]
  have hcov : ∀ p, (∃ z ∈ closedBall (0 : ℂ) 1, p = sph z) ∨ ∃ z ∈ closedBall (0 : ℂ) 1, p = rsph z
    :=
    fun p => by
      have h1 : p ∈ D₁ ∪ D₂ := by
        rw [show D₁ ∪ D₂ = univ from cover_sph]
        exact mem_univ p
      rcases h1 with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · exact Or.inl ⟨z, hz, rfl⟩
      · exact Or.inr ⟨z, hz, rfl⟩
  refine ⟨T, hTc, ?_, ?_⟩
  · intro p p' he
    rcases hcov p with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩ <;> rcases hcov p' with ⟨w, hw, rfl⟩ | ⟨w, hw,
      rfl⟩
    · rw [hT₁ z hz, hT₁ w hw] at he
      rw [c₁.injOn hz hw he]
    · rw [hT₁ z hz, hT₂ w hw] at he
      exact hcross z hz w hw he
    · rw [hT₂ z hz, hT₁ w hw] at he
      exact (hcross w hw z hz he.symm).symm
    · rw [hT₂ z hz, hT₂ w hw] at he
      rw [hG₂i hz hw he]
  · ext x
    constructor
    · rintro ⟨p, rfl⟩
      rcases hcov p with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [hT₁ z hz]
        exact Or.inl (c₁.gm hz)
      · rw [hT₂ z hz]
        exact Or.inr (c₂.gm (n1 hz))
    · rintro (hx | hx)
      · exact ⟨sph (h₁' x), by rw [hT₁ _ (c₁.hm hx)]; exact c₁.gh hx⟩
      · refine ⟨rsph (χ (h₂' x)), ?_⟩
        rw [hT₂ _ (n2 (c₂.hm hx))]
        change g₂ (ψ (χ (h₂' x))) = x
        rw [n4 (c₂.hm hx)]
        exact c₂.gh hx

/-- The image of a continuous injective sphere map fills a preconnected manifold. -/
theorem isSphereMap_range_eq_univ [T2Space S] [PreconnectedSpace S]
    (hman : ∀ x : S, IsManifoldPoint x) {T : OnePoint EuclideanPlane → S} (hT : Continuous T)
    (hi : Function.Injective T) : range T = univ := by
  have hopen : IsOpen (range T) := by
    refine isOpen_iff_forall_mem_open.mpr ?_
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : OnePoint EuclideanPlane, q ≠ p := by
      by_cases hp : p = ∞
      · exact ⟨sph 0, hp ▸ sph_ne_infty 0⟩
      · exact ⟨∞, Ne.symm hp⟩
    obtain ⟨H, hH⟩ := exists_homeomorph_onePoint q
    let ρ : ℂ → S := fun z => T (H.symm (sph z))
    have hρc : Continuous ρ :=
      hT.comp (H.symm.continuous.comp isOpenEmbedding_sph.continuous)
    have hρi : InjOn ρ univ := fun z _ w _ he =>
      isOpenEmbedding_sph.injective (H.symm.injective (hi he))
    have hO := isOpen_image_of_manifold isOpen_univ hρc.continuousOn hρi fun _ _ => hman _
    refine ⟨_, ?_, hO, ?_⟩
    · rintro _ ⟨z, -, rfl⟩
      exact ⟨_, rfl⟩
    · rcases eq_infty_or_sph (H p) with h | ⟨z, hz⟩
      · exact absurd (H.injective (h.trans hH.symm)) (Ne.symm hq)
      · exact ⟨z, mem_univ _, by
          change T (H.symm (sph z)) = T p
          rw [← hz, H.symm_apply_apply]⟩
  have hcl : IsClosed (range T) := (isCompact_range hT).isClosed
  exact IsClopen.eq_univ ⟨hcl, hopen⟩ (range_nonempty T)

/-- An injective map of the sphere into a surface is onto a connected surface, so the surface is a
sphere. -/
theorem isSphere_of_map [T2Space S] [PreconnectedSpace S]
    (hman : ∀ x : S, IsManifoldPoint x) {T : OnePoint EuclideanPlane → S} (hT : Continuous T)
    (hi : Function.Injective T) : IsSphere S := by
  have hu := isSphereMap_range_eq_univ hman hT hi
  have hb : Function.Bijective T := ⟨hi, range_eq_univ.mp hu⟩
  exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective T hb) hT).symm⟩

/-- Closed discs with the same boundary either coincide or meet exactly along that boundary. -/
theorem eq_or_inter_eq_discBd_of_discBd_eq [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {Δ₁ Δ₂ : Set S}
    (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂) (hb : discBd Δ₁ = discBd Δ₂) :
    Δ₁ = Δ₂ ∨ Δ₁ ∩ Δ₂ = discBd Δ₁ := by
  obtain ⟨h₁', g₁, c₁⟩ := h₁.exists_isChart
  obtain ⟨h₂', g₂, c₂⟩ := h₂.exists_isChart
  obtain ⟨u1, d1⟩ := c₁.union_ball
  obtain ⟨u2, d2⟩ := c₂.union_ball
  have o1 := c₁.isOpen_image_ball hman
  have o2 := c₂.isOpen_image_ball hman
  have p1 : IsPreconnected (g₁ '' ball 0 1) :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image g₁ (c₁.gc.mono ball_subset_closedBall)
  have p2 : IsPreconnected (g₂ '' ball 0 1) :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image g₂ (c₂.gc.mono ball_subset_closedBall)
  have cl1 : IsClosed (g₁ '' ball 0 1 ∪ discBd Δ₁) := by
    rw [u1]
    exact h₁.isCompact.isClosed
  have cl2 : IsClosed (g₂ '' ball 0 1 ∪ discBd Δ₁) := by
    rw [hb, u2]
    exact h₂.isCompact.isClosed
  by_cases hne : (g₁ '' ball 0 1 ∩ g₂ '' ball 0 1).Nonempty
  · have s1 := subset_of_side p1 o2 cl2 d1 hne
    have s2 := subset_of_side p2 o1 cl1 (hb ▸ d2) (by rwa [inter_comm])
    left
    rw [← u1, ← u2, Subset.antisymm s1 s2, hb]
  · right
    refine Subset.antisymm ?_ fun x hx => ⟨discBd_subset _ hx, discBd_subset _ (hb ▸ hx)⟩
    rintro x ⟨hx1, hx2⟩
    rw [← u1] at hx1
    rw [← u2] at hx2
    rcases hx1 with h1 | h1
    · rcases hx2 with h2 | h2
      · exact absurd ⟨x, h1, h2⟩ hne
      · exact hb ▸ h2
    · exact h1

/-- In a connected surface that is not a sphere, a closed disc is determined by its boundary. This
is
the third part of `EpsteinStatement`. -/
theorem eq_of_discBd_eq (hS : IsSurface S) [PreconnectedSpace S] (hns : ¬ IsSphere S) {Δ₁ Δ₂ : Set
  S}
    (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂) (hb : discBd Δ₁ = discBd Δ₂) : Δ₁ = Δ₂ := by
  have : T2Space S := hS.2.1
  rcases eq_or_inter_eq_discBd_of_discBd_eq hS.2.2 h₁ h₂ hb with heq | hinter
  · exact heq
  · obtain ⟨T, hT, hi, -⟩ := exists_sphere_map h₁ h₂ hb hinter
    exact (hns (isSphere_of_map hS.2.2 hT hi)).elim

/-- An `O`-arc in a closed disc inside `Z` is null-homotopic in `Z`. This is the second part of
`EpsteinStatement`. -/
theorem isNullHomotopicOArcIn_of_subset_disc {Z F Δ : Set S} (hF : IsOArc F) (hΔZ : Δ ⊆ Z)
    (hΔ : IsClosedDisc Δ) (hFΔ : F ⊆ Δ) : IsNullHomotopicOArcIn Z F := by
  obtain ⟨φ⟩ := hF
  refine ⟨φ, ?_⟩
  obtain ⟨c, hc, ψ, h1, h2, h3⟩ := hΔ.isSimplyConnectedSet.2
    ⟨fun x => (φ x).1, continuous_subtype_val.comp φ.continuous⟩
    (by
      rintro _ ⟨x, rfl⟩
      exact hFΔ (φ x).2)
  exact ⟨c, hΔZ hc, ψ, fun p => hΔZ (h1 p), h2, h3⟩

end GraphMinor.Surface
