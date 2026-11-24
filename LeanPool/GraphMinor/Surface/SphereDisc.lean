/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscUnion

/-!
# `O`-arcs in a sphere

`sphere_disc : SphereDiscStatement`: an `O`-arc in a sphere is the common boundary of exactly two
closed discs.

Move a point off the arc to infinity, and then use the Schoenflies theorem. This gives a
homeomorphism
of the sphere onto the one-point compactification of the plane that takes the arc to the unit
circle of `ℂ` (`exists_homeomorph_model`). For the unit circle the two discs are the closed unit
disc
and its image under `z ↦ 1 / z`. A closed disc with boundary the unit circle is minus its boundary
an
open set, by invariance of domain in the plane obtained by removing one of its points, so it fills
one of the two sides.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter OnePoint

universe u v

/-- An embedding has a continuous inverse on its range. -/
theorem exists_inv_of_isEmbedding {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] {f : X → Y} (hf : IsEmbedding f) :
    ∃ f' : Y → X, ContinuousOn f' (range f) ∧ ∀ x, f' (f x) = x := by
  classical
  let E := hf.toHomeomorph
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine ⟨fun z => if hz : z ∈ range f then E.symm ⟨z, hz⟩ else x₀, ?_, fun t => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (range f).domRestrict (fun z => if hz : z ∈ range f then E.symm ⟨z, hz⟩ else x₀) =
        fun z : range f => E.symm z := by
      ext z
      simp [Set.domRestrict, z.2]
    rw [this]
    exact E.symm.continuous
  · have hm : f t ∈ range f := ⟨t, rfl⟩
    simp only [hm, dite_true]
    exact E.symm_apply_apply t

/-- The body of `SphereDiscStatement`, for one `O`-arc. -/
def SphereDiscAt (S : Type u) [TopologicalSpace S] (F : Set S) : Prop :=
  ∃ Δ₁ Δ₂ : Set S, Δ₁ ≠ Δ₂ ∧ IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
    discBd Δ₁ = F ∧ discBd Δ₂ = F ∧ Δ₁ ∪ Δ₂ = univ ∧ Δ₁ ∩ Δ₂ = F ∧
    componentsIn (univ \ F) = {Δ₁ \ F, Δ₂ \ F} ∧
    ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F → Δ = Δ₁ ∨ Δ = Δ₂

theorem SphereDiscAt.transport {S : Type u} {S' : Type v} [TopologicalSpace S] [TopologicalSpace S']
    (T : S ≃ₜ S') {F : Set S} (h : SphereDiscAt S F) : SphereDiscAt S' (T '' F) := by
  obtain ⟨Δ₁, Δ₂, ne, d1, d2, b1, b2, cov, meet, comp, uniq⟩ := h
  have hd : ∀ {Δ : Set S}, IsClosedDisc Δ → IsClosedDisc (T '' Δ) ∧ discBd (T '' Δ) = T '' discBd Δ
    :=
    fun h => h.image T.continuous.continuousOn T.symm.continuous.continuousOn
      fun x _ => T.symm_apply_apply x
  have hl : ∀ {X : Set S'}, T '' (T.symm '' X) = X := fun {X} => by
    rw [image_image]
    simp
  have hl' : ∀ {X : Set S}, T.symm '' (T '' X) = X := fun {X} => by
    rw [image_image]
    simp
  have himg : ∀ {X Y : Set S}, T '' (X \ Y) = T '' X \ T '' Y := fun {X Y} => by
    ext y
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨x, h1, rfl⟩, fun ⟨z, hz, he⟩ => h2 (T.injective he ▸ hz)⟩
    · rintro ⟨⟨x, h1, rfl⟩, h2⟩
      exact ⟨x, ⟨h1, fun h' => h2 ⟨x, h', rfl⟩⟩, rfl⟩
  refine ⟨T '' Δ₁, T '' Δ₂, fun e => ne (T.injective.image_injective e), (hd d1).1,
    (hd d2).1, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [(hd d1).2, b1]
  · rw [(hd d2).2, b2]
  · rw [← image_union, cov, image_univ, T.surjective.range_eq]
  · rw [← image_inter T.injective, meet]
  · have hu : univ \ T '' F = T '' (univ \ F) := by
      rw [himg, image_univ, T.surjective.range_eq]
    rw [hu, componentsIn_image T.continuous.continuousOn T.symm.continuous.continuousOn
      (fun x _ => T.symm_apply_apply x), comp, image_pair, himg, himg]
  · intro Δ hΔ hb
    have h1 : IsClosedDisc (T.symm '' Δ) ∧ discBd (T.symm '' Δ) = T.symm '' discBd Δ :=
      hΔ.image T.symm.continuous.continuousOn T.continuous.continuousOn
        fun x _ => T.apply_symm_apply x
    rw [hb, hl'] at h1
    rcases uniq _ h1.1 h1.2 with h2 | h2
    · exact Or.inl (by rw [← h2, hl])
    · exact Or.inr (by rw [← h2, hl])

/-- The plane `ℂ` in the sphere. -/
noncomputable def sph (z : ℂ) : OnePoint EuclideanPlane := ((complexPlane z : EuclideanPlane) : _)

/-- The inversion `z ↦ 1 / z`, with values in the sphere. -/
noncomputable def rsph : ℂ → OnePoint EuclideanPlane := Function.update (fun z => sph z⁻¹) 0 ∞

theorem isOpenEmbedding_sph : IsOpenEmbedding sph :=
  OnePoint.isOpenEmbedding_coe.comp complexPlane.toHomeomorph.isOpenEmbedding

theorem rsph_zero : rsph 0 = ∞ := by simp [rsph]

theorem rsph_of_ne {z : ℂ} (hz : z ≠ 0) : rsph z = sph z⁻¹ := by simp [rsph, hz]

theorem sph_ne_infty (z : ℂ) : sph z ≠ ∞ := OnePoint.coe_ne_infty _

theorem eq_infty_or_sph (p : OnePoint EuclideanPlane) : p = ∞ ∨ ∃ z, p = sph z := by
  induction p using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe y => exact Or.inr ⟨complexPlane.symm y, by simp [sph]⟩

theorem continuous_rsph : Continuous rsph := by
  have hsph : Continuous sph := isOpenEmbedding_sph.continuous
  refine continuous_iff_continuousAt.mpr fun z => ?_
  by_cases hz : z = 0
  · subst hz
    refine continuousAt_update_same.mpr ?_
    have h1 : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_nhdsNE_zero
    have h2 : Tendsto sph (cocompact ℂ) (𝓝 ∞) := by
      have h3 : Tendsto (fun x : EuclideanPlane => (x : OnePoint EuclideanPlane))
          (cocompact EuclideanPlane) (𝓝 ∞) := by
        rw [← coclosedCompact_eq_cocompact, OnePoint.nhds_infty_eq]
        exact tendsto_map.mono_right le_sup_left
      exact h3.comp complexPlane.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    exact h2.comp h1
  · refine (continuousAt_update_of_ne hz).mpr ?_
    exact hsph.continuousAt.comp (continuousAt_inv₀ hz)

theorem rsph_injective : Function.Injective rsph := by
  intro z w h
  by_cases hz : z = 0
  · subst hz
    by_contra hw
    rw [rsph_zero, rsph_of_ne (Ne.symm hw)] at h
    exact sph_ne_infty _ h.symm
  · by_cases hw : w = 0
    · subst hw
      rw [rsph_zero, rsph_of_ne hz] at h
      exact absurd h (sph_ne_infty _)
    · rw [rsph_of_ne hz, rsph_of_ne hw] at h
      exact inv_injective (isOpenEmbedding_sph.injective h)

theorem exists_inv_of_compact {T : Type v} [TopologicalSpace T] [T2Space T] {K : Set ℂ}
    (hK : IsCompact K) {f : ℂ → T} (hf : Continuous f) (hinj : InjOn f K) :
    ∃ f' : T → ℂ, ContinuousOn f' (f '' K) ∧ LeftInvOn f' f K := by
  classical
  by_cases hne : K.Nonempty
  · have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have : Nonempty K := hne.to_subtype
    have hemb : IsEmbedding (fun x : K => f x.1) :=
      ((hf.comp continuous_subtype_val).isClosedEmbedding
        fun x y h => Subtype.ext (hinj x.2 y.2 h)).isEmbedding
    obtain ⟨f', hc, hl⟩ := exists_inv_of_isEmbedding hemb
    have hr : range (fun x : K => f x.1) = f '' K := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hr] at hc
    exact ⟨fun y => (f' y).1, continuous_subtype_val.comp_continuousOn hc,
      fun x hx => congrArg Subtype.val (hl ⟨x, hx⟩)⟩
  · refine ⟨fun _ => 0, continuousOn_const, fun x hx => absurd ⟨x, hx⟩ hne⟩

theorem inv_mem_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : z⁻¹ ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm] at hz ⊢
  rw [norm_inv, hz, inv_one]

theorem ne_zero_of_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : z ≠ 0 := fun h => by
  rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz
  exact zero_ne_one hz

theorem rsph_sphere : rsph '' sphere 0 1 = sph '' sphere 0 1 := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z⁻¹, inv_mem_sphere hz, (rsph_of_ne (ne_zero_of_sphere hz)).symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z⁻¹, inv_mem_sphere hz, ?_⟩
    rw [rsph_of_ne (inv_ne_zero (ne_zero_of_sphere hz)), inv_inv]

theorem cover_sph : sph '' closedBall 0 1 ∪ rsph '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun p => ?_
  rcases eq_infty_or_sph p with rfl | ⟨z, rfl⟩
  · exact Or.inr ⟨0, by simp, rsph_zero⟩
  · rcases le_or_gt ‖z‖ 1 with h | h
    · exact Or.inl ⟨z, mem_closedBall_zero_iff.mpr h, rfl⟩
    · have hz0 : z ≠ 0 := norm_pos_iff.mp (one_pos.trans h)
      refine Or.inr ⟨z⁻¹, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_inv]
        exact inv_le_one_of_one_le₀ h.le
      · rw [rsph_of_ne (inv_ne_zero hz0), inv_inv]

theorem meet_sph : sph '' closedBall 0 1 ∩ rsph '' closedBall 0 1 = sph '' sphere 0 1 := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨⟨z, hz, rfl⟩, w, hw, he⟩
    have hw0 : w ≠ 0 := fun h => sph_ne_infty z (by rw [← he, h, rsph_zero])
    rw [rsph_of_ne hw0] at he
    have h1 : w⁻¹ = z := isOpenEmbedding_sph.injective he
    have h2 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have h3 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
    have h4 : ‖z‖ * ‖w‖ = 1 := by
      rw [← h1, norm_inv]
      exact inv_mul_cancel₀ (norm_pos_iff.mpr hw0).ne'
    have h5 : ‖z‖ = 1 := by nlinarith [norm_nonneg z, norm_nonneg w]
    exact ⟨z, mem_sphere_zero_iff_norm.mpr h5, rfl⟩
  · refine subset_inter (image_mono sphere_subset_closedBall) ?_
    rw [← rsph_sphere]
    exact image_mono sphere_subset_closedBall

private theorem rsph_ball : rsph '' ball 0 1 = (sph '' closedBall 0 1)ᶜ := by
  ext p
  constructor
  · rintro ⟨w, hw, rfl⟩ hm
    have h1 : rsph w ∈ sph '' sphere 0 1 := by
      rw [← meet_sph]
      exact ⟨hm, w, ball_subset_closedBall hw, rfl⟩
    rw [← rsph_sphere] at h1
    obtain ⟨v, hv, he⟩ := h1
    obtain rfl := rsph_injective he
    exact (mem_ball_zero_iff.mp hw).ne (mem_sphere_zero_iff_norm.mp hv)
  · intro hp
    have h1 : p ∈ sph '' closedBall 0 1 ∪ rsph '' closedBall 0 1 := by
      rw [cover_sph]
      exact mem_univ _
    obtain ⟨w, hw, rfl⟩ := h1.resolve_left hp
    refine ⟨w, ?_, rfl⟩
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hw) with h | h
    · exact mem_ball_zero_iff.mpr h
    · exfalso
      refine hp (image_mono sphere_subset_closedBall ?_)
      rw [← rsph_sphere]
      exact mem_image_of_mem _ (mem_sphere_zero_iff_norm.mpr h)

private theorem disc_of_embedding {f : ℂ → OnePoint EuclideanPlane} (hf : Continuous f)
    (hinj : Function.Injective f) :
    IsClosedDisc (f '' closedBall 0 1) ∧ discBd (f '' closedBall 0 1) = f '' sphere 0 1 := by
  obtain ⟨f', hc, hl⟩ := exists_inv_of_compact (isCompact_closedBall (0 : ℂ) 1) hf hinj.injOn
  have := isClosedDisc_closedBall.1.image hf.continuousOn hc hl
  rwa [isClosedDisc_closedBall.2] at this

/-- A closed disc of the sphere minus its boundary is open. Remove one more point of the disc and
apply invariance of domain in the plane that remains. -/
private theorem isOpen_image_ball {D : Set (OnePoint EuclideanPlane)} {h : OnePoint EuclideanPlane
  → ℂ}
    {g : ℂ → OnePoint EuclideanPlane} (c : IsChart D h g) : IsOpen (g '' ball 0 1) := by
  have hhalf : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    norm_num
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  refine isOpen_iff_forall_mem_open.mpr ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨q, hq, hqv⟩ : ∃ q ∈ ball (0 : ℂ) 1, q ≠ v := by
    by_cases hv0 : v = 0
    · exact ⟨1 / 2, hhalf, by rw [hv0]; norm_num⟩
    · exact ⟨0, h0, Ne.symm hv0⟩
  obtain ⟨H, hH⟩ := exists_homeomorph_onePoint (g q)
  obtain ⟨s', hs', hl⟩ := exists_inv_of_isEmbedding isOpenEmbedding_sph.isEmbedding
  let U : Set ℂ := ball 0 1 \ {q}
  have hUo : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hUb : U ⊆ closedBall 0 1 := sdiff_subset.trans ball_subset_closedBall
  have hrange : ∀ z ∈ U, H (g z) ∈ range sph := fun z hz => by
    rcases eq_infty_or_sph (H (g z)) with h' | ⟨w, hw⟩
    · exfalso
      have h1 : g z = g q := H.injective (h'.trans hH.symm)
      exact hz.2 (c.injOn (hUb hz) (ball_subset_closedBall hq) h1)
    · exact ⟨w, hw.symm⟩
  let j : ℂ → ℂ := fun z => s' (H (g z))
  have hjc : ContinuousOn j U :=
    hs'.comp (H.continuous.comp_continuousOn (c.gc.mono hUb)) hrange
  have hsj : ∀ z ∈ U, sph (j z) = H (g z) := fun z hz => by
    obtain ⟨w, hw⟩ := hrange z hz
    change sph (s' (H (g z))) = H (g z)
    rw [← hw, hl]
  have hji : InjOn j U := fun z hz w hw he => by
    have h1 : H (g z) = H (g w) := by rw [← hsj z hz, ← hsj w hw, he]
    exact c.injOn (hUb hz) (hUb hw) (H.injective h1)
  have hopen := isOpen_image_of_injOn hUo hjc hji
  have hO : IsOpen (sph '' (j '' U)) := isOpenEmbedding_sph.isOpenMap _ hopen
  have heq : sph '' (j '' U) = H '' (g '' U) := by
    rw [image_image, image_image]
    exact image_congr hsj
  refine ⟨g '' U, image_mono sdiff_subset, ?_, ⟨v, ⟨hv, Ne.symm hqv⟩, rfl⟩⟩
  have hO' : IsOpen (H '' (g '' U)) := heq ▸ hO
  exact (H.isOpen_image).mp hO'

private theorem sphereDiscAt_model : SphereDiscAt (OnePoint EuclideanPlane) (sph '' sphere 0 1)
  := by
  have hsphc : Continuous sph := isOpenEmbedding_sph.continuous
  obtain ⟨d1, b1⟩ := disc_of_embedding hsphc isOpenEmbedding_sph.injective
  obtain ⟨d2, b2⟩ := disc_of_embedding continuous_rsph rsph_injective
  rw [rsph_sphere] at b2
  set F₀ := sph '' sphere 0 1 with hF₀
  have hd1 : sph '' closedBall 0 1 \ F₀ = sph '' ball 0 1 := by
    rw [hF₀, ← ball_union_sphere, image_union]
    ext p
    constructor
    · rintro ⟨h | h, hn⟩
      · exact h
      · exact absurd h hn
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, he⟩ := h
      obtain rfl := isOpenEmbedding_sph.injective he
      exact (mem_ball_zero_iff.mp hw).ne (mem_sphere_zero_iff_norm.mp hz)
  have hd2 : rsph '' closedBall 0 1 \ F₀ = rsph '' ball 0 1 := by
    rw [hF₀, ← rsph_sphere, ← ball_union_sphere, image_union]
    ext p
    constructor
    · rintro ⟨h | h, hn⟩
      · exact h
      · exact absurd h hn
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, he⟩ := h
      obtain rfl := rsph_injective he
      exact (mem_ball_zero_iff.mp hw).ne (mem_sphere_zero_iff_norm.mp hz)
  have hU₁ : IsOpen (sph '' ball 0 1) := isOpenEmbedding_sph.isOpenMap _ isOpen_ball
  have hcl : IsClosed (sph '' closedBall 0 1) :=
    ((isCompact_closedBall (0 : ℂ) 1).image hsphc).isClosed
  have hcl₂ : IsClosed (rsph '' closedBall 0 1) :=
    ((isCompact_closedBall (0 : ℂ) 1).image continuous_rsph).isClosed
  have hU₂ : IsOpen (rsph '' ball 0 1) := by
    rw [rsph_ball]
    exact hcl.isOpen_compl
  have hconn : ∀ {f : ℂ → OnePoint EuclideanPlane}, Continuous f → IsPreconnected (f '' ball 0 1) :=
    fun hf => (convex_ball (0 : ℂ) 1).isPreconnected.image _ hf.continuousOn
  have hdisj : Disjoint (sph '' ball 0 1) (rsph '' ball 0 1) := by
    rw [rsph_ball]
    exact Set.disjoint_left.mpr fun p h1 h2 => h2 (image_mono ball_subset_closedBall h1)
  have hne : ∀ f : ℂ → OnePoint EuclideanPlane, (f '' ball 0 1).Nonempty := fun f =>
    ⟨f 0, 0, by simp, rfl⟩
  have huniv : univ \ F₀ = sph '' ball 0 1 ∪ rsph '' ball 0 1 := by
    rw [← hd1, ← hd2, ← union_sdiff_distrib, cover_sph]
  have hcomp := componentsIn_eq_pair hU₁ hU₂ (hconn hsphc) (hconn continuous_rsph) (hne _) (hne _)
    hdisj huniv
  refine ⟨_, _, ?_, d1, d2, b1, b2, cover_sph, meet_sph, ?_, ?_⟩
  · intro he
    have h1 := congrArg (fun X => X \ F₀) he
    simp only [hd1, hd2] at h1
    obtain ⟨p, hp⟩ := hne sph
    exact Set.disjoint_left.mp hdisj hp (h1 ▸ hp)
  · rw [hd1, hd2]
    exact hcomp
  · intro Δ hΔ hb
    obtain ⟨h, g, c⟩ := hΔ.exists_isChart
    have hW := isOpen_image_ball c
    have hgs : g '' sphere 0 1 = F₀ := by rw [c.g_sphere, hb]
    have hun : g '' ball 0 1 ∪ F₀ = Δ := by
      rw [← hgs, ← image_union, ball_union_sphere, c.g_closedBall]
    have hclΔ : IsClosed (g '' ball 0 1 ∪ F₀) := hun ▸ c.isCompact.isClosed
    have hWF : Disjoint (g '' ball 0 1) F₀ := by
      rw [← hgs, Set.disjoint_iff_inter_eq_empty, ← c.g_inter ball_subset_closedBall
        sphere_subset_closedBall]
      have : ball (0 : ℂ) 1 ∩ sphere 0 1 = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_ball_zero_iff, mem_sphere_zero_iff_norm, mem_empty_iff_false,
          iff_false, not_and]
        exact fun h1 h2 => h1.ne h2
      rw [this, image_empty]
    have hsub : g '' ball 0 1 ⊆ sph '' ball 0 1 ∪ rsph '' ball 0 1 := by
      rw [← huniv]
      exact fun p hp => ⟨mem_univ _, Set.disjoint_left.mp hWF hp⟩
    have hWc : IsPreconnected (g '' ball 0 1) :=
      (convex_ball (0 : ℂ) 1).isPreconnected.image g (c.gc.mono ball_subset_closedBall)
    have hF₁ : Disjoint (sph '' ball 0 1) F₀ := by
      rw [← hd1]
      exact disjoint_sdiff_left
    have hF₂ : Disjoint (rsph '' ball 0 1) F₀ := by
      rw [← hd2]
      exact disjoint_sdiff_left
    have hWne : (g '' ball 0 1).Nonempty := hne g
    have hfin : ∀ {C : Set (OnePoint EuclideanPlane)}, IsPreconnected C → Disjoint C F₀ →
        g '' ball 0 1 ⊆ C → C ∪ F₀ = Δ := by
      intro C hCc hCF hin
      have hsubC := subset_of_side hCc hW hclΔ hCF (hWne.mono (subset_inter hin Subset.rfl))
      rw [← hun, Subset.antisymm hsubC hin]
    rcases (isPreconnected_iff_subset_of_disjoint.mp hWc) _ _ hU₁ hU₂ hsub
      (by rw [hdisj.inter_eq]; simp) with h1 | h1
    · left
      rw [← hfin (hconn hsphc) hF₁ h1, ← hd1, sdiff_union_of_subset]
      rw [hF₀]
      exact image_mono sphere_subset_closedBall
    · right
      rw [← hfin (hconn continuous_rsph) hF₂ h1, ← hd2, sdiff_union_of_subset]
      rw [hF₀, ← rsph_sphere]
      exact image_mono sphere_subset_closedBall

/-- A sphere can be mapped to the model so that a given `O`-arc goes to the unit circle. -/
theorem exists_homeomorph_model {S : Type u} [TopologicalSpace S] (hS : IsSphere S) {F : Set S}
    (hF : IsOArc F) :
    ∃ T : S ≃ₜ OnePoint EuclideanPlane, T '' F = sph '' sphere 0 1 := by
  obtain ⟨e⟩ := hS
  obtain ⟨φ⟩ := id hF
  obtain ⟨x, hx⟩ := exists_notMem_oArc (F := e '' F) ⟨φ.trans (e.image F)⟩
  obtain ⟨h, hh⟩ := exists_homeomorph_onePoint x
  let E : S ≃ₜ OnePoint EuclideanPlane := e.trans h
  have hinf : (∞ : OnePoint EuclideanPlane) ∉ E '' F := by
    rintro ⟨y, hy, hyE⟩
    have : e y = x := h.injective (hyE.trans hh.symm)
    exact hx ⟨y, hy, this⟩
  have hsub : E '' F ⊆ range sph := fun p hp => by
    rcases eq_infty_or_sph p with rfl | ⟨z, rfl⟩
    · exact absurd hp hinf
    · exact ⟨z, rfl⟩
  have himg : sph '' (sph ⁻¹' (E '' F)) = E '' F := image_preimage_eq_of_subset hsub
  obtain ⟨s', hs', hl⟩ := exists_inv_of_isEmbedding isOpenEmbedding_sph.isEmbedding
  have hG : IsOArc (sph ⁻¹' (E '' F)) := by
    have h1 := isOpenEmbedding_sph.isEmbedding.homeomorphImage (sph ⁻¹' (E '' F))
    have h2 : (E '' F : Set _) ≃ₜ (sph '' (sph ⁻¹' (E '' F)) : Set _) :=
      Homeomorph.setCongr himg.symm
    exact ⟨(φ.trans (E.image F)).trans (h2.trans h1.symm)⟩
  obtain ⟨φ₀⟩ := oArc_sphere
  obtain ⟨φ'⟩ := id hG
  obtain ⟨h₀, k₀, m, -⟩ := exists_bdMatch (φ₀.symm.trans φ')
  obtain ⟨G, hGe⟩ := exists_homeomorph_of_bdMatch hG m
  let g : EuclideanPlane ≃ₜ EuclideanPlane :=
    complexPlane.symm.toHomeomorph.trans (G.trans complexPlane.toHomeomorph)
  let C : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane := g.onePointCongr
  have hC : ∀ z, C (sph z) = sph (G z) := fun z => by
    change ((g (complexPlane z) : EuclideanPlane) : OnePoint EuclideanPlane) = sph (G z)
    simp [g, sph]
  refine ⟨E.trans C.symm, ?_⟩
  have h3 : C '' (sph '' sphere 0 1) = E '' F := by
    rw [image_image]
    simp only [hC]
    rw [← image_image (g := sph) (f := G), hGe.image_eq, m.image_eq, himg]
  have h4 : (E.trans C.symm) '' F = C.symm '' (E '' F) := by
    rw [image_image]
    rfl
  rw [h4, ← h3, image_image]
  simp

/-- **An `O`-arc in a sphere is the common boundary of exactly two closed discs.** See the module
docstring for the route. -/
theorem sphere_disc : SphereDiscStatement.{u} := by
  intro S _ hS F hF
  obtain ⟨T, hT⟩ := exists_homeomorph_model hS hF
  have h := sphereDiscAt_model.transport T.symm
  have h1 : T.symm '' (sph '' sphere 0 1) = F := by
    rw [← hT, image_image]
    simp
  rw [h1] at h
  exact h

end GraphMinor.Surface
