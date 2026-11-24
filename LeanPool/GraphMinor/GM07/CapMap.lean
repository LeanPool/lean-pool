/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section5
public import LeanPool.GraphMinor.GM07.Section8
public import LeanPool.GraphMinor.GM07.Taper

/-!
# Maps between capped surfaces

A homeomorphism of the boundaries of two closed discs extends to the discs, radially
(`exists_radial`). So a map of surfaces
that is one to one between two cuffs extends to the surfaces with discs pasted on these cuffs
(`exists_cap_map`). In particular
two ways of pasting a disc on a cuff are the same (`IsPlanarInCappedCuff.of_cap`).

`isPlanar_of_homotopy` says when a solid set is planar: each `O`-arc of it is homotopic into a
closed disc. With this we compare a
set with its image under a map homotopic to the identity, without moving the discs.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u v

local notation "𝕀" => unitInterval

variable {Y Y' : Type u} {S S' : Type v} [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace S] [TopologicalSpace S']

/-- The radial extension of a map of the circle to the closed ball. -/
theorem exists_radial {b : ℂ → ℂ} (hb : ContinuousOn b (sphere 0 1)) (hm : MapsTo b (sphere 0 1)
  (sphere 0 1))
    (hi : InjOn b (sphere 0 1)) (hs : SurjOn b (sphere 0 1) (sphere 0 1)) :
    ∃ G : ℂ → ℂ, ContinuousOn G (closedBall 0 1) ∧ (∀ z ∈ sphere (0 : ℂ) 1, G z = b z) ∧ InjOn G
      (closedBall 0 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ‖G z‖ = ‖z‖) ∧ SurjOn G (closedBall 0 1) (closedBall 0 1) := by
  classical
  let u : ℂ → ℂ := fun z => z / (‖z‖ : ℂ)
  have hus : ∀ z : ℂ, z ≠ 0 → u z ∈ sphere (0 : ℂ) 1 := fun z hz => by
    rw [mem_sphere_zero_iff_norm]
    simp [u, hz]
  let G : ℂ → ℂ := fun z => (‖z‖ : ℂ) * b (u z)
  have hn : ∀ z : ℂ, ‖G z‖ = ‖z‖ := fun z => by
    by_cases hz : z = 0
    · simp [G, hz]
    · have h1 := mem_sphere_zero_iff_norm.mp (hm (hus z hz))
      simp [G, h1]
  have hzu : ∀ z : ℂ, z ≠ 0 → (‖z‖ : ℂ) * u z = z := fun z hz => by
    have : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
    simp only [u]
    field_simp
  refine ⟨G, ?_, ?_, ?_, fun z _ => hn z, ?_⟩
  · intro z hz
    by_cases h0 : z = 0
    · subst h0
      have hG0 : G 0 = 0 := by simp [G]
      apply ContinuousAt.continuousWithinAt
      rw [ContinuousAt, hG0, tendsto_zero_iff_norm_tendsto_zero]
      simp only [hn]
      exact tendsto_norm_zero
    · have h3 : ContinuousOn (fun z => b (u z)) {z | z ≠ 0} := by
        refine hb.comp ?_ fun x hx => hus x hx
        exact fun x hx => (ContinuousAt.continuousWithinAt
          (continuousAt_id.div (Complex.continuous_ofReal.continuousAt.comp
            continuous_norm.continuousAt) (by simpa using hx)))
      have h4 : ContinuousAt (fun z => b (u z)) z := h3.continuousAt (isOpen_ne.mem_nhds h0)
      exact ((Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt).mul
        h4).continuousWithinAt
  · intro z hz
    have h1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have h2 : u z = z := by simp [u, h1]
    simp [G, h1, h2]
  · intro z _ w _ he
    have h1 : ‖z‖ = ‖w‖ := by rw [← hn z, ← hn w, he]
    by_cases hz : z = 0
    · subst hz
      rw [norm_zero] at h1
      exact (norm_eq_zero.mp h1.symm).symm
    have hw : w ≠ 0 := fun h => hz (norm_eq_zero.mp (by rw [h1, h, norm_zero]))
    have h2 : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
    have h3 : b (u z) = b (u w) := by
      simp only [G, h1] at he
      exact mul_left_cancel₀ (by rw [← h1]; exact h2) he
    have h4 := hi (hus z hz) (hus w hw) h3
    rw [← hzu z hz, ← hzu w hw, h4, h1]
  · intro w hw
    have hw' : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
    by_cases h0 : w = 0
    · exact ⟨0, by simp, by simp [G, h0]⟩
    obtain ⟨z, hz, he⟩ := hs (hus w h0)
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz1
    refine ⟨(‖w‖ : ℂ) * z, mem_closedBall_zero_iff.mpr ?_, ?_⟩
    · simpa [hz1] using hw'
    · have hne : (‖w‖ : ℂ) ≠ 0 := by simpa using h0
      have h1 : ‖(‖w‖ : ℂ) * z‖ = ‖w‖ := by simp [hz1]
      have h2 : u ((‖w‖ : ℂ) * z) = z := by
        simp only [u, h1]
        field_simp
      simp only [G, h1, h2, he]
      exact hzu w h0

/-- A map of surfaces that is one to one from a cuff onto a cuff extends to the surfaces with discs
on these cuffs. It takes the
disc onto the disc, one to one, and the inside to the inside. -/
theorem exists_cap_map {C : Set Y} {C₀ : Set S} {jY : Y → Y'} {DY : Set Y'} {j : S
  → S'} {D : Set S'}
    [CompactSpace Y] [T2Space Y']
    (hY : IsCappedCuff C Y' jY DY) (hS : IsCappedCuff C₀ S' j D) {φ : Y → S} (hφ : Continuous φ)
      (hb : BijOn φ C C₀)
    (hne : C.Nonempty) :
    ∃ Ψ : Y' → S', Continuous Ψ ∧ (∀ y, Ψ (jY y) = j (φ y)) ∧ MapsTo Ψ DY D ∧ InjOn Ψ DY
      ∧ SurjOn Ψ DY D ∧
      MapsTo Ψ (discInt DY) (discInt D) := by
  classical
  obtain ⟨h₁, g₁, c₁⟩ := hY.isClosedDisc.exists_isChart
  obtain ⟨h₂, g₂, c₂⟩ := hS.isClosedDisc.exists_isChart
  have : Nonempty Y := hne.nonempty
  let J : Y' → Y := Function.invFun jY
  have hJ : ∀ y, J (jY y) = y := Function.leftInverse_invFun hY.isEmbedding.injective
  have hemb : IsClosedEmbedding jY := hY.isEmbedding.continuous.isClosedEmbedding
    hY.isEmbedding.injective
  have hJc : ContinuousOn J (range jY) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (range jY).domRestrict J = hY.isEmbedding.toHomeomorph.symm := by
      funext y
      obtain ⟨y, x, rfl⟩ := y
      change J (jY x) = _
      rw [hJ]
      exact (hY.isEmbedding.toHomeomorph.symm_apply_apply x).symm
    rw [this]
    exact Homeomorph.continuous _
  have hbdY : discBd DY = jY '' C := hY.discBd_eq
  have hbdS : discBd D = j '' C₀ := hS.discBd_eq
  let P : Y' → S' := fun x => j (φ (J x))
  have hPc : ContinuousOn P (range jY) := hS.isEmbedding.continuous.comp_continuousOn
    (hφ.comp_continuousOn hJc)
  have hPb : ∀ y ∈ C, P (jY y) ∈ discBd D := fun y hy => by
    change j (φ (J (jY y))) ∈ _
    rw [hJ, hbdS]
    exact mem_image_of_mem j (hb.mapsTo hy)
  have hgs : ∀ z ∈ sphere (0 : ℂ) 1, g₁ z ∈ jY '' C := fun z hz => hbdY ▸ c₁.g_sphere ▸
    mem_image_of_mem g₁ hz
  let f : ℂ → ℂ := fun z => h₂ (P (g₁ z))
  have hfc : ContinuousOn f (sphere 0 1) := by
    refine c₂.hc.comp (hPc.comp (c₁.gc.mono sphere_subset_closedBall) ?_) ?_
    · intro z hz
      obtain ⟨y, -, he⟩ := hgs z hz
      exact ⟨y, he⟩
    · intro z hz
      obtain ⟨y, hy, he⟩ := hgs z hz
      change P (g₁ z) ∈ D
      rw [← he]
      exact Surface.discBd_subset _ (hPb y hy)
  have hfm : MapsTo f (sphere 0 1) (sphere 0 1) := fun z hz => by
    obtain ⟨y, hy, he⟩ := hgs z hz
    change h₂ (P (g₁ z)) ∈ _
    rw [← he, ← c₂.bd]
    exact mem_image_of_mem h₂ (hPb y hy)
  have hP2 : ∀ y ∈ C, g₂ (h₂ (P (jY y))) = P (jY y) := fun y hy => c₂.gh (Surface.discBd_subset _
    (hPb y hy))
  have hfi : InjOn f (sphere 0 1) := fun z hz w hw he => by
    obtain ⟨y, hy, hey⟩ := hgs z hz
    obtain ⟨y', hy', hey'⟩ := hgs w hw
    change h₂ (P (g₁ z)) = h₂ (P (g₁ w)) at he
    rw [← hey, ← hey'] at he
    have h1 := congrArg g₂ he
    rw [hP2 y hy, hP2 y' hy'] at h1
    change j (φ (J (jY y))) = j (φ (J (jY y'))) at h1
    rw [hJ, hJ] at h1
    have h2 := hb.injOn hy hy' (hS.isEmbedding.injective h1)
    have h3 : g₁ z = g₁ w := by rw [← hey, ← hey', h2]
    rw [← c₁.hg (sphere_subset_closedBall hz), ← c₁.hg (sphere_subset_closedBall hw), h3]
  have hfs : SurjOn f (sphere 0 1) (sphere 0 1) := fun w hw => by
    have h1 : g₂ w ∈ discBd D := c₂.g_sphere ▸ mem_image_of_mem g₂ hw
    rw [hbdS] at h1
    obtain ⟨s, hs, he⟩ := h1
    obtain ⟨y, hy, rfl⟩ := hb.surjOn hs
    have h2 : jY y ∈ discBd DY := hbdY ▸ mem_image_of_mem jY hy
    rw [← c₁.g_sphere] at h2
    obtain ⟨z, hz, hez⟩ := h2
    refine ⟨z, hz, ?_⟩
    change h₂ (P (g₁ z)) = w
    rw [hez]
    change h₂ (j (φ (J (jY y)))) = w
    rw [hJ, he, c₂.hg (sphere_subset_closedBall hw)]
  obtain ⟨G, hGc, hGs, hGi, hGn, hGo⟩ := exists_radial hfc hfm hfi hfs
  have hGm : ∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ closedBall (0 : ℂ) 1 := fun z hz =>
    mem_closedBall_zero_iff.mpr (by rw [hGn z hz]; exact mem_closedBall_zero_iff.mp hz)
  let Ψ : Y' → S' := fun x => if x ∈ DY then g₂ (G (h₁ x)) else P x
  have hcov : DY ∪ range jY = univ := by rw [union_comm]; exact hY.union_eq
  have hmeet : range jY ∩ DY = jY '' C := hY.inter_eq
  have h1c : ContinuousOn Ψ DY := by
    have h3 : ContinuousOn (fun x => g₂ (G (h₁ x))) DY := c₂.gc.comp (hGc.comp c₁.hc c₁.hm) fun x
      hx => hGm _ (c₁.hm hx)
    exact h3.congr fun x hx => ite_eq_left hx
  have hagree : ∀ y ∈ C, g₂ (G (h₁ (jY y))) = P (jY y) := fun y hy => by
    have h3 : jY y ∈ discBd DY := hbdY ▸ mem_image_of_mem jY hy
    have h4 : h₁ (jY y) ∈ sphere (0 : ℂ) 1 := c₁.bd ▸ mem_image_of_mem h₁ h3
    rw [hGs _ h4]
    change g₂ (h₂ (P (g₁ (h₁ (jY y))))) = _
    rw [c₁.gh (hY.isClosedDisc.isCompact.isClosed |> fun _ => Surface.discBd_subset _ h3), hP2 y hy]
  have hΨj : ∀ y, Ψ (jY y) = j (φ y) := fun y => by
    change (if jY y ∈ DY then _ else _) = _
    split_ifs with h3
    · have h4 : jY y ∈ range jY ∩ DY := ⟨mem_range_self y, h3⟩
      rw [hmeet] at h4
      obtain ⟨y', hy', he⟩ := h4
      rw [hemb.injective he] at hy'
      rw [hagree y hy']
      change j (φ (J (jY y))) = _
      rw [hJ]
    · change j (φ (J (jY y))) = _
      rw [hJ]
  have h2c : ContinuousOn Ψ (range jY) := by
    refine hPc.congr ?_
    rintro _ ⟨y, rfl⟩
    rw [hΨj]
    change _ = j (φ (J (jY y)))
    rw [hJ]
  have hΨd : ∀ x ∈ DY, Ψ x = g₂ (G (h₁ x)) := fun x hx => ite_eq_left hx
  refine ⟨Ψ, ?_, hΨj, ?_, ?_, ?_, ?_⟩
  · rw [← continuousOn_univ, ← hcov]
    exact h1c.union_of_isClosed h2c hY.isClosedDisc.isCompact.isClosed hemb.isClosed_range
  · intro x hx
    rw [hΨd x hx]
    exact c₂.gm (hGm _ (c₁.hm hx))
  · intro x hx x' hx' he
    rw [hΨd x hx, hΨd x' hx'] at he
    have h3 := congrArg h₂ he
    rw [c₂.hg (hGm _ (c₁.hm hx)), c₂.hg (hGm _ (c₁.hm hx'))] at h3
    have h4 := hGi (c₁.hm hx) (c₁.hm hx') h3
    rw [← c₁.gh hx, ← c₁.gh hx', h4]
  · intro w hw
    obtain ⟨z, hz, he⟩ := hGo (c₂.hm hw)
    refine ⟨g₁ z, c₁.gm hz, ?_⟩
    rw [hΨd _ (c₁.gm hz), c₁.hg hz, he, c₂.gh hw]
  · rintro x ⟨hx, hxb⟩
    rw [hΨd x hx]
    have h3 : ‖h₁ x‖ < 1 := by
      refine lt_of_le_of_ne (mem_closedBall_zero_iff.mp (c₁.hm hx)) fun he => hxb ?_
      rw [← c₁.g_sphere]
      exact ⟨h₁ x, mem_sphere_zero_iff_norm.mpr he, c₁.gh hx⟩
    refine ⟨c₂.gm (hGm _ (c₁.hm hx)), fun hb' => ?_⟩
    have h4 : h₂ (g₂ (G (h₁ x))) ∈ sphere (0 : ℂ) 1 := c₂.bd ▸ mem_image_of_mem h₂ hb'
    rw [c₂.hg (hGm _ (c₁.hm hx)), mem_sphere_zero_iff_norm, hGn _ (c₁.hm hx)] at h4
    exact h3.ne h4

/-- If a set is planar in one surface with a disc pasted on `C`, then it is planar in all of them.
-/
theorem isPlanarInCappedCuff_of_cap (hY : IsSurface Y) {C X : Set Y} {T : Type u} [TopologicalSpace
  T] {j : Y → T} {D : Set T}
    (hc : IsCappedCuff C T j D) (hX : IsPlanar (j '' X)) : IsPlanarInCappedCuff C X := by
  have : CompactSpace Y := hY.1
  have : T2Space T := hc.isSurface.2.1
  have hne : C.Nonempty := by
    obtain ⟨y, hy, rfl⟩ := hc.cuff
    exact ⟨y, mem_connectedComponentIn hy⟩
  refine ⟨hc.cuff, ⟨T, inferInstance, j, D, hc, hX⟩, fun T₂ _ j₂ D₂ hc₂ => ?_⟩
  have : T2Space T₂ := hc₂.isSurface.2.1
  obtain ⟨Ψ, hΨc, hΨj, -, hΨi, -, hΨo⟩ := exists_cap_map hc hc₂ continuous_id (bijOn_id C) hne
  have hman : ∀ x : T, IsManifoldPoint x := hc.isSurface.2.2
  have hcov : ∀ x, x ∈ range j ∨ x ∈ discInt D := fun x => by
    rcases (hc.union_eq.ge (mem_univ x)) with h | h
    · exact .inl h
    · by_cases hb : x ∈ discBd D
      · rw [hc.discBd_eq] at hb
        obtain ⟨y, -, rfl⟩ := hb
        exact .inl (mem_range_self y)
      · exact .inr ⟨h, hb⟩
  have hdis : ∀ y, ∀ x ∈ discInt D, j₂ y ≠ Ψ x := fun y x hx he => by
    have h1 := hΨo hx
    rw [← he] at h1
    have h2 : j₂ y ∈ range j₂ ∩ D₂ := ⟨mem_range_self y, h1.1⟩
    rw [hc₂.inter_eq, ← hc₂.discBd_eq] at h2
    exact h1.2 h2
  have hinj : Function.Injective Ψ := fun x x' he => by
    rcases hcov x with ⟨y, rfl⟩ | hx <;> rcases hcov x' with ⟨y', rfl⟩ | hx'
    · rw [hΨj, hΨj] at he
      exact congrArg j (hc₂.isEmbedding.injective he)
    · rw [hΨj] at he
      exact (hdis y x' hx' he).elim
    · rw [hΨj] at he
      exact (hdis y' x hx he.symm).elim
    · exact hΨi hx.1 hx'.1 he
  obtain ⟨Δ, hΔ, hsub⟩ := hX
  refine ⟨Ψ '' Δ, isClosedDisc_image_of_injective hΨc hinj hΔ, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 : j y ∈ Δ := hsub (mem_image_of_mem j hy)
  exact ⟨j y, h1, hΨj y⟩

/-- `O`-arc images: a one to one continuous map carries a parametrization along. -/
theorem exists_param_image {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [T2Space B] {F : Set A}
    (f : Circle ≃ₜ F) {g : A → B} (hg : Continuous g) (hi : InjOn g F) :
    ∃ e : Circle ≃ₜ (g '' F), ∀ w, (e w).1 = g (f w).1 := by
  let k : Circle → g '' F := fun w => ⟨g (f w).1, (f w).1, (f w).2, rfl⟩
  have hkc : Continuous k := Continuous.subtype_mk (hg.comp (continuous_subtype_val.comp
    f.continuous)) _
  have hkb : Function.Bijective k := by
    constructor
    · intro w w' he
      have h1 : g (f w).1 = g (f w').1 := congrArg Subtype.val he
      exact f.injective (Subtype.ext (hi (f w).2 (f w').2 h1))
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨f.symm ⟨x, hx⟩, Subtype.ext (by simp [k])⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective k hkb) hkc, fun w => rfl⟩

/-- A curve homotopic into a closed disc is null-homotopic. -/
theorem null_of_homotopy_into_disc {T : Type v} [TopologicalSpace T] {H : 𝕀 × Y → T}
  (hH : Continuous H) {f : Circle → Y}
    (hf : Continuous f) {Δ : Set T} (hΔ : IsClosedDisc Δ) (h1 : ∀ w, H (1, f w) ∈ Δ) :
    ClosedCurveIsNullHomotopicIn univ ⟨fun w => H (0, f w), hH.comp (continuous_const.prodMk hf)⟩
      := by
  let b : C(Circle, T) := ⟨fun w => H (1, f w), hH.comp (continuous_const.prodMk hf)⟩
  have hn : ClosedCurveIsNullHomotopicIn Δ b := hΔ.isSimplyConnectedSet.2 b (by
    rintro _ ⟨w, rfl⟩
    exact h1 w)
  refine null_of_homotopic (subset_univ Δ) ?_ hn
  exact ⟨⟨fun q => H (q.2, f q.1), hH.comp ((continuous_snd).prodMk (hf.comp continuous_fst))⟩,
    fun _ => mem_univ _, fun _ => rfl, fun _ => rfl⟩

/-- A solid set is planar if the image of each of its `O`-arcs is null-homotopic. -/
theorem isPlanar_of_null {T : Type u} [TopologicalSpace T] [CompactSpace Y] [T2Space Y]
  (hT : IsSurface T) [ConnectedSpace T]
    {j : Y → T} (hj : IsEmbedding j) {X : Set Y} (hX : IsSolid X) (hne : ¬ IsSphere T
      ∨ j '' X ≠ univ)
    (h1 : ∀ F, IsOArc F → F ⊆ X → ∀ f : Circle → Y, Continuous f → range f = F → ∀ hc : Continuous
      (fun w => j (f w)),
      ClosedCurveIsNullHomotopicIn univ ⟨fun w => j (f w), hc⟩) : IsPlanar (j '' X) := by
  have : T2Space T := hT.2.1
  have hcl : IsClosedEmbedding j := hj.continuous.isClosedEmbedding hj.injective
  rw [theorem_5_1_of_not_isSphere hT hne (isSolid_image_of_isClosedEmbedding hcl hX)]
  intro F hF hFX
  have hsub : F ⊆ range j := hFX.trans (image_subset_range _ _)
  have hF₀ : IsOArc (j ⁻¹' F) := IsOArc.pull_of_embedding hj hF hsub
  have hF₀X : j ⁻¹' F ⊆ X := fun y hy => by
    obtain ⟨y', hy', he⟩ := hFX hy
    rwa [← hj.injective he]
  obtain ⟨f⟩ := id hF₀
  obtain ⟨e, he⟩ := exists_param_image f hj.continuous hj.injective.injOn
  have himg : j '' (j ⁻¹' F) = F := image_preimage_eq_of_subset hsub
  rw [isPlanar_iff_isNullHomotopicOArc_of_isOArc hT hF, ← himg]
  refine ⟨e, ?_⟩
  have hfc : Continuous fun w => (f w).1 := continuous_subtype_val.comp f.continuous
  have h2 := h1 _ hF₀ hF₀X _ hfc (by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact (f w).2
    · intro hy
      exact ⟨f.symm ⟨y, hy⟩, by simp⟩) (hj.continuous.comp hfc)
  convert h2 using 2
  ext w
  simp [he]

/-- A solid set is planar if each of its `O`-arcs is homotopic into a closed disc. -/
theorem isPlanar_of_homotopy {T : Type u} [TopologicalSpace T] [CompactSpace Y] [T2Space Y]
  (hT : IsSurface T) [ConnectedSpace T]
    {j : Y → T} (hj : IsEmbedding j) {X : Set Y} (hX : IsSolid X) (hne : ¬ IsSphere T
      ∨ j '' X ≠ univ) {H : 𝕀 × Y → T}
    (hH : Continuous H) (h0 : ∀ y, H (0, y) = j y)
    (h1 : ∀ F, IsOArc F → F ⊆ X → ∃ Δ, IsClosedDisc Δ ∧ ∀ y ∈ F, H (1, y) ∈ Δ) : IsPlanar (j '' X)
      := by
  refine isPlanar_of_null hT hj hX hne fun F hF hFX f hf hrange hc => ?_
  obtain ⟨Δ, hΔ, hs⟩ := h1 F hF hFX
  have h2 := null_of_homotopy_into_disc hH hf hΔ fun w => hs _ (hrange ▸ mem_range_self w)
  convert h2 using 2
  ext w
  simp [h0]

/-- The inverse of a one to one map on a compact set, as a disc: the preimage of a closed disc is a
closed disc if the map is
one to one on it. -/
theorem isClosedDisc_preimage_of_injOn {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [CompactSpace A] [T2Space B]
    {f : A → B} (hf : Continuous f) (hs : Function.Surjective f) {Δ : Set B} (hΔ : IsClosedDisc Δ)
      (hi : InjOn f (f ⁻¹' Δ)) :
    IsClosedDisc (f ⁻¹' Δ) ∧ discBd (f ⁻¹' Δ) = f ⁻¹' discBd Δ := by
  obtain ⟨b, hb⟩ : Δ.Nonempty := by
    obtain ⟨h⟩ := id hΔ
    exact ⟨_, (h ⟨0, mem_closedBall_self zero_le_one⟩).2⟩
  have : Nonempty A := ⟨(hs b).choose⟩
  have hK : IsCompact (f ⁻¹' Δ) := (hΔ.isCompact.isClosed.preimage hf).isCompact
  obtain ⟨g, hgc, hgl⟩ := exists_inv_of_compactOn hK hf.continuousOn hi
  have him : f '' (f ⁻¹' Δ) = Δ := image_preimage_eq Δ hs
  rw [him] at hgc
  have hr : RightInvOn g f Δ := fun y hy => by
    obtain ⟨x, rfl⟩ := hs y
    rw [hgl (show x ∈ f ⁻¹' Δ from hy)]
  have hl : LeftInvOn f g Δ := hr
  have hgK : g '' Δ = f ⁻¹' Δ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change f (g y) ∈ Δ
      rwa [hl hy]
    · intro hx
      exact ⟨f x, hx, hgl hx⟩
  obtain ⟨h1, h2⟩ := hΔ.image hgc hf.continuousOn hl
  rw [hgK] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change f (g y) ∈ discBd Δ
    rwa [hl (Surface.discBd_subset _ hy)]
  · intro hx
    exact ⟨f x, hx, hgl (Surface.discBd_subset _ hx : f x ∈ Δ)⟩

end GraphMinor.GM07
