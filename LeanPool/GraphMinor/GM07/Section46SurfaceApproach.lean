/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.CutComp
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Gluing
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# Small connected approaches in a surface

In VII (4.6), page 228, `ψ` has one point over a point of `bd(Σ′)` off the
matching. The reason is local: a boundary point has small
neighbourhoods which stay connected once the boundary is removed. In a
half-plane chart such a neighbourhood contains an open half ball, which is
convex and lies off the boundary, and is dense in what remains.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface

private theorem isInteriorPoint_halfSpace (q : EuclideanHalfSpace 2) (hq : 0 < q.1 0) :
    IsInteriorPoint q := by
  have hc : Continuous fun p : EuclideanPlane => p 0 := by fun_prop
  have hopen : IsOpen {p : EuclideanPlane | 0 < p 0} := isOpen_lt continuous_const hc
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen q.1 hq
  have hind : IsInducing (fun x : EuclideanHalfSpace 2 => x.1) := ⟨rfl⟩
  have hinj : Function.Injective (fun x : EuclideanHalfSpace 2 => x.1) := Subtype.val_injective
  have hemb : IsEmbedding (fun x : EuclideanHalfSpace 2 => x.1) := ⟨hind, hinj⟩
  let U : Set (EuclideanHalfSpace 2) := (fun x : EuclideanHalfSpace 2 => x.1) ⁻¹' ball q.1 ρ
  have hUimg : (fun x : EuclideanHalfSpace 2 => x.1) '' U = ball q.1 ρ := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, (hball hp).le⟩, hp, rfl⟩
  have e₁ : U ≃ₜ ball q.1 ρ :=
    (hemb.homeomorphImage U).trans (Homeomorph.setCongr hUimg)
  have hρ' : ρ ≠ 0 := hρ.ne'
  let e₂ : ball q.1 ρ ≃ₜ OpenUnitDisc :=
    { toFun := fun p => ⟨ρ⁻¹ • (p.1 - q.1), by
        have hp : ‖p.1 - q.1‖ < ρ := by
          have h := p.2
          rwa [mem_ball, dist_eq_norm] at h
        simp only [OpenUnitDisc, mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos hρ]
        rw [inv_mul_lt_iff₀ hρ]
        simpa using hp⟩
      invFun := fun y => ⟨q.1 + ρ • y.1, by
        have hy : ‖y.1‖ < 1 := by simpa [OpenUnitDisc] using y.2
        simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hρ]
        nlinarith⟩
      left_inv := fun p => by
        apply Subtype.ext
        simp [smul_smul, hρ']
      right_inv := fun y => by
        apply Subtype.ext
        simp [smul_smul, hρ']
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨U, isOpen_ball.preimage hind.continuous, mem_ball_self hρ, ⟨e₁.trans e₂⟩⟩

/-- A manifold point has small neighbourhoods which stay connected without the boundary. -/
theorem surface_connected_approach {Y : Type*} [TopologicalSpace Y] {x : Y}
    (hx : IsManifoldPoint x) {O : Set Y} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ W : Set Y, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsPreconnected (W ∩ (bd Y)ᶜ) := by
  classical
  obtain ⟨U, V, hU, hV, hxU, ⟨e⟩⟩ := hx
  have hind : IsInducing (fun x : EuclideanHalfSpace 2 => x.1) := ⟨rfl⟩
  -- The open embedding of the chart domain.
  let c : V → Y := fun p => (e.symm p).1
  have hc : IsOpenEmbedding c := hU.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
  let b : V → EuclideanHalfSpace 2 := Subtype.val
  have hb : IsOpenEmbedding b := hV.isOpenEmbedding_subtypeVal
  let vx : V := e ⟨x, hxU⟩
  have hcx : c vx = x := by simp [c, vx]
  have hopen : IsOpen (b '' (c ⁻¹' O)) := hb.isOpenMap _ (hO.preimage hc.continuous)
  obtain ⟨O₁, hO₁, hO₁e⟩ := hind.isOpen_iff.mp hopen
  have hmem : (vx.1).1 ∈ O₁ := by
    have : vx.1 ∈ (fun x : EuclideanHalfSpace 2 => x.1) ⁻¹' O₁ := by
      rw [hO₁e]
      exact ⟨vx, by simpa [hcx] using hxO, rfl⟩
    exact this
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO₁ _ hmem
  let B : Set V := b ⁻¹' ((fun x : EuclideanHalfSpace 2 => x.1) ⁻¹' ball (vx.1).1 r)
  have hBo : IsOpen B := (isOpen_ball.preimage hind.continuous).preimage hb.continuous
  have hBO : ∀ p ∈ B, c p ∈ O := by
    intro p hp
    have h1 : p.1 ∈ (fun x : EuclideanHalfSpace 2 => x.1) ⁻¹' O₁ := hball hp
    rw [hO₁e] at h1
    obtain ⟨p', hp', hpp⟩ := h1
    rw [← hb.injective hpp]
    exact hp'
  refine ⟨c '' B, hc.isOpenMap _ hBo, ⟨vx, mem_ball_self hr, hcx⟩, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hBO p hp
  -- The open half ball.
  let P : Set EuclideanPlane := ball (vx.1).1 r ∩ {p | 0 < p 0}
  have hPc : Convex ℝ P := by
    apply (convex_ball _ _).inter
    exact convex_halfSpace_gt (f := fun p : EuclideanPlane => p 0) ⟨fun _ _ => rfl,
      fun _ _ => rfl⟩ 0
  let A : Set V := (fun p : V => (p.1).1) ⁻¹' P
  have hvalemb : IsEmbedding (fun p : V => (p.1).1) := IsEmbedding.subtypeVal.comp hb.isEmbedding
  have hAimg : (fun p : V => (p.1).1) '' A = P ∩ {p | ∃ h : 0 ≤ p 0, (⟨p, h⟩ : EuclideanHalfSpace
    2) ∈ V} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq, q.1.2, q.2⟩
    · rintro ⟨hp, h, hV'⟩
      exact ⟨⟨⟨p, h⟩, hV'⟩, hp, rfl⟩
  have hPV : P ⊆ {p | ∃ h : 0 ≤ p 0, (⟨p, h⟩ : EuclideanHalfSpace 2) ∈ V} := by
    intro p hp
    have h0 : 0 ≤ p 0 := hp.2.le
    refine ⟨h0, ?_⟩
    have h1 : (⟨p, h0⟩ : EuclideanHalfSpace 2) ∈ (fun x : EuclideanHalfSpace 2 => x.1) ⁻¹' O₁ :=
      hball hp.1
    rw [hO₁e] at h1
    obtain ⟨p', -, hpp⟩ := h1
    exact hpp ▸ p'.2
  have hApre : IsPreconnected A := by
    rw [← hvalemb.isInducing.isPreconnected_image, hAimg, inter_eq_left.mpr hPV]
    exact hPc.isPreconnected
  have hcA : c '' A ⊆ (bd Y)ᶜ := by
    rintro _ ⟨p, hp, rfl⟩ hb'
    apply hb'
    apply isInteriorPoint_of_isOpenEmbedding hc
    exact (isInteriorPoint_sub hV).mpr (isInteriorPoint_halfSpace _ hp.2)
  have hAclosure : ∀ p ∈ B, p ∈ closure A := by
    intro p hp
    -- Push `p` upward by small amounts inside the ball and inside `V`.
    let e₀ : EuclideanPlane := EuclideanSpace.single 0 1
    have he₀ : e₀ 0 = 1 := by simp [e₀]
    let u : ℝ → EuclideanHalfSpace 2 := fun δ => ⟨(p.1).1 + max δ 0 • e₀, by
      have h0 : 0 ≤ (p.1).1 0 := p.1.2
      have hm : 0 ≤ max δ 0 := le_max_right _ _
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, he₀, mul_one]
      linarith⟩
    have huc : Continuous u := by
      apply Continuous.subtype_mk
      fun_prop
    have hu0 : u 0 = p.1 := by
      apply Subtype.ext
      simp [u]
    have hB' : IsOpen (b '' B) := hb.isOpenMap _ hBo
    have hmemB : p.1 ∈ b '' B := ⟨p, hp, rfl⟩
    have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), u δ ∈ b '' B := by
      apply huc.continuousAt.eventually_mem
      rw [hu0]
      exact hB'.mem_nhds hmemB
    have hev' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), u δ ∈ b '' B ∧ 0 < (u δ).1 0 := by
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with δ h1 h2
      refine ⟨h1, ?_⟩
      have h0 : 0 ≤ (p.1).1 0 := p.1.2
      have hδ : (0 : ℝ) < δ := h2
      simp only [u, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, he₀, mul_one, max_eq_left hδ.le]
      linarith
    rw [_root_.mem_closure_iff]
    intro G hG hpG
    have hG' : IsOpen (b '' G) := hb.isOpenMap _ hG
    have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), u δ ∈ b '' G := by
      apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      apply huc.continuousAt.eventually_mem
      rw [hu0]
      exact hG'.mem_nhds ⟨p, hpG, rfl⟩
    obtain ⟨δ, ⟨hδB, hδpos⟩, hδG⟩ := (hev'.and hev2).exists
    obtain ⟨q, hqG, hq⟩ := hδG
    obtain ⟨q', hq'B, hq'⟩ := hδB
    have hqq : q = q' := hb.injective (hq.trans hq'.symm)
    subst hqq
    refine ⟨q, hqG, ?_⟩
    have hqball : (q.1).1 ∈ ball (vx.1).1 r := hq'B
    refine ⟨hqball, ?_⟩
    have : (q.1).1 = (u δ).1 := congrArg Subtype.val hq
    change 0 < (q.1).1 0
    rw [this]
    exact hδpos
  have hsub1 : c '' A ⊆ c '' B ∩ (bd Y)ᶜ := fun y hy => by
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨⟨p, hp.1, rfl⟩, hcA ⟨p, hp, rfl⟩⟩
  have hsub2 : c '' B ∩ (bd Y)ᶜ ⊆ closure (c '' A) := by
    rintro _ ⟨⟨p, hp, rfl⟩, -⟩
    exact image_closure_subset_closure_image hc.continuous ⟨p, hAclosure p hp, rfl⟩
  exact (hApre.image c hc.continuous.continuousOn).subset_closure hsub1 hsub2

end GraphMinor.GM07
