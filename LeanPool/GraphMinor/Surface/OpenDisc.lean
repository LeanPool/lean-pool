/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscMerge
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Open sets in which every `O`-arc bounds a closed disc

`open_disc : OpenDiscStatement`: Graph Minors VII, (4.2). Let `S` be a connected closed surface and
`Y ⊆ S` connected and open, such that every `O`-arc in `Y` bounds a closed disc in `Y`. Then `S` is
a
sphere and `Y = S`, or `Y` is an open disc.

The route. By `exists_disc_merge`, `Y` is exhausted by closed discs `D₀ ⊆ D₁ ⊆ ⋯`, each in the
inside
of the next. We then map them into the plane, one after the other. A map of `D_n` has as image a
closed domain of the plane, and by the Schoenflies theorem the map on the boundary of `D_n` extends
to
a homeomorphism of the plane (`exists_extension_step`). So the map extends to `D_{n+1}`, and no
annulus theorem is needed. A push of the plane that is the identity on the image of `D_n` makes the
image of `D_{n+1}` contain any given ball, so the limit map is onto the plane.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

universe u

/-! ### Radial pushes of the plane -/

/-- The map that changes the radius by `f`. -/
noncomputable def radialMap (f : ℝ → ℝ) (z : ℂ) : ℂ := ((f ‖z‖ / ‖z‖ : ℝ) : ℂ) * z

theorem radialMap_of_le {f : ℝ → ℝ} (hf : ∀ r ≤ 1, f r = r) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    radialMap f z = z := by
  by_cases h0 : z = 0
  · simp [radialMap, h0]
  · have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    simp [radialMap, hf _ hz, this]

theorem norm_radialMap {f : ℝ → ℝ} (hf : ∀ r, 0 < r → 0 < f r) {z : ℂ} (hz : z ≠ 0) :
    ‖radialMap f z‖ = f ‖z‖ := by
  have h1 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2 := hf _ h1
  simp only [radialMap, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity)]
  field_simp

theorem continuous_radialMap {f : ℝ → ℝ} (hc : Continuous f) (hf : ∀ r ≤ 1, f r = r) :
    Continuous (radialMap f) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases h0 : z = 0
  · subst h0
    have : radialMap f =ᶠ[𝓝 0] id := by
      filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with w hw
      exact radialMap_of_le hf (mem_ball_zero_iff.mp hw).le
    exact continuousAt_id.congr this.symm
  · have h1 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    refine ContinuousAt.mul ?_ continuousAt_id
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    exact (hc.comp continuous_norm).continuousAt.div continuous_norm.continuousAt h1

/-- For `0 < δ` and `1 + δ < M`, a homeomorphism of the plane is the identity on the unit disc and
maps the disc of radius `1 + δ` onto the disc of radius `M`. -/
theorem exists_radial {δ M : ℝ} (hδ : 0 < δ) (hM : 1 + δ < M) :
    ∃ θ : ℂ ≃ₜ ℂ, (∀ z ∈ closedBall (0 : ℂ) 1, θ z = z) ∧
      closedBall 0 M ⊆ θ '' closedBall (0 : ℂ) (1 + δ) := by
  set K := (M - 1) / δ with hK
  set L := M - 1 - δ with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hK1 : 1 < K := by
    rw [hK, lt_div_iff₀ hδ]
    linarith
  have hKδ : K * δ = M - 1 := by
    rw [hK]
    field_simp
  let f : ℝ → ℝ := fun r => min (max r (1 + K * (r - 1))) (r + L)
  have hsm1 : StrictMono fun r : ℝ => r := strictMono_id
  have hsm2 : StrictMono fun r : ℝ => 1 + K * (r - 1) := fun a b hab => by
    have : 0 < K := by linarith
    change 1 + K * (a - 1) < 1 + K * (b - 1)
    nlinarith
  have hsm3 : StrictMono fun r : ℝ => r + L := fun a b hab => by
    change a + L < b + L
    linarith
  have hfm : StrictMono f := fun a b hab => min_lt_min (max_lt_max (hsm1 hab) (hsm2 hab)) (hsm3 hab)
  have hfc : Continuous f := by fun_prop
  have hf1 : ∀ r ≤ 1, f r = r := fun r hr => by
    have h1 : 1 + K * (r - 1) ≤ r := by nlinarith
    change min (max r (1 + K * (r - 1))) (r + L) = r
    rw [max_eq_left h1, min_eq_left (by linarith)]
  have hfM : f (1 + δ) = M := by
    have h1 : 1 + K * (1 + δ - 1) = M := by
      rw [add_sub_cancel_left, hKδ]
      ring
    change min (max (1 + δ) (1 + K * (1 + δ - 1))) (1 + δ + L) = M
    rw [h1, max_eq_right hM.le, min_eq_left (by rw [hL]; linarith)]
  have hf0 : ∀ r, 0 < r → 0 < f r := fun r hr => by
    have h1 : f 0 = 0 := hf1 0 zero_le_one
    rw [← h1]
    exact hfm hr
  have htop : Tendsto f atTop atTop := by
    refine tendsto_atTop_mono (f := fun r => r) (fun r => ?_) tendsto_id
    rcases le_total r 1 with h | h
    · exact (hf1 r h).symm.le
    · change r ≤ min (max r (1 + K * (r - 1))) (r + L)
      exact le_min (le_max_left _ _) (by linarith)
  have hbot : Tendsto f atBot atBot := by
    refine Tendsto.congr' ?_ tendsto_id
    filter_upwards [eventually_le_atBot (1 : ℝ)] with r hr
    exact (hf1 r hr).symm
  have hsurj : Function.Surjective f := hfc.surjective htop hbot
  let e : ℝ ≃o ℝ := hfm.orderIsoOfSurjective f hsurj
  have hef : ∀ r, e r = f r := fun _ => rfl
  let f' : ℝ → ℝ := e.symm
  have hff' : ∀ r, f (f' r) = r := fun r => e.apply_symm_apply r
  have hf'f : ∀ r, f' (f r) = r := fun r => e.symm_apply_apply r
  have hf'c : Continuous f' := e.symm.continuous
  have hf'1 : ∀ r ≤ 1, f' r = r := fun r hr => by
    have := hf'f r
    rwa [hf1 r hr] at this
  have hf'0 : ∀ r, 0 < r → 0 < f' r := fun r hr => by
    by_contra hcon
    have h1 : f' r ≤ 0 := not_lt.mp hcon
    have h2 := hfm.monotone h1
    rw [hff', hf1 0 zero_le_one] at h2
    linarith
  have hinv : ∀ {g g' : ℝ → ℝ}, (∀ r, g' (g r) = r) → (∀ r, 0 < r → 0 < g r) →
      ∀ z, radialMap g' (radialMap g z) = z := by
    intro g g' h1 h2 z
    by_cases h0 : z = 0
    · simp [radialMap, h0]
    · have h3 := norm_radialMap h2 h0
      have h4 : 0 < ‖z‖ := norm_pos_iff.mpr h0
      have h5 := h2 _ h4
      have h6 : ((g ‖z‖ / ‖z‖ : ℝ) : ℂ) ≠ 0 := by
        have : g ‖z‖ / ‖z‖ ≠ 0 := by positivity
        exact_mod_cast this
      have h7 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast h4.ne'
      have h8 : (g ‖z‖ : ℂ) ≠ 0 := by exact_mod_cast h5.ne'
      rw [radialMap, h3, h1, radialMap, ← mul_assoc, ← Complex.ofReal_mul]
      have : ‖z‖ / g ‖z‖ * (g ‖z‖ / ‖z‖) = 1 := by
        field_simp
      rw [this]
      simp
  let θ : ℂ ≃ₜ ℂ :=
    { toFun := radialMap f
      invFun := radialMap f'
      left_inv := hinv hf'f hf0
      right_inv := hinv hff' hf'0
      continuous_toFun := continuous_radialMap hfc hf1
      continuous_invFun := continuous_radialMap hf'c hf'1 }
  refine ⟨θ, fun z hz => radialMap_of_le hf1 (mem_closedBall_zero_iff.mp hz), fun w hw => ?_⟩
  refine ⟨θ.symm w, ?_, θ.apply_symm_apply w⟩
  by_cases h0 : w = 0
  · have : θ.symm w = 0 := by
      change radialMap f' w = 0
      simp [radialMap, h0]
    rw [this, mem_closedBall_zero_iff, norm_zero]
    linarith
  · have h1 : ‖θ.symm w‖ = f' ‖w‖ := norm_radialMap hf'0 h0
    rw [mem_closedBall_zero_iff, h1]
    have h2 : f' M = 1 + δ := by rw [← hfM, hf'f]
    rw [← h2]
    exact e.symm.monotone (mem_closedBall_zero_iff.mp hw)

/-! ### Extending a map of a closed disc to a larger closed disc -/

variable {S : Type u} [TopologicalSpace S]

/-- A homeomorphism of the plane that sends the unit circle onto `F` sends the closed unit disc
onto the closed domain of `F`. -/
theorem image_closedBall_of_homeomorph (G : ℂ ≃ₜ ℂ) {F : Set ℂ} (hF : Nonempty (Circle ≃ₜ F))
    (h : G '' sphere 0 1 = F) : G '' closedBall 0 1 = closedInner F := by
  obtain ⟨h1, h2⟩ := isClosedDisc_closedBall.1.image (f := G) (f' := G.symm)
    G.continuous.continuousOn G.symm.continuous.continuousOn fun z _ => G.symm_apply_apply z
  rw [isClosedDisc_closedBall.2, h] at h2
  exact eq_closedInner_of_discBd hF h1 h2

theorem BdMatch.trans {A B C : Set ℂ} {f f' k k' : ℂ → ℂ} (m : BdMatch A B f f')
    (m' : BdMatch B C k k') : BdMatch A C (fun z => k (f z)) (fun z => f' (k' z)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := m
  obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := m'
  refine ⟨h1'.comp h1, h2.comp h2', ?_, ?_, h5'.comp h5 h1, h6.comp h6' h2'⟩
  · intro z hz
    change f' (k' (k (f z))) = z
    rw [h3' (h1 hz), h3 hz]
  · intro z hz
    change k (f (f' (k' z))) = z
    rw [h4 (h2' hz), h4' hz]

/-- **The extension step.** Let `D` be a closed disc in the inside of the closed disc `D⁺`, and let
`ψ` embed `D` in the plane. Then `ψ` extends to an embedding of `D⁺` whose image contains the ball
of radius `R`. -/
theorem exists_extension_step [T2Space S] {D E : Set S} (hD : IsClosedDisc D)
    (hE : IsClosedDisc E) (hman : ∀ x : S, IsManifoldPoint x) (hsub : D ⊆ discInt E) {ψ : S → ℂ}
    (hψc : ContinuousOn ψ D) (hψi : InjOn ψ D) (R : ℝ) :
    ∃ ψ' : S → ℂ, ContinuousOn ψ' E ∧ InjOn ψ' E ∧ EqOn ψ' ψ D ∧ closedBall 0 R ⊆ ψ' '' E := by
  classical
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  have hDsub : D ⊆ E := hsub.trans (discInt_subset _)
  obtain ⟨y₀, hy₀⟩ := hD.nonempty_discInt
  have : Nonempty S := ⟨y₀⟩
  have hDc := hD.isCompact
  -- the two closed domains
  obtain ⟨ψinv, hψinv, hψl⟩ := exists_inv_of_compactOn hDc hψc hψi
  obtain ⟨hΩ, hΩb⟩ := hD.image hψc hψinv hψl
  have hΩ₀m := hD.image (c.hc.mono hDsub) (c.gc.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact c.hm (hDsub hx))) (c.gh.mono hDsub)
  obtain ⟨hΩ₀, hΩ₀b⟩ := hΩ₀m
  set F := ψ '' discBd D with hF
  set F₀ := h '' discBd D with hF₀
  have hFo : Nonempty (Circle ≃ₜ F) := hΩb ▸ hΩ.isOArc_discBd
  have hF₀o : Nonempty (Circle ≃ₜ F₀) := hΩ₀b ▸ hΩ₀.isOArc_discBd
  have hΩeq := eq_closedInner_of_discBd hFo hΩ hΩb
  have hΩ₀eq := eq_closedInner_of_discBd hF₀o hΩ₀ hΩ₀b
  have hbdD : discBd D ⊆ D := discBd_subset D
  have hgh : ∀ x ∈ D, g (h x) = x := fun x hx => c.gh (hDsub hx)
  have hψψ : ∀ x ∈ D, ψinv (ψ x) = x := fun x hx => hψl hx
  have hmatch : BdMatch F₀ F (fun w => ψ (g w)) (fun w => h (ψinv w)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      change ψ (g (h x)) ∈ F
      rw [hgh x (hbdD hx)]
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      change h (ψinv (ψ x)) ∈ F₀
      rw [hψψ x (hbdD hx)]
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      change h (ψinv (ψ (g (h x)))) = h x
      rw [hgh x (hbdD hx), hψψ x (hbdD hx)]
    · rintro _ ⟨x, hx, rfl⟩
      change ψ (g (h (ψinv (ψ x)))) = ψ x
      rw [hψψ x (hbdD hx), hgh x (hbdD hx)]
    · refine hψc.comp (c.gc.mono ?_) ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact c.hm (hDsub (hbdD hx))
      · rintro _ ⟨x, hx, rfl⟩
        show g (h x) ∈ D
        rw [hgh x (hbdD hx)]
        exact hbdD hx
    · refine c.hc.comp (hψinv.mono (image_mono hbdD)) ?_
      rintro _ ⟨x, hx, rfl⟩
      show ψinv (ψ x) ∈ E
      rw [hψψ x (hbdD hx)]
      exact hDsub (hbdD hx)
  obtain ⟨φ⟩ := id hFo
  obtain ⟨o⟩ := oArc_sphere
  obtain ⟨h₁, k₁, m₁, -⟩ := exists_bdMatch (o.symm.trans φ)
  obtain ⟨G₂, hG₂⟩ := exists_homeomorph_of_bdMatch hFo m₁
  have hm₀ : BdMatch (sphere 0 1) F₀ (fun z => h (ψinv (h₁ z))) (fun w => k₁ (ψ (g w))) :=
    m₁.trans hmatch.symm
  obtain ⟨G₁, hG₁⟩ := exists_homeomorph_of_bdMatch hF₀o hm₀
  have hG₂im : G₂ '' sphere 0 1 = F := by
    rw [image_congr hG₂]
    exact m₁.image_eq
  have hG₁im : G₁ '' sphere 0 1 = F₀ := by
    rw [image_congr hG₁]
    exact hm₀.image_eq
  have hG₂b := image_closedBall_of_homeomorph G₂ hFo hG₂im
  have hG₁b := image_closedBall_of_homeomorph G₁ hF₀o hG₁im
  rw [← hΩeq] at hG₂b
  rw [← hΩ₀eq] at hG₁b
  let ω : ℂ → ℂ := fun z => G₂ (G₁.symm z)
  have hωc : Continuous ω := G₂.continuous.comp G₁.symm.continuous
  have hωi : Function.Injective ω := G₂.injective.comp G₁.symm.injective
  have hωF : ∀ x ∈ discBd D, ω (h x) = ψ x := by
    intro x hx
    have hmem : ψ x ∈ F := ⟨x, hx, rfl⟩
    have hz := m₁.2.1 hmem
    have h1 : h₁ (k₁ (ψ x)) = ψ x := m₁.2.2.2.1 hmem
    have h2 : G₁ (k₁ (ψ x)) = h x := by
      rw [hG₁ hz]
      change h (ψinv (h₁ (k₁ (ψ x)))) = h x
      rw [h1, hψψ x (hbdD hx)]
    change G₂ (G₁.symm (h x)) = ψ x
    rw [← h2, G₁.symm_apply_apply, hG₂ hz, h1]
  have hωΩ : ω '' (h '' D) = ψ '' D := by
    rw [← hG₁b, ← hG₂b, image_image]
    exact image_congr fun z _ => by
      change G₂ (G₁.symm (G₁ z)) = G₂ z
      rw [G₁.symm_apply_apply]
  let ψ₀ : S → ℂ := fun x => if x ∈ D then ψ x else ω (h x)
  have hψ₀D : ∀ x ∈ D, ψ₀ x = ψ x := fun x hx => ite_eq_left hx
  have hψ₀n : ∀ x, x ∉ D → ψ₀ x = ω (h x) := fun x hx => ite_eq_right hx
  have hE₂c : IsClosed (E \ discInt D) := hE.isClosed.sdiff (hD.isOpen_discInt hman)
  have hcover : D ∪ (E \ discInt D) = E := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hDsub hx
      · exact hx.1
    · intro hx
      by_cases hi : x ∈ discInt D
      · exact .inl hi.1
      · exact .inr ⟨hx, hi⟩
  have hE₂eq : ∀ x ∈ E \ discInt D, ψ₀ x = ω (h x) := by
    intro x hx
    by_cases hxD : x ∈ D
    · have hxb : x ∈ discBd D := by
        by_contra hcon
        exact hx.2 ⟨hxD, hcon⟩
      rw [hψ₀D x hxD, hωF x hxb]
    · exact hψ₀n x hxD
  have hψ₀c : ContinuousOn ψ₀ E := by
    rw [← hcover]
    refine ContinuousOn.union_of_isClosed (hψc.congr hψ₀D) ?_ hD.isClosed hE₂c
    refine ContinuousOn.congr ?_ hE₂eq
    exact hωc.comp_continuousOn (c.hc.mono sdiff_subset)
  have hhi : InjOn h E := c.gh.injOn
  have hmix : ∀ x ∈ D, ∀ y ∈ E, y ∉ D → ψ x ≠ ω (h y) := by
    intro x hx y hyE hyD he
    have h1 : ψ x ∈ ω '' (h '' D) := hωΩ ▸ mem_image_of_mem ψ hx
    obtain ⟨_, ⟨x', hx', rfl⟩, h2⟩ := h1
    rw [he] at h2
    have h3 := hωi h2
    exact hyD (hhi (hDsub hx') hyE h3 ▸ hx')
  have hψ₀i : InjOn ψ₀ E := by
    intro x hx y hy he
    by_cases h1 : x ∈ D <;> by_cases h2 : y ∈ D
    · rw [hψ₀D x h1, hψ₀D y h2] at he
      exact hψi h1 h2 he
    · rw [hψ₀D x h1, hψ₀n y h2] at he
      exact absurd he (hmix x h1 y hy h2)
    · rw [hψ₀n x h1, hψ₀D y h2] at he
      exact absurd he.symm (hmix y h2 x hx h1)
    · rw [hψ₀n x h1, hψ₀n y h2] at he
      exact hhi hx hy (hωi he)
  have hψ₀img : ω '' closedBall 0 1 ⊆ ψ₀ '' E := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hx : g z ∈ D
    · have h1 : ω z ∈ ψ '' D := by
        rw [← hωΩ]
        exact ⟨z, ⟨g z, hx, c.hg hz⟩, rfl⟩
      obtain ⟨x, hx', he⟩ := h1
      exact ⟨x, hDsub hx', by rw [hψ₀D x hx', he]⟩
    · refine ⟨g z, c.gm hz, ?_⟩
      rw [hψ₀n _ hx, c.hg hz]
  -- the push
  have hball : h '' D ⊆ ball 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hsub hx
    rw [c.discInt_eq] at this
    obtain ⟨z, hz, rfl⟩ := this
    rwa [c.hg (ball_subset_closedBall hz)]
  have hAo : IsOpen (G₁.symm '' ball 0 1) := G₁.symm.isOpenMap _ isOpen_ball
  have hsubA : closedBall (0 : ℂ) 1 ⊆ G₁.symm '' ball 0 1 := fun z hz =>
    ⟨G₁ z, hball (hG₁b ▸ mem_image_of_mem G₁ hz), G₁.symm_apply_apply z⟩
  obtain ⟨δ₀, hδ₀, hth⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hAo hsubA
  rw [thickening_closedBall hδ₀ zero_le_one] at hth
  have hδ : 0 < δ₀ / 2 := by positivity
  have hsubδ : closedBall (0 : ℂ) (1 + δ₀ / 2) ⊆ G₁.symm '' ball 0 1 :=
    (closedBall_subset_ball (by linarith)).trans hth
  have hBc : IsCompact (G₂.symm '' closedBall (0 : ℂ) R) :=
    (isCompact_closedBall _ _).image G₂.symm.continuous
  obtain ⟨M₀, hM₀⟩ := hBc.isBounded.subset_closedBall (0 : ℂ)
  set M := max M₀ 0 + 2 + δ₀ with hM
  obtain ⟨θ, hθ1, hθ2⟩ := exists_radial (M := M) hδ (by
    have := le_max_right M₀ 0
    linarith)
  let ζ : ℂ → ℂ := fun z => G₂ (θ (G₂.symm z))
  have hζc : Continuous ζ := G₂.continuous.comp (θ.continuous.comp G₂.symm.continuous)
  have hζi : Function.Injective ζ := G₂.injective.comp (θ.injective.comp G₂.symm.injective)
  refine ⟨fun x => ζ (ψ₀ x), hζc.comp_continuousOn hψ₀c, ?_, ?_, ?_⟩
  · exact fun x hx y hy he => hψ₀i hx hy (hζi he)
  · intro x hx
    change ζ (ψ₀ x) = ψ x
    rw [hψ₀D x hx]
    have h1 : ψ x ∈ G₂ '' closedBall 0 1 := hG₂b ▸ mem_image_of_mem ψ hx
    obtain ⟨z, hz, he⟩ := h1
    change G₂ (θ (G₂.symm (ψ x))) = ψ x
    rw [← he, G₂.symm_apply_apply, hθ1 z hz]
  · intro w hw
    have h1 : G₂.symm w ∈ closedBall (0 : ℂ) M := by
      have := hM₀ (mem_image_of_mem G₂.symm hw)
      rw [mem_closedBall_zero_iff] at this ⊢
      have h2 := le_max_left M₀ 0
      linarith
    obtain ⟨u, hu, hue⟩ := hθ2 h1
    obtain ⟨z, hz, hzu⟩ := hsubδ hu
    have h3 : ω z ∈ ψ₀ '' E := hψ₀img ⟨z, ball_subset_closedBall hz, rfl⟩
    obtain ⟨x, hx, hxe⟩ := h3
    refine ⟨x, hx, ?_⟩
    change G₂ (θ (G₂.symm (ψ₀ x))) = w
    rw [hxe]
    change G₂ (θ (G₂.symm (G₂ (G₁.symm z)))) = w
    rw [G₂.symm_apply_apply, hzu, hue, G₂.apply_symm_apply]

/-! ### The chain of discs -/

section Chain

variable [CompactSpace S] [T2Space S] [ConnectedSpace S]
  (hint : ∀ x : S, IsInteriorPoint x) {Y : Set S} (hYo : IsOpen Y) (hYc : IsPreconnected Y)
  (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
  (hns : ¬ (IsSphere S ∧ Y = univ))
include hint hYo H hns

omit hYo in
/-- If a closed disc overlaps the unit ball of a chart, then a larger closed disc has that whole
unit ball in its inside. -/
theorem exists_disc_of_overlap {D : Set S} (hDY : D ⊆ Y) (hD : IsClosedDisc D)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart 3 U h g) (hUY : U ⊆ Y)
    (hz : (discInt D ∩ g '' ball 0 1).Nonempty) :
    ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ g '' ball 0 1 ⊆ discInt D' := by
  obtain ⟨D', h1, h2, h3, h4⟩ := exists_disc_merge hint H hns hDY hD c hUY hz
  have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
  refine ⟨D', h1, h2, h3, subset_discInt_of_isOpen (fun x _ => hint x)
    (c.isOpen_image isOpen_ball hb) ?_⟩
  exact (image_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall
    (by norm_num)))).trans h4

include hYc

/-- Every point of `Y` lies in the inside of a closed disc of `Y` that contains a given closed disc
of `Y`: the set of such points is open, and so is the rest of `Y`, by `exists_disc_of_overlap`. -/
theorem exists_disc_mem {D : Set S} (hDY : D ⊆ Y) (hD : IsClosedDisc D) {y : S} (hy : y ∈ Y) :
    ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ y ∈ discInt D' := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  let A : Set S := {y | ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ y ∈ discInt D'}
  have hAo : IsOpen A := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro x ⟨D', h1, h2, h3, h4⟩
    filter_upwards [(h2.isOpen_discInt hman).mem_nhds h4] with z hz
    exact ⟨D', h1, h2, h3, hz⟩
  have hBo : IsOpen (Y \ A) := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro x ⟨hxY, hxA⟩
    obtain ⟨U, h, g, c, hUY, hg0⟩ := (hint x).exists_ballChart hYo hxY (R := 3) (by norm_num)
    have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
    have hV := c.isOpen_image isOpen_ball hb
    have hx : x ∈ g '' ball 0 1 := ⟨0, by simp, hg0⟩
    filter_upwards [hV.mem_nhds hx] with z hz
    obtain ⟨w, hw, rfl⟩ := id hz
    refine ⟨hUY (c.gm (hb hw)), ?_⟩
    rintro ⟨D', h1, h2, h3, h4⟩
    obtain ⟨E, h5, h6, h7, h8⟩ := exists_disc_of_overlap hint H hns h1 h2 c hUY ⟨_, h4, hz⟩
    exact hxA ⟨E, h5, h6, h3.trans h7, h8 hx⟩
  by_contra hcon
  obtain ⟨z, hz⟩ := hD.nonempty_discInt
  obtain ⟨w, -, hw1, hw2⟩ := hYc A (Y \ A) hAo hBo
    (fun x hx => by
      by_cases hxA : x ∈ A
      · exact .inl hxA
      · exact .inr ⟨hx, hxA⟩)
    ⟨z, hDY (discInt_subset D hz), D, hDY, hD, Subset.rfl, hz⟩ ⟨y, hy, hy, hcon⟩
  exact hw2.2 hw1

/-- Around every point of `Y` there is a neighbourhood that the inside of a closed disc swallows,
starting from any closed disc of `Y`. -/
theorem exists_disc_nhds {y : S} (hy : y ∈ Y) : ∃ V ∈ 𝓝 y, ∀ D : Set S, D ⊆ Y → IsClosedDisc D →
    ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ V ⊆ discInt D' := by
  obtain ⟨U, h, g, c, hUY, hg0⟩ := (hint y).exists_ballChart hYo hy (R := 3) (by norm_num)
  have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
  have hy' : y ∈ g '' ball 0 1 := ⟨0, by simp, hg0⟩
  refine ⟨g '' ball 0 1, (c.isOpen_image isOpen_ball hb).mem_nhds hy', fun D hDY hD => ?_⟩
  obtain ⟨D₁, h1, h2, h3, h4⟩ := exists_disc_mem hint hYo hYc H hns hDY hD hy
  obtain ⟨D₂, h5, h6, h7, h8⟩ := exists_disc_of_overlap hint H hns h1 h2 c hUY ⟨y, h4, hy'⟩
  exact ⟨D₂, h5, h6, h3.trans h7, h8⟩

/-- The inside of a closed disc of `Y` swallows any compact subset of `Y` and any given closed disc
of `Y`. -/
theorem exists_disc_compact {K : Set S} (hK : IsCompact K) (hKY : K ⊆ Y) {D : Set S} (hDY : D ⊆ Y)
    (hD : IsClosedDisc D) :
    ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ K ⊆ discInt D' := by
  refine hK.induction_on (p := fun K => ∀ D : Set S, D ⊆ Y → IsClosedDisc D →
    ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ K ⊆ discInt D') ?_ ?_ ?_ ?_ D hDY hD
  · exact fun D hDY hD => ⟨D, hDY, hD, Subset.rfl, empty_subset _⟩
  · intro s t hst hp D hDY hD
    obtain ⟨D', h1, h2, h3, h4⟩ := hp D hDY hD
    exact ⟨D', h1, h2, h3, hst.trans h4⟩
  · intro s t hs ht D hDY hD
    obtain ⟨D₁, h1, h2, h3, h4⟩ := hs D hDY hD
    obtain ⟨D₂, h5, h6, h7, h8⟩ := ht D₁ h1 h2
    exact ⟨D₂, h5, h6, h3.trans h7,
      union_subset (h4.trans (discInt_mono (fun x => (hint x).isManifoldPoint) h2 h7)) h8⟩
  · intro x hx
    obtain ⟨V, hV, hp⟩ := exists_disc_nhds hint hYo hYc H hns (hKY hx)
    exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, hp⟩

/-- `Y` is the increasing union of the insides of a chain of closed discs. -/
theorem exists_disc_chain (hYne : Y.Nonempty) :
    ∃ D : ℕ → Set S, (∀ n, D n ⊆ Y) ∧ (∀ n, IsClosedDisc (D n)) ∧
      (∀ n, D n ⊆ discInt (D (n + 1))) ∧ Y ⊆ ⋃ n, discInt (D n) := by
  classical
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  obtain ⟨y, hy⟩ := hYne
  obtain ⟨U, h, g, c, hUY, -⟩ := (hint y).exists_ballChart hYo hy (R := 3) (by norm_num)
  have hb : closedBall (0 : ℂ) 1 ⊆ ball 0 3 := closedBall_subset_ball (by norm_num)
  have hd₀ := (c.image_disc isClosedDisc_closedBall.1 hb).1
  have hsc := secondCountable_of_manifold hman
  have : LocallyCompactSpace Y := hYo.locallyCompactSpace
  let E : CompactExhaustion Y := default
  let T := {D : Set S // D ⊆ Y ∧ IsClosedDisc D}
  have hnext : ∀ (n : ℕ) (D : T), ∃ D' : T, D.1 ⊆ discInt D'.1 ∧
      ((↑) '' E n : Set S) ⊆ discInt D'.1 := by
    intro n D
    have hcomp : IsCompact (((↑) '' E n : Set S) ∪ D.1) :=
      ((E.isCompact n).image continuous_subtype_val).union D.2.2.isCompact
    obtain ⟨D', h1, h2, -, h4⟩ := exists_disc_compact hint hYo hYc H hns hcomp
      (union_subset (by rintro _ ⟨x, -, rfl⟩; exact x.2) D.2.1) D.2.1 D.2.2
    exact ⟨⟨D', h1, h2⟩, subset_union_right.trans h4, subset_union_left.trans h4⟩
  choose next hnext1 hnext2 using hnext
  let seq : ℕ → T := fun n => Nat.rec ⟨g '' closedBall 0 1,
    (image_subset_iff.mpr fun z hz => c.gm (hb hz)).trans hUY, hd₀⟩ next n
  refine ⟨fun n => (seq n).1, fun n => (seq n).2.1, fun n => (seq n).2.2, fun n => hnext1 n _, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
  exact mem_iUnion.mpr ⟨n + 1, hnext2 n _ ⟨_, hn, rfl⟩⟩

end Chain

/-! ### The limit map -/

/-- A chain of closed discs, each in the inside of the next, has as union a copy of the plane. -/
theorem exists_homeomorph_of_chain [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {Y : Set S}
    {D : ℕ → Set S} (hD : ∀ n, IsClosedDisc (D n))
    (hsub : ∀ n, D n ⊆ discInt (D (n + 1))) (hY : Y = ⋃ n, discInt (D n)) :
    Nonempty (Y ≃ₜ ℂ) := by
  classical
  obtain ⟨h₀, g₀, c₀⟩ := (hD 0).exists_isChart
  let T : ℕ → Type u := fun n => {ψ : S → ℂ // ContinuousOn ψ (D n) ∧ InjOn ψ (D n) ∧
    closedBall 0 ((n : ℝ) - 1) ⊆ ψ '' D n}
  have hnext : ∀ (n : ℕ) (ψ : T n), ∃ ψ' : T (n + 1), EqOn ψ'.1 ψ.1 (D n) := by
    intro n ψ
    obtain ⟨ψ', h1, h2, h3, h4⟩ := exists_extension_step (hD n) (hD (n + 1)) hman (hsub n)
      ψ.2.1 ψ.2.2.1 (n : ℝ)
    refine ⟨⟨ψ', h1, h2, ?_⟩, h3⟩
    push_cast
    simpa using h4
  choose next hnext using hnext
  have h0 : ContinuousOn h₀ (D 0) ∧ InjOn h₀ (D 0) ∧
      closedBall 0 (((0 : ℕ) : ℝ) - 1) ⊆ h₀ '' D 0 := by
    refine ⟨c₀.hc, c₀.gh.injOn, ?_⟩
    rw [closedBall_eq_empty.mpr (by norm_num)]
    exact empty_subset _
  let seq : (n : ℕ) → T n := fun n => Nat.rec ⟨h₀, h0⟩ next n
  let ψ : ℕ → S → ℂ := fun n => (seq n).1
  have hψc : ∀ n, ContinuousOn (ψ n) (D n) := fun n => (seq n).2.1
  have hψi : ∀ n, InjOn (ψ n) (D n) := fun n => (seq n).2.2.1
  have hψb : ∀ n : ℕ, closedBall 0 ((n : ℝ) - 1) ⊆ ψ n '' D n := fun n => (seq n).2.2.2
  have hψs : ∀ n, EqOn (ψ (n + 1)) (ψ n) (D n) := fun n => hnext n _
  have hDs : ∀ n, D n ⊆ D (n + 1) := fun n => (hsub n).trans (discInt_subset _)
  have hDm : Monotone D := monotone_nat_of_le_succ hDs
  have hψm : ∀ {n m : ℕ}, n ≤ m → EqOn (ψ m) (ψ n) (D n) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ m _ ih =>
      intro x hx
      rw [hψs m (hDm ‹n ≤ m› hx), ih hx]
  have hYD : ∀ n, D n ⊆ Y := fun n => by
    rw [hY]
    exact (hsub n).trans (subset_iUnion (fun n => discInt (D n)) (n + 1))
  have hidx : ∀ x : S, ∃ n, x ∈ Y → x ∈ D n := fun x => by
    by_cases hx : x ∈ Y
    · rw [hY] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact ⟨n, fun _ => discInt_subset _ hn⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose idx hidx using hidx
  let Ψ : Y → ℂ := fun x => ψ (idx x.1) x.1
  have hΨ : ∀ (x : Y) n, x.1 ∈ D n → Ψ x = ψ n x.1 := by
    intro x n hn
    have h1 := hψm (le_max_left n (idx x.1)) hn
    have h2 := hψm (le_max_right n (idx x.1)) (hidx x.1 x.2)
    exact h2.symm.trans h1
  have hinj : Function.Injective Ψ := by
    intro x y he
    have hx := hDm (le_max_left (idx x.1) (idx y.1)) (hidx x.1 x.2)
    have hy := hDm (le_max_right (idx x.1) (idx y.1)) (hidx y.1 y.2)
    rw [hΨ x _ hx, hΨ y _ hy] at he
    exact Subtype.ext (hψi _ hx hy he)
  have hball : ∀ w : ℂ, ∃ n : ℕ, ‖w‖ < (n : ℝ) - 1 := fun w => by
    obtain ⟨n, hn⟩ := exists_nat_gt (‖w‖ + 1)
    exact ⟨n, by linarith⟩
  have hsurj : Function.Surjective Ψ := by
    intro w
    obtain ⟨n, hn⟩ := hball w
    obtain ⟨x, hx, he⟩ := hψb n (mem_closedBall_zero_iff.mpr hn.le)
    exact ⟨⟨x, hYD n hx⟩, (hΨ ⟨x, hYD n hx⟩ n hx).trans he⟩
  have hcont : Continuous Ψ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx : x.1 ∈ ⋃ n, discInt (D n) := hY ▸ x.2
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hopen := (hD n).isOpen_discInt hman
    have h1 : ContinuousAt (ψ n) x.1 :=
      (hψc n).continuousAt (mem_of_superset (hopen.mem_nhds hn)
        (discInt_subset _ : discInt (D n) ⊆ D n))
    have h2 : ContinuousAt (fun z : Y => ψ n z.1) x := h1.comp continuous_subtype_val.continuousAt
    refine h2.congr ?_
    have h3 : Subtype.val ⁻¹' discInt (D n) ∈ 𝓝 x :=
      (hopen.preimage continuous_subtype_val).mem_nhds hn
    filter_upwards [h3] with z hz
    exact (hΨ z n (discInt_subset _ hz)).symm
  let e : Y ≃ ℂ := Equiv.ofBijective Ψ ⟨hinj, hsurj⟩
  have hsymm : Continuous e.symm := by
    rw [continuous_iff_continuousAt]
    intro w
    obtain ⟨n, hn⟩ := hball w
    have : Nonempty S := by
      obtain ⟨z, hz⟩ := (hD 0).nonempty_discInt
      exact ⟨z⟩
    obtain ⟨ι, hι, hιl⟩ := exists_inv_of_compactOn (hD n).isCompact (hψc n) (hψi n)
    have hballn : ball 0 ((n : ℝ) - 1) ⊆ ψ n '' D n := ball_subset_closedBall.trans (hψb n)
    have hw : ball 0 ((n : ℝ) - 1) ∈ 𝓝 w := isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hn)
    have h1 : ContinuousAt ι w := hι.continuousAt (mem_of_superset hw hballn)
    refine (IsInducing.subtypeVal.continuousAt_iff).mpr (h1.congr ?_)
    filter_upwards [hw] with z hz
    obtain ⟨x, hx, rfl⟩ := hballn hz
    change ι (ψ n x) = (e.symm (ψ n x)).1
    have h2 : e.symm (ψ n x) = ⟨x, hYD n hx⟩ := by
      rw [Equiv.symm_apply_eq]
      exact (hΨ ⟨x, hYD n hx⟩ n hx).symm
    rw [h2, hιl hx]
  exact ⟨⟨e, hcont, hsymm⟩⟩

/-- **Graph Minors VII, (4.2).** See the module docstring for the route. -/
theorem open_disc : OpenDiscStatement.{u} := by
  intro S _ Y hS _ hYc hYo H
  obtain ⟨hcpt, ht2, hint⟩ := hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  by_cases hns : IsSphere S ∧ Y = univ
  · exact .inl hns
  right
  obtain ⟨D, hDY, hD, hsub, hcov⟩ :=
    exists_disc_chain hint hYo hYc.isPreconnected H hns hYc.nonempty
  have hY : Y = ⋃ n, discInt (D n) := hcov.antisymm
    (iUnion_subset fun n => (discInt_subset _).trans (hDY n))
  obtain ⟨e⟩ := exists_homeomorph_of_chain hman hD hsub hY
  refine ⟨hYo, ⟨?_⟩⟩
  exact (Homeomorph.unitBall (E := EuclideanPlane)).symm.trans
    (complexPlane.symm.toHomeomorph.trans e.symm)

end GraphMinor.Surface
