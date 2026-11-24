/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
public import LeanPool.GraphMinor.GM12.Section4DiscTwist
public import LeanPool.GraphMinor.GM12.Section4JoinedCollars
import LeanPool.GraphMinor.GM12.Section4DiscCompression
import LeanPool.GraphMinor.GM12.Section4DiscEnlargement
import LeanPool.GraphMinor.GM12.Section4ProtectedMotion
import LeanPool.GraphMinor.GM12.Section4RadialResize
import LeanPool.GraphMinor.Surface.PushOff
import LeanPool.GraphMinor.GM12.Section4CollarRadius

/-!
# Matching nested discs and adjusting boundary points

XII (4.3), claim (7), page 251, uses a homeomorphism carrying the
source edge neighborhoods to their prescribed discs. For three
nested discs, join the two collars into one coordinate map and
change the radius to carry the inner disc onto the middle disc.
The resulting homeomorphism fixes the exterior of the outer disc.
A second construction extends an orientation preserving circle map
across a collar, preserving the middle disc and fixing the exterior.

-/

public section

namespace GraphMinor.GM12

open Set Metric Surface Topology
open scoped Pointwise

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- A continuous injective map on a compact set has a continuous inverse on its image. -/
private theorem exists_inverse_on {K : Set ℂ} (hK : IsCompact K) {c : ℂ → S}
  (hc : ContinuousOn c K) (hi : InjOn c K) :
    ∃ c' : S → ℂ, ContinuousOn c' (c '' K) ∧ MapsTo c' (c '' K) K ∧ LeftInvOn c' c K
      ∧ RightInvOn c' c (c '' K) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → S := K.domRestrict c
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp hc
  have hfi : Function.Injective f := fun a b he => Subtype.ext (hi a.2 b.2 he)
  have hem := hf.isClosedEmbedding hfi
  let e : K ≃ₜ range f := hem.isEmbedding.toHomeomorph
  have hrange : range f = c '' K := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let c' : S → ℂ := fun x => if hx : x ∈ range f then (e.symm ⟨x, hx⟩).1 else 0
  have hval : ∀ z (hz : z ∈ K), c' (c z) = z := fun z hz => by
    have hx : c z ∈ range f := ⟨⟨z, hz⟩, rfl⟩
    change (if hx : c z ∈ range f then (e.symm ⟨c z, hx⟩).1 else 0) = z
    rw [dite_eq_left hx]
    have : (⟨c z, hx⟩ : range f) = e ⟨z, hz⟩ := rfl
    rw [this, e.symm_apply_apply]
  refine ⟨c', ?_, ?_, fun z hz => hval z hz, ?_⟩
  · rw [← hrange, continuousOn_iff_continuous_domRestrict]
    have : (range f).domRestrict c' = fun x : range f => (e.symm x).1 := by
      funext x
      change (if hx : x.1 ∈ range f then (e.symm ⟨x.1, hx⟩).1 else 0) = _
      rw [dite_eq_left x.2]
    rw [this]
    exact continuous_subtype_val.comp e.symm.continuous
  · rintro _ ⟨z, hz, rfl⟩
    rw [hval z hz]
    exact hz
  · rintro _ ⟨z, hz, rfl⟩
    show c (c' (c z)) = c z
    rw [hval z hz]

/-- If `A` lies inside `B` and `B` inside `E`, a homeomorphism of the surface that is the identity
off `E` carries `A` onto `B`. We join a collar of `A` in `B` with a collar of `B` in `E`, and change
the radius. -/
theorem exists_disc_onto_nested (hman : ∀ x : S, IsManifoldPoint x) {A B E : Set S}
  (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hE : IsClosedDisc E) (hAB : A ⊆ B \ discBd B)
    (hBE : B ⊆ E \ discBd E) :
    ∃ e : S ≃ₜ S, e '' A = B ∧ ∀ x, x ∉ E → e x = x := by
  obtain ⟨pA⟩ := hA.isOArc_discBd
  obtain ⟨c₁, c₁', hcc₁, -, hm₁, hm₁', hl₁, hr₁, hin₁, hs₁, -⟩ := exists_disc_collar hA hB hAB pA
  have hi₁ : InjOn c₁ (closedBall 0 2) := hl₁.injOn
  have hB₁ : c₁ '' closedBall 0 2 = B :=
    (hm₁.image_subset).antisymm fun x hx => ⟨_, hm₁' hx, hr₁ hx⟩
  -- The outer circle of the first collar parametrizes `bd B`.
  have hS2 : ∀ w : Circle, ((2 : ℝ) : ℂ) * w ∈ sphere (0 : ℂ) 2 := fun w => by
    rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, Complex.norm_real]
    norm_num
  let u : Circle → discBd B := fun w => ⟨c₁ (((2 : ℝ) : ℂ) * w), hs₁ ▸ mem_image_of_mem c₁ (hS2 w)⟩
  have huc : Continuous u := by
    refine Continuous.subtype_mk (hcc₁.comp_continuous (by
      exact continuous_const.mul continuous_induced_dom) fun w => sphere_subset_closedBall
        (hS2 w)) _
  have hui : Function.Injective u := fun w w' he => by
    have h1 := hi₁ (sphere_subset_closedBall (hS2 w)) (sphere_subset_closedBall (hS2 w'))
      (congrArg Subtype.val he)
    exact Circle.ext (mul_left_cancel₀ (by norm_num) h1)
  have hus : Function.Surjective u := fun x => by
    obtain ⟨z, hz, he⟩ : x.1 ∈ c₁ '' sphere 0 2 := by rw [hs₁]; exact x.2
    have hzn : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
    refine ⟨unitOf z hz0, Subtype.ext ?_⟩
    change c₁ (((2 : ℝ) : ℂ) * unitOf z hz0) = x.1
    rw [← hzn, norm_mul_unitOf, he]
  let pB : Circle ≃ₜ discBd B := huc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective u ⟨hui, hus⟩)
  have hpB : ∀ w : Circle, (pB w).1 = c₁ (((2 : ℝ) : ℂ) * w) := fun _ => rfl
  obtain ⟨c₂, c₂', hcc₂, -, hm₂, hm₂', hl₂, hr₂, hin₂, hs₂, hp₂⟩ := exists_disc_collar hB hE hBE pB
  have hi₂ : InjOn c₂ (closedBall 0 2) := hl₂.injOn
  have hE₂ : c₂ '' closedBall 0 2 = E :=
    (hm₂.image_subset).antisymm fun x hx => ⟨_, hm₂' hx, hr₂ hx⟩
  have hcompat : ∀ z : ℂ, ‖z‖ = 2 → c₁ z = c₂ (collarOuterStep z) := by
    intro z hzn
    have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
    have h1 : collarOuterStep z = (unitOf z hz0 : ℂ) := by
      rw [collarOuterStep_two hzn, coe_unitOf, hzn, Complex.real_smul]
      push_cast
      ring
    rw [h1, hp₂, hpB, ← hzn, norm_mul_unitOf]
  obtain ⟨c, hcc, hci, hcA, hcB, hcE, hcs⟩ := exists_joined_collar_coordinates c₁ c₂ hcc₁ hi₁ hcc₂
    hi₂ hin₁ hB₁ hin₂ hE₂ hs₂ hcompat
  let sc : ℂ → ℂ := fun z => (3 / 2 : ℝ) • z
  have hsc : Continuous sc := by fun_prop
  have hsci : Function.Injective sc := smul_right_injective ℂ (by norm_num)
  have hball : ∀ r : ℝ, sc '' closedBall 0 r = closedBall 0 (3 / 2 * r) := fun r => by
    change (3 / 2 : ℝ) • closedBall (0 : ℂ) r = _
    have := _root_.smul_closedBall' (by norm_num : (3 / 2 : ℝ) ≠ 0) (0 : ℂ) r
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using this
  have hsph : sc '' sphere 0 2 = sphere 0 3 := by
    change (3 / 2 : ℝ) • sphere (0 : ℂ) 2 = _
    have := _root_.smul_sphere' (by norm_num : (3 / 2 : ℝ) ≠ 0) (0 : ℂ) 2
    have h2 : |(3 / 2 : ℝ)| * 2 = 3 := by rw [abs_of_pos (by norm_num)]; norm_num
    simpa only [smul_zero, Real.norm_eq_abs, h2] using this
  let d : ℂ → S := fun z => c (sc z)
  have hsub : MapsTo sc (closedBall 0 2) (closedBall 0 3) := fun z hz => by
    have : sc z ∈ sc '' closedBall 0 2 := mem_image_of_mem sc hz
    rw [hball] at this
    convert this using 2
    norm_num
  have hdc : ContinuousOn d (closedBall 0 2) := hcc.comp hsc.continuousOn hsub
  have hdi : InjOn d (closedBall 0 2) := fun z hz w hw he => hsci (hci (hsub hz) (hsub hw) he)
  have hdimg : ∀ r r' : ℝ, 3 / 2 * r = r' → d '' closedBall 0 r = c '' closedBall 0 r'
    := fun r r' he => by
    rw [← he, ← hball, image_image]
  have hdE : d '' closedBall 0 2 = E := by
    rw [hdimg 2 3 (by norm_num), hcE]
  have hdA : d '' closedBall 0 (2 / 3) = A := by
    rw [hdimg (2 / 3) 1 (by norm_num), hcA]
  have hdB : d '' closedBall 0 (4 / 3) = B := by
    rw [hdimg (4 / 3) 2 (by norm_num), hcB]
  have hds : d '' sphere 0 2 = discBd E := by
    rw [← hcs, ← hsph, image_image]
  obtain ⟨d', hdc', hdm', hdl, hdr⟩ := exists_inverse_on (isCompact_closedBall 0 2) hdc hdi
  rw [hdE] at hdc' hdm' hdr
  have hdm : MapsTo d (closedBall 0 2) E := fun z hz => hdE ▸ mem_image_of_mem d hz
  obtain ⟨Θ, hΘfix, -, hΘball⟩ := exists_radial_disc_resize
    (show (0 : ℝ) < 2 / 3 by norm_num) (show (2 / 3 : ℝ) < 3 / 2 by norm_num) (show
      (0 : ℝ) < 4 / 3 by norm_num) (show (4 / 3 : ℝ) < 3 / 2 by norm_num)
  obtain ⟨e, hec, hefix⟩ := exists_homeomorph_of_collar hman hE hdc hdc' hdm hdm' hdl hdr hds Θ
    hΘfix
  refine ⟨e, ?_, hefix⟩
  rw [← hdA, image_image, ← hdB, ← hΘball, image_image]
  exact image_congr fun z hz => hec z (closedBall_subset_closedBall (by norm_num) hz)

/-- A twist of a collar of `B` in `E`. It keeps `B`, it is the identity off `E`, and on `bd B` it
acts by a chosen homeomorphism of the circle that keeps the orientation. -/
theorem exists_boundary_twist (hman : ∀ x : S, IsManifoldPoint x) {B E : Set S}
  (hB : IsClosedDisc B) (hE : IsClosedDisc E) (hBE : B ⊆ E \ discBd E) (p : Circle ≃ₜ discBd B)
    {h : Circle ≃ₜ Circle} (hh : PreservesCircleOrientation h) :
    ∃ e : S ≃ₜ S, e '' B = B ∧ (∀ w, e (p w).1 = (p (h w)).1) ∧ ∀ x, x ∉ E → e x = x := by
  obtain ⟨c, c', hcc, hcc', hm, hm', hl, hr, hin, hs, hp⟩ := exists_disc_collar hB hE hBE p
  obtain ⟨Θ, hΘfix, hΘn, hΘc⟩ := exists_twist hh
  obtain ⟨e, hec, hefix⟩ := exists_homeomorph_of_collar hman hE hcc hcc' hm hm' hl hr hs Θ hΘfix
  have hΘb : Θ '' closedBall 0 1 = closedBall 0 1 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_closedBall_zero_iff, hΘn]
      exact mem_closedBall_zero_iff.mp hw
    · intro hz
      refine ⟨Θ.symm z, ?_, Θ.apply_symm_apply z⟩
      rw [mem_closedBall_zero_iff, ← hΘn, Θ.apply_symm_apply]
      exact mem_closedBall_zero_iff.mp hz
  have hsub : closedBall (0 : ℂ) 1 ⊆ closedBall 0 2 := closedBall_subset_closedBall (by norm_num)
  refine ⟨e, ?_, fun w => ?_, hefix⟩
  · rw [← hin, image_image]
    conv_rhs => rw [← hΘb, image_image]
    exact image_congr fun z hz => hec z (hsub hz)
  · have hw : (w : ℂ) ∈ closedBall (0 : ℂ) 2 := by
      rw [mem_closedBall_zero_iff, Circle.norm_coe]
      norm_num
    rw [← hp, hec _ hw, hΘc, hp]

end GraphMinor.GM12
