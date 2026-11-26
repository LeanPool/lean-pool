/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Ring
public import LeanPool.GraphMinor.Surface.PasteModel
public import LeanPool.GraphMinor.Surface.Cap
public import LeanPool.GraphMinor.Surface.SurfacePull
public import LeanPool.GraphMinor.Surface.CutComp

/-!
# Removing open discs from a surface

Let `E` be a closed disc in a surface whose boundary lies in the interior of the surface. The
surface without the inside of `E` is a
surface, and the boundary of `E` is a new cuff (`remove_disc`). At a point of the boundary of `E`, a
small piece of the collar from
`exists_disc_collar` is a closed disc that is a neighbourhood of the point, which gives the chart.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

variable {R : Type} [TopologicalSpace R]

/-- A subset of a space that contains an open set around a point has the same local structure there.
-/
theorem sub_open_iff {A W : Set R} (hW : IsOpen W) (hs : W ⊆ A) {y : A} (hy : y.1 ∈ W) :
    (IsInteriorPoint y ↔ IsInteriorPoint y.1) ∧ (IsManifoldPoint y.1 → IsManifoldPoint y) := by
  have hW' : IsOpen (Subtype.val ⁻¹' W : Set A) := hW.preimage continuous_subtype_val
  let e : (Subtype.val ⁻¹' W : Set A) ≃ₜ W :=
    { toFun := fun z => ⟨z.1.1, z.2⟩
      invFun := fun w => ⟨⟨w.1, hs w.2⟩, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h1 := isInteriorPoint_sub hW' (x := ⟨y, hy⟩)
  have h2 := isInteriorPoint_sub hW (x := ⟨y.1, hy⟩)
  have h3 := isInteriorPoint_homeomorph_iff e ⟨y, hy⟩
  refine ⟨h1.symm.trans (h3.symm.trans h2), fun hm => ?_⟩
  have h4 : IsManifoldPoint (⟨y.1, hy⟩ : W) := isManifoldPoint_sub hW hm
  have h5 : IsManifoldPoint (⟨y, hy⟩ : (Subtype.val ⁻¹' W : Set A)) :=
    (isManifoldPoint_iff_of_isOpenEmbedding e.isOpenEmbedding).mp h4
  exact isManifoldPoint_of_isOpenEmbedding hW'.isOpenEmbedding_subtypeVal h5

/-- A closed disc on one side of a circle in the plane. -/
theorem exists_half_disc {w : ℂ} (hw : ‖w‖ = 1) :
    ∃ (f : ℂ → ℂ) (Q : Set ℂ), ContinuousOn f Q ∧ InjOn f Q ∧ IsCompact Q ∧ IsClosedDisc Q ∧
      (0 : ℂ) ∈ discBd Q ∧ f 0 = w ∧ (∀ ζ ∈ Q, 1 ≤ ‖f ζ‖ ∧ ‖f ζ‖ ≤ 3 / 2) ∧
      ∀ᶠ z in 𝓝 w, 1 ≤ ‖z‖ → z ∈ f '' Q := by
  have hL : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  obtain ⟨hQ, hQb⟩ := isClosedDisc_rect hL (show (-1 : ℝ) < 1 by norm_num)
  have hne : w ≠ 0 := by
    rintro rfl
    simp at hw
  refine ⟨fun ζ => w * Complex.exp ζ, Icc 0 (Real.log (3 / 2)) ×ℂ Icc (-1) 1, by fun_prop, ?_,
    isCompact_Icc.reProdIm isCompact_Icc, hQ, ?_, by simp, ?_, ?_⟩
  · intro x hx y hy he
    have h3 := Real.pi_gt_three
    have hx2 := hx.2
    have hy2 := hy.2
    exact Complex.exp_inj_of_neg_pi_lt_of_le_pi (by linarith [hx2.1]) (by linarith [hx2.2])
      (by linarith [hy2.1]) (by linarith [hy2.2])
      (mul_left_cancel₀ hne he)
  · rw [hQb, frontier, Complex.interior_reProdIm, interior_Icc, interior_Icc,
      (isCompact_Icc.reProdIm isCompact_Icc).isClosed.closure_eq]
    refine ⟨⟨?_, ?_⟩, fun h => ?_⟩
    · simp [hL.le]
    · simp
    · have := h.1
      simp at this
  · intro ζ hζ
    have h1 := hζ.1
    rw [norm_mul, hw, one_mul, Complex.norm_exp]
    constructor
    · exact Real.one_le_exp h1.1
    · calc Real.exp ζ.re ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr h1.2
        _ = 3 / 2 := Real.exp_log (by norm_num)
  · have h1 : ContinuousAt (fun z : ℂ => z / w) w := by fun_prop
    have h2 : ContinuousAt (fun z : ℂ => Complex.arg (z / w)) w := by
      refine ContinuousAt.comp (f := fun z : ℂ => z / w) (g := Complex.arg) ?_ h1
      apply Complex.continuousAt_arg
      rw [div_self hne]
      exact Complex.one_mem_slitPlane
    have h3 : ∀ᶠ z in 𝓝 w, ‖z‖ < 3 / 2 := by
      refine (continuous_norm.tendsto w).eventually (gt_mem_nhds ?_)
      rw [hw]
      norm_num
    have h4 : ∀ᶠ z in 𝓝 w, |Complex.arg (z / w)| < 1 := by
      have h5 : ContinuousAt (fun z : ℂ => |Complex.arg (z / w)|) w := h2.abs
      refine h5.eventually (gt_mem_nhds ?_)
      simp [div_self hne]
    have h6 : ∀ᶠ z in 𝓝 w, z ≠ 0 := eventually_ne_nhds hne
    filter_upwards [h3, h4, h6] with z hz hz' hz0 hz1
    have hdiv : z / w ≠ 0 := div_ne_zero hz0 hne
    refine ⟨Complex.log (z / w), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Complex.log_re, norm_div, hw, div_one]
      exact Real.log_nonneg hz1
    · rw [Complex.log_re, norm_div, hw, div_one]
      exact Real.log_le_log (by linarith) hz.le
    · change (Complex.log (z / w)).im ∈ Icc (-1 : ℝ) 1
      rw [Complex.log_im]
      exact ⟨by linarith [(abs_lt.mp hz').1], by linarith [(abs_lt.mp hz').2]⟩
    · change w * Complex.exp (Complex.log (z / w)) = z
      rw [Complex.exp_log hdiv]
      field_simp

/-- At a point of the boundary of a disc, there is a closed disc on the outer side that is a
neighbourhood of the point there. -/
theorem exists_outer_disc (hR : IsSurface R) {E : Set R} (hE : IsClosedDisc E)
  (hint : ∀ x ∈ discBd E, IsInteriorPoint x) {x : R} (hx : x ∈ discBd E) :
    ∃ G, IsClosedDisc G ∧ x ∈ discBd G ∧ Disjoint G (discInt E) ∧ ∀ᶠ y in 𝓝 x, y ∉ discInt E
      → y ∈ G := by
  have ht2 : T2Space R := hR.2.1
  have hman := hR.2.2
  obtain ⟨Δ', hΔ', hin, -⟩ := exists_disc_around hman hE hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hE.isOArc_discBd
  obtain ⟨c, c', hcc, hc'c, hmc, hmc', hl, hr, hcE, hcb, hcp⟩ := exists_disc_collar hE hΔ' hin p
  let w₀ : Circle := p.symm ⟨x, hx⟩
  have hcw : c w₀ = x := by rw [hcp, p.apply_symm_apply]
  have hw : ‖(w₀ : ℂ)‖ = 1 := Circle.norm_coe w₀
  obtain ⟨f, Q, hfc, hfi, hQc, hQ, hQ0, hf0, hfn, hev⟩ := exists_half_disc hw
  have hin2 : ∀ ζ ∈ Q, f ζ ∈ closedBall (0 : ℂ) 2 := fun ζ hζ => by
    have := (hfn ζ hζ).2
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hcont : ContinuousOn (fun ζ => c (f ζ)) Q := hcc.comp hfc hin2
  have hinj : InjOn (fun ζ => c (f ζ)) Q := fun a ha b hb he => hfi ha hb (by
    rw [← hl (hin2 a ha), ← hl (hin2 b hb)]
    exact congrArg c' he)
  have : Nonempty ℂ := ⟨0⟩
  obtain ⟨hG, hGb⟩ := isClosedDisc_image_injOn hQ hQc hcont hinj
  have hball1 : ∀ z ∈ closedBall (0 : ℂ) 1, z ∈ closedBall (0 : ℂ) 2 := fun z hz
    => closedBall_subset_closedBall (by norm_num) hz
  have hEout : ∀ z ∈ closedBall (0 : ℂ) 2, c z ∈ E → ‖z‖ ≤ 1 := fun z hz hmem => by
    rw [← hcE] at hmem
    obtain ⟨u, hu, he⟩ := hmem
    have h2 : u = z := by
      rw [← hl (hball1 u hu), he, hl hz]
    have : ‖u‖ ≤ 1 := by simpa using hu
    rwa [h2] at this
  have hbdc : ∀ z : ℂ, ‖z‖ = 1 → c z ∈ discBd E := fun z hz => by
    have h1 : c ((⟨z, by simpa [Submonoid.unitSphere] using hz⟩ : Circle) : ℂ) = _ := hcp _
    exact h1 ▸ (p _).2
  refine ⟨_, hG, ?_, ?_, ?_⟩
  · rw [hGb]
    refine ⟨0, hQ0, ?_⟩
    change c (f 0) = x
    rw [hf0, hcw]
  · rw [disjoint_left]
    rintro _ ⟨ζ, hζ, rfl⟩ hz
    have h1 := hEout _ (hin2 ζ hζ) hz.1
    have h2 := hfn ζ hζ
    exact hz.2 (hbdc _ (le_antisymm h1 h2.1))
  · have hxΔ' : x ∈ Δ' \ discBd Δ' := hin (discBd_subset E hx)
    have hopen := hΔ'.isOpen_discInt hman
    have hnΔ : Δ' ∈ 𝓝 x := mem_of_superset (hopen.mem_nhds hxΔ') (discInt_subset Δ')
    have hca : ContinuousAt c' x := hc'c.continuousAt hnΔ
    have hc'x : c' x = w₀ := by
      rw [← hcw]
      exact hl (hball1 _ (by simp))
    rw [← hf0] at hev
    have htend : Tendsto c' (𝓝 x) (𝓝 (f 0)) := by
      rw [hf0, ← hc'x]
      exact hca
    filter_upwards [htend.eventually hev, hnΔ] with y hy hyΔ hyn
    have hcy : c (c' y) = y := hr hyΔ
    have hz2 := hmc' hyΔ
    have hn1 : 1 ≤ ‖c' y‖ := by
      by_contra hlt
      push Not at hlt
      apply hyn
      refine ⟨hcy ▸ hcE ▸ mem_image_of_mem _ (show c' y ∈ closedBall (0 : ℂ) 1 by simpa using
        hlt.le), fun hb => ?_⟩
      have h5 : c (p.symm ⟨y, hb⟩) = y := by rw [hcp, p.apply_symm_apply]
      have h6 : c' y = p.symm ⟨y, hb⟩ := by
        conv_lhs => rw [← h5]
        exact hl (hball1 _ (by simp))
      rw [h6] at hlt
      simp at hlt
    obtain ⟨ζ, hζ, he⟩ := hy hn1
    exact ⟨ζ, hζ, by change c (f ζ) = y; rw [he, hcy]⟩

/-- Removing the inside of one closed disc from a surface. -/
theorem remove_disc (hR : IsSurface R) {E : Set R} (hE : IsClosedDisc E)
  (hint : ∀ x ∈ discBd E, IsInteriorPoint x) :
    IsClosed (discInt E)ᶜ ∧ IsSurface ↥(discInt E)ᶜ ∧ bd ↥(discInt E)ᶜ = Subtype.val ⁻¹'
      (bd R ∪ discBd E) := by
  have ht2 : T2Space R := hR.2.1
  have hcR : CompactSpace R := hR.1
  have hman := hR.2.2
  have hop := hE.isOpen_discInt hman
  have hcl : IsClosed (discInt E)ᶜ := hop.isClosed_compl
  have hEc : IsClosed E := hE.isClosed
  have hne : Nonempty ↥(discInt E)ᶜ := by
    obtain ⟨φ⟩ := id hE.isOArc_discBd
    exact ⟨⟨_, fun h => h.2 (φ 1).2⟩⟩
  have hEsub : Eᶜ ⊆ (discInt E)ᶜ := fun x hx h => hx h.1
  have hjc : IsClosedEmbedding (Subtype.val : ↥(discInt E)ᶜ → R) := hcl.isClosedEmbedding_subtypeVal
  have hlocal : ∀ {x : ↥(discInt E)ᶜ}, x.1 ∈ discBd E → IsManifoldPoint x ∧ x ∈ bd ↥(discInt E)ᶜ
    := by
    intro x hx
    obtain ⟨G, hG, hxG, hd, hev⟩ := exists_outer_disc hR hE hint hx
    have hGs : G ⊆ range (Subtype.val : ↥(discInt E)ᶜ → R) := by
      rw [Subtype.range_val]
      exact fun y hy => disjoint_left.mp hd hy
    have hcS : CompactSpace ↥(discInt E)ᶜ := isCompact_iff_compactSpace.mp hcl.isCompact
    obtain ⟨hG', hGb⟩ := isClosedDisc_preimage hjc hG hGs
    have hnb : (Subtype.val ⁻¹' G : Set ↥(discInt E)ᶜ) ∈ 𝓝 x := by
      rw [nhds_subtype_eq_comap]
      refine mem_comap.mpr ⟨_, hev, fun y hy => ?_⟩
      exact hy y.2
    exact ⟨isManifoldPoint_of_disc hG' hnb, mem_bd_of_disc hnb (hGb ▸ hxG)⟩
  have hoff : ∀ {x : ↥(discInt E)ᶜ}, x.1 ∉ discBd E → x.1 ∈ Eᶜ := fun {x} hx hxE => x.2 ⟨hxE, hx⟩
  have hsurf : IsSurface ↥(discInt E)ᶜ := by
    refine ⟨isCompact_iff_compactSpace.mp hcl.isCompact, inferInstance, fun x => ?_⟩
    by_cases hx : x.1 ∈ discBd E
    · exact (hlocal hx).1
    · exact (sub_open_iff hEc.isOpen_compl hEsub (hoff hx)).2 (hman _)
  refine ⟨hcl, hsurf, ?_⟩
  ext x
  by_cases hx : x.1 ∈ discBd E
  · exact ⟨fun _ => .inr hx, fun _ => (hlocal hx).2⟩
  · have h1 := (sub_open_iff hEc.isOpen_compl hEsub (hoff hx)).1
    constructor
    · intro h
      exact .inl fun h2 => h (h1.mpr h2)
    · rintro (h | h)
      · exact fun h2 => h (h1.mp h2)
      · exact absurd h hx

end GraphMinor.Surface
