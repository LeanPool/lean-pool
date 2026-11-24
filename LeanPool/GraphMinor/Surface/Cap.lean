/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.OpenDisc
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Small discs on the outside of a closed disc

Let `D` be a closed disc in a surface and let `L` be a short line of its boundary. In this file we
find a closed disc `T` outside `D` that meets `D` exactly in `L` (`exists_cap`). So the boundary of
`D` is flat near `L`, and `D ∪ T` is a closed disc that has the middle of `L` in its inside. This
is the tool for collars of cuffs in `Collar.lean`.

The reason is the Schoenflies theorem. A thin strip of `D` along `L` is a closed disc in a plane
chart,
so a homeomorphism of the plane turns it into a rectangle, with `L` on the top side. The rectangle
straight above `L` is the wanted disc, when it is thin enough.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

universe u

/-- A compact convex subset of the plane with interior is a closed disc, and its boundary as a disc
is
its frontier. -/
theorem isClosedDisc_of_convex {K : Set ℂ} (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (hb : Bornology.IsBounded K) (hcl : IsClosed K) :
    IsClosedDisc K ∧ discBd K = frontier K := by
  obtain ⟨Ψ, -, h2, h3⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  rw [hcl.closure_eq] at h2
  have hK : K = Ψ.symm '' closedBall 0 1 := by
    rw [← h2, image_image]
    simp
  have hF : frontier K = Ψ.symm '' sphere 0 1 := by
    rw [← h3, image_image]
    simp
  obtain ⟨h4, h5⟩ := isClosedDisc_closedBall.1.image (f := Ψ.symm) (f' := Ψ)
    Ψ.symm.continuous.continuousOn Ψ.continuous.continuousOn fun z _ => Ψ.apply_symm_apply z
  rw [isClosedDisc_closedBall.2] at h5
  rw [hK, hF] at *
  exact ⟨h4, h5⟩

/-- A rectangle in the plane. -/
theorem isClosedDisc_rect {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsClosedDisc (Icc a b ×ℂ Icc c d) ∧ discBd (Icc a b ×ℂ Icc c d) = frontier (Icc a b ×ℂ Icc c d)
      := by
  have hconv : Convex ℝ (Icc a b ×ℂ Icc c d) :=
    ((convex_Icc a b).is_linear_preimage (f := Complex.reLm) Complex.reLm.isLinear).inter
      ((convex_Icc c d).is_linear_preimage (f := Complex.imLm) Complex.imLm.isLinear)
  refine isClosedDisc_of_convex hconv ?_ (isCompact_Icc.reProdIm isCompact_Icc).isBounded
    (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  have hopen : IsOpen (Ioo a b ×ℂ Ioo c d) :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  refine ⟨⟨(a + b) / 2, (c + d) / 2⟩, mem_interior.mpr ⟨Ioo a b ×ℂ Ioo c d, ?_, hopen, ?_⟩⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hz
    exact Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩
  · exact Complex.mem_reProdIm.mpr ⟨⟨by simp only; linarith, by simp only; linarith⟩,
      ⟨by simp only; linarith, by simp only; linarith⟩⟩

/-- The frontier of a rectangle contains its top side. -/
theorem top_subset_frontier_rect {a b c d : ℝ} {z : ℂ} (hz : z.re ∈ Icc a b) (hd : z.im = d)
    (hcd : c ≤ d) : z ∈ frontier (Icc a b ×ℂ Icc c d) := by
  have hcl : IsClosed (Icc a b ×ℂ Icc c d) := (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  rw [hcl.frontier_eq]
  refine ⟨Complex.mem_reProdIm.mpr ⟨hz, by rw [hd]; exact ⟨hcd, le_rfl⟩⟩, fun hi => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hi
  have h1 : z + ((ρ / 2 : ℝ) : ℂ) * Complex.I ∈ ball z ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have h2 := (Complex.mem_reProdIm.mp (interior_subset (hball h1))).2.2
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_one, zero_mul, add_zero] at h2
  linarith

/-- The frontier of a rectangle contains its bottom side. -/
theorem bot_subset_frontier_rect {a b c d : ℝ} {z : ℂ} (hz : z.re ∈ Icc a b) (hc : z.im = c)
    (hcd : c ≤ d) : z ∈ frontier (Icc a b ×ℂ Icc c d) := by
  have hcl : IsClosed (Icc a b ×ℂ Icc c d) := (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  rw [hcl.frontier_eq]
  refine ⟨Complex.mem_reProdIm.mpr ⟨hz, by rw [hc]; exact ⟨le_rfl, hcd⟩⟩, fun hi => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hi
  have h1 : z + ((-(ρ / 2) : ℝ) : ℂ) * Complex.I ∈ ball z ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    linarith
  have h2 := (Complex.mem_reProdIm.mp (interior_subset (hball h1))).2.1
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_one, zero_mul, add_zero] at h2
  linarith

/-- The Schoenflies theorem between two `O`-arcs of the plane. -/
theorem exists_plane_homeomorph {F₀ F : Set ℂ} (hF₀ : Nonempty (Circle ≃ₜ F₀))
    (hF : Nonempty (Circle ≃ₜ F)) {f f' : ℂ → ℂ} (m : BdMatch F₀ F f f') :
    ∃ Ψ : ℂ ≃ₜ ℂ, EqOn Ψ f F₀ ∧ Ψ '' closedInner F₀ = closedInner F := by
  obtain ⟨φ⟩ := id hF₀
  obtain ⟨o⟩ := oArc_sphere
  obtain ⟨h₁, k₁, m₁, -⟩ := exists_bdMatch (o.symm.trans φ)
  obtain ⟨G₁, hG₁⟩ := exists_homeomorph_of_bdMatch hF₀ m₁
  have hm₂ := m₁.trans m
  obtain ⟨G₂, hG₂⟩ := exists_homeomorph_of_bdMatch hF hm₂
  have hG₁im : G₁ '' sphere 0 1 = F₀ := by
    rw [image_congr hG₁]
    exact m₁.image_eq
  have hG₂im : G₂ '' sphere 0 1 = F := by
    rw [image_congr hG₂]
    exact hm₂.image_eq
  refine ⟨G₁.symm.trans G₂, fun z hz => ?_, ?_⟩
  · have h1 := m₁.2.1 hz
    have h2 : G₁ (k₁ z) = z := by
      rw [hG₁ h1]
      exact m₁.2.2.2.1 hz
    change G₂ (G₁.symm z) = f z
    rw [← h2, G₁.symm_apply_apply, hG₂ h1]
    have h3 : h₁ (k₁ z) = z := m₁.2.2.2.1 hz
    change f (h₁ (k₁ z)) = f (G₁ (k₁ z))
    rw [h3, h2]
  · rw [← image_closedBall_of_homeomorph G₁ hF₀ hG₁im, ← image_closedBall_of_homeomorph G₂ hF hG₂im,
      image_image]
    exact image_congr fun z _ => by simp

theorem bdMatch_of_leftInvOn {A : Set ℂ} {f f' : ℂ → ℂ} (hf : ContinuousOn f A)
    (hf' : ContinuousOn f' (f '' A)) (hl : LeftInvOn f' f A) : BdMatch A (f '' A) f f' := by
  refine ⟨mapsTo_image f A, ?_, hl, ?_, hf, hf'⟩
  · rintro _ ⟨z, hz, rfl⟩
    rwa [hl hz]
  · rintro _ ⟨z, hz, rfl⟩
    show f (f' (f z)) = f z
    rw [hl hz]

variable {S : Type u} [TopologicalSpace S]

/-- The point of the unit circle at angle `θ`. -/
noncomputable def cis' (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

theorem continuous_cis' : Continuous cis' := by
  unfold cis'
  fun_prop

theorem norm_cis' (θ : ℝ) : ‖cis' θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

theorem cis'_mem_closedBall (θ : ℝ) : cis' θ ∈ closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall_zero_iff, norm_cis']

theorem cis'_mem_sphere (θ : ℝ) : cis' θ ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_cis']

theorem cis'_injOn : InjOn cis' (Ioo (-Real.pi) Real.pi) := by
  intro x hx y hy he
  have h1 := congrArg Complex.log he
  simp only [cis'] at h1
  have hmem : ∀ t : ℝ, t ∈ Ioo (-Real.pi) Real.pi → Complex.log (Complex.exp (t * Complex.I))
    = t * Complex.I :=
    fun t ht => Complex.log_exp (by simpa using ht.1) (by simpa using ht.2.le)
  rw [hmem x hx, hmem y hy] at h1
  have h2 := congrArg Complex.im h1
  simpa using h2

/-- The part of the boundary of a closed disc between two angles of a chart. -/
noncomputable def angleArc (g : ℂ → S) (α β : ℝ) : Set S := (fun θ => g (cis' θ)) '' Icc α β

/-- The arc between two angles is a line of the boundary. -/
theorem IsChart.isLine_angleArc [T2Space S] {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g)
    {α β : ℝ} (hα : -Real.pi < α) (hαβ : α < β) (hβ : β < Real.pi) :
    IsLineWithEnds (angleArc g α β) (g (cis' α)) (g (cis' β)) := by
  let a : unitInterval → S := fun t => g (cis' (α + t.1 * (β - α)))
  have hsub : ∀ t : unitInterval, α + t.1 * (β - α) ∈ Icc α β := fun t => by
    have h1 := t.2.1
    have h2 := t.2.2
    constructor <;> nlinarith
  have ha : IsArcMap a := by
    refine ⟨c.gc.comp_continuous (continuous_cis'.comp (by fun_prop)) fun t
      => cis'_mem_closedBall _,
      fun s t he => ?_⟩
    have h1 := c.injOn (cis'_mem_closedBall _) (cis'_mem_closedBall _) he
    have h2 := cis'_injOn ⟨hα.trans_le (hsub s).1, (hsub s).2.trans_lt hβ⟩
      ⟨hα.trans_le (hsub t).1, (hsub t).2.trans_lt hβ⟩ h1
    have h3 : s.1 * (β - α) = t.1 * (β - α) := by linarith
    exact Subtype.ext (mul_right_cancel₀ (sub_pos.mpr hαβ).ne' h3)
  have hr : range a = angleArc g α β := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, hsub t, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩
      have hpos := sub_pos.mpr hαβ
      refine ⟨⟨(θ - α) / (β - α), div_nonneg (by linarith [hθ.1]) hpos.le,
        (div_le_one hpos).mpr (by linarith [hθ.2])⟩, ?_⟩
      change g (cis' (α + (θ - α) / (β - α) * (β - α))) = _
      rw [div_mul_cancel₀ _ hpos.ne']
      congr 2
      ring
  have := ha.isLineWithEnds
  rw [hr] at this
  have h0 : a 0 = g (cis' α) := by simp [a]
  have h1 : a 1 = g (cis' β) := by simp [a]
  rwa [h0, h1] at this

theorem IsChart.angleArc_subset {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) (α β : ℝ) :
    angleArc g α β ⊆ discBd D := by
  rw [← c.g_sphere]
  rintro _ ⟨θ, -, rfl⟩
  exact ⟨_, cis'_mem_sphere θ, rfl⟩

/-- A little room around the angles of an arc that lies in an open set. -/
theorem IsChart.exists_margin {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) {W : Set S}
    (hW : IsOpen W) {α β : ℝ} (hα : -Real.pi < α) (hαβ : α ≤ β) (hβ : β < Real.pi)
    (hsub : angleArc g α β ⊆ W) :
    ∃ η > 0, -Real.pi < α - η ∧ β + η < Real.pi ∧ ∃ O : Set ℂ, IsOpen O ∧
      (∀ θ ∈ Icc (α - η) (β + η), cis' θ ∈ O) ∧ ∀ z ∈ O, ‖z‖ ≤ 1 → g z ∈ W := by
  obtain ⟨O, hO, hOe⟩ := continuousOn_iff'.mp c.gc W hW
  have hK : IsCompact (cis' '' Icc α β) := isCompact_Icc.image continuous_cis'
  have hKO : cis' '' Icc α β ⊆ O := by
    rintro _ ⟨θ, hθ, rfl⟩
    have h1 : cis' θ ∈ g ⁻¹' W ∩ closedBall 0 1 := ⟨hsub ⟨θ, hθ, rfl⟩, cis'_mem_closedBall θ⟩
    rw [hOe] at h1
    exact h1.1
  have hpre : IsOpen (cis' ⁻¹' O ∩ Ioo (-Real.pi) Real.pi) :=
    (hO.preimage continuous_cis').inter isOpen_Ioo
  have hsubI : Icc α β ⊆ cis' ⁻¹' O ∩ Ioo (-Real.pi) Real.pi := fun θ hθ =>
    ⟨hKO ⟨θ, hθ, rfl⟩, hα.trans_le hθ.1, hθ.2.trans_lt hβ⟩
  obtain ⟨δ, hδ, hth⟩ := isCompact_Icc.exists_thickening_subset_open hpre hsubI
  have hthick : ∀ θ ∈ Icc (α - δ / 2) (β + δ / 2), θ ∈ thickening δ (Icc α β) := by
    intro θ hθ
    rw [mem_thickening_iff]
    have hmem : max α (min θ β) ∈ Icc α β := ⟨le_max_left _ _, max_le hαβ (min_le_right _ _)⟩
    refine ⟨_, hmem, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · rcases le_total θ β with h1 | h1
      · rw [min_eq_left h1]
        have := le_max_right α θ
        have h2 := hθ.2
        rcases le_total α θ with h3 | h3
        · rw [max_eq_right h3]
          linarith
        · rw [max_eq_left h3]
          linarith [hθ.1]
      · rw [min_eq_right h1, max_eq_right hαβ]
        linarith [hθ.2]
    · rcases le_total θ β with h1 | h1
      · rw [min_eq_left h1]
        rcases le_total α θ with h3 | h3
        · rw [max_eq_right h3]
          linarith
        · rw [max_eq_left h3]
          linarith [hθ.1]
      · rw [min_eq_right h1, max_eq_right hαβ]
        linarith [hθ.2]
  refine ⟨δ / 2, by positivity, ?_, ?_, O, hO, ?_, ?_⟩
  · have h1 := (hth (hthick (α - δ / 2) ⟨le_rfl, by linarith⟩)).2.1
    exact h1
  · have h1 := (hth (hthick (β + δ / 2) ⟨by linarith, le_rfl⟩)).2.2
    exact h1
  · exact fun θ hθ => (hth (hthick θ hθ)).1
  · intro z hz hn
    have h1 : z ∈ O ∩ closedBall 0 1 := ⟨hz, mem_closedBall_zero_iff.mpr hn⟩
    rw [← hOe] at h1
    exact h1.1

private theorem exists_polar_rectangle_extension
    {D : Set S} {h : S → ℂ} {g : ℂ → S} (cD : IsChart D h g)
    {R : ℝ} {U : Set S} {k : S → ℂ} {l : ℂ → S} (c : BallChart R U k l)
    {N : Set S} {O : Set ℂ} {α β η δ ε m w : ℝ}
    (hα₁ : -Real.pi < α - η) (hβ₁ : β + η < Real.pi)
    (hε : ε = δ / 2) (hε0 : 0 < ε)
    (hm : m = (α + β) / 2) (hw : w = (β - α) / 2 + η) (hw0 : 0 < w)
    (hth : Metric.thickening δ (cis' '' Icc (α - η) (β + η)) ⊆ O)
    (hOg : ∀ z ∈ O, ‖z‖ ≤ 1 → g z ∈ U ∩ N) :
    let R₀ : Set ℂ := Icc (-1) 1 ×ℂ Icc (-1) 0
    let κ : ℂ → ℂ := fun z => Complex.exp (((ε * z.im : ℝ) : ℂ) + ((m + w * z.re : ℝ) : ℂ) *
      Complex.I)
    let ν : ℂ → ℂ := fun z => k (g (κ z))
    ∃ Ψ : ℂ ≃ₜ ℂ, EqOn Ψ ν (frontier R₀) ∧ Ψ '' R₀ = ν '' R₀ ∧
      (∀ z ∈ R₀, ν z ∈ ball (0 : ℂ) R) ∧
      (∀ z ∈ R₀, l (ν z) = g (κ z)) ∧
      ∀ z, κ z = ((Real.exp (ε * z.im) : ℝ) : ℂ) * cis' (m + w * z.re) := by
  intro R₀ κ ν
  have hκc : Continuous κ := by
    change Continuous fun z : ℂ => Complex.exp (((ε * z.im : ℝ) : ℂ) +
      ((m + w * z.re : ℝ) : ℂ) * Complex.I)
    have h1 : Continuous fun z : ℂ => ((ε * z.im : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_const.mul Complex.continuous_im)
    have h2 : Continuous fun z : ℂ => ((m + w * z.re : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_const.add (continuous_const.mul
        Complex.continuous_re))
    exact Complex.continuous_exp.comp (h1.add (h2.mul continuous_const))
  have hθR : ∀ z ∈ R₀, m + w * z.re ∈ Icc (α - η) (β + η) := fun z hz => by
    obtain ⟨⟨h1, h2⟩, -⟩ := Complex.mem_reProdIm.mp hz
    have hmw : m - w = α - η := by rw [hm, hw]; ring
    have hmw' : m + w = β + η := by rw [hm, hw]; ring
    constructor
    · nlinarith
    · nlinarith
  have hκform : ∀ z, κ z = ((Real.exp (ε * z.im) : ℝ) : ℂ) * cis' (m + w * z.re) := fun z => by
    change Complex.exp _ = _
    rw [Complex.exp_add, Complex.ofReal_exp, cis']
  have hnorm : ∀ z, ‖κ z‖ = Real.exp (ε * z.im) := fun z => by
    rw [hκform, norm_mul, norm_cis', mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hκball : ∀ z ∈ R₀, κ z ∈ closedBall (0 : ℂ) 1 := fun z hz => by
    obtain ⟨-, -, h2⟩ := Complex.mem_reProdIm.mp hz
    rw [mem_closedBall_zero_iff, hnorm]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hε0.le h2)
  have hκO : ∀ z ∈ R₀, κ z ∈ O := fun z hz => by
    obtain ⟨-, h1, h2⟩ := Complex.mem_reProdIm.mp hz
    refine hth (mem_thickening_iff.mpr ⟨_, ⟨_, hθR z hz, rfl⟩, ?_⟩)
    rw [dist_eq_norm, hκform]
    have h3 : ((Real.exp (ε * z.im) : ℝ) : ℂ) * cis' (m + w * z.re) - cis' (m + w * z.re) =
        ((Real.exp (ε * z.im) - 1 : ℝ) : ℂ) * cis' (m + w * z.re) := by
      push_cast
      ring
    rw [h3, norm_mul, norm_cis', mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h4 : Real.exp (ε * z.im) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hε0.le h2)
    have h5 := Real.add_one_le_exp (ε * z.im)
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  have hgκ : ∀ z ∈ R₀, g (κ z) ∈ U ∩ N := fun z hz => hOg _ (hκO z hz)
    (mem_closedBall_zero_iff.mp (hκball z hz))
  have hlogκ : ∀ z ∈ R₀, Complex.log (κ z) = ((ε * z.im : ℝ) : ℂ) + ((m + w * z.re : ℝ) : ℂ) *
    Complex.I :=
    fun z hz => by
      have h1 := hθR z hz
      refine Complex.log_exp ?_ ?_
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im,
          Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
        linarith [h1.1]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im,
          Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
        linarith [h1.2]
  have hslit : ∀ z ∈ R₀, κ z ∈ Complex.slitPlane := fun z hz => by
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨fun he => ?_, Complex.exp_ne_zero _⟩
    have h1 : (Complex.log (κ z)).im = Complex.arg (κ z) := Complex.log_im _
    rw [hlogκ z hz, he] at h1
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, zero_add, add_zero] at h1
    linarith [(hθR z hz).2]
  let lam : ℂ → ℂ := fun u => ⟨((Complex.log u).im - m) / w, (Complex.log u).re / ε⟩
  have hlamκ : ∀ z ∈ R₀, lam (κ z) = z := fun z hz => by
    apply Complex.ext
    · change ((Complex.log (κ z)).im - m) / w = z.re
      rw [hlogκ z hz]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      field_simp
      ring
    · change (Complex.log (κ z)).re / ε = z.im
      rw [hlogκ z hz]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      field_simp
  have hlamc : ContinuousOn lam Complex.slitPlane := by
    have hlog : ContinuousOn Complex.log Complex.slitPlane :=
      fun u hu => (continuousAt_clog hu).continuousWithinAt
    have h1 : ContinuousOn (fun u => ((Complex.log u).im - m) / w) Complex.slitPlane :=
      ((Complex.continuous_im.comp_continuousOn hlog).sub continuousOn_const).div_const _
    have h2 : ContinuousOn (fun u => (Complex.log u).re / ε) Complex.slitPlane :=
      (Complex.continuous_re.comp_continuousOn hlog).div_const _
    have h3 : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) :=
      Complex.equivRealProdCLM.symm.continuous
    exact h3.comp_continuousOn (h1.prodMk h2)
  let ν' : ℂ → ℂ := fun u => lam (h (l u))
  have hgκc : ContinuousOn (fun z => g (κ z)) R₀ := cD.gc.comp hκc.continuousOn hκball
  have hνc : ContinuousOn ν R₀ := c.hc.comp hgκc fun z hz => (hgκ z hz).1
  have hνb : ∀ z ∈ R₀, ν z ∈ ball (0 : ℂ) R := fun z hz => c.hm (hgκ z hz).1
  have hlν : ∀ z ∈ R₀, l (ν z) = g (κ z) := fun z hz => c.gh (hgκ z hz).1
  have hνl : LeftInvOn ν' ν R₀ := fun z hz => by
    change lam (h (l (ν z))) = z
    rw [hlν z hz, cD.hg (hκball z hz), hlamκ z hz]
  have hνc' : ContinuousOn ν' (ν '' R₀) := by
    have h1 : ContinuousOn l (ν '' R₀) := c.gc.mono (image_subset_iff.mpr hνb)
    have h2 : MapsTo l (ν '' R₀) D := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hlν z hz]
      exact cD.gm (hκball z hz)
    have h3 : ContinuousOn (fun u => h (l u)) (ν '' R₀) := cD.hc.comp h1 h2
    refine hlamc.comp h3 ?_
    rintro _ ⟨z, hz, rfl⟩
    change h (l (ν z)) ∈ _
    rw [hlν z hz, cD.hg (hκball z hz)]
    exact hslit z hz
  obtain ⟨hR₀, hR₀b⟩ := isClosedDisc_rect (a := -1) (b := 1) (c := -1) (d := 0) (by norm_num)
    (by norm_num)
  obtain ⟨hE, hEb⟩ := hR₀.image hνc hνc' hνl
  rw [hR₀b] at hEb
  have hF₀ : Nonempty (Circle ≃ₜ frontier R₀) := by
    have := hR₀.isOArc_discBd
    rwa [hR₀b] at this
  have hF : Nonempty (Circle ≃ₜ ν '' frontier R₀) := by
    have := hE.isOArc_discBd
    rwa [hEb] at this
  have hfrR : frontier R₀ ⊆ R₀ :=
    (isCompact_Icc.reProdIm isCompact_Icc).isClosed.frontier_subset
  have hmatch : BdMatch (frontier R₀) (ν '' frontier R₀) ν ν' :=
    bdMatch_of_leftInvOn (hνc.mono hfrR) (hνc'.mono (image_mono hfrR)) (hνl.mono hfrR)
  obtain ⟨Ψ, hΨ, hΨi⟩ := exists_plane_homeomorph hF₀ hF hmatch
  rw [← eq_closedInner_of_discBd hF₀ hR₀ hR₀b, ← eq_closedInner_of_discBd hF hE hEb] at hΨi
  exact ⟨Ψ, hΨ, hΨi, hνb, hlν, hκform⟩

private theorem rectangle_subset_thickening {a b δ : ℝ} (hδ : 0 < δ) :
    (Icc a b ×ℂ Icc 0 (δ / 2)) ⊆ Metric.thickening δ
      ((fun x : ℝ => (x : ℂ)) '' Icc a b) := by
  intro z hz
  obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hz
  refine mem_thickening_iff.mpr ⟨_, ⟨z.re, h1, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have h3 : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [h3, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    h2.1]
  linarith [h2.2]

private theorem affine_apply_inverse {m w x : ℝ} (hw : w ≠ 0) :
    m + w * ((x - m) / w) = x := by
  field_simp
  ring

/-- **The cap.** Let `D` be a closed disc with a chart, let the arc between the angles `α < β` lie
in
a plane chart `U` of the surface and in the open set `N`. Then a closed disc `T ⊆ N` meets `D`
exactly
in this arc, and the arc lies in the boundary of `T`. -/
theorem exists_cap_angle [T2Space S] {D : Set S} {h : S → ℂ} {g : ℂ → S} (cD : IsChart D h g)
    {R : ℝ} {U : Set S} {k : S → ℂ} {l : ℂ → S} (c : BallChart R U k l) {N : Set S} (hN : IsOpen N)
    {α β : ℝ} (hα : -Real.pi < α) (hαβ : α < β) (hβ : β < Real.pi)
    (hsub : angleArc g α β ⊆ U ∩ N) :
    ∃ T : Set S, IsClosedDisc T ∧ T ⊆ N ∧ T ∩ D = angleArc g α β ∧ angleArc g α β ⊆ discBd T := by
  classical
  obtain ⟨η, hη, hα₁, hβ₁, O, hO, hOθ, hOg⟩ := cD.exists_margin (c.isOpen.inter hN) hα hαβ.le hβ
    hsub
  have hcK : IsCompact (cis' '' Icc (α - η) (β + η)) := isCompact_Icc.image continuous_cis'
  obtain ⟨δ, hδ, hth⟩ := hcK.exists_thickening_subset_open hO (by
    rintro _ ⟨θ, hθ, rfl⟩
    exact hOθ θ hθ)
  set ε := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  set m := (α + β) / 2 with hm
  set w := (β - α) / 2 + η with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  let R₀ : Set ℂ := Icc (-1) 1 ×ℂ Icc (-1) 0
  let κ : ℂ → ℂ := fun z => Complex.exp (((ε * z.im : ℝ) : ℂ) + ((m + w * z.re : ℝ) : ℂ) *
    Complex.I)
  let ν : ℂ → ℂ := fun z => k (g (κ z))
  let lam : ℂ → ℂ := fun u => ⟨((Complex.log u).im - m) / w, (Complex.log u).re / ε⟩
  obtain ⟨Ψ, hΨ, hΨi, hνb, hlν, hκform⟩ :=
    exists_polar_rectangle_extension cD c hα₁ hβ₁ hε hε0 hm hw hw0 hth hOg
  have hfrR : frontier R₀ ⊆ R₀ :=
    (isCompact_Icc.reProdIm isCompact_Icc).isClosed.frontier_subset
  -- the part of `D` away from the arc
  let Vo : Set ℂ := (Complex.slitPlane ∩ Complex.arg ⁻¹' Ioo (α - η) (β + η)) ∩
    {u | Real.exp (-ε) < ‖u‖}
  have hargc : ContinuousOn Complex.arg Complex.slitPlane :=
    fun u hu => (Complex.continuousAt_arg hu).continuousWithinAt
  have hVo : IsOpen Vo := (hargc.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo).inter
    (isOpen_lt continuous_const continuous_norm)
  let D₁ : Set S := g '' (closedBall 0 1 \ Vo)
  have hD₁ : IsCompact D₁ := ((isCompact_closedBall 0 1).diff hVo).image_of_continuousOn
    (cD.gc.mono sdiff_subset)
  have hcisV : ∀ θ ∈ Icc α β, cis' θ ∈ Vo := fun θ hθ => by
    have harg : Complex.arg (cis' θ) = θ := by
      rw [cis', ← Complex.log_im, Complex.log_exp]
      · simp
      · simpa using hα.trans_le hθ.1
      · simpa using (hθ.2.trans_lt hβ).le
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Complex.mem_slitPlane_iff_arg]
      refine ⟨fun he => ?_, Complex.exp_ne_zero _⟩
      rw [harg] at he
      linarith [hθ.2]
    · change Complex.arg (cis' θ) ∈ Ioo (α - η) (β + η)
      rw [harg]
      exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    · change _ < ‖cis' θ‖
      rw [norm_cis']
      exact Real.exp_lt_one_iff.mpr (by linarith)
  have harcD₁ : ∀ θ ∈ Icc α β, g (cis' θ) ∉ D₁ := by
    rintro θ hθ ⟨u, hu, he⟩
    have h1 := cD.injOn hu.1 (cis'_mem_closedBall θ) he
    exact hu.2 (h1 ▸ hcisV θ hθ)
  let a := (α - m) / w
  let b := (β - m) / w
  have hab : a < b := div_lt_div_of_pos_right (by linarith) hw0
  have hma : m + w * a = α := affine_apply_inverse hw0.ne'
  have hmb : m + w * b = β := affine_apply_inverse hw0.ne'
  have hθseg : ∀ x ∈ Icc a b, m + w * x ∈ Icc α β := fun x hx => by
    constructor
    · rw [← hma]
      have := mul_le_mul_of_nonneg_left hx.1 hw0.le
      linarith
    · rw [← hmb]
      have := mul_le_mul_of_nonneg_left hx.2 hw0.le
      linarith
  have hsegR : ∀ x ∈ Icc a b, (x : ℂ) ∈ frontier R₀ := fun x hx => by
    have h1 : -1 ≤ a := by
      simp only [a]
      rw [le_div_iff₀ hw0, hm, hw]
      linarith
    have h2 : b ≤ 1 := by
      simp only [b]
      rw [div_le_iff₀ hw0, hm, hw]
      linarith
    exact top_subset_frontier_rect (by simpa using ⟨h1.trans hx.1, hx.2.trans h2⟩) (by simp)
      (by norm_num)
  have hνseg : ∀ x ∈ Icc a b, l (Ψ x) = g (cis' (m + w * x)) := fun x hx => by
    have h1 := hfrR (hsegR x hx)
    rw [hΨ (hsegR x hx), hlν _ h1, hκform]
    simp
  let O' : Set ℂ := Ψ ⁻¹' (ball 0 R ∩ l ⁻¹' (N \ D₁))
  have hO' : IsOpen O' :=
    (c.gc.isOpen_inter_preimage isOpen_ball (hN.sdiff hD₁.isClosed)).preimage Ψ.continuous
  let Sg : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc a b
  have hSg : IsCompact Sg := isCompact_Icc.image Complex.continuous_ofReal
  have hSgO : Sg ⊆ O' := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hfrR (hsegR x hx)
    refine ⟨?_, ?_⟩
    · change Ψ x ∈ _
      rw [hΨ (hsegR x hx)]
      exact hνb _ h1
    · change l (Ψ x) ∈ N \ D₁
      rw [hνseg x hx]
      exact ⟨(hsub ⟨_, hθseg x hx, rfl⟩).2, harcD₁ _ (hθseg x hx)⟩
  obtain ⟨ρ₀, hρ₀, hρth⟩ := hSg.exists_thickening_subset_open hO' hSgO
  set ρ := ρ₀ / 2 with hρ
  let T' : Set ℂ := Icc a b ×ℂ Icc 0 ρ
  have hT'O : T' ⊆ O' := (rectangle_subset_thickening hρ₀).trans hρth
  obtain ⟨hT'd, hT'b⟩ := isClosedDisc_rect hab (half_pos hρ₀)
  let f : ℂ → S := fun z => l (Ψ z)
  let f' : S → ℂ := fun x => Ψ.symm (k x)
  have hfc : ContinuousOn f T' :=
    c.gc.comp Ψ.continuous.continuousOn fun z hz => (hT'O hz).1
  have hfU : ∀ z ∈ T', f z ∈ U := fun z hz => c.gm (hT'O hz).1
  have hfl : LeftInvOn f' f T' := fun z hz => by
    change Ψ.symm (k (l (Ψ z))) = z
    rw [c.hg (hT'O hz).1, Ψ.symm_apply_apply]
  have hfc' : ContinuousOn f' (f '' T') := by
    refine Ψ.symm.continuous.comp_continuousOn (c.hc.mono ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact hfU z hz
  obtain ⟨hTd, hTb⟩ := hT'd.image hfc hfc' hfl
  rw [hT'b] at hTb
  have harcT : ∀ x ∈ Icc a b, g (cis' (m + w * x)) ∈ f '' frontier T' := fun x hx =>
    ⟨x, bot_subset_frontier_rect (by simpa using hx) (by simp) (half_pos hρ₀).le, hνseg x hx⟩
  have hparam : ∀ θ ∈ Icc α β, ∃ x ∈ Icc a b, m + w * x = θ := fun θ hθ => by
    refine ⟨(θ - m) / w, ⟨?_, ?_⟩, ?_⟩
    · exact div_le_div_of_nonneg_right (by linarith [hθ.1]) hw0.le
    · exact div_le_div_of_nonneg_right (by linarith [hθ.2]) hw0.le
    · field_simp
      ring
  have hfrT : frontier T' ⊆ T' := (isCompact_Icc.reProdIm isCompact_Icc).isClosed.frontier_subset
  refine ⟨f '' T', hTd, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hT'O hz).2.1
  · apply Subset.antisymm
    · rintro x ⟨⟨z, hz, rfl⟩, hxD⟩
      have hzO := hT'O hz
      have hxD₁ : f z ∉ D₁ := hzO.2.2
      have hu : h (f z) ∈ closedBall (0 : ℂ) 1 := cD.hm hxD
      have huV : h (f z) ∈ Vo := by
        by_contra hcon
        exact hxD₁ ⟨_, ⟨hu, hcon⟩, cD.gh hxD⟩
      set u := h (f z) with hudef
      have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero huV.1.1
      have huO : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
      have hlogre : (Complex.log u).re = Real.log ‖u‖ := Complex.log_re u
      have hlogim : (Complex.log u).im = Complex.arg u := Complex.log_im u
      have hz₁ : lam u ∈ R₀ := by
        refine Complex.mem_reProdIm.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · change -1 ≤ ((Complex.log u).im - m) / w
          rw [le_div_iff₀ hw0, hlogim]
          have := huV.1.2.1
          rw [hm, hw]
          linarith
        · change ((Complex.log u).im - m) / w ≤ 1
          rw [div_le_iff₀ hw0, hlogim]
          have := huV.1.2.2
          rw [hm, hw]
          linarith
        · change -1 ≤ (Complex.log u).re / ε
          rw [le_div_iff₀ hε0, hlogre]
          have h1 := huV.2
          have h2 : -ε ≤ Real.log ‖u‖ :=
            (Real.le_log_iff_exp_le (norm_pos_iff.mpr hu0)).mpr h1.le
          linarith
        · change (Complex.log u).re / ε ≤ 0
          rw [hlogre]
          exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (norm_nonneg _) huO) hε0.le
      have hκu : κ (lam u) = u := by
        change Complex.exp (((ε * ((Complex.log u).re / ε) : ℝ) : ℂ) +
          ((m + w * (((Complex.log u).im - m) / w) : ℝ) : ℂ) * Complex.I) = u
        have h1 : ε * ((Complex.log u).re / ε) = (Complex.log u).re := by
          field_simp
        have h2 : m + w * (((Complex.log u).im - m) / w) = (Complex.log u).im := by
          field_simp
          ring
        rw [h1, h2, Complex.re_add_im, Complex.exp_log hu0]
      have hΨz : Ψ z = ν (lam u) := by
        change Ψ z = k (g (κ (lam u)))
        rw [hκu, hudef, cD.gh hxD]
        change Ψ z = k (l (Ψ z))
        rw [c.hg hzO.1]
      have hz' : Ψ z ∈ Ψ '' R₀ := by
        rw [hΨi, hΨz]
        exact ⟨_, hz₁, rfl⟩
      obtain ⟨z', hz'R, he⟩ := hz'
      have hzz := Ψ.injective he
      subst hzz
      have him : z'.im = 0 := le_antisymm (Complex.mem_reProdIm.mp hz'R).2.2
        (Complex.mem_reProdIm.mp hz).2.1
      have hre := (Complex.mem_reProdIm.mp hz).1
      have hz'e : z' = (z'.re : ℂ) := by
        apply Complex.ext <;> simp [him]
      refine ⟨m + w * z'.re, hθseg _ hre, ?_⟩
      change g (cis' (m + w * z'.re)) = f z'
      rw [← hνseg _ hre, ← hz'e]
    · rintro _ ⟨θ, hθ, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hparam θ hθ
      obtain ⟨y, hy, he⟩ := harcT x hx
      exact ⟨⟨y, hfrT hy, he⟩, discBd_subset D (cD.angleArc_subset α β ⟨_, hθ, rfl⟩)⟩
  · rw [hTb]
    rintro _ ⟨θ, hθ, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hparam θ hθ
    exact harcT x hx

end GraphMinor.Surface
