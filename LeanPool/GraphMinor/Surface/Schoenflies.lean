/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DomainHomeo
public import LeanPool.GraphMinor.Surface.Jordan

/-!
# The Schoenflies theorem

`schoenflies_theorem : SchoenfliesStatement`: every homeomorphism from the unit circle onto an
`O`-arc of the plane extends to a homeomorphism of the plane.

The route. `exists_homeomorph_closedInner` extends the map from the closed unit disc onto the closed
inner domain. For the outside choose `a` in `inner F` and use the inversion `j z = (z - a)⁻¹`. It
exchanges the two sides of the curve, with `0` taking the place of the point at infinity. So the
closed outer domain, with infinity added, is the closed inner domain of `j '' F`, and
`exists_homeomorph_closedInner` applies again. A push of the disc that fixes the circle makes the
centre go to `0`. The two maps agree on the circle and glue to a continuous bijection of the plane,
and invariance of domain says that its inverse is continuous.

The proof of `exists_homeomorph_closedInner` is not Thomassen's. It uses Eilenberg's criterion to
show accessibility of all points of an `O`-arc, and cuts by segments of a grid. See
`Surface/DomainHomeo.lean`. Compare C. Thomassen, *The Jordan–Schönflies theorem and the
classification of surfaces*, Amer. Math. Monthly 99 (1992) 116–130, Theorem 3.5, for the same
statement.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

/-- If open sets `O, I` split the complement of `G`, and `O` is bounded and not empty, then they are
the two parts of the complement. -/
theorem IsJordanParts.eq_of_cover {G : Set ℂ} (J : IsJordanParts G) {O I : Set ℂ} (hO : IsOpen O)
    (hI : IsOpen I) (hdis : Disjoint O I) (hcov : O ∪ I = Gᶜ) (hne : O.Nonempty)
    (hb : Bornology.IsBounded O) : inner G = O ∧ outer G = I := by
  have hsplit : ∀ {C : Set ℂ}, IsPreconnected C → C ⊆ Gᶜ → C ⊆ O ∨ C ⊆ I := by
    intro C hC hsub
    have hsub' : C ⊆ O ∪ I := hcov ▸ hsub
    by_cases hemp : (C ∩ O).Nonempty
    · exact Or.inl (hC.subset_left_of_subset_union hO hI hdis hsub' hemp)
    · right
      exact fun z hz => (hsub' hz).resolve_left fun h => hemp ⟨z, hz, h⟩
  have houter : outer G ⊆ I := by
    rcases hsplit J.isConnected_outer.isPreconnected J.outer_subset_compl with h | h
    · exact absurd (hb.subset h) J.not_isBounded_outer
    · exact h
  have hinner : inner G ⊆ O := by
    rcases hsplit J.isConnected_inner.isPreconnected J.inner_subset_compl with h | h
    · exact h
    · exfalso
      obtain ⟨z, hz⟩ := hne
      have hz' : z ∈ Gᶜ := hcov ▸ Or.inl hz
      rw [← J.union_eq] at hz'
      rcases hz' with h' | h'
      · exact Set.disjoint_left.mp hdis hz (h h')
      · exact Set.disjoint_left.mp hdis hz (houter h')
  constructor
  · refine Subset.antisymm hinner fun z hz => ?_
    have hz' : z ∈ Gᶜ := hcov ▸ Or.inl hz
    rw [← J.union_eq] at hz'
    exact hz'.resolve_right fun h => Set.disjoint_left.mp hdis hz (houter h)
  · refine Subset.antisymm houter fun z hz => ?_
    have hz' : z ∈ Gᶜ := hcov ▸ Or.inr hz
    rw [← J.union_eq] at hz'
    exact hz'.resolve_left fun h => Set.disjoint_left.mp hdis (hinner h) hz

/-- The unit circle of `ℂ` as an `O`-arc. -/
theorem oArc_sphere : Nonempty (Circle ≃ₜ sphere (0 : ℂ) 1) := by
  have hemb : IsEmbedding fun w : Circle => (w : ℂ) := IsEmbedding.subtypeVal
  have hr : range (fun w : Circle => (w : ℂ)) = sphere 0 1 := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  exact ⟨hemb.toHomeomorph.trans (Homeomorph.setCongr hr)⟩

theorem inner_sphere : inner (sphere (0 : ℂ) 1) = ball 0 1 := by
  obtain ⟨φ⟩ := oArc_sphere
  refine ((isJordanParts φ).eq_of_cover (I := (closedBall 0 1)ᶜ) isOpen_ball
    isClosed_closedBall.isOpen_compl ?_ ?_ ⟨0, by simp⟩ isBounded_ball).1
  · exact Set.disjoint_left.mpr fun z h1 h2 => h2 (ball_subset_closedBall h1)
  · ext z
    simp only [mem_union, mem_ball_zero_iff, mem_compl_iff, mem_closedBall_zero_iff,
      mem_sphere_zero_iff_norm]
    constructor
    · rintro (h | h) <;> intro h' <;> linarith
    · intro h
      rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd h1 h
      · exact Or.inr (not_le.mpr h1)

theorem closedInner_sphere : closedInner (sphere (0 : ℂ) 1) = closedBall 0 1 := by
  rw [closedInner, inner_sphere, ball_union_sphere]

/-- A push of the closed disc that fixes the circle and takes the centre to a given point. -/
theorem exists_disc_push {c : ℂ} (hc : ‖c‖ < 1) :
    ∃ θ : ℂ → ℂ, Continuous θ ∧ BijOn θ (closedBall 0 1) (closedBall 0 1) ∧ θ 0 = c ∧
      ∀ z ∈ sphere (0 : ℂ) 1, θ z = z := by
  let θ : ℂ → ℂ := fun z => z + ((1 - ‖z‖ : ℝ) : ℂ) * c
  have hθc : Continuous θ := by fun_prop
  have hnorm : ∀ z, ‖z‖ ≤ 1 → ‖θ z‖ ≤ ‖z‖ + (1 - ‖z‖) * ‖c‖ := fun z hz => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hinj : InjOn θ univ := by
    intro z _ z' _ h
    by_contra hne
    have h1 : z - z' = ((‖z‖ - ‖z'‖ : ℝ) : ℂ) * c := by
      have : z + ((1 - ‖z‖ : ℝ) : ℂ) * c = z' + ((1 - ‖z'‖ : ℝ) : ℂ) * c := h
      push_cast at this ⊢
      linear_combination this
    have h2 : ‖z - z'‖ = |‖z‖ - ‖z'‖| * ‖c‖ := by
      rw [h1, norm_mul, norm_real, Real.norm_eq_abs]
    have h3 : |‖z‖ - ‖z'‖| ≤ ‖z - z'‖ := abs_norm_sub_norm_le z z'
    have h4 : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h5 : |‖z‖ - ‖z'‖| * ‖c‖ ≤ ‖z - z'‖ * ‖c‖ :=
      mul_le_mul_of_nonneg_right h3 (norm_nonneg c)
    nlinarith
  have hfix : ∀ z ∈ sphere (0 : ℂ) 1, θ z = z := fun z hz => by
    have : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    simp [θ, this]
  have hmaps : MapsTo θ (closedBall 0 1) (closedBall 0 1) := by
    intro z hz
    have hz' := mem_closedBall_zero_iff.mp hz
    refine mem_closedBall_zero_iff.mpr ((hnorm z hz').trans ?_)
    nlinarith [norm_nonneg c]
  have hopen : MapsTo θ (ball 0 1) (ball 0 1) := by
    intro z hz
    have hz' := mem_ball_zero_iff.mp hz
    refine mem_ball_zero_iff.mpr (lt_of_le_of_lt (hnorm z hz'.le) ?_)
    nlinarith [norm_nonneg c]
  have hzero : θ 0 = c := by simp [θ]
  refine ⟨θ, hθc, ⟨hmaps, hinj.mono (subset_univ _), ?_⟩, hzero, hfix⟩
  have hU : IsOpen (θ '' ball 0 1) :=
    isOpen_image_of_injOn isOpen_ball hθc.continuousOn (hinj.mono (subset_univ _))
  have hclosed : IsClosed (θ '' closedBall 0 1) :=
    ((isCompact_closedBall (0 : ℂ) 1).image hθc).isClosed
  have hball : ball (0 : ℂ) 1 ⊆ θ '' ball 0 1 := by
    refine (convex_ball (0 : ℂ) 1).isPreconnected.subset_of_closure_inter_subset hU
      ⟨c, mem_ball_zero_iff.mpr hc, 0, by simp, hzero⟩ ?_
    rintro y ⟨hy1, hy2⟩
    have hy3 : y ∈ θ '' closedBall 0 1 :=
      hclosed.closure_subset_iff.mpr (image_mono ball_subset_closedBall) hy1
    obtain ⟨z, hz, rfl⟩ := hy3
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz) with h | h
    · exact ⟨z, mem_ball_zero_iff.mpr h, rfl⟩
    · have hzs : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr h
      rw [hfix z hzs] at hy2
      exact absurd h (mem_ball_zero_iff.mp hy2).ne
  intro y hy
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hy) with h | h
  · obtain ⟨z, hz, rfl⟩ := hball (mem_ball_zero_iff.mpr h)
    exact ⟨z, ball_subset_closedBall hz, rfl⟩
  · exact ⟨y, hy, hfix y (mem_sphere_zero_iff_norm.mpr h)⟩

/-- A homeomorphism of subsets is given by a pair of functions on the plane. -/
theorem exists_bdMatch {A B : Set ℂ} (e : A ≃ₜ B) :
    ∃ h k : ℂ → ℂ, BdMatch A B h k ∧ ∀ x : A, h x.1 = (e x).1 := by
  classical
  let h : ℂ → ℂ := fun z => if hz : z ∈ A then (e ⟨z, hz⟩).1 else 0
  let k : ℂ → ℂ := fun z => if hz : z ∈ B then (e.symm ⟨z, hz⟩).1 else 0
  have hv : ∀ x : A, h x.1 = (e x).1 := fun x => by simp [h]
  have kv : ∀ x : B, k x.1 = (e.symm x).1 := fun x => by simp [k]
  refine ⟨h, k, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hv⟩
  · intro z hz
    rw [hv ⟨z, hz⟩]
    exact (e _).2
  · intro z hz
    rw [kv ⟨z, hz⟩]
    exact (e.symm _).2
  · intro z hz
    show k (h z) = z
    rw [hv ⟨z, hz⟩, kv]
    simp
  · intro z hz
    show h (k z) = z
    rw [kv ⟨z, hz⟩, hv]
    simp
  · rw [continuousOn_iff_continuous_domRestrict]
    have : A.domRestrict h = fun x => (e x).1 := funext hv
    rw [this]
    exact continuous_subtype_val.comp e.continuous
  · rw [continuousOn_iff_continuous_domRestrict]
    have : B.domRestrict k = fun x => (e.symm x).1 := funext kv
    rw [this]
    exact continuous_subtype_val.comp e.symm.continuous

/-- `exists_homeomorph_closedInner` in terms of functions on the plane. -/
theorem exists_extension {F F' : Set ℂ} (hF : Nonempty (Circle ≃ₜ F))
    (hF' : Nonempty (Circle ≃ₜ F')) {h₀ k₀ : ℂ → ℂ} (m : BdMatch F F' h₀ k₀) :
    ∃ ψ : ℂ → ℂ, ContinuousOn ψ (closedInner F) ∧ BijOn ψ (closedInner F) (closedInner F') ∧
      EqOn ψ h₀ F := by
  obtain ⟨Ψ, hΨ⟩ := exists_homeomorph_closedInner hF hF' m
  obtain ⟨ψ, χ, ⟨h1, h2, h3, h4, h5, -⟩, hv⟩ := exists_bdMatch Ψ
  have hsub : F ⊆ closedInner F := subset_union_right
  refine ⟨ψ, h5, ⟨h1, h3.injOn, h4.surjOn h2⟩, fun z hz => ?_⟩
  rw [hv ⟨z, hsub hz⟩]
  exact hΨ ⟨z, hsub hz⟩ hz

/-- The inversion about `a`, as a bijection of the plane that exchanges `a` and `0`. -/
private noncomputable def invAt (a z : ℂ) : ℂ := a + z⁻¹

private theorem invAt_eq_iff {a z w : ℂ} : invAt a w = z ↔ w = (z - a)⁻¹ := by
  simp only [invAt]
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

private theorem invAt_invAt {a z : ℂ} : invAt a (z - a)⁻¹ = z := invAt_eq_iff.mpr rfl

private theorem invAt_injective (a : ℂ) : Function.Injective (invAt a) := by
  intro w w' h
  have := invAt_eq_iff.mp h
  simpa [invAt] using this

private theorem invAt_zero (a : ℂ) : invAt a 0 = a := by simp [invAt]

private theorem invAt_ne {a w : ℂ} (hw : w ≠ 0) : invAt a w ≠ a := fun h =>
  hw ((invAt_injective a) (h.trans (invAt_zero a).symm))

private theorem continuousOn_invAt (a : ℂ) {A : Set ℂ} (hA : (0 : ℂ) ∉ A) :
    ContinuousOn (invAt a) A :=
  continuousOn_const.add (continuousOn_id.inv₀ fun _ hz h => hA (h ▸ hz))

/-- The image of a curve under inversion about a point off it. -/
private theorem oArc_preimage_invAt {F : Set ℂ} (φ : Circle ≃ₜ F) {a : ℂ} (ha : a ∉ F) :
    Nonempty (Circle ≃ₜ invAt a ⁻¹' F) := by
  let f : Circle → ℂ := fun w => ((φ w).1 - a)⁻¹
  have hne : ∀ w, (φ w).1 - a ≠ 0 := fun w h => ha (sub_eq_zero.mp h ▸ (φ w).2)
  have hc : Continuous f :=
    ((continuous_subtype_val.comp φ.continuous).sub continuous_const).inv₀ hne
  have hi : Function.Injective f := by
    intro w w' h
    have h1 : (φ w).1 - a = (φ w').1 - a := inv_injective h
    exact φ.injective (Subtype.ext (sub_left_inj.mp h1))
  have hr : range f = invAt a ⁻¹' F := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      change invAt a _ ∈ F
      rw [invAt_invAt]
      exact (φ v).2
    · intro hw
      obtain ⟨v, hv⟩ := φ.surjective ⟨_, hw⟩
      refine ⟨v, ?_⟩
      change ((φ v).1 - a)⁻¹ = w
      rw [hv]
      exact (invAt_eq_iff.mp rfl).symm
  exact ⟨(hc.isClosedEmbedding hi).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)⟩

/-- Inversion about a point of the inside exchanges the two sides of a curve. -/
private theorem inner_preimage_invAt {F : Set ℂ} (φ : Circle ≃ₜ F) {a : ℂ} (ha : a ∈ inner F) :
    inner (invAt a ⁻¹' F) = invAt a ⁻¹' outer F ∪ {0} := by
  have J := isJordanParts φ
  have haF : a ∉ F := J.inner_subset_compl ha
  obtain ⟨φ'⟩ := oArc_preimage_invAt φ haF
  have J' := isJordanParts φ'
  have hdisj : ∀ {z}, z ∈ inner F → z ∉ outer F := fun h h' => Set.disjoint_left.mp J.disjoint h h'
  have hsplit : ∀ {z}, z ∉ F → z ∈ inner F ∨ z ∈ outer F := fun {z} hz => by
    have : z ∈ Fᶜ := hz
    rwa [← J.union_eq] at this
  have hopen : ∀ {U : Set ℂ}, IsOpen U → IsOpen ((invAt a ⁻¹' U) \ {0}) := by
    intro U hU
    have h1 := (continuousOn_invAt a (A := {0}ᶜ) (by simp)).isOpen_inter_preimage
      isOpen_compl_singleton hU
    have h2 : {0}ᶜ ∩ invAt a ⁻¹' U = (invAt a ⁻¹' U) \ {0} := by
      ext z
      simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
      tauto
    rwa [h2] at h1
  have hd : ∀ w : ℂ, dist (invAt a w) a = ‖w‖⁻¹ := fun w => by
    rw [dist_eq_norm, invAt, add_sub_cancel_left, norm_inv]
  obtain ⟨R₀, hR₀⟩ := J.isCompact_closure_inner.isBounded.subset_closedBall a
  have hR : 0 < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set R := max R₀ 1 with hRdef
  have hfar : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 / R → invAt a w ∈ outer F := by
    intro w hw hwR
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have h1 : ‖w‖ * ‖w‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    have h2 : ‖w‖ * R < 1 := (lt_div_iff₀ hR).mp hwR
    have h3 : R < ‖w‖⁻¹ := by
      by_contra hn
      have := mul_le_mul_of_nonneg_left (not_lt.mp hn) hpos.le
      linarith
    have h4 : invAt a w ∉ inner F ∪ F := fun hin => by
      have h5 := hR₀ hin
      rw [mem_closedBall, hd] at h5
      exact absurd (h5.trans (le_max_left _ _)) (not_le.mpr h3)
    exact (hsplit fun h => h4 (Or.inr h)).resolve_left fun h => h4 (Or.inl h)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp J.isOpen_inner a ha
  have hOopen : IsOpen (invAt a ⁻¹' outer F ∪ {0}) := by
    have heq : invAt a ⁻¹' outer F ∪ {0} = (invAt a ⁻¹' outer F \ {0}) ∪ ball 0 (1 / R) := by
      ext w
      by_cases hw : w = 0
      · subst hw
        simp [hR]
      · have h1 := hfar w hw
        simp only [mem_union, mem_preimage, mem_singleton_iff, hw, or_false, mem_sdiff,
          not_false_eq_true, and_true, mem_ball_zero_iff]
        tauto
    rw [heq]
    exact (hopen J.isOpen_outer).union isOpen_ball
  refine (J'.eq_of_cover (I := invAt a ⁻¹' inner F \ {0}) hOopen (hopen J.isOpen_inner) ?_ ?_
    ⟨0, Or.inr rfl⟩ ?_).1
  · refine Set.disjoint_left.mpr ?_
    rintro w (h1 | h1) ⟨h2, h3⟩
    · exact hdisj h2 h1
    · exact h3 h1
  · ext w
    constructor
    · rintro ((h1 | h1) | ⟨h1, -⟩)
      · exact fun h => J.outer_subset_compl h1 h
      · rw [mem_singleton_iff.mp h1]
        change invAt a 0 ∉ F
        rwa [invAt_zero]
      · exact fun h => J.inner_subset_compl h1 h
    · intro hw
      by_cases h0 : w = 0
      · exact Or.inl (Or.inr h0)
      · rcases hsplit hw with h | h
        · exact Or.inr ⟨h, h0⟩
        · exact Or.inl (Or.inl h)
  · refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1 / δ)).subset ?_
    rintro w (h1 | h1)
    · by_cases h0 : w = 0
      · subst h0
        simp [hδ.le]
      · rw [mem_closedBall_zero_iff, le_div_iff₀ hδ]
        have hpos : 0 < ‖w‖ := norm_pos_iff.mpr h0
        have h2 : ‖w‖ * ‖w‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
        have h3 : δ ≤ ‖w‖⁻¹ := by
          by_contra hn
          have h4 : invAt a w ∈ ball a δ := by
            rw [mem_ball, hd]
            exact not_le.mp hn
          exact hdisj (hball h4) h1
        have := mul_le_mul_of_nonneg_left h3 hpos.le
        linarith
    · rw [mem_singleton_iff.mp h1]
      simp [hδ.le]

/-- **Extension to the plane.** A homeomorphism from the unit circle of `ℂ` onto an `O`-arc extends
to a homeomorphism of `ℂ`. See the module docstring for the route. -/
theorem exists_homeomorph_of_bdMatch {F : Set ℂ} (hF : Nonempty (Circle ≃ₜ F)) {h₀ k₀ : ℂ → ℂ}
    (m : BdMatch (sphere 0 1) F h₀ k₀) : ∃ G : ℂ ≃ₜ ℂ, EqOn G h₀ (sphere 0 1) := by
  classical
  obtain ⟨φ⟩ := id hF
  have J := isJordanParts φ
  obtain ⟨a, ha⟩ := J.isConnected_inner.nonempty
  have haF : a ∉ F := J.inner_subset_compl ha
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := id m
  obtain ⟨ψ, ψc, ψb, ψe⟩ := exists_extension oArc_sphere hF m
  rw [closedInner_sphere] at ψc ψb
  set Fs := invAt a ⁻¹' F with hFs
  have h0F : (0 : ℂ) ∉ Fs := by
    change invAt a 0 ∉ F
    rwa [invAt_zero]
  have hs : ∀ {z : ℂ}, z ∈ sphere (0 : ℂ) 1 → z⁻¹ ∈ sphere (0 : ℂ) 1 := fun {z} hz => by
    rw [mem_sphere_zero_iff_norm] at hz ⊢
    rw [norm_inv, hz, inv_one]
  have hs0 : ∀ {z : ℂ}, z ∈ sphere (0 : ℂ) 1 → z ≠ 0 := fun {z} hz h => by
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz
    exact zero_ne_one hz
  let hs' : ℂ → ℂ := fun z => (h₀ z⁻¹ - a)⁻¹
  let ks' : ℂ → ℂ := fun w => (k₀ (invAt a w))⁻¹
  have hmem : ∀ {z : ℂ}, z ∈ sphere (0 : ℂ) 1 → invAt a (hs' z) = h₀ z⁻¹ := fun _ => invAt_invAt
  have hc1 : ContinuousOn (fun z : ℂ => h₀ z⁻¹) (sphere 0 1) :=
    m5.comp (continuousOn_id.inv₀ fun z hz => hs0 hz) fun z hz => hs hz
  have ms : BdMatch (sphere 0 1) Fs hs' ks' := by
    refine ⟨fun z hz => ?_, fun w hw => hs (m2 hw), fun z hz => ?_, fun w hw => ?_, ?_, ?_⟩
    · change invAt a (hs' z) ∈ F
      rw [hmem hz]
      exact m1 (hs hz)
    · show ks' (hs' z) = z
      simp only [ks']
      rw [hmem hz, m3 (hs hz), inv_inv]
    · show hs' (ks' w) = w
      simp only [hs', ks']
      rw [inv_inv, m4 hw]
      exact (invAt_eq_iff.mp rfl).symm
    · exact (hc1.sub continuousOn_const).inv₀ fun z hz h =>
        haF (by
          have h' : h₀ z⁻¹ = a := sub_eq_zero.mp h
          rw [← h']
          exact m1 (hs hz))
    · exact (m6.comp (continuousOn_invAt a h0F) fun w hw => hw).inv₀ fun w hw => hs0 (m2 hw)
  have hFs' := oArc_preimage_invAt φ haF
  obtain ⟨ψ', ψ'c, ψ'b, ψ'e⟩ := exists_extension oArc_sphere hFs' ms
  rw [closedInner_sphere] at ψ'c ψ'b
  obtain ⟨φ'⟩ := id hFs'
  have hin : inner Fs = invAt a ⁻¹' outer F ∪ {0} := inner_preimage_invAt φ ha
  have h0in : (0 : ℂ) ∈ closedInner Fs := Or.inl (hin ▸ Or.inr rfl)
  obtain ⟨c, hc, hc0⟩ := ψ'b.2.2 h0in
  have hclt : ‖c‖ < 1 := by
    refine lt_of_le_of_ne (mem_closedBall_zero_iff.mp hc) fun h => h0F ?_
    have hcs : c ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr h
    rw [← hc0, ψ'e hcs]
    exact ms.1 hcs
  obtain ⟨θ, θc, θb, θ0, θe⟩ := exists_disc_push hclt
  let χ : ℂ → ℂ := ψ' ∘ θ
  have χc : ContinuousOn χ (closedBall 0 1) := ψ'c.comp θc.continuousOn θb.1
  have χb : BijOn χ (closedBall 0 1) (closedInner Fs) := ψ'b.comp θb
  have χ0 : χ 0 = 0 := by
    change ψ' (θ 0) = 0
    rw [θ0, hc0]
  have χe : EqOn χ hs' (sphere 0 1) := fun z hz => by
    change ψ' (θ z) = hs' z
    rw [θe z hz, ψ'e hz]
  have hinv : ∀ {z : ℂ}, 1 ≤ ‖z‖ → z⁻¹ ∈ closedBall (0 : ℂ) 1 ∧ z⁻¹ ≠ 0 := fun {z} hz => by
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le one_pos hz)
    refine ⟨?_, inv_ne_zero hz0⟩
    rw [mem_closedBall_zero_iff, norm_inv]
    exact inv_le_one_of_one_le₀ hz
  have h00 : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  have hχne : ∀ {v : ℂ}, v ∈ closedBall (0 : ℂ) 1 → v ≠ 0 → χ v ≠ 0 := fun hv hv0 h =>
    hv0 (χb.2.1 hv h00 (h.trans χ0.symm))
  have hχF : ∀ {v : ℂ}, v ∈ closedBall (0 : ℂ) 1 → χ v ∈ Fs → v ∈ sphere (0 : ℂ) 1 := by
    intro v hv hvF
    have hk : ks' (χ v) ∈ sphere (0 : ℂ) 1 := ms.2.1 hvF
    have h1 : χ (ks' (χ v)) = χ v := by
      rw [χe hk]
      exact ms.2.2.2.1 hvF
    have h2 := χb.2.1 (sphere_subset_closedBall hk) hv h1
    rwa [h2] at hk
  have hout : ∀ {z : ℂ}, 1 < ‖z‖ → invAt a (χ z⁻¹) ∈ outer F := by
    intro z hz
    obtain ⟨hv, hv0⟩ := hinv hz.le
    have hvs : z⁻¹ ∉ sphere (0 : ℂ) 1 := fun h => by
      rw [mem_sphere_zero_iff_norm, norm_inv] at h
      have := inv_lt_one_of_one_lt₀ hz
      linarith
    rcases χb.1 hv with h | h
    · rw [hin] at h
      exact h.resolve_right (hχne hv hv0)
    · exact absurd (hχF hv h) hvs
  let G : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then ψ z else invAt a (χ z⁻¹)
  have Gin : ∀ {z : ℂ}, ‖z‖ ≤ 1 → G z = ψ z := fun {z} hz => by simp only [G, hz, ite_true]
  have Gout : ∀ {z : ℂ}, 1 < ‖z‖ → G z = invAt a (χ z⁻¹) := fun {z} hz => by
    simp only [G, not_le.mpr hz, ite_false]
  have hGe : EqOn G h₀ (sphere 0 1) := fun z hz => by
    rw [Gin (mem_sphere_zero_iff_norm.mp hz).le]
    exact ψe hz
  have hagree : ∀ {z : ℂ}, 1 ≤ ‖z‖ → G z = invAt a (χ z⁻¹) := by
    intro z hz
    rcases lt_or_eq_of_le hz with h | h
    · exact Gout h
    · have hzs : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr h.symm
      rw [hGe hzs, χe (hs hzs), hmem (hs hzs), inv_inv]
  have Gc : Continuous G := by
    have hc1 : ContinuousOn G (closedBall 0 1) :=
      ψc.congr fun z hz => Gin (mem_closedBall_zero_iff.mp hz)
    have hc2 : ContinuousOn G {z : ℂ | 1 ≤ ‖z‖} := by
      refine ContinuousOn.congr ?_ fun z hz => hagree hz
      have hi : ContinuousOn (fun z : ℂ => z⁻¹) {z : ℂ | 1 ≤ ‖z‖} :=
        continuousOn_id.inv₀ fun z hz => norm_pos_iff.mp (lt_of_lt_of_le one_pos hz)
      have hχi : ContinuousOn (fun z : ℂ => χ z⁻¹) {z : ℂ | 1 ≤ ‖z‖} :=
        χc.comp hi fun z hz => (hinv hz).1
      exact (continuousOn_invAt a (A := {0}ᶜ) (by simp)).comp hχi fun z hz =>
        hχne (hinv hz).1 (hinv hz).2
    have hcl : IsClosed {z : ℂ | 1 ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
    have hun := hc1.union_of_isClosed hc2 isClosed_closedBall hcl
    have hu : closedBall (0 : ℂ) 1 ∪ {z : ℂ | 1 ≤ ‖z‖} = univ := by
      ext z
      simp only [mem_union, mem_closedBall_zero_iff, mem_ofPred_eq, mem_univ, iff_true]
      exact le_total _ _
    rwa [hu, continuousOn_univ] at hun
  have hdisj : ∀ {z}, z ∈ closedInner F → z ∉ outer F := by
    rintro z (h | h) h'
    · exact Set.disjoint_left.mp J.disjoint h h'
    · exact J.outer_subset_compl h' h
  have Gi : Function.Injective G := by
    intro z z' he
    rcases le_or_gt ‖z‖ 1 with h1 | h1 <;> rcases le_or_gt ‖z'‖ 1 with h2 | h2
    · rw [Gin h1, Gin h2] at he
      exact ψb.2.1 (mem_closedBall_zero_iff.mpr h1) (mem_closedBall_zero_iff.mpr h2) he
    · rw [Gin h1, Gout h2] at he
      exact absurd (hout h2) (he ▸ hdisj (ψb.1 (mem_closedBall_zero_iff.mpr h1)))
    · rw [Gout h1, Gin h2] at he
      exact absurd (hout h1) (he.symm ▸ hdisj (ψb.1 (mem_closedBall_zero_iff.mpr h2)))
    · rw [Gout h1, Gout h2] at he
      have h3 := χb.2.1 (hinv h1.le).1 (hinv h2.le).1 (invAt_injective a he)
      exact inv_injective h3
  have Gs : Function.Surjective G := by
    intro y
    by_cases hy : y ∈ closedInner F
    · obtain ⟨z, hz, rfl⟩ := ψb.2.2 hy
      exact ⟨z, Gin (mem_closedBall_zero_iff.mp hz)⟩
    have hyF : y ∉ F := fun h => hy (Or.inr h)
    have hyo : y ∈ outer F := by
      have : y ∈ Fᶜ := hyF
      rw [← J.union_eq] at this
      exact this.resolve_left fun h => hy (Or.inl h)
    let w := (y - a)⁻¹
    have hwy : invAt a w = y := invAt_invAt
    have hw : w ∈ closedInner Fs := Or.inl (by
      rw [hin]
      exact Or.inl (show invAt a w ∈ outer F by rwa [hwy]))
    obtain ⟨v, hv, hvw⟩ := χb.2.2 hw
    have hw0 : w ≠ 0 := fun h => by
      rw [h, invAt_zero] at hwy
      exact hdisj (Or.inl ha) (hwy ▸ hyo)
    have hv0 : v ≠ 0 := fun h => hw0 (by rw [← hvw, h, χ0])
    have hvs : v ∉ sphere (0 : ℂ) 1 := fun h => by
      have h1 : χ v ∈ Fs := by
        rw [χe h]
        exact ms.1 h
      rw [hvw] at h1
      exact hyF (hwy ▸ h1)
    have hvn : ‖v‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp hv)
      fun h => hvs (mem_sphere_zero_iff_norm.mpr h)
    have hz : 1 < ‖v⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hv0)).mpr hvn
    refine ⟨v⁻¹, ?_⟩
    rw [Gout hz, inv_inv, hvw, hwy]
  have Go : IsOpenMap G := fun U hU =>
    isOpen_image_of_injOn hU Gc.continuousOn Gi.injOn
  exact ⟨(Equiv.ofBijective G ⟨Gi, Gs⟩).toHomeomorphOfContinuousOpen Gc Go, hGe⟩

/-- **The Schoenflies theorem.** Every homeomorphism from the unit circle onto an `O`-arc of the
plane extends to a homeomorphism of the plane. See the module docstring for the route. -/
theorem schoenflies_theorem : SchoenfliesStatement := by
  intro F f
  let e : ℂ ≃ₜ EuclideanPlane := complexPlane.toHomeomorph
  have hsph : e '' sphere 0 1 = UnitCircle := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [UnitCircle, mem_sphere_zero_iff_norm]
      change ‖complexPlane z‖ = 1
      rw [complexPlane.norm_map]
      exact mem_sphere_zero_iff_norm.mp hz
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [UnitCircle, mem_sphere_zero_iff_norm] at hx
      rw [mem_sphere_zero_iff_norm]
      change ‖complexPlane.symm x‖ = 1
      rw [complexPlane.symm.norm_map]
      exact hx
  let t : sphere (0 : ℂ) 1 ≃ₜ e.symm '' F :=
    ((e.image (sphere 0 1)).trans (Homeomorph.setCongr hsph)).trans (f.trans (e.symm.image F))
  obtain ⟨φ₀⟩ := oArc_sphere
  obtain ⟨h₀, k₀, m, hv⟩ := exists_bdMatch t
  obtain ⟨G, hG⟩ := exists_homeomorph_of_bdMatch ⟨φ₀.trans t⟩ m
  refine ⟨e.symm.trans (G.trans e), fun x => ?_⟩
  have hx : e.symm x.1 ∈ sphere (0 : ℂ) 1 := by
    have h1 : x.1 ∈ e '' sphere 0 1 := by
      rw [hsph]
      exact x.2
    obtain ⟨z, hz, h2⟩ := h1
    rw [← h2, e.symm_apply_apply]
    exact hz
  change e (G (e.symm x.1)) = _
  rw [hG hx, hv ⟨_, hx⟩]
  have h3 : t ⟨e.symm x.1, hx⟩ = e.symm.image F (f x) := by
    change e.symm.image F (f _) = _
    congr 2
    apply Subtype.ext
    exact e.apply_symm_apply x.1
  rw [h3]
  exact e.apply_symm_apply _

end GraphMinor.Surface
