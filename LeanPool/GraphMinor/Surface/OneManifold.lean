/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Compact connected curves

`exists_homeomorph_circle`: a compact connected Hausdorff space in which every point has a
neighbourhood that is an open interval is a circle.

The proof grows a closed arc. Take finitely many interval charts that cover the space, and let `N`
be the finite set of the ends of the charts. An end `q` of an arc lies in a chart. Near `q`, the arc
lies on one side of `q` in the chart, as it is connected. So we can walk from `q` along the other
side towards the end of the chart. Either we reach this end, and then the arc gained a point of `N`,
or we meet the arc again. By invariance of domain in dimension one, an interior point of the arc has
a neighbourhood in the arc, so we can only meet the other end of the arc. Then we have a circle. The
circle is open and closed, so it is the whole space.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Filter

local notation "𝕀" => unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- A closed interval chart: an embedding of `[-1, 1]` that is open on `(-1, 1)`. -/
def IsCurveChart (ψ : ℝ → X) : Prop :=
  ContinuousOn ψ (Icc (-1) 1) ∧ InjOn ψ (Icc (-1) 1) ∧ IsOpen (ψ '' Ioo (-1) 1)

/-- A continuous injective map on a compact interval has a continuous inverse on the image. -/
private theorem exists_inv_Icc {a b : ℝ} {f : ℝ → X} (hc : ContinuousOn f (Icc a b))
    (hi : InjOn f (Icc a b)) :
    ∃ f' : X → ℝ, ContinuousOn f' (f '' Icc a b) ∧ LeftInvOn f' f (Icc a b) := by
  classical
  by_cases hne : (Icc a b).Nonempty
  · have hcs : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
    have hemb : IsEmbedding (fun x : Icc a b => f x.1) :=
      ((continuousOn_iff_continuous_domRestrict.mp hc).isClosedEmbedding
        fun x y h => Subtype.ext (hi x.2 y.2 h)).isEmbedding
    let E := hemb.toHomeomorph
    have hmem : ∀ y ∈ f '' Icc a b, y ∈ range fun x : Icc a b => f x.1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    refine ⟨fun y => if hy : y ∈ f '' Icc a b then (E.symm ⟨y, hmem y hy⟩).1 else 0, ?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      have h1 : (f '' Icc a b).domRestrict
          (fun y => if hy : y ∈ f '' Icc a b then (E.symm ⟨y, hmem y hy⟩).1 else 0) =
          fun y : f '' Icc a b => (E.symm ⟨y.1, hmem y.1 y.2⟩).1 := by
        ext y
        simp [Set.domRestrict, y.2]
      rw [h1]
      exact continuous_subtype_val.comp (E.symm.continuous.comp (Continuous.subtype_mk
        continuous_subtype_val _))
    · intro x hx
      have hm : f x ∈ f '' Icc a b := mem_image_of_mem f hx
      simp only [hm, dite_true]
      have h2 : (⟨f x, hmem _ hm⟩ : range fun x : Icc a b => f x.1) = E ⟨x, hx⟩ := rfl
      rw [h2, E.symm_apply_apply]
  · exact ⟨fun _ => 0, continuousOn_const, fun x hx => absurd ⟨x, hx⟩ hne⟩

namespace IsCurveChart

variable {ψ : ℝ → X}

/-- The image of an open subset of `(-1, 1)` is open. -/
theorem isOpen_image (h : IsCurveChart ψ) {O : Set ℝ} (hO : IsOpen O) (hsub : O ⊆ Ioo (-1) 1) :
    IsOpen (ψ '' O) := by
  obtain ⟨ψ', hc, hl⟩ := exists_inv_Icc h.1 h.2.1
  have hc' : ContinuousOn ψ' (ψ '' Ioo (-1) 1) := hc.mono (image_mono Ioo_subset_Icc_self)
  have heq : ψ '' O = ψ '' Ioo (-1) 1 ∩ ψ' ⁻¹' O := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨mem_image_of_mem ψ (hsub hx), ?_⟩
      change ψ' (ψ x) ∈ O
      rwa [hl (Ioo_subset_Icc_self (hsub hx))]
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      have hy' : ψ' (ψ x) ∈ O := hy
      rw [hl (Ioo_subset_Icc_self hx)] at hy'
      exact ⟨x, hy', rfl⟩
  rw [heq]
  exact hc'.isOpen_inter_preimage h.2.2 hO

/-- A continuous injective map from a real interval into a curve has a neighbourhood of the middle
point in its image. This is invariance of domain in dimension one. -/
theorem image_mem_nhds (h : IsCurveChart ψ) {f : ℝ → X} {t ε : ℝ} (hε : 0 < ε)
    (hc : ContinuousOn f (Icc (t - ε) (t + ε))) (hi : InjOn f (Icc (t - ε) (t + ε))) {s : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) (hft : f t = ψ s) : f '' Ioo (t - ε) (t + ε) ∈ 𝓝 (f t) := by
  obtain ⟨ψ', hψc, hl⟩ := exists_inv_Icc h.1 h.2.1
  have ht : t ∈ Icc (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  have hW : ψ '' Ioo (-1) 1 ∈ 𝓝 (f t) := h.2.2.mem_nhds (hft ▸ mem_image_of_mem ψ hs)
  have hfW : ∀ᶠ r in 𝓝 t, f r ∈ ψ '' Ioo (-1) 1 := by
    have hcAt : ContinuousAt f t :=
      hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
    exact hcAt hW
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp hfW
  let δ := min (δ₀ / 2) ε
  have hδ : 0 < δ := lt_min (half_pos hδ₀) hε
  have hδε : δ ≤ ε := min_le_right _ _
  have hsubI : Icc (t - δ) (t + δ) ⊆ Icc (t - ε) (t + ε) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hmemW : ∀ r ∈ Icc (t - δ) (t + δ), f r ∈ ψ '' Ioo (-1) 1 := by
    intro r hr
    refine hball r (Metric.mem_ball.mpr ?_)
    rw [Real.dist_eq, abs_lt]
    have : δ ≤ δ₀ / 2 := min_le_left _ _
    constructor <;> linarith [hr.1, hr.2]
  let g : ℝ → ℝ := fun r => ψ' (f r)
  have hψsub : ψ '' Ioo (-1) 1 ⊆ ψ '' Icc (-1) 1 := image_mono Ioo_subset_Icc_self
  have hgc : ContinuousOn g (Icc (t - δ) (t + δ)) :=
    hψc.comp (hc.mono hsubI) fun r hr => hψsub (hmemW r hr)
  have hψf : ∀ r ∈ Icc (t - δ) (t + δ), ψ (g r) = f r := by
    intro r hr
    obtain ⟨x, hx, hxe⟩ := hmemW r hr
    change ψ (ψ' (f r)) = f r
    rw [← hxe, hl (Ioo_subset_Icc_self hx)]
  have hgi : InjOn g (Icc (t - δ) (t + δ)) := fun x hx y hy he =>
    hi (hsubI hx) (hsubI hy) (by rw [← hψf x hx, ← hψf y hy, he])
  have hgIoo : ∀ r ∈ Icc (t - δ) (t + δ), g r ∈ Ioo (-1 : ℝ) 1 := by
    intro r hr
    obtain ⟨x, hx, hxe⟩ := hmemW r hr
    change ψ' (f r) ∈ _
    rwa [← hxe, hl (Ioo_subset_Icc_self hx)]
  have hgimg : ∃ O : Set ℝ, IsOpen O ∧ g t ∈ O ∧ O ⊆ g '' Ioo (t - δ) (t + δ) := by
    have hlo : t - δ < t + δ := by linarith
    have hint : IsOpen (g '' Ioo (t - δ) (t + δ)) := by
      rcases hgc.strictMonoOn_of_injOn_Icc' hlo.le hgi with hm | hm
      · have himg : g '' Ioo (t - δ) (t + δ) = Ioo (g (t - δ)) (g (t + δ)) := by
          refine Subset.antisymm ?_ fun y hy => ?_
          · rintro _ ⟨r, hr, rfl⟩
            exact ⟨hm (left_mem_Icc.mpr hlo.le) (Ioo_subset_Icc_self hr) hr.1,
              hm (Ioo_subset_Icc_self hr) (right_mem_Icc.mpr hlo.le) hr.2⟩
          · obtain ⟨r, hr, hre⟩ := intermediate_value_Ioo hlo.le hgc hy
            exact ⟨r, hr, hre⟩
        rw [himg]
        exact isOpen_Ioo
      · have himg : g '' Ioo (t - δ) (t + δ) = Ioo (g (t + δ)) (g (t - δ)) := by
          refine Subset.antisymm ?_ fun y hy => ?_
          · rintro _ ⟨r, hr, rfl⟩
            exact ⟨hm (Ioo_subset_Icc_self hr) (right_mem_Icc.mpr hlo.le) hr.2,
              hm (left_mem_Icc.mpr hlo.le) (Ioo_subset_Icc_self hr) hr.1⟩
          · obtain ⟨r, hr, hre⟩ := intermediate_value_Ioo' hlo.le hgc hy
            exact ⟨r, hr, hre⟩
        rw [himg]
        exact isOpen_Ioo
    exact ⟨_, hint, ⟨t, ⟨by linarith, by linarith⟩, rfl⟩, Subset.rfl⟩
  obtain ⟨O, hO, htO, hOsub⟩ := hgimg
  have hOI : O ⊆ Ioo (-1) 1 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := hOsub hy
    exact hgIoo r (Ioo_subset_Icc_self hr)
  have hopen := h.isOpen_image hO hOI
  refine mem_of_superset (hopen.mem_nhds ?_) ?_
  · rw [← hψf t ⟨by linarith, by linarith⟩]
    exact mem_image_of_mem ψ htO
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hOsub hy
    refine ⟨r, ⟨?_, ?_⟩, (hψf r (Ioo_subset_Icc_self hr)).symm⟩
    · linarith [hr.1]
    · linarith [hr.2]

/-- Near an end of an arc, the arc lies on one side of the end in a chart. So the other side misses
the arc. -/
theorem exists_free_side (h : IsCurveChart ψ) {a : 𝕀 → X} (ha : IsArcMap a) {q' : ℝ}
    (hq : q' ∈ Ioo (-1 : ℝ) 1) (heq : a 1 = ψ q') :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ r > 0, ∀ s ∈ Ioc 0 r, q' + σ * s ∈ Ioo (-1 : ℝ) 1 ∧
      ψ (q' + σ * s) ∉ range a := by
  obtain ⟨ψ', hψc, hl⟩ := exists_inv_Icc h.1 h.2.1
  have hW : a ⁻¹' (ψ '' Ioo (-1) 1) ∈ 𝓝 (1 : 𝕀) :=
    (h.2.2.preimage ha.1).mem_nhds (by
      change a 1 ∈ ψ '' Ioo (-1) 1
      rw [heq]
      exact mem_image_of_mem ψ hq)
  obtain ⟨t₀, ht₀, hsub⟩ := exists_Ioc_subset_of_mem_nhds hW ⟨0, zero_lt_one⟩
  have hsub' : ψ '' Ioo (-1) 1 ⊆ ψ '' Icc (-1) 1 := image_mono Ioo_subset_Icc_self
  let c : 𝕀 → ℝ := fun t => ψ' (a t)
  have hψa : ∀ t ∈ Ioc t₀ 1, ψ (c t) = a t := by
    intro t ht
    obtain ⟨x, hx, hxe⟩ := hsub ht
    change ψ (ψ' (a t)) = a t
    rw [← hxe, hl (Ioo_subset_Icc_self hx)]
  have hcc : ContinuousOn c (Ioo t₀ 1) :=
    hψc.comp ha.1.continuousOn fun t ht => hsub' (hsub (Ioo_subset_Ioc_self ht))
  have hne : ∀ t ∈ Ioo t₀ 1, c t ≠ q' := fun t ht he => by
    have h1 := hψa t (Ioo_subset_Ioc_self ht)
    rw [he, ← heq] at h1
    exact ht.2.ne (ha.2 h1.symm)
  have hpre : IsPreconnected (c '' Ioo t₀ 1) := isPreconnected_Ioo.image c hcc
  have hsplit : c '' Ioo t₀ 1 ⊆ Iio q' ∪ Ioi q' := by
    rintro _ ⟨t, ht, rfl⟩
    exact (lt_or_gt_of_ne (hne t ht)).imp id id
  have hlt : t₀ < 1 := ht₀
  obtain ⟨t₁, ht₁0, ht₁1⟩ := exists_between hlt
  have hA : IsClosed (a '' Iic t₁) := (isClosed_Iic.isCompact.image ha.1).isClosed
  have hq1 : ψ q' ∉ a '' Iic t₁ := by
    rintro ⟨t, ht, he⟩
    have h1 : t = 1 := ha.2 (he.trans heq.symm)
    rw [h1] at ht
    exact absurd ht (not_le.mpr ht₁1)
  have hcont : ContinuousAt ψ q' :=
    h.1.continuousAt (Icc_mem_nhds hq.1 hq.2)
  have hev : ∀ᶠ x in 𝓝 q', ψ x ∉ a '' Iic t₁ ∧ x ∈ Ioo (-1 : ℝ) 1 :=
    (hcont.eventually (hA.isOpen_compl.mem_nhds hq1)).and (Ioo_mem_nhds hq.1 hq.2)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hfree : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (∀ t ∈ Ioo t₀ 1, σ * (c t - q') ≤ 0) →
      ∃ r > 0, ∀ s ∈ Ioc 0 r, q' + σ * s ∈ Ioo (-1 : ℝ) 1 ∧ ψ (q' + σ * s) ∉ range a := by
    intro σ hσ hside
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    refine ⟨δ / 2, half_pos hδ, fun s hs => ?_⟩
    have hd : q' + σ * s ∈ Metric.ball q' δ := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_mul]
      have : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [this, one_mul, abs_of_pos hs.1]
      linarith [hs.2]
    obtain ⟨h1, h2⟩ := hball _ hd
    refine ⟨h2, ?_⟩
    rintro ⟨t, he⟩
    have ht : t₁ < t := by
      by_contra hn
      exact h1 ⟨t, not_lt.mp hn, he⟩
    by_cases ht1 : t = 1
    · rw [ht1, heq] at he
      have h3 := h.2.1 (Ioo_subset_Icc_self hq) (Ioo_subset_Icc_self h2) he
      have h4 : σ * s = 0 := by linarith
      rcases mul_eq_zero.mp h4 with h5 | h5
      · rcases hσ with rfl | rfl <;> norm_num at h5
      · exact hs.1.ne' h5
    · have ht2 : t ∈ Ioo t₀ 1 := ⟨ht₁0.trans ht, lt_of_le_of_ne unitInterval.le_one' ht1⟩
      have h6 : c t = q' + σ * s := by
        change ψ' (a t) = _
        rw [he, hl (Ioo_subset_Icc_self h2)]
      have h7 := hside t ht2
      rw [h6] at h7
      have h8 : σ * (q' + σ * s - q') = s := by
        rw [add_sub_cancel_left, ← mul_assoc, hσ2, one_mul]
      linarith [hs.1]
  have hdis : Disjoint (Iio q') (Ioi q') :=
    Set.disjoint_left.mpr fun _ h1 h2 => lt_asymm h1 h2
  rcases (isPreconnected_iff_subset_of_disjoint.mp hpre) _ _ isOpen_Iio isOpen_Ioi hsplit
    (by rw [hdis.inter_eq]; simp) with h1 | h1
  · refine ⟨1, Or.inl rfl, hfree 1 (Or.inl rfl) fun t ht => ?_⟩
    have : c t < q' := h1 (mem_image_of_mem c ht)
    linarith
  · refine ⟨-1, Or.inr rfl, hfree (-1) (Or.inr rfl) fun t ht => ?_⟩
    have : q' < c t := h1 (mem_image_of_mem c ht)
    linarith

end IsCurveChart

omit [T2Space X] in
/-- Two arcs that meet only at one end of each join to one arc. -/
theorem exists_arc_join {a b : 𝕀 → X} (ha : IsArcMap a) (hb : IsArcMap b) (h : a 1 = b 0)
    (hm : ∀ s t, a s = b t → s = 1 ∧ t = 0) :
    ∃ c : 𝕀 → X, IsArcMap c ∧ range c = range a ∪ range b ∧ c 0 = a 0 ∧ c 1 = b 1 := by
  let p : Path (a 0) (a 1) := ⟨⟨a, ha.1⟩, rfl, rfl⟩
  let p' : Path (a 1) (b 1) := ⟨⟨b, hb.1⟩, h.symm, rfl⟩
  refine ⟨p.trans p', ⟨(p.trans p').continuous, ?_⟩, ?_, (p.trans p').source,
    (p.trans p').target⟩
  · have hp : ∀ t, p t = a t := fun _ => rfl
    have hp' : ∀ t, p' t = b t := fun _ => rfl
    intro s t he
    rw [Path.trans_apply, Path.trans_apply] at he
    by_cases hs : s.1 ≤ 1 / 2 <;> by_cases ht : t.1 ≤ 1 / 2
    · simp only [hs, ht, ↓reduceDIte, hp] at he
      have h1 := congrArg Subtype.val (ha.2 he)
      simp only at h1
      exact Subtype.ext (by linarith)
    · simp only [hs, ht, ↓reduceDIte, hp, hp'] at he
      have h1 := congrArg Subtype.val (hm _ _ he).2
      simp only at h1
      have h2 : (0 : 𝕀).1 = 0 := rfl
      exact absurd ht (by rw [not_le]; linarith)
    · simp only [hs, ht, ↓reduceDIte, hp', hp] at he
      have h1 := congrArg Subtype.val (hm _ _ he.symm).2
      simp only at h1
      have h2 : (0 : 𝕀).1 = 0 := rfl
      exact absurd hs (by rw [not_le]; linarith)
    · simp only [hs, ht, ↓reduceDIte, hp'] at he
      have h1 := congrArg Subtype.val (hb.2 he)
      simp only at h1
      exact Subtype.ext (by linarith)
  · rw [Path.trans_range]
    rfl

/-- The real form of a path. -/
private noncomputable def toReal (a : 𝕀 → X) (t : ℝ) : X := a (projIcc 0 1 zero_le_one t)

omit [TopologicalSpace X] [T2Space X] in
private theorem toReal_coe (a : 𝕀 → X) (t : 𝕀) : toReal a t.1 = a t := by
  rw [toReal, projIcc_val]

private theorem isOpen_range_of_circle {f : Circle → X} (hf : Continuous f)
    (hi : Function.Injective f) (hch : ∀ x : X, ∃ ψ : ℝ → X, IsCurveChart ψ ∧ x ∈ ψ '' Ioo (-1) 1) :
    IsOpen (range f) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro _ ⟨w, rfl⟩
  obtain ⟨χ, hχ, s, hs, hse⟩ := hch (f w)
  let F : ℝ → X := fun r => f (w * Circle.exp r)
  have hFc : Continuous F := hf.comp (continuous_const.mul Circle.exp.continuous)
  have hF0 : F 0 = f w := by simp [F]
  have hpi := Real.two_le_pi
  have hFi : InjOn F (Icc (0 - 1) (0 + 1)) := by
    intro r hr r' hr' he
    have h1 : Circle.exp r = Circle.exp r' := mul_left_cancel (hi he)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    have h2 : (m : ℝ) * (2 * Real.pi) = r - r' := by linarith
    have h3 : |r - r'| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2, hr'.1, hr'.2]
    by_contra hne
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hne
      simp only [Int.cast_zero, zero_mul] at h2
      linarith
    have h4 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    have h5 : |r - r'| = |(m : ℝ)| * (2 * Real.pi) := by
      rw [← h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith
  have h1 := hχ.image_mem_nhds one_pos (t := 0) hFc.continuousOn hFi hs (by rw [hF0, hse])
  rw [hF0] at h1
  refine mem_of_superset h1 ?_
  rintro _ ⟨r, -, rfl⟩
  exact ⟨_, rfl⟩

/-- An arc and a second arc with the same ends that meets it only in the ends make the space a
circle. -/
private theorem circle_of_two_arcs [ConnectedSpace X] {a b : 𝕀 → X}
    (ha : IsArcMap a) (hb : IsArcMap b) (h0 : a 0 = b 0) (h1 : a 1 = b 1)
    (hm : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hch : ∀ x : X, ∃ ψ : ℝ → X, IsCurveChart ψ ∧ x ∈ ψ '' Ioo (-1) 1) : Nonempty (Circle ≃ₜ X)
      := by
  obtain ⟨φ⟩ := oArc_of_two_arcs ha hb h0 h1 hm
  let f : Circle → X := fun w => (φ w).1
  have hfc : Continuous f := continuous_subtype_val.comp φ.continuous
  have hfi : Function.Injective f := fun w w' he => φ.injective (Subtype.ext he)
  have hr : range f = range a ∪ range b := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (φ w).2
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp [f]⟩
  have hO := isOpen_range_of_circle hfc hfi hch
  have hC : IsClosed (range f) := (isCompact_range hfc).isClosed
  have hu : range f = univ := IsClopen.eq_univ ⟨hC, hO⟩ (range_nonempty f)
  exact ⟨φ.trans ((Homeomorph.setCongr (hr.symm.trans hu)).trans (Homeomorph.Set.univ X))⟩

/-- One step of the growth of an arc. -/
private theorem extend_arc [ConnectedSpace X]
    (hch : ∀ x : X, ∃ ψ : ℝ → X, IsCurveChart ψ ∧ x ∈ ψ '' Ioo (-1) 1) {N : Set X}
    (hN : ∀ x : X, ∃ ψ : ℝ → X, IsCurveChart ψ ∧ x ∈ ψ '' Ioo (-1) 1 ∧ ψ (-1) ∈ N ∧ ψ 1 ∈ N)
    {a : 𝕀 → X} (ha : IsArcMap a) :
    Nonempty (Circle ≃ₜ X) ∨ ∃ a', IsArcMap a' ∧ range a ⊆ range a' ∧ ∃ y ∈ N, y ∉ range a ∧
      y ∈ range a' := by
  obtain ⟨ψ, hψ, ⟨q', hq', hqe⟩, hN1, hN2⟩ := hN (a 1)
  obtain ⟨σ, hσ, r, hr, hfree⟩ := hψ.exists_free_side ha hq' hqe.symm
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  let L : ℝ := 1 - σ * q'
  have hL : 0 < L := by
    rcases hσ with rfl | rfl
    · change 0 < 1 - 1 * q'
      linarith [hq'.2]
    · change 0 < 1 - -1 * q'
      linarith [hq'.1]
  let seg : ℝ → X := fun s => ψ (q' + σ * s)
  have hmem : ∀ s ∈ Icc 0 L, q' + σ * s ∈ Icc (-1 : ℝ) 1 := by
    intro s hs
    have h1 := hs.1
    have h2 : s ≤ 1 - σ * q' := hs.2
    have hq1 := hq'.1
    have hq2 := hq'.2
    rcases hσ with rfl | rfl
    · constructor <;> linarith
    · constructor <;> linarith
  have hsegc : ContinuousOn seg (Icc 0 L) :=
    hψ.1.comp (by fun_prop) hmem
  have hsegi : InjOn seg (Icc 0 L) := by
    intro s hs s' hs' he
    have h1 := hψ.2.1 (hmem s hs) (hmem s' hs') he
    have h2 : σ * s = σ * s' := by linarith
    have h3 : σ * (σ * s) = σ * (σ * s') := by rw [h2]
    rwa [← mul_assoc, ← mul_assoc, hσ2, one_mul, one_mul] at h3
  have hseg0 : seg 0 = a 1 := by
    change ψ (q' + σ * 0) = a 1
    rw [mul_zero, add_zero]
    exact hqe
  have hsegL : seg L ∈ N := by
    have h1 : q' + σ * L = σ := by
      change q' + σ * (1 - σ * q') = σ
      have : σ * (1 - σ * q') = σ - σ * σ * q' := by ring
      rw [this, hσ2]
      ring
    change ψ (q' + σ * L) ∈ N
    rw [h1]
    rcases hσ with rfl | rfl
    · exact hN2
    · exact hN1
  let r' := min r L
  have hr' : 0 < r' := lt_min hr hL
  have hr'L : r' ≤ L := min_le_right _ _
  have hAcl : IsClosed (range a) := (isCompact_range ha.1).isClosed
  have hB : IsCompact (Icc r' L ∩ seg ⁻¹' range a) := by
    have hcl : IsClosed (Icc r' L ∩ seg ⁻¹' range a) :=
      (hsegc.mono (Icc_subset_Icc_left hr'.le)).preimage_isClosed_of_isClosed isClosed_Icc hAcl
    exact isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  have hnear : ∀ s ∈ Ioc 0 r', seg s ∉ range a := fun s hs =>
    (hfree s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩).2
  have hsmall : ∀ u : 𝕀, 0 ≤ L * u.1 ∧ L * u.1 ≤ L := fun u => by
    constructor
    · exact mul_nonneg hL.le u.2.1
    · nlinarith [u.2.2]
  by_cases hemp : (Icc r' L ∩ seg ⁻¹' range a).Nonempty
  · left
    obtain ⟨s₀, ⟨hs₀, hs₀a⟩, hleast⟩ := hB.exists_isLeast hemp
    have hs0pos : 0 < s₀ := lt_of_lt_of_le hr' hs₀.1
    have hbefore : ∀ s ∈ Ioo 0 s₀, seg s ∉ range a := by
      intro s hs hin
      by_cases hsr : s ≤ r'
      · exact hnear s ⟨hs.1, hsr⟩ hin
      · have := hleast ⟨⟨(not_le.mp hsr).le, hs.2.le.trans hs₀.2⟩, hin⟩
        exact absurd hs.2 (not_lt.mpr this)
    have hsL : Icc 0 s₀ ⊆ Icc 0 L := Icc_subset_Icc_right hs₀.2
    obtain ⟨t, ht⟩ := hs₀a
    have ht1 : t ≠ 1 := by
      rintro rfl
      have := hsegi (right_mem_Icc.mpr hL.le |> fun _ => (⟨le_rfl, hL.le⟩ : (0 : ℝ) ∈ Icc 0 L))
        (⟨hs0pos.le, hs₀.2⟩ : s₀ ∈ Icc 0 L) (hseg0.trans ht)
      exact hs0pos.ne this
    have ht0 : t = 0 := by
      by_contra ht0
      have hpos : 0 < t.1 := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
      have hlt : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
      obtain ⟨χ, hχ, s, hs, hse⟩ := hch (a t)
      let ε := min t.1 (1 - t.1)
      have hε : 0 < ε := lt_min hpos (by linarith)
      have hε1 : ε ≤ t.1 := min_le_left _ _
      have hε2 : ε ≤ 1 - t.1 := min_le_right _ _
      have hI : Icc (t.1 - ε) (t.1 + ε) ⊆ Icc (0 : ℝ) 1 :=
        Icc_subset_Icc (by linarith) (by linarith)
      have hfc : ContinuousOn (toReal a) (Icc (t.1 - ε) (t.1 + ε)) :=
        (ha.1.comp continuous_projIcc).continuousOn
      have hfi : InjOn (toReal a) (Icc (t.1 - ε) (t.1 + ε)) := by
        intro x hx y hy he
        have h1 := ha.2 he
        have h2 := congrArg Subtype.val h1
        rwa [projIcc_of_mem zero_le_one (hI hx), projIcc_of_mem zero_le_one (hI hy)] at h2
      have hnh := hχ.image_mem_nhds hε hfc hfi hs (by rw [toReal_coe, hse])
      rw [toReal_coe, ht] at hnh
      have hcl : seg s₀ ∈ closure (seg '' Ioo 0 s₀) := by
        refine ContinuousOn.image_closure (s := Ioo 0 s₀) ?_ ?_
        · rw [closure_Ioo hs0pos.ne]
          exact hsegc.mono hsL
        · exact mem_image_of_mem seg (by
            rw [closure_Ioo hs0pos.ne]
            exact ⟨hs0pos.le, le_rfl⟩)
      obtain ⟨_, hz, s', hs', rfl⟩ := mem_closure_iff_nhds.mp hcl _ hnh
      refine hbefore s' hs' ?_
      obtain ⟨x, -, hx⟩ := hz
      exact ⟨_, hx⟩
    subst ht0
    let b : 𝕀 → X := fun u => seg (s₀ * (1 - u.1))
    have hbmem : ∀ u : 𝕀, s₀ * (1 - u.1) ∈ Icc 0 s₀ := fun u =>
      ⟨mul_nonneg hs0pos.le (by linarith [u.2.2]), by nlinarith [u.2.1]⟩
    have hb : IsArcMap b := by
      refine ⟨hsegc.comp_continuous (by fun_prop) fun u => hsL (hbmem u), fun u v he => ?_⟩
      have h1 := hsegi (hsL (hbmem u)) (hsL (hbmem v)) he
      have h2 : 1 - u.1 = 1 - v.1 := mul_left_cancel₀ hs0pos.ne' h1
      exact Subtype.ext (by linarith)
    refine circle_of_two_arcs ha hb ?_ ?_ ?_ hch
    · change a 0 = seg (s₀ * (1 - (0 : ℝ)))
      rw [sub_zero, mul_one, ht]
    · change a 1 = seg (s₀ * (1 - (1 : ℝ)))
      rw [sub_self, mul_zero, hseg0]
    · intro v u he
      have hu0 : u = 0 ∨ u = 1 := by
        by_contra hn
        push Not at hn
        have h1 : 0 < u.1 := lt_of_le_of_ne u.2.1 fun h => hn.1 (Subtype.ext h.symm)
        have h2 : u.1 < 1 := lt_of_le_of_ne u.2.2 fun h => hn.2 (Subtype.ext h)
        refine hbefore _ ⟨mul_pos hs0pos (by linarith), ?_⟩ ⟨v, he⟩
        nlinarith
      rcases hu0 with rfl | rfl
      · left
        refine ⟨ha.2 ?_, rfl⟩
        rw [he]
        change seg (s₀ * (1 - (0 : ℝ))) = a 0
        rw [sub_zero, mul_one, ← ht]
      · right
        refine ⟨ha.2 ?_, rfl⟩
        rw [he]
        change seg (s₀ * (1 - (1 : ℝ))) = a 1
        rw [sub_self, mul_zero, hseg0]
  · right
    have hoff : ∀ s ∈ Ioc 0 L, seg s ∉ range a := by
      intro s hs hin
      by_cases hsr : s ≤ r'
      · exact hnear s ⟨hs.1, hsr⟩ hin
      · exact hemp ⟨s, ⟨(not_le.mp hsr).le, hs.2⟩, hin⟩
    let b : 𝕀 → X := fun u => seg (L * u.1)
    have hb : IsArcMap b := by
      refine ⟨hsegc.comp_continuous (by fun_prop) fun u => hsmall u, fun u v he => ?_⟩
      have h1 := hsegi (hsmall u) (hsmall v) he
      exact Subtype.ext (mul_left_cancel₀ hL.ne' h1)
    have hb0 : b 0 = a 1 := by
      change seg (L * (0 : ℝ)) = a 1
      rw [mul_zero, hseg0]
    obtain ⟨c, hc, hrc, -, -⟩ := exists_arc_join ha hb hb0.symm (fun s t he => by
      have ht : t = 0 := by
        by_contra hn
        have h1 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun h => hn (Subtype.ext h.symm)
        exact hoff _ ⟨mul_pos hL h1, (hsmall t).2⟩ ⟨s, he⟩
      subst ht
      exact ⟨ha.2 (he.trans hb0), rfl⟩)
    refine ⟨c, hc, hrc ▸ subset_union_left, seg L, hsegL, hoff L ⟨hL, le_rfl⟩, ?_⟩
    rw [hrc]
    refine Or.inr ⟨1, ?_⟩
    change seg (L * (1 : ℝ)) = seg L
    rw [mul_one]

/-- **A compact connected curve is a circle.** See the module docstring for the route. -/
theorem exists_homeomorph_circle [CompactSpace X] [ConnectedSpace X]
    (hch : ∀ x : X, ∃ ψ, IsCurveChart ψ ∧ x ∈ ψ '' Ioo (-1) 1) : Nonempty (Circle ≃ₜ X) := by
  classical
  choose ψ hψ hmem using hch
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => ψ x '' Ioo (-1) 1)
    (fun x _ => (hψ x).2.2.mem_nhds (hmem x))
  have hcov : ∀ x, ∃ y ∈ t, x ∈ ψ y '' Ioo (-1) 1 := fun x => by
    have := ht.2 (mem_univ x)
    simpa using this
  let N : Set X := ⋃ y ∈ t, {ψ y (-1), ψ y 1}
  have hNfin : N.Finite := t.finite_toSet.biUnion fun _ _ => by simp
  have hN : ∀ x, ∃ χ, IsCurveChart χ ∧ x ∈ χ '' Ioo (-1) 1 ∧ χ (-1) ∈ N ∧ χ 1 ∈ N := fun x => by
    obtain ⟨y, hy, hx⟩ := hcov x
    exact ⟨ψ y, hψ y, hx, mem_biUnion hy (Or.inl rfl), mem_biUnion hy (Or.inr rfl)⟩
  have hch : ∀ x : X, ∃ χ, IsCurveChart χ ∧ x ∈ χ '' Ioo (-1) 1 := fun x => ⟨ψ x, hψ x, hmem x⟩
  have key : ∀ n : ℕ, ∀ a : 𝕀 → X, IsArcMap a → (N \ range a).ncard = n →
      Nonempty (Circle ≃ₜ X) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha hn
      rcases extend_arc hch hN ha with h | ⟨a', ha', hsub, y, hyN, hy, hy'⟩
      · exact h
      · refine ih _ ?_ a' ha' rfl
        rw [← hn]
        refine ncard_lt_ncard ⟨fun z hz => ⟨hz.1, fun h => hz.2 (?_)⟩, fun h => ?_⟩
          (hNfin.subset sdiff_subset)
        · exact absurd (hsub h) hz.2
        · exact (h ⟨hyN, hy⟩).2 hy'
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  let a₀ : 𝕀 → X := fun u => ψ x₀ (2 * u.1 - 1)
  have ha₀ : IsArcMap a₀ := by
    have hmemI : ∀ u : 𝕀, 2 * u.1 - 1 ∈ Icc (-1 : ℝ) 1 := fun u => by
      constructor <;> linarith [u.2.1, u.2.2]
    refine ⟨(hψ x₀).1.comp_continuous (by fun_prop) hmemI, fun u v he => ?_⟩
    have h1 := (hψ x₀).2.1 (hmemI u) (hmemI v) he
    exact Subtype.ext (by linarith)
  exact key _ a₀ ha₀ rfl

end GraphMinor.Surface
