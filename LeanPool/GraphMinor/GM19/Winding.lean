/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CircleLift

/-!
# Winding of plane curves

We measure how far a curve in the punctured plane turns around the origin, as the change of a
continuous angle along the curve. No part of
Mathlib gives this for curves that are only continuous, and the orientation of the plane in
`GM19/PlaneOrientation.lean` needs it.

Three facts carry the weight. A loop near a loop turns as far (`turn_eq_of_near`), so the turning of
a loop does not change along a
homotopy (`turn_eq_of_homotopy`). A loop far from the point does not turn (`turn_eq_zero_of_far`).
And two arcs with the same ends turn
equally around a point that can be joined to a far point without meeting them (`turn_eq_of_path`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology Filter

/-- `L` is a continuous angle of the curve `g`. -/
def IsAngle (g : ℝ → ℂ) (L : ℝ → ℝ) : Prop :=
  Continuous L ∧ ∀ t, g t = ‖g t‖ * Complex.exp (L t * Complex.I)

theorem exists_isAngle {g : ℝ → ℂ} (hg : Continuous g) (h0 : ∀ t, g t ≠ 0) : ∃ L, IsAngle g L := by
  have hn : ∀ t, ‖g t‖ ≠ 0 := fun t => norm_ne_zero_iff.mpr (h0 t)
  let f : ℝ → Circle := fun t => ⟨((‖g t‖ : ℝ) : ℂ)⁻¹ * g t, by
    rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk]
    change _ ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (hn t)]⟩
  have hf : Continuous f := by
    refine continuous_induced_rng.mpr ?_
    change Continuous fun t => ((‖g t‖ : ℝ) : ℂ)⁻¹ * g t
    exact (Continuous.inv₀ (Complex.continuous_ofReal.comp hg.norm) fun t
      => Complex.ofReal_ne_zero.mpr (hn t)).mul hg
  obtain ⟨L, hL, hl⟩ := exists_circle_lift_map ⟨f, hf⟩
  refine ⟨L, hL, fun t => ?_⟩
  have h1 := congrArg (fun c : Circle => (c : ℂ)) (hl t)
  simp only [Circle.coe_exp, ContinuousMap.coe_mk] at h1
  rw [h1]
  change g t = _ * (((‖g t‖ : ℝ) : ℂ)⁻¹ * g t)
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hn t)), one_mul]

theorem IsAngle.exp_eq {g : ℝ → ℂ} {L M : ℝ → ℝ} (hL : IsAngle g L) (hM : IsAngle g M)
  (h0 : ∀ t, g t ≠ 0) (t : ℝ) :
    Circle.exp (L t) = Circle.exp (M t) := by
  apply Circle.ext
  rw [Circle.coe_exp, Circle.coe_exp]
  have hn : ((‖g t‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (h0 t))
  exact mul_left_cancel₀ hn ((hL.2 t).symm.trans (hM.2 t))

theorem IsAngle.diff {g : ℝ → ℂ} {L M : ℝ → ℝ} (hL : IsAngle g L) (hM : IsAngle g M)
  (h0 : ∀ t, g t ≠ 0) (s t : ℝ) :
    L t - L s = M t - M s := by
  have := lift_diff_const hL.1 hM.1 (hL.exp_eq hM h0) s t
  linarith

/-- How far the curve `g` turns from time `s` to time `t`. -/
noncomputable def turn (g : ℝ → ℂ) (s t : ℝ) : ℝ :=
  open Classical in if h : ∃ L, IsAngle g L then h.choose t - h.choose s else 0

theorem IsAngle.turn_eq {g : ℝ → ℂ} {L : ℝ → ℝ} (hL : IsAngle g L) (h0 : ∀ t, g t ≠ 0) (s t : ℝ) :
    turn g s t = L t - L s := by
  have h : ∃ L, IsAngle g L := ⟨L, hL⟩
  rw [turn, dite_eq_left h]
  exact h.choose_spec.diff hL h0 s t

theorem IsAngle.comp {g : ℝ → ℂ} {L f : ℝ → ℝ} (hL : IsAngle g L) (hf : Continuous f) : IsAngle
  (fun t => g (f t)) fun t => L (f t) :=
  ⟨hL.1.comp hf, fun t => hL.2 (f t)⟩

theorem IsAngle.mul {g k : ℝ → ℂ} {L M : ℝ → ℝ} (hL : IsAngle g L) (hM : IsAngle k M) :
    IsAngle (fun t => g t * k t) fun t => L t + M t := by
  refine ⟨hL.1.add hM.1, fun t => ?_⟩
  change g t * k t = ((‖g t * k t‖ : ℝ) : ℂ) * Complex.exp (((L t + M t : ℝ) : ℂ) * Complex.I)
  rw [norm_mul, Complex.ofReal_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  conv_lhs => rw [hL.2 t, hM.2 t]
  ring

theorem isAngle_const {c : ℂ} (_hc : c ≠ 0) : ∃ α : ℝ, IsAngle (fun _ => c) fun _ => α :=
  ⟨Complex.arg c, continuous_const, fun _ => (Complex.norm_mul_exp_arg_mul_I c).symm⟩

theorem turn_comp {g : ℝ → ℂ} (hg : Continuous g) (h0 : ∀ t, g t ≠ 0) {f : ℝ → ℝ}
  (hf : Continuous f) (s t : ℝ) :
    turn (fun x => g (f x)) s t = turn g (f s) (f t) := by
  obtain ⟨L, hL⟩ := exists_isAngle hg h0
  rw [(hL.comp hf).turn_eq (fun x => h0 _), hL.turn_eq h0]

theorem turn_add {g : ℝ → ℂ} (hg : Continuous g) (h0 : ∀ t, g t ≠ 0) (s t u : ℝ) : turn g s t +
  turn g t u = turn g s u := by
  obtain ⟨L, hL⟩ := exists_isAngle hg h0
  rw [hL.turn_eq h0, hL.turn_eq h0, hL.turn_eq h0]
  ring

theorem turn_self {g : ℝ → ℂ} (hg : Continuous g) (h0 : ∀ t, g t ≠ 0) (s : ℝ) : turn g s s = 0 := by
  obtain ⟨L, hL⟩ := exists_isAngle hg h0
  rw [hL.turn_eq h0, sub_self]

/-- A loop turns through a multiple of `2π`. -/
theorem exists_turn_eq_mul {g : ℝ → ℂ} (hg : Continuous g) (h0 : ∀ t, g t ≠ 0) {s t : ℝ} (hst : g s
  = g t) :
    ∃ m : ℤ, turn g s t = m * (2 * Real.pi) := by
  obtain ⟨L, hL⟩ := exists_isAngle hg h0
  have hn : ((‖g s‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (h0 s))
  have h1 : Circle.exp (L s) = Circle.exp (L t) := by
    apply Circle.ext
    rw [Circle.coe_exp, Circle.coe_exp]
    have h2 := hL.2 s
    have h3 := hL.2 t
    rw [← hst] at h3
    exact mul_left_cancel₀ hn (h2.symm.trans h3)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
  refine ⟨-m, ?_⟩
  rw [hL.turn_eq h0, hm]
  push_cast
  ring

/-- A loop near a loop turns as far. -/
theorem turn_eq_of_near {g k : ℝ → ℂ} (hg : Continuous g) (hk : Continuous k) (h0 : ∀ t, g t ≠ 0)
  (hn : ∀ t, ‖k t - g t‖ < ‖g t‖)
    {s t : ℝ} (hgs : g s = g t) (hks : k s = k t) : turn k s t = turn g s t := by
  have h0k : ∀ t, k t ≠ 0 := fun t ht => by
    have := hn t
    rw [ht, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  let r : ℝ → ℂ := fun t => k t / g t
  have hr : Continuous r := hk.div hg h0
  have hre : ∀ t, r t ∈ Complex.slitPlane := fun t => by
    left
    have h1 : ‖r t - 1‖ < 1 := by
      have : r t - 1 = (k t - g t) / g t := by
        simp only [r]
        field_simp [h0 t]
      rw [this, norm_div, div_lt_one (norm_pos_iff.mpr (h0 t))]
      exact hn t
    have h2 := Complex.abs_re_le_norm (r t - 1)
    have h3 := abs_lt.mp (lt_of_le_of_lt h2 h1)
    simp only [Complex.sub_re, Complex.one_re] at h3
    linarith [h3.1]
  have ha : IsAngle r fun t => Complex.arg (r t) :=
    ⟨continuous_iff_continuousAt.mpr fun t => (Complex.continuousAt_arg
      (hre t)).comp hr.continuousAt,
      fun t => (Complex.norm_mul_exp_arg_mul_I (r t)).symm⟩
  obtain ⟨L, hL⟩ := exists_isAngle hg h0
  have hm := hL.mul ha
  have he : (fun t => g t * r t) = k := by
    funext t
    simp only [r]
    field_simp [h0 t]
  rw [he] at hm
  rw [hm.turn_eq h0k, hL.turn_eq h0]
  have : r s = r t := by simp only [r, hgs, hks]
  rw [this]
  ring

/-- A loop far from the origin does not turn around the point `p`. -/
theorem turn_eq_zero_of_far {d : ℝ → ℂ} (hd : Continuous d) {p : ℂ} (hb : ∀ t, ‖d t‖ < ‖p‖) {s t :
  ℝ} (hst : d s = d t) :
    turn (fun x => d x - p) s t = 0 := by
  have hp : -p ≠ 0 := neg_ne_zero.mpr fun h => by
    have := hb 0
    rw [h, norm_zero] at this
    exact absurd this (not_lt.mpr (norm_nonneg _))
  obtain ⟨α, hα⟩ := isAngle_const hp
  have h1 := turn_eq_of_near (g := fun _ => -p) (k := fun x => d x - p) continuous_const
    (hd.sub continuous_const) (fun _ => hp)
    (fun t => by
      have : d t - p - -p = d t := by ring
      rw [this, norm_neg]
      exact hb t) (s := s) (t := t) rfl (by simp only [hst])
  rw [h1, hα.turn_eq (fun _ => hp), sub_self]

/-- The turning of a loop does not change along a homotopy. The compact set `K` of times sees all
values of each loop. -/
theorem turn_eq_of_homotopy {H : ℝ → ℝ → ℂ} (hH : Continuous fun q : ℝ × ℝ => H q.1 q.2)
  (h0 : ∀ u t, H u t ≠ 0) {K : Set ℝ} (hK : IsCompact K)
    (hv : ∀ t, ∃ t' ∈ K, ∀ u, H u t = H u t') {s t : ℝ} (hl : ∀ u, H u s = H u t) (a b : ℝ) : turn
      (H a) s t = turn (H b) s t := by
  have hcts : ∀ u, Continuous (H u) := fun u => hH.comp (Continuous.prodMk_right u)
  have hloc : IsLocallyConstant fun u => turn (H u) s t := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun u₀ => ?_
    by_cases hne : K.Nonempty
    swap
    · refine Filter.Eventually.of_forall fun u => ?_
      obtain ⟨t', ht', -⟩ := hv 0
      exact absurd ⟨t', ht'⟩ hne
    obtain ⟨t₀, ht₀, hmin⟩ := hK.exists_isMinOn hne (hcts u₀).norm.continuousOn
    have hδ : 0 < ‖H u₀ t₀‖ := norm_pos_iff.mpr (h0 _ _)
    have hev : ∀ᶠ u in 𝓝 u₀, ∀ t' ∈ K, ‖H u t' - H u₀ t'‖ < ‖H u₀ t₀‖ := by
      refine hK.eventually_forall_of_forall_eventually fun t' _ => ?_
      have hc : Continuous fun q : ℝ × ℝ => ‖H q.1 q.2 - H u₀ q.2‖ := (hH.sub
        ((hcts u₀).comp continuous_snd)).norm
      have h1 : Tendsto (fun q : ℝ × ℝ => ‖H q.1 q.2 - H u₀ q.2‖) (𝓝 (u₀, t'))
        (𝓝 ‖H u₀ t' - H u₀ t'‖) := hc.tendsto (u₀, t')
      rw [sub_self, norm_zero] at h1
      exact h1.eventually (gt_mem_nhds hδ)
    filter_upwards [hev] with u hu
    refine turn_eq_of_near (hcts u₀) (hcts u) (h0 u₀) (fun y => ?_) (hl u₀) (hl u)
    obtain ⟨t', ht', e⟩ := hv y
    rw [e u, e u₀]
    exact lt_of_lt_of_le (hu t' ht') (hmin ht')
  exact hloc.apply_eq_of_preconnectedSpace a b

/-- Two arcs with the same ends turn equally around `p 0`, when the path `p` runs from `p 0` to a
far point without meeting the arcs. -/
theorem turn_eq_of_path {g k : ℝ → ℂ} (hg : Continuous g) (hk : Continuous k) {a b c d : ℝ}
  (hab : a ≤ b) (hcd : c ≤ d) (hs : g a = k c) (he : g b = k d)
    {p : ℝ → ℂ} (hp : Continuous p) (hg0 : ∀ t, g t ≠ p 0) (hk0 : ∀ t, k t ≠ p 0)
      (hgp : ∀ u, ∀ t ∈ Icc a b, g t ≠ p u) (hkp : ∀ u, ∀ t ∈ Icc c d, k t ≠ p u)
    (hgf : ∀ t ∈ Icc a b, ‖g t‖ < ‖p 1‖) (hkf : ∀ t ∈ Icc c d, ‖k t‖ < ‖p 1‖) :
    turn (fun t => g t - p 0) a b = turn (fun t => k t - p 0) c d := by
  have hc01 : ∀ x : ℝ, max 0 (min x 1) ∈ Icc (0 : ℝ) 1 := fun x => ⟨le_max_left _ _, max_le
    zero_le_one (min_le_right _ _)⟩
  let c₁ : ℝ → ℝ := fun x => a + (b - a) * max 0 (min x 1)
  let c₂ : ℝ → ℝ := fun x => d - (d - c) * max 0 (min (x - 1) 1)
  have hc₁ : Continuous c₁ := by fun_prop
  have hc₂ : Continuous c₂ := by fun_prop
  have hm₁ : ∀ x, c₁ x ∈ Icc a b := fun x => by
    obtain ⟨h1, h2⟩ := hc01 x
    refine ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hab) h1], ?_⟩
    simp only [c₁]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h2)]
  have hm₂ : ∀ x, c₂ x ∈ Icc c d := fun x => by
    obtain ⟨h1, h2⟩ := hc01 (x - 1)
    refine ⟨?_, ?_⟩
    · simp only [c₂]; nlinarith [mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr h2)]
    · simp only [c₂]; nlinarith [mul_nonneg (sub_nonneg.mpr hcd) h1]
  have hc₁0 : c₁ 0 = a := by simp [c₁]
  have hc₁1 : c₁ 1 = b := by simp [c₁]
  have hc₂1 : c₂ 1 = d := by simp [c₂]
  have hc₂2 : c₂ 2 = c := by
    have : (2 : ℝ) - 1 = 1 := by norm_num
    simp [c₂, this]
  let D : ℝ → ℂ := fun x => if x ≤ 1 then g (c₁ x) else k (c₂ x)
  have hD : Continuous D := Continuous.if_le (hg.comp hc₁) (hk.comp hc₂) continuous_id
    continuous_const fun x hx => by
    subst hx
    show g (c₁ 1) = k (c₂ 1)
    rw [hc₁1, hc₂1, he]
  have hDle : ∀ {x : ℝ}, x ≤ 1 → D x = g (c₁ x) := fun h => ite_eq_left h
  have hDge : ∀ {x : ℝ}, 1 ≤ x → D x = k (c₂ x) := fun {x} h => by
    rcases h.eq_or_lt with h | h
    · subst h
      rw [hDle le_rfl, hc₁1, hc₂1, he]
    · exact ite_eq_right (not_le.mpr h)
  have hD02 : D 0 = D 2 := by
    rw [hDle zero_le_one, hDge one_le_two, hc₁0, hc₂2, hs]
  have hDp : ∀ u x, D x ≠ p u := fun u x => by
    rcases le_total x 1 with h | h
    · rw [hDle h]; exact hgp u _ (hm₁ x)
    · rw [hDge h]; exact hkp u _ (hm₂ x)
  have hDf : ∀ x, ‖D x‖ < ‖p 1‖ := fun x => by
    rcases le_total x 1 with h | h
    · rw [hDle h]; exact hgf _ (hm₁ x)
    · rw [hDge h]; exact hkf _ (hm₂ x)
  have hclamp : ∀ x, ∃ x' ∈ Icc (0 : ℝ) 2, ∀ u, D x - p u = D x' - p u := fun x => by
    rcases le_total x 0 with h0 | h0
    · refine ⟨0, ⟨le_rfl, zero_le_two⟩, fun u => ?_⟩
      rw [hDle (h0.trans zero_le_one), hDle zero_le_one, hc₁0]
      have : c₁ x = a := by simp [c₁, min_eq_left (h0.trans zero_le_one), max_eq_left h0]
      rw [this]
    rcases le_total x 2 with h2 | h2
    · exact ⟨x, ⟨h0, h2⟩, fun _ => rfl⟩
    · refine ⟨2, ⟨zero_le_two, le_rfl⟩, fun u => ?_⟩
      rw [hDge (one_le_two.trans h2), hDge one_le_two, hc₂2]
      have h3 : (1 : ℝ) ≤ x - 1 := by linarith
      have : c₂ x = c := by simp [c₂, min_eq_right h3]
      rw [this]
  have h0H : ∀ u x, D x - p u ≠ 0 := fun u x => sub_ne_zero.mpr (hDp u x)
  have hcH : Continuous fun q : ℝ × ℝ => D q.2 - p q.1 := (hD.comp continuous_snd).sub
    (hp.comp continuous_fst)
  have hhom : turn (fun x => D x - p 0) 0 2 = turn (fun x => D x - p 1) 0 2 :=
    turn_eq_of_homotopy (H := fun u x => D x - p u) hcH h0H isCompact_Icc hclamp (s := 0) (t := 2)
      (fun u => by rw [hD02]) 0 1
  rw [turn_eq_zero_of_far hD hDf hD02] at hhom
  have hgc : Continuous fun t => g t - p 0 := hg.sub continuous_const
  have hkc : Continuous fun t => k t - p 0 := hk.sub continuous_const
  have hg0' : ∀ t, g t - p 0 ≠ 0 := fun t => sub_ne_zero.mpr (hg0 t)
  have hk0' : ∀ t, k t - p 0 ≠ 0 := fun t => sub_ne_zero.mpr (hk0 t)
  obtain ⟨L, hL⟩ := exists_isAngle (g := fun x => D x - p 0) (hD.sub continuous_const) (h0H 0)
  obtain ⟨L₁, hL₁⟩ := exists_isAngle (g := fun t => g t - p 0) hgc hg0'
  obtain ⟨L₂, hL₂⟩ := exists_isAngle (g := fun t => k t - p 0) hkc hk0'
  rw [hL.turn_eq (h0H 0)] at hhom
  rw [hL₁.turn_eq hg0', hL₂.turn_eq hk0']
  have hpi : 0 < 2 * Real.pi := by positivity
  have hmult : ∀ {f f' : ℝ → ℂ} {A A' : ℝ → ℝ}, IsAngle f A → IsAngle f' A' → ∀ t t', f t = f' t'
    → f t ≠ 0 → ∃ m : ℤ, A t - A' t' = m * (2 * Real.pi) := by
    intro f f' A A' hA hA' t t' he hne
    have hn : ((‖f t‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hne)
    have h1 : Circle.exp (A t) = Circle.exp (A' t') := by
      apply Circle.ext
      rw [Circle.coe_exp, Circle.coe_exp]
      have h2 := hA.2 t
      have h3 := hA'.2 t'
      rw [← he] at h3
      exact mul_left_cancel₀ hn (h2.symm.trans h3)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
    exact ⟨m, by rw [hm]; ring⟩
  have e1 := eq_of_multiples (g := fun t => L t - L₁ (c₁ t)) hpi zero_le_one (hL.1.sub
    (hL₁.1.comp hc₁)).continuousOn fun t ht =>
    hmult hL hL₁ t (c₁ t) (by rw [hDle ht.2]) (h0H 0 t)
  have e2 := eq_of_multiples (g := fun t => L t - L₂ (c₂ t)) hpi one_le_two (hL.1.sub
    (hL₂.1.comp hc₂)).continuousOn fun t ht =>
    hmult hL hL₂ t (c₂ t) (by rw [hDge ht.1]) (h0H 0 t)
  simp only [hc₁0, hc₁1, hc₂1, hc₂2] at e1 e2
  linarith

end GraphMinor.GM19
