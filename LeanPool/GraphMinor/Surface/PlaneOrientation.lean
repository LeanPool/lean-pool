/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Winding
public import LeanPool.GraphMinor.Surface.Cap
public import LeanPool.GraphMinor.Surface.OpenDisc
public import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# The orientation of the plane

We orient the plane. The direction of the boundary of a closed disc `Δ` is the one that turns
positively around the points inside `Δ`.

By the Schoenflies theorem a parametrization of `bd(Δ)` extends to a homeomorphism `G` of the plane.
If the boundary did not turn around
`G 0`, then it would be null-homotopic off `G 0`, and `G⁻¹` would make the unit circle
null-homotopic off `0`, which it is not
(`wind_ne_zero`).

The heart is `wind_eq_of_nested`. Let `Δ₁ ⊆ Δ₂` be discs and let `a, b, c` be common boundary
points. Take `z` inside `Δ₁`. The arc of
`bd(Δ₁)` from `a` to `b` and the arc of `bd(Δ₂)` from `a` to `b` miss `c`. So they miss a path from
`z` to `c` inside `Δ₁`, followed by a
path from `c` to a far point outside `Δ₂`. Hence the two arcs turn equally around `z`, and adding up
the three pairs of arcs shows that
the two boundaries turn equally around `z`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Metric Topology Filter GraphMinor.GM19

theorem isManifoldPoint_complex (x : ℂ) : IsManifoldPoint x := by
  obtain ⟨e⟩ := exists_homeomorph_ball x one_pos
  have : IsInteriorPoint x := ⟨ball x 1, isOpen_ball, mem_ball_self one_pos, ⟨e⟩⟩
  exact this.isManifoldPoint

/-! ### Cyclic order on the circle -/

/-- The positive cyclic order of three points of the circle: going around from `a` in the positive
direction, we reach `b` before `c`, and both before coming back to `a`. -/
def CircleCyclic (a b c : Circle) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ s < t ∧ t < 2 * Real.pi ∧ b = a * Circle.exp s ∧ c = a * Circle.exp t

/-- Each point of the circle other than `1` has an angle strictly between `0` and `2π`. -/
theorem exists_angle {z : Circle} (hz : z ≠ 1) :
    ∃ s : ℝ, 0 < s ∧ s < 2 * Real.pi ∧ z = Circle.exp s := by
  have harg : Circle.exp (Complex.arg z) = z := Circle.exp_arg z
  have h0 : Complex.arg z ≠ 0 := fun h ↦ hz (by rw [← harg, h, Circle.exp_zero])
  have hlo := Complex.neg_pi_lt_arg (z : ℂ)
  have hhi := Complex.arg_le_pi (z : ℂ)
  have hpi := Real.pi_pos
  rcases lt_or_gt_of_ne h0 with h | h
  · refine ⟨Complex.arg z + 2 * Real.pi, by linarith, by linarith, ?_⟩
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one, harg]
  · exact ⟨Complex.arg z, h, by linarith, harg.symm⟩

/-- Three distinct points of the circle occur in one of the two cyclic orders. -/
theorem circleCyclic_or {a b c : Circle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CircleCyclic a b c ∨ CircleCyclic a c b := by
  obtain ⟨s, hs0, hs1, hs⟩ := exists_angle (z := a⁻¹ * b) (fun h ↦ hab (by
    rw [inv_mul_eq_one] at h
    exact h))
  obtain ⟨t, ht0, ht1, ht⟩ := exists_angle (z := a⁻¹ * c) (fun h ↦ hac (by
    rw [inv_mul_eq_one] at h
    exact h))
  have hb : b = a * Circle.exp s := by rw [← hs]; simp
  have hc : c = a * Circle.exp t := by rw [← ht]; simp
  rcases lt_trichotomy s t with h | h | h
  · exact Or.inl ⟨s, t, hs0, h, ht1, hb, hc⟩
  · exact absurd (by rw [hb, hc, h]) hbc
  · exact Or.inr ⟨t, s, ht0, h, hs1, hc, hb⟩

theorem exp_eq_of_angles {s t : ℝ} (hs : 0 < s) (hs' : s < 2 * Real.pi) (ht : 0 < t)
    (ht' : t < 2 * Real.pi) (h : Circle.exp s = Circle.exp t) : s = t := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h
  have hpi := Real.pi_pos
  have h1 : (m : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
  have h2 : -(2 * Real.pi) < (m : ℝ) * (2 * Real.pi) := by linarith
  have h3 : (m : ℝ) < 1 := by nlinarith
  have h4 : (-1 : ℝ) < m := by nlinarith
  have h5 : m = 0 := by
    have h6 : m < 1 := by exact_mod_cast h3
    have h7 : -1 < m := by exact_mod_cast h4
    omega
  rw [hm, h5]
  simp

/-- Three points of the circle do not lie in both cyclic orders. -/
theorem not_circleCyclic_both {a b c : Circle} (h : CircleCyclic a b c)
    (h' : CircleCyclic a c b) : False := by
  obtain ⟨s, t, hs, hst, ht, hb, hc⟩ := h
  obtain ⟨s', t', hs', hst', ht', hc', hb'⟩ := h'
  have h1 : Circle.exp s = Circle.exp t' := mul_left_cancel (hb.symm.trans hb')
  have h2 : Circle.exp t = Circle.exp s' := mul_left_cancel (hc.symm.trans hc')
  have hpos : 0 < t' := hs'.trans hst'
  have hpos' : 0 < t := hs.trans hst
  have e1 := exp_eq_of_angles hs (hst.trans ht) hpos ht' h1
  have e2 := exp_eq_of_angles hpos' ht hs' (hst'.trans ht') h2
  linarith

theorem circleCyclic_inv {a b c : Circle} (h : CircleCyclic a b c) :
    CircleCyclic a⁻¹ c⁻¹ b⁻¹ := by
  obtain ⟨s, t, hs, hst, ht, rfl, rfl⟩ := h
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi - t, 2 * Real.pi - s, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [Circle.exp_sub, Circle.exp_two_pi]
    simp [mul_comm]
  · rw [Circle.exp_sub, Circle.exp_two_pi]
    simp [mul_comm]

theorem exists_angle_of_circle (a : Circle) : ∃ α : ℝ, a = Circle.exp α :=
  ⟨Complex.arg a, (Circle.exp_arg a).symm⟩

theorem circleCyclic_exp_of_lt {t₁ t₂ t₃ : ℝ} (h12 : t₁ < t₂) (h23 : t₂ < t₃)
    (h31 : t₃ < t₁ + 2 * Real.pi) :
    CircleCyclic (Circle.exp t₁) (Circle.exp t₂) (Circle.exp t₃) := by
  refine ⟨t₂ - t₁, t₃ - t₁, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [← Circle.exp_add, add_sub_cancel]
  · rw [← Circle.exp_add, add_sub_cancel]

/-! ### Winding and positive parametrizations in `ℂ` -/

/-- How far a parametrized closed curve turns around `z`. -/
noncomputable def wind (φ : Circle → ℂ) (z : ℂ) : ℝ :=
  turn (fun t => φ (Circle.exp t) - z) 0 (2 * Real.pi)

theorem exp_add_two_pi' (t : ℝ) : Circle.exp (t + 2 * Real.pi) = Circle.exp t := exp_add_two_pi t

theorem isAngle_exp : IsAngle (fun t => ((Circle.exp t : Circle) : ℂ)) fun t => t := by
  refine ⟨continuous_id, fun t => ?_⟩
  change ((Circle.exp t : Circle) : ℂ) = _
  rw [Circle.norm_coe, Circle.coe_exp]
  simp

/-- A curve with period `P` turns equally over each period. -/
theorem turn_period {g : ℝ → ℂ} (hg : Continuous g) (h0 : ∀ t, g t ≠ 0) {P : ℝ}
    (hP : ∀ t, g (t + P) = g t) (s t : ℝ) :
    turn g s (s + P) = turn g t (t + P) := by
  obtain ⟨L, hL⟩ := exists_isAngle hg h0
  have hc : Continuous fun x => x + P := by fun_prop
  have h1 : IsAngle g fun x => L (x + P) := by
    have := hL.comp hc
    simpa only [hP] using this
  have := h1.diff hL h0 s t
  rw [hL.turn_eq h0, hL.turn_eq h0]
  linarith

theorem circle_exp_ne {x y : ℝ} (h0 : x ≠ y) (h : |x - y| < 2 * Real.pi) :
    Circle.exp x ≠ Circle.exp y := fun he => by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
  have hpi := Real.pi_pos
  have h1 : x - y = m * (2 * Real.pi) := by rw [hm]; ring
  rw [h1, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h
  have h2 : |(m : ℝ)| < 1 := by nlinarith
  have h3 : m = 0 := by
    have : |m| < 1 := by exact_mod_cast h2
    exact Int.abs_lt_one_iff.mp this
  apply h0
  rw [h3] at h1
  simpa [sub_eq_zero] using h1

/-- A parametrization of the boundary of a plane disc extends to a homeomorphism of the plane. -/
theorem exists_plane_extension {Δ : Set ℂ} (hΔ : IsClosedDisc Δ) {φ : Circle → ℂ}
    (hc : Continuous φ) (hi : Function.Injective φ) (hr : range φ = discBd Δ) :
    ∃ G : ℂ ≃ₜ ℂ, (∀ w : Circle, G w = φ w) ∧ G '' closedBall 0 1 = Δ := by
  classical
  let f : Circle → discBd Δ := fun w => ⟨φ w, by rw [← hr]; exact mem_range_self w⟩
  have hfb : Function.Bijective f := ⟨fun a b h => hi (congrArg Subtype.val h), fun x => by
    obtain ⟨w, hw⟩ : x.1 ∈ range φ := by rw [hr]; exact x.2
    exact ⟨w, Subtype.ext hw⟩⟩
  have hfc : Continuous f := hc.subtype_mk _
  let ψ : Circle ≃ₜ discBd Δ := hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hfb)
  have hmem : ∀ w : Circle, (w : ℂ) ∈ sphere (0 : ℂ) 1 := fun w => by simp
  have hm' : ∀ x : sphere (0 : ℂ) 1, x.1 ∈ Submonoid.unitSphere ℂ := fun x => x.2
  let ρ : Circle ≃ₜ sphere (0 : ℂ) 1 :=
    { toFun := fun w => ⟨w, hmem w⟩
      invFun := fun x => ⟨x.1, hm' x⟩
      left_inv := fun w => rfl
      right_inv := fun x => rfl
      continuous_toFun := (continuous_induced_dom).subtype_mk _
      continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val }
  obtain ⟨h, k, m, hh⟩ := exists_bdMatch (ρ.symm.trans ψ)
  obtain ⟨Ψ, hΨ, hin⟩ := exists_plane_homeomorph ⟨ρ⟩ ⟨ψ⟩ m
  refine ⟨Ψ, fun w => ?_, ?_⟩
  · rw [hΨ (hmem w)]
    exact hh (ρ w)
  · rw [eq_closedInner_of_discBd ⟨ρ⟩ isClosedDisc_closedBall.1 isClosedDisc_closedBall.2, hin]
    exact (eq_closedInner_of_discBd ⟨ψ⟩ hΔ rfl).symm

/-- The boundary of a closed disc turns around the centre. -/
theorem wind_ne_zero (G : ℂ ≃ₜ ℂ) : wind (fun w : Circle => G w) (G 0) ≠ 0 := by
  intro hw
  have hpi : 0 < 2 * Real.pi := by positivity
  let g : ℝ → ℂ := fun t => G (Circle.exp t) - G 0
  have hcoe : Continuous fun t : ℝ => ((Circle.exp t : Circle) : ℂ) :=
    continuous_induced_dom.comp Circle.exp.continuous
  have hg : Continuous g := (G.continuous.comp hcoe).sub continuous_const
  have h0 : ∀ t, g t ≠ 0 := fun t => sub_ne_zero.mpr fun h => by
    have := G.injective h
    have h2 : ‖((Circle.exp t : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    rw [this, norm_zero] at h2
    exact zero_ne_one h2
  have hP : ∀ t, g (t + 2 * Real.pi) = g t := fun t => by simp only [g, exp_add_two_pi]
  obtain ⟨L, hL⟩ := exists_isAngle hg h0
  have hw' : L (2 * Real.pi) = L 0 := by
    have : turn g 0 (2 * Real.pi) = 0 := hw
    rw [hL.turn_eq h0] at this
    linarith
  have hLP : ∀ t, L (t + 2 * Real.pi) = L t := fun t => by
    have hc : Continuous fun x : ℝ => x + 2 * Real.pi := by fun_prop
    have h1 : IsAngle g fun x => L (x + 2 * Real.pi) := by
      have := hL.comp hc
      simpa only [hP] using this
    have := h1.diff hL h0 0 t
    rw [zero_add, hw'] at this
    linarith
  let cl : ℝ → ℝ := fun u => max 0 (min u 1)
  have hcl : Continuous cl := by fun_prop
  let X : ℝ → ℝ → ℂ := fun u t =>
    Complex.exp (((1 - cl u : ℝ) : ℂ) * (((Real.log ‖g t‖ : ℝ) : ℂ) + (L t : ℂ) * Complex.I))
  let H : ℝ → ℝ → ℂ := fun u t => G.symm (G 0 + X u t)
  have hlog : Continuous fun t => Real.log ‖g t‖ := hg.norm.log fun t => norm_ne_zero_iff.mpr (h0 t)
  have hX : Continuous fun q : ℝ × ℝ => X q.1 q.2 := by
    have h1 : Continuous fun q : ℝ × ℝ => Real.log ‖g q.2‖ := hlog.comp continuous_snd
    have h2 : Continuous fun q : ℝ × ℝ => L q.2 := hL.1.comp continuous_snd
    have h3 : Continuous fun q : ℝ × ℝ => cl q.1 := hcl.comp continuous_fst
    refine Complex.continuous_exp.comp ?_
    exact (Complex.continuous_ofReal.comp (continuous_const.sub h3)).mul
      ((Complex.continuous_ofReal.comp h1).add ((Complex.continuous_ofReal.comp h2).mul
        continuous_const))
  have hH : Continuous fun q : ℝ × ℝ => H q.1 q.2 := G.symm.continuous.comp
    (continuous_const.add hX)
  have hne : ∀ u t, H u t ≠ 0 := fun u t h => by
    have h1 := (G.symm_apply_eq).mp h
    exact Complex.exp_ne_zero _ (add_eq_left.mp h1)
  have hper : ∀ u, Function.Periodic (H u) (2 * Real.pi) := fun u t => by
    simp only [H, X, hLP, hP]
  have hv : ∀ t, ∃ t' ∈ Icc 0 (2 * Real.pi), ∀ u, H u t = H u t' := fun t => by
    have ho := toIcoMod_mem_Ico hpi 0 t
    rw [zero_add] at ho
    refine ⟨toIcoMod hpi 0 t, Ico_subset_Icc_self ho, fun u => ?_⟩
    rw [← self_sub_toIcoDiv_zsmul]
    exact ((hper u).sub_zsmul_eq _).symm
  have hhom := turn_eq_of_homotopy hH hne isCompact_Icc hv (s := 0) (t := 2 * Real.pi) (fun u => by
    have := hper u 0
    rw [zero_add] at this
    exact this.symm) 0 1
  have hH0 : H 0 = fun t => ((Circle.exp t : Circle) : ℂ) := by
    funext t
    have hc0 : cl 0 = 0 := by simp [cl]
    have hn : ((‖g t‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (h0 t))
    have hX0 : X 0 t = g t := by
      simp only [X, hc0, sub_zero, Complex.ofReal_one, one_mul]
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (h0 t))]
      exact (hL.2 t).symm
    change G.symm (G 0 + X 0 t) = _
    rw [hX0]
    simp only [g, add_sub_cancel, Homeomorph.symm_apply_apply]
  have hH1 : H 1 = fun _ => G.symm (G 0 + 1) := by
    funext t
    have hc1 : cl 1 = 1 := by simp [cl]
    change G.symm (G 0 + X 1 t) = _
    simp only [X, hc1, sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [hH0, hH1, isAngle_exp.turn_eq (fun t => Circle.coe_ne_zero _)] at hhom
  have hc : G.symm (G 0 + 1) ≠ 0 := fun h => by
    have h1 := (G.symm_apply_eq).mp h
    exact one_ne_zero (add_eq_left.mp h1)
  obtain ⟨α, hα⟩ := isAngle_const hc
  rw [hα.turn_eq (fun _ => hc)] at hhom
  simp only [sub_self, sub_zero] at hhom
  exact hpi.ne' hhom

/-- Going around backwards turns the other way. -/
theorem wind_inv {φ : Circle → ℂ} (hc : Continuous φ) {z : ℂ} (h0 : ∀ w, φ w ≠ z) :
    wind (fun w => φ w⁻¹) z = - wind φ z := by
  have hcoe : Continuous fun t : ℝ => Circle.exp t := Circle.exp.continuous
  let g : ℝ → ℂ := fun t => φ (Circle.exp t) - z
  have hg : Continuous g := (hc.comp hcoe).sub continuous_const
  have hg0 : ∀ t, g t ≠ 0 := fun t => sub_ne_zero.mpr (h0 _)
  have h1 : wind (fun w => φ w⁻¹) z = turn (fun t => g (-t)) 0 (2 * Real.pi) := by
    simp only [wind, g, Circle.exp_neg]
  rw [h1, turn_comp hg hg0 continuous_neg, wind]
  have hP : ∀ t, g (t + 2 * Real.pi) = g t := fun t => by simp only [g, exp_add_two_pi]
  have h2 := turn_period hg hg0 hP (-(2 * Real.pi)) 0
  have h3 := turn_add hg hg0 (-(2 * Real.pi)) 0 (-(2 * Real.pi))
  rw [turn_self hg hg0] at h3
  simp only [neg_zero]
  have h4 : -(2 * Real.pi) + 2 * Real.pi = 0 := by ring
  rw [h4, zero_add] at h2
  change turn g 0 (-(2 * Real.pi)) = - turn g 0 (2 * Real.pi)
  linarith

theorem exists_mem_period (t : ℝ) :
    ∃ t' ∈ Icc 0 (2 * Real.pi), ∃ n : ℤ, t' = t - n • (2 * Real.pi) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have ho := toIcoMod_mem_Ico hpi 0 t
  rw [zero_add] at ho
  exact ⟨toIcoMod hpi 0 t, Ico_subset_Icc_self ho, _, (self_sub_toIcoDiv_zsmul hpi 0 t).symm⟩

/-- The boundary turns equally around any two points inside. -/
theorem wind_eq_of_ball (G : ℂ ≃ₜ ℂ) {φ : Circle → ℂ} (hc : Continuous φ)
    (hG : ∀ w : Circle, G w = φ w) {a b : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hb : b ∈ ball (0 : ℂ) 1) :
    wind φ (G a) = wind φ (G b) := by
  let cl : ℝ → ℝ := fun u => max 0 (min u 1)
  have hcl : Continuous cl := by fun_prop
  have hcl' : ∀ u, cl u ∈ Icc (0 : ℝ) 1 :=
    fun u => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  let l : ℝ → ℂ := fun u => a + ((cl u : ℝ) : ℂ) * (b - a)
  have hl : Continuous l :=
    continuous_const.add ((Complex.continuous_ofReal.comp hcl).mul continuous_const)
  have hlin : ∀ u, l u ∈ ball (0 : ℂ) 1 := fun u => by
    have h := (convex_ball (0 : ℂ) 1).add_smul_sub_mem ha hb (hcl' u)
    rwa [Complex.real_smul] at h
  have hcoe : Continuous fun t : ℝ => Circle.exp t := Circle.exp.continuous
  let H : ℝ → ℝ → ℂ := fun u t => φ (Circle.exp t) - G (l u)
  have hH : Continuous fun q : ℝ × ℝ => H q.1 q.2 :=
    (hc.comp (hcoe.comp continuous_snd)).sub (G.continuous.comp (hl.comp continuous_fst))
  have hne : ∀ u t, H u t ≠ 0 := fun u t h => by
    have h1 := sub_eq_zero.mp h
    rw [← hG] at h1
    have h2 := G.injective h1
    have h3 := hlin u
    rw [← h2, mem_ball_zero_iff, Circle.norm_coe] at h3
    exact lt_irrefl _ h3
  have hper : ∀ u, Function.Periodic (H u) (2 * Real.pi) := fun u t => by
    simp only [H, exp_add_two_pi]
  have hv : ∀ t, ∃ t' ∈ Icc 0 (2 * Real.pi), ∀ u, H u t = H u t' := fun t => by
    obtain ⟨t', ht', n, rfl⟩ := exists_mem_period t
    exact ⟨_, ht', fun u => ((hper u).sub_zsmul_eq n).symm⟩
  have hhom := turn_eq_of_homotopy hH hne isCompact_Icc hv (s := 0) (t := 2 * Real.pi) (fun u => by
    have := hper u 0
    rw [zero_add] at this
    exact this.symm) 0 1
  have h0 : l 0 = a := by simp [l, cl]
  have h1 : l 1 = b := by simp [l, cl]
  simp only [H, h0, h1] at hhom
  exact hhom

/-- Two arcs in `Δ₂`, off the inside of `Δ₁`, with the same ends and missing the common boundary
point `x`, turn equally around the centre of `Δ₁`. -/
theorem turn_eq_of_nested {Δ₂ : Set ℂ} (hΔ₂ : IsClosedDisc Δ₂) (G₁ G₂ : ℂ ≃ₜ ℂ)
    (hG₂ : G₂ '' closedBall 0 1 = Δ₂) {x₁ x₂ : Circle} (hx : G₁ x₁ = G₂ x₂)
    {g k : ℝ → ℂ} (hg : Continuous g) (hk : Continuous k) {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hs : g a = k c) (he : g b = k d)
    (hgb : ∀ t, g t ∉ G₁ '' ball 0 1) (hkb : ∀ t, k t ∉ G₁ '' ball 0 1)
    (hg₂ : ∀ t, g t ∈ Δ₂) (hk₂ : ∀ t, k t ∈ Δ₂)
    (hgx : ∀ t ∈ Icc a b, g t ≠ G₁ x₁) (hkx : ∀ t ∈ Icc c d, k t ≠ G₁ x₁) :
    turn (fun t => g t - G₁ 0) a b = turn (fun t => k t - G₁ 0) c d := by
  obtain ⟨M, hM⟩ := hΔ₂.isCompact.isBounded.exists_norm_le
  obtain ⟨R, hR⟩ :=
    ((isCompact_closedBall (0 : ℂ) M).image G₂.symm.continuous).isBounded.exists_norm_le
  have hx₁ : ‖(x₁ : ℂ)‖ = 1 := Circle.norm_coe _
  have hx₂ : ‖(x₂ : ℂ)‖ = 1 := Circle.norm_coe _
  let R' : ℝ := max R 1 + 1
  have hR1 : 1 < R' := by have := le_max_right R 1; simp only [R']; linarith
  let cl : ℝ → ℝ := fun u => max 0 (min u 1)
  have hcl : Continuous cl := by fun_prop
  have hcl' : ∀ u, cl u ∈ Icc (0 : ℝ) 1 :=
    fun u => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hcl0 : cl 0 = 0 := by simp [cl]
  have hcl1 : cl 1 = 1 := by simp [cl]
  let p₁ : ℝ → ℂ := fun u => G₁ (((cl (2 * u) : ℝ) : ℂ) * x₁)
  let p₂ : ℝ → ℂ := fun u => G₂ (((1 + cl (2 * u - 1) * (R' - 1) : ℝ) : ℂ) * x₂)
  have hp₁ : Continuous p₁ := by
    refine G₁.continuous.comp
      (Continuous.mul (Complex.continuous_ofReal.comp (hcl.comp (by fun_prop))) continuous_const)
  have hp₂ : Continuous p₂ := by
    refine G₂.continuous.comp (Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const)
    exact continuous_const.add ((hcl.comp (by fun_prop)).mul continuous_const)
  let p : ℝ → ℂ := fun u => if u ≤ 1 / 2 then p₁ u else p₂ u
  have hp : Continuous p := Continuous.if_le hp₁ hp₂ continuous_id continuous_const fun u hu => by
    have h1 : u = 1 / 2 := hu
    subst h1
    simp only [p₁, p₂]
    have e1 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
    have e2 : (1 : ℝ) - 1 = 0 := by norm_num
    rw [e1, e2, hcl0, hcl1, zero_mul, add_zero]
    simpa using hx
  have hp0 : p 0 = G₁ 0 := by
    simp only [p, p₁]
    rw [ite_eq_left (by norm_num), mul_zero, hcl0]
    simp
  have hp1 : p 1 = G₂ ((R' : ℂ) * x₂) := by
    simp only [p, p₂]
    rw [ite_eq_right (by norm_num)]
    have e1 : (2 : ℝ) * 1 - 1 = 1 := by norm_num
    rw [e1, hcl1]
    congr 3
    ring
  have hfar : M < ‖p 1‖ := by
    by_contra hn
    have h1 : p 1 ∈ closedBall (0 : ℂ) M := mem_closedBall_zero_iff.mpr (not_lt.mp hn)
    have h2 := hR _ (mem_image_of_mem G₂.symm h1)
    rw [hp1, Homeomorph.symm_apply_apply, norm_mul, Complex.norm_real, hx₂, mul_one,
      Real.norm_of_nonneg (by linarith)] at h2
    have := le_max_left R 1
    simp only [R'] at h2
    linarith
  have havoid : ∀ {y : ℂ}, y ∉ G₁ '' ball 0 1 → y ∈ Δ₂ → y ≠ G₁ x₁ → ∀ u, y ≠ p u := by
    intro y hy1 hy2 hy3 u he
    by_cases hu : u ≤ 1 / 2
    · have e : p u = G₁ (((cl (2 * u) : ℝ) : ℂ) * x₁) := ite_eq_left hu
      rw [e] at he
      rcases (hcl' (2 * u)).2.lt_or_eq with h | h
      · refine hy1 ⟨_, ?_, he.symm⟩
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, hx₁, mul_one,
          Real.norm_of_nonneg (hcl' _).1]
        exact h
      · rw [h] at he
        exact hy3 (by simpa using he)
    · have e : p u = G₂ (((1 + cl (2 * u - 1) * (R' - 1) : ℝ) : ℂ) * x₂) := ite_eq_right hu
      rw [e] at he
      have hc0 := (hcl' (2 * u - 1)).1
      rcases hc0.eq_or_lt with h | h
      · rw [← h, zero_mul, add_zero] at he
        apply hy3
        rw [he, hx]
        simp
      · rw [← hG₂] at hy2
        obtain ⟨w, hw, hwe⟩ := hy2
        have := G₂.injective (hwe.trans he)
        rw [this, mem_closedBall_zero_iff, norm_mul, Complex.norm_real, hx₂, mul_one,
          Real.norm_of_nonneg (by nlinarith)] at hw
        nlinarith
  have hne0 : ∀ {y : ℂ}, y ∉ G₁ '' ball 0 1 → y ≠ G₁ 0 := fun hy he => hy ⟨0, by simp, he.symm⟩
  have := turn_eq_of_path hg hk hab hcd hs he hp (fun t => by rw [hp0]; exact hne0 (hgb t))
    (fun t => by rw [hp0]; exact hne0 (hkb t))
    (fun u t ht => havoid (hgb t) (hg₂ t) (hgx t ht) u)
    (fun u t ht => havoid (hkb t) (hk₂ t) (hkx t ht) u)
    (fun t _ => lt_of_le_of_lt (hM _ (hg₂ t)) hfar)
    (fun t _ => lt_of_le_of_lt (hM _ (hk₂ t)) hfar)
  rwa [hp0] at this

theorem image_sphere_of_extension (G : ℂ ≃ₜ ℂ) {φ : Circle → ℂ} (hG : ∀ w : Circle, G w = φ w) :
    G '' sphere 0 1 = range φ := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hm : z ∈ Submonoid.unitSphere ℂ := hz
    exact ⟨⟨z, hm⟩, (hG _).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, by simp, hG w⟩

/-- The inside of a plane disc is the image of the open ball. -/
theorem discInt_eq_of_extension {Δ : Set ℂ} (G : ℂ ≃ₜ ℂ) {φ : Circle → ℂ}
    (hG : ∀ w : Circle, G w = φ w) (hr : range φ = discBd Δ) (hΔ : G '' closedBall 0 1 = Δ) :
    discInt Δ = G '' ball 0 1 := by
  have hb : discBd Δ = G '' sphere 0 1 := by rw [← hr, image_sphere_of_extension G hG]
  rw [discInt, hb, ← hΔ, ← image_sdiff G.injective]
  congr 1
  ext z
  simp only [Set.mem_sdiff, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm, mem_ball_zero_iff]
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨h.le, h.ne⟩⟩

/-- The turning of a closed curve does not depend on where it starts. -/
theorem wind_eq_turn_rotate {φ : Circle → ℂ} (hc : Continuous φ) {z : ℂ} (h0 : ∀ w, φ w ≠ z)
    (u : Circle) : wind φ z = turn (fun t => φ (u * Circle.exp t) - z) 0 (2 * Real.pi) := by
  obtain ⟨α, rfl⟩ := exists_angle_of_circle u
  have hcoe : Continuous fun t : ℝ => Circle.exp t := Circle.exp.continuous
  let g : ℝ → ℂ := fun t => φ (Circle.exp t) - z
  have hg : Continuous g := (hc.comp hcoe).sub continuous_const
  have hg0 : ∀ t, g t ≠ 0 := fun t => sub_ne_zero.mpr (h0 _)
  have h1 : (fun t => φ (Circle.exp α * Circle.exp t) - z) = fun t => g (α + t) := by
    funext t
    simp only [g, Circle.exp_add]
  rw [h1, turn_comp hg hg0 (by fun_prop), wind, add_zero]
  have hP : ∀ t, g (t + 2 * Real.pi) = g t := fun t => by simp only [g, exp_add_two_pi]
  have := turn_period hg hg0 hP 0 α
  rwa [zero_add] at this

/-- **Nested discs.** Two nested plane discs with three common boundary points in the same cyclic
order have boundaries that turn equally around the centre of the smaller disc. -/
theorem wind_eq_of_nested {Δ₁ Δ₂ : Set ℂ} (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
    (hsub : Δ₁ ⊆ Δ₂) {φ₁ φ₂ : Circle → ℂ} (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hr₁ : range φ₁ = discBd Δ₁) (hr₂ : range φ₂ = discBd Δ₂) (G₁ G₂ : ℂ ≃ₜ ℂ)
    (hG₁ : ∀ w : Circle, G₁ w = φ₁ w) (hG₂ : ∀ w : Circle, G₂ w = φ₂ w)
    (hD₁ : G₁ '' closedBall 0 1 = Δ₁) (hD₂ : G₂ '' closedBall 0 1 = Δ₂)
    {u₁ u₂ : Circle} {s₁ t₁ s₂ t₂ : ℝ} (hs₁ : 0 < s₁) (hst₁ : s₁ < t₁) (ht₁ : t₁ < 2 * Real.pi)
    (hs₂ : 0 < s₂) (hst₂ : s₂ < t₂) (ht₂ : t₂ < 2 * Real.pi)
    (ha : φ₁ u₁ = φ₂ u₂) (hb : φ₁ (u₁ * Circle.exp s₁) = φ₂ (u₂ * Circle.exp s₂))
    (hc : φ₁ (u₁ * Circle.exp t₁) = φ₂ (u₂ * Circle.exp t₂)) :
    wind φ₁ (G₁ 0) = wind φ₂ (G₁ 0) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hcoe : Continuous fun t : ℝ => Circle.exp t := Circle.exp.continuous
  have hint₁ := discInt_eq_of_extension G₁ hG₁ hr₁ hD₁
  have hint₂ := discInt_eq_of_extension G₂ hG₂ hr₂ hD₂
  have hmono : discInt Δ₁ ⊆ discInt Δ₂ := discInt_mono isManifoldPoint_complex hΔ₁ hsub
  have hinj₁ : Function.Injective φ₁ := fun a b h => by
    rw [← hG₁, ← hG₁] at h
    exact Circle.ext (G₁.injective h)
  have hinj₂ : Function.Injective φ₂ := fun a b h => by
    rw [← hG₂, ← hG₂] at h
    exact Circle.ext (G₂.injective h)
  have hoff₁ : ∀ w, φ₁ w ∉ G₁ '' ball 0 1 := fun w h => by
    rw [← hint₁] at h
    exact h.2 (by rw [← hr₁]; exact mem_range_self w)
  have hoff₂ : ∀ w, φ₂ w ∉ G₁ '' ball 0 1 := fun w h => by
    rw [← hint₁] at h
    exact (hmono h).2 (by rw [← hr₂]; exact mem_range_self w)
  have hin₁ : ∀ w, φ₁ w ∈ Δ₂ :=
    fun w => hsub (discBd_subset _ (by rw [← hr₁]; exact mem_range_self w))
  have hin₂ : ∀ w, φ₂ w ∈ Δ₂ := fun w => discBd_subset _ (by rw [← hr₂]; exact mem_range_self w)
  have hz₁ : ∀ w, φ₁ w ≠ G₁ 0 := fun w h => hoff₁ w ⟨0, by simp, h.symm⟩
  have hz₂ : ∀ w, φ₂ w ≠ G₁ 0 := fun w h => hoff₂ w ⟨0, by simp, h.symm⟩
  let γ₁ : ℝ → ℂ := fun t => φ₁ (u₁ * Circle.exp t)
  let γ₂ : ℝ → ℂ := fun t => φ₂ (u₂ * Circle.exp t)
  have hγ₁ : Continuous γ₁ := hc₁.comp (continuous_const.mul hcoe)
  have hγ₂ : Continuous γ₂ := hc₂.comp (continuous_const.mul hcoe)
  have hγ₁c : Continuous fun t => γ₁ t - G₁ 0 := hγ₁.sub continuous_const
  have hγ₂c : Continuous fun t => γ₂ t - G₁ 0 := hγ₂.sub continuous_const
  have hγ₁0 : ∀ t, γ₁ t - G₁ 0 ≠ 0 := fun t => sub_ne_zero.mpr (hz₁ _)
  have hγ₂0 : ∀ t, γ₂ t - G₁ 0 ≠ 0 := fun t => sub_ne_zero.mpr (hz₂ _)
  have e0₁ : γ₁ 0 = φ₁ u₁ := by simp [γ₁]
  have e0₂ : γ₂ 0 = φ₂ u₂ := by simp [γ₂]
  have e2₁ : γ₁ (2 * Real.pi) = φ₁ u₁ := by
    have := exp_add_two_pi 0
    rw [zero_add] at this
    simp [γ₁, this]
  have e2₂ : γ₂ (2 * Real.pi) = φ₂ u₂ := by
    have := exp_add_two_pi 0
    rw [zero_add] at this
    simp [γ₂, this]
  have step : ∀ {x₁ x₂ : Circle} {a b c d : ℝ}, φ₁ x₁ = φ₂ x₂ → a ≤ b → c ≤ d →
      γ₁ a = γ₂ c → γ₁ b = γ₂ d → (∀ t ∈ Icc a b, γ₁ t ≠ φ₁ x₁) →
      (∀ t ∈ Icc c d, γ₂ t ≠ φ₁ x₁) →
      turn (fun t => γ₁ t - G₁ 0) a b = turn (fun t => γ₂ t - G₁ 0) c d := by
    intro x₁ x₂ a b c d hx hab hcd hs he hg hk
    refine turn_eq_of_nested hΔ₂ G₁ G₂ hD₂ (x₁ := x₁) (x₂ := x₂) (by rw [hG₁, hG₂, hx]) hγ₁ hγ₂
      hab hcd hs he (fun t => hoff₁ _) (fun t => hoff₂ _) (fun t => hin₁ _) (fun t => hin₂ _)
      (fun t ht => ?_) (fun t ht => ?_)
    · rw [hG₁]; exact hg t ht
    · rw [hG₁]; exact hk t ht
  have hne₁ : ∀ {x y : ℝ}, x ≠ y → |x - y| < 2 * Real.pi → γ₁ x ≠ γ₁ y := fun hxy h he =>
    circle_exp_ne hxy h (mul_left_cancel (hinj₁ he))
  have hne₂ : ∀ {x y : ℝ}, x ≠ y → |x - y| < 2 * Real.pi → γ₂ x ≠ γ₂ y := fun hxy h he =>
    circle_exp_ne hxy h (mul_left_cancel (hinj₂ he))
  have hb' : γ₁ s₁ = γ₂ s₂ := hb
  have hc' : γ₁ t₁ = γ₂ t₂ := hc
  have a1 : turn (fun t => γ₁ t - G₁ 0) 0 s₁ = turn (fun t => γ₂ t - G₁ 0) 0 s₂ := by
    refine step (x₁ := u₁ * Circle.exp t₁) (x₂ := u₂ * Circle.exp t₂) hc hs₁.le hs₂.le
      (by rw [e0₁, e0₂, ha]) hb' (fun t ht => ?_) (fun t ht => ?_)
    · refine hne₁ (x := t) (y := t₁) (fun he => by linarith [ht.2]) ?_
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    · rw [hc]
      refine hne₂ (x := t) (y := t₂) (fun he => by linarith [ht.2]) ?_
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have a2 : turn (fun t => γ₁ t - G₁ 0) s₁ t₁ = turn (fun t => γ₂ t - G₁ 0) s₂ t₂ := by
    refine step (x₁ := u₁) (x₂ := u₂) ha hst₁.le hst₂.le hb' hc' (fun t ht => ?_) (fun t ht => ?_)
    · rw [← e0₁]
      refine hne₁ (x := t) (y := 0) (fun he => by linarith [ht.1]) ?_
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    · rw [ha, ← e0₂]
      refine hne₂ (x := t) (y := 0) (fun he => by linarith [ht.1]) ?_
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have a3 : turn (fun t => γ₁ t - G₁ 0) t₁ (2 * Real.pi) =
      turn (fun t => γ₂ t - G₁ 0) t₂ (2 * Real.pi) := by
    refine step (x₁ := u₁ * Circle.exp s₁) (x₂ := u₂ * Circle.exp s₂) hb ht₁.le ht₂.le hc'
      (by rw [e2₁, e2₂, ha]) (fun t ht => ?_) (fun t ht => ?_)
    · refine hne₁ (x := t) (y := s₁) (fun he => by linarith [ht.1]) ?_
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    · rw [hb]
      refine hne₂ (x := t) (y := s₂) (fun he => by linarith [ht.1]) ?_
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  rw [wind_eq_turn_rotate hc₁ hz₁ u₁, wind_eq_turn_rotate hc₂ hz₂ u₂]
  change turn (fun t => γ₁ t - G₁ 0) 0 (2 * Real.pi) = turn (fun t => γ₂ t - G₁ 0) 0 (2 * Real.pi)
  rw [← turn_add hγ₁c hγ₁0 0 t₁, ← turn_add hγ₁c hγ₁0 0 s₁ t₁, ← turn_add hγ₂c hγ₂0 0 t₂,
    ← turn_add hγ₂c hγ₂0 0 s₂ t₂, a1, a2, a3]

/-- A parametrization of `bd(Δ)` that turns positively around the points inside `Δ`. -/
def IsPosParam (Δ : Set ℂ) (φ : Circle → ℂ) : Prop :=
  Continuous φ ∧ Function.Injective φ ∧ range φ = discBd Δ ∧ ∀ z ∈ discInt Δ, 0 < wind φ z

/-- Any boundary parametrization of a closed disc in `ℂ` is either positive or its circle-inverse
is positive. -/
theorem isPosParam_or_inv {Δ : Set ℂ} (hΔ : IsClosedDisc Δ) {φ : Circle → ℂ}
    (hc : Continuous φ) (hi : Function.Injective φ) (hr : range φ = discBd Δ) :
    IsPosParam Δ φ ∨ IsPosParam Δ (fun w => φ w⁻¹) := by
  obtain ⟨G, hG, hD⟩ := exists_plane_extension hΔ hc hi hr
  have hint := discInt_eq_of_extension G hG hr hD
  have hne : wind φ (G 0) ≠ 0 := by
    have := wind_ne_zero G
    have he : (fun w : Circle => G w) = φ := funext hG
    rwa [he] at this
  have hsame : ∀ z ∈ discInt Δ, wind φ z = wind φ (G 0) := by
    intro z hz
    rw [hint] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact wind_eq_of_ball G hc hG ha (by simp)
  have hoff : ∀ {z}, z ∈ discInt Δ → ∀ w, φ w ≠ z :=
    fun hz w he => hz.2 (by rw [← he, ← hr]; exact mem_range_self w)
  rcases hne.lt_or_gt with hn | hp
  · right
    refine ⟨hc.comp continuous_inv, fun a b he => inv_injective (hi he), ?_, fun z hz => ?_⟩
    · rw [← hr]
      ext y
      exact ⟨fun ⟨w, hw⟩ => ⟨_, hw⟩, fun ⟨w, hw⟩ => ⟨w⁻¹, by simpa using hw⟩⟩
    · rw [wind_inv hc (hoff hz), hsame z hz]
      linarith
  · exact Or.inl ⟨hc, hi, hr, fun z hz => by rw [hsame z hz]; exact hp⟩

theorem exists_posParam {Δ : Set ℂ} (hΔ : IsClosedDisc Δ) : ∃ φ, IsPosParam Δ φ := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hsub : ∀ w : Circle, (w : ℂ) ∈ closedBall (0 : ℂ) 1 := fun w => by simp
  let φ : Circle → ℂ := fun w => g w
  have hφc : Continuous φ := c.gc.comp_continuous continuous_induced_dom hsub
  have hφi : Function.Injective φ := fun a b he => by
    have := congrArg h he
    rw [c.hg (hsub a), c.hg (hsub b)] at this
    exact Circle.ext this
  have hφr : range φ = discBd Δ := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      have : (w : ℂ) ∈ h '' discBd Δ := by rw [c.bd]; simp
      obtain ⟨x, hx, hxe⟩ := this
      have hxD := discBd_subset _ hx
      have := c.gh hxD
      change g w ∈ _
      rw [← hxe, this]
      exact hx
    · intro hy
      have hyD := discBd_subset _ hy
      have hm : h y ∈ sphere (0 : ℂ) 1 := by rw [← c.bd]; exact mem_image_of_mem h hy
      have hm' : h y ∈ Submonoid.unitSphere ℂ := hm
      exact ⟨⟨h y, hm'⟩, c.gh hyD⟩
  rcases isPosParam_or_inv hΔ hφc hφi hφr with hPos | hPos
  · exact ⟨φ, hPos⟩
  · exact ⟨fun w => φ w⁻¹, hPos⟩

/-- A positive boundary parametrization and its circle-inverse cannot both be positive. -/
theorem not_isPosParam_inv {Δ : Set ℂ} (hΔ : IsClosedDisc Δ) {φ : Circle → ℂ}
    (hφ : IsPosParam Δ φ) : ¬ IsPosParam Δ (fun w => φ w⁻¹) := by
  intro hinv
  obtain ⟨G, hG, hD⟩ := exists_plane_extension hΔ hφ.1 hφ.2.1 hφ.2.2.1
  have hint := discInt_eq_of_extension G hG hφ.2.2.1 hD
  have hz0 : G 0 ∈ discInt Δ := by
    rw [hint]
    exact mem_image_of_mem G (mem_ball_self zero_lt_one)
  have h1 := hφ.2.2.2 (G 0) hz0
  have h2 := hinv.2.2.2 (G 0) hz0
  have hoff : ∀ u, φ u ≠ G 0 := fun u he =>
    hz0.2 (by rw [← he, ← hφ.2.2.1]; exact mem_range_self u)
  rw [wind_inv hφ.1 hoff] at h2
  linarith

/-- The cyclic order on common boundary points of nested plane discs is the same. -/
theorem order_of_nested {Δ₁ Δ₂ : Set ℂ} (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
    (hsub : Δ₁ ⊆ Δ₂) {φ₁ φ₂ : Circle → ℂ} (h₁ : IsPosParam Δ₁ φ₁) (h₂ : IsPosParam Δ₂ φ₂)
    {u v w u' v' w' : Circle} (hcy : CircleCyclic u v w)
    (ha : φ₁ u = φ₂ u') (hb : φ₁ v = φ₂ v') (hc : φ₁ w = φ₂ w') : CircleCyclic u' v' w' := by
  obtain ⟨s, t, hs, hst, ht, rfl, rfl⟩ := id hcy
  have hpi := Real.pi_pos
  have hne : ∀ {x y : ℝ}, x ≠ y → |x - y| < 2 * Real.pi →
      ∀ a : Circle, a * Circle.exp x ≠ a * Circle.exp y := fun hxy h a he =>
    circle_exp_ne hxy h (mul_left_cancel he)
  have hbne : u ≠ u * Circle.exp s := fun he => by
    have := hne (x := s) (y := 0) hs.ne' (by rw [sub_zero, abs_of_pos hs]; linarith) u
    rw [Circle.exp_zero, mul_one] at this
    exact this he.symm
  have hcne : u ≠ u * Circle.exp t := fun he => by
    have := hne (x := t) (y := 0) (by linarith : (0 : ℝ) < t).ne'
      (by rw [sub_zero, abs_of_pos (by linarith)]; linarith) u
    rw [Circle.exp_zero, mul_one] at this
    exact this he.symm
  have hbc : u * Circle.exp s ≠ u * Circle.exp t :=
    hne hst.ne (by rw [abs_lt]; constructor <;> linarith) u
  have hab' : u' ≠ v' := fun he => hbne (h₁.2.1 (by rw [ha, hb, he]))
  have hac' : u' ≠ w' := fun he => hcne (h₁.2.1 (by rw [ha, hc, he]))
  have hbc' : v' ≠ w' := fun he => hbc (h₁.2.1 (by rw [hb, hc, he]))
  rcases circleCyclic_or hab' hac' hbc' with h | h
  · exact h
  exfalso
  obtain ⟨hc₁, hi₁, hr₁, hp₁⟩ := h₁
  obtain ⟨hc₂, hi₂, hr₂, hp₂⟩ := h₂
  let φ₃ : Circle → ℂ := fun x => φ₂ x⁻¹
  have hc₃ : Continuous φ₃ := hc₂.comp continuous_inv
  have hi₃ : Function.Injective φ₃ := fun a b he => inv_injective (hi₂ he)
  have hr₃ : range φ₃ = discBd Δ₂ := by
    rw [← hr₂]
    ext y
    exact ⟨fun ⟨w, hw⟩ => ⟨_, hw⟩, fun ⟨w, hw⟩ => ⟨w⁻¹, by simpa [φ₃] using hw⟩⟩
  obtain ⟨G₁, hG₁, hD₁⟩ := exists_plane_extension hΔ₁ hc₁ hi₁ hr₁
  obtain ⟨G₃, hG₃, hD₃⟩ := exists_plane_extension hΔ₂ hc₃ hi₃ hr₃
  obtain ⟨s', t', hs', hst', ht', hv', hw''⟩ := circleCyclic_inv h
  have e := wind_eq_of_nested hΔ₁ hΔ₂ hsub hc₁ hc₃ hr₁ hr₃ G₁ G₃ hG₁ hG₃ hD₁ hD₃
    (u₁ := u) (u₂ := u'⁻¹) hs hst ht hs' hst' ht' (by simp [φ₃, ha])
    (by rw [← hv']; simp [φ₃, hb]) (by rw [← hw'']; simp [φ₃, hc])
  have hzi : G₁ 0 ∈ discInt Δ₁ := by
    rw [discInt_eq_of_extension G₁ hG₁ hr₁ hD₁]
    exact ⟨0, by simp, rfl⟩
  have hzi₂ := discInt_mono isManifoldPoint_complex hΔ₁ hsub hzi
  have h1 := hp₁ _ hzi
  have h2 := hp₂ _ hzi₂
  have hoff : ∀ w, φ₂ w ≠ G₁ 0 := fun w he =>
    hzi₂.2 (by rw [← he, ← hr₂]; exact mem_range_self w)
  rw [e, wind_inv hc₂ hoff] at h1
  linarith

/-- `a, b, c` occur in this order on `bd(Δ)`, read positively. -/
def planePos (Δ : Set ℂ) (a b c : ℂ) : Prop :=
  ∃ φ u v w, IsPosParam Δ φ ∧ φ u = a ∧ φ v = b ∧ φ w = c ∧ CircleCyclic u v w

/-! ### Complex conjugation and `EuclideanPlane` clockwise orientation -/

theorem isAngle_conj {g : ℝ → ℂ} {L : ℝ → ℝ} (hL : IsAngle g L) :
    IsAngle (fun t => starRingEnd ℂ (g t)) (fun t => -L t) := by
  refine ⟨hL.1.neg, fun t => ?_⟩
  have h1 := congrArg (starRingEnd ℂ) (hL.2 t)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, mul_neg] at h1
  change starRingEnd ℂ (g t) = ↑‖starRingEnd ℂ (g t)‖ * Complex.exp (↑(-L t) * Complex.I)
  rw [Complex.norm_conj, Complex.ofReal_neg, neg_mul, h1]

theorem turn_conj {g : ℝ → ℂ} (hg : Continuous g) (h0 : ∀ t, g t ≠ 0) (s t : ℝ) :
    turn (fun x => starRingEnd ℂ (g x)) s t = - turn g s t := by
  obtain ⟨L, hL⟩ := exists_isAngle hg h0
  have h0' : ∀ x, starRingEnd ℂ (g x) ≠ 0 := fun x => map_ne_zero_iff _
    (RingHom.injective _) |>.mpr (h0 x)
  rw [(isAngle_conj hL).turn_eq h0', hL.turn_eq h0]
  ring

theorem wind_conj {φ : Circle → ℂ} (hc : Continuous φ) {z : ℂ} (h0 : ∀ w, φ w ≠ z) :
    wind (fun w => starRingEnd ℂ (φ w)) (starRingEnd ℂ z) = - wind φ z := by
  have hcoe : Continuous fun t : ℝ => Circle.exp t := Circle.exp.continuous
  let g : ℝ → ℂ := fun t => φ (Circle.exp t) - z
  have hg : Continuous g := (hc.comp hcoe).sub continuous_const
  have hg0 : ∀ t, g t ≠ 0 := fun t => sub_ne_zero.mpr (h0 _)
  have heq : (fun t => starRingEnd ℂ (φ (Circle.exp t)) - starRingEnd ℂ z) =
      fun t => starRingEnd ℂ (g t) := by
    funext t
    exact (map_sub (starRingEnd ℂ) (φ (Circle.exp t)) z).symm
  unfold wind
  rw [heq, turn_conj hg hg0]

/-- A circle homeomorphism `φ : Circle ≃ₜ C` onto the boundary of a closed disc `D` in
`EuclideanPlane` has the plane's positive ("clockwise" in Graph Minors IX, Section 1, page 42)
orientation if its winding around every interior point of `D` (transferred to `ℂ` via
`complexPlane.symm`) is positive. -/
def IsClockwiseDiscHomeo (D : Set EuclideanPlane) {C : Set EuclideanPlane}
    (φ : Circle ≃ₜ C) : Prop :=
  ∀ x ∈ interior D, 0 < wind (fun w => complexPlane.symm (φ w).1) (complexPlane.symm x)

theorem isClosedDisc_symm_image_complexPlane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    IsClosedDisc (complexPlane.symm '' D) :=
  (hD.image complexPlane.symm.continuous.continuousOn complexPlane.continuous.continuousOn
    (fun x _ => complexPlane.apply_symm_apply x)).1

theorem discBd_symm_image_complexPlane_eq_image_discBd {D : Set EuclideanPlane}
    (hD : IsClosedDisc D) :
    discBd (complexPlane.symm '' D) = complexPlane.symm '' discBd D :=
  (hD.image complexPlane.symm.continuous.continuousOn complexPlane.continuous.continuousOn
    (fun x _ => complexPlane.apply_symm_apply x)).2

theorem discBd_symm_image_complexPlane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    discBd (complexPlane.symm '' D) = complexPlane.symm '' subBd D := by
  rw [subBd_eq_discBd_euclideanPlane hD, discBd_symm_image_complexPlane_eq_image_discBd hD]

theorem discInt_symm_image_complexPlane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    discInt (complexPlane.symm '' D) = complexPlane.symm '' interior D := by
  rw [← interior_eq_discInt_complex (isClosedDisc_symm_image_complexPlane hD)]
  exact (complexPlane.symm.toHomeomorph.image_interior D).symm

theorem isClockwiseDiscHomeo_iff_isPosParam {D : Set EuclideanPlane} (hD : IsClosedDisc D)
    {C : Set EuclideanPlane} (hC : C = subBd D) (φ : Circle ≃ₜ C) :
    IsClockwiseDiscHomeo D φ ↔
      IsPosParam (complexPlane.symm '' D) (fun w => complexPlane.symm (φ w).1) := by
  let ψ : Circle → ℂ := fun w => complexPlane.symm (φ w).1
  have hψc : Continuous ψ :=
    complexPlane.symm.continuous.comp (continuous_subtype_val.comp φ.continuous)
  have hψi : Function.Injective ψ := fun a b h =>
    φ.injective (Subtype.ext (complexPlane.symm.injective h))
  have hψr : range ψ = discBd (complexPlane.symm '' D) := by
    rw [discBd_symm_image_complexPlane hD, ← hC]
    ext z
    exact ⟨fun ⟨w, hw⟩ => hw ▸ mem_image_of_mem _ (φ w).2,
      fun ⟨x, hx, hxz⟩ => ⟨φ.symm ⟨x, hx⟩, by simp [ψ, hxz]⟩⟩
  refine ⟨fun h => ⟨hψc, hψi, hψr, ?_⟩, fun h x hx => ?_⟩
  · intro z hz
    rw [discInt_symm_image_complexPlane hD] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact h x hx
  · refine h.2.2.2 (complexPlane.symm x) ?_
    rw [discInt_symm_image_complexPlane hD]
    exact mem_image_of_mem _ hx

theorem isClockwiseDiscHomeo_or_inv {D : Set EuclideanPlane} (hD : IsClosedDisc D)
    {C : Set EuclideanPlane} (hC : C = subBd D) (φ : Circle ≃ₜ C) :
    IsClockwiseDiscHomeo D φ ∨ IsClockwiseDiscHomeo D ((Homeomorph.inv Circle).trans φ) := by
  rw [isClockwiseDiscHomeo_iff_isPosParam hD hC φ,
    isClockwiseDiscHomeo_iff_isPosParam hD hC ((Homeomorph.inv Circle).trans φ)]
  let ψ : Circle → ℂ := fun w => complexPlane.symm (φ w).1
  have hψc : Continuous ψ :=
    complexPlane.symm.continuous.comp (continuous_subtype_val.comp φ.continuous)
  have hψi : Function.Injective ψ := fun a b h =>
    φ.injective (Subtype.ext (complexPlane.symm.injective h))
  have hψr : range ψ = discBd (complexPlane.symm '' D) := by
    rw [discBd_symm_image_complexPlane hD, ← hC]
    ext z
    exact ⟨fun ⟨w, hw⟩ => hw ▸ mem_image_of_mem _ (φ w).2,
      fun ⟨x, hx, hxz⟩ => ⟨φ.symm ⟨x, hx⟩, by simp [ψ, hxz]⟩⟩
  exact isPosParam_or_inv (isClosedDisc_symm_image_complexPlane hD) hψc hψi hψr

theorem exists_isClockwiseDiscHomeo {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    ∃ φ : Circle ≃ₜ subBd D, IsClockwiseDiscHomeo D φ := by
  have hbd : subBd D = discBd D := subBd_eq_discBd_euclideanPlane hD
  obtain ⟨φ₀⟩ := hD.isOArc_discBd
  let φ : Circle ≃ₜ subBd D := φ₀.trans (Homeomorph.setCongr hbd.symm)
  rcases isClockwiseDiscHomeo_or_inv hD rfl φ with h | h
  · exact ⟨φ, h⟩
  · exact ⟨(Homeomorph.inv Circle).trans φ, h⟩

theorem not_isClockwiseDiscHomeo_inv {D : Set EuclideanPlane} (hD : IsClosedDisc D)
    {C : Set EuclideanPlane} (hC : C = subBd D) {φ : Circle ≃ₜ C}
    (hφ : IsClockwiseDiscHomeo D φ) :
    ¬ IsClockwiseDiscHomeo D ((Homeomorph.inv Circle).trans φ) := by
  rw [isClockwiseDiscHomeo_iff_isPosParam hD hC φ] at hφ
  rw [isClockwiseDiscHomeo_iff_isPosParam hD hC ((Homeomorph.inv Circle).trans φ)]
  exact not_isPosParam_inv (isClosedDisc_symm_image_complexPlane hD) hφ

theorem order_of_nested_euclideanPlane {D₁ D₂ : Set EuclideanPlane}
    (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂) (hsub : D₁ ⊆ D₂)
    {C₁ C₂ : Set EuclideanPlane} (hC₁ : C₁ = subBd D₁) (hC₂ : C₂ = subBd D₂)
    {φ₁ : Circle ≃ₜ C₁} {φ₂ : Circle ≃ₜ C₂}
    (hp₁ : IsClockwiseDiscHomeo D₁ φ₁) (hp₂ : IsClockwiseDiscHomeo D₂ φ₂)
    {u v w u' v' w' : Circle} (hcy : CircleCyclic u v w)
    (ha : (φ₁ u).1 = (φ₂ u').1) (hb : (φ₁ v).1 = (φ₂ v').1) (hc : (φ₁ w).1 = (φ₂ w').1) :
    CircleCyclic u' v' w' := by
  have hp₁' := (isClockwiseDiscHomeo_iff_isPosParam h₁ hC₁ φ₁).mp hp₁
  have hp₂' := (isClockwiseDiscHomeo_iff_isPosParam h₂ hC₂ φ₂).mp hp₂
  exact order_of_nested (isClosedDisc_symm_image_complexPlane h₁)
    (isClosedDisc_symm_image_complexPlane h₂) (image_mono hsub) hp₁' hp₂' hcy
    (congrArg complexPlane.symm ha) (congrArg complexPlane.symm hb)
    (congrArg complexPlane.symm hc)

/-- Reflection of `EuclideanPlane` corresponding to complex conjugation `starRingEnd ℂ` via
`complexPlane`. -/
noncomputable def conjPlane : EuclideanPlane ≃ₗᵢ[ℝ] EuclideanPlane :=
  complexPlane.symm.trans (Complex.conjLIE.trans complexPlane)

@[simp]
theorem complexPlane_symm_conjPlane (x : EuclideanPlane) :
    complexPlane.symm (conjPlane x) = starRingEnd ℂ (complexPlane.symm x) := by
  simp [conjPlane]

@[simp]
theorem conjPlane_symm : conjPlane.symm = conjPlane := by
  ext x i
  change (complexPlane (Complex.conjLIE.symm (complexPlane.symm x))) i =
    (complexPlane (Complex.conjLIE (complexPlane.symm x))) i
  rfl

@[simp]
theorem conjPlane_conjPlane (x : EuclideanPlane) : conjPlane (conjPlane x) = x :=
  conjPlane.symm_apply_apply x

theorem isClosedDisc_image_conjPlane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    IsClosedDisc (conjPlane '' D) :=
  (hD.image conjPlane.continuous.continuousOn conjPlane.symm.continuous.continuousOn
    (fun x _ => conjPlane.symm_apply_apply x)).1

theorem subBd_image_conjPlane (D : Set EuclideanPlane) :
    subBd (conjPlane '' D) = conjPlane '' subBd D := by
  rw [Surface.subBd_eq_frontier, Surface.subBd_eq_frontier]
  exact (conjPlane.toHomeomorph.image_frontier D).symm

theorem interior_image_conjPlane (D : Set EuclideanPlane) :
    interior (conjPlane '' D) = conjPlane '' interior D :=
  (conjPlane.toHomeomorph.image_interior D).symm

theorem isClockwiseDiscHomeo_conjPlane_inv {D : Set EuclideanPlane} {C : Set EuclideanPlane}
    {φ : Circle ≃ₜ C} (hdisj : ∀ w, (φ w).1 ∉ interior D)
    (hφ : IsClockwiseDiscHomeo D φ) :
    IsClockwiseDiscHomeo (conjPlane '' D)
      ((Homeomorph.inv Circle).trans (φ.trans (conjPlane.toHomeomorph.image C))) := by
  intro y hy
  rw [interior_image_conjPlane] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  let ψ : Circle → ℂ := fun w => complexPlane.symm (φ w).1
  have hψc : Continuous ψ :=
    complexPlane.symm.continuous.comp (continuous_subtype_val.comp φ.continuous)
  have h0 : ∀ w, ψ w ≠ complexPlane.symm x := fun w h =>
    hdisj w (complexPlane.symm.injective h ▸ hx)
  have h0_conj : ∀ w, starRingEnd ℂ (ψ w) ≠ starRingEnd ℂ (complexPlane.symm x) := fun w h =>
    h0 w (RingHom.injective (starRingEnd ℂ) h)
  have hψ_conj : Continuous (fun w => starRingEnd ℂ (ψ w)) :=
    Complex.continuous_conj.comp hψc
  change 0 < wind (fun w : Circle => complexPlane.symm (conjPlane (φ w⁻¹).1))
    (complexPlane.symm (conjPlane x))
  simp only [complexPlane_symm_conjPlane]
  rw [wind_inv hψ_conj h0_conj, wind_conj hψc h0, neg_neg]
  exact hφ x hx

theorem isClockwiseDiscHomeo_conjPlane_of_not {D : Set EuclideanPlane} (hD : IsClosedDisc D)
    {C : Set EuclideanPlane} (hC : C = subBd D) {φ : Circle ≃ₜ C}
    (hφ : ¬ IsClockwiseDiscHomeo D φ) :
    IsClockwiseDiscHomeo (conjPlane '' D) (φ.trans (conjPlane.toHomeomorph.image C)) := by
  have hinv : IsClockwiseDiscHomeo D ((Homeomorph.inv Circle).trans φ) :=
    (isClockwiseDiscHomeo_or_inv hD hC φ).resolve_left hφ
  intro y hy
  rw [interior_image_conjPlane] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  let ψ : Circle → ℂ := fun w => complexPlane.symm (φ w).1
  have hψc : Continuous ψ :=
    complexPlane.symm.continuous.comp (continuous_subtype_val.comp φ.continuous)
  have h0 : ∀ w, ψ w ≠ complexPlane.symm x := by
    intro w h
    have hx' : x ∈ subBd D := hC ▸ (complexPlane.symm.injective h ▸ (φ w).2)
    rw [Surface.subBd_eq_frontier] at hx'
    exact hx'.2 hx
  change 0 < wind (fun w : Circle => complexPlane.symm (conjPlane (φ w).1))
    (complexPlane.symm (conjPlane x))
  simp only [complexPlane_symm_conjPlane]
  rw [wind_conj hψc h0]
  have h1 := hinv x hx
  change 0 < wind (fun w : Circle => ψ w⁻¹) (complexPlane.symm x) at h1
  rw [wind_inv hψc h0] at h1
  linarith

end GraphMinor.Surface
