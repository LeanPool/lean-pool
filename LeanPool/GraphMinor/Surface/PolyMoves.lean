/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Polygon
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The half disc and loops on the boundary of polygons

The two loops `upLoop` (around the upper half disc) and `circLoop` (around the unit disc) give,
through the polygon
lemma, the maps of discs of the moves on words.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

/-- The half of the unit disc on one side of the real axis. -/
def halfD (σ : ℝ) : Set ℂ := {z | ‖z‖ ≤ 1 ∧ 0 ≤ σ * z.im}

theorem isClosed_halfD (σ : ℝ) : IsClosed (halfD σ) :=
  (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const (continuous_const.mul Complex.continuous_im))

theorem convex_halfD (σ : ℝ) : Convex ℝ (halfD σ) := by
  have h1 : Convex ℝ {z : ℂ | ‖z‖ ≤ 1} := by
    have := convex_closedBall (0 : ℂ) 1
    simpa [closedBall, dist_zero_right] using this
  have h2 : Convex ℝ {z : ℂ | 0 ≤ σ * z.im} := by
    intro x hx y hy a b ha hb _
    change 0 ≤ σ * (a • x + b • y).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im,
      zero_mul, add_zero]
    have h3 : 0 ≤ σ * x.im := hx
    have h4 : 0 ≤ σ * y.im := hy
    nlinarith [mul_nonneg ha h3, mul_nonneg hb h4]
  exact h1.inter h2

theorem frontier_halfD {σ : ℝ} (hσ : σ ≠ 0) :
    frontier (halfD σ) = {z | ‖z‖ = 1 ∧ 0 ≤ σ * z.im} ∪ {z | ‖z‖ ≤ 1 ∧ z.im = 0} := by
  have hcl := isClosed_halfD σ
  rw [frontier, hcl.closure_eq]
  ext z
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    by_contra hcon
    rw [mem_union, not_or] at hcon
    have h4 : ‖z‖ < 1 := lt_of_le_of_ne h1 fun he => hcon.1 ⟨he, h2⟩
    have h5 : 0 < σ * z.im := lt_of_le_of_ne h2 fun he => hcon.2 ⟨h1, by
      rcases mul_eq_zero.mp he.symm with h | h
      · exact absurd h hσ
      · exact h⟩
    refine h3 (mem_interior.mpr ⟨ball 0 1 ∩ {w | 0 < σ * w.im}, fun w hw =>
      ⟨(mem_ball_zero_iff.mp hw.1).le, le_of_lt hw.2⟩, isOpen_ball.inter
        (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)),
      mem_ball_zero_iff.mpr h4, h5⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨⟨h1.le, h2⟩, fun hi => ?_⟩
      obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior z hi
      have h3 : (((1 + ε / 2 : ℝ) : ℂ) * z) ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm, show ((1 + ε / 2 : ℝ) : ℂ) * z - z = ((ε / 2 : ℝ) : ℂ) * z by
          push_cast
          ring, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
            (by positivity)]
        linarith
      have h4 := (interior_subset (hb h3)).1
      rw [norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)] at h4
      linarith
    · refine ⟨⟨h1, by rw [h2, mul_zero]⟩, fun hi => ?_⟩
      obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior z hi
      have hs : 0 < |σ| := abs_pos.mpr hσ
      let w : ℂ := z - (((ε / 2 : ℝ) * (σ / |σ|) : ℝ) : ℂ) * Complex.I
      have h3 : w ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm]
        simp only [w, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real,
          Real.norm_eq_abs, abs_div, abs_abs, div_self hs.ne', abs_of_pos (half_pos hε)]
        linarith
      have h4 := (interior_subset (hb h3)).2
      have h5 : σ * w.im = - (ε / 2) * (|σ|) := by
        simp only [w, Complex.sub_im, h2, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub]
        have : σ * σ = |σ| * |σ| := (abs_mul_abs_self σ).symm
        field_simp
        nlinarith
      rw [h5] at h4
      nlinarith

theorem isClosedDisc_halfD {σ : ℝ} (hσ : σ ≠ 0) :
    IsClosedDisc (halfD σ) ∧ discBd (halfD σ) = {z | ‖z‖ = 1 ∧ 0 ≤ σ * z.im} ∪ {z | ‖z‖ ≤ 1 ∧ z.im
      = 0} := by
  have hint : (interior (halfD σ)).Nonempty := by
    let c : ℂ := ((1 / 2 * (σ / |σ|) : ℝ) : ℂ) * Complex.I
    have hs : 0 < |σ| := abs_pos.mpr hσ
    have hc : ‖c‖ = 1 / 2 := by
      simp only [c, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_div,
        abs_abs, div_self hs.ne']
      norm_num
    have hci : 0 < σ * c.im := by
      have : σ * c.im = 1 / 2 * |σ| := by
        simp only [c, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
          Complex.I_re,
          mul_one, mul_zero, add_zero]
        have : σ * σ = |σ| * |σ| := (abs_mul_abs_self σ).symm
        field_simp
        nlinarith
      rw [this]
      positivity
    refine ⟨c, mem_interior.mpr ⟨ball 0 1 ∩ {w | 0 < σ * w.im}, fun w hw =>
      ⟨(mem_ball_zero_iff.mp hw.1).le, le_of_lt hw.2⟩, isOpen_ball.inter
        (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)),
      mem_ball_zero_iff.mpr (by rw [hc]; norm_num), hci⟩⟩
  have hb : Bornology.IsBounded (halfD σ) :=
    (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset fun z hz => mem_closedBall_zero_iff.mpr
      hz.1
  obtain ⟨h1, h2⟩ := isClosedDisc_of_convex (convex_halfD σ) hint hb (isClosed_halfD σ)
  exact ⟨h1, h2.trans (frontier_halfD hσ)⟩

/-- `cis'` is injective on a whole turn. -/
theorem cis'_injOn' : InjOn cis' (Ioc (-Real.pi) Real.pi) := by
  intro x hx y hy he
  have h1 : Circle.exp x = Circle.exp y := Circle.ext (by simpa [cis', Circle.coe_exp] using he)
  have h2 := congrArg Complex.arg (congrArg ((↑) : Circle → ℂ) h1)
  rwa [Circle.arg_exp hx.1 hx.2, Circle.arg_exp hy.1 hy.2] at h2

theorem cis'_arg {z : ℂ} (hz : ‖z‖ = 1) : cis' (Complex.arg z) = z := by
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at this
  simpa [cis'] using this

theorem cis'_pi : cis' Real.pi = -1 := by simp [cis', Complex.exp_pi_mul_I]

theorem cis'_zero : cis' 0 = 1 := by simp [cis']

theorem cis'_im_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi) : 0 < (cis' θ).im := by
  rw [cis'_im]
  exact Real.sin_pos_of_pos_of_lt_pi h0 h1

theorem cis'_add_pi (θ : ℝ) : cis' (θ + Real.pi) = - cis' θ := by
  simp only [cis']
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- The loop around the upper half disc: first the segment from `-1` to `1`, then the upper half
circle. -/
noncomputable def upLoop (a l : ℕ) (x : ℝ) : ℂ :=
  if x ≤ a then ((-1 + 2 * x / a : ℝ) : ℂ) else cis' (Real.pi * (x - a) / l)

/-- The loop around the unit disc: the upper half circle from `1` to `-1`, then the lower one. -/
noncomputable def circLoop (l k : ℕ) (x : ℝ) : ℂ :=
  if x ≤ l then cis' (Real.pi * x / l) else cis' (Real.pi * (x - l) / k - Real.pi)

variable {a l k : ℕ}

theorem upLoop_le {x : ℝ} (hx : x ≤ a) : upLoop a l x = ((-1 + 2 * x / a : ℝ) : ℂ) := ite_eq_left hx

theorem upLoop_ge (ha : 0 < a) {x : ℝ} (hx : a ≤ x) : upLoop a l x = cis' (Real.pi * (x - a) / l)
  := by
  rcases eq_or_lt_of_le hx with rfl | h
  · have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have e : (-1 + 2 * (a : ℝ) / a) = 1 := by
      rw [mul_div_assoc, div_self ha']
      norm_num
    rw [upLoop_le le_rfl, sub_self, mul_zero, zero_div, cis'_zero, e]
    simp
  · exact ite_eq_right (not_le.mpr h)

theorem continuous_upLoop (ha : 0 < a) : Continuous (upLoop a l) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  refine Continuous.if_le (by fun_prop) (continuous_cis'.comp (by fun_prop)) continuous_id
    continuous_const fun x hx => ?_
  have e : (-1 + 2 * (a : ℝ) / a) = 1 := by
    rw [mul_div_assoc, div_self ha']
    norm_num
  have hx' : x = a := hx
  rw [hx', sub_self, mul_zero, zero_div, cis'_zero, e]
  simp

theorem upLoop_zero (ha : 0 < a) : upLoop a l 0 = -1 := by
  rw [upLoop_le (by positivity)]
  simp

theorem upLoop_end (ha : 0 < a) (hl : 0 < l) : upLoop a l ((a + l : ℕ) : ℝ) = -1 := by
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [upLoop_ge ha (by push_cast; linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])]
  push_cast
  rw [show Real.pi * ((a : ℝ) + l - a) / l = Real.pi by field_simp; ring, cis'_pi]

theorem upLoop_injOn (ha : 0 < a) (hl : 0 < l) : InjOn (upLoop a l) (Ico 0 ((a + l : ℕ) : ℝ)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hpi := Real.pi_pos
  have harc : ∀ x, (a : ℝ) < x → x < a + l → 0 < (upLoop a l x).im := fun x h1 h2 => by
    rw [upLoop_ge ha h1.le]
    refine cis'_im_pos (by have := sub_pos.mpr h1; positivity) ?_
    rw [div_lt_iff₀ hl']
    nlinarith
  intro x hx y hy he
  push_cast at hx hy
  rcases le_or_gt x a with h1 | h1 <;> rcases le_or_gt y a with h2 | h2
  · rw [upLoop_le h1, upLoop_le h2] at he
    have := Complex.ofReal_injective he
    field_simp at this
    linarith
  · exfalso
    have h3 := harc y h2 hy.2
    rw [← he, upLoop_le h1, Complex.ofReal_im] at h3
    exact lt_irrefl _ h3
  · exfalso
    have h3 := harc x h1 hx.2
    rw [he, upLoop_le h2, Complex.ofReal_im] at h3
    exact lt_irrefl _ h3
  · rw [upLoop_ge ha h1.le, upLoop_ge ha h2.le] at he
    have hb : ∀ x, (a : ℝ) < x → x < a + l → Real.pi * (x - a) / l ∈ Ioc (-Real.pi) Real.pi
      := fun x h3 h4 => by
      have h5 : 0 < Real.pi * (x - a) / l := by have := sub_pos.mpr h3; positivity
      refine ⟨by linarith, ?_⟩
      rw [div_le_iff₀ hl']
      nlinarith
    have h3 := cis'_injOn' (hb x h1 hx.2) (hb y h2 hy.2) he
    field_simp at h3
    linarith

theorem upLoop_image (ha : 0 < a) (hl : 0 < l) :
    upLoop a l '' Icc 0 ((a + l : ℕ) : ℝ) = discBd (halfD 1) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hpi := Real.pi_pos
  rw [(isClosedDisc_halfD one_ne_zero).2]
  ext z
  simp only [one_mul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    push_cast at hx
    rcases le_total x a with h | h
    · right
      rw [upLoop_le h]
      refine ⟨?_, by simp⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h1 : 0 ≤ 2 * x / a := div_nonneg (by linarith [hx.1]) ha'.le
      have h2 : 2 * x / a ≤ 2 := by
        rw [div_le_iff₀ ha']
        linarith
      constructor <;> linarith
    · left
      rw [upLoop_ge ha h]
      refine ⟨norm_cis' _, ?_⟩
      rw [cis'_im]
      refine Real.sin_nonneg_of_nonneg_of_le_pi (by have := sub_nonneg.mpr h; positivity) ?_
      rw [div_le_iff₀ hl']
      nlinarith [hx.2]
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h3 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr h2
      have h4 := Complex.arg_le_pi z
      refine ⟨a + l * Complex.arg z / Real.pi, ⟨by positivity, ?_⟩, ?_⟩
      · push_cast
        have : l * Complex.arg z / Real.pi ≤ l := by
          rw [div_le_iff₀ hpi]
          nlinarith
        linarith
      · rw [upLoop_ge ha (by have : 0 ≤ l * Complex.arg z / Real.pi := by positivity
                             linarith)]
        rw [show Real.pi * ((a : ℝ) + l * Complex.arg z / Real.pi - a) / l = Complex.arg z by
          field_simp
          ring]
        exact cis'_arg h1
    · have h3 : z = (z.re : ℂ) := Complex.ext rfl (by simp [h2])
      have h4 : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans h1
      obtain ⟨h5, h6⟩ := abs_le.mp h4
      refine ⟨a * (z.re + 1) / 2, ⟨by have : 0 ≤ z.re + 1 := by linarith
                                      positivity, ?_⟩, ?_⟩
      · push_cast
        nlinarith
      · rw [upLoop_le (by nlinarith), h3]
        congr 1
        simp only [Complex.ofReal_re]
        field_simp
        ring

/-- The upper half disc as a polygon. -/
theorem exists_up_map (ha : 0 < a) (hl : 0 < l) :
    ∃ Φ Φ' : ℂ → ℂ, BdMatch (closedBall 0 1) (halfD 1) Φ Φ' ∧
      ∀ x ∈ Icc (0 : ℝ) (a + l : ℕ), Φ (per (a + l) x) = upLoop a l x :=
  exists_polygon_map (isClosedDisc_halfD one_ne_zero).1 (by omega)
    (continuous_upLoop ha).continuousOn (upLoop_injOn ha hl)
    (by rw [upLoop_zero ha, upLoop_end ha hl]) (upLoop_image ha hl)

theorem circLoop_le {x : ℝ} (hx : x ≤ l) : circLoop l k x = cis' (Real.pi * x / l) := ite_eq_left hx

theorem circLoop_ge (hl : 0 < l) {x : ℝ} (hx : l ≤ x) :
    circLoop l k x = cis' (Real.pi * (x - l) / k - Real.pi) := by
  rcases eq_or_lt_of_le hx with rfl | h
  · have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
    rw [circLoop_le le_rfl, sub_self, mul_zero, zero_div, zero_sub,
      show Real.pi * (l : ℝ) / l = Real.pi by field_simp, cis'_pi]
    have := cis'_add_pi (-Real.pi)
    rw [neg_add_cancel, cis'_zero] at this
    linear_combination -this
  · exact ite_eq_right (not_le.mpr h)

theorem continuous_circLoop (hl : 0 < l) : Continuous (circLoop l k) := by
  refine Continuous.if_le (continuous_cis'.comp (by fun_prop)) (continuous_cis'.comp (by fun_prop))
    continuous_id continuous_const fun x hx => ?_
  have hx' : x = l := hx
  have h1 := circLoop_ge (k := k) hl (le_of_eq hx'.symm)
  rw [circLoop_le (le_of_eq hx')] at h1
  exact h1

theorem circLoop_injOn (hl : 0 < l) (hk : 0 < k) : InjOn (circLoop l k) (Ico 0 ((l + k : ℕ) : ℝ))
  := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hpi := Real.pi_pos
  let A : ℝ → ℝ := fun x => if x ≤ l then Real.pi * x / l else Real.pi * (x - l) / k - Real.pi
  have hA : ∀ x : ℝ, 0 ≤ x → x < (l : ℝ) + k → A x ∈ Ioc (-Real.pi) Real.pi ∧ circLoop l k x = cis'
    (A x) := by
    intro x h0 h1
    rcases le_or_gt x l with h | h
    · simp only [A, ite_eq_left h]
      refine ⟨⟨by have : 0 ≤ Real.pi * x / l := by positivity
                  linarith, ?_⟩, circLoop_le h⟩
      rw [div_le_iff₀ hl']
      nlinarith
    · simp only [A, ite_eq_right (not_le.mpr h)]
      refine ⟨⟨by have : 0 < Real.pi * (x - l) / k := by have := sub_pos.mpr h; positivity
                  linarith, ?_⟩, circLoop_ge hl h.le⟩
      have : Real.pi * (x - l) / k ≤ 2 * Real.pi := by
        rw [div_le_iff₀ hk']
        nlinarith
      linarith
  intro x hx y hy he
  push_cast at hx hy
  obtain ⟨h1, h2⟩ := hA x hx.1 hx.2
  obtain ⟨h3, h4⟩ := hA y hy.1 hy.2
  rw [h2, h4] at he
  have h5 := cis'_injOn' h1 h3 he
  have hsign : ∀ x : ℝ, 0 ≤ x → x ≤ l → 0 ≤ A x := fun x h6 h7 => by
    simp only [A, ite_eq_left h7]
    positivity
  have hsign' : ∀ x : ℝ, (l : ℝ) < x → x < (l : ℝ) + k → A x < 0 := fun x h6 h7 => by
    simp only [A, ite_eq_right (not_le.mpr h6)]
    have : Real.pi * (x - l) / k < Real.pi := by
      rw [div_lt_iff₀ hk']
      nlinarith
    linarith
  rcases le_or_gt x l with h6 | h6 <;> rcases le_or_gt y l with h7 | h7
  · simp only [A, ite_eq_left h6, ite_eq_left h7] at h5
    field_simp at h5
    exact h5
  · exfalso
    linarith [hsign x hx.1 h6, hsign' y h7 hy.2]
  · exfalso
    linarith [hsign y hy.1 h7, hsign' x h6 hx.2]
  · simp only [A, ite_eq_right (not_le.mpr h6), ite_eq_right (not_le.mpr h7)] at h5
    have : Real.pi * (x - l) / k = Real.pi * (y - l) / k := by linarith
    field_simp at this
    linarith

theorem circLoop_image (hl : 0 < l) (hk : 0 < k) :
    circLoop l k '' Icc 0 ((l + k : ℕ) : ℝ) = discBd (closedBall (0 : ℂ) 1) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hpi := Real.pi_pos
  rw [isClosedDisc_closedBall.2]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases le_total x l with h | h
    · rw [circLoop_le h]
      exact cis'_mem_sphere _
    · rw [circLoop_ge hl h]
      exact cis'_mem_sphere _
  · intro hz
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have h1 := Complex.arg_le_pi z
    have h2 := Complex.neg_pi_lt_arg z
    rcases le_total 0 (Complex.arg z) with h | h
    · refine ⟨l * Complex.arg z / Real.pi, ⟨by positivity, ?_⟩, ?_⟩
      · push_cast
        rw [div_le_iff₀ hpi]
        nlinarith
      · rw [circLoop_le (by rw [div_le_iff₀ hpi]; nlinarith)]
        rw [show Real.pi * ((l : ℝ) * Complex.arg z / Real.pi) / l = Complex.arg z by
          field_simp]
        exact cis'_arg hn
    · have h3 : 0 ≤ Complex.arg z + Real.pi := by linarith
      refine ⟨l + k * (Complex.arg z + Real.pi) / Real.pi, ⟨by positivity, ?_⟩, ?_⟩
      · push_cast
        have : k * (Complex.arg z + Real.pi) / Real.pi ≤ k := by
          rw [div_le_iff₀ hpi]
          nlinarith
        linarith
      · rw [circLoop_ge hl (by have : 0 ≤ k * (Complex.arg z + Real.pi) / Real.pi := by positivity
                               linarith)]
        rw [show Real.pi * ((l : ℝ) + k * (Complex.arg z + Real.pi) / Real.pi - l) / k - Real.pi
          = Complex.arg z by field_simp; ring]
        exact cis'_arg hn

theorem circLoop_zero (hk : 0 < k) (hl : 0 < l) : circLoop l k 0 = circLoop l k ((l + k : ℕ) : ℝ)
  := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [circLoop_le (by positivity), circLoop_ge hl (by push_cast; linarith [(Nat.cast_nonneg k :
    (0 : ℝ) ≤ k)])]
  push_cast
  rw [show Real.pi * ((l : ℝ) + k - l) / k - Real.pi = 0 by field_simp; ring]
  simp

/-- The unit disc as a polygon, with sides on the two half circles. -/
theorem exists_circ_map (hl : 0 < l) (hk : 0 < k) :
    ∃ Φ Φ' : ℂ → ℂ, BdMatch (closedBall 0 1) (closedBall 0 1) Φ Φ' ∧
      ∀ x ∈ Icc (0 : ℝ) (l + k : ℕ), Φ (per (l + k) x) = circLoop l k x :=
  exists_polygon_map isClosedDisc_closedBall.1 (by omega) (continuous_circLoop hl).continuousOn
    (circLoop_injOn hl hk) (circLoop_zero hk hl) (circLoop_image hl hk)

end GraphMinor.Surface
