/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Cap
public import LeanPool.GraphMinor.Surface.Polygon

/-!
# A polygon and its lunes in the unit disc

Take points on the unit circle at angles `θ i`, in order. The chord from one point to the next cuts
a lune off the unit disc, and what is left
after all the lunes are gone is the convex polygon on the points. This file gives the facts on the
polygon and the lunes that are used to turn a
vortex into a cuff in XVII (13.1).

The angles are indexed by the integers, with period `k`, so that all shifts are easy. Everything is
described by the linear functions `gf μ`:
the lune at `i` is the part of the unit disc where `gf (midAngle θ i) ≥ halfCos θ i`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

/-- The point of the unit circle at angle `s`. -/
noncomputable def eC (s : ℝ) : ℂ := (Circle.exp s : ℂ)

theorem eC_re (s : ℝ) : (eC s).re = Real.cos s := by
  simp [eC, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

theorem eC_im (s : ℝ) : (eC s).im = Real.sin s := by
  simp [eC, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

theorem norm_eC (s : ℝ) : ‖eC s‖ = 1 := Circle.norm_coe _

theorem eC_add_int (s : ℝ) (m : ℤ) : eC (s + 2 * Real.pi * m) = eC s := by
  apply Complex.ext
  · rw [eC_re, eC_re, mul_comm (2 * Real.pi), Real.cos_add_int_mul_two_pi]
  · rw [eC_im, eC_im, mul_comm (2 * Real.pi), Real.sin_add_int_mul_two_pi]

theorem exists_eC {w : ℂ} (hw : ‖w‖ = 1) : ∃ s, w = eC s := by
  refine ⟨Complex.arg w, ?_⟩
  apply Complex.ext
  · rw [eC_re, Complex.cos_arg (by intro h; simp [h] at hw), hw, div_one]
  · rw [eC_im, Complex.sin_arg, hw, div_one]

/-- The linear function that measures how far `w` goes in the direction `μ`. -/
noncomputable def gf (μ : ℝ) (w : ℂ) : ℝ := w.re * Real.cos μ + w.im * Real.sin μ

theorem gf_eC (μ s : ℝ) : gf μ (eC s) = Real.cos (s - μ) := by
  rw [gf, eC_re, eC_im, Real.cos_sub]

theorem gf_add (μ : ℝ) (a b : ℂ) : gf μ (a + b) = gf μ a + gf μ b := by
  simp only [gf, Complex.add_re, Complex.add_im]
  ring

theorem gf_smul (μ t : ℝ) (a : ℂ) : gf μ (t • a) = t * gf μ a := by
  simp only [gf, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem continuous_gf (μ : ℝ) : Continuous (gf μ) := by
  unfold gf
  fun_prop

theorem gf_period (μ : ℝ) (m : ℤ) : gf (μ + 2 * Real.pi * m) = gf μ := by
  funext w
  rw [gf, gf, mul_comm (2 * Real.pi), Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem gf_segment_le {μ c : ℝ} {a b w : ℂ} (ha : gf μ a ≤ c) (hb : gf μ b ≤ c)
  (hw : w ∈ segment ℝ a b) : gf μ w ≤ c := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hw
  rw [gf_add, gf_smul, gf_smul]
  have h : c = x * c + y * c := by rw [← add_mul, hxy, one_mul]
  have h1 := mul_le_mul_of_nonneg_left ha hx
  have h2 := mul_le_mul_of_nonneg_left hb hy
  linarith

theorem gf_segment_eq {μ c : ℝ} {a b w : ℂ} (ha : gf μ a ≤ c) (hb : gf μ b ≤ c)
  (hw : w ∈ segment ℝ a b) (he : gf μ w = c) :
    w = a ∨ w = b ∨ (gf μ a = c ∧ gf μ b = c) := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hw
  rw [gf_add, gf_smul, gf_smul] at he
  rcases hx.eq_or_lt with rfl | hx'
  · right; left
    have : y = 1 := by linarith
    simp [this]
  rcases hy.eq_or_lt with rfl | hy'
  · left
    have : x = 1 := by linarith
    simp [this]
  right; right
  have h : c = x * c + y * c := by rw [← add_mul, hxy, one_mul]
  have h1 := mul_le_mul_of_nonneg_left ha hx
  have h2 := mul_le_mul_of_nonneg_left hb hy
  exact ⟨le_antisymm ha (le_of_mul_le_mul_left (by linarith) hx'),
    le_antisymm hb (le_of_mul_le_mul_left (by linarith) hy')⟩

/-- Any point of the unit disc lies on a chord of the circle on which `gf μ` is constant. -/
theorem exists_level_chord (μ : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ gf μ a = gf μ w ∧ gf μ b = gf μ w ∧ w ∈ segment ℝ a b := by
  set C := Real.cos μ with hC
  set S := Real.sin μ with hS
  have hCS : C * C + S * S = 1 := by
    have := Real.sin_sq_add_cos_sq μ
    nlinarith
  set x := w.re * C + w.im * S with hx
  set y := w.im * C - w.re * S with hy
  have hwre : w.re = x * C - y * S := by
    rw [hx, hy]
    linear_combination (-w.re) * hCS
  have hwim : w.im = x * S + y * C := by
    rw [hx, hy]
    linear_combination (-w.im) * hCS
  have hnorm : x * x + y * y ≤ 1 := by
    have h1 : ‖w‖ ^ 2 ≤ 1 := by
      have := norm_nonneg w
      nlinarith
    have h2 : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h3 : x * x + y * y = (w.re * w.re + w.im * w.im) * (C * C + S * S) := by
      rw [hx, hy]
      ring
    rw [h3, hCS, mul_one, ← h2]
    exact h1
  set r := Real.sqrt (1 - x * x) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = 1 - x * x := Real.mul_self_sqrt (by nlinarith [mul_self_nonneg y])
  have hyr : |y| ≤ r := by
    apply abs_le_of_sq_le_sq' (by nlinarith) hr0 |> abs_le.mpr
  let pt : ℝ → ℂ := fun t => ⟨x * C - t * S, x * S + t * C⟩
  have hpt : ∀ t, t * t = r * r → ‖pt t‖ = 1 := fun t ht => by
    have h1 : ‖pt t‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      change (x * C - t * S) * (x * C - t * S) + (x * S + t * C) * (x * S + t * C) = 1
      have : (x * C - t * S) * (x * C - t * S) + (x * S + t * C) * (x * S + t * C) =
        (x * x + t * t) * (C * C + S * S) := by ring
      rw [this, hCS, ht, hrr]
      ring
    have h2 := norm_nonneg (pt t)
    nlinarith
  have hgf : ∀ t, gf μ (pt t) = x := fun t => by
    change (x * C - t * S) * C + (x * S + t * C) * S = x
    linear_combination x * hCS
  have hgw : gf μ w = x := rfl
  refine ⟨pt r, pt (-r), hpt r rfl, hpt (-r) (by ring), by rw [hgf, hgw], by rw [hgf, hgw], ?_⟩
  by_cases hr' : r = 0
  · have hy0 : y = 0 := by
      have := abs_nonneg y
      rw [hr'] at hyr
      exact abs_eq_zero.mp (le_antisymm hyr this)
    have : w = pt r := by
      apply Complex.ext
      · change w.re = x * C - r * S
        rw [hwre, hy0, hr']
      · change w.im = x * S + r * C
        rw [hwim, hy0, hr']
    rw [this]
    exact left_mem_segment _ _ _
  have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr')
  have hab := abs_le.mp hyr
  refine ⟨(r + y) / (2 * r), (r - y) / (2 * r), by apply div_nonneg <;> linarith, by apply
    div_nonneg <;> linarith, by field_simp; ring, ?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, pt]
    rw [hwre]
    field_simp
    ring
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, pt]
    rw [hwim]
    field_simp
    ring

theorem cos_arc {h x : ℝ} (hh : 0 < h) (hh' : h < Real.pi) :
    (|x| ≤ h → Real.cos h ≤ Real.cos x) ∧ (|x| < h → Real.cos h < Real.cos x) ∧
      (h ≤ x → x ≤ 2 * Real.pi - h → Real.cos x ≤ Real.cos h) ∧ (h < x → x < 2 * Real.pi - h
        → Real.cos x < Real.cos h) := by
  refine ⟨fun hx => ?_, fun hx => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [← Real.cos_abs x]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) hh'.le hx
  · rw [← Real.cos_abs x]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg x) hh'.le hx
  · rcases le_total x Real.pi with hp | hp
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hh.le hp h1
    · rw [← Real.cos_two_pi_sub x]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hh.le (by linarith) (by linarith)
  · rcases le_total x Real.pi with hp | hp
    · exact Real.cos_lt_cos_of_nonneg_of_le_pi hh.le hp h1
    · rw [← Real.cos_two_pi_sub x]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi hh.le (by linarith) (by linarith)

/-- The middle of the arc at `i`. -/
noncomputable def midAngle (θ : ℤ → ℝ) (i : ℤ) : ℝ := (θ i + θ (i + 1)) / 2

/-- The cosine of half the arc at `i`. -/
noncomputable def halfCos (θ : ℤ → ℝ) (i : ℤ) : ℝ := Real.cos ((θ (i + 1) - θ i) / 2)

/-- The lune at `i`. -/
def lune (θ : ℤ → ℝ) (i : ℤ) : Set ℂ := {w | ‖w‖ ≤ 1 ∧ halfCos θ i ≤ gf (midAngle θ i) w}

/-- The polygon. -/
def hull (θ : ℤ → ℝ) : Set ℂ := {w | ‖w‖ ≤ 1 ∧ ∀ i, gf (midAngle θ i) w ≤ halfCos θ i}

/-- The hypotheses on the angles: they increase, with period `k`. -/
structure IsAngles (θ : ℤ → ℝ) (k : ℤ) : Prop where
  three : 3 ≤ k
  mono : StrictMono θ
  period : ∀ n m : ℤ, θ (n + k * m) = θ n + 2 * Real.pi * m

namespace IsAngles

variable {θ : ℤ → ℝ} {k : ℤ} (A : IsAngles θ k)
include A

theorem half_pos (i : ℤ) : 0 < (θ (i + 1) - θ i) / 2 := by
  have := A.mono (show i < i + 1 by omega)
  linarith

theorem half_lt (i : ℤ) : (θ (i + 1) - θ i) / 2 < Real.pi := by
  have h1 := A.mono (show i + 1 < i + k by have := A.three; omega)
  have h2 := A.period i 1
  rw [mul_one, Int.cast_one, mul_one] at h2
  rw [h2] at h1
  linarith

theorem midAngle_shift (i m : ℤ) : midAngle θ (i + k * m) = midAngle θ i + 2 * Real.pi * m := by
  have h := A.period (i + 1) m
  rw [midAngle, midAngle, A.period, show i + k * m + 1 = i + 1 + k * m by ring, h]
  ring

theorem halfCos_shift (i m : ℤ) : halfCos θ (i + k * m) = halfCos θ i := by
  have h := A.period (i + 1) m
  rw [halfCos, halfCos, A.period, show i + k * m + 1 = i + 1 + k * m by ring, h]
  congr 1
  ring

theorem lune_shift (i m : ℤ) : lune θ (i + k * m) = lune θ i := by
  rw [lune, lune, A.midAngle_shift, A.halfCos_shift, gf_period]

theorem gf_arc {i : ℤ} {s : ℝ} (h1 : θ i ≤ s) (h2 : s ≤ θ (i + 1)) : halfCos θ i ≤ gf
  (midAngle θ i) (eC s) := by
  rw [gf_eC]
  refine (cos_arc (A.half_pos i) (A.half_lt i)).1 (abs_le.mpr ⟨?_, ?_⟩) <;> simp only [midAngle]
    <;> linarith

theorem gf_arc_lt {i : ℤ} {s : ℝ} (h1 : θ i < s) (h2 : s < θ (i + 1)) : halfCos θ i < gf
  (midAngle θ i) (eC s) := by
  rw [gf_eC]
  refine (cos_arc (A.half_pos i) (A.half_lt i)).2.1 (abs_lt.mpr ⟨?_, ?_⟩) <;> simp only [midAngle]
    <;> linarith

theorem gf_off {i : ℤ} {s : ℝ} (h1 : θ (i + 1) ≤ s) (h2 : s ≤ θ i + 2 * Real.pi) : gf
  (midAngle θ i) (eC s) ≤ halfCos θ i := by
  rw [gf_eC]
  refine (cos_arc (A.half_pos i) (A.half_lt i)).2.2.1 ?_ ?_ <;> simp only [midAngle] <;> linarith

theorem gf_off_lt {i : ℤ} {s : ℝ} (h1 : θ (i + 1) < s) (h2 : s < θ i + 2 * Real.pi) : gf
  (midAngle θ i) (eC s) < halfCos θ i := by
  rw [gf_eC]
  refine (cos_arc (A.half_pos i) (A.half_lt i)).2.2.2 ?_ ?_ <;> simp only [midAngle] <;> linarith

theorem theta_top (i : ℤ) : θ (i + k) = θ i + 2 * Real.pi := by
  have h2 := A.period i 1
  rwa [mul_one, Int.cast_one, mul_one] at h2

/-- A shift by a multiple of `k` puts `i` in the range from `j + 1` to `j + k`. -/
theorem exists_shift (i j : ℤ) : ∃ m, j + 1 ≤ i + k * m ∧ i + k * m ≤ j + k := by
  have hk : 0 < k := by have := A.three; omega
  refine ⟨-((i - j - 1) / k), ?_, ?_⟩
  · have h1 := Int.emod_nonneg (i - j - 1) hk.ne'
    have h2 := Int.emod_add_mul_ediv (i - j - 1) k
    nlinarith
  · have h1 := Int.emod_lt_of_pos (i - j - 1) hk
    have h2 := Int.emod_add_mul_ediv (i - j - 1) k
    nlinarith

theorem node_shift (i m : ℤ) : eC (θ (i + k * m)) = eC (θ i) := by
  rw [A.period, eC_add_int]

/-- All the nodes lie on the far side of each chord, or on the chord. -/
theorem node_le (i j : ℤ) : gf (midAngle θ j) (eC (θ i)) ≤ halfCos θ j := by
  obtain ⟨m, h1, h2⟩ := A.exists_shift i j
  rw [← A.node_shift i m]
  exact A.gf_off (A.mono.monotone h1) ((A.mono.monotone h2).trans_eq (A.theta_top j))

/-- The only nodes on a chord are its ends. -/
theorem node_eq {i j : ℤ} (h : gf (midAngle θ j) (eC (θ i)) = halfCos θ j) : ∃ m, i + k * m = j + 1
  ∨ i + k * m = j + k := by
  obtain ⟨m, h1, h2⟩ := A.exists_shift i j
  refine ⟨m, ?_⟩
  by_contra hn
  push Not at hn
  rw [← A.node_shift i m] at h
  have := A.gf_off_lt (A.mono (show j + 1 < i + k * m by omega))
    ((A.mono (show i + k * m < j + k by omega)).trans_eq (A.theta_top j))
  exact this.ne h

/-- Every point of the circle lies on an arc. -/
theorem exists_arc (a : ℝ) : ∃ i, θ i ≤ a ∧ a < θ (i + 1) := by
  have hpi := Real.pi_pos
  obtain ⟨m₁, hm₁⟩ := exists_int_lt ((a - θ 0) / (2 * Real.pi))
  obtain ⟨m₂, hm₂⟩ := exists_int_gt ((a - θ 0) / (2 * Real.pi))
  rw [lt_div_iff₀ (by positivity)] at hm₁
  rw [div_lt_iff₀ (by positivity)] at hm₂
  have hlow : θ (k * m₁) ≤ a := by
    have := A.period 0 m₁
    rw [zero_add] at this
    rw [this]
    nlinarith
  have hhigh : ∀ n, θ n ≤ a → n ≤ k * m₂ := fun n hn => by
    by_contra hlt
    push Not at hlt
    have h1 := A.mono hlt
    have := A.period 0 m₂
    rw [zero_add] at this
    rw [this] at h1
    nlinarith
  obtain ⟨i, hi, hmax⟩ := Int.exists_greatest_of_bdd (P := fun n => θ n
    ≤ a) ⟨k * m₂, hhigh⟩ ⟨k * m₁, hlow⟩
  refine ⟨i, hi, ?_⟩
  by_contra hn
  push Not at hn
  have := hmax (i + 1) hn
  omega

/-- A point of the circle in a lune lies on the arc of that lune. -/
theorem mem_arc {i : ℤ} {a : ℂ} (ha : ‖a‖ = 1) (h : halfCos θ i ≤ gf (midAngle θ i) a) : ∃ s, θ i
  ≤ s ∧ s ≤ θ (i + 1) ∧ a = eC s := by
  obtain ⟨s₀, rfl⟩ := exists_eC ha
  obtain ⟨m, hm⟩ : ∃ m : ℤ, s₀ + 2 * Real.pi * m ∈ Ico (θ i) (θ i + 2 * Real.pi) := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    obtain ⟨m, hm, -⟩ := existsUnique_add_zsmul_mem_Ico hpi s₀ (θ i)
    refine ⟨m, ?_⟩
    simpa [mul_comm] using hm
  refine ⟨s₀ + 2 * Real.pi * m, hm.1, ?_, (eC_add_int s₀ m).symm⟩
  by_contra hn
  push Not at hn
  rw [← eC_add_int s₀ m] at h
  exact absurd h (not_le.mpr (A.gf_off_lt hn hm.2))

/-- Two different lunes lie on opposite sides of the chord of the first. -/
theorem lune_le {i j : ℤ} (hij : ∀ m, j + k * m ≠ i + k) {w : ℂ} (hw : w ∈ lune θ j) : gf
  (midAngle θ i) w ≤ halfCos θ i := by
  obtain ⟨a, b, ha, hb, hga, hgb, hseg⟩ := exists_level_chord (midAngle θ j) hw.1
  have key : ∀ c : ℂ, ‖c‖ = 1 → gf (midAngle θ j) c = gf (midAngle θ j) w → gf (midAngle θ i) c
    ≤ halfCos θ i := fun c hc he => by
    obtain ⟨s, h1, h2, rfl⟩ := A.mem_arc hc (he ▸ hw.2)
    obtain ⟨m, hm1, hm2⟩ := A.exists_shift j i
    have hne := hij m
    have h3 : θ (i + 1) ≤ s + 2 * Real.pi * m := by
      have := A.mono.monotone hm1
      have h4 := A.period j m
      linarith
    have h4 : s + 2 * Real.pi * m ≤ θ i + 2 * Real.pi := by
      have h5 := A.mono.monotone (show j + k * m + 1 ≤ i + k by omega)
      have h6 := A.period (j + 1) m
      rw [show j + 1 + k * m = j + k * m + 1 by ring] at h6
      have := A.theta_top i
      linarith
    rw [← eC_add_int s m]
    exact A.gf_off h3 h4
  exact gf_segment_le (key a ha hga) (key b hb hgb) hseg

theorem chord_eq {i : ℤ} {w : ℂ} (hw : ‖w‖ ≤ 1) (he : gf (midAngle θ i) w = halfCos θ i) :
    w ∈ segment ℝ (eC (θ i)) (eC (θ (i + 1))) := by
  obtain ⟨a, b, ha, hb, hga, hgb, hseg⟩ := exists_level_chord (midAngle θ i) hw
  have key : ∀ c : ℂ, ‖c‖ = 1 → gf (midAngle θ i) c = halfCos θ i → c = eC (θ i) ∨ c = eC (θ
    (i + 1)) := fun c hc he' => by
    obtain ⟨s, h1, h2, rfl⟩ := A.mem_arc hc he'.ge
    rcases h1.eq_or_lt with rfl | h1'
    · exact Or.inl rfl
    rcases h2.eq_or_lt with rfl | h2'
    · exact Or.inr rfl
    exact absurd he' (A.gf_arc_lt h1' h2').ne'
  have hend : ∀ x y : ℂ, x ∈ ({eC (θ i), eC (θ (i + 1))} : Set ℂ) → y ∈ ({eC (θ i), eC (θ
    (i + 1))} : Set ℂ) →
      segment ℝ x y ⊆ segment ℝ (eC (θ i)) (eC (θ (i + 1))) := fun x y hx hy =>
    (convex_segment _ _).segment_subset (by
      rcases hx with rfl | rfl
      · exact left_mem_segment _ _ _
      · exact right_mem_segment _ _ _) (by
      rcases hy with rfl | rfl
      · exact left_mem_segment _ _ _
      · exact right_mem_segment _ _ _)
  exact hend a b (key a ha (hga.trans he)) (key b hb (hgb.trans he)) hseg

omit A in
theorem seg_norm_le {i : ℤ} {w : ℂ} (hw : w ∈ segment ℝ (eC (θ i)) (eC (θ (i + 1)))) : ‖w‖ ≤ 1 := by
  have : w ∈ closedBall (0 : ℂ) 1 := (convex_closedBall (0 : ℂ) 1).segment_subset
    (by simp [norm_eC]) (by simp [norm_eC]) hw
  simpa using this

theorem seg_le (i j : ℤ) {w : ℂ} (hw : w ∈ segment ℝ (eC (θ i)) (eC (θ (i + 1)))) : gf
  (midAngle θ j) w ≤ halfCos θ j :=
  gf_segment_le (A.node_le i j) (A.node_le (i + 1) j) hw

theorem seg_ge (i : ℤ) {w : ℂ} (hw : w ∈ segment ℝ (eC (θ i)) (eC (θ (i + 1)))) : halfCos θ i ≤ gf
  (midAngle θ i) w := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hw
  rw [gf_add, gf_smul, gf_smul]
  have h1 := A.gf_arc (le_refl (θ i)) (A.mono (show i < i + 1 by omega)).le
  have h2 := A.gf_arc (A.mono (show i < i + 1 by omega)).le (le_refl (θ (i + 1)))
  have h : halfCos θ i = x * halfCos θ i + y * halfCos θ i := by rw [← add_mul, hxy, one_mul]
  have h3 := mul_le_mul_of_nonneg_left h1 hx
  have h4 := mul_le_mul_of_nonneg_left h2 hy
  linarith

/-- The lune meets the polygon in the chord. -/
theorem lune_inter_hull (i : ℤ) : lune θ i ∩ hull θ = segment ℝ (eC (θ i)) (eC (θ (i + 1))) := by
  ext w
  constructor
  · rintro ⟨h1, h2⟩
    exact A.chord_eq h1.1 (le_antisymm (h2.2 i) h1.2)
  · intro hw
    exact ⟨⟨IsAngles.seg_norm_le (θ := θ) hw, A.seg_ge i hw⟩, IsAngles.seg_norm_le (θ
      := θ) hw, fun j => A.seg_le i j hw⟩

omit A in
theorem isLinear_gf (μ : ℝ) : IsLinearMap ℝ (gf μ) := ⟨gf_add μ, fun t a => gf_smul μ t a⟩

omit A in
theorem lune_eq (i : ℤ) : lune θ i = closedBall 0 1 ∩ {w | halfCos θ i ≤ gf (midAngle θ i) w} := by
  ext w
  simp [lune]

omit A in
theorem hull_eq : hull θ = closedBall 0 1 ∩ ⋂ i, {w | gf (midAngle θ i) w ≤ halfCos θ i} := by
  ext w
  simp [hull]

omit A in
theorem convex_lune (i : ℤ) : Convex ℝ (lune θ i) := by
  rw [lune_eq]
  exact (convex_closedBall _ _).inter (convex_halfSpace_ge (isLinear_gf _) _)

omit A in
theorem convex_hull' : Convex ℝ (hull θ) := by
  rw [hull_eq]
  exact (convex_closedBall _ _).inter (convex_iInter fun i => convex_halfSpace_le (isLinear_gf _) _)

omit A in
theorem isClosed_lune (i : ℤ) : IsClosed (lune θ i) := by
  rw [lune_eq]
  exact isClosed_closedBall.inter (isClosed_le continuous_const (continuous_gf _))

omit A in
theorem isClosed_hull : IsClosed (hull θ) := by
  rw [hull_eq]
  exact isClosed_closedBall.inter (isClosed_iInter fun i => isClosed_le
    (continuous_gf _) continuous_const)

omit A in
theorem lune_subset (i : ℤ) : lune θ i ⊆ closedBall 0 1 := fun _ hw => by simpa using hw.1

omit A in
theorem hull_subset : hull θ ⊆ closedBall 0 1 := fun _ hw => by simpa using hw.1

theorem interior_lune (i : ℤ) : (interior (lune θ i)).Nonempty := by
  have h1 : Real.cos Real.pi < halfCos θ i := Real.cos_lt_cos_of_nonneg_of_le_pi
    (A.half_pos i).le le_rfl (A.half_lt i)
  have h2 : halfCos θ i < Real.cos 0 := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (A.half_lt i).le
    (A.half_pos i)
  rw [Real.cos_pi] at h1
  rw [Real.cos_zero] at h2
  set c := halfCos θ i
  let O : Set ℂ := ball 0 1 ∩ {w | c < gf (midAngle θ i) w}
  have hO : IsOpen O := isOpen_ball.inter (isOpen_lt continuous_const (continuous_gf _))
  have hsub : O ⊆ lune θ i := fun w hw => ⟨by simpa using (mem_ball_zero_iff.mp hw.1).le, hw.2.le⟩
  refine ⟨((1 + c) / 2 : ℝ) • eC (midAngle θ i), interior_maximal hsub hO ?_⟩
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, norm_eC, mul_one, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  · change c < gf (midAngle θ i) (((1 + c) / 2 : ℝ) • eC (midAngle θ i))
    rw [gf_smul, gf_eC, sub_self, Real.cos_zero]
    linarith

omit A in
theorem same_class {a b m m' : ℤ} (h : a + k * m = b + k * m') (hab : |a - b| < k) : a = b := by
  have hd : k ∣ a - b := ⟨m' - m, by linear_combination h⟩
  have := Int.eq_zero_of_abs_lt_dvd hd hab
  omega

/-- The open part of the polygon: finitely many conditions are enough, by the period. -/
theorem isOpen_core : IsOpen {w : ℂ | ‖w‖ < 1 ∧ ∀ i, gf (midAngle θ i) w < halfCos θ i} := by
  have hk : 0 < k := by have := A.three; omega
  have heq : {w : ℂ | ‖w‖ < 1 ∧ ∀ i, gf (midAngle θ i) w < halfCos θ i} =
      ball 0 1 ∩ ⋂ i ∈ Icc (1 : ℤ) k, {w | gf (midAngle θ i) w < halfCos θ i} := by
    ext w
    simp only [mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff, mem_iInter]
    refine and_congr_right fun _ => ⟨fun h i _ => h i, fun h i => ?_⟩
    obtain ⟨m, h1, h2⟩ := A.exists_shift i 0
    have := h (i + k * m) ⟨by omega, by omega⟩
    rwa [A.midAngle_shift, A.halfCos_shift, gf_period] at this
  rw [heq]
  exact isOpen_ball.inter ((Set.finite_Icc _ _).isOpen_biInter fun i _ => isOpen_lt
    (continuous_gf _) continuous_const)

omit A in
theorem core_subset : {w : ℂ | ‖w‖ < 1 ∧ ∀ i, gf (midAngle θ i) w < halfCos θ i} ⊆ hull θ :=
  fun _ hw => ⟨hw.1.le, fun i => (hw.2 i).le⟩

theorem interior_hull : (interior (hull θ)).Nonempty := by
  have hk := A.three
  let t : ℝ := 1 / 3
  let w : ℂ := t • eC (θ 0) + t • eC (θ 1) + t • eC (θ 2)
  have hgw : ∀ i, gf (midAngle θ i) w = (gf (midAngle θ i) (eC (θ 0)) + gf (midAngle θ i) (eC
    (θ 1)) + gf (midAngle θ i) (eC (θ 2))) / 3 := fun i => by
    simp only [w, gf_add, gf_smul, t]
    ring
  have hlt : ∀ i, gf (midAngle θ i) w < halfCos θ i := fun i => by
    rw [hgw]
    have h0 := A.node_le 0 i
    have h1 := A.node_le 1 i
    have h2 := A.node_le 2 i
    by_contra hn
    have e0 : gf (midAngle θ i) (eC (θ 0)) = halfCos θ i := by linarith
    have e1 : gf (midAngle θ i) (eC (θ 1)) = halfCos θ i := by linarith
    have e2 : gf (midAngle θ i) (eC (θ 2)) = halfCos θ i := by linarith
    obtain ⟨m0, c0⟩ := A.node_eq e0
    obtain ⟨m1, c1⟩ := A.node_eq e1
    obtain ⟨m2, c2⟩ := A.node_eq e2
    have ab : ∀ {a b m m' : ℤ}, 0 ≤ a → a ≤ 2 → 0 ≤ b → b ≤ 2 → a + k * m = b + k * m' → a = b
      := fun ha ha' hb hb' he =>
      IsAngles.same_class (k := k) he (abs_lt.mpr ⟨by omega, by omega⟩)
    rcases c0 with c0 | c0 <;> rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
    · exact absurd (ab (a := 0) (b := 1) (by omega) (by omega) (by omega) (by omega)
      (c0.trans c1.symm)) (by omega)
    · exact absurd (ab (a := 0) (b := 1) (by omega) (by omega) (by omega) (by omega)
      (c0.trans c1.symm)) (by omega)
    · exact absurd (ab (a := 0) (b := 2) (by omega) (by omega) (by omega) (by omega)
      (c0.trans c2.symm)) (by omega)
    · exact absurd (ab (a := 1) (b := 2) (by omega) (by omega) (by omega) (by omega)
      (c1.trans c2.symm)) (by omega)
    · exact absurd (ab (a := 1) (b := 2) (by omega) (by omega) (by omega) (by omega)
      (c1.trans c2.symm)) (by omega)
    · exact absurd (ab (a := 0) (b := 2) (by omega) (by omega) (by omega) (by omega)
      (c0.trans c2.symm)) (by omega)
    · exact absurd (ab (a := 0) (b := 1) (by omega) (by omega) (by omega) (by omega)
      (c0.trans c1.symm)) (by omega)
    · exact absurd (ab (a := 0) (b := 1) (by omega) (by omega) (by omega) (by omega)
      (c0.trans c1.symm)) (by omega)
  have hle : ‖w‖ ≤ 1 := by
    have h := norm_add₃_le (a := t • eC (θ 0)) (b := t • eC (θ 1)) (c := t • eC (θ 2))
    simp only [norm_smul, norm_eC, mul_one, t, Real.norm_eq_abs] at h
    have ht : |(1 : ℝ) / 3| = 1 / 3 := abs_of_pos (by norm_num)
    rw [ht] at h
    calc ‖w‖ ≤ 1 / 3 + 1 / 3 + 1 / 3 := h
      _ = 1 := by norm_num
  have hlt1 : ‖w‖ < 1 := by
    refine lt_of_le_of_ne hle fun he => ?_
    obtain ⟨s, hs⟩ := exists_eC he
    obtain ⟨i, h1, h2⟩ := A.exists_arc s
    have := A.gf_arc h1 h2.le
    rw [← hs] at this
    exact absurd this (not_le.mpr (hlt i))
  exact ⟨w, interior_maximal (IsAngles.core_subset (θ := θ)) A.isOpen_core ⟨hlt1, hlt⟩⟩

theorem seg_notMem_interior_hull {i : ℤ} {w : ℂ} (hw : w ∈ segment ℝ (eC (θ i)) (eC (θ
  (i + 1)))) : w ∉ interior (hull θ) := by
  intro hi
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior w hi
  have h1 : w + (ε / 2 : ℝ) • eC (midAngle θ i) ∈ ball w ε := by
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, norm_eC, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have h2 := (interior_subset (hb h1)).2 i
  rw [gf_add, gf_smul, gf_eC, sub_self, Real.cos_zero] at h2
  have := A.seg_ge i hw
  linarith

theorem seg_notMem_interior_lune {i : ℤ} {w : ℂ} (hw : w ∈ segment ℝ (eC (θ i)) (eC (θ
  (i + 1)))) : w ∉ interior (lune θ i) := by
  intro hi
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior w hi
  have h1 : w + (-(ε / 2) : ℝ) • eC (midAngle θ i) ∈ ball w ε := by
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, norm_eC, mul_one, Real.norm_eq_abs,
      abs_neg, abs_of_pos (by positivity)]
    linarith
  have h2 := (interior_subset (hb h1)).2
  rw [gf_add, gf_smul, gf_eC, sub_self, Real.cos_zero] at h2
  have := A.seg_le i i hw
  linarith

theorem frontier_hull : frontier (hull θ) = ⋃ i, segment ℝ (eC (θ i)) (eC (θ (i + 1))) := by
  rw [frontier, isClosed_hull.closure_eq]
  ext w
  simp only [mem_sdiff, mem_iUnion]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hn
    push Not at hn
    refine h2 (interior_maximal (IsAngles.core_subset (θ := θ)) A.isOpen_core ⟨?_, fun i => ?_⟩)
    · refine lt_of_le_of_ne h1.1 fun he => ?_
      obtain ⟨s, rfl⟩ := exists_eC he
      obtain ⟨i, h3, h4⟩ := A.exists_arc s
      exact hn i (A.chord_eq h1.1 (le_antisymm (h1.2 i) (A.gf_arc h3 h4.le)))
    · exact lt_of_le_of_ne (h1.2 i) fun he => hn i (A.chord_eq h1.1 he)
  · rintro ⟨i, hw⟩
    exact ⟨⟨IsAngles.seg_norm_le (θ := θ) hw, fun j => A.seg_le i j hw⟩, A.seg_notMem_interior_hull
      hw⟩

theorem seg_shift (i m : ℤ) : segment ℝ (eC (θ (i + k * m))) (eC (θ (i + k * m + 1))) = segment ℝ
  (eC (θ i)) (eC (θ (i + 1))) := by
  rw [A.node_shift, show i + k * m + 1 = i + 1 + k * m by ring, A.node_shift]

theorem node_ne {a b : ℤ} (hab : a < b) (hb : b < a + k) : eC (θ a) ≠ eC (θ b) := by
  intro he
  have h1 := A.mono hab
  have h2 := (A.mono hb).trans_eq (A.theta_top a)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Circle.ext he)
  have hpi := Real.pi_pos
  have hm1 : (m : ℝ) < 0 := by
    by_contra hn
    push Not at hn
    nlinarith
  have hm2 : (-1 : ℝ) < m := by
    by_contra hn
    push Not at hn
    nlinarith
  have h3 : m < 0 := by exact_mod_cast hm1
  have h4 : -1 < m := by exact_mod_cast hm2
  omega

theorem isClosedDisc_hull : IsClosedDisc (hull θ) ∧ discBd (hull θ) = ⋃ i, segment ℝ (eC (θ i)) (eC
  (θ (i + 1))) := by
  obtain ⟨h1, h2⟩ := isClosedDisc_of_convex convex_hull' A.interior_hull
    (isBounded_closedBall.subset hull_subset) isClosed_hull
  exact ⟨h1, h2.trans A.frontier_hull⟩

theorem isClosedDisc_lune (i : ℤ) : IsClosedDisc (lune θ i) ∧ segment ℝ (eC (θ i)) (eC (θ
  (i + 1))) ⊆ discBd (lune θ i) := by
  obtain ⟨h1, h2⟩ := isClosedDisc_of_convex (convex_lune i) (A.interior_lune i)
    (isBounded_closedBall.subset (lune_subset i)) (isClosed_lune i)
  refine ⟨h1, fun w hw => ?_⟩
  rw [h2, frontier, (isClosed_lune i).closure_eq]
  exact ⟨⟨IsAngles.seg_norm_le (θ := θ) hw, A.seg_ge i hw⟩, A.seg_notMem_interior_lune hw⟩

end IsAngles

/-- A straight segment is a line. -/
theorem isLineWithEnds_segment {a b : ℂ} (hab : a ≠ b) : IsLineWithEnds (segment ℝ a b) a b := by
  let f : unitInterval → ℂ := fun t => AffineMap.lineMap a b (t : ℝ)
  have hc : Continuous f := by
    apply AffineMap.lineMap_continuous.comp continuous_subtype_val
  have hi : Function.Injective f := fun x y he => by
    have := (AffineMap.lineMap_injective ℝ hab) he
    exact Subtype.ext this
  have hr : range f = segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hem := hc.isClosedEmbedding hi
  refine ⟨hem.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr), ?_, ?_⟩
  · change f 0 = a
    simp [f]
  · change f 1 = b
    simp [f]

/-- The periodic extension of an increasing family of angles. -/
noncomputable def extAngle {k : ℕ} (hk : 0 < k) (s : Fin k → ℝ) (n : ℤ) : ℝ :=
  s ⟨(n % k).toNat, by
    have h1 := Int.emod_nonneg n (show (k : ℤ) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos n (show (0 : ℤ) < k by omega)
    omega⟩ + 2 * Real.pi * ((n / k : ℤ) : ℝ)

theorem extAngle_fin {k : ℕ} (hk : 0 < k) (s : Fin k → ℝ) (i : Fin k) : extAngle hk s (i.1 : ℤ)
  = s i := by
  have h1 : ((i.1 : ℤ) % k) = i.1 := Int.emod_eq_of_lt (by omega) (by omega)
  have h2 : ((i.1 : ℤ) / k) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have : (⟨((i.1 : ℤ) % k).toNat, by rw [h1]; simp⟩ : Fin k) = i := Fin.ext (by simp [h1])
  rw [extAngle]
  simp only [h2, Int.cast_zero, mul_zero, add_zero]
  exact congrArg s this

theorem extAngle_period {k : ℕ} (hk : 0 < k) (s : Fin k → ℝ) (n m : ℤ) :
    extAngle hk s (n + k * m) = extAngle hk s n + 2 * Real.pi * m := by
  have h1 : (n + k * m) % (k : ℤ) = n % k := Int.add_mul_emod_self_left n k m
  have h2 : (n + k * m) / (k : ℤ) = n / k + m := Int.add_mul_ediv_left n m (by omega)
  simp only [extAngle, h1, h2]
  push_cast
  ring

theorem isAngles_extAngle {k : ℕ} (hk : 3 ≤ k) (s : Fin k → ℝ) (hs : StrictMono s)
    (hl : ∀ i, s i < s ⟨0, by omega⟩ + 2 * Real.pi) : IsAngles (extAngle (by omega) s) k := by
  have hk0 : 0 < k := by omega
  have hp := extAngle_period hk0 s
  refine ⟨by exact_mod_cast hk, strictMono_int_of_lt_succ fun n => ?_, hp⟩
  have hr0 := Int.emod_nonneg n (show (k : ℤ) ≠ 0 by omega)
  have hrk := Int.emod_lt_of_pos n (show (0 : ℤ) < k by omega)
  have hn : n = n % k + k * (n / k) := (Int.emod_add_mul_ediv n k).symm
  set r := n % (k : ℤ) with hr
  set q := n / (k : ℤ) with hq
  have e1 : n + 1 = (r + 1) + k * q := by omega
  rw [e1, hn, hp, hp]
  obtain ⟨r', hr'⟩ := Int.eq_ofNat_of_zero_le hr0
  have hr'k : r' < k := by omega
  rw [hr']
  have hb : extAngle hk0 s (r' : ℤ) = s ⟨r', hr'k⟩ := extAngle_fin hk0 s ⟨r', hr'k⟩
  by_cases hc : r' + 1 < k
  · have hb' : extAngle hk0 s ((r' : ℤ) + 1) = s ⟨r' + 1, hc⟩ := by
      have := extAngle_fin hk0 s ⟨r' + 1, hc⟩
      simpa using this
    rw [hb, hb']
    have := hs (show (⟨r', hr'k⟩ : Fin k) < ⟨r' + 1, hc⟩ by simp [Fin.lt_def])
    linarith
  · have hrk' : (r' : ℤ) + 1 = 0 + k * 1 := by omega
    rw [hrk', hp, hb]
    have h0 := extAngle_fin hk0 s ⟨0, hk0⟩
    simp only [Nat.cast_zero] at h0
    rw [h0]
    have := hl ⟨r', hr'k⟩
    push_cast
    linarith

/-- **The polygon and the lunes.** For at least three points of the unit circle, in order, the
closed unit disc splits into the polygon on the
points and one lune for each side. Each lune is a closed disc that meets the polygon in its side,
and two lunes meet only in the given points. -/
theorem exists_polygon_lunes {k : ℕ} (hk : 3 ≤ k) (s : Fin k → ℝ) (hs : StrictMono s)
  (hl : ∀ i, s i < s ⟨0, by omega⟩ + 2 * Real.pi)
    (nx : Fin k → Fin k) (hnx : ∀ i, (nx i).1 = (i.1 + 1) % k) :
    ∃ (P : Set ℂ) (L F : Fin k → Set ℂ), IsClosedDisc P ∧ P ⊆ closedBall 0 1 ∧ discBd P = ⋃ i, F i ∧
      closedBall 0 1 = P ∪ ⋃ i, L i ∧
      (∀ i, IsClosedDisc (L i) ∧ L i ⊆ closedBall 0 1 ∧ L i ∩ P = F i ∧ F i ⊆ discBd (L i) ∧
        IsLineWithEnds (F i) (eC (s i)) (eC (s (nx i)))) ∧
      (∀ i j, i ≠ j → L i ∩ L j ⊆ range fun i => eC (s i)) ∧
      ∀ i j, eC (s j) ∈ L i ↔ j = i ∨ j = nx i := by
  have hk0 : 0 < k := by omega
  have A := isAngles_extAngle hk s hs hl
  set θ := extAngle hk0 s with hθ
  have hfin : ∀ i : Fin k, θ i.1 = s i := extAngle_fin hk0 s
  have hnode : ∀ i : Fin k, eC (θ (i.1 + 1)) = eC (s (nx i)) := fun i => by
    have hnx' : ((nx i).1 : ℤ) + k * ((i.1 + 1) / k : ℕ) = i.1 + 1 := by
      rw [hnx]
      have := Nat.mod_add_div (i.1 + 1) k
      exact_mod_cast this
    rw [← hnx', A.node_shift, hfin]
  have hcov : ∀ i : ℤ, ∃ (j : Fin k) (m : ℤ), i + k * m = j.1 := fun i => by
    obtain ⟨m, h1, h2⟩ := A.exists_shift i (-1)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ i + k * m by omega)
    exact ⟨⟨j, by omega⟩, m, hj⟩
  have hne : ∀ {i j : Fin k}, i ≠ j → ∀ m : ℤ, (j.1 : ℤ) + k * m ≠ i.1 + k := fun {i j} hij m he
    => by
    have : (j.1 : ℤ) = i.1 := IsAngles.same_class (k := k) (m := m) (m' := 1) (by rw [he, mul_one])
      (abs_lt.mpr ⟨by omega, by omega⟩)
    exact hij (Fin.ext (by omega)).symm
  refine ⟨hull θ, fun i => lune θ i.1, fun i => segment ℝ (eC (s i)) (eC (s
    (nx i))), A.isClosedDisc_hull.1, IsAngles.hull_subset, ?_, ?_, fun i => ?_, fun i j hij
      => ?_, fun i j => ?_⟩
  · rw [A.isClosedDisc_hull.2]
    ext w
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hw⟩
      obtain ⟨j, m, hjm⟩ := hcov i
      refine ⟨j, ?_⟩
      rw [← A.seg_shift i m, hjm, hnode, hfin] at hw
      exact hw
    · rintro ⟨i, hw⟩
      refine ⟨i.1, ?_⟩
      rw [hnode, hfin]
      exact hw
  · apply subset_antisymm
    · intro w hw
      have hw1 : ‖w‖ ≤ 1 := by simpa using hw
      by_cases h : ∀ i, gf (midAngle θ i) w ≤ halfCos θ i
      · exact Or.inl ⟨hw1, h⟩
      · push Not at h
        obtain ⟨i, hi⟩ := h
        obtain ⟨j, m, hjm⟩ := hcov i
        refine Or.inr (mem_iUnion.2 ⟨j, ?_⟩)
        show w ∈ lune θ j.1
        rw [← hjm, A.lune_shift]
        exact ⟨hw1, hi.le⟩
    · exact union_subset IsAngles.hull_subset (iUnion_subset fun i => IsAngles.lune_subset _)
  · have hseg := A.lune_inter_hull i.1
    rw [hnode, hfin] at hseg
    have hd := A.isClosedDisc_lune i.1
    rw [hnode, hfin] at hd
    refine ⟨hd.1, IsAngles.lune_subset _, hseg, hd.2, isLineWithEnds_segment ?_⟩
    rw [← hnode, ← hfin]
    exact A.node_ne (by omega) (by have := A.three; omega)
  · rintro w ⟨hi, hj⟩
    have h1 : gf (midAngle θ i.1) w = halfCos θ i.1 := le_antisymm (A.lune_le (hne hij) hj) hi.2
    have h2 : gf (midAngle θ j.1) w = halfCos θ j.1 := le_antisymm (A.lune_le
      (hne hij.symm) hi) hj.2
    have hseg := A.chord_eq hi.1 h1
    rcases gf_segment_eq (A.node_le i.1 j.1) (A.node_le (i.1 + 1) j.1) hseg h2 with rfl | rfl |
      ⟨e1, e2⟩
    · exact ⟨i, by simp only [← hfin i]⟩
    · exact ⟨nx i, by simp only [← hfin (nx i), hnode i]⟩
    · exfalso
      obtain ⟨m₁, c₁⟩ := A.node_eq e1
      obtain ⟨m₂, c₂⟩ := A.node_eq e2
      have hk' := A.three
      have hij' : (i.1 : ℤ) ≠ j.1 := fun h => hij (Fin.ext (by omega))
      have hcl : ∀ m m' : ℤ, (i.1 : ℤ) + k * m ≠ j.1 + k * m' := fun m m' he =>
        hij' (IsAngles.same_class (k := k) he (abs_lt.mpr ⟨by omega, by omega⟩))
      rcases c₁ with c₁ | c₁ <;> rcases c₂ with c₂ | c₂
      · exact hcl m₂ 0 (by linarith)
      · have hd : (k : ℤ) ∣ 2 := ⟨1 + m₁ - m₂, by linear_combination c₂ - c₁⟩
        have := Int.le_of_dvd (by norm_num) hd
        omega
      · exact hcl m₁ 1 (by linarith)
      · exact hcl m₁ 1 (by linarith)
  · constructor
    · intro hm
      have h1 : gf (midAngle θ i.1) (eC (s j)) = halfCos θ i.1 := by
        rw [← hfin j]
        exact le_antisymm (A.node_le _ _) (hfin j ▸ hm.2)
      rw [← hfin j] at h1
      obtain ⟨m, c⟩ := A.node_eq h1
      have hk' := A.three
      rcases c with c | c
      · right
        apply Fin.ext
        rw [hnx]
        have h2 : ((j.1 : ℤ) + k * m) % k = j.1 % k := Int.add_mul_emod_self_left _ _ _
        rw [c] at h2
        have h3 : (j.1 : ℤ) % k = j.1 := Int.emod_eq_of_lt (by omega) (by omega)
        rw [h3] at h2
        have : ((i.1 + 1 : ℕ) : ℤ) % k = ((j.1 : ℕ) : ℤ) := by push_cast; exact h2
        exact_mod_cast this.symm
      · left
        have : (j.1 : ℤ) = i.1 := IsAngles.same_class (k := k) (m := m) (m' := 1)
          (by rw [c, mul_one]) (abs_lt.mpr ⟨by omega, by omega⟩)
        exact Fin.ext (by omega)
    · rintro (rfl | rfl)
      · refine ⟨by rw [norm_eC], ?_⟩
        rw [← hfin j]
        exact A.gf_arc le_rfl (A.mono (by omega)).le
      · refine ⟨by rw [norm_eC], ?_⟩
        rw [← hnode i]
        exact A.gf_arc (A.mono (by omega)).le le_rfl

end GraphMinor.Surface
