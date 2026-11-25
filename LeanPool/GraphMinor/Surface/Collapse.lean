/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ArcDisc

/-!
# Collapsing an arc

An arc of a closed surface can be collapsed to a point by a map of the surface to itself that is
homotopic to the identity (`exists_collapse`). The map is injective off the arc and onto. This is
the fact "`Σ' ≅ Σ`" in the proof of Graph Minors XIX, (6.3) (page 340), for one edge.

By `exists_disc_of_arc` and the strip coordinates of `exists_stripChart`, it is enough to collapse a
segment of the real axis in the closed unit ball, by a map that is the identity on the unit circle.
For this we use the Joukowski map. Let `a > 1`. On the annulus `1 ≤ ‖w‖ ≤ R`, the map `j` sends `w =
t u` to `(w + 1 / w) / 2` with its real part divided by `a` and its imaginary part by `b`, where `a`
and `b` are the half axes of the ellipse that is the image of `‖w‖ = R`. It maps onto the unit ball,
it is injective off the circle `‖w‖ = 1`, and it folds this circle onto a segment. The map `w ↦ (t -
1) / (R - 1) u` maps onto the unit ball too, and it sends this circle to `0`. So it factors through
`j`, and this gives the collapse (`exists_ball_collapse`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter Complex

local notation "𝕀" => unitInterval

/-- Facts on the half axes at radius `t ≥ 1`. -/
theorem half_axes {t R : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ R) : t + t⁻¹ ≤ R + R⁻¹ ∧ t - t⁻¹ ≤ R - R⁻¹ := by
  have ht : 0 < t := by linarith
  have hR : 0 < R := by linarith
  have h3 : R⁻¹ ≤ t⁻¹ := inv_anti₀ ht h2
  refine ⟨?_, by linarith⟩
  have h4 : t⁻¹ - R⁻¹ = (R - t) / (t * R) := by field_simp
  have h5 : (R - t) / (t * R) ≤ R - t := div_le_self (by linarith) (by nlinarith)
  linarith

theorem jou_re {w : ℂ} (hw : w ≠ 0) : (jou w).re = (‖w‖ + ‖w‖⁻¹) / 2 * (w.re / ‖w‖) := by
  have ht : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have h2 : normSq w = ‖w‖ ^ 2 := normSq_eq_norm_sq w
  simp only [jou, div_ofNat_re, add_re, inv_re, h2]
  field_simp

theorem jou_im {w : ℂ} (hw : w ≠ 0) : (jou w).im = (‖w‖ - ‖w‖⁻¹) / 2 * (w.im / ‖w‖) := by
  have ht : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have h2 : normSq w = ‖w‖ ^ 2 := normSq_eq_norm_sq w
  simp only [jou, div_ofNat_im, add_im, inv_im, h2]
  field_simp
  ring

theorem jou_fibre {w w' : ℂ} (hw : w ≠ 0) (hw' : w' ≠ 0) (h : jou w = jou w') : w = w' ∨ w * w' = 1
  := by
  have h1 : (w - w') * (w * w' - 1) = 0 := by
    simp only [jou] at h
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact .inl (sub_eq_zero.mp h2)
  · exact .inr (sub_eq_zero.mp h2)

theorem exists_jou_root (ζ : ℂ) : ∃ w, 1 ≤ ‖w‖ ∧ jou w = ζ := by
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d ^ 2 = ζ ^ 2 - 1 := ⟨_, Complex.cpow_nat_inv_pow _ two_ne_zero⟩
  have hp : (ζ + d) * (ζ - d) = 1 := by linear_combination -hd
  have h1 : ζ + d ≠ 0 := left_ne_zero_of_mul_eq_one hp
  have h2 : ζ - d ≠ 0 := right_ne_zero_of_mul_eq_one hp
  have hinv1 : (ζ + d)⁻¹ = ζ - d := inv_eq_of_mul_eq_one_right hp
  have hinv2 : (ζ - d)⁻¹ = ζ + d := inv_eq_of_mul_eq_one_left hp
  by_cases hn : 1 ≤ ‖ζ + d‖
  · exact ⟨ζ + d, hn, by rw [jou, hinv1]; ring⟩
  · refine ⟨ζ - d, ?_, by rw [jou, hinv2]; ring⟩
    have h3 : ‖ζ + d‖ * ‖ζ - d‖ = 1 := by rw [← norm_mul, hp, norm_one]
    have h4 : 0 < ‖ζ + d‖ := norm_pos_iff.mpr h1
    by_contra! hbad
    have hlt := mul_lt_mul_of_pos_left hbad h4
    rw [h3, mul_one] at hlt
    exact hn hlt.le

private theorem scaledJoukowski_mapsTo_ball {a b R : ℝ} {j : ℂ → ℂ}
    (ha0 : 0 < a) (hbpos : 0 < b)
    (haR : (R + R⁻¹) / 2 = a) (hbR : (R - R⁻¹) / 2 = b)
    (hjre : ∀ w : ℂ, w ≠ 0 →
      (j w).re = (‖w‖ + ‖w‖⁻¹) / 2 * (w.re / ‖w‖) / a)
    (hjim : ∀ w : ℂ, w ≠ 0 →
      (j w).im = (‖w‖ - ‖w‖⁻¹) / 2 * (w.im / ‖w‖) / b)
    (hunit : ∀ w : ℂ, w ≠ 0 → (w.re / ‖w‖) ^ 2 + (w.im / ‖w‖) ^ 2 = 1) :
    ∀ w : ℂ, (1 ≤ ‖w‖ ∧ ‖w‖ ≤ R) → j w ∈ closedBall (0 : ℂ) 1 := by
  intro w hw
  have h0 : w ≠ 0 := by
    intro h
    exact (not_le_of_gt zero_lt_one) (by simpa [h] using hw.1)
  obtain ⟨h1, h2⟩ := half_axes hw.1 hw.2
  have hu := hunit w h0
  set p := (‖w‖ + ‖w‖⁻¹) / 2 with hp
  set q := (‖w‖ - ‖w‖⁻¹) / 2 with hq
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by
    have : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hw.1
    simp only [hq]
    linarith [hw.1]
  have hpa : p / a ≤ 1 := (div_le_one ha0).mpr (by rw [← haR]; linarith)
  have hqb : q / b ≤ 1 := (div_le_one hbpos).mpr (by rw [← hbR]; linarith)
  rw [mem_closedBall_zero_iff]
  have h3 : ‖j w‖ ^ 2 ≤ 1 := by
    rw [← normSq_eq_norm_sq, normSq_apply, hjre w h0, hjim w h0]
    set c' := w.re / ‖w‖
    set s' := w.im / ‖w‖
    have h4 : p * c' / a = p / a * c' := by ring
    have h5 : q * s' / b = q / b * s' := by ring
    rw [h4, h5]
    have h6 : (p / a) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hpa
    have h7 : (q / b) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hqb
    have hcs : c' ^ 2 + s' ^ 2 = 1 := hu
    have hc := mul_le_of_le_one_left (sq_nonneg c') h6
    have hs := mul_le_of_le_one_left (sq_nonneg s') h7
    nlinarith only [hc, hs, hcs]
  nlinarith [norm_nonneg (j w)]

private theorem scaledJoukowski_surjOn_ball {a b R : ℝ} (hR0 : 0 < R)
    (ha0 : 0 < a) (hbpos : 0 < b)
    (haR : (R + R⁻¹) / 2 = a) (hbR : (R - R⁻¹) / 2 = b)
    (hunit : ∀ w : ℂ, w ≠ 0 → (w.re / ‖w‖) ^ 2 + (w.im / ‖w‖) ^ 2 = 1) :
    let A : Set ℂ := {w | 1 ≤ ‖w‖ ∧ ‖w‖ ≤ R}
    let j : ℂ → ℂ := fun w => ((jou w).re / a : ℝ) + ((jou w).im / b : ℝ) * I
    ∀ z ∈ closedBall (0 : ℂ) 1, ∃ w ∈ A, j w = z := by
  intro A j
  have hjre : ∀ w : ℂ, w ≠ 0 →
      (j w).re = (‖w‖ + ‖w‖⁻¹) / 2 * (w.re / ‖w‖) / a := fun w hw => by
    simp [j, jou_re hw]
  have hjim : ∀ w : ℂ, w ≠ 0 →
      (j w).im = (‖w‖ - ‖w‖⁻¹) / 2 * (w.im / ‖w‖) / b := fun w hw => by
    simp [j, jou_im hw]
  intro z hz
  obtain ⟨w, hw1, hw2⟩ := exists_jou_root ((a * z.re : ℝ) + (b * z.im : ℝ) * I)
  have h0 : w ≠ 0 := fun h => by
    simp [h] at hw1
    linarith
  have hjz : j w = z := by
    apply Complex.ext
    · simp [j, hw2, ha0.ne']
    · simp [j, hw2, hbpos.ne']
  refine ⟨w, ⟨hw1, ?_⟩, hjz⟩
  by_contra hc
  push Not at hc
  have hu := hunit w h0
  have h3 : ‖z‖ ^ 2 ≤ 1 := by
    have := mem_closedBall_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  rw [← normSq_eq_norm_sq, normSq_apply, ← hjz, hjre w h0, hjim w h0] at h3
  have ht0 : 0 < ‖w‖ := by linarith
  have hin : ‖w‖⁻¹ < R⁻¹ := inv_strictAnti₀ hR0 hc
  have hin2 : ‖w‖ - ‖w‖⁻¹ > R - R⁻¹ := by linarith
  have hin3 : ‖w‖ + ‖w‖⁻¹ > R + R⁻¹ := by
    have h4 : ‖w‖⁻¹ * ‖w‖ = 1 := inv_mul_cancel₀ ht0.ne'
    have h5 : R⁻¹ * R = 1 := inv_mul_cancel₀ hR0.ne'
    have h6 : 0 < ‖w‖⁻¹ := by positivity
    have h7 : 0 < R⁻¹ := by positivity
    nlinarith
  set p := (‖w‖ + ‖w‖⁻¹) / 2 with hp
  set q := (‖w‖ - ‖w‖⁻¹) / 2 with hq
  have hpa : 1 < p / a := (one_lt_div ha0).mpr (by rw [← haR]; linarith)
  have hqb : 1 < q / b := (one_lt_div hbpos).mpr (by rw [← hbR]; linarith)
  set c' := w.re / ‖w‖
  set s' := w.im / ‖w‖
  have h4 : p * c' / a = p / a * c' := by ring
  have h5 : q * s' / b = q / b * s' := by ring
  rw [h4, h5] at h3
  have h6 : 1 < (p / a) ^ 2 := one_lt_pow₀ hpa (by norm_num)
  have h7 : 1 < (q / b) ^ 2 := one_lt_pow₀ hqb (by norm_num)
  have h8 : c' ^ 2 ≤ (p / a) ^ 2 * c' ^ 2 := le_mul_of_one_le_left (sq_nonneg _) h6.le
  have h9 : s' ^ 2 ≤ (q / b) ^ 2 * s' ^ 2 := le_mul_of_one_le_left (sq_nonneg _) h7.le
  have h10 : (p / a * c') * (p / a * c') + (q / b * s') * (q / b * s') = (p / a) ^ 2 * c' ^ 2 +
    (q / b) ^ 2 * s' ^ 2 := by ring
  rw [h10] at h3
  have hcs : c' ^ 2 + s' ^ 2 = 1 := hu
  have hc : c' ^ 2 = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (sq_nonneg c') (Ne.symm hne)
    have hlt := mul_lt_mul_of_pos_right h6 hpos
    linarith only [hlt, h9, h3, hcs]
  have hs : s' ^ 2 = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (sq_nonneg s') (Ne.symm hne)
    have hlt := mul_lt_mul_of_pos_right h7 hpos
    linarith only [hlt, h8, h3, hcs]
  linarith only [hc, hs, hcs]

private theorem norm_eq_one_of_jou_eq {w w' : ℂ} (hw : 1 ≤ ‖w‖) (hw' : 1 ≤ ‖w'‖)
    (he : jou w = jou w') : w = w' ∨ ‖w‖ = 1 ∧ ‖w'‖ = 1 := by
  have h0 : w ≠ 0 := by
    intro h
    exact (not_le_of_gt zero_lt_one) (by simpa [h] using hw)
  have h0' : w' ≠ 0 := by
    intro h
    exact (not_le_of_gt zero_lt_one) (by simpa [h] using hw')
  rcases jou_fibre h0 h0' he with h | h
  · exact Or.inl h
  · have hmul : ‖w‖ * ‖w'‖ = 1 := by rw [← norm_mul, h, norm_one]
    have heq : ‖w‖ = 1 := le_antisymm (by
      have hle := le_mul_of_one_le_right (norm_nonneg w) hw'
      rwa [hmul] at hle) hw
    have heq' : ‖w'‖ = 1 := by rwa [heq, one_mul] at hmul
    exact Or.inr ⟨heq, heq'⟩

private theorem continuousOn_of_compact_surjOn {A B : Set ℂ} {j κ c : ℂ → ℂ}
    (hAc : IsCompact A) (hjc : ContinuousOn j A) (hκc : ContinuousOn κ A)
    (hjsurj : ∀ z ∈ B, ∃ w ∈ A, j w = z) (hcj : ∀ w ∈ A, c (j w) = κ w) :
    ContinuousOn c B := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  have h1 : IsCompact (A ∩ κ ⁻¹' C) :=
    hAc.of_isClosed_subset (hκc.preimage_isClosed_of_isClosed hAc.isClosed hC) inter_subset_left
  refine ⟨j '' (A ∩ κ ⁻¹' C), (h1.image_of_continuousOn (hjc.mono inter_subset_left)).isClosed, ?_⟩
  ext z
  constructor
  · rintro ⟨h2, h3⟩
    obtain ⟨w, hw, rfl⟩ := hjsurj z h3
    refine ⟨⟨w, ⟨hw, ?_⟩, rfl⟩, h3⟩
    change κ w ∈ C
    rw [← hcj w hw]
    exact h2
  · rintro ⟨⟨w, ⟨hw, h2⟩, rfl⟩, h3⟩
    refine ⟨?_, h3⟩
    change c (j w) ∈ C
    rw [hcj w hw]
    exact h2

private theorem scaledJoukowski_radius_eq_one {a b : ℝ} (ha0 : 0 < a) (hbpos : 0 < b)
    {w z : ℂ} (hw : 1 ≤ ‖w‖)
    (hu : (w.re / ‖w‖) ^ 2 + (w.im / ‖w‖) ^ 2 = 1)
    (hjre : z.re = (‖w‖ + ‖w‖⁻¹) / 2 * (w.re / ‖w‖) / a)
    (hjim : z.im = (‖w‖ - ‖w‖⁻¹) / 2 * (w.im / ‖w‖) / b) :
    ‖w‖ = 1 ↔ z.im = 0 ∧ |z.re| ≤ a⁻¹ := by
  have hw1 : 0 < ‖w‖ := by linarith [hw]
  constructor
  · intro h
    constructor
    · rw [hjim, h]
      simp
    · have h3 : |w.re| ≤ 1 := by
        have := Complex.abs_re_le_norm w
        rwa [h] at this
      have h4 : (1 + (1 : ℝ)⁻¹) / 2 * (w.re / 1) / a = w.re / a := by norm_num
      rw [hjre, h, h4, abs_div, abs_of_pos ha0, div_eq_mul_inv]
      simpa using mul_le_mul_of_nonneg_right h3 (inv_pos.mpr ha0).le
  · rintro ⟨h1, h2⟩
    by_contra hc
    have hgt : 1 < ‖w‖ := lt_of_le_of_ne hw (Ne.symm hc)
    have hin : ‖w‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
    have hq : 0 < (‖w‖ - ‖w‖⁻¹) / 2 := by linarith
    have hp : 1 < (‖w‖ + ‖w‖⁻¹) / 2 := by
      have h4 : ‖w‖⁻¹ * ‖w‖ = 1 := inv_mul_cancel₀ hw1.ne'
      have h5 : 0 < ‖w‖⁻¹ := by positivity
      nlinarith
    rw [hjim] at h1
    have hs : w.im / ‖w‖ = 0 := by
      have h3 := div_eq_zero_iff.mp h1
      rcases h3 with h3 | h3
      · exact (mul_eq_zero.mp h3).resolve_left hq.ne'
      · exact absurd h3 hbpos.ne'
    rw [hs] at hu
    have hc2 : (w.re / ‖w‖) ^ 2 = 1 := by linarith
    have hc3 : |w.re / ‖w‖| = 1 := by
      rw [← sq_eq_sq₀ (abs_nonneg _) zero_le_one, sq_abs, hc2]
      norm_num
    rw [hjre, abs_div, abs_mul, hc3, mul_one, abs_of_pos ha0, abs_of_pos
      (by linarith), div_le_iff₀ ha0, inv_mul_cancel₀ ha0.ne'] at h2
    linarith

/-- The model collapse. In the closed unit ball, the segment of the real axis with `|x| ≤ 1 / a`
goes to `0`, and the map is the identity on the unit circle. -/
theorem exists_ball_collapse {a : ℝ} (ha : 1 < a) :
    ∃ c : ℂ → ℂ, ContinuousOn c (closedBall 0 1) ∧ MapsTo c (closedBall 0 1) (closedBall 0 1) ∧
      (∀ z ∈ sphere (0 : ℂ) 1, c z = z) ∧ (∀ z ∈ closedBall (0 : ℂ) 1, c z = 0 ↔ z.im = 0 ∧ |z.re|
        ≤ a⁻¹) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ∀ z' ∈ closedBall (0 : ℂ) 1, c z ≠ 0 → c z = c z' → z = z') ∧
      ∀ v ∈ closedBall (0 : ℂ) 1, ∃ z ∈ closedBall (0 : ℂ) 1, c z = v := by
  classical
  set b := Real.sqrt (a ^ 2 - 1) with hb
  have hb2 : b ^ 2 = a ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by nlinarith)
  have ha0 : 0 < a := by linarith
  set R := a + b with hR
  have hR1 : 1 < R := by linarith
  have hR0 : 0 < R := by linarith
  have hRinv : R⁻¹ = a - b := inv_eq_of_mul_eq_one_right (by rw [hR]; linear_combination hb2 *
    (-1 : ℝ))
  have haR : (R + R⁻¹) / 2 = a := by rw [hRinv, hR]; ring
  have hbR : (R - R⁻¹) / 2 = b := by rw [hRinv, hR]; ring
  let A : Set ℂ := {w | 1 ≤ ‖w‖ ∧ ‖w‖ ≤ R}
  have hAc : IsCompact A := by
    have h1 : A = closedBall 0 R ∩ {w | 1 ≤ ‖w‖} := by
      ext w
      simp [A, and_comm]
    rw [h1]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hA0 : ∀ w ∈ A, w ≠ 0 := fun w hw h => by
    have := hw.1
    simp [h] at this
    linarith
  let j : ℂ → ℂ := fun w => ((jou w).re / a : ℝ) + ((jou w).im / b : ℝ) * I
  let κ : ℂ → ℂ := fun w => ((‖w‖ - 1) / (R - 1) : ℝ) * (w / ‖w‖)
  have hR1' : 0 < R - 1 := by linarith
  have hjc : ContinuousOn j A := by
    have h1 : ContinuousOn jou A := by
      exact ContinuousOn.div_const (continuousOn_id.add (continuousOn_id.inv₀ hA0)) _
    have h2 : ContinuousOn (fun w => (jou w).re) A := continuous_re.comp_continuousOn h1
    have h3 : ContinuousOn (fun w => (jou w).im) A := continuous_im.comp_continuousOn h1
    exact (continuous_ofReal.comp_continuousOn (h2.div_const _)).add
      ((continuous_ofReal.comp_continuousOn (h3.div_const _)).mul continuousOn_const)
  have hκc : ContinuousOn κ A := by
    have h1 : ContinuousOn (fun w : ℂ => ((‖w‖ : ℝ) : ℂ)) A := continuous_ofReal.comp_continuousOn
      continuous_norm.continuousOn
    have h2 : ContinuousOn (fun w : ℂ => w / ((‖w‖ : ℝ) : ℂ)) A := continuousOn_id.div h1 fun w hw
      => by
      exact_mod_cast norm_ne_zero_iff.mpr (hA0 w hw)
    refine ContinuousOn.mul ?_ h2
    exact continuous_ofReal.comp_continuousOn ((continuous_norm.continuousOn.sub
      continuousOn_const).div_const _)
  have hunit : ∀ w : ℂ, w ≠ 0 → (w.re / ‖w‖) ^ 2 + (w.im / ‖w‖) ^ 2 = 1 := fun w hw => by
    have ht : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have h2 : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]
      ring
    field_simp
    linarith
  have hjre : ∀ w : ℂ, w ≠ 0 → (j w).re = (‖w‖ + ‖w‖⁻¹) / 2 * (w.re / ‖w‖) / a := fun w hw => by
    simp [j, jou_re hw]
  have hjim : ∀ w : ℂ, w ≠ 0 → (j w).im = (‖w‖ - ‖w‖⁻¹) / 2 * (w.im / ‖w‖) / b := fun w hw => by
    simp [j, jou_im hw]
  have hjnorm : ∀ w ∈ A, j w ∈ closedBall (0 : ℂ) 1 :=
    scaledJoukowski_mapsTo_ball ha0 hbpos haR hbR hjre hjim hunit
  have hjsurj : ∀ z ∈ closedBall (0 : ℂ) 1, ∃ w ∈ A, j w = z :=
    scaledJoukowski_surjOn_ball hR0 ha0 hbpos haR hbR hunit
  have hκnorm : ∀ w ∈ A, ‖κ w‖ = (‖w‖ - 1) / (R - 1) := by
    intro w hw
    have h0 := hA0 w hw
    have ht : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have h1 : 0 ≤ (‖w‖ - 1) / (R - 1) := div_nonneg (by linarith [hw.1]) hR1'.le
    simp only [κ]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1, norm_div, Complex.norm_real,
      norm_norm, div_self ht, mul_one]
  have hκ1 : ∀ w ∈ A, κ w = 0 ↔ ‖w‖ = 1 := by
    intro w hw
    rw [← norm_eq_zero, hκnorm w hw, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h
      exact .inl (by linarith)
  have hfib : ∀ w ∈ A, ∀ w' ∈ A, j w = j w' → κ w = κ w' := by
    intro w hw w' hw' h
    have hjj : jou w = jou w' := by
      apply Complex.ext
      · have := congrArg Complex.re h
        simp only [j, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero] at this
        exact (div_left_inj₀ ha0.ne').mp this
      · have := congrArg Complex.im h
        simp only [j, add_im, ofReal_im, mul_im, I_re, mul_zero, ofReal_re, I_im, mul_one,
          zero_add, add_zero] at this
        exact (div_left_inj₀ hbpos.ne').mp this
    rcases norm_eq_one_of_jou_eq hw.1 hw'.1 hjj with rfl | ⟨he, he'⟩
    · rfl
    · rw [(hκ1 w hw).mpr he, (hκ1 w' hw').mpr he']
  let c : ℂ → ℂ := fun z => if h : ∃ w ∈ A, j w = z then κ h.choose else 0
  have hcj : ∀ w ∈ A, c (j w) = κ w := by
    intro w hw
    have h : ∃ w' ∈ A, j w' = j w := ⟨w, hw, rfl⟩
    simp only [c, dite_eq_left h]
    exact hfib _ h.choose_spec.1 w hw h.choose_spec.2
  have hAsub : ∀ w ∈ A, κ w ∈ closedBall (0 : ℂ) 1 := fun w hw => by
    rw [mem_closedBall_zero_iff, hκnorm w hw, div_le_one hR1']
    linarith [hw.2]
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_of_compact_surjOn hAc hjc hκc hjsurj hcj
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hjsurj z hz
    rw [hcj w hw]
    exact hAsub w hw
  · intro z hz
    have hzn : ‖z‖ = 1 := by simpa using hz
    have h0 : z ≠ 0 := fun h => by simp [h] at hzn
    have hRn : ‖(R : ℂ) * z‖ = R := by
      rw [norm_mul, hzn, mul_one, Complex.norm_real, Real.norm_of_nonneg hR0.le]
    have hwA : (R : ℂ) * z ∈ A := ⟨by rw [hRn]; exact hR1.le, by rw [hRn]⟩
    have hw0 := hA0 _ hwA
    have h1 : j ((R : ℂ) * z) = z := by
      apply Complex.ext
      · rw [hjre _ hw0, hRn, haR]
        simp [hR0.ne', ha0.ne']
      · rw [hjim _ hw0, hRn, hbR]
        simp [hR0.ne', hbpos.ne']
    rw [← h1, hcj _ hwA]
    simp only [h1, κ, hRn]
    rw [div_self hR1'.ne']
    simp only [ofReal_one, one_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hR0.ne')
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hjsurj z hz
    rw [hcj w hw, hκ1 w hw]
    have h0 := hA0 w hw
    exact scaledJoukowski_radius_eq_one ha0 hbpos hw.1 (hunit w h0)
      (hjre w h0) (hjim w h0)
  · intro z hz z' hz' hne he
    obtain ⟨w, hw, rfl⟩ := hjsurj z hz
    obtain ⟨w', hw', rfl⟩ := hjsurj z' hz'
    rw [hcj w hw] at hne
    rw [hcj w hw, hcj w' hw'] at he
    have h1 : ‖w‖ = ‖w'‖ := by
      have := congrArg norm he
      rw [hκnorm w hw, hκnorm w' hw', div_left_inj₀ hR1'.ne'] at this
      linarith
    have h2 : ((‖w‖ - 1) / (R - 1) : ℝ) ≠ 0 := by
      intro h3
      apply hne
      simp only [κ]
      rw [h3]
      simp
    have ht : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (hA0 w hw)
    simp only [κ, ← h1] at he
    have h3 := mul_left_cancel₀ (by exact_mod_cast h2) he
    rw [div_left_inj₀ ht] at h3
    rw [h3]
  · intro v hv
    have hvn : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
    by_cases h0 : v = 0
    · have h1A : (1 : ℂ) ∈ A := ⟨by rw [norm_one], by rw [norm_one]; exact hR1.le⟩
      refine ⟨j 1, hjnorm 1 h1A, ?_⟩
      rw [hcj 1 h1A, h0]
      exact (hκ1 1 h1A).mpr norm_one
    · have hvn0 : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr h0
      set t := 1 + ‖v‖ * (R - 1) with ht
      have ht1 : 1 ≤ t := by nlinarith
      have htR : t ≤ R := by nlinarith
      have ht0 : 0 < t := by linarith
      set w : ℂ := (t : ℂ) * (v / ‖v‖) with hw
      have hwn : ‖w‖ = t := by
        rw [hw, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg
          ht0.le, norm_norm, div_self hvn0.ne', mul_one]
      have hwA : w ∈ A := ⟨by rw [hwn]; exact ht1, by rw [hwn]; exact htR⟩
      refine ⟨j w, hjnorm w hwA, ?_⟩
      rw [hcj w hwA]
      simp only [κ, hwn]
      have h1 : (t - 1) / (R - 1) = ‖v‖ := by
        rw [ht]
        field_simp
        ring
      rw [h1, hw]
      have h2 : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvn0.ne'
      have h3 : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      field_simp

/-- The map `z ↦ m + p x + i q y` of the plane. -/
noncomputable def axisStretch (m p q : ℝ) (hp : 0 < p) (hq : 0 < q) : ℂ ≃ₜ ℂ where
  toFun z := ((m + p * z.re : ℝ) : ℂ) + ((q * z.im : ℝ) : ℂ) * I
  invFun w := (((w.re - m) / p : ℝ) : ℂ) + ((w.im / q : ℝ) : ℂ) * I
  left_inv z := by
    apply Complex.ext
    · simp
      field_simp
    · simp
      field_simp
  right_inv w := by
    apply Complex.ext
    · simp
      field_simp
      ring
    · simp
      field_simp
  continuous_toFun := by
    refine (continuous_ofReal.comp (by fun_prop)).add ((continuous_ofReal.comp
      (by fun_prop)).mul continuous_const)
  continuous_invFun := by
    refine (continuous_ofReal.comp (by fun_prop)).add ((continuous_ofReal.comp
      (by fun_prop)).mul continuous_const)

variable {T : Type} [TopologicalSpace T]

/-- An axis stretch of the unit disc lies in a thickening of its real-axis segment. -/
theorem stretch_mapsTo_cthickening {O : Set ℂ} {A : ℂ → ℂ}
    {α β m ℓ η a₀ : ℝ} (hαβ : α < β) (hm : m = (α + β) / 2) (hℓ : ℓ = (β - α) / 2)
    (hp : 0 < ℓ * a₀) (hq : 0 < η / 2) (hscale : ℓ * a₀ = ℓ + η / 2)
    (hAre : ∀ z, (A z).re = m + ℓ * a₀ * z.re) (hAim : ∀ z, (A z).im = η / 2 * z.im)
    (hth : cthickening η (((↑) : ℝ → ℂ) '' Icc α β) ⊆ O) :
    MapsTo A (closedBall (0 : ℂ) 1) O := by
  intro z hz
  have hzn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hzn
  have him : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hzn
  refine hth ?_
  set y := max α (min β (A z).re) with hy
  have hrea := abs_le.mp hre
  have hyI : y ∈ Icc α β := ⟨le_max_left _ _, max_le hαβ.le (min_le_left _ _)⟩
  refine mem_cthickening_of_dist_le (A z) (y : ℂ) _ _ ⟨y, hyI, rfl⟩ ?_
  rw [dist_eq_norm]
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  have h1 : |(A z).im| ≤ η / 2 := by
    rw [hAim, abs_mul, abs_of_pos hq]
    nlinarith
  have h2 : |(A z).re - y| ≤ η / 2 := by
    have h3 : (A z).re ≤ β + η / 2 := by
      rw [hAre]
      have h7 : ℓ * a₀ * z.re ≤ ℓ * a₀ * 1 := mul_le_mul_of_nonneg_left hrea.2 hp.le
      rw [mul_one] at h7
      have h8 : m + ℓ = β := by rw [hm, hℓ]; ring
      linarith [hscale]
    have h4 : α - η / 2 ≤ (A z).re := by
      rw [hAre]
      have h7 : ℓ * a₀ * (-1) ≤ ℓ * a₀ * z.re := mul_le_mul_of_nonneg_left hrea.1 hp.le
      rw [mul_neg_one] at h7
      have h8 : m - ℓ = α := by rw [hm, hℓ]; ring
      linarith [hscale]
    rw [abs_le]
    constructor
    · have h5 : y ≤ max α (A z).re := max_le_max_left _ (min_le_right _ _)
      rcases le_total α (A z).re with h6 | h6
      · rw [max_eq_right h6] at h5
        linarith
      · rw [max_eq_left h6] at h5
        linarith
    · have h5 : min β (A z).re ≤ y := le_max_right _ _
      rcases le_total β (A z).re with h6 | h6
      · rw [min_eq_left h6] at h5
        linarith
      · rw [min_eq_right h6] at h5
        linarith
  linarith

/-- **Collapsing an arc.** In a closed surface, there is a homotopy from the identity to a map onto
the surface that sends the arc to one point and is injective off the arc. -/
theorem exists_collapse (hT : IsClosedSurface T) {a : 𝕀 → T} (ha : IsArcMap a) :
    ∃ (c : 𝕀 × T → T) (w : T), Continuous c ∧ (∀ x, c (0, x) = x) ∧ (∀ x ∈ range a, c (1, x) = w) ∧
      (∀ x ∉ range a, c (1, x) ≠ w) ∧ InjOn (fun x => c (1, x)) (range a)ᶜ ∧ Function.Surjective
        (fun x => c (1, x)) := by
  classical
  have hcpt : CompactSpace T := hT.1
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  obtain ⟨D, hD, hs⟩ := exists_disc_of_arc hT ha
  obtain ⟨h, g, cc⟩ := hD.exists_isChart
  have hbc : BallChart 1 (g '' ball 0 1) h g := by
    refine ⟨cc.isOpen_image_ball hman, cc.hc.mono ?_, cc.gc.mono ball_subset_closedBall, ?_, ?_,
      ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact cc.gm (ball_subset_closedBall hz)
    · rintro _ ⟨z, hz, rfl⟩
      rwa [cc.hg (ball_subset_closedBall hz)]
    · exact fun z hz => ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      rw [cc.hg (ball_subset_closedBall hz)]
    · exact fun z hz => cc.hg (ball_subset_closedBall hz)
  have hU : range a ⊆ g '' ball 0 1 := by
    rw [← cc.discInt_eq]
    exact hs
  obtain ⟨O, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart hman hbc ha hU
  set α := θ 0 with hα
  set β := θ 1 with hβ
  have hαβ : α < β := hθm zero_lt_one
  set m := (α + β) / 2 with hm
  set ℓ := (β - α) / 2 with hℓ
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  have hS : ((↑) : ℝ → ℂ) '' Icc α β ⊆ O := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨r, -, rfl⟩ := image_sub_compact hθc zero_le_one hy
    exact (hθ r).1
  obtain ⟨η, hη, hth⟩ := (isCompact_Icc.image continuous_ofReal).exists_cthickening_subset_open
    hK.isOpen hS
  set a₀ := 1 + η / (2 * ℓ) with ha₀
  have ha₁ : 1 < a₀ := by
    have : 0 < η / (2 * ℓ) := by positivity
    linarith
  have ha₀pos : 0 < a₀ := by linarith
  have hscale : ℓ * a₀ = ℓ + η / 2 := by
    rw [ha₀]
    field_simp
  have hp : 0 < ℓ * a₀ := by positivity
  have hq : 0 < η / 2 := by positivity
  let A : ℂ ≃ₜ ℂ := axisStretch m (ℓ * a₀) (η / 2) hp hq
  have hAre : ∀ z, (A z).re = m + ℓ * a₀ * z.re := fun z => by simp [A, axisStretch]
  have hAim : ∀ z, (A z).im = η / 2 * z.im := fun z => by simp [A, axisStretch]
  have hBO : ∀ z ∈ closedBall (0 : ℂ) 1, A z ∈ O := fun _ hz =>
    stretch_mapsTo_cthickening hαβ hm hℓ hp hq hscale hAre hAim hth hz
  let O' : Set ℂ := A ⁻¹' O
  let K' : ℂ → T := fun z => K (A z)
  have hK' : StripChart O' K' := by
    refine ⟨hK.isOpen.preimage A.continuous, hK.hc.comp A.continuous.continuousOn fun _ h => h,
      fun z hz w hw he => A.injective (hK.hi hz hw he), fun W hW hWO => ?_⟩
    have h1 : K' '' W = K '' (A '' W) := by rw [image_image]
    rw [h1]
    refine hK.ho _ (A.isOpenMap _ hW) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hWO hz
  obtain ⟨c₀, hc₀, hc₀m, hc₀s, hc₀z, hc₀i, hc₀o⟩ := exists_ball_collapse ha₁
  have hBc : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall _ _
  let Φ : 𝕀 × ℂ → ℂ := fun q => ((1 - q.1.1 : ℝ) : ℂ) * q.2 + (q.1.1 : ℂ) * c₀ q.2
  have hΦc : ContinuousOn Φ (univ ×ˢ closedBall (0 : ℂ) 1) := by
    have h1 : Continuous fun q : 𝕀 × ℂ => ((q.1.1 : ℝ) : ℂ) := continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous fun q : 𝕀 × ℂ => ((1 - q.1.1 : ℝ) : ℂ) := continuous_ofReal.comp
      (by fun_prop)
    have h3 : ContinuousOn (fun q : 𝕀 × ℂ => c₀ q.2) (univ ×ˢ closedBall (0 : ℂ) 1) :=
      hc₀.comp continuousOn_snd fun q hq => hq.2
    exact (h2.continuousOn.mul continuousOn_snd).add (h1.continuousOn.mul h3)
  have hΦm : ∀ p, ∀ z ∈ closedBall (0 : ℂ) 1, Φ (p, z) ∈ closedBall (0 : ℂ) 1 := by
    intro p z hz
    have h1 := (convex_closedBall (0 : ℂ) 1) hz (hc₀m hz) (a := 1 - p.1) (b := p.1)
      (by linarith [p.2.2]) p.2.1 (by ring)
    simpa [Φ, Complex.real_smul] using h1
  have hΦid : ∀ p, ∀ z ∈ frontier (closedBall (0 : ℂ) 1), Φ (p, z) = z := by
    intro p z hz
    rw [frontier_closedBall _ one_ne_zero] at hz
    simp only [Φ, hc₀s z hz]
    push_cast
    ring
  obtain ⟨c, hcc, hc1, hc2⟩ := exists_glue hK' hBc (fun z hz => hBO z hz) Φ hΦc hΦm hΦid
  have hΦ0 : ∀ z, Φ (0, z) = z := fun z => by simp [Φ]
  have hΦ1 : ∀ z, Φ (1, z) = c₀ z := fun z => by simp [Φ]
  have hc1' : ∀ z ∈ closedBall (0 : ℂ) 1, c (1, K' z) = K' (c₀ z) := fun z hz
    => by rw [hc1 _ z hz, hΦ1]
  have hrange : ∀ x, x ∈ range a ↔ ∃ z ∈ closedBall (0 : ℂ) 1, z.im = 0 ∧ |z.re| ≤ a₀⁻¹ ∧ K' z = x
    := by
    intro x
    constructor
    · rintro ⟨t, rfl⟩
      have hin : θ t ∈ Icc α β := ⟨hθm.monotone t.2.1, hθm.monotone t.2.2⟩
      set z := A.symm (θ t) with hz
      have h1 : A z = θ t := A.apply_symm_apply _
      have h2 : z.im = 0 := by
        have := hAim z
        rw [h1] at this
        simp only [ofReal_im] at this
        have h3 : η / 2 * z.im = 0 := this.symm
        exact (mul_eq_zero.mp h3).resolve_left hq.ne'
      have h3 : ℓ * a₀ * z.re = θ t - m := by
        have := hAre z
        rw [h1] at this
        simp only [ofReal_re] at this
        linarith
      have h4 : |z.re| ≤ a₀⁻¹ := by
        have h5 : |θ t - m| ≤ ℓ := by
          rw [abs_le, hm, hℓ]
          constructor <;> linarith [hin.1, hin.2]
        rw [← h3, abs_mul, abs_of_pos hp, mul_assoc] at h5
        have h6 : a₀ * |z.re| ≤ 1 := le_of_mul_le_mul_left (by simpa using h5) hℓpos
        have h7 : a₀⁻¹ * (a₀ * |z.re|) ≤ a₀⁻¹ * 1 := mul_le_mul_of_nonneg_left h6
          (inv_pos.mpr ha₀pos).le
        rwa [inv_mul_cancel_left₀ ha₀pos.ne', mul_one] at h7
      have hzb : z ∈ closedBall (0 : ℂ) 1 := by
        rw [mem_closedBall_zero_iff]
        refine (norm_le_abs_re_add_abs_im z).trans ?_
        rw [h2, abs_zero, add_zero]
        exact h4.trans (inv_le_one_of_one_le₀ ha₁.le)
      refine ⟨z, hzb, h2, h4, ?_⟩
      change K (A z) = _
      rw [h1, (hθ t).2]
    · rintro ⟨z, hz, h1, h2, rfl⟩
      have h3 := abs_le.mp h2
      have h4 : A z = ((m + ℓ * a₀ * z.re : ℝ) : ℂ) := by
        apply Complex.ext
        · rw [hAre]
          simp
        · rw [hAim, h1]
          simp
      have h5 : a₀ * a₀⁻¹ = 1 := mul_inv_cancel₀ ha₀pos.ne'
      have h6 : ℓ * a₀ * z.re ≤ ℓ := by
        have h7 := mul_le_mul_of_nonneg_left h3.2 hp.le
        have h8 : ℓ * a₀ * a₀⁻¹ = ℓ := by rw [mul_assoc, h5, mul_one]
        linarith
      have h7 : -ℓ ≤ ℓ * a₀ * z.re := by
        have h9 := mul_le_mul_of_nonneg_left h3.1 hp.le
        have h8 : ℓ * a₀ * a₀⁻¹ = ℓ := by rw [mul_assoc, h5, mul_one]
        rw [mul_neg] at h9
        linarith
      have hin : m + ℓ * a₀ * z.re ∈ Icc α β := by
        constructor
        · rw [hm, hℓ] at *
          linarith
        · rw [hm, hℓ] at *
          linarith
      obtain ⟨r, -, hr⟩ := image_sub_compact hθc zero_le_one hin
      refine ⟨r, ?_⟩
      change a r = K (A z)
      rw [h4, ← hr, (hθ r).2]
  have hK'i : InjOn K' (closedBall (0 : ℂ) 1) := fun z hz w hw he => A.injective (hK.hi (hBO z hz)
    (hBO w hw) he)
  have h0B : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  refine ⟨c, K' 0, hcc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ K' '' closedBall (0 : ℂ) 1
    · obtain ⟨z, hz, rfl⟩ := hx
      rw [hc1 _ z hz, hΦ0]
    · exact hc2 _ x hx
  · intro x hx
    obtain ⟨z, hz, h1, h2, rfl⟩ := (hrange x).mp hx
    rw [hc1' z hz, (hc₀z z hz).mpr ⟨h1, h2⟩]
  · intro x hx he
    by_cases hin : x ∈ K' '' closedBall (0 : ℂ) 1
    · obtain ⟨z, hz, rfl⟩ := hin
      rw [hc1' z hz] at he
      have h1 := hK'i (hc₀m hz) h0B he
      obtain ⟨h2, h3⟩ := (hc₀z z hz).mp h1
      exact hx ((hrange _).mpr ⟨z, hz, h2, h3, rfl⟩)
    · rw [hc2 _ x hin] at he
      exact hin ⟨0, h0B, he.symm⟩
  · intro x hx y hy he
    simp only at he
    have hne : ∀ z ∈ closedBall (0 : ℂ) 1, K' z ∉ range a → c₀ z ≠ 0 := fun z hz hn h0 => by
      obtain ⟨h2, h3⟩ := (hc₀z z hz).mp h0
      exact hn ((hrange _).mpr ⟨z, hz, h2, h3, rfl⟩)
    by_cases hin : x ∈ K' '' closedBall (0 : ℂ) 1 <;> by_cases hin' : y ∈ K' '' closedBall (0 : ℂ) 1
    · obtain ⟨z, hz, rfl⟩ := hin
      obtain ⟨z', hz', rfl⟩ := hin'
      rw [hc1' z hz, hc1' z' hz'] at he
      rw [hc₀i z hz z' hz' (hne z hz hx) (hK'i (hc₀m hz) (hc₀m hz') he)]
    · obtain ⟨z, hz, rfl⟩ := hin
      rw [hc1' z hz, hc2 _ y hin'] at he
      exact absurd ⟨_, hc₀m hz, he⟩ hin'
    · obtain ⟨z, hz, rfl⟩ := hin'
      rw [hc1' z hz, hc2 _ x hin] at he
      exact absurd ⟨_, hc₀m hz, he.symm⟩ hin
    · rwa [hc2 _ x hin, hc2 _ y hin'] at he
  · intro y
    by_cases hin : y ∈ K' '' closedBall (0 : ℂ) 1
    · obtain ⟨v, hv, rfl⟩ := hin
      obtain ⟨z, hz, rfl⟩ := hc₀o v hv
      exact ⟨K' z, hc1' z hz⟩
    · exact ⟨y, hc2 _ y hin⟩

end GraphMinor.Surface
