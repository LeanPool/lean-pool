/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Rescaling
public import LeanPool.CIVAxisymmetric.Zoom.Lengths
public import LeanPool.CIVAxisymmetric.Setting.MeridionalNorm
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Instances.Real.Lemmas

/-! ### The two bridges to the selected sequence -/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- Extract coordinate-wise absolute bounds from a compact set in the product space. -/
private lemma exists_bound_of_compact {K : Set ((ℝ × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ p ∈ K, |p.1.1| ≤ B ∧ |p.1.2| ≤ B ∧ |p.2| ≤ B := by
  have h_cont1 : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => p.1.1) K :=
    (continuous_fst.comp continuous_fst).continuousOn
  have h_cont2 : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => p.1.2) K :=
    (continuous_snd.comp continuous_fst).continuousOn
  have h_cont3 : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => p.2) K :=
    continuous_snd.continuousOn
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn h_cont1
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn h_cont2
  obtain ⟨B3, hB3⟩ := hK.exists_bound_of_continuousOn h_cont3
  refine ⟨max (max B1 B2) B3, fun p hp => ?_⟩
  have h1 : |p.1.1| ≤ B1 := by
    have hx := hB1 p hp
    rw [Real.norm_eq_abs] at hx
    exact hx
  have h2 : |p.1.2| ≤ B2 := by
    have hy := hB2 p hp
    rw [Real.norm_eq_abs] at hy
    exact hy
  have h3 : |p.2| ≤ B3 := by
    have ht := hB3 p hp
    rw [Real.norm_eq_abs] at ht
    exact ht
  exact ⟨h1.trans ((le_max_left B1 B2).trans (le_max_left _ B3)),
    h2.trans ((le_max_right B1 B2).trans (le_max_left _ B3)),
    h3.trans (le_max_right _ B3)⟩

/-- For `0 < h < 1/2`, the exponent `1 - 2h` is positive. -/
private lemma one_minus_two_h_pos {h : ℝ} (hh : 0 < h ∧ h < 1 / 2) : 0 < 1 - 2 * h := by
  linarith only [hh.2]

/-- Replacing the two meridional coordinates by a common absolute bound `B'` can only
increase the squared meridional radius of the zoomed point. -/
private lemma zoomPoint_meridional_sq_le {lam h zc B' x y : ℝ} (hlam : 0 < lam)
    (hx : |x| ≤ B') (hy : |y| ≤ B') :
    (lam * x) ^ 2 + (zc + lam ^ (1 - 2 * h) * y) ^ 2
      ≤ (lam * B') ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B') ^ 2 := by
  have hrpow : (0 : ℝ) ≤ lam ^ (1 - 2 * h) := Real.rpow_nonneg hlam.le _
  have habs1 : |lam * x| ≤ lam * B' := by
    rw [abs_mul, abs_of_pos hlam]
    exact mul_le_mul_of_nonneg_left hx hlam.le
  have habs2 : |zc + lam ^ (1 - 2 * h) * y| ≤ |zc| + lam ^ (1 - 2 * h) * B' := by
    refine (abs_add_le zc (lam ^ (1 - 2 * h) * y)).trans ?_
    rw [abs_mul, abs_of_nonneg hrpow]
    linarith only [mul_le_mul_of_nonneg_left hy hrpow]
  have hsq1 : (lam * x) ^ 2 ≤ (lam * B') ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le habs1) (le_of_abs_le habs1)
  have hsq2 : (zc + lam ^ (1 - 2 * h) * y) ^ 2 ≤ (|zc| + lam ^ (1 - 2 * h) * B') ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le habs2) (le_of_abs_le habs2)
  linarith only [hsq1, hsq2]

/-- As `lam → 0⁺` the squared meridional radius of the bounding point tends to `zc ^ 2`,
so it eventually stays below any strictly larger level `R`. -/
private lemma eventually_meridional_sq_lt {h zc R B' : ℝ} (hexp : 0 < 1 - 2 * h)
    (hzc : |zc| ^ 2 < R) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      (lam * B') ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B') ^ 2 < R := by
  have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.mono_left tendsto_id nhdsWithin_le_nhds
  have hrpow : Tendsto (fun lam : ℝ => lam ^ (1 - 2 * h)) (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : ℝ) ^ (1 - 2 * h))) :=
    Filter.Tendsto.mono_left
      (Real.continuousAt_rpow_const 0 (1 - 2 * h) (Or.inr hexp.le)).tendsto
      nhdsWithin_le_nhds
  have hlim : Tendsto (fun lam : ℝ => (lam * B') ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B') ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((0 : ℝ) * B') ^ 2 + (|zc| + (0 : ℝ) ^ (1 - 2 * h) * B') ^ 2)) :=
    ((hid.mul tendsto_const_nhds).pow 2).add
      ((tendsto_const_nhds.add (hrpow.mul tendsto_const_nhds)).pow 2)
  have hval : ((0 : ℝ) * B') ^ 2 + (|zc| + (0 : ℝ) ^ (1 - 2 * h) * B') ^ 2 < R := by
    rw [Real.zero_rpow (ne_of_gt hexp), zero_mul, add_zero]
    linarith only [hzc]
  exact hlim.eventually_lt_const hval

/-- The parabolic time factor `lam ^ 2 * B'` eventually drops below any positive level. -/
private lemma eventually_sq_mul_lt {B' c : ℝ} (hc : 0 < c) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ 2 * B' < c := by
  have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.mono_left tendsto_id nhdsWithin_le_nhds
  have hlim : Tendsto (fun lam : ℝ => lam ^ 2 * B') (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : ℝ) ^ 2 * B')) := (hid.pow 2).mul tendsto_const_nhds
  have hval : (0 : ℝ) ^ 2 * B' < c := by
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, zero_mul]
    exact hc
  exact hlim.eventually_lt_const hval

theorem eventually_zoomPoint_mem_unitCylinder {h zc ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hzc : |zc| < ρ)
    (hρ : ρ < 1) (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) (hKt : ∀ p ∈ K, p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), ∀ p ∈ K, zoomPoint lam h zc p ∈ unitCylinder := by
  have hexp : 0 < 1 - 2 * h := one_minus_two_h_pos hh
  have hzc_lt : |zc| < 1 := lt_trans hzc hρ
  have hzc_sq : |zc| ^ 2 < 1 := by
    have hlt := sq_lt_sq' (show -(1 : ℝ) < |zc| by linarith only [abs_nonneg zc]) hzc_lt
    rwa [one_pow] at hlt
  obtain ⟨B, hB⟩ := exists_bound_of_compact hK
  have hmer : ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      (lam * B) ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B) ^ 2 < 1 :=
    eventually_meridional_sq_lt (B' := B) hexp hzc_sq
  have htime : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ 2 * B < 1 :=
    eventually_sq_mul_lt (B' := B) (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hmer, htime] with lam hlam hlam_mer hlam_time
  intro p hp
  have hlam_pos : (0 : ℝ) < lam := hlam
  obtain ⟨hx, hy, ht⟩ := hB p hp
  have hmul : lam ^ 2 * (-B) ≤ lam ^ 2 * p.2 :=
    mul_le_mul_of_nonneg_left (neg_le_of_abs_le ht) (sq_nonneg lam)
  rw [zoomPoint_mem_unitCylinder_iff]
  refine ⟨lt_of_le_of_lt (zoomPoint_meridional_sq_le hlam_pos hx hy) hlam_mer,
    mem_Ioo.mpr ⟨?_, mul_neg_of_pos_of_neg (pow_pos hlam_pos 2) (hKt p hp)⟩⟩
  linarith only [hmul, hlam_time]

theorem eventually_zoomPoint_mem_ball {h zc ρ Rstar : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hzc : |zc| < ρ)
    (hρ : ρ < Rstar) (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), ∀ p ∈ K, (zoomPoint lam h zc p).1 ∈ vec3Ball 0 Rstar := by
  have hexp : 0 < 1 - 2 * h := one_minus_two_h_pos hh
  have hzc_lt : |zc| < Rstar := lt_trans hzc hρ
  have hRstar_pos : (0 : ℝ) < Rstar := lt_of_le_of_lt (abs_nonneg zc) hzc_lt
  have hzc_sq : |zc| ^ 2 < Rstar ^ 2 :=
    sq_lt_sq' (by linarith only [abs_nonneg zc, hzc_lt]) hzc_lt
  obtain ⟨B, hB⟩ := exists_bound_of_compact hK
  have hmer : ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      (lam * B) ^ 2 + (|zc| + lam ^ (1 - 2 * h) * B) ^ 2 < Rstar ^ 2 :=
    eventually_meridional_sq_lt (B' := B) hexp hzc_sq
  filter_upwards [self_mem_nhdsWithin, hmer] with lam hlam hlam_mer
  intro p hp
  have hlam_pos : (0 : ℝ) < lam := hlam
  obtain ⟨hx, hy, _⟩ := hB p hp
  have hfst : (zoomPoint lam h zc p).1
      = meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) := rfl
  rw [hfst, meridional_mem_vec3Ball_zero_iff]
  exact ⟨lt_of_le_of_lt (zoomPoint_meridional_sq_le hlam_pos hx hy) hlam_mer, hRstar_pos⟩

theorem eventually_zoomPoint_time_mem {h zc tstar : ℝ} (htstar : tstar < 0)
    (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) (hKt : ∀ p ∈ K, p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), ∀ p ∈ K, (zoomPoint lam h zc p).2 ∈ Ioo tstar 0 := by
  obtain ⟨B, hB⟩ := exists_bound_of_compact hK
  have htime : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ 2 * B < -tstar :=
    eventually_sq_mul_lt (B' := B) (by linarith only [htstar])
  filter_upwards [self_mem_nhdsWithin, htime] with lam hlam hlam_time
  intro p hp
  have hlam_pos : (0 : ℝ) < lam := hlam
  obtain ⟨_, _, ht⟩ := hB p hp
  have hmul : lam ^ 2 * (-B) ≤ lam ^ 2 * p.2 :=
    mul_le_mul_of_nonneg_left (neg_le_of_abs_le ht) (sq_nonneg lam)
  have hsnd : (zoomPoint lam h zc p).2 = lam ^ 2 * p.2 := rfl
  rw [hsnd]
  exact mem_Ioo.mpr ⟨by linarith only [hmul, hlam_time],
    mul_neg_of_pos_of_neg (pow_pos hlam_pos 2) (hKt p hp)⟩



/-- The ball and time clauses of the preimage statement, taken together: for a compact set of
rescaled points with negative times, the zoom point of every one of them eventually lies in
`B(R_*) × (t_*, 0)`, which is the set on which the circulation bound
`eq:aniso:zoom:circulation` holds. -/
theorem eventually_zoomPoint_mem_ball_and_time {h zc ρ Rstar tstar : ℝ}
    (hh : 0 < h ∧ h < 1 / 2) (hzc : |zc| < ρ) (hρ : ρ < Rstar) (htstar : tstar < 0)
    (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) (hKt : ∀ p ∈ K, p.2 < 0) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ), ∀ p ∈ K,
      (zoomPoint lam h zc p).1 ∈ vec3Ball 0 Rstar ∧ (zoomPoint lam h zc p).2 ∈ Ioo tstar 0 := by
  filter_upwards [eventually_zoomPoint_mem_ball hh hzc hρ K hK,
    eventually_zoomPoint_time_mem htstar K hK hKt] with lam hball htime p hp
  exact ⟨hball p hp, htime p hp⟩

/-- The radial length `eq:aniso:lengths` is strictly positive at negative times, so it tends
to `0` through positive values. This is the refinement of `tendsto_radialLength` that the
preimage statements need, since they are stated along `𝓝[>] 0`. -/
theorem tendsto_radialLength_nhdsGT : Tendsto radialLength (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_radialLength, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htneg : t < 0 := ht
  show (0 : ℝ) < radialLength t
  exact Real.rpow_pos_of_pos (neg_pos.mpr htneg) _

/-- A sequence of negative times converging to the singular time converges within the negative
reals, which is the filter `tendsto_radialLength_nhdsGT` starts from. -/
theorem tendsto_atTop_nhdsLT {t : ℕ → ℝ} (hneg : ∀ n, t n < 0)
    (htend : Tendsto t atTop (𝓝 (0 : ℝ))) : Tendsto t atTop (𝓝[<] (0 : ℝ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t htend
    (Eventually.of_forall hneg)

/-- The passage from the filter `𝓝[>] 0` to the selected sequence: whatever holds eventually
in the zoom scale holds for all large `n` at the scales `λ_n = ℓ_r(t_n)` attached to a sequence
of negative times increasing to the singular time, as selected after `eq:aniso:zoom:selected`.
Applied to `eventually_zoomPoint_mem_unitCylinder`, `eventually_zoomPoint_mem_ball`,
`eventually_zoomPoint_time_mem` or their conjunction, this is the statement that the preimage
of `Q` contains a given compact set for all large `n`. -/
theorem eventually_atTop_radialLength {P : ℝ → Prop} {t : ℕ → ℝ}
    (hneg : ∀ n, t n < 0) (htend : Tendsto t atTop (𝓝 (0 : ℝ)))
    (hP : ∀ᶠ lam in 𝓝[>] (0 : ℝ), P lam) :
    ∀ᶠ n in atTop, P (radialLength (t n)) :=
  (tendsto_radialLength_nhdsGT.comp (tendsto_atTop_nhdsLT hneg htend)).eventually hP

end CIV
