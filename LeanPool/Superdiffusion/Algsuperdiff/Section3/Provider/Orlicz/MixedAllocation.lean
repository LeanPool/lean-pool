/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-!
# MixedAllocation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic mixed two-lane Orlicz allocation

ABK26 uses, in the proof of Proposition `p.homogenization.step`, a random
variable carrying a *two-term* weak-Orlicz bound at the pair of exponents `(1,
1/4)` as if it were a pair of single-lane variables, one for each exponent, so
that the finite-range concentration corollary of Proposition `p.concentration`
may be applied lane by lane.  Neither obvious splitting survives that step: the
witnesses of the two-term relation are arbitrary random variables, in no way
functions of the original one, so nothing makes them measurable for the local
σ-field of the cube that carries it, and they only dominate it rather than sum
to it; while a deterministic truncation at a *fixed* threshold is local but pays
the truncation level, not the linear amplitude, in its `Γ_1` lane.

This module supplies the deterministic allocation that does survive.  For
positive amplitudes `a` and `b` the profile

`mixedProfile a b t = a * t + b * t ^ 4`

is the exact composite threshold appearing in the two-term tail: `a` times the
inverse of `Γ_1` at level `e^{-t}` plus `b` times the inverse of `Γ_{1/4}` at
the same level.  It is a strictly increasing bijection of `[0, ∞)` onto itself,
so a real number `x` has a unique *allocation time* `mixedTime a b |x|`, and
the two summands of the profile at that time, resigned to the sign of `x`, are
two lanes

`linearLane a b x + quarticLane a b x = x`

that are **fixed Borel functions of `x` alone**.  Composing them with a random
variable therefore preserves every σ-field the variable is measurable for; this
is `measurable_linearLane_comp` and `measurable_quarticLane_comp`, and it is
what transfers locality, and with it independence, to the lanes.

The tail transfer is `isBigO_gammaSigma_one_linearLane_comp` and
`isBigO_gammaSigma_quarter_quarticLane_comp`: a mixed tail
`P[|X| > mixedProfile a b t] ≤ C e^{-t}` gives a genuine one-lane
`O_{Γ_1}(c a)` bound for the linear lane and a genuine one-lane
`O_{Γ_{1/4}}(c' b)` bound for the quartic lane, where the tail constant `C` is
absorbed into the amplitudes by the single logarithmic shift `laneAbsorb C`.

Allocation destroys exact centering.  Both variants are supplied: the raw lanes
with explicit mean bounds (`abs_integral_linearLane_comp_le` and its quartic
twin), and the centered lanes `centeredLinearLane` and `centeredQuarticLane`,
whose sum reproduces `X` exactly when `X` is centered, and whose amplitudes pay
the constant factor `laneCenterConst`.

## References

* ABK26, Appendix (the two-term weak-Orlicz notation and `e.Gamma.sigma`).
* ABK26, Proposition `p.homogenization.step`.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

/-! ## The two-channel profile and its inverse -/

section Profile

/-- The composite threshold of a two-term `(Γ_1, Γ_{1/4})` tail at level
`e^{-t}`: the linear amplitude times `t` plus the quartic amplitude times
`t ^ 4`. -/
def mixedProfile (a b t : ℝ) : ℝ := a * t + b * t ^ 4

theorem continuous_mixedProfile (a b : ℝ) : Continuous (mixedProfile a b) := by
  unfold mixedProfile
  fun_prop

@[simp] theorem mixedProfile_zero (a b : ℝ) : mixedProfile a b 0 = 0 := by
  simp [mixedProfile]

theorem strictMonoOn_mixedProfile {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (mixedProfile a b) (Set.Ici 0) := by
  intro x hx y _hy hxy
  have hpow : x ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hx hxy.le 4
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxy ha)
    (mul_le_mul_of_nonneg_left hpow hb.le)

/-- The profile is onto `[0, ∞)`: every nonnegative level is attained at a
nonnegative time.  This is the intermediate value theorem on `[0, y / a]`. -/
theorem exists_mixedProfile_eq {a b y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : 0 ≤ y) : ∃ t ∈ Set.Ici (0 : ℝ), mixedProfile a b t = y := by
  have hbound : 0 ≤ y / a := div_nonneg hy ha.le
  have hlinear : a * (y / a) = y := by field_simp
  have htop : y ≤ mixedProfile a b (y / a) := by
    unfold mixedProfile
    rw [hlinear]
    exact le_add_of_nonneg_right (mul_nonneg hb.le (pow_nonneg hbound 4))
  have htarget : y ∈ Set.Icc (mixedProfile a b 0) (mixedProfile a b (y / a)) :=
    ⟨by simpa using hy, htop⟩
  obtain ⟨t, ht, hft⟩ :=
    intermediate_value_Icc hbound (continuous_mixedProfile a b).continuousOn htarget
  exact ⟨t, ht.1, hft⟩

/-- The allocation time: the nonnegative inverse of `mixedProfile`.  The unused
negative branch makes it a total real function. -/
def mixedTime (a b y : ℝ) : ℝ :=
  if 0 ≤ y then Function.invFunOn (mixedProfile a b) (Set.Ici 0) y else 0

theorem mixedProfile_mixedTime {a b y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : 0 ≤ y) : mixedProfile a b (mixedTime a b y) = y := by
  rw [mixedTime, ite_eq_left hy]
  exact Function.invFunOn_eq (exists_mixedProfile_eq ha hb hy)

theorem mixedTime_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    0 ≤ mixedTime a b y := by
  by_cases hy : 0 ≤ y
  · rw [mixedTime, ite_eq_left hy]
    obtain ⟨t, ht, hft⟩ := exists_mixedProfile_eq (y := y) ha hb hy
    rw [← hft]
    exact Function.invFunOn_apply_mem ht
  · rw [mixedTime, ite_eq_right hy]

theorem monotone_mixedTime {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Monotone (mixedTime a b) := by
  intro y z hyz
  by_cases hz : 0 ≤ z
  · by_cases hy : 0 ≤ y
    · by_contra hnot
      have hlt : mixedTime a b z < mixedTime a b y := lt_of_not_ge hnot
      have hstrict := strictMonoOn_mixedProfile ha hb
        (mixedTime_nonneg ha hb z) (mixedTime_nonneg ha hb y) hlt
      rw [mixedProfile_mixedTime ha hb hz, mixedProfile_mixedTime ha hb hy] at hstrict
      exact absurd hyz (not_le_of_gt hstrict)
    · rw [mixedTime, ite_eq_right hy]
      exact mixedTime_nonneg ha hb z
  · have hy' : ¬ 0 ≤ y := fun h => hz (h.trans hyz)
    rw [mixedTime, ite_eq_right hy', mixedTime, ite_eq_right hz]

theorem measurable_mixedTime {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Measurable (mixedTime a b) :=
  (monotone_mixedTime ha hb).measurable

end Profile

/-! ## The two lanes -/

section Lanes

/-- The `Γ_1` lane of the allocation: the linear part of the profile at the
allocation time of `|x|`, carrying the sign of `x`. -/
def linearLane (a b x : ℝ) : ℝ := (x / |x|) * (a * mixedTime a b |x|)

/-- The `Γ_{1/4}` lane of the allocation: the quartic part of the profile at
the allocation time of `|x|`, carrying the sign of `x`. -/
def quarticLane (a b x : ℝ) : ℝ := (x / |x|) * (b * mixedTime a b |x| ^ 4)

theorem abs_div_abs_self_le_one (x : ℝ) : abs (x / |x|) ≤ 1 := by
  rw [abs_div, abs_abs]
  by_cases hx : x = 0
  · simp [hx]
  · rw [div_self (abs_ne_zero.mpr hx)]

/-- **The allocation is a pointwise splitting.**  The two lanes are exact
summands of the identity. -/
theorem linearLane_add_quarticLane {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    linearLane a b x + quarticLane a b x = x := by
  unfold linearLane quarticLane
  rw [← mul_add, ← mixedProfile, mixedProfile_mixedTime ha hb (abs_nonneg x)]
  by_cases hx : x = 0
  · simp [hx]
  · exact div_mul_cancel₀ x (abs_ne_zero.mpr hx)

theorem measurable_linearLane {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Measurable (linearLane a b) := by
  unfold linearLane
  refine Measurable.mul (measurable_id.div continuous_abs.measurable) ?_
  exact measurable_const.mul
    ((measurable_mixedTime ha hb).comp continuous_abs.measurable)

theorem measurable_quarticLane {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Measurable (quarticLane a b) := by
  unfold quarticLane
  refine Measurable.mul (measurable_id.div continuous_abs.measurable) ?_
  exact measurable_const.mul
    (((measurable_mixedTime ha hb).comp continuous_abs.measurable).pow_const 4)

/-- **Locality transfer for the linear lane.**  The lane is a fixed Borel
function of the value alone, so composing it with a random variable preserves
every σ-field that variable is measurable for. -/
theorem measurable_linearLane_comp {Ω : Type*} {m : MeasurableSpace Ω}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {X : Ω → ℝ} (hX : Measurable[m] X) :
    Measurable[m] fun ω => linearLane a b (X ω) :=
  (measurable_linearLane ha hb).comp hX

/-- **Locality transfer for the quartic lane.** -/
theorem measurable_quarticLane_comp {Ω : Type*} {m : MeasurableSpace Ω}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {X : Ω → ℝ} (hX : Measurable[m] X) :
    Measurable[m] fun ω => quarticLane a b (X ω) :=
  (measurable_quarticLane ha hb).comp hX

theorem abs_linearLane_le {a b x s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : mixedTime a b |x| ≤ s) : |linearLane a b x| ≤ a * s := by
  unfold linearLane
  rw [abs_mul]
  have htime0 : 0 ≤ mixedTime a b |x| := mixedTime_nonneg ha hb |x|
  have habs : abs (a * mixedTime a b |x|) = a * mixedTime a b |x| :=
    abs_of_nonneg (mul_nonneg ha.le htime0)
  calc abs (x / |x|) * abs (a * mixedTime a b |x|)
      = abs (x / |x|) * (a * mixedTime a b |x|) := by rw [habs]
    _ ≤ 1 * (a * mixedTime a b |x|) :=
        mul_le_mul_of_nonneg_right (abs_div_abs_self_le_one x)
          (mul_nonneg ha.le htime0)
    _ ≤ a * s := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hs ha.le

theorem abs_quarticLane_le {a b x s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : mixedTime a b |x| ≤ s) : |quarticLane a b x| ≤ b * s ^ 4 := by
  unfold quarticLane
  rw [abs_mul]
  have htime0 : 0 ≤ mixedTime a b |x| := mixedTime_nonneg ha hb |x|
  have habs : abs (b * mixedTime a b |x| ^ 4) = b * mixedTime a b |x| ^ 4 :=
    abs_of_nonneg (mul_nonneg hb.le (pow_nonneg htime0 4))
  have hpow : mixedTime a b |x| ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ htime0 hs 4
  calc abs (x / |x|) * abs (b * mixedTime a b |x| ^ 4)
      = abs (x / |x|) * (b * mixedTime a b |x| ^ 4) := by rw [habs]
    _ ≤ 1 * (b * mixedTime a b |x| ^ 4) :=
        mul_le_mul_of_nonneg_right (abs_div_abs_self_le_one x)
          (mul_nonneg hb.le (pow_nonneg htime0 4))
    _ ≤ b * s ^ 4 := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hpow hb.le

/-- Above the linear share of the profile, the linear lane can only be large
where the original value already exceeds the whole profile. -/
theorem absTailEvent_linearLane_comp_subset {Ω : Type*} (X : Ω → ℝ)
    {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) :
    absTailEvent (fun ω => linearLane a b (X ω)) (a * s) ⊆
      absTailEvent X (mixedProfile a b s) := by
  intro ω hω
  have hgt : a * s < |linearLane a b (X ω)| := hω
  have htime : s < mixedTime a b |X ω| := by
    by_contra hnot
    exact absurd (abs_linearLane_le ha hb (le_of_not_gt hnot)) (not_le_of_gt hgt)
  have hstrict := strictMonoOn_mixedProfile ha hb hs
    (mixedTime_nonneg ha hb |X ω|) htime
  rw [mixedProfile_mixedTime ha hb (abs_nonneg (X ω))] at hstrict
  exact hstrict

/-- Above the quartic share of the profile, the quartic lane can only be large
where the original value already exceeds the whole profile. -/
theorem absTailEvent_quarticLane_comp_subset {Ω : Type*} (X : Ω → ℝ)
    {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) :
    absTailEvent (fun ω => quarticLane a b (X ω)) (b * s ^ 4) ⊆
      absTailEvent X (mixedProfile a b s) := by
  intro ω hω
  have hgt : b * s ^ 4 < |quarticLane a b (X ω)| := hω
  have htime : s < mixedTime a b |X ω| := by
    by_contra hnot
    exact absurd (abs_quarticLane_le ha hb (le_of_not_gt hnot)) (not_le_of_gt hgt)
  have hstrict := strictMonoOn_mixedProfile ha hb hs
    (mixedTime_nonneg ha hb |X ω|) htime
  rw [mixedProfile_mixedTime ha hb (abs_nonneg (X ω))] at hstrict
  exact hstrict

end Lanes

/-! ## The mixed tail datum -/

section MixedTail

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The two-term tail at the composite profile: for every level `t ≥ 1` the
variable exceeds `mixedProfile a b t` with probability at most `C e^{-t}`.
This is the shape produced by a two-term `(Γ_1, Γ_{1/4})` weak-Orlicz bound at
amplitudes `a` and `b`; see
`hasMixedGammaTailWith_two_of_isTwoTermBigOWith_abs`. -/
def HasMixedGammaTailWith (μ : Measure Ω) (X : Ω → ℝ) (C a b : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real (absTailEvent X (mixedProfile a b t)) ≤ C * Real.exp (-t)

/-- `(u ^ (1/4)) ^ 4 = u` on the nonnegative reals; the only place where a real
power of the level appears. -/
theorem rpow_quarter_pow_four {u : ℝ} (hu : 0 ≤ u) : (u ^ (1 / 4 : ℝ)) ^ 4 = u := by
  have h : ((4 : ℕ) : ℝ)⁻¹ = (1 / 4 : ℝ) := by norm_num
  have := Real.rpow_inv_natCast_pow (x := u) (n := 4) hu (by norm_num)
  rwa [h] at this

/-- `(t ^ 4) ^ (1/4) = t` on the nonnegative reals: the quartic level of the
two-term tail returns the linear level. -/
theorem pow_four_rpow_quarter {t : ℝ} (ht : 0 ≤ t) : (t ^ 4) ^ (1 / 4 : ℝ) = t := by
  rw [← Real.rpow_natCast t 4, ← Real.rpow_mul ht]
  norm_num

/-- **The bridge from the proved two-term vocabulary.**  A two-term one-sided
weak-Orlicz bound for `|X|` at the exponents `1` and `1/4` gives the mixed tail
at the same two amplitudes, with tail constant `2`: the two witness tails are
evaluated at the levels `t` and `t ^ 4`, both of which return `e^{-t}`. -/
theorem hasMixedGammaTailWith_two_of_isTwoTermBigOWith_abs
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {A₁ A₄ : ℝ}
    (hX : Probability.IsTwoTermBigOWith μ (gammaSigma 1) (gammaSigma (1 / 4))
      (fun ω => |X ω|) A₁ A₄) :
    HasMixedGammaTailWith μ X 2 A₁ A₄ := by
  obtain ⟨Y, Z, -, -, -, -, -, -, -, hle, hY, hZ⟩ := hX
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have ht4 : (1 : ℝ) ≤ t ^ 4 := one_le_pow₀ ht
  have hsub : absTailEvent X (mixedProfile A₁ A₄ t) ⊆
      upperTailEvent Y (A₁ * t) ∪ upperTailEvent Z (A₄ * t ^ 4) := by
    intro ω hω
    have hgt : A₁ * t + A₄ * t ^ 4 < |X ω| := hω
    have hsum : A₁ * t + A₄ * t ^ 4 < Y ω + Z ω := lt_of_lt_of_le hgt (hle ω)
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    have h1 : Y ω ≤ A₁ * t := not_lt.mp hcon.1
    have h2 : Z ω ≤ A₄ * t ^ 4 := not_lt.mp hcon.2
    exact absurd hsum (not_lt.mpr (add_le_add h1 h2))
  have hY' : μ.real (upperTailEvent Y (A₁ * t)) ≤ Real.exp (-t) := by
    have := hY ht
    rwa [gammaSigma_inv, Real.rpow_one] at this
  have hZ' : μ.real (upperTailEvent Z (A₄ * t ^ 4)) ≤ Real.exp (-t) := by
    have := hZ ht4
    rwa [gammaSigma_inv, pow_four_rpow_quarter ht0] at this
  calc μ.real (absTailEvent X (mixedProfile A₁ A₄ t))
      ≤ μ.real (upperTailEvent Y (A₁ * t) ∪ upperTailEvent Z (A₄ * t ^ 4)) :=
        measureReal_mono hsub
    _ ≤ μ.real (upperTailEvent Y (A₁ * t)) +
          μ.real (upperTailEvent Z (A₄ * t ^ 4)) := measureReal_union_le _ _
    _ ≤ Real.exp (-t) + Real.exp (-t) := add_le_add hY' hZ'
    _ = 2 * Real.exp (-t) := by ring

end MixedTail

/-! ## Absorbing the tail constant into the amplitude -/

section Absorb

/-- The logarithmic amplitude shift that turns a tail bound `C e^{-t}` into a
genuine `e^{-t}` bound at the enlarged amplitude. -/
def laneAbsorb (C : ℝ) : ℝ := 1 + Real.log (max 1 C)

theorem one_le_laneAbsorb (C : ℝ) : 1 ≤ laneAbsorb C := by
  have hlog : 0 ≤ Real.log (max 1 C) := Real.log_nonneg (le_max_left 1 C)
  unfold laneAbsorb
  linarith

theorem laneAbsorb_pos (C : ℝ) : 0 < laneAbsorb C :=
  lt_of_lt_of_le zero_lt_one (one_le_laneAbsorb C)

/-- The defining property of the shift: at every level `w ≥ 1` the constant `C`
is paid for by the extra decay `e^{-(laneAbsorb C - 1) w}`. -/
theorem mul_exp_neg_laneAbsorb_mul_le (C : ℝ) {w : ℝ} (hw : 1 ≤ w) :
    C * Real.exp (-(laneAbsorb C * w)) ≤ Real.exp (-w) := by
  have hmax : (0 : ℝ) < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hlog : Real.log (max 1 C) = laneAbsorb C - 1 := by
    unfold laneAbsorb; ring
  have hC : C ≤ Real.exp (laneAbsorb C - 1) := by
    rw [← hlog, Real.exp_log hmax]
    exact le_max_right 1 C
  have hnn : 0 ≤ laneAbsorb C - 1 := by
    have := one_le_laneAbsorb C; linarith
  have hstep : Real.exp (laneAbsorb C - 1) ≤ Real.exp ((laneAbsorb C - 1) * w) :=
    Real.exp_le_exp.2 (le_mul_of_one_le_right hnn hw)
  calc C * Real.exp (-(laneAbsorb C * w))
      ≤ Real.exp ((laneAbsorb C - 1) * w) * Real.exp (-(laneAbsorb C * w)) :=
        mul_le_mul_of_nonneg_right (hC.trans hstep) (Real.exp_pos _).le
    _ = Real.exp (-w) := by
        rw [← Real.exp_add]
        congr 1
        ring

end Absorb

/-! ## The one-lane tails of the allocation -/

section LaneTails

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The linear lane is a genuine `Γ_1` variable.**  A mixed tail with
constant `C` at amplitudes `(a, b)` gives `linearLane a b ∘ X = O_{Γ_1}(λ_C a)`,
with `λ_C = laneAbsorb C`. -/
theorem isBigO_gammaSigma_one_linearLane_comp {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX : HasMixedGammaTailWith μ X C a b) :
    IsBigO μ (gammaSigma 1) (fun ω => linearLane a b (X ω)) (laneAbsorb C * a) := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have hst : (1 : ℝ) ≤ laneAbsorb C * t :=
    one_le_mul_of_one_le_of_one_le (one_le_laneAbsorb C) ht
  have hs0 : (0 : ℝ) ≤ laneAbsorb C * t := le_trans zero_le_one hst
  have hthr : laneAbsorb C * a * t = a * (laneAbsorb C * t) := by ring
  rw [hthr, Real.rpow_one]
  calc μ.real (absTailEvent (fun ω => linearLane a b (X ω)) (a * (laneAbsorb C * t)))
      ≤ μ.real (absTailEvent X (mixedProfile a b (laneAbsorb C * t))) :=
        measureReal_mono (absTailEvent_linearLane_comp_subset X ha hb hs0)
    _ ≤ C * Real.exp (-(laneAbsorb C * t)) := hX hst
    _ ≤ Real.exp (-t) := mul_exp_neg_laneAbsorb_mul_le C ht

/-- **The quartic lane is a genuine `Γ_{1/4}` variable.**  A mixed tail with
constant `C` at amplitudes `(a, b)` gives
`quarticLane a b ∘ X = O_{Γ_{1/4}}(λ_C ^ 4 b)`. -/
theorem isBigO_gammaSigma_quarter_quarticLane_comp {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX : HasMixedGammaTailWith μ X C a b) :
    IsBigO μ (gammaSigma (1 / 4)) (fun ω => quarticLane a b (X ω))
      (laneAbsorb C ^ 4 * b) := by
  rw [isBigO_gammaSigma_iff]
  intro u hu
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu
  have hw1 : (1 : ℝ) ≤ u ^ (1 / 4 : ℝ) := Real.one_le_rpow hu (by norm_num)
  have hst : (1 : ℝ) ≤ laneAbsorb C * u ^ (1 / 4 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_laneAbsorb C) hw1
  have hs0 : (0 : ℝ) ≤ laneAbsorb C * u ^ (1 / 4 : ℝ) := le_trans zero_le_one hst
  have hthr : laneAbsorb C ^ 4 * b * u = b * (laneAbsorb C * u ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [mul_pow, rpow_quarter_pow_four hu0]
    ring
  rw [hthr]
  calc μ.real (absTailEvent (fun ω => quarticLane a b (X ω))
        (b * (laneAbsorb C * u ^ (1 / 4 : ℝ)) ^ 4))
      ≤ μ.real (absTailEvent X (mixedProfile a b (laneAbsorb C * u ^ (1 / 4 : ℝ)))) :=
        measureReal_mono (absTailEvent_quarticLane_comp_subset X ha hb hs0)
    _ ≤ C * Real.exp (-(laneAbsorb C * u ^ (1 / 4 : ℝ))) := hX hst
    _ ≤ Real.exp (-(u ^ (1 / 4 : ℝ))) := mul_exp_neg_laneAbsorb_mul_le C hw1

end LaneTails

/-! ## Centering a stretched-exponential variable at its own mean -/

section Centering

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cost of centering a `Γ_σ` variable at its own mean: the two-term
triangle constant times one plus the first-moment constant. -/
def laneCenterConst (σ : ℝ) : ℝ := gammaTriangleConst σ * (1 + gammaMomentConst σ)

theorem laneCenterConst_pos {σ : ℝ} (hσ : 0 < σ) : 0 < laneCenterConst σ := by
  have hmom : 0 < gammaMomentConst σ := gammaMomentConst_pos hσ
  exact mul_pos gammaTriangleConst_pos (by linarith)

theorem integrable_of_isBigO_gammaSigma {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K) (hXm : AEMeasurable X μ)
    (hX : IsBigO μ (gammaSigma σ) X K) : Integrable X μ := by
  have h := integrable_rpow_of_isBigOWith_gammaSigma (μ := μ) (Y := fun ω => |X ω|)
    (K := K) (σ := σ) (p := 1) hσ hK le_rfl (fun ω => abs_nonneg (X ω))
    (continuous_abs.measurable.comp_aemeasurable hXm) hX
  have h' : Integrable (fun ω => |X ω|) μ := by simpa using h
  rw [← MeasureTheory.integrable_norm_iff hXm.aestronglyMeasurable]
  simpa [Real.norm_eq_abs] using h'

theorem abs_integral_le_of_isBigO_gammaSigma {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K) (hXm : AEMeasurable X μ)
    (hX : IsBigO μ (gammaSigma σ) X K) :
    |∫ ω, X ω ∂μ| ≤ gammaMomentConst σ * K := by
  have hmoment := integral_abs_rpow_le_of_isBigO_gammaSigma (μ := μ) (X := X)
    (K := K) (σ := σ) (p := 1) hσ hK le_rfl hXm hX
  have hnorm : |∫ ω, X ω ∂μ| ≤ ∫ ω, |X ω| ∂μ := by
    simpa [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := μ) (f := X)
  refine hnorm.trans ?_
  simpa using hmoment

/-- **Centering costs a constant factor.**  A `Γ_σ` variable stays `Γ_σ` after
subtracting its own mean, at the amplitude `laneCenterConst σ` times the
original one. -/
theorem isBigO_gammaSigma_sub_integral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K) (hXm : AEMeasurable X μ)
    (hX : IsBigO μ (gammaSigma σ) X K) :
    IsBigO μ (gammaSigma σ) (fun ω => X ω - ∫ ω', X ω' ∂μ)
      (laneCenterConst σ * K) := by
  have hM : 0 < gammaMomentConst σ * K := mul_pos (gammaMomentConst_pos hσ) hK
  have hc := abs_integral_le_of_isBigO_gammaSigma hσ hK hXm hX
  have h := HCPolySupport.Book.Ch04.isBigO_gammaSigma_sub_const_of_abs_const_le_aemeasurable
    (μ := μ) (σ := σ) (K := K) (M := gammaMomentConst σ * K)
    (c := ∫ ω, X ω ∂μ) (X := X) hσ hK hM hX hXm hc
  have hscale : gammaTriangleConst σ * (K + gammaMomentConst σ * K)
      = laneCenterConst σ * K := by
    unfold laneCenterConst; ring
  rwa [hscale] at h

theorem integral_sub_integral_eq_zero {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) :
    ∫ ω, (X ω - ∫ ω', X ω' ∂μ) ∂μ = 0 := by
  rw [integral_sub hX (integrable_const _)]
  simp

end Centering

/-! ## The centered lanes -/

section CenteredLanes

/- The sub-σ-algebra `m` is declared before the ambient one, so that `Measure Ω`
and every bare `Measurable` in this section refer to the ambient σ-algebra. -/
variable {Ω : Type*} {m : MeasurableSpace Ω} [MeasurableSpace Ω]

/-- The `Γ_1` lane of the allocation, recentred at its own mean. -/
def centeredLinearLane (μ : Measure Ω) (a b : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => linearLane a b (X ω) - ∫ ω', linearLane a b (X ω') ∂μ

/-- The `Γ_{1/4}` lane of the allocation, recentred at its own mean. -/
def centeredQuarticLane (μ : Measure Ω) (a b : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => quarticLane a b (X ω) - ∫ ω', quarticLane a b (X ω') ∂μ

/-- The `Γ_1` amplitude constant of the centered allocation. -/
def mixedLinearConst (C : ℝ) : ℝ := laneCenterConst 1 * laneAbsorb C

/-- The `Γ_{1/4}` amplitude constant of the centered allocation. -/
def mixedQuarticConst (C : ℝ) : ℝ := laneCenterConst (1 / 4) * laneAbsorb C ^ 4

theorem mixedLinearConst_pos (C : ℝ) : 0 < mixedLinearConst C :=
  mul_pos (laneCenterConst_pos (by norm_num)) (laneAbsorb_pos C)

theorem mixedQuarticConst_pos (C : ℝ) : 0 < mixedQuarticConst C :=
  mul_pos (laneCenterConst_pos (by norm_num)) (pow_pos (laneAbsorb_pos C) 4)

theorem integrable_linearLane_comp {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hXm : Measurable X)
    (hX : HasMixedGammaTailWith μ X C a b) :
    Integrable (fun ω => linearLane a b (X ω)) μ :=
  integrable_of_isBigO_gammaSigma (by norm_num)
    (mul_pos (laneAbsorb_pos C) ha)
    ((measurable_linearLane ha hb).comp hXm).aemeasurable
    (isBigO_gammaSigma_one_linearLane_comp ha hb hX)

theorem integrable_quarticLane_comp {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hXm : Measurable X)
    (hX : HasMixedGammaTailWith μ X C a b) :
    Integrable (fun ω => quarticLane a b (X ω)) μ :=
  integrable_of_isBigO_gammaSigma (by norm_num)
    (mul_pos (pow_pos (laneAbsorb_pos C) 4) hb)
    ((measurable_quarticLane ha hb).comp hXm).aemeasurable
    (isBigO_gammaSigma_quarter_quarticLane_comp ha hb hX)

theorem measurable_centeredLinearLane {μ : Measure Ω}
    {X : Ω → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : Measurable[m] X) :
    Measurable[m] (centeredLinearLane μ a b X) :=
  (measurable_linearLane_comp ha hb hX).sub measurable_const

theorem measurable_centeredQuarticLane {μ : Measure Ω}
    {X : Ω → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : Measurable[m] X) :
    Measurable[m] (centeredQuarticLane μ a b X) :=
  (measurable_quarticLane_comp ha hb hX).sub measurable_const

/-- **The centered linear lane retains the `Γ_1` tail.** -/
theorem isBigO_gammaSigma_one_centeredLinearLane {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hXm : Measurable X) (hX : HasMixedGammaTailWith μ X C a b) :
    IsBigO μ (gammaSigma 1) (centeredLinearLane μ a b X) (mixedLinearConst C * a) := by
  have h := isBigO_gammaSigma_sub_integral (μ := μ) (σ := 1)
    (K := laneAbsorb C * a) (X := fun ω => linearLane a b (X ω)) (by norm_num)
    (mul_pos (laneAbsorb_pos C) ha)
    ((measurable_linearLane ha hb).comp hXm).aemeasurable
    (isBigO_gammaSigma_one_linearLane_comp ha hb hX)
  have hscale : laneCenterConst 1 * (laneAbsorb C * a) = mixedLinearConst C * a := by
    unfold mixedLinearConst; ring
  rwa [hscale] at h

/-- **The centered quartic lane retains the `Γ_{1/4}` tail.** -/
theorem isBigO_gammaSigma_quarter_centeredQuarticLane {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hXm : Measurable X) (hX : HasMixedGammaTailWith μ X C a b) :
    IsBigO μ (gammaSigma (1 / 4)) (centeredQuarticLane μ a b X)
      (mixedQuarticConst C * b) := by
  have h := isBigO_gammaSigma_sub_integral (μ := μ) (σ := 1 / 4)
    (K := laneAbsorb C ^ 4 * b) (X := fun ω => quarticLane a b (X ω)) (by norm_num)
    (mul_pos (pow_pos (laneAbsorb_pos C) 4) hb)
    ((measurable_quarticLane ha hb).comp hXm).aemeasurable
    (isBigO_gammaSigma_quarter_quarticLane_comp ha hb hX)
  have hscale : laneCenterConst (1 / 4) * (laneAbsorb C ^ 4 * b)
      = mixedQuarticConst C * b := by
    unfold mixedQuarticConst; ring
  rwa [hscale] at h

theorem integral_centeredLinearLane_eq_zero {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hXm : Measurable X)
    (hX : HasMixedGammaTailWith μ X C a b) :
    ∫ ω, centeredLinearLane μ a b X ω ∂μ = 0 :=
  integral_sub_integral_eq_zero (integrable_linearLane_comp ha hb hXm hX)

theorem integral_centeredQuarticLane_eq_zero {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hXm : Measurable X)
    (hX : HasMixedGammaTailWith μ X C a b) :
    ∫ ω, centeredQuarticLane μ a b X ω ∂μ = 0 :=
  integral_sub_integral_eq_zero (integrable_quarticLane_comp ha hb hXm hX)

/-- **The centered lanes still split a centered variable exactly.**  The two
mean shifts cancel because the raw lanes sum to `X`, whose mean is zero. -/
theorem centeredLinearLane_add_centeredQuarticLane {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hXm : Measurable X) (hX : HasMixedGammaTailWith μ X C a b)
    (hXmean : ∫ ω, X ω ∂μ = 0) (ω : Ω) :
    X ω = centeredLinearLane μ a b X ω + centeredQuarticLane μ a b X ω := by
  have hLint := integrable_linearLane_comp ha hb hXm hX
  have hQint := integrable_quarticLane_comp ha hb hXm hX
  have hshift : (∫ ω', linearLane a b (X ω') ∂μ) +
      ∫ ω', quarticLane a b (X ω') ∂μ = 0 := by
    rw [← integral_add hLint hQint]
    calc ∫ ω', (linearLane a b (X ω') + quarticLane a b (X ω')) ∂μ
        = ∫ ω', X ω' ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω' => ?_)
          exact linearLane_add_quarticLane ha hb (X ω')
      _ = 0 := hXmean
  have hpoint : linearLane a b (X ω) + quarticLane a b (X ω) = X ω :=
    linearLane_add_quarticLane ha hb (X ω)
  unfold centeredLinearLane centeredQuarticLane
  linarith [hpoint, hshift]

end CenteredLanes

/-! ## The packaged two-lane split -/

section Split

/-- **The deterministic mixed two-lane Orlicz allocation.**

A centered variable with a two-term `(Γ_1, Γ_{1/4})` tail at amplitudes
`(a, b)` and tail constant `C` splits into two centered summands, each a fixed
Borel function of the variable minus a constant, hence measurable for every
σ-field the variable is measurable for, and each carrying a single-lane
weak-Orlicz bound at its own exponent and its own amplitude.  This is exactly
the input format consumed by the two-lane grid concentration display: the two
lanes may be fed independently to the one-exponent concentration inequality,
and the pointwise identity recombines them.

The witnesses are the explicit `centeredLinearLane` and `centeredQuarticLane`;
the uncentered core, its explicit mean shifts, and the per-lane statements are
available separately in this module. -/
theorem exists_centeredTwoLaneSplit {Ω : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {C a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hXloc : Measurable[m] X) (hXmeas : Measurable X)
    (hXtail : HasMixedGammaTailWith μ X C a b) (hXmean : ∫ ω, X ω ∂μ = 0) :
    ∃ Y Z : Ω → ℝ,
      (∀ ω, X ω = Y ω + Z ω) ∧
        Measurable[m] Y ∧ Measurable[m] Z ∧ Measurable Y ∧ Measurable Z ∧
          IsBigO μ (gammaSigma 1) Y (mixedLinearConst C * a) ∧
            IsBigO μ (gammaSigma (1 / 4)) Z (mixedQuarticConst C * b) ∧
              (∫ ω, Y ω ∂μ = 0) ∧ (∫ ω, Z ω ∂μ = 0) :=
  ⟨centeredLinearLane μ a b X, centeredQuarticLane μ a b X,
    centeredLinearLane_add_centeredQuarticLane ha hb hXmeas hXtail hXmean,
    measurable_centeredLinearLane ha hb hXloc,
    measurable_centeredQuarticLane ha hb hXloc,
    measurable_centeredLinearLane ha hb hXmeas,
    measurable_centeredQuarticLane ha hb hXmeas,
    isBigO_gammaSigma_one_centeredLinearLane ha hb hXmeas hXtail,
    isBigO_gammaSigma_quarter_centeredQuarticLane ha hb hXmeas hXtail,
    integral_centeredLinearLane_eq_zero ha hb hXmeas hXtail,
    integral_centeredQuarticLane_eq_zero ha hb hXmeas hXtail⟩

/-- The same split, fed by the proved two-term weak-Orlicz vocabulary: a two-term
one-sided bound for `|X|` at exponents `1` and `1/4` and amplitudes `(A₁, A₄)`
is enough, the tail constant then being `2`. -/
theorem exists_centeredTwoLaneSplit_of_isTwoTermBigOWith_abs {Ω : Type*}
    {m : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {A₁ A₄ : ℝ} (hA₁ : 0 < A₁) (hA₄ : 0 < A₄)
    (hXloc : Measurable[m] X) (hXmeas : Measurable X)
    (hXtail : Probability.IsTwoTermBigOWith μ (gammaSigma 1) (gammaSigma (1 / 4))
      (fun ω => |X ω|) A₁ A₄)
    (hXmean : ∫ ω, X ω ∂μ = 0) :
    ∃ Y Z : Ω → ℝ,
      (∀ ω, X ω = Y ω + Z ω) ∧
        Measurable[m] Y ∧ Measurable[m] Z ∧ Measurable Y ∧ Measurable Z ∧
          IsBigO μ (gammaSigma 1) Y (mixedLinearConst 2 * A₁) ∧
            IsBigO μ (gammaSigma (1 / 4)) Z (mixedQuarticConst 2 * A₄) ∧
              (∫ ω, Y ω ∂μ = 0) ∧ (∫ ω, Z ω ∂μ = 0) :=
  exists_centeredTwoLaneSplit hA₁ hA₄ hXloc hXmeas
    (hasMixedGammaTailWith_two_of_isTwoTermBigOWith_abs hXtail) hXmean

end Split

end

end Algsuperdiff.Section3.Provider.Orlicz
