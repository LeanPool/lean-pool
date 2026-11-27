/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module

public import LeanPool.VenNullClockRoundRates.RoundAreaPositiveStrips
public import LeanPool.VenNullClockRoundRates.VenRateUpperAssembly
public import LeanPool.VenNullClockRoundRates.VenRateUpperBump
public import LeanPool.VenNullClockRoundRates.Layer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The common-profile upper rate on the normalized Euclidean round sphere. -/

@[expose] public section

open MeasureTheory VenMask VenRate
open scoped ContDiff

namespace VenRateUpper

private theorem first_coordinate_bound (y : UnitSphere) : y.val.1 ∈ Set.Icc (-1 : ℝ) 1 := by
  have hs : y.val.1 ^ 2 ≤ 1 := by
    nlinarith only [y.property, sq_nonneg y.val.2.1, sq_nonneg y.val.2.2]
  apply abs_le.mp
  by_contra! H
  have hsq : 1 < |y.val.1|^2 := by
    nlinarith only [mul_pos (sub_pos.mpr H) (show 0 < |y.val.1| + 1 by linarith only [H])]
  rw [sq_abs] at hsq
  exact (not_lt_of_ge hs) hsq

private theorem spherical_read_gap_bound {θ b : ℝ} (hb : 0 ≤ b) (y : UnitSphere) :
    |sphereReadGap θ b y| ≤ Real.exp b := by
  obtain ⟨h₀, h₁⟩ := en_bounds θ y
  have hp : Real.exp (b * secondEnergy θ y) ≤ Real.exp b :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right hb h₁.2)
  have hm : Real.exp (b * firstEnergy y) ≤ Real.exp b :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right hb h₀.2)
  change |Real.exp (b * secondEnergy θ y) - Real.exp (b * firstEnergy y)| ≤ _
  exact abs_le.mpr ⟨by linarith only [hm, Real.exp_pos (b * secondEnergy θ y)],
    by linarith only [hp, Real.exp_pos (b * firstEnergy y)]⟩

/-- Proposition 5. One smooth ambient restriction supplies both profiles and
satisfies the pointwise floor and cap on the unit sphere. -/
theorem smooth_round_common_profile_upper {a b θ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < 1 - Real.cos θ ^ 2) :
    ∃ c M₁ : ℝ, 0 < c ∧ 1 < M₁ ∧ ∀ M ≥ M₁,
      ∃ W : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ W ∧
        (∀ y : UnitSphere, 2 ≤ W y.val ∧ W y.val ≤ M) ∧
        DataClose roundArea (fun y => W y.val) (fun y => W y.val) θ b a
          (Real.exp (-c * Real.log M * Real.log (Real.log M))) := by
  obtain ⟨l, r, Aplus, Aminus, hl, hlr, hr, _hAp, _hAm, η, hη, hηc, hη₁,
    chiPlus, chiMinus, hchiPlus, hchiMinus, bddPlus, bddMinus, _disjoint, pushPlus, pushMinus⟩ :=
      exists_smooth_strip_cutoffs hθ hb
  let t₁ := (l + r) / 2
  let ℓ := (r - l) / 4
  have hl₁ : l < t₁ := by dsimp [t₁]; linarith only [hlr]
  have hℓ : 0 < ℓ := by dsimp [ℓ]; linarith only [hlr]
  have hsum : t₁ + ℓ ≤ r := by dsimp [t₁, ℓ]; linarith only [hlr]
  obtain ⟨ψ, B, _hB, hψ, normψ, _compactψ, supportψ, _positiveψ, supψ⟩ :=
    exists_normalized_interval_bump hl₁
  have ψSupport : ∀ t ∉ Set.Icc l t₁, ψ t = 0 := by
    intro t ht
    by_contra ne
    have h := supportψ (subset_tsupport ψ ne)
    exact ht ⟨h.1.le, h.2.le⟩
  have ηOne (x : ℝ) (hx : x ∈ Set.Icc l (t₁ + ℓ)) : η x = 1 :=
    hη₁ x ⟨hx.1, hx.2.trans hsum⟩
  have hy : Continuous (fun y : UnitSphere => y.val) := continuous_subtype_val
  have hheight : Continuous (fun y : UnitSphere => y.val.1) := continuous_fst.comp hy
  have hq : Continuous (sphereReadGap θ b) := by
    change Continuous (fun y : UnitSphere =>
      Real.exp (b * secondEnergy θ y) - Real.exp (b * firstEnergy y))
    exact (Real.continuous_exp.comp (continuous_const.mul (second_cont θ))).sub
      (Real.continuous_exp.comp (continuous_const.mul first_cont))
  obtain ⟨c, M₁, hc, hM₁, proof⟩ := exponential_upper_of_twoStripIdentities
    (F := firstEnergy) (H := fun y => y.val.1) (q := sphereReadGap θ b)
    (chiPlus := fun y => chiPlus y.val) (chiMinus := fun y => chiMinus y.val) roundArea
    first_cont hheight hq (hchiPlus.continuous.comp hy) (hchiMinus.continuous.comp hy)
    hη.continuous hηc hψ normψ supψ ψSupport hℓ (by linarith only [hl]) (hsum.trans hr.le)
    ηOne (fun y => (en_bounds θ y).1) first_coordinate_bound (fun _ => rfl)
    (spherical_read_gap_bound hb.le) bddPlus bddMinus (Real.exp_pos b).le ha.le
    pushPlus pushMinus
  refine ⟨c, M₁, hc, hM₁,?_⟩
  intro M hM
  obtain ⟨ρ, K, hρ, bdd, rate⟩ := proof M hM
  let W := twoStripProfile Prod.fst chiPlus chiMinus ρ K
  have hW : ContDiff ℝ ∞ W := contDiff_twoStripProfile contDiff_fst hchiPlus hchiMinus hρ
  refine ⟨W, hW, fun y => bdd y,?_⟩
  intro x hx
  have positiveRate : 0 ≤ Real.exp (-c * Real.log M * Real.log (Real.log M)) :=
    (Real.exp_pos _).le
  constructor
  · simpa only [layer, tilt, zero_mul, Real.exp_zero, mul_one, sub_self, abs_zero] using
    positiveRate
  · let w := fun y : UnitSphere => W y.val
    have hcont : Continuous w := hW.continuous.comp hy
    have hi (G : UnitSphere → ℝ) (hG : Continuous G) :
        Integrable (fun y => tilt w G b y * Real.exp (x * firstEnergy y)) roundArea := by
      have continuousTerm : Continuous (fun y => tilt w G b y * Real.exp (x * firstEnergy y)) :=
        (hcont.mul (Real.continuous_exp.comp (continuous_const.mul hG))).mul
          (Real.continuous_exp.comp (continuous_const.mul first_cont))
      exact continuousTerm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change |layer roundArea w (secondEnergy θ) b x - layer roundArea w firstEnergy b x| ≤ _
    have diff : layer roundArea w (secondEnergy θ) b x - layer roundArea w firstEnergy b x =
        ∫ y, (sphereReadGap θ b y * w y) * Real.exp (x * firstEnergy y) ∂roundArea := by
      unfold layer
      rw [← integral_sub (hi _ (second_cont θ)) (hi _ first_cont)]
      apply integral_congr_ae
      filter_upwards with y
      change tilt w (secondEnergy θ) b y * Real.exp (x * firstEnergy y) -
        tilt w firstEnergy b y * Real.exp (x * firstEnergy y) = _
      unfold tilt sphereReadGap
      ring
    rw [diff]
    exact rate x hx

end VenRateUpper
