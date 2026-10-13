/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicSphereRadial

/-!
# HarmonicSphereProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The radial profile that solves the radial Laplace equation

Given a continuous radial density `k` supported in an annulus `[a, b]` with
`0 < a < b`, the ordinary differential equation
`Psi'' + m * Psi' / t = k` in dimension `d = m + 1` is solved in closed form by

```
  Q t = int_0^t s^m k s ds ,   P t = Q t / t^m ,   Psi t = int_b^t P s ds .
```

`Q` vanishes below `a`, so `P` and hence `Psi'` vanish there and `Psi` is
constant near the origin; and if the **radial moment** `Q b` vanishes, then `P`
vanishes above `b` as well and `Psi` vanishes identically above `b`.  The
resulting profile is therefore constant near `0`, compactly supported, and `C^2`
on `(0, ∞)` -- exactly the input that the radial Laplacian of
`HarmonicSphereRadial` and the Green pairing of `HarmonicGreen` consume.

This module builds the three functions and proves their derivative, support and
regularity properties.  Nothing here is about harmonic functions.

## Contents

* `radialMoment`, `radialSlope`, `radialPotential` -- the three functions.
* `hasDerivAt_radialMoment`, `hasDerivAt_radialSlope`,
  `hasDerivAt_radialPotential` -- their derivatives, the middle one being the
  explicit `P' t = k t - m * Q t / t^(m+1)`.
* `radialMoment_eq_zero_of_le`, `radialMoment_eq_of_ge`,
  `radialSlope_eq_zero_of_le`, `radialSlope_eq_zero_of_ge`,
  `radialPotential_eq_zero_of_ge`, `radialPotential_eq_of_le` -- the support
  and constancy statements.
* `continuous_radialSlope`, `contDiffAt_radialPotential` -- regularity.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {m : ℕ} {k : ℝ → ℝ} {a b : ℝ}

noncomputable def radialMoment (m : ℕ) (k : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, s ^ m * k s

/-- The radial derivative determined by the moment. -/
noncomputable def radialSlope (m : ℕ) (k : ℝ → ℝ) (t : ℝ) : ℝ := radialMoment m k t / t ^ m

/-- The radial primitive normalized to vanish at radius `b`. -/
noncomputable def radialPotential (m : ℕ) (k : ℝ → ℝ) (b t : ℝ) : ℝ :=
  ∫ s in b..t, radialSlope m k s

theorem hasDerivAt_radialMoment (hk : Continuous k) (t : ℝ) :
    HasDerivAt (radialMoment m k) (t ^ m * k t) t := by
  have hcont : Continuous fun s : ℝ => s ^ m * k s := (continuous_pow m).mul hk
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

theorem continuous_radialMoment (hk : Continuous k) : Continuous (radialMoment m k) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_radialMoment hk t).continuousAt

theorem radialMoment_eq_zero_of_le (ha : 0 ≤ a) (hk0 : ∀ s : ℝ, s ≤ a → k s = 0)
    {t : ℝ} (ht : t ≤ a) : radialMoment m k t = 0 := by
  have heq : Set.EqOn (fun s : ℝ => s ^ m * k s) (fun _ : ℝ => 0) (Set.uIcc 0 t) := by
    intro s hs
    have hsa : s ≤ a := by
      rcases Set.mem_uIcc.mp hs with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact le_trans h2 ht
      · exact le_trans h2 ha
    simp [hk0 s hsa]
  rw [radialMoment, intervalIntegral.integral_congr heq]
  simp

theorem radialMoment_eq_of_ge (hk : Continuous k) (hkb : ∀ s : ℝ, b ≤ s → k s = 0)
    {t : ℝ} (ht : b ≤ t) : radialMoment m k t = radialMoment m k b := by
  have hcont : Continuous fun s : ℝ => s ^ m * k s := (continuous_pow m).mul hk
  have heq : Set.EqOn (fun s : ℝ => s ^ m * k s) (fun _ : ℝ => 0) (Set.uIcc b t) := by
    intro s hs
    have hbs : b ≤ s := by
      rcases Set.mem_uIcc.mp hs with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exact le_trans ht h1
    simp [hkb s hbs]
  have hzero : ∫ s in b..t, s ^ m * k s = 0 := by
    rw [intervalIntegral.integral_congr heq]
    simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (f := fun s : ℝ => s ^ m * k s) (a := 0) (b := b) (c := t)
    (hcont.intervalIntegrable 0 b) (hcont.intervalIntegrable b t)
  rw [radialMoment, radialMoment, ← hsplit, hzero, add_zero]

theorem radialSlope_eq_zero_of_le (ha : 0 ≤ a) (hk0 : ∀ s : ℝ, s ≤ a → k s = 0)
    {t : ℝ} (ht : t ≤ a) : radialSlope m k t = 0 := by
  rw [radialSlope, radialMoment_eq_zero_of_le ha hk0 ht, zero_div]

theorem radialSlope_eq_zero_of_ge (hk : Continuous k) (hkb : ∀ s : ℝ, b ≤ s → k s = 0)
    (hmom : radialMoment m k b = 0) {t : ℝ} (ht : b ≤ t) : radialSlope m k t = 0 := by
  rw [radialSlope, radialMoment_eq_of_ge hk hkb ht, hmom, zero_div]

theorem continuous_radialSlope (hk : Continuous k) (ha : 0 < a)
    (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) : Continuous (radialSlope m k) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  rcases lt_or_ge 0 t with ht | ht
  · exact ContinuousAt.div (continuous_radialMoment hk).continuousAt
      (continuous_pow m).continuousAt (pow_ne_zero _ (ne_of_gt ht))
  · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds t] radialSlope m k := by
      refine Filter.eventuallyEq_of_mem (s := Set.Iio a)
        (isOpen_Iio.mem_nhds (lt_of_le_of_lt ht ha)) ?_
      intro s hs
      exact (radialSlope_eq_zero_of_le ha.le hk0 (le_of_lt hs)).symm
    exact ContinuousAt.congr continuousAt_const heq

theorem hasDerivAt_radialSlope (hk : Continuous k) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (radialSlope m k) (k t - (m : ℝ) * radialMoment m k t / t ^ (m + 1)) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpm : (t : ℝ) ^ m ≠ 0 := pow_ne_zero _ ht0
  have hpow : (m : ℝ) * t ^ (m - 1) * t = (m : ℝ) * t ^ m := by
    cases m with
    | zero => simp
    | succ m' =>
      have hsub : m' + 1 - 1 = m' := rfl
      rw [hsub, pow_succ]
      ring
  refine ((hasDerivAt_radialMoment (m := m) hk t).div (hasDerivAt_pow m t) hpm).congr_deriv ?_
  field_simp
  linear_combination (-(radialMoment m k t) * t ^ m) * hpow

theorem hasDerivAt_radialPotential (hk : Continuous k) (ha : 0 < a)
    (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) (b t : ℝ) :
    HasDerivAt (radialPotential m k b) (radialSlope m k t) t := by
  have hcont := continuous_radialSlope (m := m) hk ha hk0
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable b t)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

theorem radialPotential_eq_zero_of_ge (hk : Continuous k) (hkb : ∀ s : ℝ, b ≤ s → k s = 0)
    (hmom : radialMoment m k b = 0) {t : ℝ} (ht : b ≤ t) : radialPotential m k b t = 0 := by
  have heq : Set.EqOn (radialSlope m k) (fun _ : ℝ => 0) (Set.uIcc b t) := by
    intro s hs
    have hbs : b ≤ s := by
      rcases Set.mem_uIcc.mp hs with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exact le_trans ht h1
    exact radialSlope_eq_zero_of_ge hk hkb hmom hbs
  rw [radialPotential, intervalIntegral.integral_congr heq]
  simp

theorem radialPotential_eq_of_le (hk : Continuous k) (ha : 0 < a)
    (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) {t : ℝ} (ht : t ≤ a) :
    radialPotential m k b t = radialPotential m k b 0 := by
  have hcont := continuous_radialSlope (m := m) hk ha hk0
  have heq : Set.EqOn (radialSlope m k) (fun _ : ℝ => 0) (Set.uIcc 0 t) := by
    intro s hs
    have hsa : s ≤ a := by
      rcases Set.mem_uIcc.mp hs with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact le_trans h2 ht
      · exact le_trans h2 ha.le
    exact radialSlope_eq_zero_of_le ha.le hk0 hsa
  have hzero : ∫ s in (0 : ℝ)..t, radialSlope m k s = 0 := by
    rw [intervalIntegral.integral_congr heq]
    simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (f := radialSlope m k) (a := b) (b := 0) (c := t)
    (hcont.intervalIntegrable b 0) (hcont.intervalIntegrable 0 t)
  rw [radialPotential, radialPotential, ← hsplit, hzero, add_zero]

theorem contDiffAt_radialPotential (hk : Continuous k) (ha : 0 < a)
    (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) (b : ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (radialPotential m k b) t := by
  have hslope : ContDiffOn ℝ 1 (radialSlope m k) (Set.Ioi 0) := by
    have hone : ((1 : WithTop ℕ∞)) = 0 + 1 := by norm_num
    rw [hone, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun s hs => ((hasDerivAt_radialSlope hk hs).differentiableAt).differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    rw [contDiffOn_zero]
    refine ContinuousOn.congr (f := fun s : ℝ => k s - (m : ℝ) * radialMoment m k s / s ^ (m + 1))
      ?_ ?_
    · exact hk.continuousOn.sub
        (((continuous_const.mul (continuous_radialMoment hk)).continuousOn).div
          (continuous_pow _).continuousOn fun s hs => pow_ne_zero _ (ne_of_gt hs))
    · intro s hs
      exact (hasDerivAt_radialSlope hk hs).deriv
  have hpot : ContDiffOn ℝ 2 (radialPotential m k b) (Set.Ioi 0) := by
    have htwo : ((2 : WithTop ℕ∞)) = 1 + 1 := by norm_num
    rw [htwo, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun s _ =>
      ((hasDerivAt_radialPotential hk ha hk0 b s).differentiableAt).differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    refine hslope.congr fun s _ => ?_
    exact (hasDerivAt_radialPotential hk ha hk0 b s).deriv
  exact hpot.contDiffAt (isOpen_Ioi.mem_nhds ht)

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
