/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Scalar Grönwall estimate for vorticity energy

This scalar estimate is the time integration step in the smooth energy argument
for `lem:localized-vorticity-energy`.
-/

public section


open MeasureTheory Set
open scoped Interval

namespace ESS

/-- A nonnegative energy with a differential upper bound has the expected
exponential control by its initial value and the total forcing. -/
theorem vorticityEnergyGronwallCore {a b K e₀ : ℝ} {e de f : ℝ → ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hecont : ContinuousOn e (Icc a b))
    (hfcont : Continuous f)
    (hepos : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hfpos : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hederiv : ∀ t ∈ Ico a b, HasDerivAt e (de t) t)
    (hineq : ∀ t ∈ Ico a b, de t ≤ K * e t + f t)
    (hinit : e a ≤ e₀) :
    ∀ t ∈ Icc a b,
      e t ≤ Real.exp (K * (b - a)) * (e₀ + ∫ s in a..b, f s) := by
  let F := fun t => ∫ x in a..t, f x
  let g := fun t => e t + (∫ x in a..b, f x) - F t
  have hfint : IntervalIntegrable f volume a b := hfcont.intervalIntegrable a b
  have hFcont : ContinuousOn F (Icc a b) := by
    rw [← uIcc_of_le hab]
    exact intervalIntegral.continuousOn_primitive_interval' hfint left_mem_uIcc
  have hgcont : ContinuousOn g (Icc a b) := by
    change ContinuousOn (fun t => (e t + ∫ x in a..b, f x) - F t) (Icc a b)
    exact (hecont.add continuousOn_const).sub hFcont
  have hsplit (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x in a..b, f x) = (∫ x in a..t, f x) + (∫ x in t..b, f x) := by
    have h1 : IntervalIntegrable f volume a t := hfcont.intervalIntegrable a t
    have h2 : IntervalIntegrable f volume t b := hfcont.intervalIntegrable t b
    exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hge (t : ℝ) (ht : t ∈ Icc a b) : e t ≤ g t := by
    have htail : 0 ≤ ∫ x in t..b, f x := by
      apply intervalIntegral.integral_nonneg ht.2
      intro x hx
      exact hfpos x ⟨le_trans ht.1 hx.1, hx.2⟩
    have hs := hsplit t ht
    dsimp [g, F]
    rw [hs]
    linarith only [htail]
  have hgderiv : ∀ t ∈ Ico a b, HasDerivAt g (de t - f t) t := by
    intro t ht
    have hFderiv : HasDerivAt F (f t) t := by
      simpa [F] using hfcont.integral_hasStrictDerivAt a t |>.hasDerivAt
    have he := hederiv t ht
    change HasDerivAt
      (fun s => (e s + ∫ x in a..b, f x) - ∫ x in a..s, f x)
      (de t - f t) t
    convert he.add ((hasDerivAt_const t (∫ x in a..b, f x)).sub hFderiv) using 1
    · ext s
      simp [F]
      ring
    · ring
  have hgbound : ∀ t ∈ Ico a b, de t - f t ≤ K * g t := by
    intro t ht
    have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    have h := hineq t ht
    have hge' := hge t htcc
    have hf := hfpos t htcc
    have hKg : K * e t ≤ K * g t := mul_le_mul_of_nonneg_left hge' hK
    linarith only [h, hKg, hf]
  have hginit : g a ≤ e₀ + ∫ x in a..b, f x := by
    have hfa : (∫ x in a..a, f x) = 0 := intervalIntegral.integral_same
    dsimp [g, F]
    rw [hfa]
    linarith only [hinit]
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (ε := 0) hgcont
    (fun t ht r hr => (hgderiv t ht).hasDerivWithinAt.liminf_right_slope_le hr)
    hginit (fun t ht => by simpa using hgbound t ht)
  intro t ht
  have hgt := hge t ht
  have hgrBound := hgr t ht
  rw [gronwallBound_ε0] at hgrBound
  have htime : K * (t - a) ≤ K * (b - a) := by
    gcongr
    exact ht.2
  have hExpMono : Real.exp (K * (t - a)) ≤ Real.exp (K * (b - a)) :=
    Real.exp_le_exp.mpr htime
  have hbase : 0 ≤ e₀ + ∫ x in a..b, f x := by
    have he0 : 0 ≤ e a := hepos a ⟨le_rfl, hab⟩
    have htotal : 0 ≤ ∫ x in a..b, f x := by
      apply intervalIntegral.integral_nonneg hab
      intro x hx
      exact hfpos x hx
    linarith only [he0, hinit, htotal]
  calc
    e t ≤ g t := hgt
    _ ≤ (e₀ + ∫ x in a..b, f x) * Real.exp (K * (t - a)) := by
      simpa [mul_comm] using hgrBound
    _ ≤ Real.exp (K * (b - a)) * (e₀ + ∫ x in a..b, f x) := by
      calc
        _ = (e₀ + ∫ x in a..b, f x) * Real.exp (K * (t - a)) := rfl
        _ ≤ (e₀ + ∫ x in a..b, f x) * Real.exp (K * (b - a)) :=
          mul_le_mul_of_nonneg_left hExpMono hbase
        _ = _ := by ring

/-- The scalar differential energy inequality controls both the supremum of
the energy and the time integral of a nonnegative dissipation term. -/
theorem vorticityEnergyGronwallDissipation {a b K e₀ : ℝ}
    {e de d f : ℝ → ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hecont : ContinuousOn e (Icc a b))
    (hdecont : Continuous de) (hdcont : Continuous d) (hfcont : Continuous f)
    (hepos : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hdpos : ∀ t ∈ Icc a b, 0 ≤ d t)
    (hfpos : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hederiv : ∀ t ∈ Ico a b, HasDerivAt e (de t) t)
    (hineq : ∀ t ∈ Icc a b, de t + d t ≤ K * e t + f t)
    (hinit : e a ≤ e₀) :
    (∀ t ∈ Icc a b,
      e t ≤ Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) ∧
    (∫ t in a..b, d t ≤
      e₀ + K * (b - a) *
        (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
          (∫ s in a..b, f s)) := by
  have hdeineq : ∀ t ∈ Ico a b, de t ≤ K * e t + f t := by
    intro t ht
    have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    have h := hineq t htcc
    have hd := hdpos t htcc
    linarith only [h, hd]
  have henergy := vorticityEnergyGronwallCore hab hK hecont hfcont hepos hfpos
    hederiv hdeineq hinit
  have hdeint : IntervalIntegrable de volume a b := hdecont.intervalIntegrable a b
  have hdint : IntervalIntegrable d volume a b := hdcont.intervalIntegrable a b
  have hfint : IntervalIntegrable f volume a b := hfcont.intervalIntegrable a b
  have heint : IntervalIntegrable e volume a b := by
    exact hecont.intervalIntegrable_of_Icc hab
  have hFTC : (∫ t in a..b, de t) = e b - e a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hecont
      (fun t ht => hederiv t ⟨le_of_lt ht.1, ht.2⟩) hdeint
  have hpoint : ∀ t ∈ Icc a b, d t + de t ≤ K * e t + f t := by
    intro t ht
    simpa [add_comm] using hineq t ht
  have hrightCont : ContinuousOn (fun t => K * e t + f t) (Icc a b) := by
    exact (continuousOn_const.mul hecont).add hfcont.continuousOn
  have hrightInt : IntervalIntegrable (fun t => K * e t + f t) volume a b :=
    hrightCont.intervalIntegrable_of_Icc hab
  have hKint : (∫ t in a..b, K * e t) = K * ∫ t in a..b, e t := by
    exact intervalIntegral.integral_const_mul K e
  have hint : (∫ t in a..b, d t) + (∫ t in a..b, de t) ≤
      K * (∫ t in a..b, e t) + (∫ t in a..b, f t) := by
    calc
      _ = ∫ t in a..b, (d t + de t) := by
        rw [intervalIntegral.integral_add hdint hdeint]
      _ ≤ ∫ t in a..b, (K * e t + f t) :=
        intervalIntegral.integral_mono_on hab
          ((hdcont.add hdecont).intervalIntegrable a b) hrightInt
          (fun t ht => by simpa [add_comm] using hpoint t ht)
      _ = K * (∫ t in a..b, e t) + (∫ t in a..b, f t) := by
        calc
          _ = (∫ t in a..b, K * e t) + (∫ t in a..b, f t) :=
            intervalIntegral.integral_add (heint.const_mul K) hfint
          _ = K * (∫ t in a..b, e t) + (∫ t in a..b, f t) :=
            congrArg (fun x => x + (∫ t in a..b, f t)) hKint
  have hIntE : ∫ t in a..b, e t ≤
      (b - a) * (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) := by
    calc
      _ ≤ ∫ t in a..b,
          (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) :=
        intervalIntegral.integral_mono_on hab heint
          (continuousOn_const.intervalIntegrable_of_Icc hab)
          (fun t ht => henergy t ht)
      _ = (b - a) * (Real.exp (K * (b - a)) *
          (e₀ + (∫ s in a..b, f s))) := by
        rw [intervalIntegral.integral_const]
        ring
  have hfinal : ∫ t in a..b, d t ≤
      e₀ + K * (b - a) *
        (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
          (∫ s in a..b, f s) := by
    rw [hFTC] at hint
    have hbnonneg : 0 ≤ e b := hepos b ⟨hab, le_rfl⟩
    have he0bound : e a ≤ e₀ := hinit
    have hKmul := mul_le_mul_of_nonneg_left hIntE hK
    have hKmul' : K * (∫ t in a..b, e t) ≤
        K * (b - a) * (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) := by
      calc
        _ ≤ K * ((b - a) *
            (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s)))) := hKmul
        _ = _ := by ring
    have hstep₁ : ∫ t in a..b, d t ≤
        (K * (∫ t in a..b, e t) + (∫ t in a..b, f t)) + (e a - e b) := by
      linarith only [hint]
    have hstep₂ : (K * (∫ t in a..b, e t) + (∫ t in a..b, f t)) +
        (e a - e b) ≤
        e₀ + K * (b - a) *
          (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
            (∫ s in a..b, f s) := by
      calc
        _ = K * (∫ t in a..b, e t) + ((∫ s in a..b, f s) + (e a - e b)) := by ring_nf
        _ ≤ K * (b - a) *
            (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
              ((∫ s in a..b, f s) + (e a - e b)) :=
          add_le_add_left hKmul' _
        _ = (K * (b - a) *
            (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
              (∫ s in a..b, f s)) + (e a - e b) := by ring_nf
        _ ≤ _ := by linarith only [hbnonneg, he0bound]
    calc
      _ ≤ (K * (∫ t in a..b, e t) + (∫ t in a..b, f t)) + (e a - e b) := hstep₁
      _ ≤ e₀ + K * (b - a) *
          (Real.exp (K * (b - a)) * (e₀ + (∫ s in a..b, f s))) +
            (∫ s in a..b, f s) := hstep₂
  exact ⟨henergy, hfinal⟩

end ESS
