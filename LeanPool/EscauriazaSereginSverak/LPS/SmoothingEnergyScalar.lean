/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Scalar high-order energy bounds

The corrected high-order inequality in `eq:lps-Hm-energy` dissipates the
spatial-gradient Sobolev norm. The lemmas here isolate its Young inequality
and integrating-factor estimates for the regularized smoothing argument.
-/

public section

open MeasureTheory Set
open scoped Interval


noncomputable section

namespace ESS

/-- Young's inequality turns the regularized transport pairing
into the corrected spatial-gradient dissipation (eq:lps-Hm-energy). -/
theorem lps_corrected_energy_from_transport
    {A B C K E' : ℝ}
    (hheat : E' + 2 * B ^ 2 ≤ 2 * K)
    (htransport : K ≤ C * A ^ 2 * B) :
    E' + B ^ 2 ≤ C ^ 2 * A ^ 4 := by
  have hsq := sq_nonneg (B - C * A ^ 2)
  nlinarith only [hheat, htransport, hsq]

/-- The transport-tensor estimate and the heat identity yield exactly the
corrected inhomogeneous `H^m` energy inequality (`eq:lps-Hm-energy`). -/
theorem lps_corrected_energy_from_tensor
    {E' D N C K : ℝ}
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hheat : E' + 2 * D ≤ 2 * K)
    (htransport : K ≤ Real.sqrt C * N * Real.sqrt D) :
    E' + D ≤ C * N ^ 2 := by
  have h := lps_corrected_energy_from_transport
    (A := Real.sqrt N) (B := Real.sqrt D)
    (C := Real.sqrt C) (K := K) (E' := E')
    (by simpa only [Real.sq_sqrt hD] using hheat)
    (by simpa only [Real.sq_sqrt hN] using htransport)
  have hNpow : Real.sqrt N ^ 4 = N ^ 2 := by
    calc
      Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 := by ring
      _ = N ^ 2 := by rw [Real.sq_sqrt hN]
  simpa only [Real.sq_sqrt hD, Real.sq_sqrt hC, hNpow] using h

/-- The scalar integrating-factor step used by the corrected
high-order energy estimate (eq:lps-Hm-energy). -/
theorem lps_high_order_energy_gronwall
    {a T C : ℝ} {y dy d b : ℝ → ℝ}
    (haT : a ≤ T) (hy : Continuous y) (hb : Continuous b)
    (hderiv : ∀ t ∈ Ioo a T, HasDerivAt y (dy t) t)
    (hd : ∀ t ∈ Ioo a T, 0 ≤ d t)
    (henergy : ∀ t ∈ Ioo a T, dy t + d t ≤ C * b t * y t) :
    ∀ t ∈ Icc a T,
      y t ≤ y a * Real.exp (C * ∫ s in a..t, b s) := by
  let B : ℝ → ℝ := fun t => ∫ s in a..t, b s
  let F : ℝ → ℝ := fun t => y t * Real.exp (-C * B t)
  have hB (t : ℝ) : HasDerivAt B (b t) t := by
    exact (hb.integral_hasStrictDerivAt a t).hasDerivAt
  have hBcont : Continuous B := by
    exact continuous_iff_continuousAt.mpr fun t => (hB t).continuousAt
  have hFcont : Continuous F := by
    have hargcont : Continuous (fun t => -C * B t) := continuous_const.mul hBcont
    exact hy.mul (Real.continuous_exp.comp hargcont)
  have hFderiv (t : ℝ) (ht : t ∈ Ioo a T) :
      HasDerivAt F
        (dy t * Real.exp (-C * B t) +
          y t * (Real.exp (-C * B t) * (-C * b t))) t := by
    have harg : HasDerivAt (fun s => -C * B s) (-C * b t) t :=
      (hB t).const_mul (-C)
    have hexp := (Real.hasDerivAt_exp (-C * B t)).comp t harg
    exact (hderiv t ht).mul hexp
  have hFnonpos (t : ℝ) (ht : t ∈ Ioo a T) :
      dy t * Real.exp (-C * B t) +
        y t * (Real.exp (-C * B t) * (-C * b t)) ≤ 0 := by
    have hbase : dy t - C * b t * y t ≤ 0 := by
      linarith only [henergy t ht, hd t ht]
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos (-C * B t))) hbase
    calc
      dy t * Real.exp (-C * B t) +
          y t * (Real.exp (-C * B t) * (-C * b t))
          = Real.exp (-C * B t) * (dy t - C * b t * y t) := by ring
      _ ≤ 0 := hmul
  have hanti : AntitoneOn F (Icc a T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a T) hFcont.continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hFderiv t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hFnonpos t ht
  intro t ht
  have hFa : F a = y a := by simp [F, B]
  have hFt : F t ≤ y a := by
    simpa [hFa] using hanti ⟨le_rfl, haT⟩ ht ht.1
  have hEq : y t = F t * Real.exp (C * B t) := by
    calc
      y t = y t * (Real.exp (-C * B t) * Real.exp (C * B t)) := by
        rw [← Real.exp_add]
        have : -C * B t + C * B t = 0 := by ring
        rw [this, Real.exp_zero, mul_one]
      _ = F t * Real.exp (C * B t) := by ring
  calc
    y t = F t * Real.exp (C * B t) := hEq
    _ ≤ y a * Real.exp (C * B t) :=
      mul_le_mul_of_nonneg_right hFt (Real.exp_pos _).le
    _ = y a * Real.exp (C * ∫ s in a..t, b s) := rfl


/-- The corrected high-order energy inequality controls both the energy
and the integrated spatial-gradient dissipation (eq:lps-Hm-energy). -/
theorem lps_high_order_energy_dissipation_gronwall
    {a T C : ℝ} {y dy d b : ℝ → ℝ}
    (haT : a ≤ T) (hC : 0 ≤ C)
    (hy : Continuous y) (hdcont : Continuous d) (hbcont : Continuous b)
    (hderiv : ∀ t ∈ Ioo a T, HasDerivAt y (dy t) t)
    (hd : ∀ t, 0 ≤ d t) (hb : ∀ t, 0 ≤ b t)
    (henergy : ∀ t ∈ Ioo a T, dy t + d t ≤ C * b t * y t) :
    ∀ t ∈ Icc a T,
      y t + ∫ s in a..t, d s ≤
        y a * Real.exp (C * ∫ s in a..t, b s) := by
  let D : ℝ → ℝ := fun t => ∫ s in a..t, d s
  let Y : ℝ → ℝ := fun t => y t + D t
  have hDderiv (t : ℝ) : HasDerivAt D (d t) t :=
    (hdcont.integral_hasStrictDerivAt a t).hasDerivAt
  have hDcont : Continuous D :=
    continuous_iff_continuousAt.mpr fun t => (hDderiv t).continuousAt
  have hYcont : Continuous Y := hy.add hDcont
  have hYderiv (t : ℝ) (ht : t ∈ Ioo a T) :
      HasDerivAt Y (dy t + d t) t :=
    (hderiv t ht).add (hDderiv t)
  have hDY (t : ℝ) (ht : t ∈ Icc a T) : y t ≤ Y t := by
    have hDn : 0 ≤ D t :=
      intervalIntegral.integral_nonneg ht.1 (fun s _ => hd s)
    exact le_add_of_nonneg_right hDn
  have hYenergy (t : ℝ) (ht : t ∈ Ioo a T) :
      (dy t + d t) + 0 ≤ C * b t * Y t := by
    have hcoeff : 0 ≤ C * b t := mul_nonneg hC (hb t)
    have hmul := mul_le_mul_of_nonneg_left (hDY t ⟨ht.1.le, ht.2.le⟩) hcoeff
    linarith only [henergy t ht, hmul]
  have hG := lps_high_order_energy_gronwall
    (a := a) (T := T) (C := C)
    (y := Y) (dy := fun t => dy t + d t) (d := fun _ => 0) (b := b)
    haT hYcont hbcont hYderiv (by simp) hYenergy
  intro t ht
  have hYa : Y a = y a := by simp [Y, D]
  simpa only [Y, D, hYa] using hG t ht

/-- Bounds on the initial Sobolev energy and lower-order coefficient
give a scale-independent higher-order estimate (eq:lps-Hm-energy). -/
theorem lps_high_order_energy_uniform_bound
    {a T C M₀ M₁ : ℝ} {y dy d b : ℝ → ℝ}
    (haT : a ≤ T) (hC : 0 ≤ C) (hM₀ : 0 ≤ M₀)
    (hy : Continuous y) (hdcont : Continuous d) (hbcont : Continuous b)
    (hderiv : ∀ t ∈ Ioo a T, HasDerivAt y (dy t) t)
    (hd : ∀ t, 0 ≤ d t) (hb : ∀ t, 0 ≤ b t)
    (henergy : ∀ t ∈ Ioo a T, dy t + d t ≤ C * b t * y t)
    (hinit : y a ≤ M₀)
    (hcoeff : ∀ t ∈ Icc a T, ∫ s in a..t, b s ≤ M₁) :
    ∀ t ∈ Icc a T,
      y t + ∫ s in a..t, d s ≤ M₀ * Real.exp (C * M₁) := by
  have hG := lps_high_order_energy_dissipation_gronwall
    haT hC hy hdcont hbcont hderiv hd hb henergy
  intro t ht
  have hmul : C * ∫ s in a..t, b s ≤ C * M₁ :=
    mul_le_mul_of_nonneg_left (hcoeff t ht) hC
  calc
    y t + ∫ s in a..t, d s
        ≤ y a * Real.exp (C * ∫ s in a..t, b s) := hG t ht
    _ ≤ M₀ * Real.exp (C * ∫ s in a..t, b s) :=
      mul_le_mul_of_nonneg_right hinit (Real.exp_pos _).le
    _ ≤ M₀ * Real.exp (C * M₁) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmul) hM₀

/-- A regularized high-order heat pairing and tensor transport bound
give a uniform energy and gradient-dissipation bound
(eq:lps-Hm-energy). The two pairing bounds are proved from the
regularized equation in the ordered-energy step. -/
theorem lps_high_order_bound_of_heat_transport
    {a T C M₀ M₁ : ℝ} {A B K E' : ℝ → ℝ}
    (haT : a ≤ T) (hM₀ : 0 ≤ M₀)
    (hA : Continuous A) (hB : Continuous B)
    (hderiv : ∀ t ∈ Ioo a T,
      HasDerivAt (fun s => A s ^ 2) (E' t) t)
    (hheat : ∀ t ∈ Ioo a T,
      E' t + 2 * B t ^ 2 ≤ 2 * K t)
    (htransport : ∀ t ∈ Ioo a T,
      K t ≤ C * A t ^ 2 * B t)
    (hinit : A a ^ 2 ≤ M₀)
    (hcoeff : ∀ t ∈ Icc a T,
      ∫ s in a..t, A s ^ 2 ≤ M₁) :
    ∀ t ∈ Icc a T,
      A t ^ 2 + ∫ s in a..t, B s ^ 2 ≤
        M₀ * Real.exp (C ^ 2 * M₁) := by
  apply lps_high_order_energy_uniform_bound
    (a := a) (T := T) (C := C ^ 2)
    (y := fun t => A t ^ 2) (dy := E')
    (d := fun t => B t ^ 2) (b := fun t => A t ^ 2)
    haT (sq_nonneg C) hM₀ (hA.pow 2) (hB.pow 2) (hA.pow 2)
    hderiv
    (fun t => sq_nonneg (B t))
    (fun t => sq_nonneg (A t))
    ?_ hinit hcoeff
  intro t ht
  have h := lps_corrected_energy_from_transport
    (hheat t ht) (htransport t ht)
  convert h using 1; ring

end ESS
