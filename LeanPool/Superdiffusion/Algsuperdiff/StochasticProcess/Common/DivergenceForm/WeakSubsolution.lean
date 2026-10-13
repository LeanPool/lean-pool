/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Positivity

/-!
# WeakSubsolution

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak subsolutions and supersolutions

This module defines weak subsolutions and supersolutions for the shifted
divergence-form equation on the zero-trace Sobolev carrier.  It proves the
weak comparison and maximum principles and the resolvent estimate for a
nonnegative weak supersolution.  All order conclusions are almost-everywhere
statements.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}

/-- A weak subsolution of the alpha-shifted divergence-form equation. -/
def IsAlphaShiftedWeakSubsolution (a : CoeffField d) (U : Set (Vec d))
    (α : ℝ) (f : ScalarL2 U) (u : ZeroTraceSobolev U) : Prop :=
  ∀ φ : ZeroTraceSobolev U,
    (∀ᵐ x ∂volumeMeasureOn U, 0 ≤ ZeroTraceSobolev.toL2 φ x) →
      α * inner ℝ (ZeroTraceSobolev.toL2 u) (ZeroTraceSobolev.toL2 φ) +
          coefficientPairing a U (ZeroTraceSobolev.gradient u)
            (ZeroTraceSobolev.gradient φ) ≤
        inner ℝ f (ZeroTraceSobolev.toL2 φ)

/-- A weak supersolution of the alpha-shifted divergence-form equation. -/
def IsAlphaShiftedWeakSupersolution (a : CoeffField d) (U : Set (Vec d))
    (α : ℝ) (f : ScalarL2 U) (u : ZeroTraceSobolev U) : Prop :=
  ∀ φ : ZeroTraceSobolev U,
    (∀ᵐ x ∂volumeMeasureOn U, 0 ≤ ZeroTraceSobolev.toL2 φ x) →
      inner ℝ f (ZeroTraceSobolev.toL2 φ) ≤
        α * inner ℝ (ZeroTraceSobolev.toL2 u) (ZeroTraceSobolev.toL2 φ) +
          coefficientPairing a U (ZeroTraceSobolev.gradient u)
            (ZeroTraceSobolev.gradient φ)

/-- Every weak solution is a weak subsolution. -/
theorem IsAlphaShiftedWeakSolution.isSubsolution
    {a : CoeffField d} {α : ℝ} {f : ScalarL2 U} {u : ZeroTraceSobolev U}
    (hu : IsAlphaShiftedWeakSolution a U α f u) :
    IsAlphaShiftedWeakSubsolution a U α f u := by
  intro φ _
  exact (hu φ).le

/-- Every weak solution is a weak supersolution. -/
theorem IsAlphaShiftedWeakSolution.isSupersolution
    {a : CoeffField d} {α : ℝ} {f : ScalarL2 U} {u : ZeroTraceSobolev U}
    (hu : IsAlphaShiftedWeakSolution a U α f u) :
    IsAlphaShiftedWeakSupersolution a U α f u := by
  intro φ _
  exact (hu φ).ge

/-- A weak subsolution is almost everywhere below a weak supersolution when
their right-hand sides have the same order. -/
theorem weakSubsolution_le_weakSupersolution_ae
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam : ℝ} (hα : 0 < α)
    (hEll : IsEllipticFieldOn lam Lam U a)
    {f g : ScalarL2 U} {u v : ZeroTraceSobolev U}
    (hu : IsAlphaShiftedWeakSubsolution a U α f u)
    (hv : IsAlphaShiftedWeakSupersolution a U α g v)
    (hfg : ∀ᵐ x ∂volumeMeasureOn U, f x ≤ g x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 u x ≤ ZeroTraceSobolev.toL2 v x := by
  let z : ZeroTraceSobolev U := u - v
  obtain ⟨p, hp, -⟩ :=
    ZeroTraceSobolev.existsUnique_positivePartSubConst hU z 0 le_rfl
  have hpnonneg : ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ ZeroTraceSobolev.toL2 p x := by
    filter_upwards [hp.1] with x hx
    rw [hx]
    exact le_max_right _ _
  have hform_le :
      shiftedBilin hEll α z p ≤
        inner ℝ (f - g) (ZeroTraceSobolev.toL2 p) := by
    calc
      shiftedBilin hEll α z p =
          shiftedBilin hEll α u p - shiftedBilin hEll α v p := by
        simp only [z, map_sub, sub_apply]
      _ ≤ inner ℝ f (ZeroTraceSobolev.toL2 p) -
          inner ℝ g (ZeroTraceSobolev.toL2 p) := by
        have hup : shiftedBilin hEll α u p ≤
            inner ℝ f (ZeroTraceSobolev.toL2 p) := by
          rw [shiftedBilin_apply]
          exact hu p hpnonneg
        have hvp : inner ℝ g (ZeroTraceSobolev.toL2 p) ≤
            shiftedBilin hEll α v p := by
          rw [shiftedBilin_apply]
          exact hv p hpnonneg
        exact sub_le_sub hup hvp
      _ = inner ℝ (f - g) (ZeroTraceSobolev.toL2 p) := by
        rw [inner_sub_left]
  have hforcing_nonpos :
      inner ℝ (f - g) (ZeroTraceSobolev.toL2 p) ≤ 0 :=
    Internal.scalarL2_inner_sub_nonpos_of_ae_le f g _ hfg hpnonneg
  have hpvalue : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 p x = max (ZeroTraceSobolev.toL2 z x) 0 := by
    filter_upwards [hp.1] with x hx
    simpa only [sub_zero] using hx
  have hmass : inner ℝ (ZeroTraceSobolev.toL2 z)
      (ZeroTraceSobolev.toL2 p) =
        inner ℝ (ZeroTraceSobolev.toL2 p) (ZeroTraceSobolev.toL2 p) :=
    Internal.scalarL2_inner_eq_self_of_ae_eq_max _ _ hpvalue
  have hpair : 0 ≤ coefficientPairing a U
      (ZeroTraceSobolev.gradient z) (ZeroTraceSobolev.gradient p) :=
    coefficientPairing_nonneg_of_ae_eq_indicator hEll _ _
      {x | 0 < ZeroTraceSobolev.toL2 z x} hp.2
  have hself_nonpos :
      α * inner ℝ (ZeroTraceSobolev.toL2 p)
        (ZeroTraceSobolev.toL2 p) ≤ 0 := by
    calc
      α * inner ℝ (ZeroTraceSobolev.toL2 p)
          (ZeroTraceSobolev.toL2 p) ≤
          α * inner ℝ (ZeroTraceSobolev.toL2 p)
              (ZeroTraceSobolev.toL2 p) +
            coefficientPairing a U (ZeroTraceSobolev.gradient z)
              (ZeroTraceSobolev.gradient p) := le_add_of_nonneg_right hpair
      _ = shiftedBilin hEll α z p := by rw [shiftedBilin_apply, hmass]
      _ ≤ inner ℝ (f - g) (ZeroTraceSobolev.toL2 p) := hform_le
      _ ≤ 0 := hforcing_nonpos
  have hpzero : ZeroTraceSobolev.toL2 p = 0 := by
    have hself : inner ℝ (ZeroTraceSobolev.toL2 p)
        (ZeroTraceSobolev.toL2 p) = 0 := by
      have hprod : α * inner ℝ (ZeroTraceSobolev.toL2 p)
          (ZeroTraceSobolev.toL2 p) = 0 :=
        le_antisymm hself_nonpos
          (mul_nonneg hα.le real_inner_self_nonneg)
      exact (mul_eq_zero.mp hprod).resolve_left hα.ne'
    exact inner_self_eq_zero.mp hself
  have hpzero_ae : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 p x = 0 := by
    rw [hpzero]
    exact MeasureTheory.Lp.coeFn_zero (p := (2 : ENNReal))
      (μ := volumeMeasureOn U) ℝ
  have hzvalue : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 z x =
        ZeroTraceSobolev.toL2 u x - ZeroTraceSobolev.toL2 v x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub (ZeroTraceSobolev.toL2 u)
      (ZeroTraceSobolev.toL2 v)] with x hsub
    change (ZeroTraceSobolev.toL2 (u - v)) x = _
    rw [map_sub]
    simpa only [Pi.sub_apply] using hsub
  filter_upwards [hpvalue, hpzero_ae, hzvalue] with x hpx hp0 hz
  rw [hpx, hz] at hp0
  exact sub_nonpos.mp (max_eq_right_iff.mp hp0)

/-- A weak supersolution with nonnegative right-hand side is nonnegative
almost everywhere. -/
theorem IsAlphaShiftedWeakSupersolution.nonneg_ae
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    {g : ScalarL2 U} {v : ZeroTraceSobolev U}
    (hv : IsAlphaShiftedWeakSupersolution a U α g v)
    (hg : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ g x) :
    ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ ZeroTraceSobolev.toL2 v x := by
  have hzero : IsAlphaShiftedWeakSolution a U α 0 0 := by
    simpa only [map_zero] using
      alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEll
        (0 : ScalarL2 U)
  have h0g : ∀ᵐ x ∂volumeMeasureOn U, (0 : ScalarL2 U) x ≤ g x := by
    filter_upwards [hg, MeasureTheory.Lp.coeFn_zero (E := ℝ)
      (p := (2 : ENNReal)) (volumeMeasureOn U)] with x hgx hzero
    simpa only [hzero] using! hgx
  have hle := weakSubsolution_le_weakSupersolution_ae a hU hα hEll
    hzero.isSubsolution hv h0g
  have hzeroValue : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 (0 : ZeroTraceSobolev U) x = 0 := by
    rw [map_zero]
    exact MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := (2 : ENNReal))
      (volumeMeasureOn U)
  filter_upwards [hle, hzeroValue] with x hx hzero
  rwa [hzero] at hx

/-- Resolvent estimate for a weak α-supersolution when `0 < β` and `α < β`. -/
theorem resolvent_le_of_weakSupersolution_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {alpha beta lam Lam : ℝ} (hBeta : 0 < beta)
    (hAlphaBeta : alpha < beta) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (v : ZeroTraceSobolev U)
    (hv : IsAlphaShiftedWeakSupersolution a U alpha 0 v) :
    ∀ᵐ x ∂volumeMeasureOn U,
      beta * alphaShiftedResolvent a hBeta hlam hEll
          (ZeroTraceSobolev.toL2 v) x ≤
        (beta / (beta - alpha)) * ZeroTraceSobolev.toL2 v x := by
  have hdiff : 0 < beta - alpha := sub_pos.mpr hAlphaBeta
  let c : ℝ := beta / (beta - alpha)
  let r : ZeroTraceSobolev U :=
    alphaShiftedSolution a hBeta hlam hEll (ZeroTraceSobolev.toL2 v)
  let w : ZeroTraceSobolev U := c • v - beta • r
  have hc : 0 ≤ c := div_nonneg hBeta.le hdiff.le
  have hw : IsAlphaShiftedWeakSupersolution a U beta 0 w := by
    intro φ hφ
    have hvφ := hv φ hφ
    have hvφ' : 0 ≤ shiftedBilin hEll alpha v φ := by
      rw [shiftedBilin_apply]
      simpa only [inner_zero_left] using hvφ
    have hrφ :=
      alphaShiftedSolution_isAlphaShiftedWeakSolution a hBeta hlam hEll
        (ZeroTraceSobolev.toL2 v) φ
    rw [inner_zero_left]
    change 0 ≤ beta * inner ℝ (ZeroTraceSobolev.toL2 w)
        (ZeroTraceSobolev.toL2 φ) +
      coefficientPairing a U (ZeroTraceSobolev.gradient w)
        (ZeroTraceSobolev.gradient φ)
    rw [← shiftedBilin_apply hEll beta]
    calc
      shiftedBilin hEll beta w φ =
          c * shiftedBilin hEll beta v φ -
            beta * shiftedBilin hEll beta r φ := by
        simp only [w, map_sub, map_smul, sub_apply,
          smul_apply, smul_eq_mul]
      _ = c * shiftedBilin hEll alpha v φ := by
        rw [shiftedBilin_apply hEll beta, shiftedBilin_apply hEll alpha,
          shiftedBilin_apply hEll beta r φ, hrφ]
        dsimp only [c]
        field_simp
        ring
      _ ≥ 0 := mul_nonneg hc hvφ'
  have hzeroNonneg : ∀ᵐ x ∂volumeMeasureOn U, (0 : ScalarL2 U) x ≥ 0 := by
    filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℝ)
      (p := (2 : ENNReal)) (volumeMeasureOn U)] with x hx
    simpa only [Pi.zero_apply] using hx.ge
  have hw_nonneg := hw.nonneg_ae a hU hBeta hlam hEll hzeroNonneg
  filter_upwards [hw_nonneg,
      MeasureTheory.Lp.coeFn_sub (c • ZeroTraceSobolev.toL2 v)
        (beta • ZeroTraceSobolev.toL2 r),
      MeasureTheory.Lp.coeFn_smul c (ZeroTraceSobolev.toL2 v),
      MeasureTheory.Lp.coeFn_smul beta (ZeroTraceSobolev.toL2 r)]
      with x hx hsub hcv hBetaR
  change 0 ≤ ZeroTraceSobolev.toL2 (c • v - beta • r) x at hx
  rw [map_sub, map_smul, map_smul, hsub, Pi.sub_apply, hcv, hBetaR] at hx
  change 0 ≤ c * ZeroTraceSobolev.toL2 v x -
    beta * ZeroTraceSobolev.toL2 r x at hx
  change beta * alphaShiftedResolvent a hBeta hlam hEll
      (ZeroTraceSobolev.toL2 v) x ≤ c * ZeroTraceSobolev.toL2 v x
  have hbound := sub_nonneg.mp hx
  simpa only [r, alphaShiftedResolvent_apply, c] using hbound

end DivergenceFormProcess.Form
