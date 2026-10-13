/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialWeakSolution
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PositivePart
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Private.ScalarL2Order

/-!
# PotentialOrder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Order properties of resolvents with potential

This module proves positivity, fixed-potential comparison, normalized upper
bounds, and antitonicity with respect to the nonnegative potential.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}

private theorem potentialIntegral_nonpos_of_negativePart
    {C : ℝ} {q : Vec d → ℝ}
    (hq : IsBoundedNonnegativePotential U q C)
    (u v : ZeroTraceSobolev U)
    (hv : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 v x =
        max (-ZeroTraceSobolev.toL2 u x) 0) :
    (∫ x, q x * ZeroTraceSobolev.toL2 u x *
        ZeroTraceSobolev.toL2 v x ∂volumeMeasureOn U) ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [hq.2.1, hv] with x hqx hvx
  rw [hvx]
  by_cases hux : ZeroTraceSobolev.toL2 u x < 0
  · exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hqx hux.le) (le_max_right _ _)
  · rw [max_eq_right]
    · simpa only [mul_zero, Pi.zero_apply] using (le_refl (0 : ℝ))
    · exact neg_nonpos.mpr (le_of_not_gt hux)

/-- A nonnegative forcing has a nonnegative potential resolvent almost
everywhere. -/
theorem potentialResolvent_nonneg_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam C : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ potentialResolvent a hα hlam hEll q hq f x  := by
  let u : ZeroTraceSobolev U := potentialSolution a hα hlam hEll q hq f
  obtain ⟨v, hv, -⟩ :=
    ZeroTraceSobolev.existsUnique_positivePartSubConst hU (-u) 0 le_rfl
  have hv' := hv
  simp only [map_neg] at hv'
  have hvvalue : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 v x =
        max (-ZeroTraceSobolev.toL2 u x) 0 := by
    filter_upwards [hv'.1, MeasureTheory.Lp.coeFn_neg
      (ZeroTraceSobolev.toL2 u)] with x hx hneg
    rw [hneg] at hx
    simpa only [sub_zero] using! hx
  have hvnonneg : ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ ZeroTraceSobolev.toL2 v x := by
    filter_upwards [hvvalue] with x hx
    rw [hx]
    exact le_max_right _ _
  have hvgradient : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.gradient v x =
        {y | ZeroTraceSobolev.toL2 u y < 0}.indicator
          (fun y => -ZeroTraceSobolev.gradient u y) x := by
    filter_upwards [hv'.2, MeasureTheory.Lp.coeFn_neg
      (ZeroTraceSobolev.toL2 u), MeasureTheory.Lp.coeFn_neg
      (ZeroTraceSobolev.gradient u)] with x hx hnegValue hnegGradient
    rw [Set.indicator_apply] at hx ⊢
    simpa only [Set.mem_ofPred_eq, hnegValue, hnegGradient, Pi.neg_apply,
      neg_pos] using hx
  have hpair : coefficientPairing a U
      (ZeroTraceSobolev.gradient u) (ZeroTraceSobolev.gradient v) ≤ 0 :=
    coefficientPairing_nonpos_of_ae_eq_neg_indicator hEll _ _ _ hvgradient
  have hpotential :
      (∫ x, q x * ZeroTraceSobolev.toL2 u x *
          ZeroTraceSobolev.toL2 v x ∂volumeMeasureOn U) ≤ 0 :=
    potentialIntegral_nonpos_of_negativePart hq u v hvvalue
  have hrhs : 0 ≤ inner ℝ f (ZeroTraceSobolev.toL2 v) :=
    Internal.scalarL2_inner_nonneg_of_ae_nonneg f _ hf hvnonneg
  have hinner : inner ℝ (ZeroTraceSobolev.toL2 u)
      (ZeroTraceSobolev.toL2 v) =
        -inner ℝ (ZeroTraceSobolev.toL2 v) (ZeroTraceSobolev.toL2 v) :=
    Internal.scalarL2_inner_eq_neg_self_of_ae_eq_max_neg _ _ hvvalue
  have hweak : IsPotentialWeakSolution a α q U u f := by
    simpa only [u] using
      potentialSolution_isPotentialWeakSolution a hα hlam hEll q hq f
  have hself_nonpos :
      α * inner ℝ (ZeroTraceSobolev.toL2 v)
        (ZeroTraceSobolev.toL2 v) ≤ 0 := by
    have hweakAtV := hweak v
    dsimp only [shiftedPotentialBilin] at hweakAtV
    rw [hinner, mul_neg] at hweakAtV
    linarith only [hpair, hpotential, hrhs, hweakAtV]
  have hself_nonneg :
      0 ≤ α * inner ℝ (ZeroTraceSobolev.toL2 v)
        (ZeroTraceSobolev.toL2 v) :=
    mul_nonneg hα.le real_inner_self_nonneg
  have hself : inner ℝ (ZeroTraceSobolev.toL2 v)
      (ZeroTraceSobolev.toL2 v) = 0 := by
    have hprod : α * inner ℝ (ZeroTraceSobolev.toL2 v)
        (ZeroTraceSobolev.toL2 v) = 0 :=
      le_antisymm hself_nonpos hself_nonneg
    exact (mul_eq_zero.mp hprod).resolve_left hα.ne'
  have hvzero : ZeroTraceSobolev.toL2 v = 0 :=
    inner_self_eq_zero.mp hself
  have hvzero_ae : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 v x = 0 := by
    filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℝ)
      (p := (2 : ENNReal)) (volumeMeasureOn U)] with x hzero
    rw [hvzero, hzero]
    rfl
  have hunonneg : ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ ZeroTraceSobolev.toL2 u x := by
    filter_upwards [hvvalue, hvzero_ae] with x hvx hzx
    rw [hvx] at hzx
    by_contra hx
    have hxneg : ZeroTraceSobolev.toL2 u x < 0 := lt_of_not_ge hx
    exact (ne_of_gt (lt_max_of_lt_left (neg_pos.mpr hxneg))) hzx
  simpa only [potentialResolvent_apply, u] using hunonneg

/-- The potential resolvent preserves almost-everywhere order for fixed
coefficients, shift, and potential. -/
theorem potentialResolvent_mono_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam C : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f g : ScalarL2 U)
    (hfg : ∀ᵐ x ∂volumeMeasureOn U, f x ≤ g x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      potentialResolvent a hα hlam hEll q hq f x ≤
        potentialResolvent a hα hlam hEll q hq g x  := by
  have hgf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ (g - f) x := by
    filter_upwards [hfg, MeasureTheory.Lp.coeFn_sub g f] with x hx hsub
    rw [hsub]
    exact sub_nonneg.mpr hx
  have hpos := potentialResolvent_nonneg_ae
    a hU hα hlam hEll q hq (g - f) hgf
  have hmap : potentialResolvent a hα hlam hEll q hq (g - f) =
      potentialResolvent a hα hlam hEll q hq g -
        potentialResolvent a hα hlam hEll q hq f :=
    map_sub (potentialResolvent a hα hlam hEll q hq) g f
  filter_upwards [hpos, MeasureTheory.Lp.coeFn_sub
      (potentialResolvent a hα hlam hEll q hq g)
      (potentialResolvent a hα hlam hEll q hq f)] with x hx hsub
  rw [hmap, hsub] at hx
  exact sub_nonneg.mp hx

private theorem potentialIntegral_nonneg_of_upperPart
    {α C : ℝ} (hα : 0 < α) {q : Vec d → ℝ}
    (hq : IsBoundedNonnegativePotential U q C)
    (u v : ZeroTraceSobolev U)
    (hv : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 v x =
        max (ZeroTraceSobolev.toL2 u x - α⁻¹) 0) :
    0 ≤ ∫ x, q x * ZeroTraceSobolev.toL2 u x *
        ZeroTraceSobolev.toL2 v x ∂volumeMeasureOn U := by
  apply integral_nonneg_of_ae
  filter_upwards [hq.2.1, hv] with x hqx hvx
  rw [hvx]
  by_cases hux : α⁻¹ < ZeroTraceSobolev.toL2 u x
  · have hu0 : 0 ≤ ZeroTraceSobolev.toL2 u x :=
      (inv_pos.mpr hα).le.trans hux.le
    exact mul_nonneg (mul_nonneg hqx hu0) (le_max_right _ _)
  · rw [max_eq_right]
    · simpa only [mul_zero, Pi.zero_apply] using (le_refl (0 : ℝ))
    · exact sub_nonpos.mpr (le_of_not_gt hux)

private theorem scalarL2_inner_le_integral_of_ae_le_one
    [IsFiniteMeasure (volumeMeasureOn U)]
    (f g : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, f x ≤ 1)
    (hg : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ g x) :
    inner ℝ f g ≤ ∫ x, g x ∂volumeMeasureOn U := by
  have hfg : Integrable (fun x => f x * g x) (volumeMeasureOn U) :=
    (MeasureTheory.Lp.memLp f).integrable_mul (MeasureTheory.Lp.memLp g)
  have hgInt : Integrable (fun x => g x) (volumeMeasureOn U) :=
    (MeasureTheory.Lp.memLp g).integrable (by norm_num)
  rw [scalarInner_eq_integral]
  exact integral_mono_ae hfg hgInt (by
    filter_upwards [hf, hg] with x hfx hgx
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfx hgx)

private theorem alpha_mul_inner_eq_integral_add_self_of_ae_eq_max_sub_inv
    [IsFiniteMeasure (volumeMeasureOn U)]
    {α : ℝ} (hα : 0 < α) (u v : ScalarL2 U)
    (hv : ∀ᵐ x ∂volumeMeasureOn U, v x = max (u x - α⁻¹) 0) :
    α * inner ℝ u v =
      (∫ x, v x ∂volumeMeasureOn U) + α * inner ℝ v v := by
  have hvInt : Integrable (fun x => v x) (volumeMeasureOn U) :=
    (MeasureTheory.Lp.memLp v).integrable (by norm_num)
  have hvvInt : Integrable (fun x => v x * v x) (volumeMeasureOn U) :=
    (MeasureTheory.Lp.memLp v).integrable_mul (MeasureTheory.Lp.memLp v)
  rw [scalarInner_eq_integral, scalarInner_eq_integral]
  change α * (∫ x, u x * v x ∂volumeMeasureOn U) =
    (∫ x, v x ∂volumeMeasureOn U) + α * ∫ x, v x * v x ∂volumeMeasureOn U
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add hvInt (hvvInt.const_mul α)]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  have hαinv : α * α⁻¹ = 1 := mul_inv_cancel₀ hα.ne'
  by_cases hxu : α⁻¹ < u x
  · have hxv : v x = u x - α⁻¹ := by
      rw [hx, max_eq_left (sub_nonneg.mpr hxu.le)]
    rw [hxv]
    calc
      α * (u x * (u x - α⁻¹)) =
          α * (α⁻¹ * (u x - α⁻¹)) +
            α * ((u x - α⁻¹) * (u x - α⁻¹)) := by ring
      _ = (u x - α⁻¹) + α * ((u x - α⁻¹) * (u x - α⁻¹)) := by
        rw [← mul_assoc, hαinv, one_mul]
  · have hxv : v x = 0 := by
      rw [hx, max_eq_right]
      exact sub_nonpos.mpr (le_of_not_gt hxu)
    rw [hxv]
    ring

/-- Multiplication by the shift bounds the potential resolvent by one when the
forcing is almost everywhere at most one. -/
theorem alpha_mul_potentialResolvent_le_one_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam C : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, f x ≤ 1) :
    ∀ᵐ x ∂volumeMeasureOn U,
      α * potentialResolvent a hα hlam hEll q hq f x ≤ 1  := by
  let : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa only [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  let u : ZeroTraceSobolev U := potentialSolution a hα hlam hEll q hq f
  obtain ⟨v, ⟨hvvalue, hvgradient⟩, _⟩ :=
    ZeroTraceSobolev.existsUnique_positivePartSubConst hU u α⁻¹
      (inv_nonneg.mpr hα.le)
  have hvnonneg : ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ ZeroTraceSobolev.toL2 v x := by
    filter_upwards [hvvalue] with x hx
    rw [hx]
    exact le_max_right _ _
  have hpair : 0 ≤ coefficientPairing a U
      (ZeroTraceSobolev.gradient u) (ZeroTraceSobolev.gradient v) :=
    coefficientPairing_nonneg_of_ae_eq_indicator hEll _ _
      {y | α⁻¹ < ZeroTraceSobolev.toL2 u y} hvgradient
  have hpotential : 0 ≤
      ∫ x, q x * ZeroTraceSobolev.toL2 u x *
        ZeroTraceSobolev.toL2 v x ∂volumeMeasureOn U :=
    potentialIntegral_nonneg_of_upperPart hα hq u v hvvalue
  have hweak : IsPotentialWeakSolution a α q U u f := by
    simpa only [u] using
      potentialSolution_isPotentialWeakSolution a hα hlam hEll q hq f
  have hforcing_le : inner ℝ f (ZeroTraceSobolev.toL2 v) ≤
      ∫ x, ZeroTraceSobolev.toL2 v x ∂volumeMeasureOn U :=
    scalarL2_inner_le_integral_of_ae_le_one f _ hf hvnonneg
  have hmass_identity :
      α * inner ℝ (ZeroTraceSobolev.toL2 u) (ZeroTraceSobolev.toL2 v) =
        (∫ x, ZeroTraceSobolev.toL2 v x ∂volumeMeasureOn U) +
          α * inner ℝ (ZeroTraceSobolev.toL2 v)
            (ZeroTraceSobolev.toL2 v) :=
    alpha_mul_inner_eq_integral_add_self_of_ae_eq_max_sub_inv
      hα _ _ hvvalue
  have hvnorm_nonpos :
      α * inner ℝ (ZeroTraceSobolev.toL2 v)
        (ZeroTraceSobolev.toL2 v) ≤ 0 := by
    have hweakAtV := hweak v
    dsimp only [shiftedPotentialBilin] at hweakAtV
    linarith only [hpair, hpotential, hforcing_le, hmass_identity, hweakAtV]
  have hvzero : ZeroTraceSobolev.toL2 v = 0 := by
    have hinner_nonpos : inner ℝ (ZeroTraceSobolev.toL2 v)
        (ZeroTraceSobolev.toL2 v) ≤ 0 := by
      by_contra hn
      exact (not_lt_of_ge hvnorm_nonpos)
        (mul_pos hα (lt_of_not_ge hn))
    exact inner_self_eq_zero.mp
      (le_antisymm hinner_nonpos real_inner_self_nonneg)
  have hvzero_ae : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 v x = 0 := by
    rw [hvzero]
    exact MeasureTheory.Lp.coeFn_zero (p := (2 : ENNReal))
      (μ := volumeMeasureOn U) ℝ
  filter_upwards [hvvalue, hvzero_ae] with x hx hxzero
  have hu_le : ZeroTraceSobolev.toL2 u x ≤ α⁻¹ :=
    sub_nonpos.mp (max_eq_right_iff.mp (hx.symm.trans hxzero))
  change α * ZeroTraceSobolev.toL2 u x ≤ 1
  calc
    α * ZeroTraceSobolev.toL2 u x ≤ α * α⁻¹ :=
      mul_le_mul_of_nonneg_left hu_le hα.le
    _ = 1 := mul_inv_cancel₀ hα.ne'

/-- Increasing a bounded nonnegative potential decreases its resolvent on
nonnegative forcing. -/
theorem potentialResolvent_antitone_potential_ae
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam C₁ C₂ : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q₁ q₂ : Vec d → ℝ)
    (hq₁ : IsBoundedNonnegativePotential U q₁ C₁)
    (hq₂ : IsBoundedNonnegativePotential U q₂ C₂)
    (hqle : ∀ᵐ x ∂volumeMeasureOn U, q₁ x ≤ q₂ x)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      potentialResolvent a hα hlam hEll q₂ hq₂ f x ≤
        potentialResolvent a hα hlam hEll q₁ hq₁ f x  := by
  let u₂ : ZeroTraceSobolev U := potentialSolution a hα hlam hEll q₂ hq₂ f
  let g : ScalarL2 U :=
    f - potentialMul q₂ hq₂ (ZeroTraceSobolev.toL2 u₂) +
      potentialMul q₁ hq₁ (ZeroTraceSobolev.toL2 u₂)
  have hu₂nonneg : ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ ZeroTraceSobolev.toL2 u₂ x := by
    simpa only [u₂, potentialResolvent_apply] using
      potentialResolvent_nonneg_ae a hU hα hlam hEll q₂ hq₂ f hf
  have hgle : ∀ᵐ x ∂volumeMeasureOn U, g x ≤ f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_add
        (f - potentialMul q₂ hq₂ (ZeroTraceSobolev.toL2 u₂))
        (potentialMul q₁ hq₁ (ZeroTraceSobolev.toL2 u₂)),
      MeasureTheory.Lp.coeFn_sub f
        (potentialMul q₂ hq₂ (ZeroTraceSobolev.toL2 u₂)),
      potentialMul_coeFn q₁ hq₁ (ZeroTraceSobolev.toL2 u₂),
      potentialMul_coeFn q₂ hq₂ (ZeroTraceSobolev.toL2 u₂),
      hqle, hu₂nonneg] with x hadd hsub hq₁x hq₂x hq12 hux
    change (f - potentialMul q₂ hq₂ (ZeroTraceSobolev.toL2 u₂) +
      potentialMul q₁ hq₁ (ZeroTraceSobolev.toL2 u₂)) x ≤ f x
    rw [hadd, Pi.add_apply, hsub, Pi.sub_apply, hq₁x, hq₂x]
    calc
      f x - q₂ x * ZeroTraceSobolev.toL2 u₂ x +
          q₁ x * ZeroTraceSobolev.toL2 u₂ x =
        f x + (q₁ x - q₂ x) * ZeroTraceSobolev.toL2 u₂ x := by ring
      _ ≤ f x + 0 := add_le_add (le_refl _)
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq12) hux)
      _ = f x := add_zero _
  have hu₂q₁ : IsPotentialWeakSolution a α q₁ U u₂ g := by
    intro v
    have hweak := potentialSolution_isPotentialWeakSolution
      a hα hlam hEll q₂ hq₂ f v
    change shiftedPotentialBilin a α q₂ U u₂ v =
      inner ℝ f (ZeroTraceSobolev.toL2 v) at hweak
    dsimp only [shiftedPotentialBilin] at hweak ⊢
    rw [← shiftedBilin_apply hEll α u₂ v,
      ← inner_potentialMul_eq_integral (C := C₁) q₁ hq₁]
    rw [← shiftedBilin_apply hEll α u₂ v,
      ← inner_potentialMul_eq_integral (C := C₂) q₂ hq₂] at hweak
    dsimp only [g]
    rw [inner_add_left, inner_sub_left]
    calc
      shiftedBilin hEll α u₂ v +
          inner ℝ (potentialMul q₁ hq₁ (ZeroTraceSobolev.toL2 u₂))
            (ZeroTraceSobolev.toL2 v) =
        (shiftedBilin hEll α u₂ v +
            inner ℝ (potentialMul q₂ hq₂ (ZeroTraceSobolev.toL2 u₂))
              (ZeroTraceSobolev.toL2 v)) -
          inner ℝ (potentialMul q₂ hq₂ (ZeroTraceSobolev.toL2 u₂))
              (ZeroTraceSobolev.toL2 v) +
          inner ℝ (potentialMul q₁ hq₁ (ZeroTraceSobolev.toL2 u₂))
              (ZeroTraceSobolev.toL2 v) := by ring
      _ = inner ℝ f (ZeroTraceSobolev.toL2 v) -
          inner ℝ (potentialMul q₂ hq₂ (ZeroTraceSobolev.toL2 u₂))
              (ZeroTraceSobolev.toL2 v) +
          inner ℝ (potentialMul q₁ hq₁ (ZeroTraceSobolev.toL2 u₂))
              (ZeroTraceSobolev.toL2 v) := by rw [hweak]
  have hu₂eq : u₂ = potentialSolution a hα hlam hEll q₁ hq₁ g :=
    (isPotentialWeakSolution_iff_eq a hα hlam hEll q₁ hq₁ g u₂).1 hu₂q₁
  have hmono := potentialResolvent_mono_ae
    a hU hα hlam hEll q₁ hq₁ g f hgle
  simpa only [potentialResolvent_apply, ← hu₂eq, u₂] using hmono

end DivergenceFormProcess.Form
