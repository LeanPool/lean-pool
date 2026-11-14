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

/-- A weak subsolution of the shifted equation with potential. -/
def IsPotentialWeakSubsolution (a : CoeffField d) (α : ℝ)
    (q : Vec d → ℝ) (U : Set (Vec d)) (u : ZeroTraceSobolev U)
    (f : ScalarL2 U) : Prop :=
  ∀ φ : ZeroTraceSobolev U,
    (∀ᵐ x ∂volumeMeasureOn U, 0 ≤ ZeroTraceSobolev.toL2 φ x) →
      shiftedPotentialBilin a α q U u φ ≤
        inner ℝ f (ZeroTraceSobolev.toL2 φ)

/-- A weak supersolution of the shifted equation with potential. -/
def IsPotentialWeakSupersolution (a : CoeffField d) (α : ℝ)
    (q : Vec d → ℝ) (U : Set (Vec d)) (u : ZeroTraceSobolev U)
    (f : ScalarL2 U) : Prop :=
  ∀ φ : ZeroTraceSobolev U,
    (∀ᵐ x ∂volumeMeasureOn U, 0 ≤ ZeroTraceSobolev.toL2 φ x) →
      inner ℝ f (ZeroTraceSobolev.toL2 φ) ≤
        shiftedPotentialBilin a α q U u φ

/-- A potential weak solution is a potential weak subsolution. -/
theorem IsPotentialWeakSolution.isSubsolution
    {a : CoeffField d} {α : ℝ} {q : Vec d → ℝ} {f : ScalarL2 U}
    {u : ZeroTraceSobolev U} (hu : IsPotentialWeakSolution a α q U u f) :
    IsPotentialWeakSubsolution a α q U u f := by
  intro φ _
  exact (hu φ).le

/-- A potential weak solution is a potential weak supersolution. -/
theorem IsPotentialWeakSolution.isSupersolution
    {a : CoeffField d} {α : ℝ} {q : Vec d → ℝ} {f : ScalarL2 U}
    {u : ZeroTraceSobolev U} (hu : IsPotentialWeakSolution a α q U u f) :
    IsPotentialWeakSupersolution a α q U u f := by
  intro φ _
  exact (hu φ).ge

/-- Potential weak subsolutions lie below potential weak supersolutions when
their forcing terms have the same order. -/
theorem potentialWeakSubsolution_le_weakSupersolution_ae
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam C : ℝ} (hα : 0 < α)
    (hEll : IsEllipticFieldOn lam Lam U a) (q : Vec d → ℝ)
    (hq : IsBoundedNonnegativePotential U q C)
    {f g : ScalarL2 U} {u v : ZeroTraceSobolev U}
    (hu : IsPotentialWeakSubsolution a α q U u f)
    (hv : IsPotentialWeakSupersolution a α q U v g)
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
      potentialBilin (α := α) hEll q hq z p ≤
        inner ℝ (f - g) (ZeroTraceSobolev.toL2 p) := by
    calc
      potentialBilin (α := α) hEll q hq z p =
          potentialBilin (α := α) hEll q hq u p -
            potentialBilin (α := α) hEll q hq v p := by
        simp only [z, map_sub, sub_apply]
      _ ≤ inner ℝ f (ZeroTraceSobolev.toL2 p) -
          inner ℝ g (ZeroTraceSobolev.toL2 p) := by
        have hup : potentialBilin (α := α) hEll q hq u p ≤
            inner ℝ f (ZeroTraceSobolev.toL2 p) := by
          rw [potentialBilin_apply]
          exact hu p hpnonneg
        have hvp : inner ℝ g (ZeroTraceSobolev.toL2 p) ≤
            potentialBilin (α := α) hEll q hq v p := by
          rw [potentialBilin_apply]
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
  have hpotential : 0 ≤
      ∫ x, q x * ZeroTraceSobolev.toL2 z x *
        ZeroTraceSobolev.toL2 p x ∂volumeMeasureOn U := by
    apply integral_nonneg_of_ae
    filter_upwards [hq.2.1, hpvalue] with x hqx hpx
    rw [hpx]
    by_cases hx : 0 ≤ ZeroTraceSobolev.toL2 z x
    · rw [max_eq_left hx]
      exact mul_nonneg (mul_nonneg hqx hx) hx
    · rw [max_eq_right (le_of_not_ge hx)]
      simpa only [Pi.zero_apply, mul_zero] using (le_refl (0 : ℝ))
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
      _ ≤ α * inner ℝ (ZeroTraceSobolev.toL2 p)
              (ZeroTraceSobolev.toL2 p) +
            coefficientPairing a U (ZeroTraceSobolev.gradient z)
              (ZeroTraceSobolev.gradient p) +
            ∫ x, q x * ZeroTraceSobolev.toL2 z x *
              ZeroTraceSobolev.toL2 p x ∂volumeMeasureOn U :=
        le_add_of_nonneg_right hpotential
      _ = potentialBilin (α := α) hEll q hq z p := by
        rw [potentialBilin_apply]
        unfold shiftedPotentialBilin
        rw [hmass]
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


/-- A nonnegative forcing has a nonnegative potential resolvent almost
everywhere. -/
theorem potentialResolvent_nonneg_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam C : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ potentialResolvent a hα hlam hEll q hq f x := by
  let u : ZeroTraceSobolev U := potentialSolution a hα hlam hEll q hq f
  have hweak : IsPotentialWeakSolution a α q U u f :=
    potentialSolution_isPotentialWeakSolution a hα hlam hEll q hq f
  have hzero : IsPotentialWeakSubsolution a α q U 0 0 := by
    intro φ _
    rw [← potentialBilin_apply (hEll := hEll) (hq := hq)]
    simp only [map_zero, zero_apply, inner_zero_left, le_refl]
  have hzeroForcing : ∀ᵐ x ∂volumeMeasureOn U, (0 : ScalarL2 U) x ≤ f x := by
    filter_upwards [hf, MeasureTheory.Lp.coeFn_zero (E := ℝ)
      (p := (2 : ENNReal)) (volumeMeasureOn U)] with x hfx hx
    simpa only [hx, Pi.zero_apply] using hfx
  have hle := potentialWeakSubsolution_le_weakSupersolution_ae a hU hα hEll q hq
    hzero hweak.isSupersolution hzeroForcing
  have hzeroValue : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 (0 : ZeroTraceSobolev U) x = 0 := by
    rw [map_zero]
    exact MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := (2 : ENNReal)) (volumeMeasureOn U)
  filter_upwards [hle, hzeroValue] with x hx hzero
  simpa only [hzero, potentialResolvent_apply, u] using hx

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
        potentialResolvent a hα hlam hEll q hq g x := by
  have hf := potentialSolution_isPotentialWeakSolution a hα hlam hEll q hq f
  have hg := potentialSolution_isPotentialWeakSolution a hα hlam hEll q hq g
  simpa only [potentialResolvent_apply] using
    potentialWeakSubsolution_le_weakSupersolution_ae a hU hα hEll q hq
      hf.isSubsolution hg.isSupersolution hfg

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
      α * potentialResolvent a hα hlam hEll q hq f x ≤ 1 := by
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
        potentialResolvent a hα hlam hEll q₁ hq₁ f x := by
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
