/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialOrder
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WeakSubsolution

/-!
# PotentialComparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak comparison with a bounded nonnegative potential

This file extends the zero-potential weak comparison principle to the
potential form.  It is used to compare Dirichlet resolvents on nested cubes.
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

end DivergenceFormProcess.Form
