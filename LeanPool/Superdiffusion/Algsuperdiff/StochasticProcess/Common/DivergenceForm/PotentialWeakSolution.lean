/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.MeasureTheory.Function.Holder
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.AlphaShiftedWeakSolution

/-!
# PotentialWeakSolution

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak solutions with a bounded nonnegative potential

This module adds a bounded measurable zeroth-order potential to the shifted
divergence-form equation.  The solution is constructed on the existing
`ZeroTraceSobolev` graph carrier by Lax--Milgram.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}
variable {a : CoeffField d} {α lam Lam C : ℝ} {q : Vec d → ℝ}

open ZeroTraceSobolev

/-- A measurable potential which lies between zero and a finite constant
almost everywhere on the domain. -/
def IsBoundedNonnegativePotential (U : Set (Vec d)) (q : Vec d → ℝ)
    (C : ℝ) : Prop :=
  Measurable q ∧
    (∀ᵐ x ∂volumeMeasureOn U, 0 ≤ q x) ∧
    (∀ᵐ x ∂volumeMeasureOn U, q x ≤ C)

theorem boundedPotential_memLp
    (hq : IsBoundedNonnegativePotential U q C) :
    MemLp q ∞ (volumeMeasureOn U) := by
  apply memLp_top_of_bound hq.1.aestronglyMeasurable C
  filter_upwards [hq.2.1, hq.2.2] with x hq0 hqC
  simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hqC

/-- The L∞ class of a bounded nonnegative potential on the domain. -/
noncomputable def boundedPotentialLp
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C) :
    Lp ℝ ∞ (volumeMeasureOn U) :=
  (boundedPotential_memLp hq).toLp q

/-- Multiplication by a bounded nonnegative potential as a bounded operator on
scalar `L²`. -/
noncomputable def potentialMul
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C) :
    ScalarL2 U →L[ℝ] ScalarL2 U :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL
    (volumeMeasureOn U) ∞ 2 2 (boundedPotentialLp q hq)

/-- Multiplication by the potential agrees almost everywhere with pointwise
multiplication. -/
theorem potentialMul_coeFn
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) :
    potentialMul q hq f =ᵐ[volumeMeasureOn U] fun x => q x * f x := by
  have hmul := ContinuousLinearMap.coeFn_holder (r := (2 : ENNReal))
    (ContinuousLinearMap.mul ℝ ℝ)
    (boundedPotentialLp q hq) f
  have hqcoe := MemLp.coeFn_toLp (boundedPotential_memLp hq)
  filter_upwards [hmul, hqcoe] with x hmulx hqx
  change ContinuousLinearMap.holder 2 (ContinuousLinearMap.mul ℝ ℝ)
      (boundedPotentialLp q hq) f x = q x * f x
  rw [hmulx]
  change boundedPotentialLp q hq x * f x = q x * f x
  change boundedPotentialLp q hq x = q x at hqx
  rw [hqx]

/-- The scalar inner product against a potential multiple is the corresponding
triple-product integral. -/
theorem inner_potentialMul_eq_integral
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f g : ScalarL2 U) :
    inner ℝ (potentialMul q hq f) g =
      ∫ x, q x * f x * g x ∂volumeMeasureOn U := by
  rw [scalarInner_eq_integral]
  apply integral_congr_ae
  filter_upwards [potentialMul_coeFn q hq f] with x hx
  rw [hx]

/-- The unbundled shifted weak form with an additional potential term. -/
noncomputable def shiftedPotentialBilin
    (a : CoeffField d) (α : ℝ) (q : Vec d → ℝ) (U : Set (Vec d))
    (u v : ZeroTraceSobolev U) : ℝ :=
  α * inner ℝ (toL2 u) (toL2 v) +
      coefficientPairing a U (gradient u) (gradient v) +
    ∫ x, q x * toL2 u x * toL2 v x ∂volumeMeasureOn U

/-- The weak equation for a shifted divergence-form operator with potential. -/
def IsPotentialWeakSolution
    (a : CoeffField d) (α : ℝ) (q : Vec d → ℝ) (U : Set (Vec d))
    (u : ZeroTraceSobolev U) (f : ScalarL2 U) : Prop :=
  ∀ v : ZeroTraceSobolev U,
    shiftedPotentialBilin a α q U u v = inner ℝ f (toL2 v)

/-- The continuous bilinear form of the shifted divergence-form operator with
a bounded nonnegative potential. -/
noncomputable def potentialBilin
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C) :
    ZeroTraceSobolev U →L[ℝ] ZeroTraceSobolev U →L[ℝ] ℝ :=
  shiftedBilin hEll α +
    ContinuousLinearMap.bilinearComp
      (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
      ((potentialMul q hq).comp toL2) toL2

/-- Evaluation of the bundled potential form agrees with the stated weak
form. -/
theorem potentialBilin_apply
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (u v : ZeroTraceSobolev U) :
    potentialBilin (α := α) hEll q hq u v =
      shiftedPotentialBilin a α q U u v := by
  simp only [potentialBilin, add_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    shiftedPotentialBilin]
  change shiftedBilin hEll α u v +
      inner ℝ (potentialMul q hq (toL2 u)) (toL2 v) = _
  rw [shiftedBilin_apply, inner_potentialMul_eq_integral]

private theorem potentialTerm_nonneg
    (hq : IsBoundedNonnegativePotential U q C)
    (u : ZeroTraceSobolev U) :
    0 ≤ inner ℝ (potentialMul q hq (toL2 u)) (toL2 u) := by
  rw [scalarInner_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards [potentialMul_coeFn q hq (toL2 u), hq.2.1] with x hx hqx
  rw [hx]
  rw [mul_assoc]
  exact mul_nonneg hqx (mul_self_nonneg _)

private theorem potentialBilin_lower_bound
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hq : IsBoundedNonnegativePotential U q C)
    (u : ZeroTraceSobolev U) :
    min α lam * ‖u‖ * ‖u‖ ≤ potentialBilin (α := α) hEll q hq u u := by
  calc
    min α lam * ‖u‖ * ‖u‖ ≤ shiftedBilin hEll α u u :=
      shiftedBilin_lower_bound hEll u
    _ ≤ shiftedBilin hEll α u u +
        inner ℝ (potentialMul q hq (toL2 u)) (toL2 u) :=
      le_add_of_nonneg_right (potentialTerm_nonneg hq u)
    _ = potentialBilin (α := α) hEll q hq u u := by
      simp only [potentialBilin, add_apply,
        ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply]
      rfl

theorem potentialBilin_coercive
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hq : IsBoundedNonnegativePotential U q C) :
    IsCoercive (potentialBilin (α := α) hEll q hq) :=
  ⟨min α lam, lt_min hα hlam, potentialBilin_lower_bound hEll hq⟩

/-- Existence and uniqueness for the weak equation with bounded nonnegative
potential. -/
theorem existsUnique_isPotentialWeakSolution
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) :
    ∃! u : ZeroTraceSobolev U, IsPotentialWeakSolution a α q U u f := by
  let hB : IsCoercive (potentialBilin (α := α) hEll q hq) :=
    potentialBilin_coercive hα hlam hEll hq
  let e : ZeroTraceSobolev U ≃L[ℝ] ZeroTraceSobolev U :=
    hB.continuousLinearEquivOfBilin
  let r : ZeroTraceSobolev U :=
    (InnerProductSpace.toDual ℝ (ZeroTraceSobolev U)).symm
      ((InnerProductSpace.toDual ℝ (ScalarL2 U) f).comp toL2)
  have hr (v : ZeroTraceSobolev U) :
      inner ℝ r v = inner ℝ f (toL2 v) := by
    exact InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ) (E := ZeroTraceSobolev U) (x := v)
      (y := (((InnerProductSpace.toDual ℝ (ScalarL2 U) f).comp toL2) :
        StrongDual ℝ (ZeroTraceSobolev U)))
  refine ⟨e.symm r, ?_, ?_⟩
  · intro v
    rw [← potentialBilin_apply hEll q hq]
    calc
      potentialBilin (α := α) hEll q hq (e.symm r) v =
          inner ℝ (e (e.symm r)) v := by
        symm
        exact hB.continuousLinearEquivOfBilin_apply (e.symm r) v
      _ = inner ℝ r v := by rw [e.apply_symm_apply]
      _ = inner ℝ f (toL2 v) := hr v
  · intro u hu
    have huRiesz : r = e u := by
      apply hB.unique_continuousLinearEquivOfBilin
      intro v
      rw [hr v, potentialBilin_apply hEll q hq]
      exact (hu v).symm
    apply e.injective
    rw [← huRiesz, e.apply_symm_apply]

/-- The canonical bounded linear weak-solution operator with potential. -/
noncomputable def potentialSolution
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C) :
    ScalarL2 U →L[ℝ] ZeroTraceSobolev U :=
  let hB : IsCoercive (potentialBilin (α := α) hEll q hq) :=
    potentialBilin_coercive hα hlam hEll hq
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint (toL2 (U := U)))

/-- The canonical operator solves the weak equation with potential. -/
theorem potentialSolution_isPotentialWeakSolution
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) :
    IsPotentialWeakSolution a α q U
      (potentialSolution a hα hlam hEll q hq f) f := by
  let hB : IsCoercive (potentialBilin (α := α) hEll q hq) :=
    potentialBilin_coercive hα hlam hEll hq
  let e : ZeroTraceSobolev U ≃L[ℝ] ZeroTraceSobolev U :=
    hB.continuousLinearEquivOfBilin
  intro v
  rw [← potentialBilin_apply hEll q hq]
  calc
    potentialBilin (α := α) hEll q hq
        (potentialSolution a hα hlam hEll q hq f) v =
        inner ℝ (e (potentialSolution a hα hlam hEll q hq f)) v := by
      symm
      exact hB.continuousLinearEquivOfBilin_apply
        (potentialSolution a hα hlam hEll q hq f) v
    _ = inner ℝ
        (ContinuousLinearMap.adjoint (toL2 (U := U)) f) v := by
      change inner ℝ (e (e.symm
        (ContinuousLinearMap.adjoint (toL2 (U := U)) f))) v = _
      rw [e.apply_symm_apply]
    _ = inner ℝ f (toL2 v) :=
      ContinuousLinearMap.adjoint_inner_left (toL2 (U := U)) v f

/-- A weak solution with potential is exactly the canonical solution. -/
theorem isPotentialWeakSolution_iff_eq
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) (u : ZeroTraceSobolev U) :
    IsPotentialWeakSolution a α q U u f ↔
      u = potentialSolution a hα hlam hEll q hq f := by
  constructor
  · intro hu
    exact (existsUnique_isPotentialWeakSolution a hα hlam hEll q hq f).unique
      hu (potentialSolution_isPotentialWeakSolution a hα hlam hEll q hq f)
  · rintro rfl
    exact potentialSolution_isPotentialWeakSolution a hα hlam hEll q hq f

/-- The scalar `L²` resolvent with bounded nonnegative potential. -/
noncomputable def potentialResolvent
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C) :
    ScalarL2 U →L[ℝ] ScalarL2 U :=
  toL2.comp (potentialSolution a hα hlam hEll q hq)

/-- The potential resolvent is the value component of the weak solution. -/
@[simp] theorem potentialResolvent_apply
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) :
    potentialResolvent a hα hlam hEll q hq f =
      toL2 (potentialSolution a hα hlam hEll q hq f) := rfl

/-- The identically zero function is a bounded nonnegative potential. -/
theorem isBoundedNonnegativePotential_zero (U : Set (Vec d)) :
    IsBoundedNonnegativePotential U (fun _ => (0 : ℝ)) 0 :=
  ⟨measurable_const,
    Filter.Eventually.of_forall fun _ => le_rfl,
    Filter.Eventually.of_forall fun _ => le_rfl⟩

/-- For the zero potential the weak-solution operator with potential is the
alpha-shifted weak-solution operator. -/
theorem potentialSolution_zero_potential
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hq : IsBoundedNonnegativePotential U (fun _ => (0 : ℝ)) C)
    (f : ScalarL2 U) :
    potentialSolution a hα hlam hEll (fun _ => (0 : ℝ)) hq f =
      alphaShiftedSolution a hα hlam hEll f := by
  symm
  rw [← isPotentialWeakSolution_iff_eq a hα hlam hEll _ hq f]
  intro v
  have hweak :=
    alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEll f v
  simpa only [shiftedPotentialBilin, zero_mul, integral_zero, add_zero]
    using hweak

/-- For the zero potential the scalar resolvent with potential is the
alpha-shifted resolvent. -/
theorem potentialResolvent_zero_potential
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hq : IsBoundedNonnegativePotential U (fun _ => (0 : ℝ)) C)
    (f : ScalarL2 U) :
    potentialResolvent a hα hlam hEll (fun _ => (0 : ℝ)) hq f =
      alphaShiftedResolvent a hα hlam hEll f := by
  rw [potentialResolvent_apply, potentialSolution_zero_potential,
    alphaShiftedResolvent_apply]

/-- Resolvent identity in the positive shift for a fixed potential. -/
theorem potentialSolution_resolvent_identity
    (a : CoeffField d) {U : Set (Vec d)} {α β lam Lam C : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) :
    potentialSolution a hα hlam hEll q hq f -
        potentialSolution a hβ hlam hEll q hq f =
      (β - α) • potentialSolution a hα hlam hEll q hq
        (potentialResolvent a hβ hlam hEll q hq f) := by
  let uα := potentialSolution a hα hlam hEll q hq f
  let uβ := potentialSolution a hβ hlam hEll q hq f
  have hαweak := potentialSolution_isPotentialWeakSolution
    a hα hlam hEll q hq f
  have hβweak := potentialSolution_isPotentialWeakSolution
    a hβ hlam hEll q hq f
  have hdiff : IsPotentialWeakSolution a α q U (uα - uβ)
      ((β - α) • potentialResolvent a hβ hlam hEll q hq f) := by
    intro v
    rw [← potentialBilin_apply hEll q hq]
    rw [map_sub, sub_apply]
    rw [potentialBilin_apply hEll q hq, potentialBilin_apply hEll q hq]
    change shiftedPotentialBilin a α q U uα v -
      shiftedPotentialBilin a α q U uβ v = _
    have hβexpand : shiftedPotentialBilin a α q U uβ v =
        shiftedPotentialBilin a β q U uβ v +
          (α - β) * inner ℝ (toL2 uβ) (toL2 v) := by
      simp only [shiftedPotentialBilin]
      ring
    rw [hαweak v, hβexpand, hβweak v]
    simp only [uβ, potentialResolvent_apply, real_inner_smul_left]
    ring
  calc
    uα - uβ =
        potentialSolution a hα hlam hEll q hq
          ((β - α) • potentialResolvent a hβ hlam hEll q hq f) :=
      (isPotentialWeakSolution_iff_eq a hα hlam hEll q hq _ _).1 hdiff
    _ = (β - α) • potentialSolution a hα hlam hEll q hq
        (potentialResolvent a hβ hlam hEll q hq f) := by rw [map_smul]

/-- Operator resolvent identity in the positive shift for a fixed potential. -/
theorem potentialResolvent_resolvent_identity
    (a : CoeffField d) {U : Set (Vec d)} {α β lam Lam C : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C) :
    potentialResolvent a hα hlam hEll q hq -
        potentialResolvent a hβ hlam hEll q hq =
      (β - α) • ((potentialResolvent a hα hlam hEll q hq).comp
        (potentialResolvent a hβ hlam hEll q hq)) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, potentialResolvent_apply]
  rw [← map_sub,
    potentialSolution_resolvent_identity a hα hβ hlam hEll q hq f, map_smul]
  rfl

/-- The solution with potential is the unperturbed solution minus the
unperturbed resolvent applied to the potential load. -/
theorem potentialResolvent_perturbation_identity
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) :
    potentialResolvent a hα hlam hEll q hq f =
      alphaShiftedResolvent a hα hlam hEll f -
        alphaShiftedResolvent a hα hlam hEll
          (potentialMul q hq (potentialResolvent a hα hlam hEll q hq f)) := by
  let u := potentialSolution a hα hlam hEll q hq f
  let g := f - potentialMul q hq (toL2 u)
  have hu : IsAlphaShiftedWeakSolution a U α g u := by
    intro v
    have hweak := potentialSolution_isPotentialWeakSolution
      a hα hlam hEll q hq f v
    dsimp only [shiftedPotentialBilin] at hweak
    rw [← shiftedBilin_apply hEll α u v,
      ← inner_potentialMul_eq_integral (C := C) q hq (toL2 u) (toL2 v)] at hweak
    rw [← shiftedBilin_apply hEll α u v, inner_sub_left]
    exact eq_sub_of_add_eq hweak
  have huid : u = alphaShiftedSolution a hα hlam hEll g :=
    (isAlphaShiftedWeakSolution_iff_eq a hα hlam hEll g u).1 hu
  change toL2 u = _
  rw [huid]
  dsimp only [g]
  rw [map_sub, map_sub]
  rfl

/-- Coercive graph-norm energy estimate for the potential solution. -/
theorem potentialSolution_energy_le
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) :
    min α lam * ‖potentialSolution a hα hlam hEll q hq f‖ ^ 2 ≤
      ‖f‖ * ‖potentialResolvent a hα hlam hEll q hq f‖ := by
  let u := potentialSolution a hα hlam hEll q hq f
  have hlower := potentialBilin_lower_bound
    (α := α) hEll hq u
  have hweak := potentialSolution_isPotentialWeakSolution
    a hα hlam hEll q hq f u
  rw [← potentialBilin_apply hEll q hq] at hweak
  change min α lam * ‖u‖ ^ 2 ≤ ‖f‖ * ‖toL2 u‖
  calc
    min α lam * ‖u‖ ^ 2 = min α lam * ‖u‖ * ‖u‖ := by ring
    _ ≤ potentialBilin (α := α) hEll q hq u u := hlower
    _ = inner ℝ f (toL2 u) := hweak
    _ ≤ ‖f‖ * ‖toL2 u‖ := real_inner_le_norm f (toL2 u)

/-- The potential energy is bounded by the forcing paired with the solution. -/
theorem potentialIntegral_sq_le
    (a : CoeffField d) {U : Set (Vec d)} {α lam Lam C : ℝ}
    (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q C)
    (f : ScalarL2 U) :
    (∫ x, q x * (potentialResolvent a hα hlam hEll q hq f x) ^ 2
        ∂volumeMeasureOn U) ≤
      ‖f‖ * ‖potentialResolvent a hα hlam hEll q hq f‖ := by
  let u := potentialSolution a hα hlam hEll q hq f
  have hweak := potentialSolution_isPotentialWeakSolution
    a hα hlam hEll q hq f u
  have hcoeff : 0 ≤ coefficientPairing a U (gradient u) (gradient u) := by
    exact coefficientPairing_nonneg_of_ae_eq_indicator hEll _ _ Set.univ
      (Filter.Eventually.of_forall fun x => by simp)
  change (∫ x, q x * (toL2 u x) ^ 2 ∂volumeMeasureOn U) ≤ _
  dsimp only [shiftedPotentialBilin] at hweak
  calc
    (∫ x, q x * (toL2 u x) ^ 2 ∂volumeMeasureOn U) ≤
        α * inner ℝ (toL2 u) (toL2 u) +
          coefficientPairing a U (gradient u) (gradient u) +
          ∫ x, q x * toL2 u x * toL2 u x ∂volumeMeasureOn U := by
      have hmass : 0 ≤ α * inner ℝ (toL2 u) (toL2 u) :=
        mul_nonneg hα.le real_inner_self_nonneg
      have hint : (∫ x, q x * (toL2 u x) ^ 2 ∂volumeMeasureOn U) =
          ∫ x, q x * toL2 u x * toL2 u x ∂volumeMeasureOn U := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      rw [hint]
      exact le_add_of_nonneg_left (add_nonneg hmass hcoeff)
    _ = inner ℝ f (toL2 u) := hweak
    _ ≤ ‖f‖ * ‖toL2 u‖ := real_inner_le_norm f (toL2 u)

end DivergenceFormProcess.Form
