/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.Order.MonotoneConvergence
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Truncation.WeakGradientLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialOrder

/-!
# PenalizationSequence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exterior penalization on a nested domain

This module constructs the bounded potentials which penalize the complement
of a part domain and proves the compactness estimates for their resolvents.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ} {V U : Set (Vec d)}

/-- The exterior penalization potential `n · 1_(U \ V)`. -/
noncomputable def penalizationPotential
    (U V : Set (Vec d)) (n : ℕ) (x : Vec d) : ℝ :=
  (U \ V).indicator (fun _ => (n : ℝ)) x

/-- The exterior penalization is a bounded nonnegative potential. -/
theorem penalizationPotential_isBoundedNonnegative
    (hU : MeasurableSet U) (hV : MeasurableSet V) (n : ℕ) :
    IsBoundedNonnegativePotential U (penalizationPotential U V n) n := by
  refine ⟨measurable_const.indicator (MeasurableSet.diff hU hV), ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ U \ V
      · rw [penalizationPotential, Set.indicator_of_mem hx]
        exact Nat.cast_nonneg n
      · rw [penalizationPotential, Set.indicator_of_notMem hx]
  · exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ U \ V
      · rw [penalizationPotential, Set.indicator_of_mem hx]
      · rw [penalizationPotential, Set.indicator_of_notMem hx]
        exact Nat.cast_nonneg n

/-- The zero-trace solution of the exterior-penalized problem. -/
noncomputable def penalizedSolution
    (a : CoeffField d) (hU : IsOpen U) (hV : IsOpen V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (n : ℕ) :
    ScalarL2 U →L[ℝ] ZeroTraceSobolev U :=
  potentialSolution a hα hlam hEll (penalizationPotential U V n)
    (penalizationPotential_isBoundedNonnegative
      hU.measurableSet hV.measurableSet n)

/-- The scalar `L²` resolvent of the exterior-penalized problem. -/
noncomputable def penalizedResolvent
    (a : CoeffField d) (hU : IsOpen U) (hV : IsOpen V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (n : ℕ) :
    ScalarL2 U →L[ℝ] ScalarL2 U :=
  potentialResolvent a hα hlam hEll (penalizationPotential U V n)
    (penalizationPotential_isBoundedNonnegative
      hU.measurableSet hV.measurableSet n)

/-- The penalized resolvent is the value component of the penalized solution. -/
@[simp] theorem penalizedResolvent_apply
    (a : CoeffField d) (hU : IsOpen U) (hV : IsOpen V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (n : ℕ) (f : ScalarL2 U) :
    penalizedResolvent a hU hV hα hlam hEll n f =
      ZeroTraceSobolev.toL2
        (penalizedSolution a hU hV hα hlam hEll n f) := rfl

/-- The exterior potentials increase with the penalization parameter. -/
theorem penalizationPotential_mono (hU : MeasurableSet U)
    (n m : ℕ) (hnm : n ≤ m) :
    ∀ᵐ x ∂volumeMeasureOn U,
      penalizationPotential U V n x ≤ penalizationPotential U V m x := by
  filter_upwards [self_mem_ae_restrict hU] with x hxU
  by_cases hxV : x ∈ V
  · have hxn : x ∉ U \ V := fun hx => hx.2 hxV
    rw [penalizationPotential, penalizationPotential,
      Set.indicator_of_notMem hxn, Set.indicator_of_notMem hxn]
  · have hx : x ∈ U \ V := ⟨hxU, hxV⟩
    rw [penalizationPotential, penalizationPotential,
      Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    exact_mod_cast hnm

/-- Penalized resolvents of nonnegative data decrease almost everywhere as
the exterior penalty increases. -/
theorem penalizedResolvent_antitone_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x)
    (n m : ℕ) (hnm : n ≤ m) :
    ∀ᵐ x ∂volumeMeasureOn U,
      penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll m f x ≤
        penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f x  := by
  exact potentialResolvent_antitone_potential_ae a hU hα hlam hEll
    (penalizationPotential U V n)
    (penalizationPotential U V m)
    (penalizationPotential_isBoundedNonnegative
      hU.isOpen.measurableSet hV.isOpen.measurableSet n)
    (penalizationPotential_isBoundedNonnegative
      hU.isOpen.measurableSet hV.isOpen.measurableSet m)
    (penalizationPotential_mono hU.isOpen.measurableSet n m hnm) f hf

/-- Penalized resolvents of nonnegative data are nonnegative almost
everywhere. -/
theorem penalizedResolvent_nonneg_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x)
    (n : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f x  := by
  exact potentialResolvent_nonneg_ae a hU hα hlam hEll
    (penalizationPotential U V n)
    (penalizationPotential_isBoundedNonnegative
      hU.isOpen.measurableSet hV.isOpen.measurableSet n) f hf

/-- The zero-trace graph norms of the penalized solutions have a bound
independent of the penalty. -/
theorem norm_penalizedSolution_le
    (a : CoeffField d) (hU : IsOpen U) (hV : IsOpen V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (n : ℕ) :
    ‖penalizedSolution a hU hV hα hlam hEll n f‖ ≤
      (min α lam)⁻¹ * ‖f‖ := by
  let u := penalizedSolution a hU hV hα hlam hEll n f
  have henergy := potentialSolution_energy_le a hα hlam hEll
    (penalizationPotential U V n)
    (penalizationPotential_isBoundedNonnegative
      hU.measurableSet hV.measurableSet n) f
  change ‖u‖ ≤ (min α lam)⁻¹ * ‖f‖
  have henergy' : min α lam * ‖u‖ * ‖u‖ ≤ ‖f‖ * ‖u‖ := by
    calc
      min α lam * ‖u‖ * ‖u‖ = min α lam * ‖u‖ ^ 2 := by ring
      _ ≤ ‖f‖ * ‖ZeroTraceSobolev.toL2 u‖ := henergy
      _ ≤ ‖f‖ * ‖u‖ :=
        mul_le_mul_of_nonneg_left
          (ZeroTraceSobolev.norm_toL2_le u) (norm_nonneg f)
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    exact mul_nonneg (inv_nonneg.mpr (lt_min hα hlam).le) (norm_nonneg f)
  · have huPos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    apply (le_inv_mul_iff₀ (lt_min hα hlam)).2
    apply (mul_le_mul_iff_right₀ huPos).1
    simpa only [mul_assoc, mul_comm] using henergy'

/-- The potential-energy estimate is exactly an exterior `L²` penalty
estimate. -/
theorem penalized_exterior_integral_le
    (a : CoeffField d) (hU : IsOpen U) (hV : IsOpen V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (n : ℕ) :
    (n : ℝ) *
        ∫ x in U \ V,
          (penalizedResolvent a hU hV hα hlam hEll n f x) ^ 2 ∂volume ≤
      ‖f‖ * ‖penalizedResolvent a hU hV hα hlam hEll n f‖ := by
  have henergy := potentialIntegral_sq_le a hα hlam hEll
    (penalizationPotential U V n)
    (penalizationPotential_isBoundedNonnegative
      hU.measurableSet hV.measurableSet n) f
  rw [show ((n : ℝ) * ∫ x in U \ V,
      (penalizedResolvent a hU hV hα hlam hEll n f x) ^ 2 ∂volume) =
      ∫ x, penalizationPotential U V n x *
        (penalizedResolvent a hU hV hα hlam hEll n f x) ^ 2
          ∂volumeMeasureOn U by
    rw [← integral_const_mul]
    change (
      ∫ x, (n : ℝ) *
          (penalizedResolvent a hU hV hα hlam hEll n f x) ^ 2
        ∂volume.restrict (U \ V)) = _
    rw [← Measure.restrict_restrict_of_subset (Set.sdiff_subset)]
    rw [← MeasureTheory.integral_indicator
      (MeasurableSet.diff hU.measurableSet hV.measurableSet)]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict hU.measurableSet] with x hxU
    by_cases hxV : x ∈ V
    · have hxnot : x ∉ U \ V := fun hx => hx.2 hxV
      rw [penalizationPotential, Set.indicator_of_notMem hxnot,
        Set.indicator_of_notMem hxnot, zero_mul]
    · have hx : x ∈ U \ V := ⟨hxU, hxV⟩
      rw [penalizationPotential, Set.indicator_of_mem hx,
        Set.indicator_of_mem hx]]
  exact henergy

/-- The pointwise infimum of the exterior-penalized resolvents. -/
noncomputable def penalizationPointwiseLimit
    (a : CoeffField d) (hU : IsOpen U) (hV : IsOpen V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) : Vec d → ℝ :=
  fun x => ⨅ n, penalizedResolvent a hU hV hα hlam hEll n f x

/-- The penalized resolvents converge almost everywhere to their pointwise
infimum. -/
theorem penalizedResolvent_tendsto_pointwiseLimit_ae
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      Tendsto
        (fun n => penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f x)
        atTop (nhds (penalizationPointwiseLimit
          a hU.isOpen hV.isOpen hα hlam hEll f x))  := by
  have hnonneg : ∀ n, ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f x :=
    fun n => penalizedResolvent_nonneg_ae a hU hV hα hlam hEll f hf n
  have hanti : ∀ n m, n ≤ m → ∀ᵐ x ∂volumeMeasureOn U,
      penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll m f x ≤
        penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f x :=
    fun n m hnm =>
      penalizedResolvent_antitone_ae a hU hV hα hlam hEll f hf n m hnm
  have hantiNM : ∀ n m, ∀ᵐ x ∂volumeMeasureOn U, n ≤ m →
      penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll m f x ≤
        penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f x := by
    intro n m
    by_cases hnm : n ≤ m
    · exact (hanti n m hnm).mono fun _ hx _ => hx
    · exact Filter.Eventually.of_forall fun _ h => (hnm h).elim
  filter_upwards [ae_all_iff.2 hnonneg,
    ae_all_iff.2 fun n => ae_all_iff.2 fun m => hantiNM n m]
      with x hx0 hxanti
  apply tendsto_atTop_ciInf
  · intro n m hnm
    exact hxanti n m hnm
  · refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hx0 n

/-- The pointwise infimum of the penalized resolvents belongs to `L²(U)`. -/
theorem penalizationPointwiseLimit_memLp (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    MemLp (penalizationPointwiseLimit
      a hU.isOpen hV.isOpen hα hlam hEll f) 2 (volumeMeasureOn U)  := by
  let u : ℕ → ScalarL2 U := fun n =>
    penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f
  let g := penalizationPointwiseLimit
    a hU.isOpen hV.isOpen hα hlam hEll f
  have htend : ∀ᵐ x ∂volumeMeasureOn U,
      Tendsto (fun n => u n x) atTop (nhds (g x)) :=
    penalizedResolvent_tendsto_pointwiseLimit_ae a hU hV hα hlam hEll f hf
  have hmeas : AEStronglyMeasurable g (volumeMeasureOn U) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (MeasureTheory.Lp.memLp (u n)).aestronglyMeasurable) htend
  have hbound : ∀ᵐ x ∂volumeMeasureOn U, ‖g x‖ ≤ ‖u 0 x‖ := by
    have hnonneg : ∀ n, ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ u n x :=
      fun n => penalizedResolvent_nonneg_ae
        a hU hV hα hlam hEll f hf n
    have hle := penalizedResolvent_antitone_ae
      a hU hV hα hlam hEll f hf 0
    filter_upwards [htend, ae_all_iff.2 hnonneg,
      ae_all_iff.2 fun n => hle n (Nat.zero_le n)] with x hx hx0 hxle
    have hg0 : 0 ≤ g x := ge_of_tendsto hx
      (Filter.Eventually.of_forall fun n => hx0 n)
    have hgu : g x ≤ u 0 x := le_of_tendsto hx
      (Filter.Eventually.of_forall fun n => hxle n)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hg0,
      abs_of_nonneg (hx0 0)] using hgu
  exact ((eLpNorm_mono_ae hmeas hbound).trans_lt (MeasureTheory.Lp.eLpNorm_lt_top (u 0)))

/-- The monotone penalized resolvents converge strongly in `L²(U)` to their
almost-everywhere infimum. -/
theorem penalizedResolvent_tendsto_L2 (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    Tendsto
      (fun n => penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f)
      atTop
      (nhds ((penalizationPointwiseLimit_memLp
        a hU hV hα hlam hEll f hf).toLp
          (penalizationPointwiseLimit
            a hU.isOpen hV.isOpen hα hlam hEll f)))  := by
  let u : ℕ → ScalarL2 U := fun n =>
    penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f
  let g := penalizationPointwiseLimit
    a hU.isOpen hV.isOpen hα hlam hEll f
  have htend : ∀ᵐ x ∂volumeMeasureOn U,
      Tendsto (fun n => u n x) atTop (nhds (g x)) :=
    penalizedResolvent_tendsto_pointwiseLimit_ae a hU hV hα hlam hEll f hf
  have hg : MemLp g 2 (volumeMeasureOn U) :=
    penalizationPointwiseLimit_memLp a hU hV hα hlam hEll f hf
  have hdom : ∀ n, ∀ᵐ x ∂volumeMeasureOn U, ‖u n x‖ ≤ u 0 x := by
    intro n
    have hnonneg := penalizedResolvent_nonneg_ae
      a hU hV hα hlam hEll f hf n
    have hzero := penalizedResolvent_nonneg_ae
      a hU hV hα hlam hEll f hf 0
    have hle := penalizedResolvent_antitone_ae
      a hU hV hα hlam hEll f hf 0 n (Nat.zero_le n)
    filter_upwards [hnonneg, hzero, hle] with x hnx h0x hnx0
    dsimp only [u] at hnx h0x hnx0 ⊢
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnx] using hnx0
  have heLp := HCPolySupport.tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
    (fun n => (MeasureTheory.Lp.memLp (u n)).aestronglyMeasurable) hg
    (MeasureTheory.Lp.memLp (u 0)) hdom htend
  exact MeasureTheory.Lp.tendsto_Lp_of_tendsto_eLpNorm g hg heLp

end DivergenceFormProcess.Form
