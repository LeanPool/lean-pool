/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationSequence
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainZeroTrace
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# PenalizationLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Identification of the exterior-penalization limit

The compactness limit of the penalized problems is identified with the
zero extension of the shifted Dirichlet resolvent on the part domain.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ} {V U : Set (Vec d)}

private theorem exists_weaklyConvergent_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (s : ℕ → H) (M : ℝ) (hM : ∀ n, ‖s n‖ ≤ M) :
    ∃ z : H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ v : H,
        Tendsto (fun n => inner ℝ (s (φ n)) v) atTop (nhds (inner ℝ z v)) := by
  let ds : ℕ → WeakDual ℝ H := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (s n))
  have hmem : ∀ n, ds n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) M := by
    intro n
    change dist (WeakDual.toStrongDual (ds n)) 0 ≤ M
    rw [dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ H (s n)‖ ≤ M
    simpa only [LinearIsometryEquiv.norm_map] using hM n
  obtain ⟨b, -, φ, hφ, hb⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) M hmem
  let z : H := (InnerProductSpace.toDual ℝ H).symm
    (WeakDual.toStrongDual b)
  refine ⟨z, φ, hφ, fun v => ?_⟩
  have hev := (WeakDual.eval_continuous v).tendsto b |>.comp hb
  simpa only [Function.comp_apply, ds, StrongDual.coe_toWeakDual,
    InnerProductSpace.toDual_apply_apply, z,
    InnerProductSpace.toDual_symm_apply] using! hev

noncomputable def exteriorRestriction
    (hU : MeasurableSet U) : ScalarL2 U →L[ℝ] ScalarL2 (U \ V) :=
  (restrictToDomain (U \ V)).comp
    (zeroExtendFromDomain hU).toContinuousLinearMap

private theorem exteriorRestriction_coeFn
    (hU : MeasurableSet U) (hV : MeasurableSet V) (f : ScalarL2 U) :
    exteriorRestriction (V := V) hU f =ᵐ[volumeMeasureOn (U \ V)] f := by
  filter_upwards
    [restrictToDomain_coeFn (U \ V) (zeroExtendFromDomain hU f),
      ae_restrict_of_ae (zeroExtendFromDomain_coeFn hU f),
      self_mem_ae_restrict (hU.diff hV)]
      with x hrestrict hzero hx
  change restrictToDomain (U \ V) (zeroExtendFromDomain hU f) x = f x
  rw [hrestrict, hzero, Set.indicator_of_mem hx.1]

private theorem norm_exteriorRestriction_sq
    (hU : MeasurableSet U) (hV : MeasurableSet V) (f : ScalarL2 U) :
    ‖exteriorRestriction (V := V) hU f‖ ^ 2 =
      ∫ x in U \ V, (f x) ^ 2 ∂volume := by
  rw [← real_inner_self_eq_norm_sq, scalarInner_eq_integral]
  apply integral_congr_ae
  filter_upwards [exteriorRestriction_coeFn (V := V) hU hV f] with x hx
  rw [hx]
  ring

private theorem shiftedBilin_tendsto_of_weak
    {a : CoeffField d} {α lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    {s : ℕ → ZeroTraceSobolev U} {z : ZeroTraceSobolev U}
    (hs : ∀ v : ZeroTraceSobolev U,
      Tendsto (fun n => inner ℝ (s n) v) atTop (nhds (inner ℝ z v)))
    (v : ZeroTraceSobolev U) :
    Tendsto (fun n => shiftedBilin hEll α (s n) v) atTop
      (nhds (shiftedBilin hEll α z v)) := by
  let L : StrongDual ℝ (ZeroTraceSobolev U) :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp (shiftedBilin hEll α)
  let r : ZeroTraceSobolev U :=
    (InnerProductSpace.toDual ℝ (ZeroTraceSobolev U)).symm L
  have h := hs r
  have heq (w : ZeroTraceSobolev U) :
      inner ℝ w r = shiftedBilin hEll α w v := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  rw [← heq z]
  exact h.congr' (Filter.Eventually.of_forall fun n => heq (s n))

private theorem toL2_eq_of_weak_and_strong
    {s : ℕ → ZeroTraceSobolev U} {z : ZeroTraceSobolev U}
    {g : ScalarL2 U}
    (hweak : ∀ v : ZeroTraceSobolev U,
      Tendsto (fun n => inner ℝ (s n) v) atTop (nhds (inner ℝ z v)))
    (hstrong : Tendsto (fun n => ZeroTraceSobolev.toL2 (s n))
      atTop (nhds g)) :
    ZeroTraceSobolev.toL2 z = g := by
  apply ext_inner_left ℝ
  intro v
  let T : ZeroTraceSobolev U →L[ℝ] ScalarL2 U := ZeroTraceSobolev.toL2
  let r : ZeroTraceSobolev U := ContinuousLinearMap.adjoint T v
  have hw := hweak r
  have hweakL2 : Tendsto
      (fun n => inner ℝ v (ZeroTraceSobolev.toL2 (s n))) atTop
      (nhds (inner ℝ v (ZeroTraceSobolev.toL2 z))) := by
    have heq (w : ZeroTraceSobolev U) :
        inner ℝ w r = inner ℝ v (ZeroTraceSobolev.toL2 w) := by
      rw [real_inner_comm]
      exact ContinuousLinearMap.adjoint_inner_left T w v
    rw [← heq z]
    exact hw.congr' (Filter.Eventually.of_forall fun n => heq (s n))
  have hstrongL2 :=
    (InnerProductSpace.toDual ℝ (ScalarL2 U) v).continuous.tendsto g |>.comp hstrong
  exact tendsto_nhds_unique hweakL2 hstrongL2

private theorem norm_exteriorRestriction_penalized_tendsto_zero
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    Tendsto
      (fun n => ‖exteriorRestriction (V := V) hU.isOpen.measurableSet
        (penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll (n + 1) f)‖)
      atTop (nhds 0) := by
  let M : ℝ := (min α lam)⁻¹ * ‖f‖
  let B : ℝ := ‖f‖ * M
  let r : ℕ → ScalarL2 (U \ V) := fun n =>
    exteriorRestriction (V := V) hU.isOpen.measurableSet
      (penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll (n + 1) f)
  change Tendsto (fun n => ‖r n‖) atTop (nhds 0)
  have hsqle : ∀ n, ‖r n‖ ^ 2 ≤ B * ((n + 1 : ℕ) : ℝ)⁻¹ := by
    intro n
    have hpen := penalized_exterior_integral_le
      a hU.isOpen hV.isOpen hα hlam hEll f (n + 1)
    have hres :
        ‖penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll (n + 1) f‖ ≤ M := by
      calc
        ‖penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll (n + 1) f‖ ≤
            ‖penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll (n + 1) f‖ :=
          ZeroTraceSobolev.norm_toL2_le _
        _ ≤ M := norm_penalizedSolution_le
          a hU.isOpen hV.isOpen hα hlam hEll f (n + 1)
    have hpen' : ((n + 1 : ℕ) : ℝ) * ‖r n‖ ^ 2 ≤ B := by
      calc
        ((n + 1 : ℕ) : ℝ) * ‖r n‖ ^ 2 =
            ((n + 1 : ℕ) : ℝ) *
              ∫ x in U \ V,
                (penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll
                  (n + 1) f x) ^ 2 ∂volume := by
          rw [norm_exteriorRestriction_sq
            hU.isOpen.measurableSet hV.isOpen.measurableSet]
        _ ≤ ‖f‖ *
            ‖penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll
              (n + 1) f‖ := hpen
        _ ≤ B := mul_le_mul_of_nonneg_left hres (norm_nonneg f)
    apply (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).2
    simpa only [mul_comm] using hpen'
  have hupper : Tendsto (fun n : ℕ => B * ((n + 1 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) := by
    have hone : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹)
        atTop (nhds 0) := by
      simpa only [one_div, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero] using hone.const_mul B
  have hsq : Tendsto (fun n => ‖r n‖ ^ 2) atTop (nhds 0) :=
    squeeze_zero (fun n => sq_nonneg ‖r n‖) hsqle hupper
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun n => Real.sqrt (‖r n‖ ^ 2)) atTop
    (nhds (Real.sqrt 0)) at hsqrt
  simpa only [Function.comp_apply, Real.sqrt_sq_eq_abs, abs_norm,
    Real.sqrt_zero] using hsqrt

private theorem exists_penalization_weak_limit
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    ∃ z : ZeroTraceSobolev U, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ v : ZeroTraceSobolev U,
        Tendsto
          (fun n => inner ℝ
            (penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll
              (φ n + 1) f) v)
          atTop (nhds (inner ℝ z v)) := by
  let s : ℕ → ZeroTraceSobolev U := fun n =>
    penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll (n + 1) f
  exact exists_weaklyConvergent_subsequence s ((min α lam)⁻¹ * ‖f‖)
    (fun n => norm_penalizedSolution_le
      a hU.isOpen hV.isOpen hα hlam hEll f (n + 1))

private theorem exteriorRestriction_eq_zero_of_weak_limit
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    {z : ZeroTraceSobolev U} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hweak : ∀ v : ZeroTraceSobolev U,
      Tendsto
        (fun n => inner ℝ
          (penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll
            (φ n + 1) f) v)
        atTop (nhds (inner ℝ z v))) :
    exteriorRestriction (V := V) hU.isOpen.measurableSet
      (ZeroTraceSobolev.toL2 z) = 0 := by
  let R : ScalarL2 U →L[ℝ] ScalarL2 (U \ V) :=
    exteriorRestriction (V := V) hU.isOpen.measurableSet
  let T : ZeroTraceSobolev U →L[ℝ] ScalarL2 (U \ V) :=
    R.comp ZeroTraceSobolev.toL2
  let s : ℕ → ZeroTraceSobolev U := fun n =>
    penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll (φ n + 1) f
  have hRnorm := norm_exteriorRestriction_penalized_tendsto_zero
    a hU hV hα hlam hEll f
  have hRTnorm : Tendsto (fun n => ‖T (s n)‖) atTop (nhds 0) := by
    exact hRnorm.comp hφ.tendsto_atTop
  have hRT : Tendsto (fun n => T (s n)) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, norm_zero] using hRTnorm
  let r : ZeroTraceSobolev U := ContinuousLinearMap.adjoint T (T z)
  have hw := hweak r
  have hweakInner : Tendsto (fun n => inner ℝ (T z) (T (s n)))
      atTop (nhds (inner ℝ (T z) (T z))) := by
    have heq (w : ZeroTraceSobolev U) :
        inner ℝ w r = inner ℝ (T z) (T w) := by
      rw [real_inner_comm]
      exact ContinuousLinearMap.adjoint_inner_left T w (T z)
    rw [← heq z]
    exact hw.congr' (Filter.Eventually.of_forall fun n => heq (s n))
  have hstrongInner :=
    (InnerProductSpace.toDual ℝ (ScalarL2 (U \ V)) (T z)).continuous.tendsto 0
      |>.comp hRT
  have hself : inner ℝ (T z) (T z) = 0 := by
    simpa only [map_zero] using tendsto_nhds_unique hweakInner hstrongInner
  have hTz : T z = 0 := inner_self_eq_zero.mp hself
  exact hTz

private theorem weak_limit_toL2_eq_pointwiseLimit [NeZero d]
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x)
    {z : ZeroTraceSobolev U} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hweak : ∀ v : ZeroTraceSobolev U,
      Tendsto
        (fun n => inner ℝ
          (penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll
            (φ n + 1) f) v)
        atTop (nhds (inner ℝ z v))) :
    ZeroTraceSobolev.toL2 z =
      (penalizationPointwiseLimit_memLp a hU hV hα hlam hEll f hf).toLp
        (penalizationPointwiseLimit
          a hU.isOpen hV.isOpen hα hlam hEll f) := by
  let g : ScalarL2 U :=
    (penalizationPointwiseLimit_memLp a hU hV hα hlam hEll f hf).toLp
      (penalizationPointwiseLimit
        a hU.isOpen hV.isOpen hα hlam hEll f)
  let s : ℕ → ZeroTraceSobolev U := fun n =>
    penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll (φ n + 1) f
  have hindex : Tendsto (fun n => φ n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    refine Filter.eventually_atTop.2 ⟨b, fun n hbn => ?_⟩
    exact hbn.trans ((hφ.id_le n).trans (Nat.le_add_right (φ n) 1))
  have hstrongAll := penalizedResolvent_tendsto_L2
    a hU hV hα hlam hEll f hf
  have hstrong : Tendsto (fun n => ZeroTraceSobolev.toL2 (s n))
      atTop (nhds g) := by
    simpa only [Function.comp_apply, s, penalizedResolvent_apply] using!
      hstrongAll.comp hindex
  exact toL2_eq_of_weak_and_strong hweak hstrong

private theorem weak_limit_ae_zero_off
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    {z : ZeroTraceSobolev U} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hweak : ∀ v : ZeroTraceSobolev U,
      Tendsto
        (fun n => inner ℝ
          (penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll
            (φ n + 1) f) v)
        atTop (nhds (inner ℝ z v))) :
    ∀ᵐ x ∂volumeMeasureOn U,
      x ∉ V → ZeroTraceSobolev.toL2 z x = 0 := by
  have hRzero := exteriorRestriction_eq_zero_of_weak_limit
    a hU hV hα hlam hEll f hφ hweak
  have hzeroW : ∀ᵐ x ∂volumeMeasureOn (U \ V),
      ZeroTraceSobolev.toL2 z x = 0 := by
    filter_upwards
      [exteriorRestriction_coeFn (V := V) hU.isOpen.measurableSet
        hV.isOpen.measurableSet (ZeroTraceSobolev.toL2 z),
        MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := (2 : ENNReal))
          (volumeMeasureOn (U \ V))]
        with x hcoe hzero
    rw [← hcoe, hRzero, hzero]
    rfl
  rw [ae_restrict_iff' hU.isOpen.measurableSet]
  have hzeroGlobal :=
    (ae_restrict_iff' (hU.isOpen.measurableSet.diff hV.isOpen.measurableSet)).mp hzeroW
  filter_upwards [hzeroGlobal] with x hx
  intro hxU hxV
  exact hx ⟨hxU, hxV⟩

private theorem extension_value_restrict [NeZero d]
    (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    (v : ZeroTraceSobolev V) :
    ZeroTraceSobolev.toL2 v =ᵐ[volumeMeasureOn V]
      ZeroTraceSobolev.toL2
        (ZeroTraceSobolev.extendByZeroToPartSuperset
          hV hU.isOpen hVU v) := by
  have hext := ZeroTraceSobolev.extendByZeroToPartSuperset_toL2
    hV hU.isOpen hVU v
  apply (ae_restrict_iff' hV.isOpen.measurableSet).2
  have hextGlobal := (ae_restrict_iff' hU.isOpen.measurableSet).mp hext
  filter_upwards [hextGlobal] with x hx
  intro hxV
  rw [hx (hVU hxV), Set.indicator_of_mem hxV]

private theorem extension_gradient_restrict [NeZero d]
    (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    (v : ZeroTraceSobolev V) :
    ZeroTraceSobolev.gradient v =ᵐ[volumeMeasureOn V]
      ZeroTraceSobolev.gradient
        (ZeroTraceSobolev.extendByZeroToPartSuperset
          hV hU.isOpen hVU v) := by
  have hext := ZeroTraceSobolev.extendByZeroToPartSuperset_gradient
    hV hU.isOpen hVU v
  apply (ae_restrict_iff' hV.isOpen.measurableSet).2
  have hextGlobal := (ae_restrict_iff' hU.isOpen.measurableSet).mp hext
  filter_upwards [hextGlobal] with x hx
  intro hxV
  rw [hx (hVU hxV), Set.indicator_of_mem hxV]

private theorem shiftedBilin_extension_eq [NeZero d]
    (a : CoeffField d)
    (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {α lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (w v : ZeroTraceSobolev V) :
    shiftedBilin hEll α
        (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU w)
        (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU v) =
      α * inner ℝ (ZeroTraceSobolev.toL2 w) (ZeroTraceSobolev.toL2 v) +
        coefficientPairing a V (ZeroTraceSobolev.gradient w)
          (ZeroTraceSobolev.gradient v) := by
  rw [shiftedBilin_apply]
  have hvalue := scalar_inner_zeroExtension_eq_restriction
    hV.isOpen.measurableSet hU.isOpen.measurableSet hVU
    (ZeroTraceSobolev.toL2
      (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU w))
    (ZeroTraceSobolev.toL2 w)
    (ZeroTraceSobolev.toL2
      (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU v))
    (ZeroTraceSobolev.toL2 v)
    (ZeroTraceSobolev.extendByZeroToPartSuperset_toL2
      hV hU.isOpen hVU w)
    (extension_value_restrict hV hU hVU v)
  have hgradient := coefficientPairing_zeroExtension_eq_restriction
    a hV.isOpen.measurableSet hU.isOpen.measurableSet hVU
    (ZeroTraceSobolev.gradient
      (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU w))
    (ZeroTraceSobolev.gradient w)
    (ZeroTraceSobolev.gradient
      (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU v))
    (ZeroTraceSobolev.gradient v)
    (ZeroTraceSobolev.extendByZeroToPartSuperset_gradient hV hU.isOpen hVU w)
    (extension_gradient_restrict hV hU hVU v)
  rw [hvalue, hgradient]

private theorem forcing_inner_extension_eq [NeZero d]
    (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    (f : ScalarL2 U) (v : ZeroTraceSobolev V) :
    inner ℝ f
        (ZeroTraceSobolev.toL2
          (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU v)) =
      inner ℝ (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f)
        (ZeroTraceSobolev.toL2 v) := by
  calc
    inner ℝ f
        (ZeroTraceSobolev.toL2
          (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU v)) =
        inner ℝ
          (ZeroTraceSobolev.toL2
            (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU v)) f :=
      real_inner_comm _ _
    _ = inner ℝ (ZeroTraceSobolev.toL2 v)
        (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f) :=
      scalar_inner_zeroExtension_eq_restriction hV.isOpen.measurableSet
        hU.isOpen.measurableSet hVU _ _ _ _
        (ZeroTraceSobolev.extendByZeroToPartSuperset_toL2
          hV hU.isOpen hVU v)
        (restrictScalarL2ToPart_coeFn hV.isOpen.measurableSet
          hU.isOpen.measurableSet hVU f)
    _ = inner ℝ (restrictScalarL2ToPart (V := V)
          hU.isOpen.measurableSet f) (ZeroTraceSobolev.toL2 v) :=
      real_inner_comm _ _

private theorem penalization_integral_extension_eq_zero [NeZero d]
    (hV : IsOpenBoundedConvexDomain V)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    (u : ZeroTraceSobolev U) (v : ZeroTraceSobolev V) (n : ℕ) :
    (∫ x, penalizationPotential U V n x * ZeroTraceSobolev.toL2 u x *
        ZeroTraceSobolev.toL2
          (ZeroTraceSobolev.extendByZeroToPartSuperset
            hV hU.isOpen hVU v) x ∂volumeMeasureOn U) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards
    [ZeroTraceSobolev.extendByZeroToPartSuperset_toL2
      hV hU.isOpen hVU v,
      self_mem_ae_restrict hU.isOpen.measurableSet]
      with x hext hxU
  by_cases hxV : x ∈ V
  · have hxnot : x ∉ U \ V := fun hx => hx.2 hxV
    rw [penalizationPotential, Set.indicator_of_notMem hxnot, zero_mul]
    simp only [Pi.zero_apply, zero_mul]
  · have hx : x ∈ U \ V := ⟨hxU, hxV⟩
    rw [hext, Set.indicator_of_notMem hxV, mul_zero]
    simp only [Pi.zero_apply]

private theorem pointwiseLimitLp_eq_extendedPartResolvent [NeZero d]
    (a : CoeffField d)
    (hV : IsOpenBoundedConvexDomain V) (hVne : V.Nonempty)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    (penalizationPointwiseLimit_memLp a hU hV hα hlam hEll f hf).toLp
        (penalizationPointwiseLimit
          a hU.isOpen hV.isOpen hα hlam hEll f) =
      ZeroTraceSobolev.toL2
        (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
          (alphaShiftedSolution a hα hlam
            (hEll.mono hV.isOpen.measurableSet hVU)
            (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))) := by
  obtain ⟨z, φ, hφ, hweak⟩ :=
    exists_penalization_weak_limit a hU hV hα hlam hEll f
  have hzZero := weak_limit_ae_zero_off
    a hU hV hα hlam hEll f hφ hweak
  obtain ⟨w, hwz⟩ :=
    exists_eq_extendByZeroToPartSuperset_of_ae_zero
      hV hVne hU hVU z hzZero
  let fV : ScalarL2 V :=
    restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f
  let hEllV : IsEllipticFieldOn lam Lam V a :=
    hEll.mono hV.isOpen.measurableSet hVU
  have hwWeak : IsAlphaShiftedWeakSolution a V α fV w := by
    intro v
    let vU : ZeroTraceSobolev U :=
      ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU v
    let s : ℕ → ZeroTraceSobolev U := fun k =>
      penalizedSolution a hU.isOpen hV.isOpen hα hlam hEll (φ k + 1) f
    have hform := shiftedBilin_tendsto_of_weak (α := α) hEll hweak vU
    have heq (k : ℕ) : shiftedBilin hEll α (s k) vU =
        inner ℝ f (ZeroTraceSobolev.toL2 vU) := by
      have hp := potentialSolution_isPotentialWeakSolution a hα hlam hEll
        (penalizationPotential U V (φ k + 1))
        (penalizationPotential_isBoundedNonnegative
          hU.isOpen.measurableSet hV.isOpen.measurableSet (φ k + 1)) f vU
      change shiftedPotentialBilin a α (penalizationPotential U V (φ k + 1))
        U (s k) vU = inner ℝ f (ZeroTraceSobolev.toL2 vU) at hp
      dsimp only [shiftedPotentialBilin] at hp
      rw [← shiftedBilin_apply hEll α (s k) vU,
        penalization_integral_extension_eq_zero hV hU hVU (s k) v
          (φ k + 1), add_zero] at hp
      exact hp
    have hconst : Tendsto (fun k => shiftedBilin hEll α (s k) vU)
        atTop (nhds (inner ℝ f (ZeroTraceSobolev.toL2 vU))) :=
      tendsto_const_nhds.congr'
        (Filter.Eventually.of_forall fun k => (heq k).symm)
    have hzForm : shiftedBilin hEll α z vU =
        inner ℝ f (ZeroTraceSobolev.toL2 vU) :=
      tendsto_nhds_unique hform hconst
    rw [← hwz] at hzForm
    rw [shiftedBilin_extension_eq a hV hU hVU hEll w v,
      forcing_inner_extension_eq hV hU hVU f v] at hzForm
    exact hzForm
  have hwEq : w = alphaShiftedSolution a hα hlam hEllV fV :=
    (isAlphaShiftedWeakSolution_iff_eq a hα hlam hEllV fV w).1 hwWeak
  have hzValue := weak_limit_toL2_eq_pointwiseLimit
    a hU hV hα hlam hEll f hf hφ hweak
  calc
    (penalizationPointwiseLimit_memLp a hU hV hα hlam hEll f hf).toLp
        (penalizationPointwiseLimit
          a hU.isOpen hV.isOpen hα hlam hEll f) =
        ZeroTraceSobolev.toL2 z := hzValue.symm
    _ = ZeroTraceSobolev.toL2
        (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU w) := by
      rw [hwz]
    _ = ZeroTraceSobolev.toL2
        (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
          (alphaShiftedSolution a hα hlam hEllV fV)) := by rw [hwEq]

/-- The almost-everywhere infimum of the exterior-penalized resolvents is the
shifted resolvent on the convex part domain. -/
theorem penalizationPointwiseLimit_eq_partResolvent_ae [NeZero d]
    (a : CoeffField d)
    (hV : IsOpenBoundedConvexDomain V) (hVne : V.Nonempty)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn V,
      penalizationPointwiseLimit
          a hU.isOpen hV.isOpen hα hlam hEll f x =
        alphaShiftedResolvent a hα hlam
          (hEll.mono hV.isOpen.measurableSet hVU)
          (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f) x := by
  let gfun := penalizationPointwiseLimit
    a hU.isOpen hV.isOpen hα hlam hEll f
  let hg := penalizationPointwiseLimit_memLp a hU hV hα hlam hEll f hf
  let g : ScalarL2 U := hg.toLp gfun
  let w : ZeroTraceSobolev V := alphaShiftedSolution a hα hlam
    (hEll.mono hV.isOpen.measurableSet hVU)
    (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f)
  have hEq : g = ZeroTraceSobolev.toL2
      (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU w) :=
    pointwiseLimitLp_eq_extendedPartResolvent
      a hV hVne hU hVU hα hlam hEll f hf
  have hgcoe : g =ᵐ[volumeMeasureOn U] gfun := MemLp.coeFn_toLp hg
  have hext := ZeroTraceSobolev.extendByZeroToPartSuperset_toL2
    hV hU.isOpen hVU w
  apply (ae_restrict_iff' hV.isOpen.measurableSet).2
  have hgGlobal := (ae_restrict_iff' hU.isOpen.measurableSet).mp hgcoe
  have hextGlobal := (ae_restrict_iff' hU.isOpen.measurableSet).mp hext
  filter_upwards [hgGlobal, hextGlobal] with x hgx hextx
  intro hxV
  have hxU := hVU hxV
  calc
    penalizationPointwiseLimit
        a hU.isOpen hV.isOpen hα hlam hEll f x = g x := (hgx hxU).symm
    _ = ZeroTraceSobolev.toL2
        (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU w) x := by
      rw [hEq]
    _ = ZeroTraceSobolev.toL2 w x := by
      rw [hextx hxU, Set.indicator_of_mem hxV]
    _ = alphaShiftedResolvent a hα hlam
        (hEll.mono hV.isOpen.measurableSet hVU)
        (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f) x := rfl

/-- The pointwise infimum of the exterior-penalized resolvents equals the
part-domain shifted resolvent almost everywhere. -/
theorem iInf_penalizedResolvent_eq_part_ae [NeZero d]
    (a : CoeffField d)
    (hV : IsOpenBoundedConvexDomain V) (hVne : V.Nonempty)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn V,
      (⨅ n, penalizedResolvent
          a hU.isOpen hV.isOpen hα hlam hEll n f x) =
        alphaShiftedResolvent a hα hlam
          (hEll.mono hV.isOpen.measurableSet hVU)
          (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f) x := by
  simpa only [penalizationPointwiseLimit] using
    penalizationPointwiseLimit_eq_partResolvent_ae
      a hV hVne hU hVU hα hlam hEll f hf

end DivergenceFormProcess.Form
