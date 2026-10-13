/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.WholeSpaceDenseRange
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveC0
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointExtension
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.ExponentialComparison
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExcessiveStopping

/-!
# CruxStreamBarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Coefficient-generic C₀ data for the whole-space barrier

The lower crux comparison does not use global small contrast.  Its
coefficient-dependent inputs are precisely vanishing of the analytic minimal
resolvent on `C₀`, dense range of that resolver, and vanishing for bounded
nonnegative compactly supported data.  The remaining inputs are supplied by
`WholeSpaceBarrierData`: the axis-cube constructor and its continuous
zero-extension witness are coefficient-generic consequences of the
continuous skew field carried by `WholeSpaceAnalyticData`.

This module packages those inputs without changing the established
small-contrast API.  It supplies both the old small-contrast datum and the
stream field as instances of the new definition-shaped structure.
-/

namespace DivergenceFormProcess.Form

open CompactlySupported Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

private theorem analyticMinimalResolventReal_congr_cruxStream
    (mu : PositiveShift) {f g : Vec d → ℝ} (hfg : f = g)
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) (x : Vec d) :
    A.analyticMinimalResolventReal mu f hf hfD x =
      A.analyticMinimalResolventReal mu g hg hgE x := by
  subst g
  exact A.analyticMinimalResolventReal_bound_irrel mu hf hfD hgE x

end WholeSpaceAnalyticData

/-- The exact coefficient-dependent `C₀` and compact-data inputs used by the
excessive-barrier half of the crux.  Axis-cube barrier data and their
continuity witnesses are already constructed from `WholeSpaceAnalyticData`
and therefore are not additional fields. -/
structure WholeSpaceC0BarrierData (A : WholeSpaceAnalyticData d) where
  /-- The analytic minimal resolvent maps `C₀` to `C₀`. -/
  vanishing : A.HasVanishingAnalyticMinimalResolvent
  /-- Every analytic minimal `C₀` resolvent operator has dense range. -/
  denseRange : A.HasDenseRangeAnalyticMinimalC0OfVanishing vanishing
  /-- Positive bounded compactly supported data have resolvents vanishing at
  infinity at every positive shift. -/
  compactVanishing : ∀ (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (_hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D), HasCompactSupport f →
      Tendsto (fun x ↦ (A.analyticMinimalResolvent mu f hf hfD x).toReal)
        (cocompact (Vec d)) (nhds 0)

namespace WholeSpaceC0BarrierData

variable {A : WholeSpaceAnalyticData d}

/-- The positive contractive resolver canonically assembled from the barrier
data. -/
def resolvent (B : WholeSpaceC0BarrierData A) :
    PositiveC0ContractiveResolvent (Vec d) :=
  A.analyticMinimalPositiveC0ContractiveResolventOfVanishing
    B.vanishing B.denseRange

@[simp] theorem resolvent_operator (B : WholeSpaceC0BarrierData A)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    B.resolvent.toContractiveResolvent.operator mu f =
      A.analyticMinimalC0ResolventOfVanishing B.vanishing mu f := rfl

end WholeSpaceC0BarrierData

namespace WholeSpaceBarrierData

variable {A : WholeSpaceAnalyticData d} (P : WholeSpaceBarrierData A)

/-- The whole-space barrier as a `C₀` function under the coefficient-generic
barrier input. -/
def barrierC0OfData (B : WholeSpaceC0BarrierData A) : C₀(Vec d, ℝ) where
  toFun := P.barrier
  continuous_toFun := P.continuous_barrier
  zero_at_infty' := by
    have h1 := B.compactVanishing P.lam P.measurable_indicator_f
      P.indicator_f_nonneg P.abs_indicator_f_le P.hasCompactSupport_indicator_f
    have hcongr : ∀ x, (A.analyticMinimalResolvent P.lam (P.V.indicator P.f)
          P.measurable_indicator_f P.abs_indicator_f_le x).toReal =
        (A.analyticMinimalResolvent P.lam P.f P.hf P.hfD x).toReal := fun x ↦
      congrArg ENNReal.toReal
        (A.analyticMinimalResolvent_congr_ae P.lam P.measurable_indicator_f P.hf
          P.abs_indicator_f_le P.hfD P.hfV.symm x)
    have h2 : Tendsto P.utilde (cocompact (Vec d)) (nhds 0) :=
      P.hasCompactSupport_utilde.is_zero_at_infty
    unfold barrier
    simpa only [sub_zero] using (h1.congr hcongr).sub h2

@[simp] theorem barrierC0OfData_apply (B : WholeSpaceC0BarrierData A)
    (x : Vec d) : P.barrierC0OfData B x = P.barrier x := rfl

theorem barrierC0OfData_nonneg (B : WholeSpaceC0BarrierData A) (x : Vec d) :
    0 ≤ P.barrierC0OfData B x := P.barrier_nonneg x

/-- Evaluation of the generic analytic `C₀` resolver on the barrier. -/
theorem analyticMinimalResolventReal_barrierC0OfData
    (B : WholeSpaceC0BarrierData A) (mu : PositiveShift) (x : Vec d) :
    A.analyticMinimalC0ResolventOfVanishing B.vanishing mu
        (P.barrierC0OfData B) x =
      A.analyticMinimalResolventReal mu P.barrier P.measurable_barrier
        (fun y ↦ P.abs_barrier_le y) x := by
  rw [WholeSpaceAnalyticData.analyticMinimalC0ResolventOfVanishing_apply]
  exact A.analyticMinimalResolventReal_bound_irrel mu _ _
    (fun y ↦ P.abs_barrier_le y) x

/-- The resolvent inequality used by exponential comparison, with no global
small-contrast input. -/
theorem mul_operator_barrierC0OfData_le
    (B : WholeSpaceC0BarrierData A)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        A.analyticMinimalC0ResolventOfVanishing B.vanishing mu g)
    (mu : PositiveShift) (hmu : (P.lam : ℝ) < (mu : ℝ)) (x : Vec d) :
    (mu : ℝ) * R.toContractiveResolvent.operator mu
        (P.barrierC0OfData B) x ≤
      (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) * P.barrierC0OfData B x := by
  rw [hT mu (P.barrierC0OfData B)]
  rw [P.analyticMinimalResolventReal_barrierC0OfData B mu x]
  exact P.mul_analyticMinimalResolventReal_barrier_le mu hmu x

/-- The assembled generic barrier is excessive for the one-point extension.
This is the stopping input used by the S-free lower crux comparison. -/
theorem isLambdaExcessive_onePointAssemble_barrierC0OfData
    (B : WholeSpaceC0BarrierData A)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        A.analyticMinimalC0ResolventOfVanishing B.vanishing mu g) :
    R.onePointKernelSemigroup.IsLambdaExcessive (P.lam : ℝ)
      (PositiveC0ContractiveResolvent.onePointAssemble
        (P.barrierC0OfData B) 0) := by
  have hassemble : ∀ z : OnePoint (Vec d),
      0 ≤ PositiveC0ContractiveResolvent.onePointAssemble
        (P.barrierC0OfData B) 0 z := by
    intro z
    induction z using OnePoint.rec with
    | infty => simp
    | coe x => simpa using P.barrierC0OfData_nonneg B x
  have hR : ∀ mu : PositiveShift, (P.lam : ℝ) < (mu : ℝ) → ∀ z,
      (mu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator mu
          (PositiveC0ContractiveResolvent.onePointAssemble
            (P.barrierC0OfData B) 0) z ≤
        (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) *
          PositiveC0ContractiveResolvent.onePointAssemble
            (P.barrierC0OfData B) 0 z := by
    intro mu hmu z
    rw [PositiveC0ContractiveResolvent.onePointResolvent_operator,
      PositiveC0ContractiveResolvent.onePointRemainder_assemble,
      PositiveC0ContractiveResolvent.onePointAssemble_infty, mul_zero]
    induction z using OnePoint.rec with
    | infty => simp
    | coe x =>
        rw [PositiveC0ContractiveResolvent.onePointAssemble_coe,
          PositiveC0ContractiveResolvent.onePointAssemble_coe, add_zero, add_zero]
        exact P.mul_operator_barrierC0OfData_le B R hT mu hmu x
  have hcomp : ∀ (t : NNReal) (z : OnePoint (Vec d)),
      kernelIntegral (R.onePointKernelSemigroup t)
        (PositiveC0ContractiveResolvent.onePointAssemble
          (P.barrierC0OfData B) 0) z ≤
        Real.exp ((P.lam : ℝ) * (t : ℝ)) *
          PositiveC0ContractiveResolvent.onePointAssemble
            (P.barrierC0OfData B) 0 z := by
    intro t z
    exact PositiveC0ContractiveResolvent.integral_kernelSemigroup_le_exp_mul
      R.onePointResolvent (P.lam : ℝ) _ hR _ (fun _ ↦ le_rfl) t z
  exact SubMarkovKernelSemigroup.isLambdaExcessive_of_c0Semigroup_apply_le_exp_mul
    (P.lam : ℝ) _ hassemble hcomp

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open CompactlySupported Filter HCPolySupport MeasureTheory Set Topology
open DivergenceFormProcess.Form MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Compact-data vanishing for the stream field at every positive shift.  At
large shift this is the localized-tail theorem; at smaller shift the
resolvent equation writes the answer as a sum of two `C₀` functions. -/
private theorem zero_at_infty_toReal_streamAnalyticMinimalResolvent_of_compact_allShifts
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (hfcompact : HasCompactSupport f) :
    Tendsto (fun x ↦ ((streamWholeSpaceAnalyticData M omega
      ).analyticMinimalResolvent mu f hf hfD x).toReal)
      (cocompact (Vec d)) (nhds 0) := by
  by_cases hmu : 1 ≤ (mu : ℝ)
  · exact zero_at_infty_toReal_streamAnalyticMinimalResolvent_of_compact
      M omega mu hmu hf hf0 hfD hfcompact
  · let lam : PositiveShift :=
      ⟨(mu : ℝ) + 1, Set.mem_Ioi.mpr
        (add_pos_of_pos_of_nonneg mu.property zero_le_one)⟩
    have hlam : 1 ≤ (lam : ℝ) := by
      dsimp only [lam]
      exact le_add_of_nonneg_left mu.property.le
    let A := streamWholeSpaceAnalyticData M omega
    have hhigh := zero_at_infty_toReal_streamAnalyticMinimalResolvent_of_compact
      M omega lam hlam hf hf0 hfD hfcompact
    have hD : 0 ≤ D := (abs_nonneg (f 0)).trans (hfD 0)
    have hfLp : MemLp f 2 volume := hfcompact.memLp_of_bound
      hf.aestronglyMeasurable D (Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using hfD x)
    let g : C₀(Vec d, ℝ) :=
      { toFun := fun x ↦ (A.analyticMinimalResolvent lam f hf hfD x).toReal
        continuous_toFun :=
          (A.continuous_analyticMinimalResolventReal_of_memLp lam hf hD hfD
            hfLp).congr fun x ↦
              A.analyticMinimalResolventReal_eq_toReal lam hf hf0 hfD x
        zero_at_infty' := hhigh }
    have hgNorm : ∀ y, |g y| ≤ ‖g‖ := by
      intro y
      rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF y
    have hgzero : Tendsto
        (A.analyticMinimalResolventReal mu g g.continuous.measurable hgNorm)
        (cocompact (Vec d)) (nhds 0) := by
      simpa only using hasVanishing_streamAnalyticMinimalResolvent M omega mu g
    have hfun : A.analyticMinimalResolventReal lam f hf hfD = g := by
      funext x
      exact A.analyticMinimalResolventReal_eq_toReal lam hf hf0 hfD x
    have hEq : ∀ x,
        (A.analyticMinimalResolvent mu f hf hfD x).toReal =
          g x + A.analyticMinimalResolventReal mu g g.continuous.measurable
            hgNorm x := by
      intro x
      have hres := A.analyticMinimalResolventReal_resolventEquation mu lam hf hfD x
      have hcoeff : (lam : ℝ) - (mu : ℝ) = 1 := by
        dsimp only [lam]
        ring
      rw [hcoeff, one_mul] at hres
      have hinner : A.analyticMinimalResolventReal mu
          (A.analyticMinimalResolventReal lam f hf hfD)
          (A.measurable_analyticMinimalResolventReal lam hf hfD)
          (A.abs_analyticMinimalResolventReal_le lam hf hfD) x =
          A.analyticMinimalResolventReal mu g g.continuous.measurable hgNorm x :=
        A.analyticMinimalResolventReal_congr_cruxStream mu hfun
          (A.measurable_analyticMinimalResolventReal lam hf hfD)
          g.continuous.measurable
          (A.abs_analyticMinimalResolventReal_le lam hf hfD) hgNorm x
      calc
        (A.analyticMinimalResolvent mu f hf hfD x).toReal =
            A.analyticMinimalResolventReal mu f hf hfD x :=
          (A.analyticMinimalResolventReal_eq_toReal mu hf hf0 hfD x).symm
        _ = A.analyticMinimalResolventReal lam f hf hfD x +
            A.analyticMinimalResolventReal mu
              (A.analyticMinimalResolventReal lam f hf hfD)
              (A.measurable_analyticMinimalResolventReal lam hf hfD)
              (A.abs_analyticMinimalResolventReal_le lam hf hfD) x := hres
        _ = g x + A.analyticMinimalResolventReal mu g
            g.continuous.measurable hgNorm x :=
          congrArg₂ (· + ·) (congrFun hfun x) hinner
    have hsum := hhigh.add hgzero
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards with x
    exact (hEq x).symm

/-- The stream field supplies the coefficient-generic barrier data entirely
from the localized split-skew vanishing and dense-range theorems. -/
theorem streamWholeSpaceC0BarrierData
    (M : ABKModel d) (omega : FullSample d M.gamma) :
    WholeSpaceC0BarrierData (streamWholeSpaceAnalyticData M omega) where
  vanishing := hasVanishing_streamAnalyticMinimalResolvent M omega
  denseRange := hasDenseRange_streamAnalyticMinimalC0 M omega
  compactVanishing := fun mu {f} hf hf0 {D} hfD hfcompact ↦
    zero_at_infty_toReal_streamAnalyticMinimalResolvent_of_compact_allShifts
      M omega mu (f := f) hf hf0 (D := D) hfD hfcompact

end

end Algsuperdiff.Section5.Field
