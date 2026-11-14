/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Comparison
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDE
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEIdentification

/-!
# ExitTimePDEIdentificationL2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The shift-uniform comparison of the Dirichlet resolvents with the torsion function

The Dirichlet resolvent of the constant datum on an exhaustion cube at the
positive shift `lam` is the solution of
  `-div (a grad u) + lam u = 1` in `V`,  `u = 0` on the boundary of `V`,

and the torsion function is the solution of the same problem without the
shift.  This file compares the two in `L^2(V)`, with an error that is
proportional to the shift and otherwise depends only on the uniform bound of
the torsion function.

The comparison rests on one identity.  The torsion function solves the shifted
problem with the datum `1 + lam w`, so it is the shifted resolvent of that
datum, and by linearity the difference between the torsion function and the
Dirichlet resolvent of the constant datum is `lam` times the shifted resolvent
of the torsion function.

The identity is used three times.  At a shift small enough that `1 + lam w`
stays nonnegative — any shift below the reciprocal of the uniform bound — the
positivity of the shifted resolvent gives that the torsion function is
nonnegative.  The positivity applied again then gives that the Dirichlet
resolvent of the constant datum is below the torsion function at every
positive shift.  Finally, the torsion function is below its uniform bound
times the constant datum, so the order preservation of the shifted resolvent
bounds the shifted resolvent of the torsion function by that bound times the
Dirichlet resolvent of the constant datum, which is itself below the bound;
the difference is therefore at most the shift times the square of the bound.

The sandwich is then read as a norm estimate: on a cube of finite volume an
almost-everywhere bound is an `L^2` bound, so the Dirichlet resolvents of the
constant datum converge to the torsion function in `L^2(V)` at a rate
proportional to the shift.

Everything here is an almost-everywhere statement about `L^2` classes, or a
consequence of one.  The pointwise reading on the cube is separate.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The `L²` class of the constant datum of an exhaustion cube. -/
def cubeOneL2 (d v : ℕ) : ScalarL2 (wholeSpaceCube d v) :=
  boundedMeasurableToScalarL2 (isOpenBoundedConvexDomain_wholeSpaceCube d v)
    ((measurable_cubeOneDatum d v).comp measurable_subtype_coe)
    (fun y => abs_cubeOneDatum_le d v y)

theorem cubeOneL2_ae (d v : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v), cubeOneL2 d v x = 1 := by
  filter_upwards [boundedMeasurableToScalarL2_coeFn
      (isOpenBoundedConvexDomain_wholeSpaceCube d v)
      ((measurable_cubeOneDatum d v).comp measurable_subtype_coe)
      (fun y => abs_cubeOneDatum_le d v y),
    ae_restrict_mem
      (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen.measurableSet]
    with x hx hmem
  rw [cubeOneL2, hx, domainExtension_of_mem hmem]
  exact cubeOneDatum_of_mem hmem

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The `L²` class of the torsion function of an exhaustion cube. -/
def cubeTorsionL2 (v : ℕ) : ScalarL2 (wholeSpaceCube d v) :=
  (A.cubeTorsionFunction v).toH1Function.toScalarL2

theorem cubeTorsionL2_ae (v : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      A.cubeTorsionL2 v x = (A.cubeTorsionFunction v).toH1Function.toFun x :=
  (A.cubeTorsionFunction v).toH1Function.coeFn_toScalarL2

/-- The torsion function solves the shifted problem with the shifted datum. -/
theorem cubeTorsionL2_eq_alphaShiftedResolvent (v : ℕ) (lam : PositiveShift) :
    A.cubeTorsionL2 v =
      alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (cubeOneL2 d v + (lam : ℝ) • A.cubeTorsionL2 v) := by
  have hU : IsOpenBoundedConvexDomain (wholeSpaceCube d v) :=
    isOpenBoundedConvexDomain_wholeSpaceCube d v
  have hG : ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      (cubeOneL2 d v + (lam : ℝ) • A.cubeTorsionL2 v) x =
        (fun _ : Vec d => (1 : ℝ)) x +
          (lam : ℝ) * (A.cubeTorsionFunction v).toH1Function.toFun x := by
    filter_upwards [MeasureTheory.Lp.coeFn_add (cubeOneL2 d v)
        ((lam : ℝ) • A.cubeTorsionL2 v),
      MeasureTheory.Lp.coeFn_smul (lam : ℝ) (A.cubeTorsionL2 v),
      cubeOneL2_ae d v, A.cubeTorsionL2_ae v] with x hadd hsmul hone htors
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hone, htors]
  have hweak := isAlphaShiftedWeakSolution_of_isScalarForcedWeakSolution hU
    (alpha := (lam : ℝ)) (A.cubeTorsionFunction v)
    (A.cubeTorsionFunction_isScalarForcedWeakSolution v) _ hG
  have heq := (isAlphaShiftedWeakSolution_iff_eq A.a lam.property A.hnu
    (A.cubeEllipticity v) _ _).1 hweak
  have := congrArg ZeroTraceSobolev.toL2 heq
  rw [ZeroTraceSobolev.toL2_ofH10Function] at this
  exact this

/-- The torsion function exceeds the Dirichlet resolvent of the constant datum
by the shifted resolvent of itself. -/
theorem cubeTorsionL2_sub_alphaShiftedResolvent_cubeOneL2 (v : ℕ)
    (lam : PositiveShift) :
    A.cubeTorsionL2 v -
        alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
          (cubeOneL2 d v) =
      (lam : ℝ) • alphaShiftedResolvent A.a lam.property A.hnu
        (A.cubeEllipticity v) (A.cubeTorsionL2 v) := by
  conv_lhs => rw [A.cubeTorsionL2_eq_alphaShiftedResolvent v lam]
  rw [map_add, map_smul, add_sub_cancel_left]

/-- **The torsion function is nonnegative.**  At a shift small enough that the
shifted datum stays nonnegative, the torsion function is the shifted resolvent
of a nonnegative datum. -/
theorem cubeTorsionL2_nonneg (v : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v), 0 ≤ A.cubeTorsionL2 v x := by
  have hU : IsOpenBoundedConvexDomain (wholeSpaceCube d v) :=
    isOpenBoundedConvexDomain_wholeSpaceCube d v
  have hMnn : 0 ≤ A.cubeTorsionBound v := A.cubeTorsionBound_nonneg v
  set c : ℝ := (A.cubeTorsionBound v + 1)⁻¹ with hc
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  have hcM : c * A.cubeTorsionBound v < 1 := by
    rw [hc, inv_mul_eq_div, div_lt_one (by linarith only [hMnn])]
    linarith only []
  set lam : PositiveShift := ⟨c, Set.mem_Ioi.mpr hcpos⟩ with hlam
  have hGnn : ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      0 ≤ (cubeOneL2 d v + (lam : ℝ) • A.cubeTorsionL2 v) x := by
    filter_upwards [MeasureTheory.Lp.coeFn_add (cubeOneL2 d v)
        ((lam : ℝ) • A.cubeTorsionL2 v),
      MeasureTheory.Lp.coeFn_smul (lam : ℝ) (A.cubeTorsionL2 v),
      cubeOneL2_ae d v, A.cubeTorsionL2_ae v,
      A.abs_cubeTorsionFunction_le v] with x hadd hsmul hone htors habs
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hone, htors]
    have hlow : -A.cubeTorsionBound v ≤
        (A.cubeTorsionFunction v).toH1Function.toFun x := (abs_le.mp habs).1
    have : -(c * A.cubeTorsionBound v) ≤
        c * (A.cubeTorsionFunction v).toH1Function.toFun x := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left hlow hcpos.le
    change (0 : ℝ) ≤ 1 + c * (A.cubeTorsionFunction v).toH1Function.toFun x
    linarith only [this, hcM]
  have hres := alphaShiftedResolvent_nonneg_ae A.a hU lam.property A.hnu
    (A.cubeEllipticity v) (cubeOneL2 d v + (lam : ℝ) • A.cubeTorsionL2 v) hGnn
  rw [← A.cubeTorsionL2_eq_alphaShiftedResolvent v lam] at hres
  exact hres

/-- The Dirichlet resolvent of the constant datum is below the torsion
function. -/
theorem alphaShiftedResolvent_cubeOneL2_le_cubeTorsionL2 (v : ℕ)
    (lam : PositiveShift) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
          (cubeOneL2 d v) x ≤ A.cubeTorsionL2 v x := by
  have hU : IsOpenBoundedConvexDomain (wholeSpaceCube d v) :=
    isOpenBoundedConvexDomain_wholeSpaceCube d v
  have hpos := alphaShiftedResolvent_nonneg_ae A.a hU lam.property A.hnu
    (A.cubeEllipticity v) (A.cubeTorsionL2 v) (A.cubeTorsionL2_nonneg v)
  have hdiff := A.cubeTorsionL2_sub_alphaShiftedResolvent_cubeOneL2 v lam
  filter_upwards [hpos,
    MeasureTheory.Lp.coeFn_sub (A.cubeTorsionL2 v)
      (alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (cubeOneL2 d v)),
    MeasureTheory.Lp.coeFn_smul (lam : ℝ)
      (alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (A.cubeTorsionL2 v))] with x hx hsub hsmul
  have hval : A.cubeTorsionL2 v x -
      alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (cubeOneL2 d v) x =
      (lam : ℝ) * alphaShiftedResolvent A.a lam.property A.hnu
        (A.cubeEllipticity v) (A.cubeTorsionL2 v) x := by
    rw [← Pi.sub_apply, ← hsub, hdiff, hsmul, Pi.smul_apply, smul_eq_mul]
  have hnn : 0 ≤ (lam : ℝ) * alphaShiftedResolvent A.a lam.property A.hnu
      (A.cubeEllipticity v) (A.cubeTorsionL2 v) x :=
    mul_nonneg lam.property.le hx
  linarith only [hval, hnn]

theorem cubeTorsionL2_le (v : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      A.cubeTorsionL2 v x ≤ A.cubeTorsionBound v := by
  filter_upwards [A.cubeTorsionL2_ae v, A.abs_cubeTorsionFunction_le v]
    with x htors habs
  rw [htors]
  exact (abs_le.mp habs).2

/-- The shifted resolvent of the torsion function is bounded by the bound of
the torsion function times the shifted resolvent of the constant datum. -/
theorem alphaShiftedResolvent_cubeTorsionL2_le (v : ℕ) (lam : PositiveShift) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
          (A.cubeTorsionL2 v) x ≤
        A.cubeTorsionBound v *
          alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
            (cubeOneL2 d v) x := by
  have hU : IsOpenBoundedConvexDomain (wholeSpaceCube d v) :=
    isOpenBoundedConvexDomain_wholeSpaceCube d v
  have hle : ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      A.cubeTorsionL2 v x ≤ (A.cubeTorsionBound v • cubeOneL2 d v) x := by
    filter_upwards [A.cubeTorsionL2_le v, cubeOneL2_ae d v,
      MeasureTheory.Lp.coeFn_smul (A.cubeTorsionBound v) (cubeOneL2 d v)]
      with x hx hone hsmul
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hone, mul_one]
    exact hx
  have hmono := alphaShiftedResolvent_mono_ae A.a hU lam.property A.hnu
    (A.cubeEllipticity v) (A.cubeTorsionL2 v)
    (A.cubeTorsionBound v • cubeOneL2 d v) hle
  filter_upwards [hmono,
    MeasureTheory.Lp.coeFn_smul (A.cubeTorsionBound v)
      (alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (cubeOneL2 d v))] with x hx hsmul
  rw [map_smul] at hx
  rw [hsmul, Pi.smul_apply, smul_eq_mul] at hx
  exact hx

/-- **The shift-uniform sandwich.**  The Dirichlet resolvent of the constant
datum at a positive shift is below the torsion function and above it minus the
shift times the square of the uniform bound. -/
theorem cubeTorsionL2_sub_alphaShiftedResolvent_cubeOneL2_le (v : ℕ)
    (lam : PositiveShift) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      A.cubeTorsionL2 v x -
          alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
            (cubeOneL2 d v) x ≤
        (lam : ℝ) * (A.cubeTorsionBound v * A.cubeTorsionBound v) := by
  have hdiff := A.cubeTorsionL2_sub_alphaShiftedResolvent_cubeOneL2 v lam
  have hMnn : 0 ≤ A.cubeTorsionBound v := A.cubeTorsionBound_nonneg v
  filter_upwards [A.alphaShiftedResolvent_cubeTorsionL2_le v lam,
    A.alphaShiftedResolvent_cubeOneL2_le_cubeTorsionL2 v lam,
    A.cubeTorsionL2_le v,
    MeasureTheory.Lp.coeFn_sub (A.cubeTorsionL2 v)
      (alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (cubeOneL2 d v)),
    MeasureTheory.Lp.coeFn_smul (lam : ℝ)
      (alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (A.cubeTorsionL2 v))] with x hres hlow hup hsub hsmul
  have hval : A.cubeTorsionL2 v x -
      alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (cubeOneL2 d v) x =
      (lam : ℝ) * alphaShiftedResolvent A.a lam.property A.hnu
        (A.cubeEllipticity v) (A.cubeTorsionL2 v) x := by
    rw [← Pi.sub_apply, ← hsub, hdiff, hsmul, Pi.smul_apply, smul_eq_mul]
  have hFM : alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
      (cubeOneL2 d v) x ≤ A.cubeTorsionBound v := le_trans hlow hup
  have hstep : A.cubeTorsionBound v *
      alphaShiftedResolvent A.a lam.property A.hnu (A.cubeEllipticity v)
        (cubeOneL2 d v) x ≤ A.cubeTorsionBound v * A.cubeTorsionBound v :=
    mul_le_mul_of_nonneg_left hFM hMnn
  have hfinal : (lam : ℝ) * alphaShiftedResolvent A.a lam.property A.hnu
        (A.cubeEllipticity v) (A.cubeTorsionL2 v) x ≤
      (lam : ℝ) * (A.cubeTorsionBound v * A.cubeTorsionBound v) :=
    mul_le_mul_of_nonneg_left (le_trans hres hstep) lam.property.le
  rw [hval]
  exact hfinal

/-! ## The `L²` rate -/

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
