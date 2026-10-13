/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.DivergenceDeGiorgiBound
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.MeasurableRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDETorsion

/-!
# ExitTimePDEIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The torsion function of an exhaustion cube and its uniform bound

The unshifted Dirichlet problem with constant forcing on an exhaustion cube,

  `-div (a grad w) = 1` in `V`,  `w = 0` on the boundary of `V`,

is solvable, and this file fixes one measurable solution and bounds it
uniformly.

The constant forcing is written in divergence form once and for all
(`cubeTorsionField`): the field with a single nonzero coordinate equal to the
negative of the corresponding coordinate function.  Its length at a point is
the absolute value of that coordinate, hence at most the half-side of the cube.
The divergence-form De Giorgi estimate therefore bounds the solution in the
supremum norm by a dimensional constant times `sqrt d`, divided by the lower
ellipticity constant, times the square of the half-side.

The solution is fixed as a measurable representative
(`cubeTorsionFunction`), because the De Giorgi estimate and every later
pointwise argument read the values of the function rather than its `L²` class.

The other statement proved here is the passage from the scalar weak equation
to the shifted weak equation on the zero-trace graph carrier
(`isAlphaShiftedWeakSolution_of_isScalarForcedWeakSolution`): a solution of
`-div (a grad u) = g` also solves `(lam - div (a grad)) u = g + lam u`, and on
an open bounded convex domain the graph carrier is exhausted by honest
zero-trace Sobolev functions, so the test class is the same one.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The constant forcing in divergence form -/

/-- The divergence form of the constant forcing one: the field whose only
nonzero coordinate is the negative of the corresponding coordinate function. -/
def cubeTorsionField (d : ℕ) [NeZero d] : Vec d → Vec d :=
  scalarToDivergenceField (fun _ : Vec d => (1 : ℝ)) default 0

omit [NeZero d] in
/-- The coordinate primitive of the constant one based at the origin is the
corresponding coordinate function. -/
theorem coordinatePrimitive_one (i : Fin d) (x : Vec d) :
    coordinatePrimitive (fun _ : Vec d => (1 : ℝ)) i 0 x = x i := by
  unfold coordinatePrimitive
  simp

theorem cubeTorsionField_apply (x : Vec d) (j : Fin d) :
    cubeTorsionField d x j = if j = default then -x (default : Fin d) else 0 := by
  unfold cubeTorsionField scalarToDivergenceField
  by_cases hj : j = (default : Fin d)
  · rw [ite_eq_left hj, ite_eq_left hj, coordinatePrimitive_one]
  · rw [ite_eq_right hj, ite_eq_right hj]

theorem vecNormSq_cubeTorsionField (x : Vec d) :
    vecNormSq (cubeTorsionField d x) = x (default : Fin d) * x (default : Fin d) := by
  classical
  unfold vecNormSq vecDot
  rw [Finset.sum_eq_single (default : Fin d)]
  · rw [cubeTorsionField_apply, ite_eq_left rfl]
    ring
  · intro j _ hj
    rw [cubeTorsionField_apply, ite_eq_right hj, mul_zero]
  · intro hcontra
    exact absurd (Finset.mem_univ (default : Fin d)) hcontra

theorem memVectorL2_cubeTorsionField {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : MemVectorL2 U (cubeTorsionField d) :=
  scalarToDivergenceField_memVectorL2 hU (fun _ => (1 : ℝ)) contDiff_const _ 0

/-! ## From the scalar equation to the shifted equation -/

/-- **The scalar weak equation is a shifted weak equation with shifted
forcing.**  On an open bounded convex domain every element of the zero-trace
graph carrier is an honest zero-trace Sobolev function, so the two test
classes agree. -/
theorem isAlphaShiftedWeakSolution_of_isScalarForcedWeakSolution
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {a : CoeffField d}
    {alpha : ℝ} (u : H10Function U) {g : Vec d → ℝ}
    (hg : IsScalarForcedWeakSolution a U g u.toH1Function) (G : ScalarL2 U)
    (hG : ∀ᵐ x ∂volumeMeasureOn U,
      G x = g x + alpha * u.toH1Function.toFun x) :
    IsAlphaShiftedWeakSolution a U alpha G
      (ZeroTraceSobolev.ofH10Function u) := by
  intro z
  obtain ⟨φ, hφvalue, hφgrad⟩ := ZeroTraceSobolev.exists_h10Function hU z
  have hvalue : ZeroTraceSobolev.toL2 z = φ.toH1Function.toScalarL2 := hφvalue.symm
  have hgrad : ZeroTraceSobolev.gradient z = φ.toH1Function.gradToHilbertVectorL2 :=
    hφgrad.symm
  have hcoefficient :
      coefficientPairing a U
          (ZeroTraceSobolev.gradient (ZeroTraceSobolev.ofH10Function u))
          (ZeroTraceSobolev.gradient z) =
        ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume := by
    rw [ZeroTraceSobolev.gradient_ofH10Function, hgrad, coefficientPairing]
    apply integral_congr_ae
    filter_upwards
      [u.toH1Function.coeFn_gradToHilbertVectorL2,
        φ.toH1Function.coeFn_gradToHilbertVectorL2,
        coeFn_hilbertVectorL2ToVectorL2 (U := U)
          u.toH1Function.gradToHilbertVectorL2,
        coeFn_hilbertVectorL2ToVectorL2 (U := U)
          φ.toH1Function.gradToHilbertVectorL2] with x hu hv hu' hv'
    rw [hu', hv', hu, hv]
    rfl
  have hmass :
      inner ℝ (ZeroTraceSobolev.toL2 (ZeroTraceSobolev.ofH10Function u))
          (ZeroTraceSobolev.toL2 z) =
        ∫ x in U, u.toH1Function.toFun x * φ.toH1Function.toFun x ∂volume := by
    rw [ZeroTraceSobolev.toL2_ofH10Function, hvalue, scalarInner_eq_integral]
    apply integral_congr_ae
    filter_upwards [u.toH1Function.coeFn_toScalarL2,
      φ.toH1Function.coeFn_toScalarL2] with x hu hv
    rw [hu, hv]
  have hforcing : inner ℝ G (ZeroTraceSobolev.toL2 z) =
      ∫ x in U, (g x + alpha * u.toH1Function.toFun x) *
        φ.toH1Function.toFun x ∂volume := by
    rw [hvalue, scalarInner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hG, φ.toH1Function.coeFn_toScalarL2] with x hGx hv
    rw [hGx, hv]
  have hgInt : Integrable (fun x => g x * φ.toH1Function.toFun x)
      (volumeMeasureOn U) := hg.1.integrable_mul φ.toH1Function.memL2
  have huInt : Integrable
      (fun x => alpha * (u.toH1Function.toFun x * φ.toH1Function.toFun x))
      (volumeMeasureOn U) :=
    (u.toH1Function.memL2.integrable_mul φ.toH1Function.memL2).const_mul alpha
  rw [hcoefficient, hmass, hforcing, hg.2 φ]
  calc
    alpha * ∫ x in U, u.toH1Function.toFun x * φ.toH1Function.toFun x ∂volume +
          ∫ x in U, g x * φ.toH1Function.toFun x ∂volume =
        (∫ x in U, alpha *
            (u.toH1Function.toFun x * φ.toH1Function.toFun x) ∂volume) +
          ∫ x in U, g x * φ.toH1Function.toFun x ∂volume := by
      rw [integral_const_mul]
    _ = ∫ x in U, (g x * φ.toH1Function.toFun x +
          alpha * (u.toH1Function.toFun x * φ.toH1Function.toFun x)) ∂volume := by
      rw [integral_add hgInt huInt]
      ring
    _ = ∫ x in U, (g x + alpha * u.toH1Function.toFun x) *
          φ.toH1Function.toFun x ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      ring

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The torsion function -/

/-- **A measurable torsion function exists on every exhaustion cube.** -/
theorem exists_measurable_cubeTorsionSolution (v : ℕ) :
    ∃ w : H10Function (wholeSpaceCube d v),
      Measurable w.toH1Function.toFun ∧
        IsZeroTraceDirichletRhsWeakSolution A.a (wholeSpaceCube d v) w
          (cubeTorsionField d) := by
  classical
  have hU : IsOpenBoundedConvexDomain (wholeSpaceCube d v) :=
    isOpenBoundedConvexDomain_wholeSpaceCube d v
  have : IsFiniteMeasure (volumeMeasureOn (wholeSpaceCube d v)) :=
    hU.isFiniteMeasure_restrict_volume
  obtain ⟨w0, hw0⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := A.a) (U := wholeSpaceCube d v) (g := cubeTorsionField d)
      (memVectorL2_cubeTorsionField hU)
      (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
        hU)
      (wholeSpaceCube_nonempty d v) (A.cubeEllipticity v)
  obtain ⟨w, hwmeas, -, hwsol⟩ :=
    HCPolySupport.IsZeroTraceDirichletRhsWeakSolution.exists_measurableH10Rep hU hw0
  exact ⟨w, hwmeas, hwsol⟩

/-- The chosen measurable torsion function of an exhaustion cube. -/
def cubeTorsionFunction (v : ℕ) : H10Function (wholeSpaceCube d v) :=
  Classical.choose (A.exists_measurable_cubeTorsionSolution v)

theorem measurable_cubeTorsionFunction (v : ℕ) :
    Measurable (A.cubeTorsionFunction v).toH1Function.toFun :=
  (Classical.choose_spec (A.exists_measurable_cubeTorsionSolution v)).1

theorem cubeTorsionFunction_isZeroTraceDirichletRhsWeakSolution (v : ℕ) :
    IsZeroTraceDirichletRhsWeakSolution A.a (wholeSpaceCube d v)
      (A.cubeTorsionFunction v) (cubeTorsionField d) :=
  (Classical.choose_spec (A.exists_measurable_cubeTorsionSolution v)).2

/-- **The torsion function solves the unshifted problem with constant
forcing.** -/
theorem cubeTorsionFunction_isScalarForcedWeakSolution (v : ℕ) :
    IsScalarForcedWeakSolution A.a (wholeSpaceCube d v) (fun _ => (1 : ℝ))
      (A.cubeTorsionFunction v).toH1Function := by
  have : IsFiniteMeasure (volumeMeasureOn (wholeSpaceCube d v)) :=
    (isOpenBoundedConvexDomain_wholeSpaceCube d v).isFiniteMeasure_restrict_volume
  refine ⟨memLp_const (1 : ℝ), fun φ => ?_⟩
  rw [A.cubeTorsionFunction_isZeroTraceDirichletRhsWeakSolution v φ]
  exact integral_scalarToDivergenceField_vecDot_grad_eq
    (isOpenBoundedConvexDomain_wholeSpaceCube d v) (fun _ => (1 : ℝ))
    contDiff_const default 0 φ

/-! ## The uniform bound -/

/-- **The dimensional constant of the torsion bound.**  It is twice the De
Giorgi constant of the dimension.  It reads the analytic data only through the
proof of `2 ≤ d`, so it does not depend on the cube, on the coefficient field
or on the lower ellipticity constant. -/
def cubeTorsionConstant : ℝ :=
  2 * Classical.choose (Regularity.exists_deGiorgi_bound_constant A.hd)

theorem cubeTorsionConstant_nonneg : 0 ≤ A.cubeTorsionConstant := by
  have h := (Classical.choose_spec (Regularity.exists_deGiorgi_bound_constant A.hd)).1
  rw [cubeTorsionConstant]
  linarith only [h]

/-- The uniform bound for the torsion function of an exhaustion cube: the
dimensional constant times the square root of the dimension, divided by the
lower ellipticity constant, times the square of the half-side of the cube. -/
def cubeTorsionBound (v : ℕ) : ℝ :=
  A.cubeTorsionConstant * (Real.sqrt d / A.nu) * ((3 : ℝ) ^ v * (3 : ℝ) ^ v)

theorem cubeTorsionBound_nonneg (v : ℕ) : 0 ≤ A.cubeTorsionBound v := by
  have h1 : (0 : ℝ) ≤ Real.sqrt d / A.nu :=
    div_nonneg (Real.sqrt_nonneg _) A.hnu.le
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ v * (3 : ℝ) ^ v := by positivity
  exact mul_nonneg (mul_nonneg A.cubeTorsionConstant_nonneg h1) h2

/-- **The torsion function of an exhaustion cube is uniformly bounded, with a
constant that does not depend on the cube.**  The divergence form of the
constant forcing has length at most the half-side of the cube, so the
divergence-form De Giorgi estimate applies at the dimensional constant, and
the resulting bound is that constant times the square root of the dimension,
divided by the lower ellipticity constant, times the square of the
half-side. -/
theorem abs_cubeTorsionFunction_le (v : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      |(A.cubeTorsionFunction v).toH1Function.toFun x| ≤ A.cubeTorsionBound v := by
  have hU : IsOpenBoundedConvexDomain (wholeSpaceCube d v) :=
    isOpenBoundedConvexDomain_wholeSpaceCube d v
  have hgBound : ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d v),
      Real.sqrt (vecNormSq (cubeTorsionField d x)) ≤ (3 : ℝ) ^ v := by
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [vecNormSq_cubeTorsionField, ← sq, Real.sqrt_sq_eq_abs]
    exact abs_le.mpr ⟨(mem_wholeSpaceCube_iff.mp hx default).1.le,
      (mem_wholeSpaceCube_iff.mp hx default).2.le⟩
  have hbound :=
    (Classical.choose_spec (Regularity.exists_deGiorgi_bound_constant A.hd)).2
      (fun _ => -((3 : ℝ) ^ v)) (2 * (3 : ℝ) ^ v) (by positivity)
      A.a A.nu (A.cubeEllipticityUpper v) A.hnu (A.cubeEllipticity v)
      (A.cubeTorsionFunction v) (cubeTorsionField d)
      (A.cubeTorsionFunction_isZeroTraceDirichletRhsWeakSolution v)
      (A.measurable_cubeTorsionFunction v) (memVectorL2_cubeTorsionField hU)
      ((3 : ℝ) ^ v) (by positivity) hgBound
  filter_upwards [hbound] with x hx
  calc |(A.cubeTorsionFunction v).toH1Function.toFun x|
      ≤ Classical.choose (Regularity.exists_deGiorgi_bound_constant A.hd) *
          (2 * (3 : ℝ) ^ v) * (Real.sqrt d / A.nu * (3 : ℝ) ^ v) := hx
    _ = A.cubeTorsionBound v := by
        rw [cubeTorsionBound, cubeTorsionConstant]
        ring

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
