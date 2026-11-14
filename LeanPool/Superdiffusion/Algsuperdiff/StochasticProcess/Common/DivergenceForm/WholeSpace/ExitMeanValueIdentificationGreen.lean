/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEIdentification

/-!
# ExitMeanValueIdentificationGreen

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Green potential is the zero-trace weak solution of the unshifted Dirichlet problem

The vanishing-shift limit of the Dirichlet resolvents of a bounded
measurable datum on an exhaustion cube is here identified analytically: it is the value function
of an honest zero-trace Sobolev function on the cube solving
  `-div (a grad w) = f`   weakly, with zero trace,

and it is the only such value function up to almost-everywhere equality.

The representative is exact: the module produces an `H10Function` whose value function *is*
the Green potential, not merely a function almost everywhere equal to it.  Pointwise arguments
downstream read the values of the Green potential, so the exact representative matters.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open ZeroTraceSobolev
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ}

/-! ## Two generic transfers -/

/-- An `H¹` function whose value function is replaced by an almost everywhere equal one. -/
theorem exists_h1Function_toFun_eq {U : Set (Vec d)} (u : H1Function U) {g : Vec d → ℝ}
    (hg : MemL2On U g) (hgu : g =ᵐ[volumeMeasureOn U] u.toFun) :
    ∃ w : H1Function U, w.toFun = g ∧ w.grad = u.grad := by
  refine ⟨⟨g, u.grad, hg, u.gradMemL2, ?_⟩, rfl, rfl⟩
  intro i φ hφ hφc hφsub
  have hu := u.hasWeakGradient i φ hφ hφc hφsub
  have hcongr : ∫ x in U, g x * (fderiv ℝ φ x) (basisVec i) ∂volume =
      ∫ x in U, u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgu] with x hx
    rw [hx]
  rw [hcongr, hu]

/-- The scalar-forced weak equation only sees the almost-everywhere class of its datum. -/
theorem IsScalarForcedWeakSolution.congr_datum {U : Set (Vec d)} {a : CoeffField d}
    {g g' : Vec d → ℝ} {u : H1Function U} (h : IsScalarForcedWeakSolution a U g u)
    (hgg : g' =ᵐ[volumeMeasureOn U] g) :
    IsScalarForcedWeakSolution a U g' u := by
  refine ⟨(MeasureTheory.memLp_congr_ae hgg).mpr h.1, fun φ ↦ ?_⟩
  rw [h.2 φ]
  refine integral_congr_ae ?_
  filter_upwards [hgg] with x hx
  rw [hx]

variable [NeZero d]

omit [NeZero d] in
/-- The `L²` class of the datum agrees almost everywhere on the cube with the datum. -/
theorem cubeDatumL2_ae (v : ℕ) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) :
    ⇑(cubeDatumL2 v hf hfD) =ᵐ[volumeMeasureOn (wholeSpaceCube d v)] f := by
  have hcoe : ⇑(cubeDatumL2 v hf hfD) =ᵐ[volumeMeasureOn (wholeSpaceCube d v)]
      domainExtension (f ∘ Subtype.val) :=
    boundedMeasurableToScalarL2_coeFn (isOpenBoundedConvexDomain_wholeSpaceCube d v)
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)
  filter_upwards [hcoe,
    ae_restrict_mem (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen.measurableSet]
    with x hx hxmem
  rw [hx, domainExtension_of_mem hxmem]
  rfl

end

end DivergenceFormProcess.Form
