/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationWhole
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PartGreenH10

/-!
# PartWholeHarmonic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The whole-space resolvent and its harmonic part on a bounded part domain

The whole-space resolvent `psi = R_mu f` is an `H¹` function of every exhaustion cube and solves

  `-div (a grad psi) = f - mu psi`   weakly there.

A bounded open convex domain lies inside an exhaustion cube, and both the `H¹` membership and the
weak equation restrict to an open subset, so the same two statements hold on the domain with no
new analysis.  Subtracting the Green potential of the same residual on the domain leaves the
harmonic part of the whole-space resolvent there: it is weakly `a`-harmonic on the domain and
differs from `psi` by a named zero-trace Sobolev function.

This is the statement of `ExitMeanValueIdentificationWhole.lean` with the exhaustion cube
replaced by an arbitrary bounded open convex domain; the Caccioppoli Cauchy estimate and the
exhaustion limit are consumed through the cube statement and are not repeated.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The whole-space resolvent on a bounded part domain -/

/-- **The whole-space resolvent is an `H¹` function of every bounded part domain and solves the
shifted equation there.**  Its value function is the exact continuous representative of the
resolvent, not merely a function almost everywhere equal to it. -/
theorem exists_h1Function_analyticMinimalResolventReal_part {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ∃ z : H1Function V,
      z.toFun = A.analyticMinimalResolventReal mu f hf hfD ∧
        IsScalarForcedWeakSolution A.a V (A.wholeSpaceResidual mu hf hfD) z := by
  obtain ⟨z, hzval, hzsol⟩ :=
    A.exists_h1Function_analyticMinimalResolventReal (partCubeIndex hV) mu hf hD hfD
  exact ⟨z.restrict hV.isOpen (subset_wholeSpaceCube_partCubeIndex hV), hzval,
    hzsol.restrictSubset hV.isOpen (subset_wholeSpaceCube_partCubeIndex hV)⟩

/-! ## The harmonic part -/

/-- **The harmonic part of the whole-space resolvent on a bounded part domain**: the resolvent
less the Green potential of its residual. -/
def partWholeSpaceHarmonicPart {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) : Vec d → ℝ :=
  fun y ↦ A.analyticMinimalResolventReal mu f hf hfD y -
    A.partGreenPotential hV (A.wholeSpaceResidual mu hf hfD)
      (A.measurable_wholeSpaceResidual mu hf hfD) (cubeLevelResidualBound_nonneg hD)
      (A.abs_wholeSpaceResidual_le mu hf hfD) y

/-- **The harmonic part of the whole-space resolvent is weakly `a`-harmonic on the part domain,
and differs from the whole-space resolvent by a named zero-trace Sobolev function.** -/
theorem exists_h1Function_partWholeSpaceHarmonicPart {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) :
    ∃ h : H1Function V,
      h.toFun = A.partWholeSpaceHarmonicPart hV mu hf hD hfD ∧
        IsScalarForcedWeakSolution A.a V (fun _ ↦ (0 : ℝ)) h ∧
        ∀ y, A.analyticMinimalResolventReal mu f hf hfD y - h.toFun y =
          (A.partGreenH10 hV (A.measurable_wholeSpaceResidual mu hf hfD)
            (cubeLevelResidualBound_nonneg hD)
            (A.abs_wholeSpaceResidual_le mu hf hfD)).toH1Function.toFun y := by
  obtain ⟨z, hzval, hzsol⟩ := A.exists_h1Function_analyticMinimalResolventReal_part hV mu hf hD hfD
  have hwsol := A.isScalarForcedWeakSolution_partGreenH10 hV
    (A.measurable_wholeSpaceResidual mu hf hfD) (cubeLevelResidualBound_nonneg hD)
    (A.abs_wholeSpaceResidual_le mu hf hfD)
  have hdiff := hzsol.sub (partEllipticity A hV) hwsol
  have hwval := A.partGreenH10_toFun hV (A.measurable_wholeSpaceResidual mu hf hfD)
    (cubeLevelResidualBound_nonneg hD) (A.abs_wholeSpaceResidual_le mu hf hfD)
  set w : H10Function V := A.partGreenH10 hV (A.measurable_wholeSpaceResidual mu hf hfD)
    (cubeLevelResidualBound_nonneg hD) (A.abs_wholeSpaceResidual_le mu hf hfD) with hwdef
  have hfun : (z - w.toH1Function).toFun = A.partWholeSpaceHarmonicPart hV mu hf hD hfD := by
    rw [H1Function.sub_toFun]
    funext y
    show z.toFun y - w.toH1Function.toFun y = _
    rw [hzval, hwval]
    rfl
  refine ⟨z - w.toH1Function, hfun, ?_, ?_⟩
  · refine hdiff.congr_datum ?_
    filter_upwards with x
    rw [sub_self]
  · intro y
    rw [hfun, hwval]
    simp only [partWholeSpaceHarmonicPart]
    ring

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
