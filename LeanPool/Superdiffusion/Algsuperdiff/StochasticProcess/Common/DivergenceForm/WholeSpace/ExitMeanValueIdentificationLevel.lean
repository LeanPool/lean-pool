/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolutionRestriction
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationGreen
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Vanishing

/-!
# ExitMeanValueIdentificationLevel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The harmonic part of a cube resolvent at a finite exhaustion level

Fix two exhaustion cubes `V ⊆ W` and a positive shift.  The Dirichlet resolvent of `W` applied
to a bounded measurable datum is an honest `H¹` function of `W` — this is the level-`W` solution
of `ExitTimePDEIdentification.lean`, with its value function replaced by the exact continuous
representative — and it solves

  `-div (a grad psi) = f - mu psi`   weakly on `W`, hence also weakly on `V`.

Subtracting the Green potential on `V` of the same residual `f - mu psi`, which is the zero-trace
solution of `-div (a grad w) = f - mu psi` on `V`, leaves a function that is weakly `a`-harmonic
on `V` and differs from `psi` by that zero-trace function.  That is the level-`W` harmonic part.

No limit and no compactness argument is used: at a finite level the resolvent is a zero-trace
Sobolev function of the larger cube by construction, and restriction of the weak equation to an
open subset is the zero-extension of test functions.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-! ## The residual of a cube resolvent -/

/-- The residual of the Dirichlet resolvent of an exhaustion cube: the datum less the shift
times the resolvent. -/
def cubeLevelResidual (m : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) : Vec d → ℝ :=
  fun y ↦ f y - (mu : ℝ) * A.analyticCubeResolvent mu f hf hfD m y

theorem measurable_cubeLevelResidual (m : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.cubeLevelResidual m mu hf hfD) :=
  hf.sub ((A.measurable_analyticCubeResolvent mu hf hfD m).const_mul _)

theorem abs_cubeLevelResidual_le (m : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (y : Vec d) :
    |A.cubeLevelResidual m mu hf hfD y| ≤ 2 * D := by
  have hbound := A.abs_analyticCubeResolvent_le mu hf hD hfD m y
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
  have hsecond : |(mu : ℝ) * A.analyticCubeResolvent mu f hf hfD m y| ≤ D := by
    rw [abs_mul, abs_of_pos hmu]
    calc
      (mu : ℝ) * |A.analyticCubeResolvent mu f hf hfD m y| ≤ (mu : ℝ) * (D / (mu : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hmu.le
      _ = D := mul_div_cancel₀ D hmu.ne'
  refine (abs_sub _ _).trans ?_
  linarith only [hfD y, hsecond]

theorem cubeLevelResidualBound_nonneg {D : ℝ} (hD : 0 ≤ D) : (0 : ℝ) ≤ 2 * D := by
  linarith only [hD]

/-! ## The exact `H¹` representative of a cube resolvent -/

/-- **The Dirichlet resolvent of an exhaustion cube is an `H¹` function of that cube** whose
value function is the continuous representative, and it solves the shifted equation with the
residual as forcing. -/
theorem exists_cubeResolventH1 (m : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    ∃ z : H1Function (wholeSpaceCube d m),
      z.toFun = A.analyticCubeResolvent mu f hf hfD m ∧
        IsScalarForcedWeakSolution A.a (wholeSpaceCube d m)
          (A.cubeLevelResidual m mu hf hfD) z := by
  have hsol := A.cubeDatumResolventH10_isScalarForcedWeakSolution mu hf hfD m
  dsimp only at hsol
  have hvalue : (A.cubeDatumResolventH10 mu hf hfD m).toH1Function.toFun
      =ᵐ[volumeMeasureOn (wholeSpaceCube d m)] A.analyticCubeResolvent mu f hf hfD m := by
    have h2 := A.cubeDatumResolventH10_value mu hf hfD m
    have h3 := A.analyticCubeResolvent_ae mu hf hfD m
    filter_upwards [(A.cubeDatumResolventH10 mu hf hfD m).toH1Function.coeFn_toScalarL2, h3]
      with x hx1 hx3
    rw [← hx1, h2, ← hx3]
  have hmem : MemL2On (wholeSpaceCube d m) (A.analyticCubeResolvent mu f hf hfD m) :=
    (MeasureTheory.memLp_congr_ae hvalue).mp
      (A.cubeDatumResolventH10 mu hf hfD m).toH1Function.memL2
  obtain ⟨z, hzval, hzgrad⟩ :=
    exists_h1Function_toFun_eq (A.cubeDatumResolventH10 mu hf hfD m).toH1Function hmem
      hvalue.symm
  refine ⟨z, hzval, ?_⟩
  have hsol' : IsScalarForcedWeakSolution A.a (wholeSpaceCube d m)
      (fun y ↦ (cubeDatumL2 m hf hfD) y -
        (mu : ℝ) * (A.cubeDatumResolventH10 mu hf hfD m).toH1Function.toFun y) z := by
    refine ⟨hsol.1, fun phi ↦ ?_⟩
    rw [hzgrad]
    exact hsol.2 phi
  refine hsol'.congr_datum ?_
  filter_upwards [cubeDatumL2_ae m hf hfD, hvalue] with x hx1 hx2
  rw [hx1, hx2]
  rfl

/-! ## The level harmonic part -/

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
