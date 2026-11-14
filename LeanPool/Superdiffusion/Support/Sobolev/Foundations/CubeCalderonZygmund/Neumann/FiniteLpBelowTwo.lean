/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Support.Sobolev.Foundations.CubeCalderonZygmund.Neumann.EnergyDuality
public import LeanPool.Superdiffusion.Support.Sobolev.Foundations.CubeCalderonZygmund.Neumann.FiniteLpAboveTwo
public import LeanPool.Superdiffusion.Support.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpAdjoint

/-!
# FiniteLpBelowTwo

Ported from scottnarmstrong/CoarseGraining at c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Below-two Neumann cube Calderón--Zygmund estimate

This file proves the adjoint-duality branch for a supplied mean-zero Neumann
solution with only `L^p` datum, then combines it with the energy and good-`λ`
branches to cover every finite exponent.
-/

namespace HCPolySupport

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

/-- The below-two supplied-solution Neumann CZ estimate with `L^p`-only datum. -/
theorem centeredCubeH1MeanZeroNeumannDivergence_cz_lpData_of_lt_two
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : q.exponent.toReal < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanLpField (originCube d m) q)
      (u : H1MeanZeroFunction (openCubeSet (originCube d m))), 0 < sigma0 →
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
        (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x) →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH1MeanZeroNeumannDivergence_cz_of_two_lt d
    q.conjugate (INTERNAL.conjugate_toReal_gt_two_of_lt_two q hq)
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  refine cubeEuclideanLpENorm_le_of_adjoint_bound (originCube d m) q h
    u.toH1Function.grad_memVectorL2 (K := C * (ENNReal.ofReal sigma0)⁻¹) ?_ ?_
  · exact ENNReal.mul_ne_top hCtop.ne
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0)))
  · intro Gfield hGtwo
    let v := centeredCubeMeanZeroScalarDivergenceSolution m hsigma0 Gfield.toField hGtwo
    refine ⟨v.toH1Function.grad, v.toH1Function.grad_memVectorL2, ?_, ?_⟩
    · apply hC m sigma0 Gfield v hsigma0
      exact centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
        m hsigma0 Gfield.toField hGtwo
    · exact centeredCubeMeanZeroScalarDivergenceSolution_normalized_cross_pairing
        m hsigma0 u h.toField Gfield.toField hsolution hGtwo

/-- The supplied-solution centered-cube Neumann Calderón--Zygmund estimate for
every finite exponent and an `L^p` datum.  No auxiliary `L²` hypothesis is
exposed. -/
theorem centeredCubeH1MeanZeroNeumannDivergence_cz_lpData
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanLpField (originCube d m) q)
      (u : H1MeanZeroFunction (openCubeSet (originCube d m))), 0 < sigma0 →
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
        (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x) →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  by_cases hlt : q.exponent.toReal < 2
  · exact centeredCubeH1MeanZeroNeumannDivergence_cz_lpData_of_lt_two d q hlt
  by_cases hgt : 2 < q.exponent.toReal
  · obtain ⟨C, hCtop, hC⟩ :=
      centeredCubeH1MeanZeroNeumannDivergence_cz_of_two_lt d q hgt
    refine ⟨C, hCtop, ?_⟩
    intro m sigma0 h u hsigma0 hsolution
    have htwo_le : (2 : ℝ≥0∞) ≤ q.exponent := by
      apply (ENNReal.toReal_le_toReal (by norm_num) q.lt_top.ne).mp
      simpa only [ENNReal.toReal_ofNat] using hgt.le
    let hL2Lp : CubeEuclideanL2LpField (originCube d m) q :=
      { toCubeEuclideanLpField := h
        euclideanMemL2 := h.euclideanMemLp.mono_exponent htwo_le }
    simpa only [hL2Lp] using hC m sigma0 hL2Lp u hsigma0 hsolution
  have hreal : q.exponent.toReal = 2 :=
    le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
  have hexp : q.exponent = 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' q.lt_top.ne (by norm_num)).mp
    simpa only [ENNReal.toReal_ofNat] using hreal
  have hq : q = FiniteLpExponent.two := by
    cases q
    simp only [FiniteLpExponent.two] at hexp ⊢
    cases hexp
    rfl
  subst q
  refine ⟨1, by norm_num, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  simpa only [one_mul] using
    centeredCubeH1MeanZeroScalarDivergence_cz_two m sigma0 h u hsigma0 hsolution

end CubeCalderonZygmund

end
end HCPolySupport
