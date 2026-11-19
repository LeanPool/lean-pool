/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreRadiusNotHolomorphic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.HolomorphicQuotientPhaseFinite
public import LeanPool.GinibrePoincare.Analysis.GinibreTwoRadiusEquilibriumLaw
public import LeanPool.GinibrePoincare.Analysis.GammaPolynomialMoments
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorPolynomialMoments
public import LeanPool.GinibrePoincare.Analysis.GinibreInteriorWeakGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-! The paper's literal symmetric radial counterexample to holomorphic divisibility. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

theorem ginibre_configurationNormSq_memLp_two {n : ℕ} (hn : 0 < n) :
    MemLp (configurationNormSq : Configuration n → ℝ) 2 (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hc : MemLp (ginibreCenterSquared n) 2 (ginibreMeasure n) := by
    have hi : MemLp (fun x : ℝ => x) 2 (gammaMeasure 1 1) := by
      apply (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      simpa [Real.norm_eq_abs] using Laguerre.integrable_pow_gamma 1 2 (by decide)
    rw [← ginibreCenterSquared_equilibrium_gamma n hn] at hi
    exact hi.comp_of_map (by unfold ginibreCenterSquared coordinateSum; fun_prop)
  have hr : MemLp (pairwiseRadius : Configuration n → ℝ) 2 (ginibreMeasure n) := by
    by_cases h : n=1
    · subst n
      have he : (pairwiseRadius : Configuration 1 → ℝ)=fun _ => 0 := by
        funext z
        simp [pairwiseRadius]
      rw [he]
      exact memLp_const (0 : ℝ)
    · have hn2 : 2≤n := by omega
      apply (memLp_two_iff_integrable_sq_norm
        (show Continuous (pairwiseRadius : Configuration n → ℝ) by
          unfold pairwiseRadius; fun_prop).aestronglyMeasurable).mpr
      simpa [Real.norm_eq_abs] using ginibreFull_polynomial_joint_moment_integrable n hn2 0 2
  have he : (configurationNormSq : Configuration n → ℝ)=
      fun z => (ginibreCenterSquared n z+pairwiseRadius z)/(n : ℝ) := by
    funext z
    have hp := pairwiseRadius_eq_normSq z
    dsimp [ginibreCenterSquared] at *
    have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    field_simp
    nlinarith
  rw [he]
  simpa [div_eq_mul_inv, mul_comm] using (hc.add hr).const_mul ((n : ℝ)⁻¹)

/-- The squared norm `z ↦ configurationNormSq z`, as a complex-valued element of `L²` of the
Ginibre measure. -/
def ginibreSquaredNormL2 (n : ℕ) (hn : 0 < n) : Lp ℂ 2 (ginibreMeasure n) :=
  (Complex.ofRealCLM.comp_memLp' (ginibre_configurationNormSq_memLp_two hn)).toLp
    (fun z => (configurationNormSq z : ℂ))

theorem ginibreSquaredNormL2_coeFn (n : ℕ) (hn : 0 < n) :
    ginibreSquaredNormL2 n hn =ᵐ[ginibreMeasure n] fun z => (configurationNormSq z : ℂ) :=
  (Complex.ofRealCLM.comp_memLp' (ginibre_configurationNormSq_memLp_two hn)).coeFn_toLp

theorem ginibreSquaredNormL2_phase_zero (n : ℕ) (hn : 0 < n) :
    ginibreSquaredNormL2 n hn ∈ ginibreHolomorphicPhaseDegree n 0 hn := by
  intro u hu
  simp only [pow_zero, one_smul]
  apply Lp.ext
  have mp := measurePreserving_globalPhase_ginibreMeasure hn u hu
  have hcomp := mp.quasiMeasurePreserving.ae_eq_comp (ginibreSquaredNormL2_coeFn n hn)
  filter_upwards [Lp.coeFn_compMeasurePreserving (ginibreSquaredNormL2 n hn) mp,
    hcomp, ginibreSquaredNormL2_coeFn n hn] with z hz ht he
  change (ginibreGlobalPhaseL2 hn u hu (ginibreSquaredNormL2 n hn)) z = _
  change (ginibreGlobalPhaseL2 hn u hu (ginibreSquaredNormL2 n hn)) z =
    (ginibreSquaredNormL2 n hn) (globalPhase u z) at hz
  rw [hz]
  rw [show (ginibreSquaredNormL2 n hn) (globalPhase u z) = (configurationNormSq (globalPhase u z) :
      ℂ) from ht, he]
  congr 1
  simp [configurationNormSq, globalPhase, Complex.normSq_eq_norm_sq, hu]

/-- The literal squared Euclidean radius has no holomorphic quotient representative. -/
theorem ginibreSquaredNormL2_not_holomorphic (n : ℕ) (hn : 0 < n) :
    ginibreSquaredNormL2 n hn ∉ ginibreHolomorphicAmbientClosedSpan n hn := by
  intro hh
  let := ginibreMeasure_isProbabilityMeasure hn
  have hd := ginibre_holomorphic_phase_mem_quotientDegree hn _ hh
    (ginibreSquaredNormL2_phase_zero n hn)
  rw [ginibreFiniteQuotientDegreeZero_eq_constants] at hd
  obtain ⟨a, ha⟩ := hd
  have hac : ginibreSquaredNormL2 n hn =ᵐ[ginibreMeasure n] fun _ => a := by
    rw [← ha]
    exact Lp.coeFn_const _ _ _
  have hae := (ginibreSquaredNormL2_coeFn n hn).symm.trans hac
  have hv := (ginibre_ae_eq_iff_volume n hn _ _).mp hae
  have hf : Continuous (fun z : Configuration n => (configurationNormSq z : ℂ)) := by
    unfold configurationNormSq
    fun_prop
  have he := (hf.ae_eq_iff_eq volume continuous_const).mp hv
  have hzero := congrFun he 0
  have hone := congrFun he (fun _ => (1 : ℂ))
  have h10 := hone.trans hzero.symm
  simp [configurationNormSq, hn.ne'] at h10

end
end GinibrePoincare
