/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreNonsymmetricCounterexampleCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreNonsymmetricCounterexampleMoments
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakPermutation
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Ginibre nonsymmetric counterexample coordinates

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `ginibre_coordinate_re_sq_integral`.
-/

@[expose] public section
open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem ginibre_coordinate_re_sq_integrable (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    Integrable (fun z : Configuration n => (z i).re^2) (ginibreMeasure n) := by
  apply (ginibre_configurationNormSq_integrable n hn).mono'
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).re^2) (ginibreMeasure n) from (show
        Continuous (fun z : Configuration n => (z i).re^2) by fun_prop).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro z
  have h := Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  simp only [Real.norm_eq_abs, abs_sq]
  change (z i).re^2≤∑ j, Complex.normSq (z j)
  have hi : (z i).re^2≤Complex.normSq (z i) := by rw [Complex.normSq_apply]; nlinarith [sq_nonneg (z
                                                    i).im]
  exact hi.trans h

theorem ginibre_coordinate_im_sq_integrable (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    Integrable (fun z : Configuration n => (z i).im^2) (ginibreMeasure n) := by
  apply (ginibre_configurationNormSq_integrable n hn).mono'
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).im^2) (ginibreMeasure n) from (show
        Continuous (fun z : Configuration n => (z i).im^2) by fun_prop).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro z
  have h := Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  simp only [Real.norm_eq_abs, abs_sq]
  change (z i).im^2≤∑ j, Complex.normSq (z j)
  have hi : (z i).im^2≤Complex.normSq (z i) := by rw [Complex.normSq_apply]; nlinarith [sq_nonneg (z
                                                    i).re]
  exact hi.trans h

theorem ginibre_coordinate_re_sq_eq_im_sq (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (∫ z : Configuration n, (z i).re^2 ∂ginibreMeasure n)=
      ∫ z : Configuration n, (z i).im^2 ∂ginibreMeasure n := by
  have hp := measurePreserving_globalPhase_ginibreMeasure (by omega : 0<n)
    Complex.I (by simp)
  have h := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).re^2)
      ((ginibreMeasure n).map (globalPhase Complex.I)) from
      (show Continuous (fun z : Configuration n => (z i).re^2) by fun_prop).aestronglyMeasurable)
  rw [hp.map_eq] at h
  simpa [globalPhase, Complex.mul_re] using h

theorem ginibre_coordinate_re_sq_eq (n : ℕ) (_ : 2 ≤ n) (i j : Fin n) :
    (∫ z : Configuration n, (z i).re^2 ∂ginibreMeasure n)=
      ∫ z : Configuration n, (z j).re^2 ∂ginibreMeasure n := by
  have hp := ginibre_measurePreserving_permute (Equiv.swap i j)
  have h := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).re^2)
      ((ginibreMeasure n).map (permute (Equiv.swap i j))) from
      (show Continuous (fun z : Configuration n => (z i).re^2) by fun_prop).aestronglyMeasurable)
  rw [hp.map_eq] at h
  simpa [permute] using h

theorem ginibre_coordinate_re_sq_integral (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (∫ z : Configuration n, (z i).re^2 ∂ginibreMeasure n)=((n : ℝ)+1)/(4*(n : ℝ)) := by
  have hsum : (∫ z, configurationNormSq z ∂ginibreMeasure n)=
      2*(n : ℝ)*(∫ z : Configuration n, (z i).re^2 ∂ginibreMeasure n) := by
    unfold configurationNormSq
    simp_rw [Complex.normSq_apply,← sq]
    rw [integral_finsetSum _ (fun j _ =>
      show Integrable (fun z : Configuration n => (z j).re^2+(z j).im^2) (ginibreMeasure n) from
      (ginibre_coordinate_re_sq_integrable n hn j).add (ginibre_coordinate_im_sq_integrable n hn
          j))]
    simp_rw [integral_add (ginibre_coordinate_re_sq_integrable n hn _)
      (ginibre_coordinate_im_sq_integrable n hn _),← ginibre_coordinate_re_sq_eq_im_sq n hn]
    simp_rw [ginibre_coordinate_re_sq_eq n hn _ i]
    simp
    ring
  rw [ginibre_configurationNormSq_integral n hn] at hsum
  have hnR : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  apply (eq_div_iff (by positivity : 4*(n : ℝ)≠0)).mpr
  linarith

end
end GinibrePoincare
