/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryPositiveWeightClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryPositiveWeightPairing
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryJointWeyl
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryEntireCRTests

/-!
# Correspondence auxiliary positive weight closure

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `isClosed_positiveLocalWeightedEntireL2`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The classes in `L²` of the measure with density `w` that admit an entire
(complex-differentiable) representative. -/
def positiveLocalWeightedEntireL2 (n : ℕ) (w : Configuration n → ℝ) :
    Set (Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z)))) :=
  {u | ∃ F : Configuration n → ℂ, Differentiable ℂ F ∧
    F =ᵐ[volume.withDensity (fun z => ENNReal.ofReal (w z))] u}

private def CRCompactKernel {n : ℕ} (θ : Configuration n → ℝ) (j : Fin n)
    (z : Configuration n) : ℂ :=
  (fderiv ℝ θ z (realCoordinateDirection j) : ℂ) +
    Complex.I*(fderiv ℝ θ z (imaginaryCoordinateDirection j) : ℂ)

private theorem CRCompactKernel_continuous {n : ℕ} (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (j : Fin n) : Continuous (CRCompactKernel θ j) := by
  exact ((Complex.continuous_ofReal.comp
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const))).add
      (continuous_const.mul (Complex.continuous_ofReal.comp
        ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)))

private theorem CRCompactKernel_compact {n : ℕ} (θ : Configuration n → ℝ)
    (hc : HasCompactSupport θ) (j : Fin n) : HasCompactSupport (CRCompactKernel θ j) := by
  have hr : HasCompactSupport (fun z => (fderiv ℝ θ z (realCoordinateDirection j) : ℂ)) :=
    (hc.fderiv_apply ℝ _).comp_left (g := Complex.ofReal) (by simp)
  have hi : HasCompactSupport (fun z => (fderiv ℝ θ z (imaginaryCoordinateDirection j) : ℂ)) :=
    (hc.fderiv_apply ℝ _).comp_left (g := Complex.ofReal) (by simp)
  exact hr.add (hi.mul_left (f := fun _ => Complex.I))

private theorem weighted_volume_AC {n : ℕ} (w : Configuration n → ℝ)
    (hwm : Measurable w)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z) :
    volume ≪ volume.withDensity (fun z => ENNReal.ofReal (w z)) := by
  apply withDensity_absolutelyContinuous' (hwm.ennreal_ofReal.aemeasurable)
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨c, hc, hcw⟩ := hw {z} (isCompact_singleton)
  exact (ENNReal.ofReal_pos.mpr (hc.trans_le (hcw z (by simp)))).ne'

private theorem mem_positiveLocalWeightedEntireL2_iff_tests {n : ℕ}
    (w : Configuration n → ℝ) (hwm : Measurable w)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    (u : Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z)))) :
    u ∈ positiveLocalWeightedEntireL2 n w ↔
      ∀ θ : {θ : Configuration n → ℝ // ContDiff ℝ ∞ θ ∧ HasCompactSupport θ},
        ∀ j : Fin n, positiveWeightCompactPairing w hw (CRCompactKernel θ.val j)
          (CRCompactKernel_continuous θ.val θ.property.1 j)
          (CRCompactKernel_compact θ.val θ.property.2 j) u = 0 := by
  constructor
  · rintro ⟨F, hF, he⟩ θ j
    rw [positiveWeightCompactPairing_eq_integral]
    have heV := (weighted_volume_AC w hwm hw).ae_eq he
    calc
      _ = ∫ z, F z * CRCompactKernel θ.val j z := by
        apply integral_congr_ae
        filter_upwards [heV] with z hz
        rw [← hz, mul_comm]
      _ = 0 := entire_compact_CR_test F hF θ.val θ.property.1 θ.property.2 j
  · intro hu
    have hlocal := locallyIntegrable_of_positive_compact_weight n w u hw (Lp.memLp u)
    obtain ⟨F, hF, he⟩ := configurationWeakCauchyRiemann_has_holomorphic_representative u hlocal
      (by
        intro θ hθ hc j
        have hzero := hu ⟨θ, hθ, hc⟩ j
        rw [positiveWeightCompactPairing_eq_integral] at hzero
        have hi : Integrable (fun z => CRCompactKernel θ j z * u z) volume := by
          simpa only [smul_eq_mul] using hlocal.integrable_smul_left_of_hasCompactSupport
            (CRCompactKernel_continuous θ hθ j) (CRCompactKernel_compact θ hc j)
        have hr := Complex.reCLM.integral_comp_comm hi
        have him := Complex.imCLM.integral_comp_comm hi
        rw [hzero] at hr him
        constructor
        · simpa [CRCompactKernel, Complex.mul_re, mul_comm] using hr
        · simpa [CRCompactKernel, Complex.mul_im, mul_comm] using him)
    exact ⟨F, hF, (withDensity_absolutelyContinuous volume _).ae_eq he.symm⟩

/-- The genuine entire-function subspace of arbitrary weighted L² is closed
whenever the measurable weight is bounded below by a positive constant on
compact sets. All local transport and joint Weyl reconstruction are proved. -/
theorem isClosed_positiveLocalWeightedEntireL2 (n : ℕ) (w : Configuration n → ℝ)
    (hwm : Measurable w)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z) :
    IsClosed (positiveLocalWeightedEntireL2 n w) := by
  have heq : positiveLocalWeightedEntireL2 n w =
      ⋂ θ : {θ : Configuration n → ℝ // ContDiff ℝ ∞ θ ∧ HasCompactSupport θ},
        ⋂ j : Fin n, {u | positiveWeightCompactPairing w hw (CRCompactKernel θ.val j)
          (CRCompactKernel_continuous θ.val θ.property.1 j)
          (CRCompactKernel_compact θ.val θ.property.2 j) u = 0} := by
    ext u
    simpa only [mem_iInter, Set.mem_ofPred_eq] using mem_positiveLocalWeightedEntireL2_iff_tests w
        hwm hw u
  rw [heq]
  apply isClosed_iInter
  intro θ
  apply isClosed_iInter
  intro j
  exact isClosed_eq (positiveWeightCompactPairing w hw (CRCompactKernel θ.val j)
    (CRCompactKernel_continuous θ.val θ.property.1 j)
    (CRCompactKernel_compact θ.val θ.property.2 j)).continuous continuous_const

end
end GinibrePoincare
