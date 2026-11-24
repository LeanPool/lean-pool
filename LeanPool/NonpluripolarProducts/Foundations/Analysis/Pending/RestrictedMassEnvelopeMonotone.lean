/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalPotentials

/-!
# The admissible mass envelope is nondecreasing in the error

Source: Copy-4, `eq:def-restricted-volume` (`transcendental-nakamaye-copy4-20260911`);
CT22, Section 2; blueprint `ana:restricted-volume-monotone`.

An `ε`-admissible presentation `θ + ddᶜu` is `ε'`-admissible for `ε ≤ ε'`
(`AdmissibleRestrictedCurrentPresentation.raiseError`, same representative and
potential), and on every regular patch, off the poles,
`(T + ε'ω)|_V = (T + εω)|_V + (ε' - ε) ω|_V` with both summands semipositive
`(1,1)`-forms.  The top-power density is monotone on such sums, so the
absolutely continuous restricted top masses, hence their suprema, increase.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Pullback of a `(1,1)`-form by a complex linear map is `(1,1)`. -/
theorem isOneOne_compContinuousLinearMap {k : ℕ}
    {A : CoordinateRealTwoForm n} (hA : IsOneOne A) (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    IsOneOne (A.compContinuousLinearMap L) := by
  intro a b
  have h := hA (L a) (L b)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  convert h using 2 <;> ext i <;> fin_cases i <;> simp [hL]

/-- Pullback of a semipositive form by a complex linear map is semipositive. -/
theorem coefficientSemipositive_compContinuousLinearMap {k : ℕ}
    {A : CoordinateRealTwoForm n} (hA : CoefficientSemipositive A)
    (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    CoefficientSemipositive (A.compContinuousLinearMap L) := by
  intro v
  have h := hA (L v)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  convert h using 2
  ext i
  fin_cases i <;> simp [hL]

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M}

theorem kahler_smul_isSemipositive (omega : KahlerBackground n M) {c : ℝ} (hc : 0 ≤ c) :
    (c • omega.form).val.IsSemipositive := by
  intro e z hz v
  rw [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rcases eq_or_ne v 0 with rfl | hv
  · rw [smul_zero, ((omega.form).val.coeff e z).map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1)
      (by simp) (by decide), mul_zero]
  · exact mul_nonneg hc ((omega.isKahler.1 e z hz).2 v hv).le

/-- An `ε`-admissible presentation is `ε'`-admissible for `ε ≤ ε'`. -/
def raiseError {ε ε' : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) (h : (ε : ℝ) ≤ ε') :
    AdmissibleRestrictedCurrentPresentation omega alpha V ε' where
  representative := p.representative
  represents := p.represents
  potential := p.potential
  potential_psh := by
    have hsum := LocalPotentials.isThetaPshPotential_add_of_semipositive p.potential_psh
      (kahler_smul_isSemipositive omega (sub_nonneg.mpr h))
    have hform : p.representative + (ε : ℝ) • omega.form + ((ε' : ℝ) - ε) • omega.form =
        p.representative + (ε' : ℝ) • omega.form := by
      rw [add_assoc, ← add_smul, add_sub_cancel]
    rwa [hform] at hsum
  smoothAnalyticSingularities := p.smoothAnalyticSingularities
  not_carrier_subset_poleSet := p.not_carrier_subset_poleSet

theorem coordinateCurrentForm_raiseError {ε ε' : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) (h : (ε : ℝ) ≤ ε')
    (e : ComplexChart n M) (z : ComplexModel n) :
    coordinateCurrentForm (raiseError p h) e z =
      coordinateCurrentForm p e z + ((ε' : ℝ) - ε) • omega.form.val.coeff e z := by
  simp only [coordinateCurrentForm, perturbedRepresentative,
    raiseError, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul]
  ext v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  ring

/-- **The admissible mass envelope is nondecreasing in the error**, given
monotonicity of the top-power
density on semipositive `(1,1)`-forms (`hmono`). -/
theorem restrictedMassEnvelope_mono_of
    (hmono : ∀ {k : ℕ} (A B : CoordinateRealTwoForm k), IsOneOne A →
      CoefficientSemipositive A → IsOneOne B → CoefficientSemipositive B →
      actualTopPowerDensity A ≤ actualTopPowerDensity (A + B))
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    {ε ε' : PositiveError} (h : (ε : ℝ) ≤ ε') :
    restrictedMassEnvelope (acTopMassData omega) alpha V ε ≤
      restrictedMassEnvelope (acTopMassData omega) alpha V ε' := by
  refine iSup_le fun p => le_trans ?_ (le_iSup _ (raiseError p h))
  change acTopMass p ≤ acTopMass (raiseError p h)
  refine iSup_le fun F => le_trans ?_ (le_iSup _ F)
  refine Finset.sum_le_sum fun i _ => lintegral_mono_ae ?_
  refine (ae_restrict_iff' (F.measurableSet_piece i)).mpr (Eventually.of_forall ?_)
  intro w hw
  apply ENNReal.ofReal_le_ofReal
  set P := F.patch i
  set e := complexChartAt (n := n) P.center
  set L := fderiv ℝ P.coordinateParametrization w
  have hdom : w ∈ P.parameterDomain := F.piece_subset i hw
  have hz : P.coordinateParametrization w ∈ e.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hdom)
  have hpole : e.val.symm (P.coordinateParametrization w) ∉ poleSet p.potential := by
    intro hmem
    exact Set.disjoint_left.mp (F.image_disjoint_avoid i) ⟨w, hw, rfl⟩ hmem
  have hL := RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hdom
  obtain ⟨hA1, hA2⟩ := coordinateCurrentForm_isOneOne_and_semipositive p e hz hpole
  have hω := omega.isKahler.1 e _ hz
  have hc : (0 : ℝ) ≤ (ε' : ℝ) - ε := sub_nonneg.mpr h
  have hB1 : IsOneOne (((ε' : ℝ) - ε) • omega.form.val.coeff e
      (P.coordinateParametrization w)) := by
    intro a b
    simp only [ContinuousAlternatingMap.smul_apply, hω.1 a b]
  have hB2 : CoefficientSemipositive (((ε' : ℝ) - ε) • omega.form.val.coeff e
      (P.coordinateParametrization w)) := by
    intro v
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rcases eq_or_ne v 0 with rfl | hv
    · rw [smul_zero, (omega.form.val.coeff e (P.coordinateParametrization w)).map_eq_zero_of_eq
        ![0, 0] (i := 0) (j := 1) (by simp) (by decide), mul_zero]
    · exact mul_nonneg hc (hω.2 v hv).le
  have key := hmono _ _ (isOneOne_compContinuousLinearMap hA1 L hL)
    (coefficientSemipositive_compContinuousLinearMap hA2 L hL)
    (isOneOne_compContinuousLinearMap hB1 L hL)
    (coefficientSemipositive_compContinuousLinearMap hB2 L hL)
  simp only [patchDensity]
  rw [coordinateCurrentForm_raiseError p h]
  convert key using 2
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.add_apply, e, L]

end

end SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone
