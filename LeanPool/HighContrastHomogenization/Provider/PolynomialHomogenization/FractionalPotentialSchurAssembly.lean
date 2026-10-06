/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalGagliardoSquareFunction

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalPotentialSchurAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Assembly of a pointwise fractional potential estimate with Schur
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Boundary-weighted energy relative to an arbitrary constant vector. -/
@[expose]
def euclideanBoundaryWeightedEnergyAround (U : Set (Vec d)) (p : ℝ)
    (F : Vec d → Vec d) (m : Vec d) : ℝ≥0∞ :=
  eVolumeAverage U fun x => euclideanBoundaryWeight U p x *
    ENNReal.ofReal (vecNormSq (F x - m))

/-- A Schur-ready pointwise potential representation implies the normalized
boundary-weighted estimate relative to the same reference vector. -/
theorem exists_euclideanBoundaryWeightedEnergyAround_le_of_pointwisePotential
    (hd : 1 ≤ d) {rho Rad s a : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad) (hs : 0 < s)
    (hsa : s < a) (hsa1 : s + a < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad → ∀ (F : Vec d → Vec d), Measurable F →
          ∀ (m : Vec d) (P : ℝ≥0∞), P ≠ ⊤ →
            (∀ᵐ x ∂volume.restrict U,
              euclideanBoundaryWeight U (2 * s) x *
                  ENNReal.ofReal (vecNormSq (F x - m)) ≤
                P * (∫⁻ y in U, fractionalBoundarySchurKernel U s x y *
                  fractionalGagliardoAmplitude U s F y ∂volume) ^ (2 : ℝ)) →
            euclideanBoundaryWeightedEnergyAround U (2 * s) F m ≤
              P * C * fracSeminormSq U s F := by
  obtain ⟨C, hCtop, hschur⟩ :=
    exists_lintegral_fractionalBoundarySchurKernel_rpow_two_le
      hd hrho hRad hs hsa hsa1
  refine ⟨C, hCtop, ?_⟩
  intro U hU hsand F hF m P hPtop hpoint
  have hUne : U.Nonempty := by
    obtain ⟨_hrho, _hRad, c, hinner, _houter⟩ := hsand
    exact ⟨c, hinner (center_mem_euclideanBallAt c hrho)⟩
  have hUpos : 0 < volume U :=
    volume_pos_of_isOpenBoundedConvexDomain hU hUne
  have hUtop : volume U ≠ ⊤ := hU.volume_lt_top.ne
  have hampMeas : Measurable (fractionalGagliardoAmplitude U s F) :=
    measurable_fractionalGagliardoAmplitude hF
  have hraw :
      (∫⁻ x in U, euclideanBoundaryWeight U (2 * s) x *
          ENNReal.ofReal (vecNormSq (F x - m)) ∂volume) ≤
        P * (C * ∫⁻ y in U,
          fractionalGagliardoAmplitude U s F y ^ (2 : ℝ) ∂volume) := by
    calc
      (∫⁻ x in U, euclideanBoundaryWeight U (2 * s) x *
          ENNReal.ofReal (vecNormSq (F x - m)) ∂volume) ≤
          ∫⁻ x in U, P *
            (∫⁻ y in U, fractionalBoundarySchurKernel U s x y *
              fractionalGagliardoAmplitude U s F y ∂volume) ^ (2 : ℝ) ∂volume :=
        lintegral_mono_ae hpoint
      _ = P * (∫⁻ x in U,
          (∫⁻ y in U, fractionalBoundarySchurKernel U s x y *
            fractionalGagliardoAmplitude U s F y ∂volume) ^ (2 : ℝ) ∂volume) :=
        lintegral_const_mul' P _ hPtop
      _ ≤ P * (C * ∫⁻ y in U,
          fractionalGagliardoAmplitude U s F y ^ (2 : ℝ) ∂volume) :=
        mul_le_mul_right (hschur U hU hsand _ hampMeas) P
  rw [setLIntegral_fractionalGagliardoAmplitude_rpow_two_eq
    hUpos hUtop] at hraw
  unfold euclideanBoundaryWeightedEnergyAround eVolumeAverage
  calc
    (∫⁻ x in U, euclideanBoundaryWeight U (2 * s) x *
        ENNReal.ofReal (vecNormSq (F x - m)) ∂volume) / volume U ≤
        (P * (C * (volume U * fracSeminormSq U s F))) / volume U :=
      ENNReal.div_le_div_right hraw _
    _ = P * C * fracSeminormSq U s F := by
      rw [div_eq_mul_inv]
      calc
        P * (C * (volume U * fracSeminormSq U s F)) * (volume U)⁻¹ =
            P * C * ((volume U)⁻¹ * volume U) *
              fracSeminormSq U s F := by ac_rfl
        _ = P * C * fracSeminormSq U s F := by
          rw [ENNReal.inv_mul_cancel hUpos.ne' hUtop]
          simp only [mul_one]

end

end HighContrast
end HCPolySupport
