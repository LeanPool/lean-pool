/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledPhysicalBlockDecay
public import LeanPool.HighContrastHomogenization.Provider.Quenched.RestoredSource
public import LeanPool.HighContrastHomogenization.Provider.Quenched.ScaledMaximumStrictSource
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio

/-!
# High-contrast homogenization: Provider.Quenched.CoupledPhysicalScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical scale from a coupled mixing witness

This module restores the microscopic source, combines it with the selected
mixing scale, and proves the strict two-part tail and physical all-later row
estimate.  The mixing tail and bad-event certificate are consumed from one
coupled witness.
-/

namespace HCPolySupport.HighContrast.Quenched

open Filter MeasureTheory IndependentSums

noncomputable section

variable {d : ℕ}

/-- Deterministic outer constants can simultaneously absorb the rebase cost,
the annealed and mixing length exponents, and the two strict tail thresholds. -/
theorem exists_coupled_physical_outer_constants
    (cMix Crebase Cann Cmix : ℝ) :
    ∃ C cSrc : ℝ,
      1 < C ∧ 1 < cSrc ∧ cMix ≤ C ∧ cSrc < C ∧
        Crebase ≤ C ∧ Cann + Cmix ≤ C := by
  let C : ℝ := max 2 (max cMix (max Crebase (Cann + Cmix))) + 1
  refine ⟨C, 2, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · have htwo : (2 : ℝ) ≤ max 2 (max cMix (max Crebase (Cann + Cmix))) :=
      le_max_left _ _
    dsimp only [C]
    linarith only [htwo]
  · have hmix : cMix ≤ max cMix (max Crebase (Cann + Cmix)) :=
      le_max_left _ _
    have houter : max cMix (max Crebase (Cann + Cmix)) ≤
        max 2 (max cMix (max Crebase (Cann + Cmix))) := le_max_right _ _
    dsimp only [C]
    exact (hmix.trans houter).trans (le_add_of_nonneg_right zero_le_one)
  · have htwo : (2 : ℝ) ≤ max 2 (max cMix (max Crebase (Cann + Cmix))) :=
      le_max_left _ _
    dsimp only [C]
    linarith only [htwo]
  · have hrebase : Crebase ≤ max Crebase (Cann + Cmix) := le_max_left _ _
    have hmiddle : max Crebase (Cann + Cmix) ≤
        max cMix (max Crebase (Cann + Cmix)) := le_max_right _ _
    have houter : max cMix (max Crebase (Cann + Cmix)) ≤
        max 2 (max cMix (max Crebase (Cann + Cmix))) := le_max_right _ _
    dsimp only [C]
    exact (hrebase.trans (hmiddle.trans houter)).trans
      (le_add_of_nonneg_right zero_le_one)
  · have hsum : Cann + Cmix ≤ max Crebase (Cann + Cmix) := le_max_right _ _
    have hmiddle : max Crebase (Cann + Cmix) ≤
        max cMix (max Crebase (Cann + Cmix)) := le_max_right _ _
    have houter : max cMix (max Crebase (Cann + Cmix)) ≤
        max 2 (max cMix (max Crebase (Cann + Cmix))) := le_max_right _ _
    dsimp only [C]
    exact (hsum.trans (hmiddle.trans houter)).trans
      (le_add_of_nonneg_right zero_le_one)

/-- Restore the microscopic source and assemble the physical replay length,
random scale, strict two-part tail, and all-later block-row estimate. -/
theorem exists_physical_scale_of_coupled_mixing_witness
    {P : Measure (CoeffSpace d)} [NeZero d] [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdagger : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    {rho cMix cd eta kappa delta Cann Cmix C cSrc : ℝ}
    {Abar : BlockMat d} {N : ℕ}
    (W : CoupledMixingScaleWitness P
      (fun m a => quenched_block_row rho Abar
        (max 1 (S a / (3 : ℝ) ^ N)) (physical_scale_coeff N a) m)
      cMix cd eta kappa delta)
    (hkappa : 0 < kappa) (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    (hN : (3 : ℝ) ^ N ≤ (2 + aspectRatio E * K) ^ Cann)
    (hW : W.normalization ≤ (2 + aspectRatio E * K) ^ Cmix)
    (habsorb : Cann + Cmix ≤ C)
    (hC : 1 < C) (hcMix : cMix ≤ C)
    (hcSrcOne : 1 < cSrc) (hcSrcC : cSrc < C) :
    ∃ (Lpoly : ℝ) (Ssrc X : CoeffSpace d → ℝ),
      Lpoly = coupled_physical_length N W ∧
      (∀ a, Ssrc a = max 1 (S a / (3 : ℝ) ^ N)) ∧
      (∀ a, X a = Lpoly * max 1 (max (W.scale a) (Ssrc a))) ∧
      1 ≤ Lpoly ∧
      Lpoly ≤ (2 + aspectRatio E * K) ^ C ∧
      Measurable Ssrc ∧
      (∀ a, 1 ≤ Ssrc a) ∧
      Measurable X ∧
      (∀ a, 1 ≤ X a) ∧
      (∀ t : ℝ, 1 ≤ t →
        P.real {a | C * Lpoly * t ≤ X a} ≤
          Real.exp (-cd * t ^ eta) + (Psi (cSrc * t))⁻¹) ∧
      ∀ᵐ a ∂P,
        HasAllLaterPhysicalBlockRow rho kappa C Abar S X a := by
  obtain ⟨Ssrc, hSsrcMeas, hSsrcOne, hSsrcEq, hSsrcTail⟩ :=
    exists_restored_source_scale hdagger N
  let Lpoly : ℝ := coupled_physical_length N W
  let X : CoeffSpace d → ℝ := fun a =>
    Lpoly * max 1 (max (W.scale a) (Ssrc a))
  have hLpolyOne : 1 ≤ Lpoly := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      W.one_le_normalization
  have hLpolyPos : 0 < Lpoly := zero_lt_one.trans_le hLpolyOne
  have hPi : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdagger
  have hK : 1 ≤ K := hdagger.one_lt_growthWitness.le
  have hPiK : 1 ≤ aspectRatio E * K :=
    one_le_mul_of_one_le_of_one_le hPi hK
  have hbaseOne : 1 ≤ 2 + aspectRatio E * K := by
    exact one_le_two.trans (le_add_of_nonneg_right (zero_le_one.trans hPiK))
  have hbasePos : 0 < 2 + aspectRatio E * K := zero_lt_one.trans_le hbaseOne
  have hLpolyBound : Lpoly ≤ (2 + aspectRatio E * K) ^ C := by
    have hproduct :
        (3 : ℝ) ^ N * W.normalization ≤
          (2 + aspectRatio E * K) ^ Cann *
            (2 + aspectRatio E * K) ^ Cmix :=
      mul_le_mul hN hW
        (le_trans zero_le_one W.one_le_normalization)
        (Real.rpow_nonneg hbasePos.le _)
    calc
      Lpoly ≤ (2 + aspectRatio E * K) ^ Cann *
          (2 + aspectRatio E * K) ^ Cmix := by
        simpa only [Lpoly, coupled_physical_length] using hproduct
      _ = (2 + aspectRatio E * K) ^ (Cann + Cmix) := by
        rw [Real.rpow_add hbasePos]
      _ ≤ (2 + aspectRatio E * K) ^ C :=
        Real.rpow_le_rpow_of_exponent_le hbaseOne habsorb
  have hXMeas : Measurable X := by
    simpa only [X] using
      measurable_scaled_max_one W.measurable_scale hSsrcMeas Lpoly
  have hXOne : ∀ a, 1 ≤ X a := by
    simpa only [X] using one_le_scaled_max_one (Rmix := W.scale)
      (Ssrc := Ssrc) hLpolyOne
  have htail :
      ∀ t : ℝ, 1 ≤ t →
        P.real {a | C * Lpoly * t ≤ X a} ≤
          Real.exp (-cd * t ^ eta) + (Psi (cSrc * t))⁻¹ := by
    intro t ht
    have hcSrcT : 1 ≤ cSrc * t :=
      one_le_mul_of_one_le_of_one_le hcSrcOne.le ht
    simpa only [X] using
      measureReal_scaled_max_one_tail_le_of_source_lt
        (P := P) (Rmix := W.scale) (Ssrc := Ssrc)
        (L := Lpoly) (C := C) (cMix := cMix) (cSrc := cSrc)
        (cd := cd) (η := eta) (t := t) (Ψ := Psi)
        hLpolyPos ht hC hcMix hcSrcC (W.scale_tail t ht)
        (hSsrcTail (cSrc * t) hcSrcT)
  have hdeltaC : delta ≤ C :=
    hdelta.2.le.trans hC.le
  have hrowAE := W.eventually_hasAllLaterPhysicalBlockRow
    hkappa hdelta.1 hdeltaC
  have hSsrcFun : Ssrc = fun a => max 1 (S a / (3 : ℝ) ^ N) :=
    funext hSsrcEq
  have hXEq : X = coupled_physical_scale N W Ssrc := by
    funext a
    simp only [X, Lpoly, coupled_physical_length, coupled_physical_scale,
      coupled_normalized_scale]
    ring
  have hrowAE' :
      ∀ᵐ a ∂P,
        HasAllLaterPhysicalBlockRow rho kappa C Abar S X a := by
    rw [hSsrcFun] at hXEq
    simpa only [hXEq] using hrowAE
  refine ⟨Lpoly, Ssrc, X, rfl, hSsrcEq, fun _ => rfl, hLpolyOne,
    hLpolyBound, hSsrcMeas, hSsrcOne, hXMeas, hXOne, htail, hrowAE'⟩

end

end HCPolySupport.HighContrast.Quenched
