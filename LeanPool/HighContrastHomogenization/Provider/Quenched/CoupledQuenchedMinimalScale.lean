/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledPhysicalScale
public import LeanPool.HighContrastHomogenization.Provider.Quenched.InvariantFullMeasureEventAE

/-!
# High-contrast homogenization: Provider.Quenched.CoupledQuenchedMinimalScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coupled quenched minimal scale

The physical replay scale controls two different constants.  Its tail uses an
outer dimensional constant, while the block row retains the small threshold
selected before the law.  Keeping the latter coefficient avoids losing the
entry-scale smallness when the strict source tail and the mixing tail are
combined.
-/

namespace HCPolySupport.HighContrast.Quenched

open Filter MeasureTheory

noncomputable section

variable {d : ℕ}

/-- With fixed outer constants, the coupled witness gives a measurable
quenched scale with the strict two-part tail and, on one invariant full-measure
event, the small block row at entry together with its algebraic decay. -/
theorem exists_quenched_minimal_scale_of_coupled_witness
    {P : Measure (CoeffSpace d)} [NeZero d] [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hstationary : HCPoly.Frozen.IsStationaryLaw P)
    (hdagger : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    {rho cMix cd eta kappa delta Cann Cmix C cSrc : ℝ}
    {Abar : BlockMat d} {N : ℕ}
    (W : CoupledMixingScaleWitness P
      (fun m a => quenchedBlockRow rho Abar
        (max 1 (S a / (3 : ℝ) ^ N)) (physicalScaleCoefficient N a) m)
      cMix cd eta kappa delta)
    (hkappa : 0 < kappa) (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    (hN : (3 : ℝ) ^ N ≤ (2 + aspectRatio E * K) ^ Cann)
    (hW : W.normalization ≤ (2 + aspectRatio E * K) ^ Cmix)
    (habsorb : Cann + Cmix ≤ C) (hC : 1 < C)
    (hcMix : cMix ≤ C) (hcSrcOne : 1 < cSrc) (hcSrcC : cSrc < C) :
    ∃ (Lpoly : ℝ) (Ssrc X : CoeffSpace d → ℝ),
      Lpoly = coupledPhysicalLength N W ∧
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
      ∃ OmegaEnd : Set (CoeffSpace d),
        MeasurableSet OmegaEnd ∧
        P.real OmegaEnd = 1 ∧
        (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' OmegaEnd = OmegaEnd) ∧
        ∀ a ∈ OmegaEnd,
          HasAllLaterPhysicalBlockRow rho kappa delta Abar S X a := by
  obtain ⟨Lpoly, Ssrc, X, hLpolyEq, hSsrcEq, hXEq, hLpolyOne,
    hLpolyBound, hSsrcMeas, hSsrcOne, hXMeas, hXOne, htail, -⟩ :=
    exists_physical_scale_of_coupled_mixing_witness hdagger W hkappa
      hdelta hN hW habsorb hC hcMix hcSrcOne hcSrcC
  have hSsrcFun :
      Ssrc = fun a => max 1 (S a / (3 : ℝ) ^ N) :=
    funext hSsrcEq
  have hXFun :
      X = coupledPhysicalScale N W
        (fun a => max 1 (S a / (3 : ℝ) ^ N)) := by
    funext a
    rw [hXEq a, hLpolyEq, coupledPhysicalScale,
      coupledPhysicalLength, coupledNormalizedScale, hSsrcFun]
    ring
  have hrow :
      ∀ᵐ a ∂P,
        HasAllLaterPhysicalBlockRow rho kappa delta Abar S X a := by
    rw [hXFun]
    exact W.eventually_hasAllLaterPhysicalBlockRow hkappa hdelta.1 le_rfl
  obtain ⟨OmegaEnd, hOmegaEnd, hOmegaEndFull, hOmegaEndInvariant,
    hOmegaEndRow⟩ :=
    exists_integerTranslate_invariant_fullMeasure_of_ae hstationary hrow
  exact ⟨Lpoly, Ssrc, X, hLpolyEq, hSsrcEq, hXEq, hLpolyOne,
    hLpolyBound, hSsrcMeas, hSsrcOne, hXMeas, hXOne, htail,
    OmegaEnd, hOmegaEnd, hOmegaEndFull, hOmegaEndInvariant,
    hOmegaEndRow⟩

end

end HCPolySupport.HighContrast.Quenched
