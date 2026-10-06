/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedMainBridge
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedToQuenchedTransfer
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop211Rebase
public import LeanPool.HighContrastHomogenization.Provider.Quenched.EndpointRelativeEngineData

/-!
# High-contrast homogenization: Provider.Quenched.QuenchedConvergenceDischarge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

/-- Quenched convergence from the annealed contrast-decay endpoint. -/
theorem quenched_convergence_of_contrast_core
    (d : ℕ) (hd : 2 ≤ d)
    (hcontrastCore : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∃ cSc : ℝ, 0 < cSc ∧
        ∃ alpha Cdelay : ℝ, 0 < alpha ∧ 0 ≤ Cdelay ∧
          ∀ (cStar gBase : ℝ) (Pbase : Measure (CoeffSpace d))
            (Ebase : BlockMat d) (PsiBase : ℝ → ℝ) (Kbase : ℝ)
            (Sbase : CoeffSpace d → ℝ),
            cStar ∈ Set.Ioc 0 cSc →
            gBase = (1 + g) / 2 →
            IsProbabilityMeasure Pbase →
            HCPoly.Frozen.IsStationaryLaw Pbase →
            HCPoly.Frozen.IsUnitRangeLaw Pbase →
            HCPoly.Frozen.CoarseEllipticityDagger
              Pbase gBase Ebase PsiBase Kbase Sbase →
            annealedContrast Pbase 0 - 1 ≤ cStar →
            blockContrast Ebase ≤ 1 + cSc →
            ∃ m0 : ℕ,
              (3 : ℝ) ^ m0 ≤ (2 + aspectRatio Ebase * Kbase) ^ Cdelay ∧
              ∀ j : ℕ,
                annealedContrast Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤
                  (3 : ℝ) ^ (-alpha * (j : ℝ))) :
    ∃ cd : ℝ, 0 < cd ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C κ cSrc : ℝ, 1 < C ∧ 0 < κ ∧ 0 < cSrc ∧
          ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
            ∃ Cδ : ℝ, 1 ≤ Cδ ∧
              ∀ (P : Measure (CoeffSpace d))
                (E : BlockMat d) (Psi : ℝ → ℝ) (K : ℝ)
                (S : CoeffSpace d → ℝ),
                IsProbabilityMeasure P →
                HCPoly.Frozen.IsStationaryLaw P →
                HCPoly.Frozen.IsUnitRangeLaw P →
                HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
                ∃ (Abar : BlockMat d) (Lpoly : ℝ)
                  (X : CoeffSpace d → ℝ),
                  IsSymmetricBlockMat Abar ∧
                  Book.Ch02.BlockPosDef Abar ∧
                  (∀ m : ℕ,
                    BlockMatLoewnerLE Abar
                      (annealedBlock P (centeredCube d (m : ℤ)))) ∧
                  (∀ m : ℕ,
                    BlockMatLoewnerLE
                      (blockSharp (annealedBlock P (centeredCube d (m : ℤ))))
                      Abar) ∧
                  1 ≤ Lpoly ∧
                  Lpoly ≤ (2 + aspectRatio E * K) ^ Cδ ∧
                  Measurable X ∧
                  (∀ a, 1 ≤ X a) ∧
                  (∀ t : ℝ, 1 ≤ t →
                    P.real {a | C * Lpoly * t ≤ X a} ≤
                      Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) +
                        (Psi (cSrc * t))⁻¹) ∧
                  ∃ OmegaEnd : Set (CoeffSpace d),
                    MeasurableSet OmegaEnd ∧
                    P.real OmegaEnd = 1 ∧
                    (∀ z : Fin d → ℤ,
                      translateCoeff z ⁻¹' OmegaEnd = OmegaEnd) ∧
                    ∀ a ∈ OmegaEnd, ∀ m : ℤ, X a ≤ (3 : ℝ) ^ m →
                      (if S a ≤ (3 : ℝ) ^ m then
                          ∑' n : ℕ,
                            (3 : ℝ) ^ (-((1 + 3 * g) / 4) * (n : ℝ)) *
                              sSup {r : ℝ | ∃ w : Fin d → ℤ,
                                standardCellCenter (m - (n : ℤ)) w ∈
                                  centeredCube d m ∧
                                r = blockExcess
                                  (coarseBlock
                                    (standardCell d (m - (n : ℤ)) w) a)
                                  Abar}
                        else 0) ≤ δ * ((3 : ℝ) ^ m / X a) ^ (-κ) := by
  have hcontrastCoreStrict : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∃ cSc : ℝ, 0 < cSc ∧
        ∃ alpha Cdelay : ℝ, 0 < alpha ∧ 0 ≤ Cdelay ∧
          ∀ (cStar gBase : ℝ) (Pbase : Measure (CoeffSpace d))
            (Ebase : BlockMat d) (PsiBase : ℝ → ℝ) (Kbase : ℝ)
            (Sbase : CoeffSpace d → ℝ),
            cStar ∈ Set.Ioo 0 cSc →
            gBase = (1 + g) / 2 →
            IsProbabilityMeasure Pbase →
            HCPoly.Frozen.IsStationaryLaw Pbase →
            HCPoly.Frozen.IsUnitRangeLaw Pbase →
            HCPoly.Frozen.CoarseEllipticityDagger
              Pbase gBase Ebase PsiBase Kbase Sbase →
            annealedContrast Pbase 0 - 1 ≤ cStar →
            blockContrast Ebase ≤ 1 + cSc →
            ∃ m0 : ℕ,
              (3 : ℝ) ^ m0 ≤ (2 + aspectRatio Ebase * Kbase) ^ Cdelay ∧
              ∀ j : ℕ,
                annealedContrast Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤
                  (3 : ℝ) ^ (-alpha * (j : ℝ)) := by
    intro g hg
    obtain ⟨cSc, hcSc, alpha, Cdelay, halpha, hCdelay, hcore⟩ :=
      hcontrastCore g hg
    refine ⟨cSc, hcSc, alpha, Cdelay, halpha, hCdelay, ?_⟩
    intro cStar gBase Pbase Ebase PsiBase Kbase Sbase hcStar
    exact hcore cStar gBase Pbase Ebase PsiBase Kbase Sbase
      ⟨hcStar.1, hcStar.2.le⟩
  have hseam := exists_quenched_minimal_scale_of_coupled_providers d hd
    hcontrastCoreStrict (exists_prop211_rebase_provider d hd)
    (exists_coupledWitnessAssembly d hd
      (exists_coupledWitnessEngineData_of_endpoint d hd))
  have hbridge : ∃ cd : ℝ, 0 < cd ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C cSrc kappa delta : ℝ,
          0 < C ∧ 0 < cSrc ∧ 0 < kappa ∧
          delta ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d)
            (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
            ∃ (Abar : BlockMat d) (Nann : ℕ) (Lpoly : ℝ)
              (Ssrc X : CoeffSpace d → ℝ),
              IsSymmetricBlockMat Abar ∧
              Book.Ch02.BlockPosDef Abar ∧
              (∀ m : ℕ,
                BlockMatLoewnerLE Abar
                  (annealedBlock P (centeredCube d (m : ℤ)))) ∧
              (∀ m : ℕ,
                BlockMatLoewnerLE
                  (blockSharp (annealedBlock P (centeredCube d (m : ℤ))))
                  Abar) ∧
              (∀ a, Ssrc a = max 1 (S a / (3 : ℝ) ^ Nann)) ∧
              1 ≤ Lpoly ∧
              Lpoly ≤ (2 + aspectRatio E * K) ^ C ∧
              Measurable Ssrc ∧
              (∀ a, 1 ≤ Ssrc a) ∧
              Measurable X ∧
              (∀ a, 1 ≤ X a) ∧
              (∀ t : ℝ, 1 ≤ t →
                P.real {a | C * Lpoly * t ≤ X a} ≤
                  Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) +
                    (Psi (cSrc * t))⁻¹) ∧
              ∃ OmegaEnd : Set (CoeffSpace d),
                MeasurableSet OmegaEnd ∧
                P.real OmegaEnd = 1 ∧
                (∀ z : Fin d → ℤ,
                  translateCoeff z ⁻¹' OmegaEnd = OmegaEnd) ∧
                ∀ a ∈ OmegaEnd,
                  HasAllLaterPhysicalBlockRow ((1 + 3 * g) / 4)
                    kappa delta Abar S X a := by
    obtain ⟨cd, hcd, hseam⟩ := hseam
    refine ⟨cd, hcd, ?_⟩
    intro g hg
    obtain ⟨C, cSrc, kappa, delta, hC, hcSrc, hkappa, hdelta, hseam⟩ :=
      hseam g hg
    refine ⟨C, cSrc, kappa, delta, hC, hcSrc, hkappa, hdelta, ?_⟩
    intro P E Psi K S hP hstat hunit hdag
    obtain ⟨Abar, Nann, alpha, Lpoly, Ssrc, X, _halpha, hsymm, hpos,
      hlower, hupper, _hcontrast, hSsrc, hLpoly, hcost, hmeasSsrc,
      honeSsrc, hmeasX, honeX, _hSX, htail, hOmega⟩ :=
      hseam P E Psi K S hP hstat hunit hdag
    exact ⟨Abar, Nann, Lpoly, Ssrc, X, hsymm, hpos, hlower, hupper,
      hSsrc, hLpoly, hcost, hmeasSsrc, honeSsrc, hmeasX, honeX, htail,
      hOmega⟩
  have hresult := quenched_convergence_of_coupled_providers d hd hbridge
  exact hresult

end


end HCPolySupport.HighContrast.Quenched
