/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.PolynomialEntry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedContrastComparison
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledQuenchedMinimalScale
public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedMainBridge
public import LeanPool.HighContrastHomogenization.Provider.Quenched.ThresholdCalibration

/-!
# High-contrast homogenization: Provider.Quenched.AnnealedToQuenchedTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coupled annealed-to-quenched step

The polynomial entry theorem fixes the first small annealed scale.  The
annealed endpoint transports it through the rebased law, and one coupled
quenched witness then supplies both the optimal marginal tail and the
all-later bad-event certificate.  This module composes those three outputs
without separating the selected random scale from its certificate.
-/

namespace HCPolySupport.HighContrast.Quenched

open _root_.Filter MeasureTheory

noncomputable section

/-- The polynomial entry theorem, the annealed contrast endpoint, the triadic
rebase, and one coupled quenched witness produce the physical quenched minimal
scale.  The row coefficient is the small threshold `delta`, rather than the
larger constant used to combine the two tails. -/
theorem exists_quenched_minimal_scale_of_coupled_providers
    (d : ℕ) (hd : 2 ≤ d)
    (hcontrastCore : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
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
                  (3 : ℝ) ^ (-alpha * (j : ℝ)))
    (hRebase :
      ∀ {cSc g cStar Centry : ℝ},
        cStar ∈ Set.Ioo 0 cSc →
        g ∈ Set.Ico (0 : ℝ) 1 → 0 < Centry →
        ∃ Crebase : ℝ, 0 < Crebase ∧ Centry ≤ Crebase ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d)
            (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
            (∃ mEnt : ℕ,
              (mEnt : ℤ) ≤
                ⌈Centry * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
              annealedContrast P (mEnt : ℤ) - 1 ≤ cStar ∧
              (3 : ℝ) ^ mEnt ≤
                3 * (2 + aspectRatio E * K) ^ Centry) →
            ∃ (nBase : ℕ) (Pbase : Measure (CoeffSpace d))
              (gBase : ℝ) (Ebase : BlockMat d) (PsiBase : ℝ → ℝ)
              (Kbase : ℝ) (Sbase : CoeffSpace d → ℝ),
              gBase = (1 + g) / 2 ∧
              IsProbabilityMeasure Pbase ∧
              HCPoly.Frozen.IsStationaryLaw Pbase ∧
              HCPoly.Frozen.IsUnitRangeLaw Pbase ∧
              HCPoly.Frozen.CoarseEllipticityDagger
                Pbase gBase Ebase PsiBase Kbase Sbase ∧
              annealedContrast Pbase 0 - 1 ≤ cStar ∧
              blockContrast Ebase ≤ 1 + cSc ∧
              (∀ j : ℕ,
                annealedContrast Pbase (j : ℤ) =
                  annealedContrast P ((nBase + j : ℕ) : ℤ)) ∧
              (∀ j : ℕ,
                annealedBlock Pbase (centeredCube d (j : ℤ)) =
                  annealedBlock P
                    (centeredCube d ((nBase + j : ℕ) : ℤ))) ∧
              (3 : ℝ) ^ nBase ≤
                (2 + aspectRatio E * K) ^ Crebase ∧
              2 + aspectRatio Ebase * Kbase ≤
                (2 + aspectRatio E * K) ^ Crebase)
    (hCoupled :
      ∃ cd : ℝ, 0 < cd ∧
        ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
          ∀ alpha : ℝ, 0 < alpha →
          ∃ Cmix cMix kappa delta : ℝ,
            0 < Cmix ∧ 0 < cMix ∧ 0 < kappa ∧
            delta ∈ Set.Ioo (0 : ℝ) 1 ∧
            ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d)
              (Psi : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
              (Abar : BlockMat d) (Nann : ℕ),
              IsProbabilityMeasure P →
              HCPoly.Frozen.IsStationaryLaw P →
              HCPoly.Frozen.IsUnitRangeLaw P →
              HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
              IsSymmetricBlockMat Abar →
              Book.Ch02.BlockPosDef Abar →
              (∀ j : ℕ,
                annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤
                  (3 : ℝ) ^ (-alpha * (j : ℝ))) →
              (∀ j : ℕ,
                BlockMatLoewnerLE Abar
                    (annealedBlock P
                      (centeredCube d ((Nann + j : ℕ) : ℤ))) ∧
                  BlockMatLoewnerLE
                    (annealedBlock P
                      (centeredCube d ((Nann + j : ℕ) : ℤ)))
                    (blockScale
                      (1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))) Abar)) →
              ∃ W : CoupledMixingScaleWitness P
                (fun m a => quenched_block_row ((1 + 3 * g) / 4) Abar
                  (max 1 (S a / (3 : ℝ) ^ Nann))
                  (physical_scale_coeff Nann a) m)
                cMix cd ((d : ℝ) - 2 * g) kappa delta,
                W.normalization ≤ (2 + aspectRatio E * K) ^ Cmix) :
    ∃ cd : ℝ, 0 < cd ∧
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
            ∃ (Abar : BlockMat d) (Nann : ℕ) (alpha Lpoly : ℝ)
              (Ssrc X : CoeffSpace d → ℝ),
              0 < alpha ∧
              IsSymmetricBlockMat Abar ∧
              Book.Ch02.BlockPosDef Abar ∧
              (∀ m : ℕ,
                BlockMatLoewnerLE Abar
                  (annealedBlock P (centeredCube d (m : ℤ)))) ∧
              (∀ m : ℕ,
                BlockMatLoewnerLE
                  (blockSharp (annealedBlock P (centeredCube d (m : ℤ))))
                  Abar) ∧
              (∀ j : ℕ,
                annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤
                  (3 : ℝ) ^ (-alpha * (j : ℝ))) ∧
              (∀ a, Ssrc a = max 1 (S a / (3 : ℝ) ^ Nann)) ∧
              1 ≤ Lpoly ∧
              Lpoly ≤ (2 + aspectRatio E * K) ^ C ∧
              Measurable Ssrc ∧
              (∀ a, 1 ≤ Ssrc a) ∧
              Measurable X ∧
              (∀ a, 1 ≤ X a) ∧
              (∀ a, S a ≤ X a) ∧
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
  have : NeZero d := ⟨by omega⟩
  obtain ⟨cd, hcd, hCoupled⟩ := hCoupled
  refine ⟨cd, hcd, ?_⟩
  intro g hg
  obtain ⟨cSc, hcSc, alpha, Cdelay, halpha, hCdelay,
    hcontrastCore⟩ := hcontrastCore g hg
  obtain ⟨deltaEntry, cEnd, hdeltaEntry, hcEnd, hcalibration⟩ :=
    exists_threshold_calibration_below cSc hcSc
  obtain ⟨cStar, hcStar, hEntry⟩ :=
    HCPoly.Frozen.polynomial_entry_random_source d hd
      cSc deltaEntry cEnd hcSc hdeltaEntry hcEnd hcalibration
  obtain ⟨Centry, hCentry, hEntry⟩ := hEntry g hg
  have hfactor : 1 < (1 + deltaEntry) ^ 2 := by
    nlinarith only [hdeltaEntry.1]
  have hEndOne : 0 < 1 + cEnd := by linarith only [hcEnd]
  have hstrict := mul_lt_mul_of_pos_right hfactor hEndOne
  have hcEndSc : cEnd < cSc := by
    nlinarith only [hstrict, hcalibration]
  have hcStarSc : cStar ∈ Set.Ioo 0 cSc :=
    ⟨hcStar.1, (hcStar.2.trans (min_le_right _ _)).trans_lt hcEndSc⟩
  obtain ⟨Crebase, hCrebase, -, hRebase⟩ :=
    hRebase hcStarSc hg hCentry
  let Cann : ℝ := Crebase * (1 + Cdelay)
  obtain ⟨Cmix, cMix, kappa, delta, -, -, hkappa, hdelta, hCoupled⟩ :=
    hCoupled g hg alpha halpha
  obtain ⟨C, cSrc, hC, hcSrc, hcMixC, hcSrcC, -, habsorb⟩ :=
    exists_coupled_physical_outer_constants cMix Crebase Cann Cmix
  refine ⟨C, cSrc, kappa, delta, zero_lt_one.trans hC,
    zero_lt_one.trans hcSrc, hkappa, hdelta, ?_⟩
  intro P E Psi K S hP hstationary hunit hdagger
  let : IsProbabilityMeasure P := hP
  obtain ⟨nBase, Pbase, gBase, Ebase, PsiBase, Kbase, Sbase,
    hgBase, hPbase, hstationaryBase, hunitBase, hdaggerBase,
    hentryBase, hcontrastBase, hcontrastCovariance, hblockCovariance,
    hnBase, hbaseCost⟩ :=
    hRebase P E Psi K S hP hstationary hunit hdagger
      (hEntry P E Psi K S hP hstationary hunit hdagger)
  have hbase : (1 : ℝ) ≤ 2 + aspectRatio E * K := by
    have hAspect : 1 ≤ aspectRatio E :=
      one_le_aspectRatio_of_coarseEllipticityDagger hdagger
    have hK : 1 ≤ K := hdagger.one_lt_growthWitness.le
    have hproduct : 1 ≤ aspectRatio E * K :=
      one_le_mul_of_one_le_of_one_le hAspect hK
    exact one_le_two.trans (le_add_of_nonneg_right (zero_le_one.trans hproduct))
  obtain ⟨m0, hdelay, hcontrastBaseDecay⟩ :=
    hcontrastCore cStar gBase Pbase Ebase PsiBase Kbase Sbase hcStarSc
      hgBase hPbase hstationaryBase hunitBase hdaggerBase hentryBase
      hcontrastBase
  obtain ⟨Abar, Nann, hAbar, hAbarPos, hNann,
    hcontrast, hblocks, hAbarEq⟩ :=
    exists_annealed_endpoint_of_rebased_contrast_decay hstationaryBase
      hdaggerBase hcontrastCovariance hblockCovariance hbase hnBase
      hbaseCost hCdelay le_rfl hdelay hcontrastBaseDecay
  obtain ⟨hlowerLimit, hupperLimit⟩ :=
    annealedLimitBlock_sandwich_of_covariance hstationary hdagger
      hstationaryBase hdaggerBase hblockCovariance
  have hlower : ∀ m : ℕ,
      BlockMatLoewnerLE Abar
        (annealedBlock P (centeredCube d (m : ℤ))) := by
    simpa only [hAbarEq] using hlowerLimit
  have hupper : ∀ m : ℕ,
      BlockMatLoewnerLE
        (blockSharp (annealedBlock P (centeredCube d (m : ℤ)))) Abar := by
    simpa only [hAbarEq] using hupperLimit
  obtain ⟨W, hW⟩ :=
    hCoupled P E Psi K S Abar Nann hP hstationary hunit hdagger
      hAbar hAbarPos hcontrast hblocks
  obtain ⟨Lpoly, Ssrc, X, hLpolyEq, hSsrc, hXEq, hLpoly, hLpolyBound,
    hSsrcMeasurable, hSsrcOne, hXMeasurable, hXOne, htail,
    OmegaEnd, hOmegaEnd, hOmegaEndFull, hOmegaEndInvariant,
    hOmegaEndRow⟩ :=
    exists_quenched_minimal_scale_of_coupled_witness hstationary hdagger W
      hkappa hdelta hNann hW habsorb hC hcMixC hcSrc hcSrcC
  have hburn : ∀ a, S a ≤ X a := by
    intro a
    have hpowPos : 0 < (3 : ℝ) ^ Nann := pow_pos (by norm_num) _
    have hsource : S a / (3 : ℝ) ^ Nann ≤ Ssrc a := by
      rw [hSsrc a]
      exact le_max_right _ _
    have hscaled : S a ≤ (3 : ℝ) ^ Nann * Ssrc a := by
      simpa only [mul_comm] using (div_le_iff₀ hpowPos).mp hsource
    have hnormOne : 1 ≤ W.normalization := W.one_le_normalization
    have hsrcMax : Ssrc a ≤ max 1 (max (W.scale a) (Ssrc a)) :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hsrcNonneg : 0 ≤ Ssrc a := zero_le_one.trans (hSsrcOne a)
    have hnormSrc : Ssrc a ≤ W.normalization * Ssrc a := by
      calc
        Ssrc a = 1 * Ssrc a := by ring
        _ ≤ W.normalization * Ssrc a :=
          mul_le_mul_of_nonneg_right hnormOne hsrcNonneg
    calc
      S a ≤ (3 : ℝ) ^ Nann * Ssrc a := hscaled
      _ ≤ (3 : ℝ) ^ Nann * (W.normalization * Ssrc a) :=
        mul_le_mul_of_nonneg_left hnormSrc (by positivity)
      _ ≤ ((3 : ℝ) ^ Nann * W.normalization) *
          max 1 (max (W.scale a) (Ssrc a)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hsrcMax
          (mul_nonneg (by positivity) (zero_le_one.trans hnormOne))
      _ = X a := by
        rw [hXEq a, hLpolyEq]
        rfl
  exact ⟨Abar, Nann, alpha, Lpoly, Ssrc, X, halpha, hAbar, hAbarPos,
    hlower, hupper, hcontrast, hSsrc,
    hLpoly, hLpolyBound, hSsrcMeasurable, hSsrcOne,
    hXMeasurable, hXOne, hburn, htail, OmegaEnd, hOmegaEnd,
    hOmegaEndFull, hOmegaEndInvariant, hOmegaEndRow⟩

end

end HCPolySupport.HighContrast.Quenched
