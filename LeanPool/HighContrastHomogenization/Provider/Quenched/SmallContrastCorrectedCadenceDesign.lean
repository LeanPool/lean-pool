/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSplitSupplyAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueBasePar
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpLineAtJb
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastValueClauseAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCadenceProfile
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTwoOffsetEndpointBody
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRealClauses
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionStep
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowAtCenters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDropCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepHub
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAbsorptionChoice
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHvarFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLineProducer
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastValueClauseAtCarriers
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateMean
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSupplyPack
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSupplyPortsAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHoneAtIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceGroupNonneg
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFamilyLineClausesSrc
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedEndpointBody

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedCadenceDesign

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The hcore body from the one-step family, through the corrected descent

The cadence assembly re-aimed at the corrected three-channel descent
(the strengthened free-threshold estimate): the clauses are discharged exactly as
the cadence design discharges them, but the entry-slot source
is kept **explicit** through the `_src` line chain and priced by the
corrected three-channel hypothesis `hsrc3` — an absolutely decaying
channel at the anchor, the lag channel, and an absolutely decaying channel
at the generation — and the descent core is
`hcore_body_of_corrected_family`: the linear level schedule with law-free rate and
linear threshold.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The `hcore` body through the corrected descent.** -/
theorem hcore_body_of_corrected_design [NeZero d] (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {lAl : ℤ} {E : BlockMat d}
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl (canonicalMetric E)))
    (hfin : ∀ k : ℤ,
      HasFiniteAdaptedMean P (roundedGrid lAl (canonicalMetric E)) k)
    {N₀ : ℕ} (hlN : lAl ≤ (N₀ : ℤ))
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1)
    {Cpre eta : ℝ} {H : ℕ} (hCpre : 0 ≤ Cpre) (heta : 0 < eta)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hrecE : canonicalShear E = 0)
    {cIso : ℝ} (hcIso : 0 ≤ cIso) (hcsmall : cIso < 1)
    {cDeep : ℝ} (hcDeep0 : 0 ≤ cDeep)
    {S0 SStar0 K0 : ℕ → Mat d}
    (hS0 : ∀ n : ℕ, (S0 n).PosDef) (hStar0 : ∀ n : ℕ, (SStar0 n).PosDef)
    (hform : ∀ n : ℕ,
      toFullBlockMat (adaptedMean P (roundedGrid lAl (canonicalMetric E))
          ((N₀ : ℤ) + (n : ℤ))) =
        schurBlock (S0 n) (SStar0 n) (K0 n))
    (henvC : ∀ n : ℕ,
      BlockMatLoewnerLE
        (adaptedMean P (roundedGrid lAl (canonicalMetric E))
          ((N₀ : ℤ) + (n : ℤ)))
        (isotropyReference cIso E))
    (hcompC : ∀ n : ℕ,
      BlockMatLoewnerLE E
        (blockScale (isotropyKap2 cIso)
          (adaptedMean P (roundedGrid lAl (canonicalMetric E))
            ((N₀ : ℤ) + (n : ℤ)))))
    {Csub Msc delta0 conv deltaDrop : ℝ}
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta0pos : 0 < delta0)
    (hconv0 : 0 ≤ conv) (hdeltaDrop0 : 0 ≤ deltaDrop)
    (hbS : 0 ≤ blockSize E (isotropyReference cIso E))
    (hfloor : ∀ m : ℕ,
      hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ m ≤ delta0)
    (hdropchoice :
      dropConstantIsotropy (1 + cIso) E (isotropyReference cIso E) * delta0 ≤
        deltaDrop)
    {M₀ : ℝ} (hM₀ : metricFactorValue E (1 + cIso) (isotropyKap2 cIso) ≤ M₀)
    {K R : ℝ} {Gacc : ℕ} {sKw : ℤ} (hR : 1 ≤ R)
    {ns : ℕ} (hns : H + 1 ≤ ns)
    {A : ℝ}
    (hAdef : A = fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) g
      (rowSplitConstant cIso cDeep) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) E (isotropyReference cIso E))
      deltaDrop (slotCVsum d) (cVmConstant d conv))
    (hA1 : 1 ≤ A)
    {Ssrc0 Ssrc1 Ssrc2 b0 bA b2 : ℝ}
    (hSsrc0 : 1 ≤ Ssrc0) (hSsrc1 : 1 ≤ Ssrc1) (hSsrc2 : 1 ≤ Ssrc2)
    (hb0 : 0 < b0) (hbA : 0 < bA) (hb2 : 0 < b2)
    {cA : ℕ}
    (hgs3 : (128 * A ^ 2) ^ 3 * delta0 ≤ 1 / 3)
    (hcA24 : 24 * A ≤ (3 : ℝ) ^ (recursionAlpha g * (cA : ℝ)))
    (hfam : ∀ m : ℕ, ns ≤ m → ∀ n : ℕ, ns ≤ n →
      adaptedHattedContrast P (roundedGrid lAl (canonicalMetric E))
          ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
        4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
              (16 * (d : ℝ) *
                (adaptedHattedContrast P (roundedGrid lAl (canonicalMetric E))
                    ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                  adaptedHattedContrast P (roundedGrid lAl (canonicalMetric E))
                    ((N₀ : ℤ) + (n : ℤ)))) +
            rowValue2Isotropy d (rowSplitConstant cIso cDeep) (isotropyKap2 cIso)
              (hatExcessAt P (roundedGrid lAl (canonicalMetric E))
                ((N₀ : ℤ) + (n : ℤ))) +
            weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel R)
              (Response.maxGroupConstantAtLevel R)
              (Response.energyGoodConstantAtLevel R) P (canonicalMetric E)
              (Response.responseSkew (K0 n)) (isotropyReference cIso E)
              (loadScaleOfScalar (1 + cIso) (isotropyKap2 cIso))
              (canonicalMetric E) (contrastRho g) (n - ns)
              (R ^ 4 * badMomentMajorant K
                (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
              (R / 2) R ((N₀ : ℤ) + (n : ℤ)) lAl
              (fun j => slotFamilyValue d Csub Msc delta0
                (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
                  (min n m)) (n - min n m) j)
              (slotFamilyValue d Csub Msc delta0
                (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
                  (min n m)) (n - min n m) 0)
              (meanDrop2ValueIsotropy P lAl (1 + cIso) (canonicalMetric E) E
                (isotropyReference cIso E) ((N₀ : ℤ) + (n : ℤ)))
              (conv * slotFamilyValue d Csub Msc delta0
                (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
                  (min n m)) (n - min n m) 0)) +
          2 * ((3 * (d : ℝ) + 4) *
            hatExcessAt P (roundedGrid lAl (canonicalMetric E))
              ((N₀ : ℤ) + (n : ℤ)) ^ 2))
    (hsrc3 : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      3 * weakCoefficient d Cpre *
        weakSourceGroupSummed
          (absorbedNormalizer 16 16 (designNormalizer R M₀))
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho g)
          (slotVsumSharp d Csub Msc delta0 (n - min n m))
          (conv * slotSourceSeq d Csub Msc delta0 (n - min n m) 0)
          (Real.sqrt 2 *
              Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1) *
              Response.profileBadMajorantAt 4
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
                (R / 2) R +
            Real.sqrt 2 *
                (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
              Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1)) ^ 2 ≤
      Ssrc1 * (3 : ℝ) ^ (-(bA * (m : ℝ))) +
        Ssrc0 * (3 : ℝ) ^ (-(b0 * ((n - m : ℕ) : ℝ))) +
        Ssrc2 * (3 : ℝ) ^ (-(b2 * (n : ℝ))))
    {base Centry Cpref : ℝ} (hbase : 3 ≤ base) (hCpref : 0 ≤ Cpref)
    (hentry : (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base Centry)
    (hpref : 9 / 2 *
        ((1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
          (3 : ℝ) ^ (linRate A (recursionAlpha g) b0 bA b2 cA Ssrc0 *
            ((linR ns cA A (recursionAlpha g) b0 bA b2 Ssrc0 Ssrc1 Ssrc2
              delta0 0 : ℕ) : ℝ))) *
        (Real.rpow (3 : ℝ)
          (linRate A (recursionAlpha g) b0 bA b2 cA Ssrc0 / 2) + 1) ≤
      Real.rpow base Cpref)
    (htransfer : ∀ m : ℕ, 2 * N₀ ≤ m →
      annealedContrast P (m : ℤ) - 1 ≤
        (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast P (roundedGrid lAl (canonicalMetric E))
            (Prop42Scalar.correctedTiltScale N₀ m : ℤ) - 1)) +
          9 / 2 *
            ((1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
              (3 : ℝ) ^ (linRate A (recursionAlpha g) b0 bA b2 cA Ssrc0 *
                ((linR ns cA A (recursionAlpha g) b0 bA b2 Ssrc0 Ssrc1 Ssrc2
                  delta0 0 : ℕ) : ℝ))) *
            Real.rpow (3 : ℝ)
              (-((m - Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ))) :
    ∃ m₀ : ℕ,
      (3 : ℝ) ^ m₀ ≤ Real.rpow base (Centry +
          (1 + Cpref /
            (linRate A (recursionAlpha g) b0 bA b2 cA Ssrc0 / 2))) ∧
        ∀ j : ℕ, annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
          Real.rpow (3 : ℝ)
            (-(linRate A (recursionAlpha g) b0 bA b2 cA Ssrc0 / 2) *
              (j : ℝ)) := by
  classical
  have hdelta00 : 0 ≤ delta0 := hdelta0pos.le
  have hkap1 : (1 : ℝ) ≤ isotropyKap2 cIso := one_le_isotropyKap2 hcIso hcsmall
  have hkap0 : (0 : ℝ) ≤ isotropyKap2 cIso := by linarith only [hkap1]
  have hR0 : (0 : ℝ) ≤ R := by linarith only [hR]
  have hcF0 : (0 : ℝ) ≤ 1 + cIso := by linarith only [hcIso]
  have hrho1 : contrastRho g < 1 := contrastRho_lt_one hg1
  have hbmaj : ∀ n : ℕ, 0 ≤ R ^ 4 * badMomentMajorant K
      (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw) := by
    intro n
    have := badMomentMajorant_nonneg K
      (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw)
    positivity
  have hFnn : ∀ j : ℕ,
      0 ≤ hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ j :=
    hatExcess_nonneg hgrid hfin N₀
  have hFmono : ∀ p j : ℕ, p ≤ j →
      hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ j ≤
        hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ p :=
    fun _ _ hpj => hatExcess_antitone hstat hgrid hfin hlN hpj
  have hM00 : (0 : ℝ) ≤ M₀ := le_trans (metricFactorValue_nonneg _ _ _) hM₀
  have hMd0 : (0 : ℝ) ≤ designNormalizer R M₀ := designNormalizer_nonneg hR hM00
  have hMabs0 : (0 : ℝ) ≤ absorbedNormalizer 16 16 (designNormalizer R M₀) :=
    absorbedNormalizer_nonneg (by norm_num) (by norm_num) hMd0
  have hVnn : ∀ m n j : ℕ, 0 ≤ slotFamilyValue d Csub Msc delta0
      (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ (min n m))
      (n - min n m) j := by
    intro m n j
    exact slotFamilyValue_nonneg d hCsub hMsc hdelta00 (hFnn (min n m)) _ _
  have hrecfam : ∀ n : ℕ, ns ≤ n → ∀ m : ℕ, ns ≤ m → m ≤ n →
      hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ n ≤
        A * iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g))
            (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀) n +
          A * hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ m ^ 2 +
            3 * weakCoefficient d Cpre *
        weakSourceGroupSummed
          (absorbedNormalizer 16 16 (designNormalizer R M₀))
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho g)
          (slotVsumSharp d Csub Msc delta0 (n - min n m))
          (conv * slotSourceSeq d Csub Msc delta0 (n - min n m) 0)
          (Real.sqrt 2 *
              Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1) *
              Response.profileBadMajorantAt 4
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
                (R / 2) R +
            Real.sqrt 2 *
                (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
              Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1)) ^ 2 := by
    rw [hAdef]
    refine family_hrec_of_line_clauses_src (P := P)
      (q := roundedGrid lAl (canonicalMetric E))
      (N₀ := N₀) (ns := ns) (H := H) (Hw := fun k => k - ns)
      (V := fun m n j => slotFamilyValue d Csub Msc delta0
        (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ (min n m))
        (n - min n m) j)
      (V0 := fun m n => slotFamilyValue d Csub Msc delta0
        (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ (min n m))
        (n - min n m) 0)
      (Dr := fun n j =>
        meanDrop2ValueIsotropy P lAl (1 + cIso) (canonicalMetric E) E
          (isotropyReference cIso E) ((N₀ : ℤ) + (n : ℤ)) (min j n))
      (Vmean := fun m n => conv * slotFamilyValue d Csub Msc delta0
        (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ (min n m))
        (n - min n m) 0)
      (bmaj := fun n => R ^ 4 * badMomentMajorant K
        (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
      (beta := R / 2) (lev := R)
      (wv := fun m n =>
        weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel R)
          (Response.maxGroupConstantAtLevel R)
          (Response.energyGoodConstantAtLevel R) P (canonicalMetric E)
          (Response.responseSkew (K0 n)) (isotropyReference cIso E)
          (loadScaleOfScalar (1 + cIso) (isotropyKap2 cIso))
          (canonicalMetric E) (contrastRho g) (n - ns)
          (R ^ 4 * badMomentMajorant K
            (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
          (R / 2) R ((N₀ : ℤ) + (n : ℤ)) lAl
          (fun j => slotFamilyValue d Csub Msc delta0
            (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
              (min n m)) (n - min n m) j)
          (slotFamilyValue d Csub Msc delta0
            (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
              (min n m)) (n - min n m) 0)
          (meanDrop2ValueIsotropy P lAl (1 + cIso) (canonicalMetric E) E
            (isotropyReference cIso E) ((N₀ : ℤ) + (n : ℤ)))
          (conv * slotFamilyValue d Csub Msc delta0
            (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
              (min n m)) (n - min n m) 0))
      (vsum := fun m n => slotVsumSharp d Csub Msc delta0 (n - min n m))
      (vmsrc := fun m n => conv * slotSourceSeq d Csub Msc delta0
        (n - min n m) 0)
      (bsrc := fun n =>
        Real.sqrt 2 *
            Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1) *
            Response.profileBadMajorantAt 4
              (R ^ 4 * badMomentMajorant K
                (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
              (R / 2) R +
          Real.sqrt 2 *
              (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
            Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1))
      (by norm_num) (by norm_num) hMd0
      ⟨hg0, hg1, hCpre, heta, rowSplitConstant_nonneg hcIso hcDeep0, hkap0,
        hMabs0, dropConstantIsotropy_nonneg hcF0 hbS, hdeltaDrop0⟩
      hFnn hFmono hVnn (fun m n => hVnn m n 0)
      (fun n j => supply_hDrnn P lAl hcF0 (canonicalMetric E) hbS hstat
        hgrid hfin hlN n j)
      (fun m n => mul_nonneg hconv0 (hVnn m n 0))
      hbmaj (by linarith only [hR0]) (fun _ => le_rfl)
      (fun n hn => by omega)
      (fun n hn => by show n - ns + 1 ≤ n; omega)
      ?_ ?_ ?_ ?_ ?_ ?_
    · -- hmaj
      intro m hm n hn
      have hcongr := weakValueBoundSharpIsotropyAt_congr_Dr
        (Response.recentConstantAtLevel R) (Response.maxGroupConstantAtLevel R)
        (Response.energyGoodConstantAtLevel R) P (canonicalMetric E)
        (Response.responseSkew (K0 n)) (isotropyReference cIso E)
        (loadScaleOfScalar (1 + cIso) (isotropyKap2 cIso))
        (canonicalMetric E) (contrastRho g) (n - ns)
        (R ^ 4 * badMomentMajorant K
          (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
        (R / 2) R ((N₀ : ℤ) + (n : ℤ)) lAl
        (fun j => slotFamilyValue d Csub Msc delta0
          (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
            (min n m)) (n - min n m) j)
        (slotFamilyValue d Csub Msc delta0
          (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
            (min n m)) (n - min n m) 0)
        (Dr := fun j =>
          meanDrop2ValueIsotropy P lAl (1 + cIso) (canonicalMetric E) E
            (isotropyReference cIso E) ((N₀ : ℤ) + (n : ℤ)) (min j n))
        (Dr' := meanDrop2ValueIsotropy P lAl (1 + cIso) (canonicalMetric E) E
          (isotropyReference cIso E) ((N₀ : ℤ) + (n : ℤ)))
        (truncated_drop_agrees (by omega))
        (conv * slotFamilyValue d Csub Msc delta0
          (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
            (min n m)) (n - min n m) 0)
      refine le_trans (le_of_eq hcongr.symm) ?_
      exact hmaj_at_design_carriers_at_level (P := P) (E := E) (cIso := cIso)
        (rho := contrastRho g) (lAl := lAl) (N₀ := N₀) (S0 := S0)
        (SStar0 := SStar0) (K0 := K0)
        (V := fun n' j => slotFamilyValue d Csub Msc delta0
          (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
            (min n' m)) (n' - min n' m) j)
        (V0 := fun n' => slotFamilyValue d Csub Msc delta0
          (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
            (min n' m)) (n' - min n' m) 0)
        (Dr := fun n' j =>
          meanDrop2ValueIsotropy P lAl (1 + cIso) (canonicalMetric E) E
            (isotropyReference cIso E) ((N₀ : ℤ) + (n' : ℤ)) (min j n'))
        (Vmean := fun n' => conv * slotFamilyValue d Csub Msc delta0
          (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀
            (min n' m)) (n' - min n' m) 0)
        (bmaj := fun n' => R ^ 4 * badMomentMajorant K
          (((N₀ : ℤ) + (n' : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
        (beta := R / 2) (lev := R) (Hw := fun k => k - ns) (M := M₀)
        hE hEpd hsharp hrecE hcIso hcsmall hrho1 hS0 hStar0 hform henvC
        hcompC (fun n' j => hVnn m n' j) (fun n' => hVnn m n' 0)
        (fun n' j => supply_hDrnn P lAl hcF0 (canonicalMetric E) hbS hstat
          hgrid hfin hlN n' j)
        (fun n' => mul_nonneg hconv0 (hVnn m n' 0))
        hbmaj (by linarith only [hR0]) hR hM₀ n
    · -- hone
      intro m hm n hn
      exact hone_of_one_step_family_isotropy (hfam m hm) n hn
    · -- hVsum
      intro m hm n hn
      exact supply_hVsum hd hCsub hMsc hdelta00 hgrid hfin N₀
        (fun k => min k m) (fun k => k - min k m) (fun k => k - ns) n
    · -- hVmeanle
      intro m hm n hn
      exact supply_hVmeanle hconv0
    · -- hDrdelta
      intro n hn j hj
      exact supply_hDrdelta P lAl (1 + cIso) (canonicalMetric E) E
        (isotropyReference cIso E) hFnn hfloor
        (dropConstantIsotropy_nonneg hcF0 hbS) hdropchoice n j
    · -- hDrdrop
      intro n hn j hj
      rw [Finset.mem_range] at hj
      have hj' : j < n - ns + 1 := hj
      exact supply_hDrdrop P lAl (1 + cIso) (canonicalMetric E) E
        (isotropyReference cIso E) le_rfl hstat hgrid hfin hlN n j
        (by omega)
  have hfam' : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ n ≤
        A * iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g))
            (hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀) n +
          A * hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ m ^ 2 +
            3 * weakCoefficient d Cpre *
        weakSourceGroupSummed
          (absorbedNormalizer 16 16 (designNormalizer R M₀))
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho g)
          (slotVsumSharp d Csub Msc delta0 (n - min n m))
          (conv * slotSourceSeq d Csub Msc delta0 (n - min n m) 0)
          (Real.sqrt 2 *
              Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1) *
              Response.profileBadMajorantAt 4
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
                (R / 2) R +
            Real.sqrt 2 *
                (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
              Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1)) ^ 2 :=
    fun n m hm hmn => hrecfam n (le_trans hm hmn) m hm hmn
  exact hcore_body_of_corrected_family
    (src := fun n m => 3 * weakCoefficient d Cpre *
        weakSourceGroupSummed
          (absorbedNormalizer 16 16 (designNormalizer R M₀))
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho g)
          (slotVsumSharp d Csub Msc delta0 (n - min n m))
          (conv * slotSourceSeq d Csub Msc delta0 (n - min n m) 0)
          (Real.sqrt 2 *
              Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1) *
              Response.profileBadMajorantAt 4
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
                (R / 2) R +
            Real.sqrt 2 *
                (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
              Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1)) ^ 2)
    hA1 (recursionAlpha_pos hg1) hcA24 hdelta0pos hgs3 hSsrc0 hSsrc1 hSsrc2
    hb0 hbA hb2 hFnn hFmono hfloor hfam' hsrc3 hbase hCpref hentry hpref
    htransfer

end

end HCPolySupport.HighContrast.Quenched
