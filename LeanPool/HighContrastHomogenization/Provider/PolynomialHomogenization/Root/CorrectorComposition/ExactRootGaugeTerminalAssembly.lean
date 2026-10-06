/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootGaugeTerminalPieces
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.IdentityGaugeTerminalCube
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.SlopeBoundedRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.EventRetainingCertificate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CertificatePositiveDefiniteness

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootGaugeTerminalAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `ExactRootGaugeTerminal`, assembled

This module inhabits the large-scale C¹ slope approximation's ball terminal at the event-retaining
certificate, modulo a
single named analytic hypothesis, `ExactRootBallTriangle` — the weighted-energy
triangle inequality on the exact-root pullback ball.  Everything else is
discharged:

* the row's certificate is read off the root certificate at the **consumer's
  own** corrector smallness (`exists_rowCertificate_of_rootGoodScaleAt`), so the
  five-ceiling reconciliation gains no sixth constraint; the scale the rebasing
  costs is absorbed by the terminal's own free delay `L`;
* the terminal's carrier is the row's carrier
  (`rootJointCarrier_eq_rowCarrier`), and the gauge-pullback clause is then
  definitional (`pushforwardMarker_gaugePullback`);
* the far branch is the cube row packaged between two volume-ratio comparisons
  (`farBranch_estimate`);
* the near band is the ball-to-ball comparison, the triangle, and the
  corrector's own energy against the solution's (`nearBranch_estimate`);
* when the whole radius range lies in the near band — which happens exactly when
  `108 √d · rStart > R`, and then no triadic cube of the row is available at all
  — the terminal closes at `eRef := 0` with **no** triangle inequality, because
  the corrector at slope `0` is trivial.

`ExactRootBallTriangle` is Minkowski for `‖s^{1/2} ·‖_{L̲²(V)}`, stated for the
exact pair of square-integrable fields the terminal compares.  The repository
proves it only for `H1Function`s on triadic cubes
(`weightedGradNorm_sub_le_add_sub_h1`), never on a general set; the
domain-generic ingredients that would discharge it
(`sqrt_normalizedLocalSymmetricEnergy_add_le`,
`ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq`, both stated for
an arbitrary `U : Set (Vec d)`) need one `IsEllipticFieldOn` witness and two
`MemVectorL2` witnesses on the ball that this module did not build.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- **The one analytic ingredient not discharged here**: the
weighted-energy triangle inequality on the exact-root pullback ball, for the
**two fields the terminal actually compares** — the exact-root pullback of an
`MemH1a` solution gradient, and an affine-plus-corrector field of a joint local
equation.  Both are square-integrable on the ball, which is exactly what makes
the statement true; it is Minkowski for `‖s^{1/2} ·‖_{L̲²(V)}`.

**The membership premises are deliberately part of the statement.**  The
unrestricted triangle inequality over arbitrary fields is *false*: `lintegral`
is the lower integral, so for a Bernstein set `S` (inner measure `0` on both
`S` and `Sᶜ`) the pair `F = 1_S • v`, `G = -1_{Sᶜ} • v` has
`weightedGradNorm _ _ F = weightedGradNorm _ _ G = 0` while `F - G = v`.
Stating the hypothesis over arbitrary fields would therefore make every
theorem depending on it vacuous. -/
@[expose]
def ExactRootBallTriangle (d : ℕ) [NeZero d] : Prop :=
  ∀ (abar : Mat d) (hS : (symmPart abar).PosDef) (a : CoeffSpace d) (R : ℝ)
    (u : Vec d → ℝ) (Du : Vec d → Vec d),
    MemH1a (⇑a.1 : CoeffField d) (ellipsoid abar R) u Du →
    ∀ (aId : Book.Ch03.CoeffFamily d)
      (Phi : Vec d → NormalizedLocalH1Carrier d),
      IsFiniteAffineCorrectionJointLocalEquation aId Phi →
      ∀ e : Vec d,
        weightedGradNorm
            (affineCoefficient (Selection.normalizedRoot (symmPart abar))
              ((Matrix.isUnit_iff_isUnit_det _).mp
                (normalizedRoot_posDef_of_posDef hS).isUnit)
              (⇑(normalizedCenteredCoeff a abar hS).1))
            (closedNormBall d R)
            (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
                (Du (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) -
              (e + (Phi e).globalGradientRepresentative y)) ≤
          weightedGradNorm
              (affineCoefficient (Selection.normalizedRoot (symmPart abar))
                ((Matrix.isUnit_iff_isUnit_det _).mp
                  (normalizedRoot_posDef_of_posDef hS).isUnit)
                (⇑(normalizedCenteredCoeff a abar hS).1))
              (closedNormBall d R)
              (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
                (Du (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) +
            weightedGradNorm
              (affineCoefficient (Selection.normalizedRoot (symmPart abar))
                ((Matrix.isUnit_iff_isUnit_det _).mp
                  (normalizedRoot_posDef_of_posDef hS).isUnit)
                (⇑(normalizedCenteredCoeff a abar hS).1))
              (closedNormBall d R)
              (fun y ↦ e + (Phi e).globalGradientRepresentative y)

variable {d : ℕ}

/-- The degenerate-case constant is below the near-band constant. -/
theorem degenerate_le_nearBranchConstant [NeZero d] {B Aslope : ℝ}
    (hB : 0 < B) (hAslope : 0 < Aslope) :
    ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (108 * Real.sqrt d) ≤
      nearBranchConstant d B Aslope := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have h0 : (0 : ℝ) ≤ ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have h1 : (0 : ℝ) ≤ ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hBA : (0 : ℝ) ≤ B * Aslope := (mul_pos hB hAslope).le
  have hX : (0 : ℝ) ≤ ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
      ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg h1 hBA) h2
  have h108 : (0 : ℝ) ≤ 108 * Real.sqrt d := by positivity
  have hextra : (0 : ℝ) ≤ ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
      (((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
        ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * (108 * Real.sqrt d) :=
    mul_nonneg (mul_nonneg h0 hX) h108
  unfold nearBranchConstant
  have heq : ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
        (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
          ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * (108 * Real.sqrt d) =
      ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (108 * Real.sqrt d) +
        ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
          (((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
            ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * (108 * Real.sqrt d) := by
    ring
  rw [heq]
  linarith only [hextra]

/-! ## The terminal -/

/-- **The exact-root gauge ball terminal at the event-retaining certificate**, modulo
the weighted-energy triangle inequality on the ball. -/
theorem exactRootGaugeTerminal_onReconciled_of_ballTriangle (d : ℕ) [NeZero d]
    (htri : ExactRootBallTriangle d) (cStar : ℝ → ℝ)
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) (hcStar : 0 < cStar g)
    {κc : ℝ} (hκc : 0 < κc) {eta : ℝ} (heta : eta ∈ Set.Ioo (0 : ℝ) 1) :
    ExactRootGaugeTerminal d (reconciledRootGoodScaleOn d cStar g κc)
      (Root.RootPushCorrectorFamilyPredicate d) eta := by
  classical
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hsq1 : (1 : ℝ) ≤ Real.sqrt d := by
    have hdnat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    have hdge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdnat
    have hsqle := Real.sqrt_le_sqrt hdge1
    rwa [Real.sqrt_one] at hsqle
  have hϑhalf : (1 : ℝ) / 2 ≤ max eta (1 / 2 : ℝ) := le_max_right _ _
  have hϑ1 : max eta (1 / 2 : ℝ) < 1 := max_lt heta.2 (by norm_num)
  have hϑ0 : (0 : ℝ) ≤ max eta (1 / 2 : ℝ) := le_trans (by norm_num) hϑhalf
  obtain ⟨A₀, Aslope, cMax, hA₀, hAslope, hcMax, hrowAll⟩ :=
    Root.exists_printOrderUndelayedExactGaugeRowWithSlope d g
      (max eta (1 / 2 : ℝ)) hg hϑhalf hϑ1
  obtain ⟨Benergy, cB, hBenergy, hcB, hbound⟩ :=
    Root.exists_jointCorrectorRepresentativeEnergyBound d
      (printCertificateOrder g)
      (Root.printCertificateOrder_pos_of_mem_Ico hg)
      (Root.printCertificateOrder_lt_half_of_mem_Ico hg)
  have hc'pos : 0 < min (cStar g) (min cMax (2 * cB)) :=
    lt_min hcStar (lt_min hcMax.1 (by linarith only [hcB.1]))
  have hc'cStar : min (cStar g) (min cMax (2 * cB)) ≤ cStar g := min_le_left _ _
  have hc'cMax : min (cStar g) (min cMax (2 * cB)) ≤ cMax :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hc'2cB : min (cStar g) (min cMax (2 * cB)) ≤ 2 * cB :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hhalfcB : min (cStar g) (min cMax (2 * cB)) / 2 ≤ cB := by
    linarith only [hc'2cB]
  have hKratio : (1 : ℝ) ≤ cStar g / min (cStar g) (min cMax (2 * cB)) :=
    (one_le_div hc'pos).2 hc'cStar
  have hK1 : (1 : ℝ) ≤
      (cStar g / min (cStar g) (min cMax (2 * cB))) ^ κc⁻¹ := by
    have h := Real.rpow_le_rpow zero_le_one hKratio (inv_nonneg.2 hκc.le)
    rwa [Real.one_rpow] at h
  refine ⟨Quenched.triadicCeilingIndex
      ((cStar g / min (cStar g) (min cMax (2 * cB))) ^ κc⁻¹),
    max (farBranchConstant d * A₀) (nearBranchConstant d Benergy Aslope),
    lt_max_of_lt_left (mul_pos farBranchConstant_pos hA₀), ?_⟩
  intro abar hS Phi gradPhi hmarker a x hx hgood
  obtain ⟨hS2, rfl, rfl⟩ := hmarker
  have hSeq : hS2 = hS := Subsingleton.elim _ _
  subst hSeq
  -- the stationary corrector family clause event at this sample
  have hcore : a ∈ Root.pushforwardCore d abar hS2 :=
    mem_invariantTranslationCore_iff.mpr
      (rootNormalizedSupply_of_rootGoodScaleOn d (c := cStar g)
        (kappaRate := κc) hg abar hS2 a x hgood)
  have hev : Root.RootCorrectorEvent d (Root.normalizedSample abar hS2 a) :=
    Root.pushforwardEvent_of_mem_core_self hcore
  -- the row's certificate, at this module's own smallness
  obtain ⟨xRow, hxRow1, hxRowLe, hcertRow⟩ :=
    exists_rowCertificate_of_rootGoodScaleAt d hκc hc'pos hc'cStar hgood.1
  obtain ⟨hS3, hI, aIdentity, PhiRow, hCauchyId, hIdentity, hPhiRow,
      hgoodTail, hrow⟩ :=
    hrowAll (min (cStar g) (min cMax (2 * cB))) κc hc'pos hc'cMax abar a xRow
      hcertRow
  have hS3eq : hS3 = hS2 := Subsingleton.elim _ _
  subst hS3eq
  have hcarrier := rootJointCarrier_eq_rowCarrier d
    (canonicalIdentityGeometry d g hg) hS3 hev hI aIdentity hIdentity
    hCauchyId PhiRow hPhiRow
  have hcoeff := exactRootCoeff_ae_identityGauge
    (canonicalIdentityGeometry d g hg) hS3 hI aIdentity hIdentity
  refine ⟨PhiRow, fun e ↦ pushforwardMarker_gaugePullback d hS3 hcore PhiRow hcarrier e,
    ?_⟩
  intro R u Du hu hweak
  dsimp only
  intro hstartR
  -- names
  set rS : ℝ := (3 : ℝ) ^ (Quenched.triadicCeilingIndex x +
    Quenched.triadicCeilingIndex
      ((cStar g / min (cStar g) (min cMax (2 * cB))) ^ κc⁻¹)) with hrSdef
  have hrS1 : (1 : ℝ) ≤ rS := one_le_pow₀ (by norm_num)
  have hrSpos : (0 : ℝ) < rS := lt_of_lt_of_le zero_lt_one hrS1
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le hrSpos hstartR
  have hR1 : (1 : ℝ) ≤ R := le_trans hrS1 hstartR
  set Fld : Vec d → Vec d := fun y ↦
    matVecMul (Selection.normalizedRoot (symmPart abar))
      (Du (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) with hFlddef
  -- the row's start index is below the canonical outer generation of `rS`
  have hxRowrS : xRow ≤ rS := by
    have h1 := Quenched.le_pow_triadicCeilingIndex hK1
    have h2 := Quenched.le_pow_triadicCeilingIndex hx
    have hstep : xRow ≤ (3 : ℝ) ^ Quenched.triadicCeilingIndex
        ((cStar g / min (cStar g) (min cMax (2 * cB))) ^ κc⁻¹) *
        (3 : ℝ) ^ Quenched.triadicCeilingIndex x :=
      hxRowLe.trans (mul_le_mul h1 h2 (le_trans zero_le_one hx) (by positivity))
    rw [hrSdef, pow_add]
    calc xRow ≤ (3 : ℝ) ^ Quenched.triadicCeilingIndex
          ((cStar g / min (cStar g) (min cMax (2 * cB))) ^ κc⁻¹) *
          (3 : ℝ) ^ Quenched.triadicCeilingIndex x := hstep
      _ = (3 : ℝ) ^ Quenched.triadicCeilingIndex x *
          (3 : ℝ) ^ Quenched.triadicCeilingIndex
            ((cStar g / min (cStar g) (min cMax (2 * cB))) ^ κc⁻¹) := by ring
  by_cases hcase : 108 * (Real.sqrt d * rS) ≤ R
  · -- the mixed case: the far branch is available
    have hquot : (0 : ℝ) < R / Real.sqrt d := by positivity
    have hmRle : Real.sqrt d * (3 : ℝ) ^ innerTriadicGeneration
        (R / Real.sqrt d) hquot ≤ R := by
      have h := innerTriadicGeneration_scale_le hquot
      rw [le_div_iff₀ hsq] at h
      linarith only [h]
    have hmRlt : R < 3 * (Real.sqrt d * (3 : ℝ) ^ innerTriadicGeneration
        (R / Real.sqrt d) hquot) := by
      have h := lt_three_mul_innerTriadicGeneration_scale hquot
      rw [div_lt_iff₀ hsq] at h
      linarith only [h]
    have hmRbound : R ≤ (3 : ℝ) ^ innerTriadicGeneration
        (R / Real.sqrt d) hquot * (3 * Real.sqrt d) := by
      linarith only [hmRlt]
    obtain ⟨-, -, hgap⟩ := farBranch_bounds (d := d) (rStart := rS) (r := rS)
      (R := R) hrSpos le_rfl hmRbound hcase hcase
    have hnZ0 : 0 ≤ outerTriadicGeneration (2 * (2 * rS)) (by positivity) :=
      outerTriadicGeneration_nonneg_of_one_le (by positivity)
        (by linarith only [hrS1])
    have hmZ0 : 0 ≤ innerTriadicGeneration (R / Real.sqrt d) hquot := by
      omega
    set nN : ℕ := (outerTriadicGeneration (2 * (2 * rS))
      (by positivity)).toNat with hnNdef
    set mN : ℕ := (innerTriadicGeneration (R / Real.sqrt d) hquot).toNat
      with hmNdef
    have hnNcast : (nN : ℤ) = outerTriadicGeneration (2 * (2 * rS))
        (by positivity) := Int.toNat_of_nonneg hnZ0
    have hmNcast : (mN : ℤ) = innerTriadicGeneration (R / Real.sqrt d) hquot :=
      Int.toNat_of_nonneg hmZ0
    have hnm : nN + 2 ≤ mN := by omega
    have hmRleN : Real.sqrt d * (3 : ℝ) ^ mN ≤ R := by
      have hz : (3 : ℝ) ^ mN = (3 : ℝ) ^ ((mN : ℤ)) := by
        rw [zpow_natCast]
      rw [hz, hmNcast]
      exact hmRle
    have hmRltN : R < 3 * (Real.sqrt d * (3 : ℝ) ^ mN) := by
      have hz : (3 : ℝ) ^ mN = (3 : ℝ) ^ ((mN : ℤ)) := by
        rw [zpow_natCast]
      rw [hz, hmNcast]
      exact hmRlt
    -- the terminal cube solution
    have hmcube : matImage (Selection.normalizedRoot (symmPart abar))
        (openCubeSet (originCube d (mN : ℤ))) ⊆ ellipsoid abar R :=
      matImage_subset_ellipsoid_of_subset_closedNormBall hS3
        (openCubeSet_originCube_subset_closedNormBall mN hmRleN)
    obtain ⟨w, hw⟩ := exists_identityGaugeTerminalCubeSolution d
      (canonicalIdentityGeometry d g hg) hS3 hI aIdentity hIdentity
      (mN : ℤ) hmcube u Du hu hweak
    have hwF : w.toH1.grad = Fld := hw.trans hFlddef.symm
    -- the row's start
    have hstartN : (Quenched.triadicCeilingIndex xRow : ℤ) ≤ (nN : ℤ) := by
      have hrSn : rS ≤ (3 : ℝ) ^ nN := by
        have houter := le_outerTriadicGeneration_scale
          (by positivity : (0 : ℝ) < 2 * (2 * rS))
        have hz : (3 : ℝ) ^ nN = (3 : ℝ) ^ ((nN : ℤ)) := by rw [zpow_natCast]
        rw [hz, hnNcast]
        linarith only [houter, hrSpos]
      have := Quenched.triadicCeilingIndex_le_of_le_pow hxRow1
        (le_trans hxRowrS hrSn)
      exact_mod_cast this
    obtain ⟨e, heNorm, hrowq⟩ := hrow nN mN hstartN hnm w
    refine ⟨e, ?_⟩
    intro r hr
    have hrS_le_r : rS ≤ r := hr.1
    have hrR : r ≤ R := hr.2
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le hrSpos hrS_le_r
    have hslopeE : ENNReal.ofReal (euclideanNorm e) ≤ ENNReal.ofReal Aslope *
        weightedGradNorm
          (aIdentity.coeffOn (originCube d (mN : ℤ))).toCoeffField
          (openCubeSet (originCube d (mN : ℤ))) Fld := by
      rw [← hwF, weightedGradNorm_eq_ofReal_h1EnergyNormOnCube,
        ← ENNReal.ofReal_mul hAslope.le]
      exact ENNReal.ofReal_le_ofReal heNorm
    by_cases hthr : 108 * (Real.sqrt d * r) ≤ R
    · -- far branch
      obtain ⟨-, hqm, -⟩ := farBranch_bounds (d := d) (rStart := rS) (r := r)
        (R := R) hrSpos hrS_le_r hmRbound hthr hcase
      obtain ⟨hnq, -, -⟩ := farBranch_bounds (d := d) (rStart := rS) (r := r)
        (R := R) hrSpos hrS_le_r hmRbound hthr hcase
      have hqZ0 : 0 ≤ outerTriadicGeneration (2 * (2 * r)) (by positivity) := by
        omega
      set qN : ℕ := (outerTriadicGeneration (2 * (2 * r))
        (by positivity)).toNat with hqNdef
      have hqNcast : (qN : ℤ) = outerTriadicGeneration (2 * (2 * r))
          (by positivity) := Int.toNat_of_nonneg hqZ0
      have hqmN : qN ≤ mN := by omega
      have hnqN : nN ≤ qN := by omega
      have hq3 : (3 : ℝ) ^ qN ≤ 12 * r := by
        have hlt := outerTriadicGeneration_scale_lt_three_mul
          (by positivity : (0 : ℝ) < 2 * (2 * r))
        have hz : (3 : ℝ) ^ qN = (3 : ℝ) ^ ((qN : ℤ)) := by rw [zpow_natCast]
        rw [hz, hqNcast]
        linarith only [hlt]
      have hcubeq : closedNormBall d r ⊆
          openCubeSet (originCube d (qN : ℤ)) := by
        rw [hqNcast]
        exact closedNormBall_subset_outerCube hrpos
      have hratioq : volume (openCubeSet (originCube d (qN : ℤ))) /
          volume (closedNormBall d r) ≤
          ENNReal.ofReal ((6 * Real.sqrt d) ^ d) := by
        rw [hqNcast]
        exact outerCube_closedNormBall_volume_ratio_le hrpos
      have hrowAt := hrowq qN (Finset.mem_Icc.mpr ⟨hnqN, hqmN⟩)
      rw [hwF] at hrowAt
      have hfar := farBranch_estimate d hcoeff hϑ0 hϑ1.le hA₀ hrpos hRpos hqmN
        hq3 hcubeq hratioq hmRleN hmRltN
        (fun y ↦ Fld y - (e + (PhiRow e).globalGradientRepresentative y))
        Fld hrowAt
      refine hfar.trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hratio0 : (0 : ℝ) ≤ (r / R) ^ max eta (1 / 2 : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hratio0
    · -- near band
      have hnear : R < 108 * (Real.sqrt d * r) := lt_of_not_ge hthr
      have hJZ0 : 0 ≤ outerTriadicGeneration (2 * (2 * R)) (by positivity) :=
        outerTriadicGeneration_nonneg_of_one_le (by positivity)
          (by linarith only [hR1])
      set JN : ℕ := (outerTriadicGeneration (2 * (2 * R))
        (by positivity)).toNat with hJNdef
      have hJNcast : (JN : ℤ) = outerTriadicGeneration (2 * (2 * R))
          (by positivity) := Int.toNat_of_nonneg hJZ0
      have hcubeJ : closedNormBall d R ⊆
          openCubeSet (originCube d (JN : ℤ)) := by
        rw [hJNcast]
        exact closedNormBall_subset_outerCube hRpos
      have hratioJ : volume (openCubeSet (originCube d (JN : ℤ))) /
          volume (closedNormBall d R) ≤
          ENNReal.ofReal ((6 * Real.sqrt d) ^ d) := by
        rw [hJNcast]
        exact outerCube_closedNormBall_volume_ratio_le hRpos
      have hnJ : nN ≤ JN := by
        have hmono := outerTriadicGeneration_le_outerTriadicGeneration
          (rStart := rS) (r := R) hrSpos hstartR
        omega
      have hstartJ : (Quenched.triadicCeilingIndex xRow : ℤ) ≤ (JN : ℤ) := by
        have : (nN : ℤ) ≤ (JN : ℤ) := by exact_mod_cast hnJ
        exact le_trans hstartN this
      have hcorE := hbound aIdentity
        (min (cStar g) (min cMax (2 * cB)) / 2)
        (Quenched.triadicCeilingIndex xRow : ℤ)
        ⟨by linarith only [hc'pos], hhalfcB⟩ hgoodTail hCauchyId PhiRow hPhiRow
        e JN hstartJ
      have hnearEst := nearBranch_estimate d hcoeff hϑ0 hϑ1.le hBenergy hAslope
        hrpos hRpos hrR hnear hcubeJ hratioJ hmRleN hmRltN
        Fld (fun y ↦ e + (PhiRow e).globalGradientRepresentative y)
        (htri abar hS3 a R u Du hu aIdentity PhiRow hPhiRow e)
        hcorE hslopeE
      refine hnearEst.trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hratio0 : (0 : ℝ) ≤ (r / R) ^ max eta (1 / 2 : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hratio0
  · -- the degenerate case: every admissible radius is in the near band
    have hallNear : R < 108 * (Real.sqrt d * rS) := lt_of_not_ge hcase
    refine ⟨0, ?_⟩
    intro r hr
    have hrS_le_r : rS ≤ r := hr.1
    have hrR : r ≤ R := hr.2
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le hrSpos hrS_le_r
    have hnear : R < 108 * (Real.sqrt d * r) := by
      have hmono : Real.sqrt d * rS ≤ Real.sqrt d * r :=
        mul_le_mul_of_nonneg_left hrS_le_r hsq.le
      linarith only [hallNear, hmono]
    have hzero := jointLimit_zero_grad_ae hCauchyId PhiRow hPhiRow
    have hfield : (fun y ↦ Fld y -
        (0 + (PhiRow 0).globalGradientRepresentative y)) =ᵐ[volume] Fld := by
      filter_upwards [hzero] with y hy
      rw [hy]
      simp
    have hcongr : weightedGradNorm
        (affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS3).isUnit)
          (⇑(normalizedCenteredCoeff a abar hS3).1))
        (closedNormBall d r)
        (fun y ↦ Fld y - (0 + (PhiRow 0).globalGradientRepresentative y)) =
        weightedGradNorm
          (affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS3).isUnit)
            (⇑(normalizedCenteredCoeff a abar hS3).1))
          (closedNormBall d r) Fld :=
      weightedGradNorm_congr_ae _ _ (ae_restrict_of_ae hfield)
    have hballs := weightedGradNorm_closedNormBall_le_of_near hrpos hRpos hrR
      hnear
      (affineCoefficient (Selection.normalizedRoot (symmPart abar))
        ((Matrix.isUnit_iff_isUnit_det _).mp
          (normalizedRoot_posDef_of_posDef hS3).isUnit)
        (⇑(normalizedCenteredCoeff a abar hS3).1)) Fld
    have hratioLower : (1 : ℝ) ≤ (108 * Real.sqrt d) *
        (r / R) ^ max eta (1 / 2 : ℝ) := by
      have hrR1 : r / R ≤ 1 := (div_le_one hRpos).2 hrR
      have hrRpos : (0 : ℝ) < r / R := by positivity
      have hpow : r / R ≤ (r / R) ^ max eta (1 / 2 : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hrRpos hrR1 hϑ1.le
        rwa [Real.rpow_one] at h
      have hlow : 1 < (108 * Real.sqrt d) * (r / R) := by
        rw [← mul_div_assoc, lt_div_iff₀ hRpos, one_mul]
        linarith only [hnear]
      have hcoefN : (0 : ℝ) ≤ 108 * Real.sqrt d := by positivity
      have := mul_le_mul_of_nonneg_left hpow hcoefN
      linarith only [hlow, this]
    have hnearC : (0 : ℝ) < (216 * Real.sqrt d) ^ d := by positivity
    have hbase : (0 : ℝ) ≤ ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg hnearC.le _
    have hconst : ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) ≤
        max (farBranchConstant d * A₀)
            (nearBranchConstant d Benergy Aslope) *
          (r / R) ^ max eta (1 / 2 : ℝ) := by
      calc ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)
        = ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * 1 := by ring
      _ ≤ ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
          ((108 * Real.sqrt d) * (r / R) ^ max eta (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hratioLower hbase
      _ = (((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (108 * Real.sqrt d)) *
          (r / R) ^ max eta (1 / 2 : ℝ) := by ring
      _ ≤ nearBranchConstant d Benergy Aslope *
          (r / R) ^ max eta (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (degenerate_le_nearBranchConstant hBenergy hAslope)
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ max (farBranchConstant d * A₀)
            (nearBranchConstant d Benergy Aslope) *
          (r / R) ^ max eta (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (by positivity) _)
    have hfinal : weightedGradNorm
        (affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS3).isUnit)
          (⇑(normalizedCenteredCoeff a abar hS3).1))
        (closedNormBall d r)
        (fun y ↦ Fld y -
          (0 + (PhiRow 0).globalGradientRepresentative y)) ≤
        ENNReal.ofReal (max (farBranchConstant d * A₀)
            (nearBranchConstant d Benergy Aslope) *
              (r / R) ^ max eta (1 / 2 : ℝ)) *
          weightedGradNorm
            (affineCoefficient (Selection.normalizedRoot (symmPart abar))
              ((Matrix.isUnit_iff_isUnit_det _).mp
                (normalizedRoot_posDef_of_posDef hS3).isUnit)
              (⇑(normalizedCenteredCoeff a abar hS3).1))
            (closedNormBall d R) Fld := by
      rw [hcongr]
      refine hballs.trans ?_
      rw [ENNReal.ofReal_rpow_of_pos hnearC]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl
    exact hfinal

end

end CorrectorComposition
end HighContrast
end HCPolySupport
