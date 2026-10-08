/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.JointNegOneClasses
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.PowerTailAtScale

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.JointNegOnePower

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem normalizedDual_eq_of_ae_eq
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d} (s : ℝ)
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F =
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s G := by
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Book.Ch03.cubeBesovDualFullNorm_eq_of_ae_eq_on_cubeSet
  simpa only [volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using!
      hFG.fun_comp (fun z ↦ z i)

private theorem outer_pair_restrict_gap_three
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q : ℕ) :
    triadicScaledNegOneNorm (q : ℤ) (innerFiniteGradientClass a e q) +
        triadicScaledNegOneNorm (q : ℤ) (innerFiniteFluxClass a e q) ≤
      gapThreeNegOneRestrictionConstant d *
        (triadicScaledNegOneNorm ((q : ℤ) + 3)
            (outerFiniteGradientClass a e ((q : ℤ) + 3)) +
          triadicScaledNegOneNorm ((q : ℤ) + 3)
            (outerFiniteFluxClass a e ((q : ℤ) + 3))) := by
  have hgrad := triadicScaledNegOne_restrict_gap_three_le
    (d := d) (q : ℤ) (outerFiniteGradientClass a e ((q : ℤ) + 3))
  have hflux := triadicScaledNegOne_restrict_gap_three_le
    (d := d) (q : ℤ) (outerFiniteFluxClass a e ((q : ℤ) + 3))
  simpa only [innerFiniteGradientClass, innerFiniteFluxClass,
    mul_add] using add_le_add hgrad hflux

private theorem outer_finite_dual_rows_le_power_rate
    {d : ℕ} [NeZero d] (g c kappa x Cfinite : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hKappa : 0 < kappa) (hx : 0 < x)
    (hCfinite : 0 ≤ Cfinite)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hPower : ScalarIdentityPowerTail aIdentity (printCertificateOrder g)
      (correctorTargetAmplitude c kappa) kappa x)
    (hfinite : ∀ (a : Book.Ch03.CoeffFamily d) (m : ℤ) (e : Vec d),
      scalarIdentityWeakError a (printCertificateOrder g) m ≤ 1 →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo (originCube d m)
          (printCertificateOrder g)
          (fun y ↦ (finiteAffineSolution a m e).toH1.grad y - e) ≤
        Cfinite * scalarIdentityWeakError a (printCertificateOrder g) m * euclideanNorm e ∧
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo (originCube d m)
          (printCertificateOrder g)
          (fun y ↦ matVecMul (Book.Ch03.publicCoeffField (originCube d m) a y)
            ((finiteAffineSolution a m e).toH1.grad y) - e) ≤
        Cfinite * scalarIdentityWeakError a (printCertificateOrder g) m * euclideanNorm e)
    (e : Vec d) (q : ℕ) (hxq : x ≤ (3 : ℝ) ^ q)
    (hdeltaLt : (c / 2) * ((((3 : ℝ) ^ q) / x) ^ (-kappa)) < c) :
    let rate := (((3 : ℝ) ^ q) / x) ^ (-kappa)
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo
        (originCube d ((q + 3 : ℕ) : ℤ)) (printCertificateOrder g)
        (fun y ↦ (outerFiniteGradientClass aIdentity e ((q + 3 : ℕ) : ℤ) y).toVec) ≤
      Cfinite * rate * euclideanNorm e ∧
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo
        (originCube d ((q + 3 : ℕ) : ℤ)) (printCertificateOrder g)
        (fun y ↦ (outerFiniteFluxClass aIdentity e ((q + 3 : ℕ) : ℤ) y).toVec) ≤
      Cfinite * rate * euclideanNorm e := by
  let rate : ℝ := (((3 : ℝ) ^ q) / x) ^ (-kappa)
  let delta : ℝ := (c / 2) * rate
  let m : ℕ := q + 3
  have hscalePos : 0 < ((3 : ℝ) ^ q) / x := by positivity
  have hratePos : 0 < rate := Real.rpow_pos_of_pos hscalePos _
  have hxM : x ≤ (3 : ℝ) ^ m := by
    calc
      x ≤ (3 : ℝ) ^ q := hxq
      _ ≤ (3 : ℝ) ^ m := by
        exact pow_le_pow_right₀ (by norm_num) (by simp [m])
  have hPowerM := hPower (m : ℤ)
    (by simpa only [zpow_natCast] using hxM)
  have hTargetRateM : correctorTargetAmplitude c kappa *
      (((3 : ℝ) ^ m) / x) ^ (-kappa) ≤ delta := by
    have hratioMono : ((3 : ℝ) ^ q) / x ≤ ((3 : ℝ) ^ m) / x := by
      exact div_le_div_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by simp [m])) hx.le
    have hpowMono : (((3 : ℝ) ^ m) / x) ^ (-kappa) ≤ rate := by
      dsimp only [rate]
      exact Real.rpow_le_rpow_of_nonpos hscalePos hratioMono
        (by linarith only [hKappa])
    rw [correctorTargetAmplitude]
    have hpow : (3 : ℝ) ^ (-kappa) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (neg_neg_of_pos hKappa)
    have hfactorOne : 1 - (3 : ℝ) ^ (-kappa) ≤ 1 :=
      sub_le_self _ (Real.rpow_nonneg (by norm_num) _)
    calc
      (c / 2 * (1 - (3 : ℝ) ^ (-kappa))) *
          (((3 : ℝ) ^ m) / x) ^ (-kappa) ≤
        (c / 2) * (((3 : ℝ) ^ m) / x) ^ (-kappa) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hfactorOne (half_pos hc.1).le)
            (Real.rpow_nonneg (by positivity) _)
      _ ≤ (c / 2) * rate :=
        mul_le_mul_of_nonneg_left hpowMono (half_pos hc.1).le
      _ = delta := rfl
  have hweakM : scalarIdentityWeakError aIdentity
      (printCertificateOrder g) (m : ℤ) ≤ 1 :=
    hPowerM.trans (hTargetRateM.trans (hdeltaLt.le.trans hc.2.le))
  have hfiniteRaw := hfinite aIdentity (m : ℤ) e hweakM
  have hfiniteBound : Cfinite * scalarIdentityWeakError aIdentity
      (printCertificateOrder g) (m : ℤ) * euclideanNorm e ≤
      Cfinite * rate * euclideanNorm e := by
    have hweakRate : scalarIdentityWeakError aIdentity
        (printCertificateOrder g) (m : ℤ) ≤ rate := by
      exact hPowerM.trans (hTargetRateM.trans
        (by
          dsimp only [delta]
          have hcHalf : c / 2 ≤ 1 := by linarith only [hc.2]
          exact mul_le_of_le_one_left hratePos.le hcHalf))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hweakRate hCfinite)
      (euclideanNorm_nonneg e)
  have hfiniteRows :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (m : ℤ)) (printCertificateOrder g)
          (fun y ↦ (outerFiniteGradientClass
            aIdentity e (m : ℤ) y).toVec) ≤
        Cfinite * rate * euclideanNorm e ∧
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (m : ℤ)) (printCertificateOrder g)
          (fun y ↦ (outerFiniteFluxClass
            aIdentity e (m : ℤ) y).toVec) ≤
        Cfinite * rate * euclideanNorm e := by
    constructor
    · rw [normalizedDual_eq_of_ae_eq _
          (outerFiniteGradient_toVec_ae aIdentity e (m : ℤ))]
      exact hfiniteRaw.1.trans hfiniteBound
    · rw [normalizedDual_eq_of_ae_eq _
          (outerFiniteFlux_toVec_ae aIdentity e (m : ℤ))]
      exact hfiniteRaw.2.trans hfiniteBound
  exact hfiniteRows

private theorem joint_negative_pair_le_finite_and_remainder_rates
    {d : ℕ} [NeZero d] (aIdentity : Book.Ch03.CoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d) (e : Vec d) (q : ℕ)
    (Cdual : ℝ≥0∞) (Cfinite Cremainder Ctail rate : ℝ)
    (hCfinite : 0 ≤ Cfinite) (hCremainder : 0 < Cremainder)
    (hCtail : 0 < Ctail) (hratePos : 0 < rate)
    (houterPair : triadicScaledNegOneNorm ((q + 3 : ℕ) : ℤ)
          (outerFiniteGradientClass aIdentity e ((q + 3 : ℕ) : ℤ)) +
        triadicScaledNegOneNorm ((q + 3 : ℕ) : ℤ)
          (outerFiniteFluxClass aIdentity e ((q + 3 : ℕ) : ℤ)) ≤
      Cdual * ENNReal.ofReal (Cfinite * rate * euclideanNorm e))
    (hremPair : triadicScaledNegOneNorm (q : ℤ)
          (jointGradientRemainderClass aIdentity Phi e q) +
        triadicScaledNegOneNorm (q : ℤ)
          (jointFluxRemainderClass aIdentity Phi e q) ≤
      Cdual * ENNReal.ofReal ((2 * Cremainder * Ctail) * rate * euclideanNorm e)) :
    triadicScaledNegOneNorm (q : ℤ)
          (correctorGradientOnOriginCube Phi e (q : ℤ)) +
        triadicScaledNegOneNorm (q : ℤ)
          (scalarIdentityCorrectorFluxDefectOnOriginCube aIdentity Phi e (q : ℤ)) ≤
      (1 + Cdual * (gapThreeNegOneRestrictionConstant d + 1) *
        ENNReal.ofReal (Cfinite + 2 * Cremainder * Ctail)) *
        ENNReal.ofReal (rate * euclideanNorm e) := by
  let m : ℕ := q + 3
  let Creal : ℝ := Cfinite + 2 * Cremainder * Ctail
  let C : ℝ≥0∞ := 1 + Cdual *
    (gapThreeNegOneRestrictionConstant d + 1) * ENNReal.ofReal Creal
  have hinnerPair := outer_pair_restrict_gap_three aIdentity e q
  have houterIndex : ((m : ℕ) : ℤ) = (q : ℤ) + 3 := by
    simp only [m]
    omega
  rw [← houterIndex] at hinnerPair
  have hjointGrad := triadicScaledNegOneNorm_add_le (q : ℤ)
    (innerFiniteGradientClass aIdentity e q)
    (jointGradientRemainderClass aIdentity Phi e q)
  have hjointFlux := triadicScaledNegOneNorm_add_le (q : ℤ)
    (innerFiniteFluxClass aIdentity e q)
    (jointFluxRemainderClass aIdentity Phi e q)
  have hjoint :
      triadicScaledNegOneNorm (q : ℤ)
            (correctorGradientOnOriginCube Phi e (q : ℤ)) +
          triadicScaledNegOneNorm (q : ℤ)
            (scalarIdentityCorrectorFluxDefectOnOriginCube
              aIdentity Phi e (q : ℤ)) ≤
        (gapThreeNegOneRestrictionConstant d *
          (Cdual * ENNReal.ofReal
            (Cfinite * rate * euclideanNorm e))) +
        Cdual * ENNReal.ofReal
          ((2 * Cremainder * Ctail) * rate * euclideanNorm e) := by
    rw [correctorGradient_eq_innerFinite_add_remainder
      aIdentity Phi e q,
      correctorFlux_eq_innerFinite_add_remainder
        aIdentity Phi e q]
    calc
      _ ≤ (triadicScaledNegOneNorm (q : ℤ)
              (innerFiniteGradientClass aIdentity e q) +
            triadicScaledNegOneNorm (q : ℤ)
              (jointGradientRemainderClass aIdentity Phi e q)) +
          (triadicScaledNegOneNorm (q : ℤ)
              (innerFiniteFluxClass aIdentity e q) +
            triadicScaledNegOneNorm (q : ℤ)
              (jointFluxRemainderClass aIdentity Phi e q)) :=
        add_le_add hjointGrad hjointFlux
      _ = (triadicScaledNegOneNorm (q : ℤ)
              (innerFiniteGradientClass aIdentity e q) +
            triadicScaledNegOneNorm (q : ℤ)
              (innerFiniteFluxClass aIdentity e q)) +
          (triadicScaledNegOneNorm (q : ℤ)
              (jointGradientRemainderClass aIdentity Phi e q) +
            triadicScaledNegOneNorm (q : ℤ)
              (jointFluxRemainderClass aIdentity Phi e q)) := by ring
      _ ≤ gapThreeNegOneRestrictionConstant d *
              (Cdual * ENNReal.ofReal
                (Cfinite * rate * euclideanNorm e)) +
            Cdual * ENNReal.ofReal
              ((2 * Cremainder * Ctail) * rate * euclideanNorm e) :=
        add_le_add (hinnerPair.trans (by
          simpa only [mul_comm] using
            mul_le_mul_left houterPair
              (gapThreeNegOneRestrictionConstant d))) hremPair
  have hcollapse :
      gapThreeNegOneRestrictionConstant d *
          (Cdual * ENNReal.ofReal
            (Cfinite * rate * euclideanNorm e)) +
        Cdual * ENNReal.ofReal
          ((2 * Cremainder * Ctail) * rate * euclideanNorm e) ≤
      C * ENNReal.ofReal (rate * euclideanNorm e) := by
    have hrateNorm : 0 ≤ rate * euclideanNorm e :=
      mul_nonneg hratePos.le (euclideanNorm_nonneg e)
    have hfiniteOfReal : ENNReal.ofReal
        (Cfinite * rate * euclideanNorm e) =
        ENNReal.ofReal Cfinite * ENNReal.ofReal
          (rate * euclideanNorm e) := by
      rw [show Cfinite * rate * euclideanNorm e =
        Cfinite * (rate * euclideanNorm e) by ring,
        ENNReal.ofReal_mul hCfinite]
    have hremOfReal : ENNReal.ofReal
        ((2 * Cremainder * Ctail) * rate * euclideanNorm e) =
        ENNReal.ofReal (2 * Cremainder * Ctail) *
          ENNReal.ofReal (rate * euclideanNorm e) := by
      rw [show (2 * Cremainder * Ctail) * rate * euclideanNorm e =
        (2 * Cremainder * Ctail) * (rate * euclideanNorm e) by ring,
        ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg (by norm_num) hCremainder.le) hCtail.le)]
    rw [hfiniteOfReal, hremOfReal]
    have hcoeff : gapThreeNegOneRestrictionConstant d *
          (Cdual * ENNReal.ofReal Cfinite) +
        Cdual * ENNReal.ofReal (2 * Cremainder * Ctail) ≤ C := by
      have hremCoeffNonneg : 0 ≤ 2 * Cremainder * Ctail :=
        mul_nonneg (mul_nonneg (by norm_num) hCremainder.le) hCtail.le
      have hfiniteReal : ENNReal.ofReal Cfinite ≤ ENNReal.ofReal Creal :=
        ENNReal.ofReal_le_ofReal (by
          dsimp only [Creal]
          exact le_add_of_nonneg_right hremCoeffNonneg)
      have hremReal : ENNReal.ofReal (2 * Cremainder * Ctail) ≤
          ENNReal.ofReal Creal :=
        ENNReal.ofReal_le_ofReal (by
          dsimp only [Creal]
          exact le_add_of_nonneg_left hCfinite)
      calc
        _ ≤ gapThreeNegOneRestrictionConstant d *
              (Cdual * ENNReal.ofReal Creal) +
            Cdual * ENNReal.ofReal Creal :=
          add_le_add
            (by
              simpa only [mul_comm, mul_left_comm, mul_assoc] using
                mul_le_mul_left (mul_le_mul_left hfiniteReal Cdual)
                  (gapThreeNegOneRestrictionConstant d))
            (by simpa only [mul_comm] using
              mul_le_mul_left hremReal Cdual)
        _ = Cdual * (gapThreeNegOneRestrictionConstant d + 1) *
              ENNReal.ofReal Creal := by ring
        _ ≤ C := by
          dsimp only [C]
          exact le_add_left le_rfl
    calc
      _ = (gapThreeNegOneRestrictionConstant d *
              (Cdual * ENNReal.ofReal Cfinite) +
            Cdual * ENNReal.ofReal (2 * Cremainder * Ctail)) *
          ENNReal.ofReal (rate * euclideanNorm e) := by ring
      _ ≤ C * ENNReal.ofReal (rate * euclideanNorm e) :=
        mul_le_mul_left hcoeff _
  exact hjoint.trans hcollapse

/-- The exact identity-gauge joint corrector inherits the
inverse-side-length normalized negative-one power rate.  The finite part is
taken three generations out and restricted back before it is joined to the
finite-to-limit remainder. -/
theorem exists_identityGaugeJointScaledNegOnePowerConstant
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ 0 < C ∧
      ∀ (aGauge : CoeffSpace d)
        (hI : (symmPart (1 : Mat d)).PosDef)
        (aIdentity : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aIdentity.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace (1 : Mat d) hI aGauge).1 :
              CoeffField d)) →
        ∀ (kappa x : ℝ), 0 < kappa → 0 < x →
          ScalarIdentityPowerTail aIdentity (printCertificateOrder g)
            (correctorTargetAmplitude
              (identitySuccessorSmallness d g geom hg hdual) kappa)
            kappa x →
          ∀ (Phi : Vec d → NormalizedLocalH1Carrier d),
            IsFiniteAffineCorrectionJointLocalEquation aIdentity Phi →
            ∀ (e : Vec d) (q : ℕ), x ≤ (3 : ℝ) ^ q →
              let rate := (((3 : ℝ) ^ q) / x) ^ (-kappa)
              triadicScaledNegOneNorm (q : ℤ)
                    (correctorGradientOnOriginCube Phi e (q : ℤ)) +
                  triadicScaledNegOneNorm (q : ℤ)
                    (scalarIdentityCorrectorFluxDefectOnOriginCube
                      aIdentity Phi e (q : ℤ)) ≤
                C * ENNReal.ofReal (rate * euclideanNorm e) := by
  obtain ⟨Cfinite, hCfinite, hfinite⟩ :=
    exists_identityFiniteResponseConstant d g hg
  obtain ⟨Cremainder, hCremainder, hremainder⟩ :=
    exists_jointFiniteRemainderRowsConstant d
      (printCertificateOrder g) (printOrder_margins hg).1
  let sOrder : FractionalOrder :=
    ⟨printCertificateOrder g, (printOrder_margins hg).1,
      (printOrder_margins hg).2.1.trans (by norm_num)⟩
  obtain ⟨Cdual, hCdualTop, hCdualPos, hdualRows⟩ :=
    exists_scaledNegOne_pair_le_normalizedDualRows d sOrder
      (printOrder_margins hg).2.1
  let Ctail : ℝ := 2 * identitySuccessorEnergyConstant d g geom hg hdual
  let Creal : ℝ := Cfinite + 2 * Cremainder * Ctail
  let C : ℝ≥0∞ := 1 + Cdual *
    (gapThreeNegOneRestrictionConstant d + 1) * ENNReal.ofReal Creal
  have hCtail : 0 < Ctail := by
    dsimp only [Ctail]
    exact mul_pos (by norm_num)
      (identitySuccessorEnergyConstant_pos d g geom hg hdual)
  have hCreal : 0 < Creal := by
    dsimp only [Creal]
    positivity
  have hCTop : C < ∞ := by
    dsimp only [C]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
      ENNReal.mul_lt_top
        (ENNReal.mul_lt_top hCdualTop
          (ENNReal.add_lt_top.2
            ⟨gapThreeNegOneRestrictionConstant_lt_top d,
              ENNReal.one_lt_top⟩)) ENNReal.ofReal_lt_top⟩
  have hCPos : 0 < C := by
    dsimp only [C]
    exact zero_lt_one.trans_le (le_add_right le_rfl)
  refine ⟨C, hCTop, hCPos, ?_⟩
  intro aGauge hI aIdentity hIdentity kappa x hKappa hx hPower
    Phi hPhi e q hxq
  let c := identitySuccessorSmallness d g geom hg hdual
  let rate : ℝ := (((3 : ℝ) ^ q) / x) ^ (-kappa)
  let delta : ℝ := (c / 2) * rate
  let m : ℕ := q + 3
  have hc : c ∈ Ioo (0 : ℝ) 1 :=
    identitySuccessorSmallness_mem d g geom hg hdual
  have hscalePos : 0 < ((3 : ℝ) ^ q) / x := by positivity
  have hscaleOne : 1 ≤ ((3 : ℝ) ^ q) / x := by
    exact (le_div_iff₀ hx).2 (by simpa only [one_mul] using hxq)
  have hratePos : 0 < rate := by
    dsimp only [rate]
    exact Real.rpow_pos_of_pos hscalePos _
  have hrateOne : rate ≤ 1 := by
    dsimp only [rate]
    exact Real.rpow_le_one_of_one_le_of_nonpos hscaleOne
      (by linarith only [hKappa])
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact mul_pos (half_pos hc.1) hratePos
  have hdeltaLt : delta < c := by
    dsimp only [delta]
    have hhalf : c / 2 < c := by linarith only [hc.1]
    exact (mul_le_of_le_one_right (half_pos hc.1).le hrateOne).trans_lt hhalf
  have hdelta : delta ∈ Ioc (0 : ℝ) c := ⟨hdeltaPos, hdeltaLt.le⟩
  have hTargetNonneg : 0 ≤ correctorTargetAmplitude c kappa :=
    (correctorTargetAmplitude_pos hc.1 hKappa).le
  have hgoodRaw := powerTail_goodTail_at_nat hPower
    hTargetNonneg hKappa hxq hx
  have hgood : ScalarIdentityGoodTail aIdentity
      (printCertificateOrder g) delta (q : ℤ) := by
    rw [canonical_restarted_tolerance_eq hKappa] at hgoodRaw
    simpa only [c, delta, rate] using hgoodRaw
  have hweakQ : scalarIdentityWeakError aIdentity
      (printCertificateOrder g) (q : ℤ) ≤ 1 :=
    (hgood.weakError_le le_rfl).trans (hdeltaLt.le.trans hc.2.le)
  have htail := identityGaugeJointWeightedTail
    d g geom hg hdual aGauge hI aIdentity hIdentity delta (q : ℤ)
      hdelta hgood Phi hPhi e q m (le_refl _) (by simp [m])
  have hremEnergy : Book.Ch03.h1EnergyNormOnCube
      (originCube d (q : ℤ)) aIdentity
      (jointFiniteRemainderCubeSolution
        aIdentity Phi hPhi e q m (by simp [m])).toH1 ≤
      Ctail * (1 + delta) * delta * euclideanNorm e := by
    rw [jointFiniteRemainder_energy_eq]
    simpa only [Ctail] using htail
  have hrem := hremainder aIdentity Phi hPhi e q m (by simp [m])
    (Ctail * (1 + delta) * delta * euclideanNorm e) hweakQ hremEnergy
  have hdeltaOne : delta ≤ 1 := hdeltaLt.le.trans hc.2.le
  have hremBound : Cremainder *
      (Ctail * (1 + delta) * delta * euclideanNorm e) ≤
      (2 * Cremainder * Ctail) * rate * euclideanNorm e := by
    have hone : 1 + delta ≤ 2 := by linarith only [hdeltaOne]
    have hdeltaRate : delta ≤ rate := by
      dsimp only [delta]
      have hcHalf : c / 2 ≤ 1 := by linarith only [hc.2]
      exact mul_le_of_le_one_left hratePos.le hcHalf
    calc
      _ = (Cremainder * Ctail) * (1 + delta) * delta *
          euclideanNorm e := by ring
      _ ≤ (Cremainder * Ctail) * 2 * delta * euclideanNorm e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hone
              (mul_nonneg hCremainder.le hCtail.le)) hdeltaPos.le)
          (euclideanNorm_nonneg e)
      _ ≤ (2 * Cremainder * Ctail) * rate * euclideanNorm e := by
        rw [show (Cremainder * Ctail) * 2 =
          2 * Cremainder * Ctail by ring]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaRate
            (mul_nonneg (mul_nonneg (by norm_num) hCremainder.le)
              hCtail.le)) (euclideanNorm_nonneg e)
  have hremRowsRaw :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (q : ℤ)) (printCertificateOrder g)
          (jointFiniteRemainderCubeSolution
            aIdentity Phi hPhi e q m (by simp [m])).toH1.grad ≤
        (2 * Cremainder * Ctail) * rate * euclideanNorm e ∧
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (q : ℤ)) (printCertificateOrder g)
          (fun y ↦ matVecMul (Book.Ch03.publicCoeffField
            (originCube d (q : ℤ)) aIdentity y)
            ((jointFiniteRemainderCubeSolution
              aIdentity Phi hPhi e q m (by simp [m])).toH1.grad y)) ≤
        (2 * Cremainder * Ctail) * rate * euclideanNorm e :=
    ⟨hrem.1.trans hremBound, hrem.2.trans hremBound⟩
  have hremRows :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (q : ℤ)) (printCertificateOrder g)
          (fun y ↦ (jointGradientRemainderClass
            aIdentity Phi e q y).toVec) ≤
        (2 * Cremainder * Ctail) * rate * euclideanNorm e ∧
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (q : ℤ)) (printCertificateOrder g)
          (fun y ↦ (jointFluxRemainderClass
            aIdentity Phi e q y).toVec) ≤
        (2 * Cremainder * Ctail) * rate * euclideanNorm e := by
    constructor
    · rw [normalizedDual_eq_of_ae_eq _
          (jointGradientRemainder_toVec_ae
            aIdentity Phi hPhi e q)]
      exact hremRowsRaw.1
    · rw [normalizedDual_eq_of_ae_eq _
          (jointFluxRemainder_toVec_ae
            aIdentity Phi hPhi e q)]
      exact hremRowsRaw.2
  have hfiniteRows := outer_finite_dual_rows_le_power_rate g c kappa x Cfinite
    hc hKappa hx hCfinite aIdentity hPower
    (fun a m e hweak ↦ ⟨(hfinite a m e hweak).1, (hfinite a m e hweak).2.1⟩)
    e q hxq hdeltaLt
  have houterPair := hdualRows (m : ℤ)
    (outerFiniteGradientClass aIdentity e (m : ℤ))
    (outerFiniteFluxClass aIdentity e (m : ℤ))
    (Cfinite * rate * euclideanNorm e) hfiniteRows.1 hfiniteRows.2
  have hremPair := hdualRows (q : ℤ)
    (jointGradientRemainderClass aIdentity Phi e q)
    (jointFluxRemainderClass aIdentity Phi e q)
    ((2 * Cremainder * Ctail) * rate * euclideanNorm e)
    hremRows.1 hremRows.2
  exact joint_negative_pair_le_finite_and_remainder_rates
    aIdentity Phi e q Cdual Cfinite Cremainder Ctail rate
    hCfinite hCremainder hCtail hratePos houterPair hremPair

end

end HighContrast
end HCPolySupport
