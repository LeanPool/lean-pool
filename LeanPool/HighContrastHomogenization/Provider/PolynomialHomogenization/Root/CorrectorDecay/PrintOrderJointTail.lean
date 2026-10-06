/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.PrintOrderLocalCauchy
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FiniteCorrectorLimitBridge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1QuantitativeCorrectorTail

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.PrintOrderJointTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open Filter MeasureTheory Set

noncomputable section

private theorem finiteAffineInnerGradientClass_succ_sub_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q j : ℕ) :
    finiteAffineInnerGradientClass a e q (j + 1) -
        finiteAffineInnerGradientClass a e q j =
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ ((q + j : ℕ) : ℤ) by omega)
        (finiteAffineSuccessorDifference a ((q + j : ℕ) : ℤ) e)).toH1.gradToHilbertVectorL2 := by
  let u1 := finiteAffineSolutionInnerH1 a (q : ℤ)
    ((q + (j + 1) : ℕ) : ℤ) (by omega) e
  let u0 := finiteAffineSolutionInnerH1 a (q : ℤ)
    ((q + j : ℕ) : ℤ) (by omega) e
  let w := finiteCubeSolutionRestriction a
    (show (q : ℤ) ≤ ((q + j : ℕ) : ℤ) by omega)
    (finiteAffineSuccessorDifference a ((q + j : ℕ) : ℤ) e)
  change u1.gradToHilbertVectorL2 - u0.gradToHilbertVectorL2 =
    w.toH1.gradToHilbertVectorL2
  apply Lp.ext
  filter_upwards [u1.coeFn_gradToHilbertVectorL2,
      u0.coeFn_gradToHilbertVectorL2,
      w.toH1.coeFn_gradToHilbertVectorL2,
      Lp.coeFn_sub u1.gradToHilbertVectorL2
        u0.gradToHilbertVectorL2] with x hu1 hu0 hw hsub
  rw [hsub, Pi.sub_apply, hu1, hu0, hw]
  dsimp only [u1, u0, w]
  rw [finiteAffineSolutionInnerH1_grad,
    finiteAffineSolutionInnerH1_grad,
    finiteCubeSolutionRestriction_grad,
    finiteAffineSuccessorDifference_grad]
  have hindex : ((q + (j + 1) : ℕ) : ℤ) =
      ((q + j : ℕ) : ℤ) + 1 := by omega
  rw [hindex]
  rfl

private theorem sqrt_innerGradient_succ_sub_eq_energy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q j : ℕ) :
    Real.sqrt (normalizedLocalSymmetricEnergy
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)
      (finiteAffineInnerGradientClass a e q (j + 1) -
        finiteAffineInnerGradientClass a e q j)) =
      Book.Ch03.h1EnergyNormOnCube (originCube d (q : ℤ)) a
        (finiteCubeSolutionRestriction a
          (show (q : ℤ) ≤ ((q + j : ℕ) : ℤ) by omega)
          (finiteAffineSuccessorDifference a
            ((q + j : ℕ) : ℤ) e)).toH1 := by
  let w : H1Function (openCubeSet (originCube d (q : ℤ))) :=
    Eq.mp (by simp only [Book.Ch02.cubeDomain_coe])
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ ((q + j : ℕ) : ℤ) by omega)
        (finiteAffineSuccessorDifference a
          ((q + j : ℕ) : ℤ) e)).toH1
  rw [finiteAffineInnerGradientClass_succ_sub_eq]
  change Real.sqrt (normalizedLocalSymmetricEnergy _
    w.gradToHilbertVectorL2) = _
  rw [Root.sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal]
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      (originCube d (q : ℤ)) a)]
  have hgrad : w.grad =
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ ((q + j : ℕ) : ℤ) by omega)
        (finiteAffineSuccessorDifference a
          ((q + j : ℕ) : ℤ) e)).toH1.grad := rfl
  rw [hgrad, weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
  rw [ENNReal.toReal_ofReal]
  unfold Book.Ch03.h1EnergyNormOnCube
  exact Real.sqrt_nonneg _

/-- The exact-gauge local Cauchy witness produces the joint normalized limit
and its fixed-cube weak equation at the printed order. -/
theorem existsUnique_identityGaugeJointLocalEquation
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation)
    (aGauge : CoeffSpace d) (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI aGauge).1 :
          CoeffField d))
    (delta : ℝ) (n : ℤ)
    (hdelta : delta ∈ Ioc (0 : ℝ)
      (identitySuccessorSmallness d g geom hg hdual))
    (hgood : ScalarIdentityGoodTail aIdentity
      (printCertificateOrder g) delta n) :
    ∃! Phi : Vec d → NormalizedLocalH1Carrier d,
      IsFiniteAffineCorrectionJointLocalEquation aIdentity Phi := by
  have hCauchy := identityGaugeFiniteCorrectionLocalCauchy
    d g geom hg hdual aGauge hI aIdentity hIdentity delta n hdelta hgood
  obtain ⟨Phi, hPhi, hPhiUnique⟩ :=
    existsUnique_finiteAffineCorrectionJointLocalLimit aIdentity hCauchy
  refine ⟨Phi, ⟨?_, ?_⟩, ?_⟩
  · simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi
  · intro e q
    have hPhiEq :
        Phi = finiteAffineCorrectionJointLocalLimit aIdentity hCauchy :=
      (isFiniteAffineCorrectionJointLocalLimit_iff_eq
        aIdentity hCauchy Phi).mp hPhi
    rw [hPhiEq]
    simpa only [finiteAffineCorrectionJointLocalH1] using
      finiteAffineCorrectionJointLocalH1_isHarmonic
        aIdentity hCauchy e q
  · intro Psi hPsi
    have hPsiLimit :
        IsFiniteAffineCorrectionJointLocalLimit aIdentity Psi := by
      simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPsi.1
    exact hPhiUnique Psi hPsiLimit

/-- The printed-order exact-gauge successor estimate telescopes to a
quantitative tail of the joint corrector, with no rounded-family join. -/
theorem identityGaugeJointWeightedTail
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation)
    (aGauge : CoeffSpace d) (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI aGauge).1 :
          CoeffField d))
    (delta : ℝ) (n : ℤ)
    (hdelta : delta ∈ Ioc (0 : ℝ)
      (identitySuccessorSmallness d g geom hg hdual))
    (hgood : ScalarIdentityGoodTail aIdentity
      (printCertificateOrder g) delta n)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation aIdentity Phi)
    (e : Vec d) (q m : ℕ) (hnq : n ≤ (q : ℤ)) (hqm : q + 3 ≤ m) :
    Real.sqrt (normalizedLocalSymmetricEnergy
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) aIdentity)
      (((show LocalGradientL2 d q from
            constantGradientOnOriginCube e (q : ℤ)) +
          (Phi e).gradientComponent q) -
        finiteAffineInnerGradientClass aIdentity e q (m - q))) ≤
      (2 * identitySuccessorEnergyConstant d g geom hg hdual) *
        (1 + delta) * delta * euclideanNorm e := by
  let C := identitySuccessorEnergyConstant d g geom hg hdual
  have hC : 0 < C := identitySuccessorEnergyConstant_pos
    d g geom hg hdual
  let k : ℕ := m - q
  have hk3 : 3 ≤ k := by dsimp only [k]; omega
  have hqk : q + k = m := by dsimp only [k]; omega
  apply sqrt_jointLocalGradient_sub_finiteAffine_le_of_uniform_tail
    aIdentity Phi hPhi e q k
      ((2 * C) * (1 + delta) * delta * euclideanNorm e)
  intro r hkr
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) aIdentity
  have hvol : 0 < volume (localGradientCube d q) := by
    have hreal := volume_openCubeSet_originCube_toReal_pos
      (d := d) (q : ℤ)
    exact (ENNReal.toReal_pos_iff.mp
      (by simpa only [localGradientCube] using hreal)).1
  have hvoltop : volume (localGradientCube d q) ≠ ⊤ := by
    simpa only [localGradientCube] using
      (volume_openCubeSet_lt_top (originCube d (q : ℤ))).ne
  have htelescope := sqrt_normalizedLocalSymmetricEnergy_sub_le_sum_Ico
    hEll hvol hvoltop (finiteAffineInnerGradientClass aIdentity e q)
      k r hkr
  refine htelescope.trans ?_
  let E : ℕ → ℝ := fun j => scalarIdentityWeakError aIdentity
    (printCertificateOrder g) ((q + j : ℕ) : ℤ)
  have hterm : ∀ j ∈ Finset.Ico k r,
      Real.sqrt (normalizedLocalSymmetricEnergy hEll
        (finiteAffineInnerGradientClass aIdentity e q (j + 1) -
          finiteAffineInnerGradientClass aIdentity e q j)) ≤
        C * (E j + E (j + 1)) * euclideanNorm e := by
    intro j hj
    have hkj : k ≤ j := (Finset.mem_Ico.mp hj).1
    have hqj3 : (q : ℤ) ≤ ((q + j : ℕ) : ℤ) - 1 - 2 := by
      have : 3 ≤ j := hk3.trans hkj
      omega
    have hinterval : ScalarIdentityGoodTailOnInterval aIdentity
        (printCertificateOrder g) delta (q : ℤ)
          (((q + j : ℕ) : ℤ) + 1) :=
      (hgood.interval (hnq.trans (by omega))).mono_start hnq
    have hsuc := identityGaugeSuccessorEnergy_le
      d g geom hg hdual aGauge hI aIdentity hIdentity delta
      (q : ℤ) (q : ℤ) ((q + j : ℕ) : ℤ) e hdelta
      (le_refl _) hqj3 hinterval
    rw [sqrt_innerGradient_succ_sub_eq_energy]
    rw [← successorInner_energy_eq_direct_restriction
      aIdentity ((q + j : ℕ) : ℤ) (q : ℤ) e hqj3]
    simpa only [C, E, show (((q + j : ℕ) : ℤ) + 1) =
      ((q + (j + 1) : ℕ) : ℤ) by omega] using hsuc
  calc
    ∑ j ∈ Finset.Ico k r,
        Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (finiteAffineInnerGradientClass aIdentity e q (j + 1) -
            finiteAffineInnerGradientClass aIdentity e q j)) ≤
        ∑ j ∈ Finset.Ico k r,
          C * (E j + E (j + 1)) * euclideanNorm e := by
      exact Finset.sum_le_sum hterm
    _ = C *
          ((∑ j ∈ Finset.Ico k r, E j) +
            (∑ j ∈ Finset.Ico k r, E (j + 1))) *
          euclideanNorm e := by
      calc
        _ = ∑ j ∈ Finset.Ico k r,
            (C * E j * euclideanNorm e +
              C * E (j + 1) * euclideanNorm e) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j ∈ Finset.Ico k r, C * E j * euclideanNorm e) +
            (∑ j ∈ Finset.Ico k r,
              C * E (j + 1) * euclideanNorm e) :=
          Finset.sum_add_distrib
        _ = _ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
    _ = C *
          ((∑ j ∈ Finset.Ico k r, E j) +
            (∑ j ∈ Finset.Ico (k + 1) (r + 1), E j)) *
          euclideanNorm e := by
      have hshift : (∑ j ∈ Finset.Ico k r, E (j + 1)) =
          ∑ j ∈ Finset.Ico (k + 1) (r + 1), E j := by
        simpa only [Nat.add_comm] using Finset.sum_Ico_add E k r 1
      rw [hshift]
    _ ≤ C * (2 * ((1 + delta) * delta)) * euclideanNorm e := by
      have hgoodQ := hgood.mono_start hnq
      have hsum0corr := hgoodQ.sum_Ico_corrected_nat_shift_le k r
      have hsum1corr := hgoodQ.sum_Ico_corrected_nat_shift_le
        (k + 1) (r + 1)
      have hsum0weak : (∑ j ∈ Finset.Ico k r, E j) ≤
          ∑ j ∈ Finset.Ico k r,
            scalarIdentityCorrectedWeakError aIdentity
              (printCertificateOrder g) ((q : ℤ) + (j : ℤ)) := by
        apply Finset.sum_le_sum
        intro j _
        have hE := scalarIdentityWeakError_nonneg aIdentity
          (printCertificateOrder g) ((q : ℤ) + (j : ℤ))
        dsimp only [E, scalarIdentityCorrectedWeakError]
        rw [Nat.cast_add]
        nlinarith only [hE]
      have hsum1weak : (∑ j ∈ Finset.Ico (k + 1) (r + 1), E j) ≤
          ∑ j ∈ Finset.Ico (k + 1) (r + 1),
            scalarIdentityCorrectedWeakError aIdentity
              (printCertificateOrder g) ((q : ℤ) + (j : ℤ)) := by
        apply Finset.sum_le_sum
        intro j _
        have hE := scalarIdentityWeakError_nonneg aIdentity
          (printCertificateOrder g) ((q : ℤ) + (j : ℤ))
        dsimp only [E, scalarIdentityCorrectedWeakError]
        rw [Nat.cast_add]
        nlinarith only [hE]
      have hsum0' : (∑ j ∈ Finset.Ico k r, E j) ≤
          (1 + delta) * delta :=
        hsum0weak.trans hsum0corr
      have hsum1' : (∑ j ∈ Finset.Ico (k + 1) (r + 1), E j) ≤
          (1 + delta) * delta :=
        hsum1weak.trans hsum1corr
      apply mul_le_mul_of_nonneg_right _ (euclideanNorm_nonneg e)
      apply mul_le_mul_of_nonneg_left _ hC.le
      linarith only [hsum0', hsum1']
    _ = (2 * C) * (1 + delta) * delta * euclideanNorm e := by ring

/-- A sufficiently small exact-gauge print-order tail simultaneously supplies
the joint limit, its equations, and its quantitative finite tail. -/
theorem exists_identityGaugeJointLimitWithTail
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation)
    (aGauge : CoeffSpace d) (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI aGauge).1 :
          CoeffField d))
    (delta : ℝ) (n : ℤ)
    (hdelta : delta ∈ Ioc (0 : ℝ)
      (identitySuccessorSmallness d g geom hg hdual))
    (hgood : ScalarIdentityGoodTail aIdentity
      (printCertificateOrder g) delta n) :
    ∃ Phi : Vec d → NormalizedLocalH1Carrier d,
      IsFiniteAffineCorrectionJointLocalEquation aIdentity Phi ∧
      ∀ (e : Vec d) (q m : ℕ), n ≤ (q : ℤ) → q + 3 ≤ m →
        Real.sqrt (normalizedLocalSymmetricEnergy
          (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
            (originCube d (q : ℤ)) aIdentity)
          (((show LocalGradientL2 d q from
                constantGradientOnOriginCube e (q : ℤ)) +
              (Phi e).gradientComponent q) -
            finiteAffineInnerGradientClass aIdentity e q (m - q))) ≤
          (2 * identitySuccessorEnergyConstant d g geom hg hdual) *
            (1 + delta) * delta * euclideanNorm e := by
  obtain ⟨Phi, hPhi, _⟩ := existsUnique_identityGaugeJointLocalEquation
    d g geom hg hdual aGauge hI aIdentity hIdentity delta n hdelta hgood
  refine ⟨Phi, hPhi, ?_⟩
  intro e q m hnq hqm
  exact identityGaugeJointWeightedTail d g geom hg hdual aGauge hI
    aIdentity hIdentity delta n hdelta hgood Phi hPhi e q m hnq hqm

end

end HighContrast
end HCPolySupport
