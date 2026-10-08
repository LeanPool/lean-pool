/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentitySuccessorTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalCauchy

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.PrintOrderLocalCauchy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

private theorem norm_localGradientRestrict_le {d m n : ℕ}
    (hmn : m ≤ n) (f : LocalGradientL2 d n) :
    ‖localGradientRestrict hmn f‖ ≤ ‖f‖ := by
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  change ‖((Lp.memLp f).mono_measure hmu).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure f hmu)

private theorem gradToHilbertVectorL2_eq_of_grad_eq {d : ℕ}
    {U : Set (Vec d)} (u v : H1Function U) (hgrad : u.grad = v.grad) :
    u.gradToHilbertVectorL2 = v.gradToHilbertVectorL2 := by
  apply Lp.ext
  filter_upwards
      [u.coeFn_gradToHilbertVectorL2,
        v.coeFn_gradToHilbertVectorL2]
    with x hu hv
  rw [hu, hv, hgrad]

private theorem gradToHilbertVectorL2_sub {d : ℕ} {U : Set (Vec d)}
    (u v : H1Function U) :
    (u - v).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 := by
  rw [sub_eq_add_neg, H1Function.gradToHilbertVectorL2_add]
  have hneg := H1Function.gradToHilbertVectorL2_smul (-1 : ℝ) v
  rw [show (-v : H1Function U) = (-1 : ℝ) • v by rfl, hneg]
  simp only [neg_smul, one_smul, sub_eq_add_neg]

private theorem normalizedLocalH1_finiteAffineCorrection_grad
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) :
    (normalizedLocalH1
      (finiteAffineCorrectionLocalSequence a e) q k).grad =
        (finiteAffineCorrectionLocalSequence a e (q + k)).grad := by
  funext x
  change
    (normalizeOnUnitCube
      (finiteAffineCorrectionLocalSequence a e (q + k))).grad x =
        (finiteAffineCorrectionLocalSequence a e (q + k)).grad x
  rw [normalizeOnUnitCube_grad]

private theorem normalizedFiniteCorrection_successor_gradient_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k r : ℕ) (hqr : q ≤ r)
    (hrm : (r : ℤ) ≤ ((q + k : ℕ) : ℤ)) :
    (normalizedLocalH1
          (finiteAffineCorrectionLocalSequence a e) q
          (k + 1)).gradToHilbertVectorL2 -
        (normalizedLocalH1
          (finiteAffineCorrectionLocalSequence a e) q k).gradToHilbertVectorL2 =
      localGradientRestrict hqr
        (finiteCubeSolutionRestriction a hrm
          (finiteAffineSuccessorDifference a
            ((q + k : ℕ) : ℤ) e)).toH1.gradToHilbertVectorL2 := by
  let w : H1Function (localGradientCube d r) :=
    Eq.mp (by simp only [localGradientCube, Book.Ch02.cubeDomain_coe])
      (finiteCubeSolutionRestriction a hrm
        (finiteAffineSuccessorDifference a ((q + k : ℕ) : ℤ) e)).toH1
  change _ = localGradientRestrict hqr w.gradToHilbertVectorL2
  rw [← gradToHilbertVectorL2_sub,
    localGradientRestrict_gradToHilbertVectorL2_restrictLocalH1]
  apply gradToHilbertVectorL2_eq_of_grad_eq
  funext x
  rw [H1Function.sub_grad,
    normalizedLocalH1_finiteAffineCorrection_grad,
    normalizedLocalH1_finiteAffineCorrection_grad]
  change _ = w.grad x
  have hwgrad : w.grad x =
      (finiteCubeSolutionRestriction a hrm
        (finiteAffineSuccessorDifference a ((q + k : ℕ) : ℤ) e)).toH1.grad x := rfl
  rw [hwgrad, finiteCubeSolutionRestriction_grad,
    finiteAffineSuccessorDifference_grad]
  have hindex : ((q + (k + 1) : ℕ) : ℤ) =
      ((q + k : ℕ) : ℤ) + 1 := by omega
  change
    (finiteAffineCorrection a
          ((q + (k + 1) : ℕ) : ℤ) e).toH1Function.grad x -
        (finiteAffineCorrection a
          ((q + k : ℕ) : ℤ) e).toH1Function.grad x =
      (finiteAffineCubeSolution a
          (((q + k : ℕ) : ℤ) + 1) e).toH1.grad x -
        (finiteAffineCubeSolution a
          ((q + k : ℕ) : ℤ) e).toH1.grad x
  rw [hindex]
  simp only [finiteAffineCubeSolution, finiteAffineSolution_toH1,
    H1Function.add_grad, finiteAffineBoundaryH1_grad]
  abel

theorem successorInner_energy_eq_direct_restriction
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m r : ℤ) (e : Vec d) (hr : r ≤ m - 1 - 2) :
    finiteCenteredCubeSolutionEnergy a (m - 1 - 2)
        (successorInnerRestriction a m e) r =
      Book.Ch03.h1EnergyNormOnCube (originCube d r) a
        (finiteCubeSolutionRestriction a (by omega : r ≤ m)
          (finiteAffineSuccessorDifference a m e)).toH1 := by
  rw [finiteCenteredCubeSolutionEnergy_eq_of_le a (m - 1 - 2)
    (successorInnerRestriction a m e) r hr]
  unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.localizedCoeffEnergyValue
  simp only [finiteCubeSolutionRestriction_grad,
    successorInnerRestriction]

/-- At the printed order, the exact identity-gauge successor estimate makes
the literal finite-corrector sequence locally Cauchy. -/
theorem identityGaugeFiniteCorrectionLocalCauchy
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
    FiniteAffineCorrectionLocalCauchy aIdentity := by
  let C := identitySuccessorEnergyConstant d g geom hg hdual
  have hC : 0 < C := identitySuccessorEnergyConstant_pos
    d g geom hg hdual
  have hsuccessor := identityGaugeSuccessorEnergy_le
    d g geom hg hdual aGauge hI aIdentity hIdentity
  intro e q
  let r : ℕ := max q n.toNat
  have hqr : q ≤ r := Nat.le_max_left q n.toNat
  have hnr : n ≤ (r : ℤ) := by
    exact (Int.self_le_toNat n).trans
      (Int.ofNat_le.mpr (Nat.le_max_right q n.toNat))
  let K : ℕ := r - q + 3
  have hqK : q + K = r + 3 := by
    dsimp only [K]
    omega
  let G : ℕ → LocalGradientL2 d q := fun k =>
    (normalizedLocalH1
      (finiteAffineCorrectionLocalSequence aIdentity e) q k).gradToHilbertVectorL2
  let E : ℕ → ℝ := fun j =>
    scalarIdentityWeakError aIdentity (printCertificateOrder g)
      ((r : ℤ) + (j : ℤ))
  let eps : ℕ → ℝ := fun j => E (j + 3) + E (j + 4)
  have hgoodR : ScalarIdentityGoodTail aIdentity
      (printCertificateOrder g) delta (r : ℤ) :=
    hgood.mono_start hnr
  have hEsum : Summable E := by
    simpa only [E] using hgoodR.summable_nat_shift
  have hepsSum : Summable eps := by
    have hthree : Summable (fun j => E (j + 3)) :=
      (summable_nat_add_iff 3).2 hEsum
    have hfour : Summable (fun j => E (j + 4)) :=
      (summable_nat_add_iff 4).2 hEsum
    simpa only [eps] using hthree.add hfour
  let D : ℝ :=
    Real.sqrt
        (cubeVolume (originCube d (r : ℤ)) /
          (aIdentity.coeffOn (originCube d (r : ℤ))).lam) * C
  have hstep : ∀ j,
      ‖G (j + 1 + K) - G (j + K)‖ ≤
        D * eps j * euclideanNorm e := by
    intro j
    let m : ℤ := ((q + (j + K) : ℕ) : ℤ)
    have hm : m = (r : ℤ) + ((j + 3 : ℕ) : ℤ) := by
      dsimp only [m]
      omega
    have hrm : (r : ℤ) ≤ m := by omega
    have hthreeScale : (r : ℤ) ≤ m - 1 - 2 := by omega
    have hinterval : ScalarIdentityGoodTailOnInterval aIdentity
        (printCertificateOrder g) delta (r : ℤ) (m + 1) :=
      hgoodR.interval (by omega)
    let w : Book.Ch03.CubeSolution (originCube d (r : ℤ)) aIdentity :=
      finiteCubeSolutionRestriction aIdentity hrm
        (finiteAffineSuccessorDifference aIdentity m e)
    let B : ℝ := C *
      (scalarIdentityWeakError aIdentity (printCertificateOrder g) m +
        scalarIdentityWeakError aIdentity
          (printCertificateOrder g) (m + 1)) * euclideanNorm e
    have hB : 0 ≤ B := by
      dsimp only [B]
      exact mul_nonneg
        (mul_nonneg hC.le
          (add_nonneg
            (scalarIdentityWeakError_nonneg aIdentity
              (printCertificateOrder g) m)
            (scalarIdentityWeakError_nonneg aIdentity
              (printCertificateOrder g) (m + 1))))
        (euclideanNorm_nonneg e)
    have henergy : Book.Ch03.h1EnergyNormOnCube
        (originCube d (r : ℤ)) aIdentity w.toH1 ≤ B := by
      have hsuc := hsuccessor delta (r : ℤ) (r : ℤ) m e hdelta
        (le_refl _) hthreeScale hinterval
      rw [successorInner_energy_eq_direct_restriction
        aIdentity m (r : ℤ) e hthreeScale] at hsuc
      simpa only [w, B] using hsuc
    have hweighted : weightedGradNorm
        (aIdentity.coeffOn (originCube d (r : ℤ))).toCoeffField
        (openCubeSet (originCube d (r : ℤ))) w.toH1.grad ≤
          ENNReal.ofReal B := by
      rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
      exact ENNReal.ofReal_le_ofReal henergy
    have hwNorm : ‖w.toH1.gradToHilbertVectorL2‖ ≤
        Real.sqrt
            (cubeVolume (originCube d (r : ℤ)) /
              (aIdentity.coeffOn (originCube d (r : ℤ))).lam) * B :=
      norm_gradToHilbertVectorL2_le_sqrt_cubeVolume_div_lam_mul_of_weightedGradNorm_le
        (originCube d (r : ℤ)) aIdentity w.toH1 B hB hweighted
    have hclass :
        G (j + 1 + K) - G (j + K) =
          localGradientRestrict hqr w.toH1.gradToHilbertVectorL2 := by
      have hkone : j + 1 + K = (j + K) + 1 := by omega
      rw [hkone]
      simpa only [G, m, w] using
        normalizedFiniteCorrection_successor_gradient_eq
          aIdentity e q (j + K) r hqr hrm
    calc
      ‖G (j + 1 + K) - G (j + K)‖ =
          ‖localGradientRestrict hqr w.toH1.gradToHilbertVectorL2‖ := by
        rw [hclass]
      _ ≤ ‖w.toH1.gradToHilbertVectorL2‖ :=
        norm_localGradientRestrict_le hqr _
      _ ≤ Real.sqrt
            (cubeVolume (originCube d (r : ℤ)) /
              (aIdentity.coeffOn (originCube d (r : ℤ))).lam) * B := hwNorm
      _ = D * eps j * euclideanNorm e := by
        dsimp only [D, B, eps, E]
        rw [hm]
        have hmone :
            (r : ℤ) + ((j + 3 : ℕ) : ℤ) + 1 =
              (r : ℤ) + ((j + 4 : ℕ) : ℤ) := by omega
        rw [hmone]
        ring
  have hshift : CauchySeq (fun j => G (j + K)) :=
    localGradientL2_cauchySeq_of_summable_successive_norm_le
      (fun j => G (j + K)) eps D e hepsSum (by
        intro j
        simpa only [add_assoc] using hstep j)
  exact (cauchySeq_shift K).1 hshift

end

end HighContrast
end HCPolySupport
