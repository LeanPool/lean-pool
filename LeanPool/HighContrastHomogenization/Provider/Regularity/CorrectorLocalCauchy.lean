/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorJointLimit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorTelescope
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSuccessorGradient
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.Energy

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorLocalCauchy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local Cauchy convergence of finite correctors

A scalar good tail makes the unshifted finite zero-trace corrections Cauchy
on every fixed centered cube.  The proof converts normalized coefficient
energy to the ordinary local Hilbert `L²` norm using the actual lower
ellipticity constant, then discards finitely many successor differences.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

private theorem norm_localGradientRestrict_le {d m n : ℕ}
    (hmn : m ≤ n) (g : LocalGradientL2 d n) :
    ‖localGradientRestrict hmn g‖ ≤ ‖g‖ := by
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  change ‖((Lp.memLp g).mono_measure hmu).toLp g‖ ≤ ‖g‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g)
    (eLpNorm_mono_measure g hmu)

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

private theorem norm_gradToHilbertVectorL2_le_energyNorm
    {d : ℕ} (Q : TriadicCube d) (a : Book.Ch03.CoeffFamily d)
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    ‖u.gradToHilbertVectorL2‖ ≤
      Real.sqrt (cubeVolume Q / (a.coeffOn Q).lam) *
        Book.Ch03.h1EnergyNormOnCube Q a u := by
  let b : CoeffField d := Book.Ch03.publicCoeffField Q a
  let lam : ℝ := (a.coeffOn Q).lam
  let E : ℝ := Book.Ch03.h1EnergyNormOnCube Q a u
  have hlam : 0 < lam := by
    simpa only [lam] using (a.coeffOn Q).lam_pos
  have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
  have hEll : IsEllipticFieldOn lam (a.coeffOn Q).Lam
      (openCubeSet Q) b := by
    simpa only [lam, b] using
      Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet Q a
  have hsqInt : IntegrableOn (fun x => vecNormSq (u.grad x))
      (openCubeSet Q) :=
    integrableOn_vecNormSq_h1Grad u
  have henergyInt : IntegrableOn
      (coefficientEnergyDensity b u.grad) (openCubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      hEll u.grad_memVectorL2
  have hmem : ∀ᵐ x ∂ volumeMeasureOn (openCubeSet Q),
      x ∈ openCubeSet Q := by
    exact (ae_restrict_iff' (measurableSet_openCubeSet Q)).2
      (_root_.Filter.Eventually.of_forall fun x hx => hx)
  have hpoint : ∀ᵐ x ∂ volumeMeasureOn (openCubeSet Q),
      lam * vecNormSq (u.grad x) ≤ coefficientEnergyDensity b u.grad x := by
    filter_upwards [hmem] with x hx
    exact lowerBound_symmPart_of_isEllipticMatrix
      (hEll.2 x hx) (u.grad x)
  have hlower :
      lam * ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume ≤
        ∫ x in openCubeSet Q, coefficientEnergyDensity b u.grad x ∂volume := by
    calc
      lam * ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume =
          ∫ x in openCubeSet Q, lam * vecNormSq (u.grad x) ∂volume := by
        rw [integral_const_mul]
      _ ≤ ∫ x in openCubeSet Q,
          coefficientEnergyDensity b u.grad x ∂volume :=
        integral_mono_ae (hsqInt.const_mul lam) henergyInt hpoint
  have hnormSq :
      ‖u.gradToHilbertVectorL2‖ ^ 2 =
        ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume := by
    calc
      ‖u.gradToHilbertVectorL2‖ ^ 2 =
          inner ℝ u.gradToHilbertVectorL2
            u.gradToHilbertVectorL2 := by
        exact (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x in openCubeSet Q, vecDot (u.grad x) (u.grad x) ∂volume :=
        inner_toHilbertVectorL2OfVecField_eq_integral
          u.grad_memVectorL2 u.grad_memVectorL2
      _ = ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume := rfl
  have havg : 0 ≤ cubeAverage Q
      (coefficientEnergyDensity b u.grad) := by
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      Q b u.grad
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q a)
  have henergySq : E ^ 2 =
      (cubeVolume Q)⁻¹ *
        ∫ x in openCubeSet Q,
          coefficientEnergyDensity b u.grad x ∂volume := by
    calc
      E ^ 2 = cubeAverage Q
          (coefficientEnergyDensity b u.grad) := by
        dsimp only [E]
        rw [
          Book.Ch03.h1EnergyNormOnCube_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
        ]
        exact Real.sq_sqrt havg
      _ = (cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q,
            coefficientEnergyDensity b u.grad x ∂volume := by
        rw [cubeAverage, setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  have henergyIntegral :
      ∫ x in openCubeSet Q, coefficientEnergyDensity b u.grad x ∂volume =
        cubeVolume Q * E ^ 2 := by
    rw [henergySq]
    field_simp [hvol.ne']
  have hE : 0 ≤ E := by
    dsimp only [E]
    unfold Book.Ch03.h1EnergyNormOnCube
    exact Real.sqrt_nonneg _
  have hsqDiv : ‖u.gradToHilbertVectorL2‖ ^ 2 ≤
      (cubeVolume Q * E ^ 2) / lam := by
    apply (le_div_iff₀ hlam).2
    calc
      ‖u.gradToHilbertVectorL2‖ ^ 2 * lam =
          lam * ‖u.gradToHilbertVectorL2‖ ^ 2 := by ring
      _ = lam *
          ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume := by
        rw [hnormSq]
      _ ≤ ∫ x in openCubeSet Q,
          coefficientEnergyDensity b u.grad x ∂volume := hlower
      _ = cubeVolume Q * E ^ 2 := henergyIntegral
  have hsq : ‖u.gradToHilbertVectorL2‖ ^ 2 ≤
      (cubeVolume Q / lam) * E ^ 2 := by
    calc
      ‖u.gradToHilbertVectorL2‖ ^ 2 ≤
          (cubeVolume Q * E ^ 2) / lam := hsqDiv
      _ = (cubeVolume Q / lam) * E ^ 2 := by ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hE)).1
  calc
    ‖u.gradToHilbertVectorL2‖ ^ 2 ≤
        (cubeVolume Q / lam) * E ^ 2 := hsq
    _ = (Real.sqrt (cubeVolume Q / lam) * E) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hvol.le hlam.le)]

/-- A normalized weighted-gradient bound gives an ordinary local Hilbert
`L²` bound, with the exact volume and lower-ellipticity conversion factor. -/
theorem norm_gradToHilbertVectorL2_le_sqrt_cubeVolume_div_lam_mul_of_weightedGradNorm_le
    {d : ℕ} (Q : TriadicCube d) (a : Book.Ch03.CoeffFamily d)
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (B : ℝ) (hB : 0 ≤ B)
    (hweighted :
      weightedGradNorm (a.coeffOn Q).toCoeffField
          (openCubeSet Q) u.grad ≤ ENNReal.ofReal B) :
    ‖u.gradToHilbertVectorL2‖ ≤
      Real.sqrt (cubeVolume Q / (a.coeffOn Q).lam) * B := by
  have henergy : Book.Ch03.h1EnergyNormOnCube Q a u ≤ B := by
    rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube] at hweighted
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 hweighted
  exact (norm_gradToHilbertVectorL2_le_energyNorm Q a u).trans
    (mul_le_mul_of_nonneg_left henergy (Real.sqrt_nonneg _))

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

/-- Small scalar good tails make the literal unshifted finite-corrector
sequence locally gradient-Cauchy for every boundary slope. -/
theorem exists_finiteAffineCorrectionLocalCauchyThreshold
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        FiniteAffineCorrectionLocalCauchy a := by
  obtain ⟨C, c, hC, hc, hsuccessor⟩ :=
    exists_finiteAffineSuccessorWeightedGradientEstimateConstant
      d s hs hs_lt
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood e q
  let r : ℕ := max q n.toNat
  have hqr : q ≤ r := Nat.le_max_left q n.toNat
  have hnr : n ≤ (r : ℤ) := by
    exact (Int.self_le_toNat n).trans
      (Int.ofNat_le.mpr (Nat.le_max_right q n.toNat))
  let K : ℕ := r - q + 2
  have hqK : q + K = r + 2 := by
    dsimp only [K]
    omega
  let g : ℕ → LocalGradientL2 d q := fun k =>
    (normalizedLocalH1
      (finiteAffineCorrectionLocalSequence a e) q k).gradToHilbertVectorL2
  let E : ℕ → ℝ := fun j =>
    scalarIdentityCorrectedWeakError a s ((r : ℤ) + (j : ℤ))
  let eps : ℕ → ℝ := fun j => E (j + 2) + E (j + 3)
  have hgoodR : ScalarIdentityGoodTail a s delta (r : ℤ) :=
    hgood.mono_start hnr
  have hEsum : Summable E := by
    simpa only [E] using hgoodR.summable_corrected_nat_shift
  have hepsSum : Summable eps := by
    have htwo : Summable (fun j => E (j + 2)) :=
      (summable_nat_add_iff 2).2 hEsum
    have hthree : Summable (fun j => E (j + 3)) :=
      (summable_nat_add_iff 3).2 hEsum
    simpa only [eps] using htwo.add hthree
  let D : ℝ :=
    Real.sqrt
        (cubeVolume (originCube d (r : ℤ)) /
          (a.coeffOn (originCube d (r : ℤ))).lam) * C
  have hstep : ∀ j,
      ‖g (j + 1 + K) - g (j + K)‖ ≤
        D * eps j * euclideanNorm e := by
    intro j
    let m : ℤ := ((q + (j + K) : ℕ) : ℤ)
    have hm : m = (r : ℤ) + ((j + 2 : ℕ) : ℤ) := by
      dsimp only [m]
      omega
    have hrm : (r : ℤ) ≤ m := by omega
    have htwoScale : (r : ℤ) ≤ m - 2 := by omega
    have hinterval :
        ScalarIdentityGoodTailOnInterval a s delta (r : ℤ) (m + 1) :=
      (hgood.interval (by omega)).mono_start hnr
    let w : Book.Ch03.CubeSolution (originCube d (r : ℤ)) a :=
      finiteCubeSolutionRestriction a hrm
        (finiteAffineSuccessorDifference a m e)
    let B : ℝ := C *
      (scalarIdentityCorrectedWeakError a s m +
        scalarIdentityCorrectedWeakError a s (m + 1)) *
          euclideanNorm e
    have hB : 0 ≤ B := by
      dsimp only [B]
      exact mul_nonneg
        (mul_nonneg hC.le
          (add_nonneg
            (scalarIdentityCorrectedWeakError_nonneg a s m)
            (scalarIdentityCorrectedWeakError_nonneg a s (m + 1))))
        (euclideanNorm_nonneg e)
    have hweighted :
        weightedGradNorm
            (a.coeffOn (originCube d (r : ℤ))).toCoeffField
            (openCubeSet (originCube d (r : ℤ))) w.toH1.grad ≤
          ENNReal.ofReal B := by
      simpa only [w, B, finiteCubeSolutionRestriction_grad] using
        hsuccessor a delta (r : ℤ) m e hdelta htwoScale hinterval
    have hwNorm : ‖w.toH1.gradToHilbertVectorL2‖ ≤
        Real.sqrt
            (cubeVolume (originCube d (r : ℤ)) /
              (a.coeffOn (originCube d (r : ℤ))).lam) * B :=
      norm_gradToHilbertVectorL2_le_sqrt_cubeVolume_div_lam_mul_of_weightedGradNorm_le
        (originCube d (r : ℤ)) a w.toH1 B hB hweighted
    have hclass :
        g (j + 1 + K) - g (j + K) =
          localGradientRestrict hqr w.toH1.gradToHilbertVectorL2 := by
      have hkone : j + 1 + K = (j + K) + 1 := by omega
      rw [hkone]
      simpa only [g, m, w] using
        normalizedFiniteCorrection_successor_gradient_eq
          a e q (j + K) r hqr hrm
    calc
      ‖g (j + 1 + K) - g (j + K)‖ =
          ‖localGradientRestrict hqr w.toH1.gradToHilbertVectorL2‖ := by
        rw [hclass]
      _ ≤ ‖w.toH1.gradToHilbertVectorL2‖ :=
        norm_localGradientRestrict_le hqr _
      _ ≤ Real.sqrt
            (cubeVolume (originCube d (r : ℤ)) /
              (a.coeffOn (originCube d (r : ℤ))).lam) * B := hwNorm
      _ = D * eps j * euclideanNorm e := by
        dsimp only [D, B, eps, E]
        rw [hm]
        have hmone :
            (r : ℤ) + ((j + 2 : ℕ) : ℤ) + 1 =
              (r : ℤ) + ((j + 3 : ℕ) : ℤ) := by omega
        rw [hmone]
        ring
  have hshift : CauchySeq (fun j => g (j + K)) :=
    localGradientL2_cauchySeq_of_summable_successive_norm_le
      (fun j => g (j + K)) eps D e hepsSum (by
        intro j
        simpa only [add_assoc] using hstep j)
  exact (cauchySeq_shift K).1 hshift

end

end HighContrast
end HCPolySupport
