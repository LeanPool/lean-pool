/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1WeightedCorrectorProjection
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSuccessorGradient

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1QuantitativeCorrectorTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quantitative coefficient-energy tail of finite correctors

The finite-successor estimate is telescoped in the symmetric coefficient
energy itself.  The fixed-cube joint limit then retains the same bound,
without conversion through a lower ellipticity constant.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory

noncomputable section

theorem sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    (u : H1Function U) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll
      u.gradToHilbertVectorL2) =
      (weightedGradNorm b U u.grad).toReal := by
  let W := weightedGradNorm b U u.grad
  have henergy : ENNReal.ofReal
        (normalizedLocalSymmetricEnergy hEll u.gradToHilbertVectorL2) =
      weightedGradNorm b U u.grad ^ 2 := by
    simpa only [H1Function.gradToHilbertVectorL2] using
      ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq
        hEll u.grad_memVectorL2
  have hEnonneg := normalizedLocalSymmetricEnergy_nonneg
    hEll u.gradToHilbertVectorL2
  have hsq : normalizedLocalSymmetricEnergy hEll u.gradToHilbertVectorL2 =
      W.toReal ^ 2 := by
    have hreal := congrArg ENNReal.toReal henergy
    simpa only [ENNReal.toReal_ofReal hEnonneg, ENNReal.toReal_pow, W] using hreal
  rw [hsq, Real.sqrt_sq ENNReal.toReal_nonneg]

private theorem sqrt_normalizedEnergy_grad_le_of_weightedGradNorm_le
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam B : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    (u : H1Function U) (hB : 0 ≤ B)
    (hweighted : weightedGradNorm b U u.grad ≤ ENNReal.ofReal B) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll
      u.gradToHilbertVectorL2) ≤ B := by
  rw [sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal hEll u]
  have hrealWeighted := ENNReal.toReal_mono ENNReal.ofReal_ne_top hweighted
  simpa only [ENNReal.toReal_ofReal hB] using hrealWeighted

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
  apply MeasureTheory.Lp.ext
  filter_upwards [u1.coeFn_gradToHilbertVectorL2,
      u0.coeFn_gradToHilbertVectorL2,
      w.toH1.coeFn_gradToHilbertVectorL2,
      MeasureTheory.Lp.coeFn_sub u1.gradToHilbertVectorL2
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

private theorem sqrt_finiteAffineInnerGradientClass_succ_sub_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hweighted : weightedGradNorm
      (a.coeffOn (originCube d (q : ℤ))).toCoeffField
      (openCubeSet (originCube d (q : ℤ)))
      (finiteAffineSuccessorDifference a ((q + j : ℕ) : ℤ) e).toH1.grad ≤
        ENNReal.ofReal B) :
    Real.sqrt (normalizedLocalSymmetricEnergy
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)
      (finiteAffineInnerGradientClass a e q (j + 1) -
        finiteAffineInnerGradientClass a e q j)) ≤ B := by
  rw [finiteAffineInnerGradientClass_succ_sub_eq]
  apply sqrt_normalizedEnergy_grad_le_of_weightedGradNorm_le
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a) _ hB
  rw [finiteCubeSolutionRestriction_grad]
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      (originCube d (q : ℤ)) a)]
  exact hweighted

/-- The joint affine corrector is quantitatively close, on every fixed inner
cube, to every finite affine corrector at least two generations outside it. -/
theorem exists_jointFiniteCorrectorWeightedTailConstants
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n0 : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n0 →
        ∀ Phi : Vec d → NormalizedLocalH1Carrier d,
          IsFiniteAffineCorrectionJointLocalEquation a Phi →
          ∀ (e : Vec d) (q m : ℕ), n0 ≤ (q : ℤ) → q + 2 ≤ m →
          Real.sqrt (normalizedLocalSymmetricEnergy
            (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
              (originCube d (q : ℤ)) a)
            (((show LocalGradientL2 d q from
                  constantGradientOnOriginCube e (q : ℤ)) +
                (Phi e).gradientComponent q) -
              finiteAffineInnerGradientClass a e q (m - q))) ≤
            C * (1 + delta) * delta * euclideanNorm e := by
  obtain ⟨Cstep, c, hCstep, hc, hstep⟩ :=
    exists_finiteAffineSuccessorWeightedGradientEstimateConstant
      d s hs hs_lt
  let C : ℝ := 2 * Cstep
  have hC : 0 < C := mul_pos (by norm_num) hCstep
  refine ⟨C, c, hC, hc, ?_⟩
  intro a delta n0 hdelta hgood Phi hPhi e q m hnq hqm2
  have hgoodQ : ScalarIdentityGoodTail a s delta (q : ℤ) :=
    hgood.mono_start hnq
  let k : ℕ := m - q
  have hk2 : 2 ≤ k := by dsimp only [k]; omega
  have hqk : q + k = m := by dsimp only [k]; omega
  apply sqrt_jointLocalGradient_sub_finiteAffine_le_of_uniform_tail
    a Phi hPhi e q k (C * (1 + delta) * delta * euclideanNorm e)
  intro r hkr
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) a
  have hvol : 0 < volume (localGradientCube d q) := by
    have hreal := volume_openCubeSet_originCube_toReal_pos (d := d) (q : ℤ)
    exact (ENNReal.toReal_pos_iff.mp (by simpa only [localGradientCube] using hreal)).1
  have hvoltop : volume (localGradientCube d q) ≠ ⊤ := by
    simpa only [localGradientCube] using
      (volume_openCubeSet_lt_top (originCube d (q : ℤ))).ne
  have htelescope := sqrt_normalizedLocalSymmetricEnergy_sub_le_sum_Ico
    hEll hvol hvoltop (finiteAffineInnerGradientClass a e q) k r hkr
  refine htelescope.trans ?_
  let E : ℕ → ℝ := fun j ↦
    scalarIdentityCorrectedWeakError a s ((q + j : ℕ) : ℤ)
  have hterm : ∀ j ∈ Finset.Ico k r,
      Real.sqrt (normalizedLocalSymmetricEnergy hEll
        (finiteAffineInnerGradientClass a e q (j + 1) -
          finiteAffineInnerGradientClass a e q j)) ≤
        Cstep * (E j + E (j + 1)) * euclideanNorm e := by
    intro j hj
    have hkj : k ≤ j := (Finset.mem_Ico.mp hj).1
    have hqj2 : (q : ℤ) ≤ ((q + j : ℕ) : ℤ) - 2 := by
      have : 2 ≤ j := hk2.trans hkj
      omega
    have hinterval : ScalarIdentityGoodTailOnInterval a s delta
        (q : ℤ) (((q + j : ℕ) : ℤ) + 1) :=
      hgoodQ.interval (by omega)
    have hsuc := hstep a delta (q : ℤ) ((q + j : ℕ) : ℤ) e
      hdelta hqj2 hinterval
    let Bj : ℝ := Cstep *
      (scalarIdentityCorrectedWeakError a s ((q + j : ℕ) : ℤ) +
        scalarIdentityCorrectedWeakError a s (((q + j : ℕ) : ℤ) + 1)) *
      euclideanNorm e
    have hBj : 0 ≤ Bj := by
      dsimp only [Bj]
      exact mul_nonneg
        (mul_nonneg hCstep.le
          (add_nonneg
            (scalarIdentityCorrectedWeakError_nonneg a s ((q + j : ℕ) : ℤ))
            (scalarIdentityCorrectedWeakError_nonneg a s
              (((q + j : ℕ) : ℤ) + 1))))
        (euclideanNorm_nonneg e)
    have hlocal := sqrt_finiteAffineInnerGradientClass_succ_sub_le
      a e q j Bj hBj hsuc
    simpa only [Bj, E, show (((q + j : ℕ) : ℤ) + 1) =
      ((q + (j + 1) : ℕ) : ℤ) by omega] using hlocal
  calc
    ∑ j ∈ Finset.Ico k r,
        Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (finiteAffineInnerGradientClass a e q (j + 1) -
            finiteAffineInnerGradientClass a e q j)) ≤
        ∑ j ∈ Finset.Ico k r,
          Cstep * (E j + E (j + 1)) * euclideanNorm e := by
            exact Finset.sum_le_sum hterm
    _ = Cstep *
          ((∑ j ∈ Finset.Ico k r, E j) +
            (∑ j ∈ Finset.Ico k r, E (j + 1))) *
          euclideanNorm e := by
      calc
        _ = ∑ j ∈ Finset.Ico k r,
            (Cstep * E j * euclideanNorm e +
              Cstep * E (j + 1) * euclideanNorm e) := by
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = (∑ j ∈ Finset.Ico k r, Cstep * E j * euclideanNorm e) +
            (∑ j ∈ Finset.Ico k r,
              Cstep * E (j + 1) * euclideanNorm e) :=
                Finset.sum_add_distrib
        _ = _ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
    _ = Cstep *
          ((∑ j ∈ Finset.Ico k r, E j) +
            (∑ j ∈ Finset.Ico (k + 1) (r + 1), E j)) *
          euclideanNorm e := by
      have hshift : (∑ j ∈ Finset.Ico k r, E (j + 1)) =
          ∑ j ∈ Finset.Ico (k + 1) (r + 1), E j := by
        simpa only [Nat.add_comm] using
          (Finset.sum_Ico_add E k r 1)
      rw [hshift]
    _ ≤ Cstep * (2 * ((1 + delta) * delta)) * euclideanNorm e := by
      have hsum0 := hgoodQ.sum_Ico_corrected_nat_shift_le k r
      have hsum1 := hgoodQ.sum_Ico_corrected_nat_shift_le (k + 1) (r + 1)
      have hsum0' : (∑ j ∈ Finset.Ico k r, E j) ≤
          (1 + delta) * delta := by
        simpa only [E, Nat.cast_add] using hsum0
      have hsum1' : (∑ j ∈ Finset.Ico (k + 1) (r + 1), E j) ≤
          (1 + delta) * delta := by
        simpa only [E, Nat.cast_add] using hsum1
      have hnonneg : 0 ≤ Cstep := hCstep.le
      have hnorm : 0 ≤ euclideanNorm e := euclideanNorm_nonneg e
      apply mul_le_mul_of_nonneg_right _ hnorm
      apply mul_le_mul_of_nonneg_left _ hnonneg
      nlinarith only [hsum0', hsum1']
    _ = C * (1 + delta) * delta * euclideanNorm e := by
      dsimp only [C]
      ring

end

end Root
end HighContrast
end HCPolySupport
