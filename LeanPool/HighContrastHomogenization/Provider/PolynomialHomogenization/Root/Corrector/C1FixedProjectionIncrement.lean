/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FixedProjectionDecayCore
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1QuantitativeCorrectorTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineBestFitEnergyGrowth

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1FixedProjectionIncrement

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Propagation of consecutive exact-minimizer increments

The difference of two consecutive residuals is the finite affine solution
with the difference slope.  Its coefficient energy at the smaller scale is
therefore bounded by the two minimizing residual energies, and the available
fixed-boundary growth theorem propagates that bound to any later observation
scale.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory

noncomputable section

theorem normalizedLocalSymmetricEnergy_neg_increment
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b) (F : HilbertVectorL2 U) :
    normalizedLocalSymmetricEnergy hEll (-F) =
      normalizedLocalSymmetricEnergy hEll F := by
  unfold normalizedLocalSymmetricEnergy
  rw [map_neg, inner_neg_left, inner_neg_right]
  ring

theorem sqrt_normalizedLocalSymmetricEnergy_neg_increment
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b) (F : HilbertVectorL2 U) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (-F)) =
      Real.sqrt (normalizedLocalSymmetricEnergy hEll F) := by
  rw [normalizedLocalSymmetricEnergy_neg_increment]

private theorem sqrt_normalizedLocalSymmetricEnergy_sub_le_increment
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    (hvol : 0 < volume U) (hvoltop : volume U ≠ ⊤)
    (F G : HilbertVectorL2 U) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (F - G)) ≤
      Real.sqrt (normalizedLocalSymmetricEnergy hEll F) +
        Real.sqrt (normalizedLocalSymmetricEnergy hEll G) := by
  rw [sub_eq_add_neg]
  have hraw := sqrt_normalizedLocalSymmetricEnergy_add_le
    hEll hvol hvoltop F (-G)
  rw [normalizedLocalSymmetricEnergy_neg_increment] at hraw
  exact hraw

private theorem sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k : ℤ) (u : H1Function (openCubeSet (originCube d k))) :
    Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d k) a) u.gradToHilbertVectorL2) =
      Book.Ch03.h1EnergyNormOnCube (originCube d k) a u := by
  rw [sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal]
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet (originCube d k) a)]
  erw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
  rw [ENNReal.toReal_ofReal]
  unfold Book.Ch03.h1EnergyNormOnCube
  exact Real.sqrt_nonneg _

private theorem residual_energy_eq_excess_toReal_increment
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {k m : ℤ} (hkm : k ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (b : Vec d)
    (hb : weightedGradNorm
          (a.coeffOn (originCube d k)).toCoeffField
          (openCubeSet (originCube d k))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m b).toH1.grad x) =
        finiteAffineGradientExcess a k m u) :
    Book.Ch03.h1EnergyNormOnCube (originCube d k) a
        (finiteAffineGradientResidual a hkm u b).toH1 =
      (finiteAffineGradientExcess a k m u).toReal := by
  have hbridge := weightedGradNorm_finiteAffineGradientResidual
    a hkm u b
  rw [hb] at hbridge
  have henergy : 0 ≤ Book.Ch03.h1EnergyNormOnCube (originCube d k) a
      (finiteAffineGradientResidual a hkm u b).toH1 := by
    unfold Book.Ch03.h1EnergyNormOnCube
    positivity
  calc
    Book.Ch03.h1EnergyNormOnCube (originCube d k) a
        (finiteAffineGradientResidual a hkm u b).toH1 =
        (ENNReal.ofReal
          (Book.Ch03.h1EnergyNormOnCube (originCube d k) a
            (finiteAffineGradientResidual a hkm u b).toH1)).toReal := by
      rw [ENNReal.toReal_ofReal henergy]
    _ = (finiteAffineGradientExcess a k m u).toReal := by rw [hbridge]

private theorem finiteAffineDifference_gradClass_eq_residual_sub
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {j m : ℤ} (hjm : j ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (b0 b1 : Vec d) :
    (finiteCubeSolutionRestriction a hjm
        (finiteAffineCubeSolution a m (b0 - b1))).toH1.gradToHilbertVectorL2 =
      (finiteAffineGradientResidual a hjm u b1).toH1.gradToHilbertVectorL2 -
        (finiteAffineGradientResidual a hjm u b0).toH1.gradToHilbertVectorL2 := by
  let w := finiteCubeSolutionRestriction a hjm
    (finiteAffineCubeSolution a m (b0 - b1))
  let r0 := finiteAffineGradientResidual a hjm u b0
  let r1 := finiteAffineGradientResidual a hjm u b1
  have hsub : openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le hjm
  have hadd := ae_mono (Measure.restrict_mono hsub (le_refl volume))
    (finiteAffineSolution_grad_add a m b0 (-b1))
  have hneg := ae_mono (Measure.restrict_mono hsub (le_refl volume))
    (finiteAffineSolution_grad_smul a m (-1 : ℝ) b1)
  apply MeasureTheory.Lp.ext
  filter_upwards [w.toH1.coeFn_gradToHilbertVectorL2,
      r0.toH1.coeFn_gradToHilbertVectorL2,
      r1.toH1.coeFn_gradToHilbertVectorL2,
      MeasureTheory.Lp.coeFn_sub r1.toH1.gradToHilbertVectorL2
        r0.toH1.gradToHilbertVectorL2,
      hadd, hneg] with x hw hr0 hr1 hsubcoe haddx hnegx
  rw [hw, hsubcoe, Pi.sub_apply, hr1, hr0]
  simp only [w, r0, r1, finiteCubeSolutionRestriction_grad,
    finiteAffineGradientResidual_grad]
  have hnegx' : (finiteAffineSolution a m (-b1)).toH1.grad x =
      -(finiteAffineSolution a m b1).toH1.grad x := by
    simpa only [neg_smul, one_smul] using hnegx
  change WithLp.toLp 2 _ = WithLp.toLp 2 _ - WithLp.toLp 2 _
  rw [← WithLp.toLp_sub]
  congr 1
  change (finiteAffineSolution a m (b0 + -b1)).toH1.grad x = _
  rw [haddx, hnegx']
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
  ring

/-- At the smaller of two consecutive minimizer scales, the finite affine
increment has energy bounded by the two residual energies. -/
theorem finiteAffineDifferenceEnergy_le_exactResiduals
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {j m : ℤ} (hjm : j ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (b0 b1 : Vec d)
    (hb0 : weightedGradNorm
          (a.coeffOn (originCube d j)).toCoeffField
          (openCubeSet (originCube d j))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m b0).toH1.grad x) =
        finiteAffineGradientExcess a j m u)
    (hb1j : Book.Ch03.h1EnergyNormOnCube (originCube d j) a
        (finiteAffineGradientResidual a hjm u b1).toH1 ≤
      ((3 ^ d : ℕ) : ℝ) *
        (finiteAffineGradientExcess a (j + 1) m u).toReal) :
    finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m (b0 - b1)) j ≤
      (finiteAffineGradientExcess a j m u).toReal +
        ((3 ^ d : ℕ) : ℝ) *
          (finiteAffineGradientExcess a (j + 1) m u).toReal := by
  let w := finiteCubeSolutionRestriction a hjm
    (finiteAffineCubeSolution a m (b0 - b1))
  let r0 := finiteAffineGradientResidual a hjm u b0
  let r1 := finiteAffineGradientResidual a hjm u b1
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d j) a
  have hvol : 0 < volume (openCubeSet (originCube d j)) := by
    exact (ENNReal.toReal_pos_iff.mp
      (volume_openCubeSet_originCube_toReal_pos (d := d) j)).1
  have hvoltop : volume (openCubeSet (originCube d j)) ≠ ⊤ :=
    (volume_openCubeSet_lt_top (originCube d j)).ne
  have hclass : w.toH1.gradToHilbertVectorL2 =
      r1.toH1.gradToHilbertVectorL2 - r0.toH1.gradToHilbertVectorL2 := by
    simpa only [w, r0, r1] using
      finiteAffineDifference_gradClass_eq_residual_sub a hjm u b0 b1
  have htri := sqrt_normalizedLocalSymmetricEnergy_sub_le_increment
    hEll hvol hvoltop r1.toH1.gradToHilbertVectorL2
      r0.toH1.gradToHilbertVectorL2
  erw [← hclass,
    sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube,
    sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube,
    sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube] at htri
  have hE0 := residual_energy_eq_excess_toReal_increment
    a hjm u b0 hb0
  rw [hE0] at htri
  rw [finiteCenteredCubeSolutionEnergy_eq_of_le a m
    (finiteAffineCubeSolution a m (b0 - b1)) j hjm]
  calc
    Book.Ch03.h1EnergyNormOnCube (originCube d j) a w.toH1 ≤
        Book.Ch03.h1EnergyNormOnCube (originCube d j) a r1.toH1 +
          (finiteAffineGradientExcess a j m u).toReal := htri
    _ ≤ ((3 ^ d : ℕ) : ℝ) *
          (finiteAffineGradientExcess a (j + 1) m u).toReal +
        (finiteAffineGradientExcess a j m u).toReal :=
      add_le_add hb1j le_rfl
    _ = _ := by ring

/-- The previous residual at scale `j+1`, restricted to its centered child,
has the standard normalized-volume loss. -/
theorem residualEnergy_at_predecessor_le_exactSuccessor
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {j m : ℤ} (hjm : j + 1 ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (b1 : Vec d)
    (hb1 : weightedGradNorm
          (a.coeffOn (originCube d (j + 1))).toCoeffField
          (openCubeSet (originCube d (j + 1)))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m b1).toH1.grad x) =
        finiteAffineGradientExcess a (j + 1) m u) :
    Book.Ch03.h1EnergyNormOnCube (originCube d j) a
        (finiteAffineGradientResidual a (by omega : j ≤ m) u b1).toH1 ≤
      ((3 ^ d : ℕ) : ℝ) *
        (finiteAffineGradientExcess a (j + 1) m u).toReal := by
  let r1 := finiteAffineGradientResidual a hjm u b1
  have hE1 : Book.Ch03.h1EnergyNormOnCube (originCube d (j + 1)) a r1.toH1 =
      (finiteAffineGradientExcess a (j + 1) m u).toReal := by
    simpa only [r1] using
      residual_energy_eq_excess_toReal_increment a hjm u b1 hb1
  have hraw := h1EnergyNormOnCube_finiteCubeSolutionRestriction_sub_one_le
    a (j + 1) r1
  rw [hE1] at hraw
  have heq : Book.Ch03.h1EnergyNormOnCube (originCube d j) a
        (finiteAffineGradientResidual a (by omega : j ≤ m) u b1).toH1 =
      Book.Ch03.h1EnergyNormOnCube (originCube d ((j + 1) - 1)) a
        (finiteCubeSolutionRestriction a (by omega : (j + 1) - 1 ≤ j + 1)
          r1).toH1 := by
    unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.localizedCoeffEnergyValue
    simp only [r1, finiteCubeSolutionRestriction_grad,
      finiteAffineGradientResidual_grad]
    have hcube : originCube d j = originCube d ((j + 1) - 1) := by
      congr 1
      ring
    rw [hcube]
  exact heq.trans_le hraw

/-- A consecutive exact-minimizer increment propagated to an observation
scale carries precisely the quarter-power growth from the available theorem. -/
theorem finiteAffineExactMinimizerIncrementEnergy_le
    {d : ℕ} [NeZero d]
    (s c Cgrow : ℝ)
    (hgrowth : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ)
      (n m : ℤ), n < m →
      delta ∈ Set.Ioc (0 : ℝ) c →
      ScalarIdentityGoodMaxOnInterval a s delta n m →
      ∀ (j : ℤ) (_hj : j ∈ Finset.Icc n m)
        (k : ℤ) (_hk : k ∈ Finset.Icc n m), j ≤ k → ∀ b : Vec d,
        finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) k ≤
          Cgrow ^ 2 * Real.rpow 3
              (((Int.toNat (k - j) : ℕ) : ℝ) / 4) *
            finiteCenteredCubeSolutionEnergy a m
              (finiteAffineCubeSolution a m b) j)
    (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ)
    {n j q m : ℤ} (hnm : n < m)
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) c)
    (hgood : ScalarIdentityGoodMaxOnInterval a s delta n m)
    (hj : j ∈ Finset.Ico n q) (hqm : q ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    let b0 := finiteAffineExactMinimizer a
      (by exact (Finset.mem_Ico.mp hj).2.le.trans hqm) u
    let b1 := finiteAffineExactMinimizer a
      (by exact (Int.add_one_le_iff.mpr (Finset.mem_Ico.mp hj).2).trans hqm) u
    finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m (b0 - b1)) q ≤
      Cgrow ^ 2 * Real.rpow 3 (((q : ℝ) - (j : ℝ)) / 4) *
        ((finiteAffineGradientExcess a j m u).toReal +
          ((3 ^ d : ℕ) : ℝ) *
            (finiteAffineGradientExcess a (j + 1) m u).toReal) := by
  dsimp only
  let b0 := finiteAffineExactMinimizer a
    (by exact (Finset.mem_Ico.mp hj).2.le.trans hqm) u
  let b1 := finiteAffineExactMinimizer a
    (by exact (Int.add_one_le_iff.mpr (Finset.mem_Ico.mp hj).2).trans hqm) u
  have hb0 := finiteAffineExactMinimizer_spec a
    (by exact (Finset.mem_Ico.mp hj).2.le.trans hqm) u
  have hb1 := finiteAffineExactMinimizer_spec a
    (by exact (Int.add_one_le_iff.mpr (Finset.mem_Ico.mp hj).2).trans hqm) u
  have hchild := residualEnergy_at_predecessor_le_exactSuccessor
    a ((Int.add_one_le_iff.mpr (Finset.mem_Ico.mp hj).2).trans hqm) u b1 hb1
  have hbase := finiteAffineDifferenceEnergy_le_exactResiduals
    a ((Finset.mem_Ico.mp hj).2.le.trans hqm) u b0 b1 hb0 hchild
  have hjIcc : j ∈ Finset.Icc n m := by
    exact Finset.mem_Icc.2 ⟨(Finset.mem_Ico.mp hj).1,
      (Finset.mem_Ico.mp hj).2.le.trans hqm⟩
  have hqIcc : q ∈ Finset.Icc n m := by
    exact Finset.mem_Icc.2 ⟨(Finset.mem_Ico.mp hj).1.trans
      (Finset.mem_Ico.mp hj).2.le, hqm⟩
  have hraw := hgrowth a delta n m hnm hdelta hgood
    j hjIcc q hqIcc (Finset.mem_Ico.mp hj).2.le (b0 - b1)
  have hgap : (((Int.toNat (q - j) : ℕ) : ℝ) / 4) =
      ((q : ℝ) - (j : ℝ)) / 4 := by
    have hz : ((Int.toNat (q - j) : ℕ) : ℤ) = q - j :=
      Int.toNat_of_nonneg (sub_nonneg.mpr (Finset.mem_Ico.mp hj).2.le)
    have hzReal : ((Int.toNat (q - j) : ℕ) : ℝ) = ((q - j : ℤ) : ℝ) := by
      exact_mod_cast hz
    rw [hzReal]
    push_cast
    ring
  rw [hgap] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left hbase
    (mul_nonneg (sq_nonneg Cgrow) (Real.rpow_nonneg (by norm_num) _)))

end

end Root
end HighContrast
end HCPolySupport
