/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineIntegerDownscale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineFiniteCarrierTransport
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.NormalizedBlocks
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.HomogenizationErrorControl

/-!
# VarianceCarrierSeam

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch05.Section54.VarianceBoundGoodScale
open scoped MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The seam at the genuine coefficient cutoff law -/

section GenuineLaw

variable (M : ABKModel d) (L : ℤ)

/-- The isotropic comparator normalizer `𝐁(σ_L)` carried by the transported
finite-corridor bound: it is literally the `B` bound there, so a consumer can
rewrite between the two forms by `rfl`. -/
def cutoffComparatorNormalizer : FullBlockMat d :=
  Ch02.constantFullBlockMatrix
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))

/-- **The Step-2 downscale display in the units of the Step-3 corridor bound.**
Multiplying `e.means.downscale.by.defect` by `σ_L^2` removes the `σ_L^{-2}`
gauge, leaving the pure amplitude `4 δ₁^2`, which is the scale on which the
transported corridor bound `C δ (δ + 3^{-d(n-L)})` is stated.  The premises are
exactly those of the proved display. -/
theorem coefficientCutoffLaw_sq_sigmaBar_mul_annealedSigmaStarInvScalarAtScale_sub_le_four_mul_sq
    {n m : ℤ} (hLn : L ≤ n) (hnm : n ≤ m)
    {s : ℝ} (hs : 0 < s) {delta1 : ℝ} (hdelta1 : delta1 ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hmoment : ∫⁻ omega, ENNReal.ofReal
        (Observable.cutoffHomogenizationErrorRepresentative M L L hs
          (Annealed.sigmaBar M L) omega ^ 4)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (delta1 ^ 2))
    {p q : Vec d} (hpq : q = (Annealed.sigmaBar M L : ℝ) • p)
    (hqnorm : vecNormSq q = (Annealed.sigmaBar M L : ℝ)) :
    ((Annealed.sigmaBar M L : ℝ) *
        (annealedSigmaStarInvScalarAtScale M L m -
          annealedSigmaStarInvScalarAtScale M L n)) ^ (2 : ℕ) ≤
      4 * delta1 ^ 2 := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hbase :=
    coefficientCutoffLaw_sq_abs_annealedSigmaStarInvScalarAtScale_sub_le M hLn hnm hs
      hdelta1 hmoment hpq hqnorm
  rw [sq_abs] at hbase
  have hinv : (Annealed.sigmaBar M L : ℝ) * ((Annealed.sigmaBar M L : ℝ))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hsigma)
  have hexpand :
      ((Annealed.sigmaBar M L : ℝ) *
          (annealedSigmaStarInvScalarAtScale M L m -
            annealedSigmaStarInvScalarAtScale M L n)) ^ (2 : ℕ) =
        (Annealed.sigmaBar M L : ℝ) ^ (2 : ℕ) *
          (annealedSigmaStarInvScalarAtScale M L m -
            annealedSigmaStarInvScalarAtScale M L n) ^ (2 : ℕ) := by
    ring
  have hstep :=
    mul_le_mul_of_nonneg_left hbase
      (le_of_lt (pow_pos hsigma 2) : (0 : ℝ) ≤ (Annealed.sigmaBar M L : ℝ) ^ (2 : ℕ))
  rw [hexpand]
  refine hstep.trans (le_of_eq ?_)
  have hgauge : (Annealed.sigmaBar M L : ℝ) ^ (2 : ℕ) *
      ((Annealed.sigmaBar M L : ℝ))⁻¹ ^ (2 : ℕ) = 1 := by
    rw [← mul_pow, hinv, one_pow]
  calc
    (Annealed.sigmaBar M L : ℝ) ^ (2 : ℕ) *
        (4 * ((Annealed.sigmaBar M L : ℝ))⁻¹ ^ 2 * delta1 ^ 2)
        = ((Annealed.sigmaBar M L : ℝ) ^ (2 : ℕ) *
            ((Annealed.sigmaBar M L : ℝ))⁻¹ ^ (2 : ℕ)) * (4 * delta1 ^ 2) := by
          ring
    _ = 4 * delta1 ^ 2 := by rw [hgauge, one_mul]

end GenuineLaw

end

end Algsuperdiff.Section3.Provider.Homogenization
