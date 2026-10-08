/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreDefinitions
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceConstantMatrix
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseGeometry
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneySquareWeights
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity
public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.CoordinateStandard
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.OverlapCoordinateBridge
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ExactOverlapEuclideanComparison
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeEuclideanHsFullNormConstantMatrix
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CommonQuantitativeAffineScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedOuterSpatialResponsePowerTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedPhysicalDirichletEuclideanHs
public import LeanPool.HighContrastHomogenization.Support.Besov.Negative.ExactAggregationBridge
public import LeanPool.HighContrastHomogenization.Support.Besov.PositiveOverlapBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.NegativeBesovLocalize
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ExactOverlapEuclideanFullComparison
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedHarmonicReplacement
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.AEEq
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.Response
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.RHSCorrections
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincare.QTwo
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteSequenceBounds
public import LeanPool.HighContrastHomogenization.Provider.Regularity.SmallTailIteration

/-!
# High-contrast homogenization: Provider.Regularity.MixedOrderFiniteRecurrenceCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite energy recurrence over an independent response row

The finite sequence argument only uses a nonnegative forcing row, its
pointwise unit bound, and four analytic estimates.  In particular, the order
used to construct those analytic estimates is not part of the recurrence
bookkeeping.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Book.Ch03
open scoped BigOperators ENNReal

noncomputable section

open FiniteLipschitzCoreInternal

/-- A fixed-step affine recurrence and three response-row analytic estimates
imply the finite energy recurrence, without assigning a fractional order to
the response row. -/
theorem exists_mixedResponseFiniteLipschitzEnergyRecurrenceConstant
    (d : ℕ)
    (N : ℕ) (hN : 0 < N) (Cstep : ℝ) (hCstep : 0 ≤ Cstep)
    (Cc : ℝ) (hCc : 0 < Cc) (Ct : ℝ) (hCt : 0 < Ct)
    (Ce : ℝ) (hCe : 0 < Ce) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (aRounded : Book.Ch03.CoeffFamily d) (R : ℤ → ℝ),
        (∀ j : ℤ, 0 ≤ R j) →
        (∀ (m : ℤ) (u : Book.Ch03.CubeSolution
            (originCube d m) aRounded) (k : ℤ), k ≤ m →
          finiteLipschitzAffineErrorRow aRounded m u (k - (N : ℤ)) ≤
            (1 / 8 : ℝ) * finiteLipschitzAffineErrorRow aRounded m u k +
              Cstep * R k * finiteLipschitzEnergyRow aRounded m u k) →
        (∀ (k : ℤ) (u : Book.Ch03.CubeSolution
            (originCube d k) aRounded) (c : ℝ) (e : Vec d),
          R k ≤ 1 →
            Book.Ch03.h1EnergyNormOnCube (originCube d (k - 2)) aRounded
                (finiteCubeSolutionRestriction aRounded
                  (by omega : k - 2 ≤ k) u).toH1 ≤
              Cc * (normalizedAffineCandidateError
                (originCube d k) u.toH1.toFun c e + euclideanNorm e)) →
        (∀ (m : ℤ) (u : Book.Ch03.CubeSolution
            (originCube d m) aRounded),
          R m ≤ 1 →
            euclideanNorm (finiteLipschitzBestSlope aRounded m u m) ≤
              Ct * finiteLipschitzEnergyRow aRounded m u m) →
        (∀ (m : ℤ) (u : Book.Ch03.CubeSolution
            (originCube d m) aRounded) (k : ℤ) (_hkm : k ≤ m),
          R k ≤ 1 →
            finiteLipschitzAffineErrorRow aRounded m u k ≤
              Ce * finiteLipschitzEnergyRow aRounded m u k) →
        ∀ (n m : ℤ)
          (u : Book.Ch03.CubeSolution (originCube d m) aRounded), n ≤ m →
          (∀ k ∈ Finset.Icc n m, R k ≤ 1) →
          ∀ h ∈ Finset.Icc n m,
            finiteLipschitzEnergyRow aRounded m u h ≤
              C * finiteLipschitzEnergyRow aRounded m u m +
                C * ∑ j ∈ Finset.Ioc h m,
                  R j * finiteLipschitzEnergyRow aRounded m u j := by
  obtain ⟨Ca, hCa, hadj⟩ := exists_finiteLipschitzAdjacentSlopeConstant d
  let L : ℝ := ((3 ^ d : ℕ) : ℝ)
  let A : ℝ := (3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)
  let B : ℝ := (N : ℝ) * A * Ce
  let X : ℝ := Cc * ((1 + 2 * Ca) * (2 * B) + Ct)
  let Y : ℝ := Cc * ((1 + 2 * Ca) * (2 * Cstep))
  let C : ℝ := 1 + L + X + Y
  have hL : 0 ≤ L := by positivity
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hA) hCe.le
  have hX : 0 ≤ X := by
    dsimp [X]
    positivity
  have hY : 0 ≤ Y := by
    dsimp [Y]
    positivity
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith only [hL, hX, hY]
  refine ⟨C, hC, ?_⟩
  intro aRounded R hR hstep hcacc hterminal herrorEnergy
    n m u hnm hgood h hh
  let E := finiteLipschitzAffineErrorRow aRounded m u
  let D := finiteLipschitzEnergyRow aRounded m u
  let p := finiteLipschitzBestSlope aRounded m u
  have hD : ∀ j, 0 ≤ D j := finiteLipschitzEnergyRow_nonneg aRounded m u
  have hE : ∀ j, 0 ≤ E j := finiteLipschitzAffineErrorRow_nonneg aRounded m u
  have htail_nonneg : 0 ≤ ∑ j ∈ Finset.Ioc h m, R j * D j :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hR j) (hD j)
  by_cases htop : h = m
  · subst h
    simp only [Finset.Ioc_self, Finset.sum_empty, mul_zero, add_zero]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (hD m)
  by_cases hpred : h = m - 1
  · have hrestrict :=
      h1EnergyNormOnCube_finiteCubeSolutionRestriction_sub_one_le
        aRounded m u
    have hrow : D (m - 1) ≤ L * D m := by
      calc
        D (m - 1) = Book.Ch03.h1EnergyNormOnCube
            (originCube d (m - 1)) aRounded
            (finiteCubeSolutionRestriction aRounded
              (by omega : m - 1 ≤ m) u).toH1 := by
          simpa only [D] using
            finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le
              aRounded m u (m - 1) (by omega)
        _ ≤ L * Book.Ch03.h1EnergyNormOnCube
            (originCube d m) aRounded u.toH1 := by
          simpa only [L] using hrestrict
        _ = L * D m := by
          simpa only [D] using
            congrArg (fun x : ℝ ↦ L * x)
              (finiteLipschitzEnergyRow_self aRounded m u).symm
    have hLC : L ≤ C := by
      dsimp [C]
      linarith only [hX, hY]
    subst h
    exact hrow.trans ((mul_le_mul_of_nonneg_right hLC (hD m)).trans
      (le_add_of_nonneg_right
        (mul_nonneg (zero_le_one.trans hC) htail_nonneg)))
  have hhm : h ≤ m - 2 := by
    have hle : h ≤ m := (Finset.mem_Icc.1 hh).2
    omega
  let r : ℤ := h + 2
  have hrm : r ≤ m := by dsimp [r]; omega
  have hrn : n ≤ r := by
    have hn : n ≤ h := (Finset.mem_Icc.1 hh).1
    dsimp [r]
    omega
  let ur : Book.Ch03.CubeSolution (originCube d r) aRounded :=
    finiteCubeSolutionRestriction aRounded hrm u
  have hrmem : r ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨hrn, hrm⟩
  have hcacc' := hcacc r ur
    (finiteLipschitzBestIntercept aRounded m u r) (p r) (hgood r hrmem)
  have hDh : D h ≤ Cc * (E r + euclideanNorm (p r)) := by
    have hindex : r - 2 = h := by dsimp [r]; ring
    calc
      D h = D (r - 2) := congrArg D hindex.symm
      _ ≤ Cc * (E r + euclideanNorm (p r)) := by
        dsimp only [D]
        rw [finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le
          aRounded m u (r - 2) (by omega)]
        simpa only [E, p, ur,
          finiteLipschitzAffineErrorRow, finiteLipschitzRestriction_toFun,
          finiteLipschitzRestriction_grad, finiteCubeSolutionRestriction_toFun,
          min_eq_left hrm, finiteCubeSolutionRestriction_grad,
          Book.Ch03.h1EnergyNormOnCube, Book.Ch03.localizedCoeffEnergyValue,
          Book.Ch03.normalizedSetAverage, coefficientEnergyDensity] using hcacc'
  have hterminal' : euclideanNorm (p m) ≤ Ct * D m :=
    hterminal m u (hgood m (Finset.mem_Icc.2 ⟨hnm, le_rfl⟩))
  have hslopeSum : ∑ j ∈ Finset.Ico r m,
      euclideanNorm (p j - p (j + 1)) ≤
        2 * Ca * ∑ j ∈ Finset.Icc r m, E j := by
    calc
      ∑ j ∈ Finset.Ico r m, euclideanNorm (p j - p (j + 1)) ≤
          ∑ j ∈ Finset.Ico r m, Ca * (E j + E (j + 1)) := by
        exact Finset.sum_le_sum fun j hj ↦ hadj aRounded m u j (by
          simp only [Finset.mem_Ico] at hj
          omega)
      _ = Ca * ∑ j ∈ Finset.Ico r m, (E j + E (j + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ Ca * (2 * ∑ j ∈ Finset.Icc r m, E j) :=
        mul_le_mul_of_nonneg_left
          (sum_adjacent_le_two_sum_Icc E hrm hE) hCa.le
      _ = 2 * Ca * ∑ j ∈ Finset.Icc r m, E j := by ring
  have hslope : euclideanNorm (p r) ≤
      Ct * D m + 2 * Ca * ∑ j ∈ Finset.Icc r m, E j :=
    (euclideanNorm_le_terminal_add_sum_adjacent p hrm).trans
      (add_le_add hterminal' hslopeSum)
  have hEm : E m ≤ Ce * D m :=
    herrorEnergy m u m (le_refl m)
      (hgood m (Finset.mem_Icc.2 ⟨hnm, le_rfl⟩))
  have htopSum : ∑ j ∈ Finset.Ioc (m - (N : ℤ)) m, E j ≤ B * D m := by
    calc
      ∑ j ∈ Finset.Ioc (m - (N : ℤ)) m, E j ≤
          (N : ℝ) * A * E m := by
        simpa only [E, A] using
          finiteLipschitzTopAffineErrorSum_le aRounded m u N
      _ ≤ (N : ℝ) * A * (Ce * D m) :=
        mul_le_mul_of_nonneg_left hEm
          (mul_nonneg (Nat.cast_nonneg N) hA)
      _ = B * D m := by dsimp [B]; ring
  let F : ℤ → ℝ := fun j ↦ R j * D j
  have hF : ∀ j, 0 ≤ F j := fun j ↦ mul_nonneg (hR j) (hD j)
  have hEsum := finiteStepErrorSum_le N hN E F Cstep (B * D m)
    hrm hE hF hCstep (mul_nonneg hB (hD m))
      (fun k hk ↦ by
        have hkm' : k ≤ m := (Finset.mem_Icc.1 hk).2
        simpa only [E, F, D, mul_assoc] using hstep m u k hkm') htopSum
  have hforce : ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k ≤
      ∑ j ∈ Finset.Ioc h m, F j := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk ↦ by
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_Ioc]
        omega)
      (fun j _ _ ↦ hF j)
  have hEsum' : ∑ j ∈ Finset.Icc r m, E j ≤
      2 * (B * D m + Cstep * ∑ j ∈ Finset.Ioc h m, F j) :=
    hEsum.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (B * D m))
        (mul_le_mul_of_nonneg_left hforce hCstep)) (by norm_num))
  have hEr : E r ≤ ∑ j ∈ Finset.Icc r m, E j :=
    Finset.single_le_sum (fun j _ ↦ hE j)
      (Finset.mem_Icc.2 ⟨le_rfl, hrm⟩)
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.Icc r m, E j :=
    Finset.sum_nonneg fun j _ ↦ hE j
  have hraw : D h ≤ X * D m + Y * ∑ j ∈ Finset.Ioc h m, F j := by
    calc
      D h ≤ Cc * (E r + euclideanNorm (p r)) := hDh
      _ ≤ Cc * ((1 + 2 * Ca) * (∑ j ∈ Finset.Icc r m, E j) +
          Ct * D m) := by
        apply mul_le_mul_of_nonneg_left _ hCc.le
        nlinarith only [hEr, hslope, hCa.le, hsum_nonneg]
      _ ≤ Cc * ((1 + 2 * Ca) *
          (2 * (B * D m + Cstep * ∑ j ∈ Finset.Ioc h m, F j)) +
            Ct * D m) := by
        apply mul_le_mul_of_nonneg_left _ hCc.le
        exact add_le_add
          (mul_le_mul_of_nonneg_left hEsum'
            (by linarith only [hCa] : 0 ≤ 1 + 2 * Ca))
          (le_refl (Ct * D m))
      _ = X * D m + Y * ∑ j ∈ Finset.Ioc h m, F j := by
        dsimp [X, Y]
        ring
  have hXC : X ≤ C := by dsimp [C]; linarith only [hL, hY]
  have hYC : Y ≤ C := by dsimp [C]; linarith only [hL, hX]
  simpa only [D, F] using hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_right hXC (hD m))
    (mul_le_mul_of_nonneg_right hYC htail_nonneg))

end

end HighContrast
end HCPolySupport
