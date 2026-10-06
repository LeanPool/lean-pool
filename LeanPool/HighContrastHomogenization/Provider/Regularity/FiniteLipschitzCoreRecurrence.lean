/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreDefinitions
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreTerminal
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteSequenceBounds
public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodMax
public import LeanPool.HighContrastHomogenization.Provider.Regularity.SmallTailIteration

/-!
# High-contrast homogenization: Provider.Regularity.FiniteLipschitzCoreRecurrence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite centered-cube energy recurrence

This module proves the finite energy recurrence from the shared analytic and
terminal estimates.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Book.Ch03
open scoped BigOperators ENNReal

noncomputable section


namespace FiniteLipschitzCoreInternal

theorem finiteLipschitzTopAffineErrorSum_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (N : ℕ) :
    ∑ j ∈ Finset.Ioc (m - (N : ℤ)) m,
        finiteLipschitzAffineErrorRow a m u j ≤
      (N : ℝ) *
        ((3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)) *
          finiteLipschitzAffineErrorRow a m u m := by
  classical
  let c := finiteLipschitzBestIntercept a m u m
  let e := finiteLipschitzBestSlope a m u m
  let A : ℝ := (3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)
  let E := finiteLipschitzAffineErrorRow a m u
  have hres : MemLp (fun x ↦ u.toH1.toFun x - (c + vecDot e x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d m)) := by
    simpa only [c, e] using
      finiteLipschitzBestResidual_memLp a m u (le_refl m)
  have hEm : normalizedAffineCandidateError
      (originCube d m) u.toH1.toFun c e = E m := by
    simp only [E, c, e, finiteLipschitzAffineErrorRow,
      finiteLipschitzBestIntercept, finiteLipschitzBestSlope,
      finiteLipschitzRestriction_toFun, min_self]
  have hpoint : ∀ j ∈ Finset.Ioc (m - (N : ℤ)) m, E j ≤ A * E m := by
    intro j hj
    simp only [Finset.mem_Ioc] at hj
    let q : ℕ := Int.toNat (m - j)
    have hgap : 0 ≤ m - j := sub_nonneg.mpr hj.2
    have hqcast : (q : ℤ) = m - j := Int.toNat_of_nonneg hgap
    have hqN : q ≤ N := by
      dsimp [q] at hqcast ⊢
      omega
    have hfactor : (3 : ℝ) ^ q * (((3 ^ d) ^ q : ℕ) : ℝ) ≤ A := by
      dsimp [A]
      exact mul_le_mul
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hqN)
        (by exact_mod_cast Nat.pow_le_pow_right (by positivity : 0 < 3 ^ d) hqN)
        (by positivity) (by positivity)
    have hbest := finiteLipschitzAffineErrorRow_best_le a m u hj.2 c e
    have hrestrict := normalizedAffineCandidateError_originCube_sub_nat_le
      m q u.toH1.toFun c e hres
    rw [show m - (q : ℤ) = j by omega] at hrestrict
    calc
      E j ≤ normalizedAffineCandidateError
          (originCube d j) u.toH1.toFun c e := hbest
      _ ≤ ((3 : ℝ) ^ q * (((3 ^ d) ^ q : ℕ) : ℝ)) *
          normalizedAffineCandidateError (originCube d m) u.toH1.toFun c e :=
        hrestrict
      _ = ((3 : ℝ) ^ q * (((3 ^ d) ^ q : ℕ) : ℝ)) * E m := by
        rw [hEm]
      _ ≤ A * E m :=
        mul_le_mul_of_nonneg_right hfactor
          (finiteLipschitzAffineErrorRow_nonneg a m u m)
  calc
    ∑ j ∈ Finset.Ioc (m - (N : ℤ)) m, E j ≤
        ∑ _j ∈ Finset.Ioc (m - (N : ℤ)) m, A * E m :=
      Finset.sum_le_sum hpoint
    _ = (N : ℝ) * A * E m := by
      rw [Finset.sum_const, nsmul_eq_mul, Int.card_Ioc]
      simp only [sub_sub_cancel, Int.toNat_natCast]
      ring
    _ = (N : ℝ) *
        ((3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)) *
          finiteLipschitzAffineErrorRow a m u m := rfl

theorem exists_finiteLipschitzEnergyRecurrenceConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (n m : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d m) a), n ≤ m →
          ScalarIdentityGoodMaxOnInterval a s 1 n m →
          ∀ h ∈ Finset.Icc n m,
            finiteLipschitzEnergyRow a m u h ≤
              C * finiteLipschitzEnergyRow a m u m +
                C * ∑ j ∈ Finset.Ioc h m,
                  scalarIdentityWeakError a s j * finiteLipschitzEnergyRow a m u j := by
  obtain ⟨N, hN, Cstep, hCstep, hstep⟩ :=
    exists_finiteLipschitzOneStepConstant d s hs hs_lt
  obtain ⟨Cc, hCc, hcacc⟩ :=
    exists_finiteLipschitzCaccioppoliAffineConstant d s hs hs_lt
  obtain ⟨Ca, hCa, hadj⟩ := exists_finiteLipschitzAdjacentSlopeConstant d
  obtain ⟨Ct, hCt, hterminal⟩ :=
    exists_finiteLipschitzTerminalSlopeConstant d s hs hs_lt
  obtain ⟨Ce, hCe, herrorEnergy⟩ :=
    exists_finiteLipschitzAffineErrorEnergyConstant d s hs hs_lt
  let L : ℝ := ((3 ^ d : ℕ) : ℝ)
  let A : ℝ := (3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)
  let B : ℝ := (N : ℝ) * A * Ce
  let X : ℝ := Cc * ((1 + 2 * Ca) * (2 * B) + Ct)
  let Y : ℝ := Cc * ((1 + 2 * Ca) * (2 * Cstep))
  let C : ℝ := 1 + L + X + Y
  have hL : 0 ≤ L := by positivity
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hA) hCe.le
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
  intro a n m u hnm hgood h hh
  let E := finiteLipschitzAffineErrorRow a m u
  let D := finiteLipschitzEnergyRow a m u
  let p := finiteLipschitzBestSlope a m u
  have hD : ∀ j, 0 ≤ D j := finiteLipschitzEnergyRow_nonneg a m u
  have hE : ∀ j, 0 ≤ E j := finiteLipschitzAffineErrorRow_nonneg a m u
  have herr : ∀ j ∈ Finset.Icc n m, scalarIdentityWeakError a s j ≤ 1 :=
    hgood
  have htail_nonneg : 0 ≤ ∑ j ∈ Finset.Ioc h m,
      scalarIdentityWeakError a s j * D j :=
    Finset.sum_nonneg fun j _ ↦
      mul_nonneg (scalarIdentityWeakError_nonneg a s j) (hD j)
  by_cases htop : h = m
  · subst h
    simp only [Finset.Ioc_self, Finset.sum_empty, mul_zero, add_zero]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (hD m)
  by_cases hpred : h = m - 1
  · have hrestrict :=
      h1EnergyNormOnCube_finiteCubeSolutionRestriction_sub_one_le a m u
    have hrow : D (m - 1) ≤ L * D m := by
      calc
        D (m - 1) = Book.Ch03.h1EnergyNormOnCube (originCube d (m - 1)) a
            (finiteCubeSolutionRestriction a (by omega : m - 1 ≤ m) u).toH1 := by
          simpa only [D] using
            finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le
              a m u (m - 1) (by omega)
        _ ≤ L * Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1 := by
          simpa only [L] using hrestrict
        _ = L * D m := by
          simpa only [D] using
            congrArg (fun x : ℝ ↦ L * x) (finiteLipschitzEnergyRow_self a m u).symm
    have hLC : L ≤ C := by
      dsimp [C]
      linarith only [hX, hY]
    subst h
    exact hrow.trans ((mul_le_mul_of_nonneg_right hLC (hD m)).trans
      (le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hC) htail_nonneg)))
  have hhm : h ≤ m - 2 := by
    have := (show h ≤ m from (Finset.mem_Icc.1 hh).2)
    omega
  let r : ℤ := h + 2
  have hrm : r ≤ m := by dsimp [r]; omega
  have hrn : n ≤ r := by
    have := (Finset.mem_Icc.1 hh).1
    dsimp [r]
    omega
  let ur : Book.Ch03.CubeSolution (originCube d r) a :=
    finiteCubeSolutionRestriction a hrm u
  have hrmem : r ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨hrn, hrm⟩
  have hcacc' := hcacc a r ur
    (finiteLipschitzBestIntercept a m u r) (p r) (herr r hrmem)
  have hDh : D h ≤ Cc * (E r + euclideanNorm (p r)) := by
    have hindex : r - 2 = h := by dsimp [r]; ring
    calc
      D h = D (r - 2) := congrArg D hindex.symm
      _ ≤ Cc * (E r + euclideanNorm (p r)) := by
        dsimp only [D]
        rw [finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le
          a m u (r - 2) (by omega)]
        simpa only [E, p, ur,
          finiteLipschitzAffineErrorRow, finiteLipschitzRestriction_toFun,
          finiteLipschitzRestriction_grad, finiteCubeSolutionRestriction_toFun,
          min_eq_left hrm, finiteCubeSolutionRestriction_grad,
          Book.Ch03.h1EnergyNormOnCube, Book.Ch03.localizedCoeffEnergyValue,
          Book.Ch03.normalizedSetAverage, coefficientEnergyDensity] using hcacc'
  have hterminal' : euclideanNorm (p m) ≤ Ct * D m := by
    exact hterminal a m u (herr m (Finset.mem_Icc.2 ⟨hnm, le_rfl⟩))
  have hslopeSum : ∑ j ∈ Finset.Ico r m, euclideanNorm (p j - p (j + 1)) ≤
      2 * Ca * ∑ j ∈ Finset.Icc r m, E j := by
    calc
      ∑ j ∈ Finset.Ico r m, euclideanNorm (p j - p (j + 1)) ≤
          ∑ j ∈ Finset.Ico r m, Ca * (E j + E (j + 1)) := by
        exact Finset.sum_le_sum fun j hj ↦ hadj a m u j (by
          simp only [Finset.mem_Ico] at hj
          omega)
      _ = Ca * ∑ j ∈ Finset.Ico r m, (E j + E (j + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ Ca * (2 * ∑ j ∈ Finset.Icc r m, E j) :=
        mul_le_mul_of_nonneg_left (sum_adjacent_le_two_sum_Icc E hrm hE) hCa.le
      _ = 2 * Ca * ∑ j ∈ Finset.Icc r m, E j := by ring
  have hslope : euclideanNorm (p r) ≤
      Ct * D m + 2 * Ca * ∑ j ∈ Finset.Icc r m, E j :=
    (euclideanNorm_le_terminal_add_sum_adjacent p hrm).trans
      (add_le_add hterminal' hslopeSum)
  have hEm : E m ≤ Ce * D m :=
    herrorEnergy a m u m (le_refl m) (herr m (Finset.mem_Icc.2 ⟨hnm, le_rfl⟩))
  have htopSum : ∑ j ∈ Finset.Ioc (m - (N : ℤ)) m, E j ≤ B * D m := by
    calc
      ∑ j ∈ Finset.Ioc (m - (N : ℤ)) m, E j ≤
          (N : ℝ) * A * E m := by
        simpa only [E, A] using finiteLipschitzTopAffineErrorSum_le a m u N
      _ ≤ (N : ℝ) * A * (Ce * D m) :=
        mul_le_mul_of_nonneg_left hEm (mul_nonneg (Nat.cast_nonneg N) hA)
      _ = B * D m := by dsimp [B]; ring
  let F : ℤ → ℝ := fun j ↦ scalarIdentityWeakError a s j * D j
  have hF : ∀ j, 0 ≤ F j := fun j ↦
    mul_nonneg (scalarIdentityWeakError_nonneg a s j) (hD j)
  have hEsum := finiteStepErrorSum_le N hN E F Cstep (B * D m) hrm hE hF
    hCstep.le (mul_nonneg hB (hD m))
      (fun k hk ↦ by
        have hkm' : k ≤ m := (Finset.mem_Icc.1 hk).2
        simpa only [E, F, D, mul_assoc] using hstep a m u k hkm') htopSum
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
        (mul_le_mul_of_nonneg_left hforce hCstep.le)) (by norm_num))
  have hEr : E r ≤ ∑ j ∈ Finset.Icc r m, E j :=
    Finset.single_le_sum (fun j _ ↦ hE j) (Finset.mem_Icc.2 ⟨le_rfl, hrm⟩)
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.Icc r m, E j :=
    Finset.sum_nonneg fun j _ ↦ hE j
  have hraw : D h ≤ X * D m + Y * ∑ j ∈ Finset.Ioc h m, F j := by
    calc
      D h ≤ Cc * (E r + euclideanNorm (p r)) := hDh
      _ ≤ Cc * ((1 + 2 * Ca) * (∑ j ∈ Finset.Icc r m, E j) + Ct * D m) := by
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


end FiniteLipschitzCoreInternal

open FiniteLipschitzCoreInternal

/-- Unit pointwise identity-comparison errors give the finite energy
recurrence used by the small-tail closure. -/
theorem exists_scalarIdentityFiniteEnergyRecurrenceConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (n m : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d m) a), n ≤ m →
          ScalarIdentityGoodMaxOnInterval a s 1 n m →
          ∀ h ∈ Finset.Icc n m,
            finiteCenteredCubeSolutionEnergy a m u h ≤
              C * finiteCenteredCubeSolutionEnergy a m u m +
                C * ∑ j ∈ Finset.Ioc h m,
                  scalarIdentityWeakError a s j *
                    finiteCenteredCubeSolutionEnergy a m u j := by
  simpa only [finiteCenteredCubeSolutionEnergy, finiteLipschitzEnergyRow] using!
    exists_finiteLipschitzEnergyRecurrenceConstant d s hs hs_lt


end

end HighContrast
end HCPolySupport
