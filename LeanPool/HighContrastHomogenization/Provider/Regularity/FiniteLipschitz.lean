/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreBestFit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreRecurrence

/-!
# High-contrast homogenization: Provider.Regularity.FiniteLipschitz

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite large-scale Lipschitz estimate on centered cubes

The comparison coefficient is the identity matrix and every spatial domain
is a centered Euclidean triadic cube.
-/

namespace HCPolySupport
namespace HighContrast

open scoped BigOperators ENNReal

noncomputable section

/-- A summably small identity-comparison error row gives a uniform weighted
gradient bound between centered Euclidean cubes. -/
theorem exists_scalarIdentityFiniteLipschitzConstant
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d)
        (n m : ℤ) (_hnm : n < m)
        (_hgood : ScalarIdentityGoodTailOnInterval a s c n m)
        (u : Book.Ch03.CubeSolution (originCube d m) a),
        weightedGradNorm
            (a.coeffOn (originCube d n)).toCoeffField
            (openCubeSet (originCube d n)) u.toH1.grad ≤
          ENNReal.ofReal C *
            weightedGradNorm
              (a.coeffOn (originCube d m)).toCoeffField
              (openCubeSet (originCube d m)) u.toH1.grad := by
  obtain ⟨C₀, hC₀, hrecurrence⟩ :=
    exists_scalarIdentityFiniteEnergyRecurrenceConstant d s hs hs_lt
  let C : ℝ := 2 * C₀
  let c : ℝ := min (1 / 2 : ℝ) (2 * C₀)⁻¹
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hC : 1 ≤ C := by dsimp [C]; linarith only [hC₀]
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (inv_pos.mpr (mul_pos (by norm_num) hC₀pos))
  have hclt : c < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨C, c, hC, ⟨hcpos, hclt⟩, ?_⟩
  intro a n m hnm hgood u
  have hnm' : n ≤ m := hnm.le
  have hmax : ScalarIdentityGoodMaxOnInterval a s 1 n m :=
    hgood.toGoodMax.mono hclt.le
  let D := finiteCenteredCubeSolutionEnergy a m u
  have hD : ∀ j ∈ Finset.Icc n m, 0 ≤ D j := fun j _ ↦ by
    dsimp [D, finiteCenteredCubeSolutionEnergy, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  have herr : ∀ j ∈ Finset.Icc n m, 0 ≤ scalarIdentityWeakError a s j :=
    fun j _ ↦ scalarIdentityWeakError_nonneg a s j
  have hsmall : ∑ j ∈ Finset.Icc n m, scalarIdentityWeakError a s j ≤
      (2 * C₀)⁻¹ := hgood.trans (min_le_right _ _)
  have hreal : D n ≤ 2 * C₀ * D m :=
    smallTail_interval_bound C₀ D (scalarIdentityWeakError a s) hnm' hC₀
      hD herr (hrecurrence a n m u hnm' hmax) hsmall n
      (Finset.mem_Icc.2 ⟨le_rfl, hnm'⟩)
  let un : Book.Ch03.CubeSolution (originCube d n) a :=
    finiteCubeSolutionRestriction a hnm' u
  have hDn : D n =
      Book.Ch03.h1EnergyNormOnCube (originCube d n) a un.toH1 := by
    have hcoeff : (a.coeffOn (originCube d (min n m))).toCoeffField =
        (a.coeffOn (originCube d n)).toCoeffField :=
      congrArg (fun Q : TriadicCube d ↦ (a.coeffOn Q).toCoeffField)
        (congrArg (originCube d) (min_eq_left hnm'))
    have hset : openCubeSet (originCube d (min n m)) =
        openCubeSet (originCube d n) :=
      congrArg openCubeSet (congrArg (originCube d) (min_eq_left hnm'))
    dsimp only [D]
    unfold finiteCenteredCubeSolutionEnergy Book.Ch03.h1EnergyNormOnCube
      Book.Ch03.localizedCoeffEnergyValue
    simp only [finiteCubeSolutionRestriction_grad, un]
    rw [hcoeff, hset]
  have hDm : D m =
      Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1 := by
    have hcoeff : (a.coeffOn (originCube d (min m m))).toCoeffField =
        (a.coeffOn (originCube d m)).toCoeffField :=
      congrArg (fun Q : TriadicCube d ↦ (a.coeffOn Q).toCoeffField)
        (congrArg (originCube d) (min_self m))
    have hset : openCubeSet (originCube d (min m m)) =
        openCubeSet (originCube d m) :=
      congrArg openCubeSet (congrArg (originCube d) (min_self m))
    dsimp only [D]
    unfold finiteCenteredCubeSolutionEnergy Book.Ch03.h1EnergyNormOnCube
      Book.Ch03.localizedCoeffEnergyValue
    simp only [finiteCubeSolutionRestriction_grad]
    rw [hcoeff, hset]
  have hinner : weightedGradNorm
        (a.coeffOn (originCube d n)).toCoeffField
        (openCubeSet (originCube d n)) u.toH1.grad = ENNReal.ofReal (D n) := by
    calc
      _ = weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n)) un.toH1.grad := by
        dsimp only [un]
        rw [finiteCubeSolutionRestriction_grad]
      _ = ENNReal.ofReal
          (Book.Ch03.h1EnergyNormOnCube (originCube d n) a un.toH1) :=
        weightedGradNorm_eq_ofReal_h1EnergyNormOnCube
          (originCube d n) a un.toH1
      _ = ENNReal.ofReal (D n) := congrArg ENNReal.ofReal hDn.symm
  have houter : weightedGradNorm
        (a.coeffOn (originCube d m)).toCoeffField
        (openCubeSet (originCube d m)) u.toH1.grad = ENNReal.ofReal (D m) := by
    calc
      _ = ENNReal.ofReal
          (Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1) :=
        weightedGradNorm_eq_ofReal_h1EnergyNormOnCube
          (originCube d m) a u.toH1
      _ = ENNReal.ofReal (D m) := congrArg ENNReal.ofReal hDm.symm
  rw [hinner, houter]
  calc
    ENNReal.ofReal (D n) ≤ ENNReal.ofReal (2 * C₀ * D m) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal C * ENNReal.ofReal (D m) := by
      rw [ENNReal.ofReal_mul (zero_le_one.trans hC)]

end

end HighContrast
end HCPolySupport
