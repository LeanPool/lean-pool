/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

/- Physical dual right-hand-side estimates on ruled Whitney cells. -/

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalDualToBesovBridge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledWhitneyCellDuality
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledWhitneyDirichletRHSRow

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledWhitneyPhysicalDualRHSRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast
open Book Book.Ch03 MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- Package a field in `MemVectorL2 (cubeSet Q)` as a Euclidean `L²` field for the
normalized cube measure. -/
private def cubeEuclideanLpFieldOfMemVectorL2
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemVectorL2 (cubeSet Q) F) :
    CubeEuclideanLpField Q FiniteLpExponent.two :=
  { toField := F
    euclideanMemLp := by
      have hnormalized : MemLp F (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) :=
        memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF
      simpa only [Function.comp_apply, HilbertVec.ofVecL_apply] using!
        (HilbertVec.ofVecL d).comp_memLp' hnormalized }

/-- The available fractional smooth-dual comparison controls one physical
negative Whitney square by the corresponding physical full-dual square. -/
theorem negativeWhitneyCellEnergy_le_fullDual
    (hd : 1 ≤ d) {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : Vec d → Vec d)
    (hF : MemVectorL2 (system.cell i) F) :
    negativeWhitneyCellEnergy system s F i ≤
      (fractionalDualToBesovConstant d) ^ (2 : ℕ) *
        (ENNReal.ofReal
          (physicalFullDualBesovVectorNorm (whitneyCellCube system i) s F)) ^
            (2 : ℕ) := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd)⟩
  let Q : TriadicCube d := whitneyCellCube system i
  have hFQ : MemVectorL2 (cubeSet Q) F := by
    change MemLp F 2 (volume.restrict (cubeSet Q))
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa [Q, whitneyCellCube, volumeMeasureOn] using! hF
  let FF : CubeEuclideanLpField Q FiniteLpExponent.two :=
    cubeEuclideanLpFieldOfMemVectorL2 Q F hFQ
  have hmain :=
    negSobolevNorm_le_fractionalDualToBesovConstant_mul_fullDualSum
      Q hs hsHalf FF
  have hmain' : negSobolevNorm (system.cell i) s F ≤
      fractionalDualToBesovConstant d *
        ENNReal.ofReal
          (physicalFullDualBesovVectorNorm (whitneyCellCube system i) s F) := by
    simpa [Q, FF, whitneyCellCube, physicalFullDualBesovVectorNorm] using! hmain
  unfold negativeWhitneyCellEnergy
  calc
    negSobolevNorm (system.cell i) s F ^ (2 : ℝ) ≤
        (fractionalDualToBesovConstant d *
          ENNReal.ofReal
            (physicalFullDualBesovVectorNorm (whitneyCellCube system i) s F)) ^
          (2 : ℝ) := ENNReal.rpow_le_rpow hmain' (by norm_num)
    _ = (fractionalDualToBesovConstant d) ^ (2 : ℕ) *
        (ENNReal.ofReal
          (physicalFullDualBesovVectorNorm (whitneyCellCube system i) s F)) ^
            (2 : ℕ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num

end

end HighContrast
end HCPolySupport
