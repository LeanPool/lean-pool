/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointCarriers

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormAdjoint

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adjoint diagonal weak estimate

The primal estimate for the transposed coefficient is applied with the signed
congruence of the reference block.  All source carriers are then read back at
the original coefficient and reference.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem diagonalWeakNorm_adjoint_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hrho2 : rho < 2)
    (hs : rho / 2 < s) (hs1 : s ≤ 1) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (a : CoeffSpace d) (p r : Vec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakAdjointState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakAdjointState hq t a p r))) ≤
      if diagonalWeakMaximum rho q t E a = ⊤ then ⊤ else
        ENNReal.ofReal
          (16 * diagonalWeakMetricFactor m E * diagonalWeakLoadPlus E p r *
              (diagonalWeakCellSum q t H s E a +
                diagonalWeakAverageSum q t H s rho E a) +
            (16 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
                diagonalWeakMetricFactor m E) *
              (if delta < (diagonalWeakMaximum rho q t E a).toReal then
                  Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
                else
                  (3 : ℝ) ^ (-((s - rho / 2) * (H : ℝ)))) *
                diagonalWeakAdjointEnergy hq t a p r) := by
  let Ead := blockMatMul (blockDiag 1 (-1))
    (blockMatMul E (blockDiag 1 (-1)))
  have hEad : IsSymmetricBlockMat Ead :=
    isSymmetricBlockMat_adjointSign_congr hE
  have hEadpd : BlockPosDef Ead := blockPosDef_adjointSign_congr hEpd
  have hmain := diagonalWeakNorm_primal_le hq t H hsymm hsq hm
    hEad hEadpd hrho hrho2 hs hs1 hdelta hdelta1 (a := a.transpose) p r
  have hM : diagonalWeakMaximum rho q t Ead a.transpose =
      diagonalWeakMaximum rho q t E a := by
    exact diagonalWeakMaximum_adjoint rho hq t E a
  have hK : diagonalWeakMetricFactor m Ead =
      diagonalWeakMetricFactor m E := diagonalWeakMetricFactor_adjoint m E
  have hL : diagonalWeakLoadMinus Ead p r =
      diagonalWeakLoadPlus E p r := diagonalWeakLoadMinus_adjoint E p r
  have hcell : diagonalWeakCellSum q t H s Ead a.transpose =
      diagonalWeakCellSum q t H s E a :=
    diagonalWeakCellSum_adjoint hq t H s E a
  have hav : diagonalWeakAverageSum q t H s rho Ead a.transpose =
      diagonalWeakAverageSum q t H s rho E a :=
    diagonalWeakAverageSum_adjoint hq t H s rho hE hEpd a
  rw [hM, hK, hL, hcell, hav] at hmain
  exact hmain

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The adjoint all-scale estimate at a released split level. -/
theorem diagonalWeakNorm_adjoint_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho)
    (hs : rho / 2 < s) (hs1 : s ≤ 1) (hdelta : 0 < delta)
    (a : CoeffSpace d) (p r : Vec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakAdjointState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakAdjointState hq t a p r))) ≤
      if diagonalWeakMaximum rho q t E a = ⊤ then ⊤ else
        ENNReal.ofReal
          (recentConstantAtLevel delta * diagonalWeakMetricFactor m E *
              diagonalWeakLoadPlus E p r *
              (diagonalWeakCellSum q t H s E a +
                diagonalWeakAverageSum q t H s rho E a) +
            (maxGroupConstantAtLevel delta / (2 * s - rho) *
                diagonalWeakMetricFactor m E) *
              (if delta < (diagonalWeakMaximum rho q t E a).toReal then
                  Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
                else
                  (3 : ℝ) ^ (-((s - rho / 2) * (H : ℝ)))) *
                diagonalWeakAdjointEnergy hq t a p r) := by
  let Ead := blockMatMul (blockDiag 1 (-1))
    (blockMatMul E (blockDiag 1 (-1)))
  have hEad : IsSymmetricBlockMat Ead :=
    isSymmetricBlockMat_adjointSign_congr hE
  have hEadpd : BlockPosDef Ead := blockPosDef_adjointSign_congr hEpd
  have hmain := diagonalWeakNorm_primal_at_level_le hq t H hsymm hsq hm
    hEad hEadpd hrho hs hs1 hdelta (a := a.transpose) p r
  have hM : diagonalWeakMaximum rho q t Ead a.transpose =
      diagonalWeakMaximum rho q t E a :=
    diagonalWeakMaximum_adjoint rho hq t E a
  have hK : diagonalWeakMetricFactor m Ead =
      diagonalWeakMetricFactor m E := diagonalWeakMetricFactor_adjoint m E
  have hL : diagonalWeakLoadMinus Ead p r =
      diagonalWeakLoadPlus E p r := diagonalWeakLoadMinus_adjoint E p r
  have hcell : diagonalWeakCellSum q t H s Ead a.transpose =
      diagonalWeakCellSum q t H s E a :=
    diagonalWeakCellSum_adjoint hq t H s E a
  have hav : diagonalWeakAverageSum q t H s rho Ead a.transpose =
      diagonalWeakAverageSum q t H s rho E a :=
    diagonalWeakAverageSum_adjoint hq t H s rho hE hEpd a
  rw [hM, hK, hL, hcell, hav] at hmain
  exact hmain

end

end HCPolySupport.HighContrast.Response
