/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.DeGiorgiCutoffTest
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2

/-!
# CaccioppoliAbsorbed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Young-absorbed Caccioppoli inequality
-/

noncomputable section

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-- Young inequality for the cutoff flux cross term, with the explicit
nonsymmetric ellipticity constant.  Half of the elliptic energy is kept and
the remainder is charged to the cutoff gradient. -/
theorem cutoff_flux_young {lam Lam e p : ℝ} {A : Mat d} (z de : Vec d)
    (hA : IsEllipticMatrix lam Lam A) :
    |2 * e * p * vecDot (matVecMul A z) de| ≤
      lam / 2 * (e ^ 2 * vecNormSq z) +
        (2 * Lam ^ 2 / lam) * (p ^ 2 * vecNormSq de) := by
  have hlam : 0 < lam := hA.1
  have hLam : 0 < Lam := hlam.trans_le hA.2.1
  let c : ℝ := Real.sqrt lam / Lam * e
  let b : ℝ := 2 * Lam / Real.sqrt lam * p
  have hsqrt : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hlam).ne'
  have hLam0 : Lam ≠ 0 := hLam.ne'
  have hcb : c * b = 2 * e * p := by
    dsimp [c, b]
    field_simp
  have hy := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    c b (matVecMul A z) de
  rw [hcb] at hy
  refine hy.trans (add_le_add ?_ ?_)
  · have hAz := vecNormSq_matVecMul_le_of_isEllipticMatrix hA z
    have hc2 : c ^ 2 = lam / Lam ^ 2 * e ^ 2 := by
      dsimp [c]
      rw [mul_pow, div_pow, Real.sq_sqrt hlam.le]
    rw [hc2]
    calc
      (lam / Lam ^ 2 * e ^ 2) * vecNormSq (matVecMul A z) / 2 ≤
          (lam / Lam ^ 2 * e ^ 2) * (Lam ^ 2 * vecNormSq z) / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAz
            (mul_nonneg (div_nonneg hlam.le (sq_nonneg Lam)) (sq_nonneg e)))
          zero_le_two
      _ = lam / 2 * (e ^ 2 * vecNormSq z) := by
        field_simp
  · have hb2 : b ^ 2 / 2 = 2 * Lam ^ 2 / lam * p ^ 2 := by
      dsimp [b]
      rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hlam.le]
      field_simp
    calc
      b ^ 2 * vecNormSq de / 2 = (b ^ 2 / 2) * vecNormSq de := by ring
      _ ≤ _ := by
        rw [hb2]
        ring_nf
        exact le_rfl

end DivergenceFormProcess.Form
