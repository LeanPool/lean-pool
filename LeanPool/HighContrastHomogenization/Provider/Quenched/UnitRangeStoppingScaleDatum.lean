/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeGaussianGauge
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleEngineAdapter

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeStoppingScaleDatum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The stopping scale in its weak-Orlicz shape

The endgame states its stopping-scale estimate as a weak-Orlicz bound on the
`μ`-th power of the generation-`n` scale,

`R_n^μ = O_{Ψ_fr}(C 3^(nμ))`,

against the finite-range gauge, and then converts it into the shifted tail the
bad-tail engine consumes by choosing an integer buffer `b` large enough to absorb
the constant `C`
(`e.random.quenched.tail`, read as the shifted tail of the quenched radius).

This file performs that conversion.  The buffer exists for every positive `C`,
and once it is chosen the shifted tail holds at the dimensional constant
`c_fr(d)`, with no reference to any source scale, source gauge or window: the
stopping scale is an arbitrary family here, exactly as it is in the engine.  The
composition with the engine is recorded at the end, so the whole route runs
without the source window.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open Book.Ch05.Section57

noncomputable section

variable {d : ℕ}

/-! ## The datum -/

/-! ## The buffer -/

/-- A buffer absorbing the constant of the weak-Orlicz bound exists. -/
theorem exists_shift_of_pos {mu C : ℝ} (hmu : 0 < mu) (hC : 0 < C) :
    ∃ b : ℕ, C ≤ (3 : ℝ) ^ (mu * (b : ℝ)) := by
  obtain ⟨b, hb⟩ := exists_nat_ge (Real.logb 3 C / mu)
  refine ⟨b, ?_⟩
  have hlog : Real.logb 3 C ≤ mu * (b : ℝ) := by
    rw [div_le_iff₀ hmu] at hb
    linarith only [hb]
  have hkey : (3 : ℝ) ^ Real.logb 3 C ≤ (3 : ℝ) ^ (mu * (b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  rwa [Real.rpow_logb (by norm_num) (by norm_num) hC] at hkey

/-! ## The shifted tail -/

/-! ## The composition into the engine -/

end

end Quenched
end HighContrast
end HCPolySupport
