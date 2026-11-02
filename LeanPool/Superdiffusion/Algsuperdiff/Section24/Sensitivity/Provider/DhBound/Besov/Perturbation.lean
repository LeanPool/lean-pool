/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov.Product

/-!
# Perturbation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Constants and unit-cube normalizations for the perturbation Besov bound

Source: ABK26, the second inequality of `e.sensitivity.basic.split1`:

```
‖ h ‖_{B^{3/8}_{2,2}(□₀)}  ≤  C ( | (h)_{□₀} | + ‖ ∇h ‖_{L^∞(□₀)} ) .
```

What remains here is the arithmetic surface that the surviving Section 2.4
cone consumes: the constant `besovPerturbConst s`, which is the `ℓ²`
geometric sum `∑ 3^{2(s-1)j}` (convergent because `s < 1`), and the two
unit-cube normalizations of the cube scale factor and the Besov scale weight.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov

open HCPolySupport MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The `ℓ²` depth constant -/

/-- The constant of the perturbation bound: the `ℓ²` geometric sum `∑ 3^{2(s-1)j}`. -/
noncomputable def besovPerturbConst (s : ℝ) : ℝ :=
  Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹)

theorem besovPerturbConst_pos {s : ℝ} (hs : s < 1) : 0 < besovPerturbConst s := by
  have hlt : Real.rpow (3 : ℝ) (2 * (s - 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpos : 0 < (1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹ := inv_pos.mpr (by linarith)
  exact Real.sqrt_pos.mpr hpos

/-! ## The unit-cube statement -/

theorem cubeScaleFactor_originCube_zero (d : ℕ) :
    cubeScaleFactor (originCube d 0) = 1 := by
  simp [cubeScaleFactor_originCube]

@[simp] theorem cubeBesovScaleWeight_originCube_zero (d : ℕ) (s : ℝ) :
    cubeBesovScaleWeight s (originCube d 0) = 1 := by
  simp [cubeBesovScaleWeight]

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Besov
