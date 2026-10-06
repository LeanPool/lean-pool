/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecursionAssembly

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastPerGenerationRec

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The per-generation recursion step, assembled

Step 4 of, scalar half: the conclusion of
`exists_account_one_step_entry_of_block_at_level` at one generation, together with the metric
factor bound and the summed slot bounds, put into the drop-history shape
`hrec_final_sharp_at_jb_src` consumes.

Reading the one-step conclusion at `eps = F_t` and multiplying by `d`:

```
F_t ≤ a·(F_s − F_t) + b_q·F_t² + c_w·W²,
a   = 64·C_pre·d·(3/2 + 1/(4η)),
b_q = 2d(3d+4) + 4·C_pre·d·rowCoefficient,
c_w = 4·C_pre·d,
```

which is exactly the input of `hrec_of_one_step_sharp_at_jb` / `hrec_final_sharp_at_jb_src`.  The
row value
is `rowCoefficient · eps²` by definition, so it lands in the quadratic slot
alongside the centering term — this is the printed accounting in which every
`eps²` coefficient is dimensional or `κ`-scaled.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The `eps²`-coefficient of the entry row value. -/
@[expose]
def rowCoefficient (Cd g : ℝ) (mAl : Mat d) (G : ℕ) (s t : ℤ) (kap : ℝ) : ℝ :=
  2 * (2 * boundaryConst Cd g mAl *
      (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (s : ℝ)))) *
    (1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g)))) * (kap * (36 * (1 + (d : ℝ))))

/-- The drop coefficient of the one-step estimate. -/
@[expose]
def dropCoefficient (d : ℕ) (Cpre eta : ℝ) : ℝ :=
  64 * Cpre * (d : ℝ) * (3 / 2 + 1 / (4 * eta))

/-- The quadratic coefficient of the one-step estimate. -/
@[expose]
def quadCoefficient (d : ℕ) (Cpre Crow : ℝ) : ℝ :=
  2 * (d : ℝ) * (3 * (d : ℝ) + 4) + 4 * Cpre * (d : ℝ) * Crow

/-- The weak coefficient of the one-step estimate. -/
@[expose]
def weakCoefficient (d : ℕ) (Cpre : ℝ) : ℝ := 4 * Cpre * (d : ℝ)

/-- **The one-step estimate in scalar shape.**  Multiplying the account's
hatted one-step conclusion by `d` turns it into the input of
`hrec_of_one_step_sharp_at_jb`, with the three coefficients above. -/
theorem one_step_scalar_shape (d : ℕ) {Cpre eta Crow W hatS hatT : ℝ}
    (hd0 : (0 : ℝ) ≤ (d : ℝ))
    (hstep : hatT - 1 ≤
      4 * Cpre * ((3 / 2 + 1 / (4 * eta)) * (16 * (d : ℝ) * (hatS - hatT)) +
          Crow * ((d : ℝ) * (hatT - 1)) ^ 2 + W ^ 2) +
        2 * ((3 * (d : ℝ) + 4) * ((d : ℝ) * (hatT - 1)) ^ 2)) :
    (d : ℝ) * (hatT - 1) ≤
      dropCoefficient d Cpre eta *
          ((d : ℝ) * (hatS - 1) - (d : ℝ) * (hatT - 1)) +
        quadCoefficient d Cpre Crow * ((d : ℝ) * (hatT - 1)) ^ 2 +
        weakCoefficient d Cpre * W ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_left hstep hd0
  rw [dropCoefficient, quadCoefficient, weakCoefficient]
  nlinarith only [hmul]

end

end HCPolySupport.HighContrast.Quenched
