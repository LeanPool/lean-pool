/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSupplyPorts
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueIsoAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSupplyPortsAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The released sharp weak value's drop-family port

The released value, like the pinned one, reads the drop family only inside the
window, so the account may hand the fused core a truncated family and the two
agree.  The threshold pair and the three coefficients play no part.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The released sharp weak value depends on the drop family only inside the
window.** -/
theorem weakValueBoundSharpIsotropyAt_congr_Dr (cfirst cmax ctail : ℝ)
    (P : Measure (CoeffSpace d))
    (m0 h0 : Mat d) (F : BlockMat d) (L : ℝ) (n : Mat d) (rho : ℝ) (Hw : ℕ)
    (bmaj beta lev : ℝ) (t l : ℤ) (V : ℕ → ℝ) (V0 : ℝ) {Dr Dr' : ℕ → ℝ}
    (h : ∀ j ∈ Finset.range (Hw + 1), Dr j = Dr' j) (Vmean : ℝ) :
    weakValueBoundSharpIsotropyAt cfirst cmax ctail P m0 h0 F L n rho Hw
        bmaj beta lev t l V V0 Dr Vmean =
      weakValueBoundSharpIsotropyAt cfirst cmax ctail P m0 h0 F L n rho Hw
        bmaj beta lev t l V V0 Dr' Vmean := by
  have h1 : (∑ j ∈ Finset.range (Hw + 1),
      (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) =
      ∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr' j) :=
    Finset.sum_congr rfl fun j hj => by rw [h j hj]
  have h2 : (∑ j ∈ Finset.range (Hw + 1),
      (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
        Real.sqrt (2 * (d : ℝ) * Dr j)) =
      ∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
          Real.sqrt (2 * (d : ℝ) * Dr' j) :=
    Finset.sum_congr rfl fun j hj => by rw [h j hj]
  rw [weakValueBoundSharpIsotropyAt, weakValueBoundSharpIsotropyAt, h1, h2]

end

end HCPolySupport.HighContrast.Quenched
