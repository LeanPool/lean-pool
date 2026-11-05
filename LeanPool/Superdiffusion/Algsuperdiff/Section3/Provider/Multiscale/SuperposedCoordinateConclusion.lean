/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SuperposedConclusion
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

/-!
# SuperposedCoordinateConclusion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A finite-coordinate reduction of the corrected superposed A

The operator-norm consumers of Section 3 do not require an almost-sure bound
simultaneous over the uncountable unit sphere.  Positivity bounds each of the
two coarse matrix norms by its trace, and both traces are sums of the `2 * d`
pure coordinate quadratic forms

```text
((sqrt sigma)\u207b\u00b9 e_j, 0),    (0, sqrt sigma e_j).
```

The deterministic theorem below records that reduction using CoarseGraining's
trace A.  The final theorem intersects the corrected superposed conclusion only
over `j : Fin d`, once for each pure leg.  It retains the exact
scale-separation, wave-envelope, and all-load potential gates; no gate is
strengthened and no uncountable intersection is taken.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Affine

noncomputable section

variable {d : ℕ}

/-! ## Deterministic finite-coordinate trace reduction -/


/-! ## The exact superposed payload at one load -/

/-- The right-hand side of the corrected assembled superposed conclusion at
one unframed load `(p,q)`. -/
def superposedConclusionPayload (M : ABKModel d) (m i L : ℤ)
    (E b eps t beta : ℝ) (k₀ kp : ℕ) (omega : CutoffSample d)
    (p q : Vec d) : ℝ :=
  layerSumConst beta (2 * M.gamma + eps) kp
      (ktotConst M m i 3 (ktotEnvelopeSup M m L eps t) p q)
      (collarEnvelopeConst M m i L eps t (superposedDivConst d) p q)
      (6 * (d : ℝ)) *
    ((3 : ℝ) ^ ((2 * M.gamma + eps) *
        ((Percolation.hsep M m E b omega + k₀ : ℕ) : ℝ)) *
      (1 + (3 : ℝ) ^
          (2 * beta * ((Percolation.hsep M m E b omega + k₀ : ℕ) : ℝ)) *
        Real.exp (-((kp : ℝ) / 36))))

/-! ## A simultaneous a.e. result over exactly `2 * d` loads -/


end

end Algsuperdiff.Section3.Provider.Multiscale
