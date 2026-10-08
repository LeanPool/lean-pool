/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileMaximumLp
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointCarriers

/-!
# High-contrast homogenization: Provider.Response.ProfileEnergyCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Optimizer-energy profile carriers

The bad branch retains the correlation between the all-scale response maximum
and the optimizer energy.  The good branch retains only the optimizer energy
and the deterministic below-window factor.  Both are extended-real `L²`
seminorms, so a divergent maximum remains on the bad branch.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The correlated bad-event optimizer energy. -/
@[expose]
def profileBadEnergy (P : Measure (CoeffSpace d))
    (M : CoeffSpace d → ℝ≥0∞) (energy : CoeffSpace d → ℝ) : ℝ≥0∞ :=
  eLpNorm ({a | (1 : ℝ≥0∞) < M a}.indicator fun a =>
    M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (energy a)) 2 P

/-- The good-event optimizer energy with its below-window factor. -/
@[expose]
def profileGoodEnergy (P : Measure (CoeffSpace d)) (alpha : ℝ) (H : ℕ)
    (M : CoeffSpace d → ℝ≥0∞) (energy : CoeffSpace d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
    eLpNorm ({a | M a ≤ (1 : ℝ≥0∞)}.indicator fun a =>
      ENNReal.ofReal (energy a)) 2 P

/-- **The bad-event optimizer energy at a released split level.**  The
fixed-level carrier is this at `lev = 1`, definitionally: the event is literally
`{a | 1 < M a}`.  The printed threshold factor multiplies the *sum* of the two
branches, so it is carried by the consumer's own outer coefficient and does not
appear here. -/
@[expose]
def profileBadEnergyAt (P : Measure (CoeffSpace d)) (lev : ℝ≥0∞)
    (M : CoeffSpace d → ℝ≥0∞) (energy : CoeffSpace d → ℝ) : ℝ≥0∞ :=
  eLpNorm ({a | lev < M a}.indicator fun a =>
    M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (energy a)) 2 P

/-- **The good-event optimizer energy at a released split level.**  The
fixed-level carrier is this at `lev = 1`, definitionally. -/
@[expose]
def profileGoodEnergyAt (P : Measure (CoeffSpace d)) (lev : ℝ≥0∞) (alpha : ℝ)
    (H : ℕ) (M : CoeffSpace d → ℝ≥0∞) (energy : CoeffSpace d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
    eLpNorm ({a | M a ≤ lev}.indicator fun a =>
      ENNReal.ofReal (energy a)) 2 P

end

end HCPolySupport.HighContrast.Response
