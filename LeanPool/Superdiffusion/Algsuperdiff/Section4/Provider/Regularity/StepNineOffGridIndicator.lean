/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepNineOffGridTransfer

/-!
# StepNineOffGridIndicator

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` off-grid transfer: the boundary indicator and the composed
# displays

## The indicator mismatch, and why it is not real here

Steps 4--6 of §4.4 carry the boundary leg gated by `𝟙_{z ∉ □_{m−1}}` at the
lattice centre `z`; `e.gradient.with.shom` prints `𝟙_{x ∉ □_{m−1}}` at the
theorem's arbitrary centre `x`, with no comment.  The mismatch is genuine if the
centre is chosen by nearest point: through the nearest lattice point `z` one only
has `dist(z,0) ≤ 3^{m−1}/2 + 3^{n}/2`, so `z` can fall marginally outside
`□_{m−1}` while `x` is inside — and then the `z`-form's boundary leg is switched
on while the `x`-form's is switched off, which is the wrong direction.

`StepNineOffGridGeometry` removes the mismatch at the source.  Rounding toward
the origin gives `|z_i| ≤ |x_i|` coordinatewise, hence

```text
  x ∈ □_{m−1}  ⟹  z ∈ □_{m−1} ,        equivalently   𝟙_{z∉□_{m−1}} ≤ 𝟙_{x∉□_{m−1}} ,
```

which is exactly the direction the transfer needs: the `z`-form's right-hand
side is then dominated by the `x`-form's.  **No band enlargement, at any scale,
and no extra constant.**  The lattice `3^nℤ^d ∩ □_m` of Step 3 is unchanged;
only the choice of representative inside it is.  This strictly improves on the
nearest-point route, which pays a scale.

## What is delivered

* `offGridCentre_mem_inner` — `x ∈ □_{m−1} → z ∈ □_{m−1}`;
* `energyDensityEstimate_offGrid` — `e.energy.density.estimate` transferred, in
  the frozen root's `ℝ≥0∞` carrier, at the constant `3^d·C`;
* `energyDensityEstimate_offGrid_pair` — the frozen root's TWO- conclusion
  shape (the general clause, and the boundary-leg-free clause gated on `x ∈
  □_{m−1}`), produced from the corresponding `z`-clauses.

## References

* ABK26, `t.regularity`, (the indicator flip), 12203.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The indicator -/

/-- **The indicator transfer.**  The toward-origin lattice centre inherits the
membership in `□_{m−1}`; this is the step the manuscript omits, at zero cost. -/
theorem offGridCentre_mem_inner {m : ℤ} (n : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m - 1))) :
    offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) :=
  offGridCentre_mem_openCubeSet n hx

section BoundaryLeg

open scoped Classical

end BoundaryLeg

/-! ## 2. The composed display, in the frozen root's carrier -/

/-- **`e.energy.density.estimate`, transferred off the grid**.

From the §4.4 chain's own conclusion at the lattice centre `z = offGridCentre n
x` and scale `n+1`, the theorem's conclusion at an arbitrary centre `x ∈ □_m` and
scale `n`, with the constant multiplied by `3^d` and nothing else moved: the
exponent `3^{(1−α)(m−n)}` and the whole right-hand bracket are untouched.

`bracket` is opaque here — the transfer never looks inside it, so the caller
may supply the printed three-leg bracket, its boundary-leg-free specialization,
or any other. -/
theorem energyDensityEstimate_offGrid (nu : ℝ) (f : Vec d → ℝ) {x : Vec d} {m n : ℤ}
    {C alpha : ℝ} {bracket : ℝ≥0∞}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n ≤ m)
    (hz : ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn
          (truncatedWindow (offGridCentre n x) m (n + 1)))
        ≤ ENNReal.ofReal (C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
          bracket) :
    ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
      ≤ ENNReal.ofReal (((3 : ℝ) ^ d * C) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) * bracket := by
  have htr := energyDensityLhs_offGrid_transfer nu f hx hnm
  have hstep := mul_le_mul' (le_refl (ENNReal.ofReal ((3 : ℝ) ^ d))) hz
  have hcoef : ENNReal.ofReal ((3 : ℝ) ^ d) *
      ENNReal.ofReal (C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))))
      = ENNReal.ofReal (((3 : ℝ) ^ d * C) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d), mul_assoc]
  calc ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
      ≤ ENNReal.ofReal ((3 : ℝ) ^ d) *
          (ENNReal.ofReal (Real.sqrt nu) *
            eLpNorm f 2 (Support.normalizedVolumeMeasureOn
              (truncatedWindow (offGridCentre n x) m (n + 1)))) := htr
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ d) *
          (ENNReal.ofReal (C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
            bracket) := hstep
    _ = (ENNReal.ofReal ((3 : ℝ) ^ d) *
          ENNReal.ofReal (C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))))) *
            bracket := by rw [mul_assoc]
    _ = ENNReal.ofReal (((3 : ℝ) ^ d * C) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) * bracket := by
        rw [hcoef]

/-- **The frozen root's two-clause conclusion, transferred.**

`anomalous_regularity` states `e.energy.density.estimate` as a conjunction:
the general clause with the `‖∇h‖`-leg present, and the clause with that leg
dropped, gated on `x ∈ □_{m−1}` (the rendering of `𝟙_{x∉□_{m−1}}`).  This is that pair,
produced from the corresponding pair at the lattice centre `z` and scale `n+1`
— the gate of the second `z`-clause being `z ∈ □_{m−1}`, which
`offGridCentre_mem_inner` supplies from `x ∈ □_{m−1}` at zero cost. -/
theorem energyDensityEstimate_offGrid_pair (nu : ℝ) (f : Vec d → ℝ) {x : Vec d} {m n : ℤ}
    {C alpha : ℝ} {bracketFull bracketInner : ℝ≥0∞}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n ≤ m)
    (hzfull : ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn
          (truncatedWindow (offGridCentre n x) m (n + 1)))
        ≤ ENNReal.ofReal (C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
          bracketFull)
    (hzinner : offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
      ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn
          (truncatedWindow (offGridCentre n x) m (n + 1)))
        ≤ ENNReal.ofReal (C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
          bracketInner) :
    (ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
      ≤ ENNReal.ofReal (((3 : ℝ) ^ d * C) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) * bracketFull) ∧
      (x ∈ openCubeSet (originCube d (m - 1)) →
        ENNReal.ofReal (Real.sqrt nu) *
            eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
          ≤ ENNReal.ofReal (((3 : ℝ) ^ d * C) *
              Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) * bracketInner) := by
  refine ⟨energyDensityEstimate_offGrid nu f hx hnm hzfull, fun hxin => ?_⟩
  exact energyDensityEstimate_offGrid nu f hx hnm (hzinner (offGridCentre_mem_inner n hxin))

end

end Algsuperdiff.Section4.Provider.Regularity
