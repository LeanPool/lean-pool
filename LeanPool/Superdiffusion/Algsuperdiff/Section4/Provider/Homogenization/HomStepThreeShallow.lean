/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepThreeCoarse
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.EuclideanWspLocalization

/-!
# HomStepThreeShallow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the shallow range (unit A2)

## The gap

The correction: the word "Hence" in the paper silently extends Theorem C's
display from `j ≤ m - X_m(α)` to ALL `j ≤ m`.  It is proved
(`hence_holds_on_deep_range`) that on the DEEP range the extension is free, so
the gap is EXACTLY the shallow range `m - X_m(α) < j ≤ m`.  The correction
lists two routes, neither written in the manuscript:

* **(a)** averaging over the scale-`(m - X_m)` descendants;
* **(b)** invoking Theorem C at `n₀ = min{j, m - X_m(α)}`.

The obvious alternative — a volume comparison from `□_m` down to `z + □_j` —
costs `3^{(d/2)(m-j)}`, MUCH larger than the printed `3^{(1-α)X_m(α)}`, and is
what makes the gap real.

## What is proved here: the analytic core of route (a)

Route (a) is exact and costs NOTHING beyond the deep-range bound, because the
normalized average over a cube is the *average* of the normalized averages over
its descendants at any depth — `CoarseGraining`'s
`descendantsENNAverage_lintegral_normalizedCubeMeasure_eq` — and an average is
at most a maximum.  Hence:

```
  ⨍_R |∇u|² ≤ B  for every scale-(m - X) descendant R of Q
      ⟹  ⨍_Q |∇u|² ≤ B,
```

`cubeAverage_le_of_descendants`, at the depth where the descendants sit.  Consequently the
shallow-range display holds with
the SAME constant as the deep-range one, i.e. the printed
`3^{(1-α)X_m(α)} 3^{(1-α)(m-j)}` is not merely sufficient but generous by the
factor `3^{(1-α)(m-j)} ≥ 1`.

## What this module does NOT do — the two named identifications

Plugging this into the abstract family `F j z = ν^{1/2}‖∇u‖_{L²(z+□_j)}` needs
two carrier identifications, both absent and both purely mechanical:

1. **the real/`ℝ≥0∞` average bridge** —
   `Real.sqrt (normalizedSetAverage (openCubeSet R) (fun y => vecNormSq (∇u y)))`
   versus `(∫⁻ x, ENNReal.ofReal (vecNormSq (∇u x)) ∂normalizedCubeMeasure R).toReal`
   (equal once `vecNormSq ∘ ∇u` is integrable on the cube, which the `H1Function`
   carrier supplies);
2. **the indexing bridge** — `descendantsAtDepth Q n` versus the manuscript's
   `{z + □_{j₀}: z ∈ 3^{j₀}ℤ^d ∩ Q}` at `j₀ = Q.scale - n`
   (`scale_eq_sub_of_mem_descendantsAtDepth` gives the scale; the centre
   enumeration is the missing half).

Neither is a statement-level item and neither needs the author: is a GAP IN THE
MANUSCRIPT'S JUSTIFICATION, not a false display, and route (a) is sound.  The
correction's disposition is therefore unchanged — the display stands, the
justification is recorded — and this module supplies the part of route (a)
that is genuine analysis.
-/

open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. An average is at most a maximum -/

/-- The descendant average of a family dominated by `B` is dominated by `B`. -/
theorem descendantsENNAverage_le_of_forall_le (Q : TriadicCube d) (j : ℕ)
    {F : TriadicCube d → ℝ≥0∞} {B : ℝ≥0∞}
    (hF : ∀ R ∈ descendantsAtDepth Q j, F R ≤ B) :
    descendantsENNAverage Q j F ≤ B := by
  classical
  have hne : (descendantsAtDepth Q j).Nonempty := descendantsAtDepth_nonempty Q j
  have hcard : 0 < (descendantsAtDepth Q j).card := Finset.card_pos.mpr hne
  have hcard0 : ((descendantsAtDepth Q j).card : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Nat.ne_of_gt hcard
  have hcardtop : ((descendantsAtDepth Q j).card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : (∑ R ∈ descendantsAtDepth Q j, F R) ≤
      ((descendantsAtDepth Q j).card : ℝ≥0∞) * B := by
    calc (∑ R ∈ descendantsAtDepth Q j, F R)
        ≤ ∑ _R ∈ descendantsAtDepth Q j, B := Finset.sum_le_sum hF
      _ = ((descendantsAtDepth Q j).card : ℝ≥0∞) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [descendantsENNAverage]
  calc ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, F R
      ≤ ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (((descendantsAtDepth Q j).card : ℝ≥0∞) * B) := mul_le_mul' le_rfl hsum
    _ = B := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcard0 hcardtop, one_mul]

/-! ## 2. Route (a): the shallow cube's average is controlled by its deep
descendants -/

/-- **The analytic core of route (a).**

The normalized average over a triadic cube is the AVERAGE of the normalized
averages over its depth-`j` descendants (`CoarseGraining`'s exact partition
identity), hence at most their maximum.  So a bound valid at every deep
scale-`(Q.scale - j)` descendant transfers to the shallow cube `Q` itself, with
NO loss — in particular without the `3^{(d/2)(m-j)}` volume factor the naive
argument would pay. -/
theorem cubeAverage_le_of_descendants (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → ℝ≥0∞) {B : ℝ≥0∞}
    (hdeep : ∀ R ∈ descendantsAtDepth Q j,
      (∫⁻ x, f x ∂normalizedCubeMeasure R) ≤ B) :
    (∫⁻ x, f x ∂normalizedCubeMeasure Q) ≤ B := by
  have hid := descendantsENNAverage_lintegral_normalizedCubeMeasure_eq Q j f
  rw [← hid]
  exact descendantsENNAverage_le_of_forall_le Q j hdeep

end

end Algsuperdiff.Section4.Provider.Homogenization
