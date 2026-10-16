/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorAssemblyLhs
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlueWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SigmaBarIndex

/-!
# InteriorAssemblyAnchorShape

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The anchor-shape weakening of the correction leg

The composed correction leg of `InteriorGlue` is *stronger* than the frozen
statement's second interior summand: it carries the honest `s^{-1/2}` where the
anchor prints `s^{-7}`, and the honest `σ_{n+2}` where the anchor prints `σ_n`.
This module records the weakening, so that the composed estimate can be read
**in the anchor's own printed shape**:

```text
   σ_{n+2}^{-1} · 3^{n} · (correction leg)
       ≤ C(d) · s^{-7} · σ_n^{-1} · 3^{(1+s)n} · [g]_{H^s(x+□_n)} ,
```

which is exactly the frozen statement's

```text
   C s^{-7} σ_n^{-1} 3^{(1+s)n} [g]_{H^s(W)}
```

with `C = 4 · interiorCorrectionConst d`.  Two steps, both priced and both
one-directional:

* the `σ` index move `σ_{n+2}^{-1} ≤ 4 σ_n^{-1}` — `SigmaBarIndex`, discharged
  inside the anchor's own regime, no landmark binder.

The prefactor `σ_{n+2}^{-1} · 3^{n}` is exactly what dividing the harmonic
display of the child-frame composition by its own left-hand weight
`σ · cubeBesovScaleWeight 1 (□_n) = σ · 3^{-n}` produces, at the comparator
choice `σ := σ_{n+2}` (the index of the parent's flux correction and of the
anchor's error slot).

**No `γ`-move is made anywhere**; the regime is the anchor's own
`γ ≤ C^{-1} c⋆^{10}`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the interior clause's second
  summand).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The two one-directional moves -/

/-- The scale weights combine to the printed `3^{(1+s)n}`. -/
theorem rpow_three_mul_eq_one_add (s : ℝ) (n : ℤ) :
    Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ)) =
      Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) := by
  change (3 : ℝ) ^ ((n : ℝ)) * (3 : ℝ) ^ (s * (n : ℝ)) = (3 : ℝ) ^ ((1 + s) * (n : ℝ))
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The anchor's geometry binder, in the `translateSet` spelling the child-frame
composition is entered at. -/
theorem translateSet_openCubeSet_subset_of_anchorGeometry {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    translateSet x (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d m) := by
  rw [← image_add_eq_translateSet x (openCubeSet (originCube d n))]
  exact fun p hp => (hgeom hp).2

/-- Restrict clause-(iv) data to the frontier-empty parent window and its child.
The result is independent of the coefficient slot used by the comparison. -/
theorem interior_comparison_window_data {n m : ℤ} {x z : Vec d} {s : ℝ}
    (hz : z ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hfr : (fun y => z + y) '' openCubeSet (originCube d (n + 2)) ∩
      frontier (openCubeSet (originCube d m)) = ∅)
    {g : Vec d → Vec d}
    (hg : MemLp g 2 (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    translateSet x (openCubeSet (originCube d n)) ⊆ openCubeSet (originCube d m) ∧
    translateSet z (openCubeSet (originCube d (n + 2))) ⊆ openCubeSet (originCube d m) ∧
    MemLp g 2 (Support.normalizedVolumeMeasureOn
      (((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m))) ∧
    MemLp (Gagliardo.gagliardoKernel s 2 g) 2 (Support.normalizedGagliardoMeasureOn
      (((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m))) ∧
    MemLp g 2 (Support.normalizedVolumeMeasureOn
      ((fun y => x + y) '' openCubeSet (originCube d n))) ∧
    MemLp (Gagliardo.gagliardoKernel s 2 g) 2 (Support.normalizedGagliardoMeasureOn
      ((fun y => x + y) '' openCubeSet (originCube d n))) := by
  have hsub : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) := fun y hy => (hgeom hy).2
  have hvol : volume (((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m)) ≠ 0 := by
    rw [inter_eq_of_frontier_inter_empty hz hfr]
    exact volume_image_add_openCubeSet_ne_zero z (originCube d (n + 2))
  exact ⟨translateSet_openCubeSet_subset_of_anchorGeometry hgeom,
    translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr,
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hvol hg,
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hvol hgW,
    memLp_two_child_of_clause_iv hsub hg, memLp_two_gagliardo_child_of_clause_iv hsub hgW⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay
