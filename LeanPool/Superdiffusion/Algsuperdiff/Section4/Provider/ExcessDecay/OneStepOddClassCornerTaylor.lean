/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerGeometry

/-!
# OneStepOddClassCornerTaylor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two-point Taylor elimination, box-generic

The pointwise atom's `(★)` (`OneStepEvenBound.abs_evenAffinePart_le_pointwise`)
is stated on the proved one-met-face slab/Taylor boxes.  The corner pricing
needs the same estimate on the window-hugging corner boxes of
`OneStepOddClassCornerGeometry`, and — for the third application — at an affine
competitor that is *not* a minimizer.

The estimate: for `V` odd about the met upper `i`-face, `f = V − ℓ` the
residual against an arbitrary affine `ℓ = affineEval (c − A·x) A`, harmonic on
`T` with Hessian bound `M` there, and `y` within depth `delta` of the face
with `y`, `ρᵢy`, `y − delta·eᵢ ∈ T`:

```text
  |evenᵢ(ℓ)(y)| ≤ 2|f y| + |f (y − delta·eᵢ)| + 3 M delta² .
```

The reflection identity `f∘ρᵢ + f = −2·evenᵢ(ℓ)` supplies the even part; the
two second-order Taylor steps (towards the reflected and the pushed point)
eliminate the unknown normal derivative.

## References

* Adapted from `OneStepEvenBound.abs_evenAffinePart_le_pointwise` (same
  repository), the boxes abstracted.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}


/-! ## 8. Crude volume lower bounds -/

/-- Any box with all edges at least `delta` has volume at least `delta^d`. -/
theorem volume_toReal_coordBox_ge_of_edges {lo hi : Fin d → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hedge : ∀ l, delta ≤ hi l - lo l) :
    delta ^ d ≤ (volume (coordBox lo hi)).toReal := by
  have hle : ∀ l, lo l ≤ hi l := fun l => by linarith only [hedge l, hdelta]
  rw [volume_coordBox_toReal hle]
  calc delta ^ d = ∏ _l : Fin d, delta := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ l : Fin d, (hi l - lo l) :=
        Finset.prod_le_prod₀ (fun _ _ => hdelta.le) (fun l _ => hedge l)

/-- The face slab's edges are all at least `delta`. -/
theorem cornerFaceSlab_edge_ge {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) (l : Fin d) :
    delta ≤ cornerFaceSlabHi x m k i l - cornerFaceSlabLo x m k i delta l := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [cornerFaceSlabHi, cornerFaceSlabLo]
  by_cases hli : l = i
  · rw [ite_eq_left hli, ite_eq_left hli]
    linarith only []
  · rw [ite_eq_right hli, ite_eq_right hli]
    have h := quarter_zpow_lt_hug_edge hx hkm l
    linarith only [h, hdelta16, hw]

/-- The corner slab's edges are all at least `delta`. -/
theorem cornerPairSlab_edge_ge {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) (l : Fin d) :
    delta ≤ cornerPairSlabHi x m k i j l - cornerPairSlabLo x m k i j delta l := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [cornerPairSlabHi, cornerPairSlabLo]
  by_cases hlij : l = i ∨ l = j
  · rw [ite_eq_left hlij, ite_eq_left hlij]
    linarith only []
  · rw [ite_eq_right hlij, ite_eq_right hlij]
    have h := quarter_zpow_lt_hug_edge hx hkm l
    linarith only [h, hdelta16, hw]

/-! ## 9. Face-depth accessors -/

/-- A point of the face slab is within `delta` of the met face. -/
theorem cornerFaceSlab_depth {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    {y : Vec d}
    (hy : y ∈ coordBox (cornerFaceSlabLo x m k i delta) (cornerFaceSlabHi x m k i)) :
    (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y i ∧ y i < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  have h := (mem_coordBox_iff.1 hy) i
  rw [cornerFaceSlabLo, ite_eq_left rfl, cornerFaceSlabHi, ite_eq_left rfl] at h
  exact h

/-- A point of the corner slab is within `delta` of the `j`-face (and of the
`i`-face). -/
theorem cornerPairSlab_depth {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ}
    {y : Vec d}
    (hy : y ∈ coordBox (cornerPairSlabLo x m k i j delta)
      (cornerPairSlabHi x m k i j)) :
    ((1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y i ∧ y i < (1 / 2 : ℝ) * (3 : ℝ) ^ m)
      ∧ ((1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y j
          ∧ y j < (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  have hi' := (mem_coordBox_iff.1 hy) i
  have hj' := (mem_coordBox_iff.1 hy) j
  rw [cornerPairSlabLo, ite_eq_left (Or.inl rfl), cornerPairSlabHi,
    ite_eq_left (Or.inl rfl)] at hi'
  rw [cornerPairSlabLo, ite_eq_left (Or.inr rfl), cornerPairSlabHi,
    ite_eq_left (Or.inr rfl)] at hj'
  exact ⟨hi', hj'⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
