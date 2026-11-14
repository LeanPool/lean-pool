/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.BlockBesovSeminorm
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfacesComponentwise

/-!
# BlockBesovPositive

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport
  (abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds_two_two)


/-!
# The positive block Besov seminorm and the block duality pairing

Step 2 of `l.approximate.recurrence.formula` pairs two **doubled** fields:

```
  fint_{z+cu_n} bfF_z . bfA_m tilde S_z
    <= [ bfAhom^{1/2} bfF_z ]_{Hbar^1(z+cu_n)}
       [ bfAhom^{-1/2} bfA_m tilde S_z ]_{Hbar^{-1}(z+cu_n)} .
```

`BlockBesovSeminorm.lean` supplies the negative half `blockNegativeBesovTwo`,
in the **component-sum** rendering.  This module supplies the doubled
fluctuation and the pairing itself.  The positive side is never packed into a
block quantity: it enters componentwise, through CoarseGraining's
`cubeBesovPositiveVectorPartialSeminormTwo` on each of the two blocks.

* `blockCubeFluctuation` -- the doubled cube fluctuation `Y - fint_Q Y`.
* `abs_cubeAverage_blockVecDot_blockCubeFluctuation_le` -- the block duality
  pairing, the sum of two copies of CoarseGraining's componentwise sharp `q =
  2` bound
  `abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds_two_two`.

No new analysis occurs here: `blockVecDot X Y = vecDot X.1 Y.1 + vecDot X.2 Y.2`
is definitionally a two-term sum, and `blockNegativeBesovTwo` is definitionally
the sum of the two component seminorms, so the block pairing is exactly the sum
of two upstream `Vec d` pairings.  This module is the carrier lift.

## Feeding the partial-bound hypotheses

CoarseGraining's duality theorem consumes bounds on the *finite-depth*
seminorms (`... ≤ Bu` for every truncation `N`), not on their suprema.  The two
`_le_blockNegativeBesovTwo` lemmas below produce exactly those on the negative
side, from the block seminorm, given the `BddAbove` producers of
`TruncationPoincareBridge.lean`.  On the positive side the pairing takes the
componentwise finite-depth bounds directly, as its binders `hpos1` and `hpos2`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section



variable {d : ℕ}

/-! ## Additivity of the cube average -/

/-- Additivity of `cubeAverage` under cube-set integrability. -/
theorem cubeAverage_add_of_integrableOn (Q : TriadicCube d) (f g : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet Q) volume)
    (hg : IntegrableOn g (cubeSet Q) volume) :
    cubeAverage Q (fun x => f x + g x) = cubeAverage Q f + cubeAverage Q g := by
  unfold cubeAverage
  rw [MeasureTheory.integral_add hf hg, mul_add]

/-! ## The two doubled carriers -/

/-- **The doubled cube fluctuation** of a block field: the componentwise
`Vec d` fluctuations, packed. -/
def blockCubeFluctuation (Q : TriadicCube d) (G : Vec d → BlockVec d) :
    Vec d → BlockVec d :=
  fun x =>
    (cubeFluctuationVec Q (fun y => (G y).1) x,
      cubeFluctuationVec Q (fun y => (G y).2) x)


/-! ## From the block seminorms to the partial bounds -/

private theorem cubeBesovNegativeVectorSeminormTwo_nonneg' (Q : TriadicCube d) (s : ℝ)
    (u : Vec d → Vec d) : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s u := by
  unfold cubeBesovNegativeVectorSeminormTwo
  refine Real.sSup_nonneg ?_
  rintro y ⟨N, rfl⟩
  exact cubeBesovNegativeVectorPartialSeminormTwo_nonneg _ _ _ _


/-- The first component's finite-depth negative seminorms are bounded by the
block seminorm. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_fst_le_blockNegativeBesovTwo
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → BlockVec d)
    (hbd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => (F x).1)))
    (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => (F x).1) ≤
      blockNegativeBesovTwo Q s F := by
  have h1 : cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => (F x).1) ≤
      cubeBesovNegativeVectorSeminormTwo Q s (fun x => (F x).1) := le_csSup hbd ⟨N, rfl⟩
  have h2 : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s (fun x => (F x).2) :=
    cubeBesovNegativeVectorSeminormTwo_nonneg' Q s _
  unfold blockNegativeBesovTwo
  linarith

/-- The second component's finite-depth negative seminorms are bounded by the
block seminorm. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_snd_le_blockNegativeBesovTwo
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → BlockVec d)
    (hbd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => (F x).2)))
    (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => (F x).2) ≤
      blockNegativeBesovTwo Q s F := by
  have h1 : cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => (F x).2) ≤
      cubeBesovNegativeVectorSeminormTwo Q s (fun x => (F x).2) := le_csSup hbd ⟨N, rfl⟩
  have h2 : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s (fun x => (F x).1) :=
    cubeBesovNegativeVectorSeminormTwo_nonneg' Q s _
  unfold blockNegativeBesovTwo
  linarith


/-! ## The block duality pairing -/

/-- **The block negative/positive Besov duality pairing (carrier).**

The sum of two copies of CoarseGraining's componentwise sharp `q = 2` bound,
one per doubled component.

: the caller supplies the exponent window `hs`, the four `L^2` memberships, the
sign of `Bg`, the two integrabilities of the pairing integrands on the cube,
and the four families of finite-depth seminorm bounds.  These are exactly the
hypotheses of the upstream componentwise theorem, doubled. -/
theorem abs_cubeAverage_blockVecDot_blockCubeFluctuation_le
    (Q : TriadicCube d) (s : ℝ) (F G : Vec d → BlockVec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hF1 : MemLp (fun x => (F x).1) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hF2 : MemLp (fun x => (F x).2) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG1 : MemLp (fun x => (G x).1) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG2 : MemLp (fun x => (G x).2) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hInt1 : IntegrableOn
      (fun x => vecDot ((F x).1) (cubeFluctuationVec Q (fun y => (G y).1) x))
      (cubeSet Q) volume)
    (hInt2 : IntegrableOn
      (fun x => vecDot ((F x).2) (cubeFluctuationVec Q (fun y => (G y).2) x))
      (cubeSet Q) volume)
    (hneg1 : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => (F x).1) ≤ Bu)
    (hneg2 : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => (F x).2) ≤ Bu)
    (hpos1 : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => (G x).1) ≤ Bg)
    (hpos2 : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => (G x).2) ≤ Bg) :
    |cubeAverage Q (fun x => blockVecDot (F x) (blockCubeFluctuation Q G x))| ≤
      2 * ((d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg))) := by
  have hpoint :
      (fun x => blockVecDot (F x) (blockCubeFluctuation Q G x)) =
        fun x =>
          vecDot ((F x).1) (cubeFluctuationVec Q (fun y => (G y).1) x) +
            vecDot ((F x).2) (cubeFluctuationVec Q (fun y => (G y).2) x) := by
    funext x
    rfl
  have hsplit :
      cubeAverage Q (fun x => blockVecDot (F x) (blockCubeFluctuation Q G x)) =
        cubeAverage Q
            (fun x => vecDot ((F x).1) (cubeFluctuationVec Q (fun y => (G y).1) x)) +
          cubeAverage Q
            (fun x => vecDot ((F x).2) (cubeFluctuationVec Q (fun y => (G y).2) x)) := by
    rw [hpoint]
    exact cubeAverage_add_of_integrableOn Q _ _ hInt1 hInt2
  have hbound1 :=
    abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds_two_two
      Q s (fun x => (F x).1) (fun x => (G x).1) hs hF1 hG1 hBg hneg1 hpos1
  have hbound2 :=
    abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds_two_two
      Q s (fun x => (F x).2) (fun x => (G x).2) hs hF2 hG2 hBg hneg2 hpos2
  rw [hsplit]
  calc
    |cubeAverage Q
          (fun x => vecDot ((F x).1) (cubeFluctuationVec Q (fun y => (G y).1) x)) +
        cubeAverage Q
          (fun x => vecDot ((F x).2) (cubeFluctuationVec Q (fun y => (G y).2) x))|
        ≤ |cubeAverage Q
              (fun x => vecDot ((F x).1) (cubeFluctuationVec Q (fun y => (G y).1) x))| +
            |cubeAverage Q
              (fun x => vecDot ((F x).2) (cubeFluctuationVec Q (fun y => (G y).2) x))| :=
          abs_add_le _ _
    _ ≤ 2 * ((d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg))) := by
      linarith only [hbound1, hbound2]

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
