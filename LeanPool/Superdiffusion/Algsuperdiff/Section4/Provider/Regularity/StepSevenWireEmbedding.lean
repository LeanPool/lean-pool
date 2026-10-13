/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenEndEmbedding
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportNorms
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.OscillationPoincare
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfacesComponentwise

/-!
# StepSevenWireEmbedding

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d: wiring the mean-zero fractional Sobolev embedding

## The gap this module closes

The Step-7d oscillation endpoint carries a second conditional input
`hembed : oscLoc ≤ Cemb · besovP1` — the mean-zero fractional Sobolev embedding
`e.fractional.Sobolev.embedding`, read at `(s,p,q) = (1,2,1)` (the zero-trace
twin is the wrong one: `u` carries the boundary datum `h`, not `0`).  The
producer is
`cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm`,
whose left side is `‖u - (u)_Q‖_{L²(Q)}`, whose binder is `H1Function` with no
zero-trace hypothesis, and whose constant is dimension-only.  Two carrier
residues remain, and both are closed here.

## Residue (a): the coordinate aggregation — the constant is `d`, not `√d`

The Section-3 producer's right-hand side is the coordinate sum
`Σ_i [∂_i u]_{B^{-1}_{2,1}}` of scalar circ norms, while the `besovP1` slot is
a single vector object.
The bridge is proved upstream, per coordinate, at constant **one**:
CoarseGraining's

```text
  cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
```

says
that whenever `B` dominates every finite-depth vector partial seminorm
`cubeBesovNegativeVectorPartialSeminorm Q s N F`, each coordinate's circ norm is
at most `3^{s·scale}·B`.  Summing the `d` coordinates gives the factor `d`.

The factor is `d`, not `√d`: `√d` is the Cauchy--Schwarz constant at the
depth level, and it is attainable, but the available upstream bridge is the
per-coordinate one at constant `1`, so the honest aggregation in the proved
carriers costs `d`.  Both are `C(d)`; the printed constant is `C(d)`.  Nothing
else moves.

## Residue (b): the off-grid cube `z'+□_{m'-1}`

`z'` is the clamped, off-lattice centre, so `z'+□_{m'-1}` is not a `TriadicCube`
and the Section-3 producer does not apply to it directly.
`normalizedL2On_image_add_sub_average_le_cubeBesovOscillation` performs exactly
that recovery, from three proved ingredients and no new analysis:

* `image_add_eq_translateSet` — `z'+□ = translateSet z' □`;
* `normalizedL2On_sub_volumeAverage_le` — the mean minimizes the deviation, so
  the §4.4 window's own mean may be replaced by the origin-cube average
  `(u(·+z'))_{□}` for free;

together with the Section-3 identity
`normalizedL2SqOnSet_openCubeSet_centred_eq_cubeBesovOscillation_sq`.

## The scale normalization (one factor of `3`)

Everything here is stated at the scale normalization of `Q`: the oscillation
carries `(cubeScaleFactor Q)⁻¹ = 3^{-Q.scale}` and the negative Besov carrier
`cubeBesovNegativeVectorSeminorm Q 1 F` is `3^{-Q.scale}‖F‖_{B^{-1}_{2,1}(Q)}`
already.  At `Q.scale = m'-1` the printed display weights the oscillation by
`3^{-(m'-1)}` (matching) and the Besov leg by `3^{-m'}` (one factor `3`
smaller); that single `3` is inside the printed `C`, and no exponent moves.

## References

* ABK26, `e.fractional.Sobolev.embedding`; Step 7d.
* `Algsuperdiff/Section3/Provider/Besov/OscillationPoincare.lean`.
* CoarseGraining,
  `Homogenization/Deterministic/WeakNormInterfacesComponentwise.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section3.Provider.Besov
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The embedding constant -/

/-- **The Step-7d embedding constant**: the Section-3 multiscale Poincaré constant
times the coordinate count `d`.  Both factors are dimension-only — no
ellipticity object of any kind occurs. -/
noncomputable def stepSevenEmbeddingConst (d : ℕ) : ℝ :=
  (d : ℝ) * oscillationMultiscalePoincareConstant d

theorem stepSevenEmbeddingConst_nonneg (d : ℕ) : 0 ≤ stepSevenEmbeddingConst d  :=
  mul_nonneg (Nat.cast_nonneg d) (oscillationMultiscalePoincareConstant_nonneg d)

/-! ## 2. Residue: the coordinate aggregation -/

/-- **The coordinate aggregation, at the proved constant `d`.**  If `B` dominates
every finite-depth vector partial seminorm of `F` on `Q`, then the coordinate
sum of the scalar negative circ norms is at most `d · 3^{s·scale} · B`.

The per-coordinate step is CoarseGraining's own bridge at constant `1`; the `d`
is the plain coordinate count. -/
theorem sum_cubeBesovCircNorm_le_dim_mul (Q : TriadicCube d) (s : ℝ)
    (F : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N F ≤ B) :
    ∑ i : Fin d, cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => F x i) ≤
      (d : ℝ) * (cubeBesovScaleWeight (-s) Q * B) := by
  have hcoord : ∀ i : Fin d,
      cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => F x i) ≤
        cubeBesovScaleWeight (-s) Q * B := fun i =>
    circNorm_component_le_negativeVectorPartialBound
      Q s F i hB
  calc ∑ i : Fin d, cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => F x i)
      ≤ ∑ _i : Fin d, cubeBesovScaleWeight (-s) Q * B :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * (cubeBesovScaleWeight (-s) Q * B) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 3. The embedding at the note normalization -/

private theorem cubeScaleFactor_pos_aux (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  rw [cubeScaleFactor]
  exact zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale

/-- **`e.fractional.Sobolev.embedding` at the §4.4 cube, from a uniform partial
bound.**  For every `H¹(Q)` function `u` and every `B` dominating the
finite-depth vector partial seminorms of `∇u` at index `1`,

```text
  3^{-scale}‖u - (u)_Q‖_{L²(Q)}  ≤  d · C_osc(d) · B .
```

This is the `hembed` slot: `oscLoc ≤ Cemb · besov`, at the scale normalization,
with a coefficient-free `C(d)`.  Unconditional beyond the printed embedding's
own binders. -/
theorem stepSevenEmbedding_of_partialBound (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N u.grad ≤ B) :
    (cubeScaleFactor Q)⁻¹ * cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ≤
      stepSevenEmbeddingConst d * B  := by
  have hQpos : 0 < cubeScaleFactor Q := cubeScaleFactor_pos_aux Q
  have hosc :=
    cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm
      Q u
  have hsum := sum_cubeBesovCircNorm_le_dim_mul Q 1 u.grad hB
  have hweight : cubeBesovScaleWeight (-1) Q = cubeScaleFactor Q :=
    cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor Q
  rw [hweight] at hsum
  have hC0 : (0 : ℝ) ≤ oscillationMultiscalePoincareConstant d :=
    oscillationMultiscalePoincareConstant_nonneg d
  have hchain : cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ≤
      oscillationMultiscalePoincareConstant d * ((d : ℝ) * (cubeScaleFactor Q * B)) :=
    le_trans hosc (mul_le_mul_of_nonneg_left hsum hC0)
  have hinv : (0 : ℝ) ≤ (cubeScaleFactor Q)⁻¹ := (inv_pos.mpr hQpos).le
  have hstep := mul_le_mul_of_nonneg_left hchain hinv
  have hcancel : (cubeScaleFactor Q)⁻¹ *
      (oscillationMultiscalePoincareConstant d * ((d : ℝ) * (cubeScaleFactor Q * B))) =
      stepSevenEmbeddingConst d * B *
        ((cubeScaleFactor Q)⁻¹ * cubeScaleFactor Q) := by
    rw [stepSevenEmbeddingConst]; ring
  rw [inv_mul_cancel₀ (ne_of_gt hQpos), mul_one] at hcancel
  linarith only [hstep, hcancel.ge, hcancel.le]

/-- **`e.fractional.Sobolev.embedding` at the §4.4 cube, at the negative Besov `q =
1` carrier.**  The `BddAbove` binder is the printed membership `∇u ∈
B^{-1}_{2,1}(Q)` in the upstream interface's own form. -/
theorem stepSevenEmbedding (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) (hbdd : BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminorm Q 1 N u.grad)) :
    (cubeScaleFactor Q)⁻¹ * cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ≤
      stepSevenEmbeddingConst d * cubeBesovNegativeVectorSeminorm Q 1 u.grad  := by
  refine stepSevenEmbedding_of_partialBound Q u ?_
  intro N
  exact le_csSup hbdd (Set.mem_range_self N)

/-! ## 4. Residue (b): the off-grid window, by translating the sample -/

private theorem normalizedL2On_eq_sqrt_normalizedL2SqOnSet (W : Set (Vec d))
    (f : Vec d → ℝ) : normalizedL2On W f = Real.sqrt (normalizedL2SqOnSet W f) := rfl

/-- **The off-grid recovery, by translating the sample.**

For an off-lattice centre `c` and a triadic cube `Q`, the §4.4 mean-subtracted
`L²` oscillation on the translated window `c+□_Q` is at most the origin-cube
oscillation of the translated sample:

```text
  ‖u - (u)_{c+□_Q}‖_{L²(c+□_Q)}  ≤  ‖v - (v)_{□_Q}‖_{L²(□_Q)} ,
                                      v = u(·+c) .
```

The mean is replaced for free (it minimizes the deviation) and the normalized
`L²` square transports under translation — no constant, no new analysis. -/
theorem normalizedL2On_image_add_sub_average_le_cubeBesovOscillation
    {Q : TriadicCube d} {c : Vec d} {w : Vec d → ℝ}
    (v : H1Function (openCubeSet Q)) (hv : ∀ y, v.toFun y = w (y + c))
    (hTm : MeasurableSet ((fun y => c + y) '' openCubeSet Q))
    (hTpos : 0 < (volume ((fun y => c + y) '' openCubeSet Q)).toReal)
    (hTfin : volume ((fun y => c + y) '' openCubeSet Q) ≠ ⊤)
    (hw : IntegrableOn w ((fun y => c + y) '' openCubeSet Q))
    (hw2 : IntegrableOn (fun x => w x ^ 2) ((fun y => c + y) '' openCubeSet Q)) :
    normalizedL2On ((fun y => c + y) '' openCubeSet Q)
        (fun x => w x - volumeAverage ((fun y => c + y) '' openCubeSet Q) w) ≤
      cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => v.toFun x) := by
  set A : ℝ := cubeAverage Q (fun x => v.toFun x) with hA
  have hmin := normalizedL2On_sub_volumeAverage_le hTm hTpos hTfin hw hw2 A
  have himg : (fun y => c + y) '' openCubeSet Q = translateSet c (openCubeSet Q) :=
    image_add_eq_translateSet c (openCubeSet Q)
  have htr : normalizedL2SqOnSet (translateSet c (openCubeSet Q)) (fun x => w x - A) =
      normalizedL2SqOnSet (openCubeSet Q) (fun y => w (y + c) - A) :=
    normalizedL2SqOnSet_translateSet c (openCubeSet Q) (fun x => w x - A)
  have hfun : (fun y => w (y + c) - A) = fun y => v.toFun y - A := by
    funext y; rw [hv y]
  have hsq :=
    normalizedL2SqOnSet_openCubeSet_centred_eq_cubeBesovOscillation_sq Q v
  have hval : normalizedL2SqOnSet ((fun y => c + y) '' openCubeSet Q) (fun x => w x - A) =
      cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => v.toFun x) ^ 2 := by
    rw [himg, htr, hfun, hA]
    exact hsq
  have hrhs : normalizedL2On ((fun y => c + y) '' openCubeSet Q) (fun x => w x - A) =
      cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => v.toFun x) := by
    rw [normalizedL2On_eq_sqrt_normalizedL2SqOnSet, hval,
      Real.sqrt_sq (cubeBesovOscillation_nonneg Q (2 : ℝ≥0∞) _)]
  rw [← hrhs]
  exact hmin

end

end Algsuperdiff.Section4.Provider.Regularity
