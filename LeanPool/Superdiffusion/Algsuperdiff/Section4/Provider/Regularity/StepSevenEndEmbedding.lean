/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenEndPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SandwichNondegeneracy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringVolume

/-!
# StepSevenEndEmbedding

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d, part two: the oscillation endpoint

## The target

```text
  3^{-(m'-1)}‖u - (u)_{(z+□_{m'-1})∩□_m}‖_{L²((z+□_{m'-1})∩□_m)} 1_{𝒢(m',z;·,·)}
    ≤ C 3^{-(m'-1)}‖u - (u)_{z'+□_{m'-1}}‖_{L²(z'+□_{m'-1})} 1_{𝒢}     (S44-G)
    ≤ C σ_m^{-1/2} 3^{(1/2)(d+γ)(m-m')}
        ( ν^{1/2}‖∇u‖_{L²(□_m)} + σ_m^{-1/2} 3^{sm}[𝐠]_{H^s(□_m)} ) .
```

## Step one: the window replacement

The manuscript replaces the truncated window `(z+□_{m'-1}) ∩ □_m` by the
off-grid cube `z'+□_{m'-1}` "at the cost of a constant `C`".  The inclusion
is the Step-7a sandwich (`StepSevenSelectionData.upper_sandwich_in`); the
comparison of the two *mean-subtracted* `L²` norms is asserted.  It is proved
here from two proved facts and one proved geometric input:

* `normalizedL2On_sub_volumeAverage_le` — the mean minimizes the `L²(S)`
  deviation, so `(u)_S` may be replaced by `(u)_T` for free;
* `normalizedL2On_le_of_subset` — nested windows compare at the square root of
  the volume ratio;
* `image_add_wellPlacedCentre_subset_truncatedWindow` — the inscribed cube
  `□_{k-1}` inside `(z+□_k)∩□_m`, which bounds the ratio by `3^d`.

The produced constant is therefore the explicit `3^{d/2}`, a `C(d)` exactly as
printed.  (The sharp constant is `2^{d/2}`; the inscribed-cube route gives
`3^{d/2}`, and the difference is inside `C`.)

## Step two: the embedding, and the summability bridge

The manuscript's second inequality is `e.fractional.Sobolev.embedding` composed
with `e.cg.Poincare.with.rhs.grad.applied`.  Two independent conditional
inputs, both named for what they are:

* **`hembed`** stays a named input here, with its producer identified.  The two
  sides sit at different summability indices:
  - `l.coarse.graining.RHS` produces the `q = 2` object.  CoarseGraining's proved
    `coarsePoincareRHSTheory`
    (`Homogenization/Book/Ch03/Theorems/CoarsePoincare.lean`)
    concludes with `scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) …`,
    i.e. `B^{-s}_{2,2}`, at ONE exponent `s` with `0 < s < 1` strictly.
  - `e.fractional.Sobolev.embedding` consumes the `q = 1` object: the tex
    prints `[∇u]_{B^{-s}_{p,1}}` (macro `\besov{-s}{p}{1}`) and the proved
    local theorem above is at `q = 1`.
  - CoarseGraining has NO change-of-summability lemma on any negative Besov
    carrier in either direction (exhaustive sweep), and NO formalization of the
    embedding.
  - The manuscript's own conversion is `[·]_{B^{-1}_{2,1}} ≤
    C(t)[·]_{B^{-t}_{2,2}}` with the geometric factor `(Σ_{n≤0}
    3^{2(1-t)n})^{1/2}`, which needs `t < 1` strictly and diverges as `t ↑ 1`.
    The hypothesis in hand is at index exactly `-1`, so the printed chain
    cannot be run as written.  CoarseGraining's own proved constant `(1 -
    3^{-2(1/2-t)})^{-1/2}` degenerating at the same endpoint is the independent
    Lean-side confirmation.  So `hbridge` is a genuine external obligation, not
    a formalization artifact: as printed, the Step-7d chain is index-broken.

## The scalar carriers

* `oscTrunc` — `3^{-(m'-1)}‖u -
  (u)_{(z+□_{m'-1})∩□_m}‖_{L²((z+□_{m'-1})∩□_m)}·1_𝒢`; this is the `oscHi` leg,
  the quantity `e.gradient.with.shom` transports.
* `oscLoc` — the same weight on `z'+□_{m'-1}`.
* `besovP1` / `besov` — `3^{-m'}‖∇u‖` in `B^{-1}_{2,1}` and in `B^{-1}_{2,2}`.
* `shomMinv`, `gradM`, `dataM` — as in `StepSevenEndPoincare`.

## References

* ABK26, Step 7d; `e.fractional.Sobolev.embedding`; the summability
  conversion.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The mean comparison across nested windows -/

/-- **The mean comparison on nested windows.**  For `S ⊆ T`,

```text
  ‖u - (u)_S‖_{L²(S)}  ≤  (|T|/|S|)^{1/2} ‖u - (u)_T‖_{L²(T)} .
```

The mean on `S` is replaced by the mean on `T` for free (the mean minimizes the
deviation), and the nested windows then compare at the square root of the
volume ratio.  This is the inequality the manuscript asserts. -/
theorem normalizedL2On_sub_average_le_of_subset {S T : Set (Vec d)} {u : Vec d → ℝ}
    (hST : S ⊆ T) (hSm : MeasurableSet S) (hSpos : 0 < (volume S).toReal)
    (hSfin : volume S ≠ ⊤) (hTpos : 0 < (volume T).toReal)
    (huS : IntegrableOn u S) (huS2 : IntegrableOn (fun x => u x ^ 2) S)
    (hint : IntegrableOn (fun x => (u x - volumeAverage T u) ^ 2) T) :
    normalizedL2On S (fun x => u x - volumeAverage S u) ≤
      Real.sqrt ((volume T).toReal / (volume S).toReal) *
        normalizedL2On T (fun x => u x - volumeAverage T u) :=
  le_trans
    (normalizedL2On_sub_volumeAverage_le hSm hSpos hSfin huS huS2 (volumeAverage T u))
    (normalizedL2On_le_of_subset (f := fun x => u x - volumeAverage T u) hST hTpos
      hSpos hint)

/-! ## 2. The volume ratio of the Step-7a sandwich pair -/

/-- **The sandwich pair's volume ratio.**  For `z ∈ □_m` and `k ≤ m`, every
translate of `□_k` has volume at most `3^d` times that of the truncated window
`(z+□_k) ∩ □_m` — the inscribed cube `□_{k-1}` of
`image_add_wellPlacedCentre_subset_truncatedWindow` supplies the lower bound. -/
theorem volume_toReal_image_add_le_three_pow_mul_truncatedWindow {m k : ℤ}
    {z : Vec d} (c : Vec d) (hz : z ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    (volume ((fun v => c + v) '' openCubeSet (originCube d k))).toReal ≤
      (3 : ℝ) ^ d * (volume (truncatedWindow z m k)).toReal := by
  have hjm : k - 1 ≤ m := by linarith only [hkm]
  have hsub := image_add_wellPlacedCentre_subset_truncatedWindow (j := k) z hz hjm
  have hle : volume ((fun y => wellPlacedCentre z m (k - 1) + y) ''
      openCubeSet (originCube d (k - 1))) ≤ volume (truncatedWindow z m k) :=
    measure_mono hsub
  have htop : volume (truncatedWindow z m k) ≠ ⊤ :=
    ne_of_lt (volume_truncatedWindow_lt_top z m k)
  have hreal : ((3 : ℝ) ^ (k - 1)) ^ d ≤ (volume (truncatedWindow z m k)).toReal := by
    rw [← volume_toReal_openCubeSet_originCube d (k - 1),
      ← volume_image_add (wellPlacedCentre z m (k - 1)) (openCubeSet (originCube d (k - 1)))]
    exact ENNReal.toReal_mono htop hle
  have hlhs : (volume ((fun v => c + v) '' openCubeSet (originCube d k))).toReal =
      ((3 : ℝ) ^ k) ^ d := by
    rw [volume_image_add, volume_toReal_openCubeSet_originCube]
  have hsplit : ((3 : ℝ) ^ k) ^ d = (3 : ℝ) ^ d * ((3 : ℝ) ^ (k - 1)) ^ d := by
    have h3 : (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ (k - 1) := by
      have hk : k - 1 + 1 = k := by ring
      have h := zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0) (k - 1)
      rw [hk] at h
      rw [h]
      ring
    rw [h3, mul_pow]
  rw [hlhs, hsplit]
  exact mul_le_mul_of_nonneg_left hreal (by positivity)

/-! ## 3. The mean comparison at the Step-7a sandwich -/

/-- **The Step-7d mean comparison, at the sandwich pair**, with the constant made
explicit:

```text
  ‖u - (u)_{(z+□_k)∩□_m}‖_{L²((z+□_k)∩□_m)}
    ≤ 3^{d/2} ‖u - (u)_{z'+□_k}‖_{L²(z'+□_k)} .
```

`hST` is `StepSevenSelectionData.upper_sandwich_in` at `k = m'-1`.  The
`3^{d/2}` is the inscribed-cube constant; the sharp value is `2^{d/2}` and the
difference is inside `C(d)`. -/
theorem stepSevenEndpointMeanComparison {m k : ℤ} {z c : Vec d} {u : Vec d → ℝ}
    (hz : z ∈ openCubeSet (originCube d m)) (hkm : k ≤ m)
    (hST : truncatedWindow z m k ⊆ (fun v => c + v) '' openCubeSet (originCube d k))
    (huS : IntegrableOn u (truncatedWindow z m k))
    (huS2 : IntegrableOn (fun x => u x ^ 2) (truncatedWindow z m k))
    (hint : IntegrableOn
      (fun x => (u x - volumeAverage ((fun v => c + v) ''
        openCubeSet (originCube d k)) u) ^ 2)
      ((fun v => c + v) '' openCubeSet (originCube d k))) :
    normalizedL2On (truncatedWindow z m k)
        (fun x => u x - volumeAverage (truncatedWindow z m k) u) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On ((fun v => c + v) '' openCubeSet (originCube d k))
          (fun x => u x - volumeAverage ((fun v => c + v) ''
            openCubeSet (originCube d k)) u) := by
  set S : Set (Vec d) := truncatedWindow z m k with hSdef
  set T : Set (Vec d) := (fun v => c + v) '' openCubeSet (originCube d k) with hTdef
  have hSm : MeasurableSet S := (isOpen_truncatedWindow z m k).measurableSet
  have hSfin : volume S ≠ ⊤ := ne_of_lt (volume_truncatedWindow_lt_top z m k)
  have hSpos : 0 < (volume S).toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_truncatedWindow_pos k hz)) hSfin
  have hTeq : (volume T).toReal = ((3 : ℝ) ^ k) ^ d := by
    rw [hTdef, volume_image_add, volume_toReal_openCubeSet_originCube]
  have hTpos : 0 < (volume T).toReal := by
    rw [hTeq]
    positivity
  have hratio := volume_toReal_image_add_le_three_pow_mul_truncatedWindow (k := k) c hz hkm
  have hdiv : (volume T).toReal / (volume S).toReal ≤ (3 : ℝ) ^ d := by
    rw [div_le_iff₀ hSpos]
    exact hratio
  have hmain := normalizedL2On_sub_average_le_of_subset hST hSm hSpos hSfin hTpos
    huS huS2 hint
  have hsq : Real.sqrt ((volume T).toReal / (volume S).toReal) ≤
      Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_le_sqrt hdiv
  exact le_trans hmain
    (mul_le_mul_of_nonneg_right hsq (normalizedL2On_nonneg _ _))

/-! ## 4. The oscillation endpoint on scalars -/

/-- The bracket identity that turns `StepSevenEndPoincare`'s output shape into the
printed Step-7d one: for `0 ≤ S`, `√S·g + S·D = √S·(g + √S·D)`. -/
theorem sqrt_mul_bracket_eq {S g D : ℝ} (hS : 0 ≤ S) :
    Real.sqrt S * g + S * D = Real.sqrt S * (g + Real.sqrt S * D) := by
  have hsq : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS
  calc Real.sqrt S * g + S * D
      = Real.sqrt S * g + (Real.sqrt S * Real.sqrt S) * D := by rw [hsq]
    _ = Real.sqrt S * (g + Real.sqrt S * D) := by ring

/-- **The Step-7d oscillation endpoint**, on abstract reals.

The four links of the manuscript's chain:

```text
  oscTrunc ≤ Cmean·oscLoc          (proved above)
  oscLoc   ≤ Cemb ·besovP1         (hembed  — e.fractional.Sobolev.embedding, mean-zero)
  besovP1  ≤ Cbr  ·besov           (hbridge — the summability change)
  besov    ≤ Cout ·Ktr·(√σ_m^{-1}·gradM + σ_m^{-1}·dataM)   (StepSevenEndPoincare)
```

composed, and the bracket rewritten into the printed
`σ_m^{-1/2}(ν^{1/2}‖∇u‖_{L²(□_m)} + σ_m^{-1/2}3^{sm}[𝐠]_{H^s(□_m)})`. -/
theorem stepSevenOscillationEndpoint {Cmean Cemb Cbr Cout Ktr oscTrunc oscLoc besovP1
    besov shomMinv gradM dataM : ℝ}
    (hCmean : 0 ≤ Cmean) (hCemb : 0 ≤ Cemb) (hCbr : 0 ≤ Cbr)
    (hshomMinv : 0 ≤ shomMinv)
    (hmean : oscTrunc ≤ Cmean * oscLoc)
    (hembed : oscLoc ≤ Cemb * besovP1)
    (hbridge : besovP1 ≤ Cbr * besov)
    (hpoincare : besov ≤ Cout * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM)) :
    oscTrunc ≤ Cmean * Cemb * Cbr * (Cout * Ktr) *
      (Real.sqrt shomMinv * (gradM + Real.sqrt shomMinv * dataM)) := by
  have h1 : Cbr * besov ≤ Cbr * (Cout * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM)) :=
    mul_le_mul_of_nonneg_left hpoincare hCbr
  have h2 : besovP1 ≤ Cbr * (Cout * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM)) := le_trans hbridge h1
  have h3 : Cemb * besovP1 ≤ Cemb * (Cbr * (Cout * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM))) :=
    mul_le_mul_of_nonneg_left h2 hCemb
  have h4 : oscLoc ≤ Cemb * (Cbr * (Cout * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM))) := le_trans hembed h3
  have h5 : Cmean * oscLoc ≤ Cmean * (Cemb * (Cbr * (Cout * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM)))) :=
    mul_le_mul_of_nonneg_left h4 hCmean
  have h6 : oscTrunc ≤ Cmean * (Cemb * (Cbr * (Cout * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM)))) := le_trans hmean h5
  have hbr := sqrt_mul_bracket_eq (S := shomMinv) (g := gradM) (D := dataM) hshomMinv
  have hkey : Cmean * (Cemb * (Cbr * (Cout * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM)))) =
      Cmean * Cemb * Cbr * (Cout * Ktr) *
        (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by ring
  rw [hkey, hbr] at h6
  exact h6

end

end Algsuperdiff.Section4.Provider.Regularity
