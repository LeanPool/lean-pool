/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.AffineExcess
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeReflection.Reflections

/-!
# OneStepCornerTransportNorms

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Transport of the excess calculus along a coordinate negation

This module transports the excess/seminorm calculus of
`Algsuperdiff/Section4/Support/AffineExcess.lean` along the **coordinate
negation**

```
σ_i := coordFaceReflection (0 : ℝ) i ,     σ_i y l = if l = i then -(y l) else y l ,
```

the linear isometric involution of `Vec d` that negates the `i`-th coordinate
(CoarseGraining's `Homogenization.coordFaceReflection` at the face coordinate
`a = 0`).

It is the **measure-side half** of the lower/mixed-face transport of the §4.3
boundary branch.  The domain cube `□_m` is origin-symmetric, so negating one
coordinate carries a window that meets the *lower* `i`-face of `□_m` to a window
that meets the *upper* `i`-face; the boundary branch therefore only ever has to
be proved for upper faces, and the lower and mixed (corner) faces are obtained
by composing the upper-face statement with the negations `σ_i`.  The present
module supplies the half of that reduction which is pure measure theory: every
norm, average, affine distance, excess and minimizer predicate appearing in the
branch is *exactly invariant* under `σ_i`, with no constant.

The two facts that drive everything are:

* `σ_i` is measure preserving and a measurable embedding, so `volume`, set
  integrals, `volumeAverage` and `normalizedL2On` transport with equality
  (`volume_preimage_coordFaceReflection` … `normalizedL2On_comp_coordFaceReflection`);
* at `a = 0` the map is *linear* and self-adjoint for `vecDot`
  (`vecDot_coordFaceReflection_zero`), so the affine competitor family is
  carried onto itself by `(c, g) ↦ (c, σ_i g)`
  (`affineEval_comp_coordFaceReflection_zero`,
  `affineDistSet_comp_coordFaceReflection_zero`).

Consequently the whole excess tower is invariant: `affineDistOn`,
`affineDistSet`, `affineExcessRaw`, `affineExcess`, and the minimizer predicate
`IsAffineMinimizer` (as an iff).  The `MemLp` side condition transports too
(`memLp_comp_coordFaceReflection`), so the hypotheses of the `NormalizedL2`
calculus survive the move.

Only the *reflected* face coordinate `a = 0` gives a linear map, so the affine
half of the module is stated at `a = 0`; the purely measure-theoretic half is
stated at a general face coordinate `a`, where it is equally true.

## References

* ABK26, §4.3 boundary branch.
* CoarseGraining,
  `Homogenization/Sobolev/Foundations/CubeReflection/Reflections.lean`
  (`coordFaceReflection`, `measurePreserving_coordFaceReflection`).
* `Algsuperdiff/Section4/Support/AffineExcess.lean` (the transported calculus).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec vecDot volumeAverage coordFaceReflection)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The coordinate negation -/

/-- **The reflection at the face coordinate `0` is the coordinate negation.**
`σ_i` negates the `i`-th coordinate and fixes every other one. -/
theorem coordFaceReflection_zero_apply (i : Fin d) (y : Vec d) (l : Fin d) :
    coordFaceReflection (0 : ℝ) i y l = if l = i then -(y l) else y l := by
  rw [HCPolySupport.coordFaceReflection_apply]
  by_cases hli : l = i
  · rw [ite_eq_left hli, ite_eq_left hli]
    ring
  · rw [ite_eq_right hli, ite_eq_right hli]

/-- The coordinate reflection is a measurable embedding: it is measurable (being
measure preserving), injective (being an involution), and it maps measurable
sets to measurable sets (its image is its own preimage). -/
theorem measurableEmbedding_coordFaceReflection (a : ℝ) (i : Fin d) :
    MeasurableEmbedding (coordFaceReflection (d := d) a i) := by
  have hmeas : Measurable (coordFaceReflection (d := d) a i) :=
    (HCPolySupport.measurePreserving_coordFaceReflection a i).measurable
  have hinv : Function.Involutive (coordFaceReflection (d := d) a i) :=
    HCPolySupport.coordFaceReflection_involutive a i
  refine ⟨hinv.injective, hmeas, ?_⟩
  intro s hs
  have himg : coordFaceReflection (d := d) a i '' s
      = coordFaceReflection (d := d) a i ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, hinv y]
      exact hy
    · intro hx
      exact ⟨coordFaceReflection a i x, hx, hinv x⟩
  rw [himg]
  exact hmeas hs

/-! ## 2. The measure-side transport -/

/-- The reflection preserves Lebesgue measure, so a window and its preimage have
the same volume. -/
theorem volume_preimage_coordFaceReflection {a : ℝ} (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) :
    volume (coordFaceReflection (d := d) a i ⁻¹' W) = volume W :=
  (HCPolySupport.measurePreserving_coordFaceReflection a i).measure_preimage
    hW.nullMeasurableSet

/-- **The change of variables.**  Integrating `f ∘ σ_i` over the reflected window
is integrating `f` over the window, with no Jacobian. -/
theorem setIntegral_comp_coordFaceReflection {a : ℝ} (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) (f : Vec d → ℝ) :
    ∫ y in coordFaceReflection (d := d) a i ⁻¹' W, f (coordFaceReflection a i y) ∂volume
      = ∫ y in W, f y ∂volume :=
  ((HCPolySupport.measurePreserving_coordFaceReflection a i).restrict_preimage
    hW).integral_comp (measurableEmbedding_coordFaceReflection a i) f

/-- The volume average is invariant: both the normalizer and the integral
transport. -/
theorem volumeAverage_comp_coordFaceReflection {a : ℝ} (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) (f : Vec d → ℝ) :
    volumeAverage (coordFaceReflection (d := d) a i ⁻¹' W)
        (fun y => f (coordFaceReflection a i y)) = volumeAverage W f := by
  change (volume (coordFaceReflection (d := d) a i ⁻¹' W)).toReal⁻¹
      * ∫ y in coordFaceReflection (d := d) a i ⁻¹' W,
          f (coordFaceReflection a i y) ∂volume
    = (volume W).toReal⁻¹ * ∫ y in W, f y ∂volume
  rw [volume_preimage_coordFaceReflection i hW, setIntegral_comp_coordFaceReflection i hW f]

/-- The volume-normalized `L²` seminorm is invariant under the reflection. -/
theorem normalizedL2On_comp_coordFaceReflection {a : ℝ} (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) (f : Vec d → ℝ) :
    normalizedL2On (coordFaceReflection (d := d) a i ⁻¹' W)
        (fun y => f (coordFaceReflection a i y)) = normalizedL2On W f := by
  change Real.sqrt (volumeAverage (coordFaceReflection (d := d) a i ⁻¹' W)
      (fun y => f (coordFaceReflection a i y) ^ 2))
    = Real.sqrt (volumeAverage W (fun y => f y ^ 2))
  exact congrArg Real.sqrt
    (volumeAverage_comp_coordFaceReflection (a := a) i hW (fun x => f x ^ 2))

/-! ## 3. The affine transport at the face coordinate `0` -/

/-- **Self-adjointness of the coordinate negation.**  At `a = 0` the reflection is
linear and orthogonal, so it moves across the euclidean pairing. -/
theorem vecDot_coordFaceReflection_zero (i : Fin d) (g y : Vec d) :
    vecDot g (coordFaceReflection (0 : ℝ) i y)
      = vecDot (coordFaceReflection (0 : ℝ) i g) y := by
  simp only [vecDot]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [coordFaceReflection_zero_apply, coordFaceReflection_zero_apply]
  by_cases hji : j = i
  · rw [ite_eq_left hji, ite_eq_left hji]
    ring
  · rw [ite_eq_right hji, ite_eq_right hji]

/-- **The affine family is carried onto itself.**  Precomposing the affine
function `(c, g)` with the coordinate negation is the affine function
`(c, σ_i g)`: the intercept is untouched and the slope is reflected. -/
theorem affineEval_comp_coordFaceReflection_zero (i : Fin d) (c : ℝ) (g y : Vec d) :
    affineEval c g (coordFaceReflection (0 : ℝ) i y)
      = affineEval c (coordFaceReflection (0 : ℝ) i g) y := by
  unfold affineEval
  rw [vecDot_coordFaceReflection_zero]

/-- The affine distance is invariant, with the slope reflected along. -/
theorem affineDistOn_comp_coordFaceReflection_zero (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) (f : Vec d → ℝ) (c : ℝ) (g : Vec d) :
    affineDistOn (coordFaceReflection (0 : ℝ) i ⁻¹' W)
        (fun y => f (coordFaceReflection (0 : ℝ) i y)) c
        (coordFaceReflection (0 : ℝ) i g)
      = affineDistOn W f c g := by
  have hfun : (fun x : Vec d =>
        f (coordFaceReflection (0 : ℝ) i x)
          - affineEval c (coordFaceReflection (0 : ℝ) i g) x)
      = fun x : Vec d =>
        f (coordFaceReflection (0 : ℝ) i x)
          - affineEval c g (coordFaceReflection (0 : ℝ) i x) := by
    funext x
    rw [affineEval_comp_coordFaceReflection_zero]
  change normalizedL2On (coordFaceReflection (0 : ℝ) i ⁻¹' W)
      (fun x => f (coordFaceReflection (0 : ℝ) i x)
        - affineEval c (coordFaceReflection (0 : ℝ) i g) x)
    = normalizedL2On W (fun x => f x - affineEval c g x)
  rw [hfun]
  exact normalizedL2On_comp_coordFaceReflection (a := (0 : ℝ)) i hW
    (fun x => f x - affineEval c g x)

/-- **The competitor set is invariant.**  The bijection `(c, g) ↦ (c, σ_i g)` of
the affine parameter space `ℝ × Vec d` --- its own inverse, by involutivity ---
matches the two competitor families. -/
theorem affineDistSet_comp_coordFaceReflection_zero (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) (f : Vec d → ℝ) :
    affineDistSet (coordFaceReflection (0 : ℝ) i ⁻¹' W)
        (fun y => f (coordFaceReflection (0 : ℝ) i y)) = affineDistSet W f := by
  ext t
  simp only [affineDistSet, Set.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(p.1, coordFaceReflection (0 : ℝ) i p.2), ?_⟩
    have h := affineDistOn_comp_coordFaceReflection_zero i hW f p.1
      (coordFaceReflection (0 : ℝ) i p.2)
    rw [HCPolySupport.coordFaceReflection_involutive] at h
    exact h.symm
  · rintro ⟨p, rfl⟩
    exact ⟨(p.1, coordFaceReflection (0 : ℝ) i p.2),
      affineDistOn_comp_coordFaceReflection_zero i hW f p.1 p.2⟩

/-- The unnormalized excess is invariant: it is the infimum of an invariant
set. -/
theorem affineExcessRaw_comp_coordFaceReflection_zero (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) (f : Vec d → ℝ) :
    affineExcessRaw (coordFaceReflection (0 : ℝ) i ⁻¹' W)
        (fun y => f (coordFaceReflection (0 : ℝ) i y)) = affineExcessRaw W f := by
  unfold affineExcessRaw
  rw [affineDistSet_comp_coordFaceReflection_zero i hW f]

/-- The best-affine predicate transports both ways: `(c, g)` is a minimizer for
`f` on `W` exactly when `(c, σ_i g)` is one for `f ∘ σ_i` on `σ_i ⁻¹' W`. -/
theorem isAffineMinimizer_comp_coordFaceReflection_zero (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) (f : Vec d → ℝ) (c : ℝ) (g : Vec d) :
    IsAffineMinimizer (coordFaceReflection (0 : ℝ) i ⁻¹' W)
        (fun y => f (coordFaceReflection (0 : ℝ) i y)) c
        (coordFaceReflection (0 : ℝ) i g)
      ↔ IsAffineMinimizer W f c g := by
  unfold IsAffineMinimizer
  rw [affineDistOn_comp_coordFaceReflection_zero i hW f c g,
    affineExcessRaw_comp_coordFaceReflection_zero i hW f]

/-! ## 4. The `L²` side condition -/

/-- The `MemLp` hypothesis of the `NormalizedL2` calculus transports along the
reflection, so no side condition is lost when the boundary branch is moved. -/
theorem memLp_comp_coordFaceReflection {a : ℝ} (i : Fin d) {W : Set (Vec d)}
    (hW : MeasurableSet W) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) :
    MemLp (fun y => f (coordFaceReflection (d := d) a i y)) 2
      (volume.restrict (coordFaceReflection (d := d) a i ⁻¹' W)) :=
  hf.comp_measurePreserving
    ((HCPolySupport.measurePreserving_coordFaceReflection a i).restrict_preimage hW)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
