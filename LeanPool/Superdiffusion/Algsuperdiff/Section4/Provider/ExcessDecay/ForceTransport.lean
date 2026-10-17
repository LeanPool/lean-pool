/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.HighContrastHomogenization.Support.Geometry.Translation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.DefinitionsAPI

/-!
# ForceTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The A4 transport of the fractional (Gagliardo) force seminorm

The frozen §4.3 anchor writes its force leg as

```text
  [g]_{H^s(W)} = normalizedGagliardoESeminormOn W s g ,
      W = ((z + □_{n+2}) ∩ □_m) ,
```

while every proved §4.3 estimate lives in the translated frame at the
**origin** cube `□_{n+2}`.  The anchor's `z` is an **arbitrary real point** of
`□_m`, so that lemma does not apply.

This module proves the real-translation statement directly.  The route is the
one the lattice proof uses, carried out on an arbitrary set: the map `x ↦ x +
z` is measure preserving for the *restricted* Lebesgue measure between `A` and
`z + A` (CoarseGraining's `measurePreserving_addRight_restrict_translateSet`),
and `volume (z + A) = volume A`, so it is measure preserving for **both** slots
of `normalizedGagliardoMeasureOn` — the volume-normalized first slot and the
plain restricted second slot.  The Gagliardo kernel is translation covariant
because `dist (x + z) (y + z) = dist x y`, so the two `eLpNorm`s agree.  No
constant and no side condition appear: the identity is exact, and holds for an
arbitrary (possibly non-measurable) `f`, because it is proved through the
`lintegral` form of `eLpNorm` and a *measurable equivalence*.

## Main results

* `normalizedGagliardoMeasureOn_translateSet`,
  `measurePreserving_prodMap_addRight_normalizedGagliardoMeasureOn` — the
  two-slot change of variables.
* `normalizedGagliardo / `normalizedGagliardo — the real-translation covariance
  `[f]_{H^s(z+A)} = [f(· + z)]_{H^s(A)}`.
* `normalizedGagliardo — evenness.
* `eLpNorm_normalizedVolumeMeasureOn_translateSet` — the same change of
  variables in the one-slot (`L^p`) measure, used by the `L²` carrier bridge.
* `normalizedGagliardo — on the *open* realization of a triadic cube the
  anchor's object is CoarseGraining's `cubeGagliardoESeminorm`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the force leg `[g]_{H^s}` on
  the window `(z+□_{n+2}) ∩ □_m`); (the definition of `[·]_{W^{s,p}}`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. `eLpNorm` under a measure-preserving measurable equivalence -/

omit [NormedSpace ℝ E] in
/-- Change of variables for `eLpNorm` along a measurable equivalence, at finite
exponent.  Stated through the `lintegral` form, so **no measurability of the
integrand is required** — the point at which the arbitrary force field `g` of
the anchor is admissible. -/
private theorem eLpNorm_comp_measurableEquiv {alpha beta : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta] {mu : Measure alpha}
    {nu : Measure beta} (e : alpha ≃ᵐ beta)
    (he : MeasurePreserving (fun x => e x) mu nu) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) (f : beta → E) :
    eLpNorm f p nu = eLpNorm (fun x => f (e x)) p mu := by
  by_cases hf : AEStronglyMeasurable f nu
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt
        (show AEStronglyMeasurable (fun x => f (e x)) mu from hf.comp_measurePreserving he)]
    congr 1
    exact MeasurePreserving.lintegral_map_equiv (fun a => ‖f a‖ₑ ^ p.toReal) e he
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, eLpNorm_of_not_aestronglyMeasurable]
    intro h
    exact hf ((he.aestronglyMeasurable_comp_iff e.measurableEmbedding).1 h)

/-! ## 2. The one-slot change of variables -/

/-- The volume-normalized measure of a translate is the pushforward of the
volume-normalized measure. -/
theorem normalizedVolumeMeasureOn_translateSet (z : Vec d) (A : Set (Vec d)) :
    Support.normalizedVolumeMeasureOn (translateSet z A) =
      Measure.map (fun x : Vec d => x + z) (Support.normalizedVolumeMeasureOn A) := by
  rw [Support.normalizedVolumeMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
    Measure.map_smul (f := fun x : Vec d => x + z) (hf := (measurable_add_const z).aemeasurable),
    (measurePreserving_addRight_restrict_translateSet z A).map_eq,
    volume_translateSet_eq]

/-- `x ↦ x + z` is measure preserving from `⨍_A` to `⨍_{z+A}`. -/
theorem measurePreserving_addRight_normalizedVolumeMeasureOn (z : Vec d)
    (A : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x + z)
      (Support.normalizedVolumeMeasureOn A)
      (Support.normalizedVolumeMeasureOn (translateSet z A)) :=
  ⟨(MeasurableEquiv.addRight z).measurable,
    (normalizedVolumeMeasureOn_translateSet z A).symm⟩

omit [NormedSpace ℝ E] in
/-- **The `L^p` norm over a translate.**  Exact, with no measurability side
condition. -/
theorem eLpNorm_normalizedVolumeMeasureOn_translateSet (z : Vec d)
    (A : Set (Vec d)) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (f : Vec d → E) :
    eLpNorm f p (Support.normalizedVolumeMeasureOn (translateSet z A)) =
      eLpNorm (fun x => f (x + z)) p (Support.normalizedVolumeMeasureOn A) :=
  eLpNorm_comp_measurableEquiv (MeasurableEquiv.addRight z)
    (measurePreserving_addRight_normalizedVolumeMeasureOn z A) hp0 hpt f

omit [NormedSpace ℝ E] in
/-- The same in the frozen statement's `(fun y => z + y) '' A` spelling. -/
theorem eLpNorm_normalizedVolumeMeasureOn_image_add (z : Vec d) (A : Set (Vec d))
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) (f : Vec d → E) :
    eLpNorm f p (Support.normalizedVolumeMeasureOn ((fun y => z + y) '' A)) =
      eLpNorm (fun x => f (x + z)) p (Support.normalizedVolumeMeasureOn A) := by
  rw [image_add_eq_translateSet z A,
    eLpNorm_normalizedVolumeMeasureOn_translateSet z A hp0 hpt]

/-! ## 3. The two-slot change of variables -/

/-- **The Gagliardo product measure of a translate is the pushforward under the
pair translation.**  Both slots move: the normalized first slot because the
normalizing volume is translation invariant, the plain second slot because
restricted Lebesgue measure is. -/
theorem normalizedGagliardoMeasureOn_translateSet (z : Vec d) (A : Set (Vec d)) :
    Support.normalizedGagliardoMeasureOn (translateSet z A) =
      Measure.map (Prod.map (fun x : Vec d => x + z) (fun x : Vec d => x + z))
        (Support.normalizedGagliardoMeasureOn A) := by
  have : SFinite (volume.restrict A) := inferInstance
  have : SFinite (volume.restrict (translateSet z A)) := inferInstance
  have hmeas : Measurable (fun x : Vec d => x + z) := measurable_id.add_const z
  rw [Support.normalizedGagliardoMeasureOn_def, Support.normalizedGagliardoMeasureOn_def,
    Support.normalizedVolumeMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
    Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_smul (hf := (hmeas.prodMap hmeas).aemeasurable),
    ← Measure.map_prod_map _ _ hmeas hmeas,
    (measurePreserving_addRight_restrict_translateSet z A).map_eq,
    volume_translateSet_eq]

/-- The pair translation is measure preserving for the Gagliardo product
measure. -/
theorem measurePreserving_prodMap_addRight_normalizedGagliardoMeasureOn (z : Vec d)
    (A : Set (Vec d)) :
    MeasurePreserving
      (fun w => (((MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d).prodCongr
        (MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d))) w)
      (Support.normalizedGagliardoMeasureOn A)
      (Support.normalizedGagliardoMeasureOn (translateSet z A)) := by
  refine ⟨(MeasurableEquiv.prodCongr _ _).measurable, ?_⟩
  rw [normalizedGagliardoMeasureOn_translateSet z A]
  rfl

/-! ## 4. The real-translation covariance of the fractional seminorm -/

/-- **`[f]_{H^s(z+A)} = [f(· + z)]_{H^s(A)}`** for an **arbitrary real**
translation vector `z` and an arbitrary set `A`.

This is the statement CoarseGraining does not have: its `cubeGagliardoESeminorm` lattice
translation only moves a cube by an integer multiple of its scale factor.  The identity is
exact — no constant, no `s`-restriction, no regularity of `f`. -/
theorem normalizedGagliardoESeminormOn_translateSet (z : Vec d) (A : Set (Vec d))
    (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn (translateSet z A) s f =
      Support.normalizedGagliardoESeminormOn A s (fun x => f (x + z)) := by
  have hker : (fun w : Vec d × Vec d =>
        Gagliardo.gagliardoKernel s 2 f
          (((MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d).prodCongr
            (MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d)) w)) =
      Gagliardo.gagliardoKernel s 2 (fun x => f (x + z)) := by
    funext w
    change Gagliardo.gagliardoKernel s 2 f (w.1 + z, w.2 + z) =
      Gagliardo.gagliardoKernel s 2 (fun x => f (x + z)) w
    rw [Gagliardo.gagliardoKernel_apply, Gagliardo.gagliardoKernel_apply,
      dist_add_right]
  rw [Support.normalizedGagliardoESeminormOn_def,
    Support.normalizedGagliardoESeminormOn_def,
    eLpNorm_comp_measurableEquiv
      ((MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d).prodCongr
        (MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d))
      (measurePreserving_prodMap_addRight_normalizedGagliardoMeasureOn z A)
      (by norm_num) (by norm_num), hker]

/-- The same in the frozen statement's `(fun y => z + y) '' A` spelling: the
anchor's force leg, read at the origin cube. -/
theorem normalizedGagliardoESeminormOn_image_add (z : Vec d) (A : Set (Vec d))
    (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn ((fun y => z + y) '' A) s f =
      Support.normalizedGagliardoESeminormOn A s (fun x => f (x + z)) := by
  rw [image_add_eq_translateSet z A, normalizedGagliardoESeminormOn_translateSet]

/-! ## 5. Evenness -/

/-- **The fractional seminorm is even**: the kernel only sees `f x - f y`. -/
theorem normalizedGagliardoESeminormOn_neg (A : Set (Vec d)) (s : ℝ)
    (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn A s (fun x => -f x) =
      Support.normalizedGagliardoESeminormOn A s f := by
  have hneg : (fun x => -f x) = -f := rfl
  rw [Support.normalizedGagliardoESeminormOn_def,
    Support.normalizedGagliardoESeminormOn_def, hneg,
    Gagliardo.gagliardoKernel_neg]
  exact eLpNorm_neg _ _ _

/-! ## 6. The force datum transports -/

omit [NormedSpace ℝ E] in
/-- `L^p` membership transports along a measure-preserving measurable
equivalence. -/
private theorem memLp_comp_measurableEquiv {alpha beta : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta] {mu : Measure alpha}
    {nu : Measure beta} (e : alpha ≃ᵐ beta)
    (he : MeasurePreserving (fun x => e x) mu nu) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) {f : beta → E} (hf : MemLp f p nu) :
    MemLp (fun x => f (e x)) p mu := by
  rw [memLp_iff, ← eLpNorm_comp_measurableEquiv e he hp0 hpt f]
  exact hf.eLpNorm_lt_top

omit [NormedSpace ℝ E] in
/-- **The `L²` half of the force datum transports.**  `g ∈ L^p(z+A)` in the
anchor's normalized measure is `g(· + z) ∈ L^p(A)`. -/
theorem memLp_normalizedVolumeMeasureOn_image_add {z : Vec d} {A : Set (Vec d)}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) {f : Vec d → E}
    (hf : MemLp f p (Support.normalizedVolumeMeasureOn ((fun y => z + y) '' A))) :
    MemLp (fun x => f (x + z)) p (Support.normalizedVolumeMeasureOn A) := by
  rw [image_add_eq_translateSet z A] at hf
  exact memLp_comp_measurableEquiv (MeasurableEquiv.addRight z)
    (measurePreserving_addRight_normalizedVolumeMeasureOn z A) hp0 hpt hf

/-- **The fractional half of the force datum transports.**  The Gagliardo kernel
of `g` is `L²` for the anchor's window measure exactly when the kernel of the
transported force is `L²` at the origin frame. -/
theorem memLp_gagliardoKernel_image_add {z : Vec d} {A : Set (Vec d)} {s : ℝ}
    {f : Vec d → E}
    (hf : MemLp (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn ((fun y => z + y) '' A))) :
    MemLp (Gagliardo.gagliardoKernel s 2 (fun x => f (x + z))) 2
      (Support.normalizedGagliardoMeasureOn A) := by
  have hker : (fun w : Vec d × Vec d =>
        Gagliardo.gagliardoKernel s 2 f
          (((MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d).prodCongr
            (MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d)) w)) =
      Gagliardo.gagliardoKernel s 2 (fun x => f (x + z)) := by
    funext w
    change Gagliardo.gagliardoKernel s 2 f (w.1 + z, w.2 + z) =
      Gagliardo.gagliardoKernel s 2 (fun x => f (x + z)) w
    rw [Gagliardo.gagliardoKernel_apply, Gagliardo.gagliardoKernel_apply,
      dist_add_right]
  rw [image_add_eq_translateSet z A] at hf
  have := memLp_comp_measurableEquiv
    ((MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d).prodCongr
      (MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d))
    (measurePreserving_prodMap_addRight_normalizedGagliardoMeasureOn z A)
    (by norm_num) (by norm_num) hf
  rwa [hker] at this

/-! ## 7. The open cube -/

/-- On the *open* realization of a triadic cube the volume-normalized measure is
CoarseGraining's `normalizedCubeMeasure` (the boundary is Lebesgue null). -/
theorem normalizedVolumeMeasureOn_openCubeSet (Q : TriadicCube d) :
    Support.normalizedVolumeMeasureOn (openCubeSet Q) = normalizedCubeMeasure Q := by
  have h : Support.normalizedVolumeMeasureOn (openCubeSet Q) =
      Support.normalizedVolumeMeasureOn (cubeSet Q) := by
    rw [Support.normalizedVolumeMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
      volume_openCubeSet_eq_volume_cubeSet,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [h, Support.normalizedVolumeMeasureOn_cubeSet]

/-- The Gagliardo product measure on the open cube is CoarseGraining's. -/
theorem normalizedGagliardoMeasureOn_openCubeSet (Q : TriadicCube d) :
    Support.normalizedGagliardoMeasureOn (openCubeSet Q) =
      Gagliardo.gagliardoCubeMeasure Q := by
  rw [Support.normalizedGagliardoMeasureOn_def, normalizedVolumeMeasureOn_openCubeSet,
    Gagliardo.gagliardoCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- **The anchor's fractional seminorm on an open cube is CoarseGraining's cube
seminorm.**  The bridge into the whole `cubeGagliardo*` A. -/
theorem normalizedGagliardoESeminormOn_openCubeSet (Q : TriadicCube d) (s : ℝ)
    (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn (openCubeSet Q) s f =
      Gagliardo.cubeGagliardoESeminorm Q s 2 f := by
  rw [Support.normalizedGagliardoESeminormOn_def, normalizedGagliardoMeasureOn_openCubeSet,
    Gagliardo.Internal.cubeGagliardoESeminorm_def]

/-- **The anchor's force leg, transported.**  The `[g]_{H^s}` slot of the frozen
statement, on the bare translated parent window, equals CoarseGraining's cube
seminorm of the transported force at the origin cube. -/
theorem normalizedGagliardoESeminormOn_image_add_openCubeSet (z : Vec d)
    (Q : TriadicCube d) (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn ((fun y => z + y) '' openCubeSet Q) s f =
      Gagliardo.cubeGagliardoESeminorm Q s 2 (fun x => f (x + z)) := by
  rw [normalizedGagliardoESeminormOn_image_add z (openCubeSet Q) s f,
    normalizedGagliardoESeminormOn_openCubeSet]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
