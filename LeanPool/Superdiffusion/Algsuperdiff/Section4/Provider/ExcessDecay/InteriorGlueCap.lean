/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlue
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridErrorFluxCorrected
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Translate

/-!
# InteriorGlueCap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The cap at the root: the off-grid child error against the anchor's own
# `fluxCorrectedErrorRepresentative`

This module closes the two remaining steps:

* the sample translation, which is legitimate because every real translation
  preserves the cutoff-sample law
  (`GoodEvents.measurePreserving_translateCutoffSample`).

The result is stated on **one** probability-one event, for **every** real
translate `w` at once, exactly as the assembly consumes it; the anchor's own
geometry binder supplies `w := x − z` through
`InteriorGlue.translateSet_cubeSet_subset_of_anchorGeometry`.

## What this does *not* do

The left-hand side is the off-grid error of the child cube, in the parent's
`z`-frame.  Nothing here assumes it.

## References

* ABK26, `e.mathcalE.stability.applied`;
  `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The root specialization -/

omit [NeZero d] in
/-- The scale gap of the anchor's parent/child pair, as a natural number. -/
private theorem originCube_scale_gap (n : ℤ) :
    ((originCube d (n + 2)).scale - (originCube d n).scale).toNat = 2 := by
  have h : (originCube d (n + 2)).scale - (originCube d n).scale = 2 := by
    simp only [originCube]
    ring
  rw [h]
  rfl

omit [NeZero d] in
/-- At the anchor's own root the `F1'` functional **is** the proved representative:
`fluxCorrectedErrorFunctionalAtRoot` at `root = Q = □_{n+2}` with the
comparator `σ_{n+2} Id` reduces to `Support.fluxCorrectedErrorRepresentative`,
definitionally. -/
theorem fluxCorrectedErrorFunctionalAtRoot_eq_representative (M : ABKModel d)
    (L k : ℤ) (u : {u : ℝ // 0 < u}) :
    fluxCorrectedErrorFunctionalAtRoot M L k (originCube d k) (originCube d k)
        (u : ℝ) (isotropicComparatorMatrix (Annealed.sigmaBar M k)) =
      fluxCorrectedErrorRepresentative M L k u :=
  rfl

/-! ## 2. The cap at the root, at the untranslated sample -/

/-- **The off-grid child error against the anchor's representative.**

On one probability-one event, for every real translate `w` with
`w + □_n ⊆ □_{n+2}` (half-open),

```text
  𝓔_{t,∞,2}(w + □_n; ã_{L,n+2}, σ_{n+2}) ≤ C(d,t,u)^{1/2} · 3^{2u} ·
      𝓔_{u,∞,2}(□_{n+2}; ã_{L,n+2}, σ_{n+2}) ,
```

the right-hand factor being the frozen theorem's own
`fluxCorrectedErrorRepresentative M L (n+2) ⟨u⟩`. -/
theorem ae_offGridChildError_le_fluxCorrectedErrorRepresentative (M : ABKModel d)
    (L n : ℤ) {t u : ℝ} (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ w : Vec d,
        translateSet w (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + 2)) →
        offGridErrorFunctional w (originCube d n) t
            (fluxCorrectedRegField M L (n + 2) (originCube d (n + 2)) omega).toFun
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) ≤
          Real.sqrt (offGridStabilityConst d t u) *
            ((3 : ℝ) ^ (2 * u) *
              fluxCorrectedErrorRepresentative M L (n + 2) ⟨u, hu0⟩ omega) := by
  filter_upwards [ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot
    M L (n + 2) (originCube d (n + 2))
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) hu0 hut ht] with omega hall
  intro w hcontain
  have hbase := hall w (originCube d n) (originCube d (n + 2)) hcontain
  rw [originCube_scale_gap (d := d) n] at hbase
  rw [fluxCorrectedErrorFunctionalAtRoot_eq_representative M L (n + 2) ⟨u, hu0⟩] at hbase
  have hexp : (u * ((2 : ℕ) : ℝ)) = 2 * u := by
    push_cast
    ring
  rwa [hexp] at hbase

/-! ## 3. The cap at the translated sample -/

/-- **The same estimate at the anchor's translated sample.**

The anchor reads its error at `translateCutoffSample z ω`; every real
translation preserves the cutoff-sample law, so the probability-one event
transports. -/
theorem ae_offGridChildError_le_representative_translate (M : ABKModel d)
    (L n : ℤ) (z : Vec d) {t u : ℝ} (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ w : Vec d,
        translateSet w (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + 2)) →
        offGridErrorFunctional w (originCube d n) t
            (fluxCorrectedRegField M L (n + 2) (originCube d (n + 2))
              (Cutoff.translateCutoffSample z omega)).toFun
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) ≤
          Real.sqrt (offGridStabilityConst d t u) *
            ((3 : ℝ) ^ (2 * u) *
              fluxCorrectedErrorRepresentative M L (n + 2) ⟨u, hu0⟩
                (Cutoff.translateCutoffSample z omega)) :=
  (GoodEvents.measurePreserving_translateCutoffSample M z).quasiMeasurePreserving.ae
    (ae_offGridChildError_le_fluxCorrectedErrorRepresentative M L n hu0 hut ht)

/-! ## 4. The anchor's own slot, entered at the geometry binder -/

/-- **The glue item, at the anchor's binders.**

At the printed slot `(t, u) = (s/6, s/8)` and the anchor's geometry binder, the
off-grid error of the anchor's own child window `x + □_n`, read in the parent's
`z`-frame at the translate `w = x − z`, is bounded by the anchor's own
`fluxCorrectedErrorRepresentative M L (n+2) ⟨s/8⟩` at the translated sample,
with the absolute depth factor `3^{s/4}` (at most `3^{1/4} < 1.32`). -/
theorem ae_offGridChildError_le_representative_harmonicSlot (M : ABKModel d)
    (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        offGridErrorFunctional (x - z) (originCube d n) (s / 6)
            (fluxCorrectedRegField M L (n + 2) (originCube d (n + 2))
              (Cutoff.translateCutoffSample z omega)).toFun
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (2 * (s / 8)) *
              fluxCorrectedErrorRepresentative M L (n + 2)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  filter_upwards [ae_offGridChildError_le_representative_translate M L n z
    (by linarith only [hs] : (0 : ℝ) < s / 8)
    (by linarith only [hs] : s / 8 < s / 6)
    (by linarith only [hs1] : s / 6 ≤ 1 / 2)] with omega hall
  intro x m hgeom
  exact hall (x - z) (translateSet_cubeSet_subset_of_anchorGeometry hgeom)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
