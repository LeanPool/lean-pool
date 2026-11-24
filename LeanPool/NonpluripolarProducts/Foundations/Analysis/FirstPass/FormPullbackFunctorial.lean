/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ClosedFormPullback

/-!
# Functoriality of the pullback of smooth real forms

Source: standard (`f^* ` is a functor on differential forms); needed for the
modification statements of Copy-4, `sec:prelim` and blueprint
`ana:locus-properties`, whose hypothesis is an `IsBlowupSequence`, i.e. a finite
COMPOSITION of blowups.

`SmoothRealForm.pullback` selects, at each source-chart point, the preferred
target chart at the image point.  Therefore neither functoriality law holds on
the nose: the two sides pick different intermediate charts off the overlap.  Both
hold *geometrically*, i.e. after restricting the coefficients to the chart
targets, which is exactly the equivalence `SmoothRealForm.GeometricallyEq` that
`GeometricRealForm` and `RealBottChern` quotient by.

* `pullback_id_geometricallyEq`: `id^* a = a`.  This is literally the tensor
  transformation law `SmoothRealForm.compatible` for the transition from the
  ambient chart to the preferred chart at the point.
* `pullback_comp_geometricallyEq`: `(f ∘ g)^* a = g^* (f^* a)`.  The chain rule
  for the coordinate representatives, plus the fact that the intermediate chart
  chosen by `g^*` is the preferred chart at `g x`, which is exactly where
  `f^* a` reads its own coefficients.
* `ofRepresentative_pullback_id`, `ofRepresentative_pullback_comp`: the same two
  laws at the level of real Bott--Chern classes, where they are genuine
  equalities.

The consumers are the modification statements of `Pending.LocusProperties`,
each of which is an induction over `IsBlowupSequence`: the reflexive case needs
the first law and the step case the second.
-/

@[expose] public section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

open HolomorphicMaps

noncomputable section

variable {p n : ℕ}
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z]

namespace SmoothRealForm

/-- **`id^* a = a`** geometrically. -/
theorem pullback_id_geometricallyEq (a : SmoothRealForm n X p) :
    (pullback (f := (id : X → X))
      (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)) a).GeometricallyEq a := by
  intro e z hz
  set d := complexChartAt (n := n) (e.val.symm z) with hd
  have hsrc : e.val.symm z ∈ d.val.source := mem_complexChartAt_source _
  have hzs : z ∈ (chartTransition e d).source := ⟨hz, hsrc⟩
  ext v
  rw [a.compatible e d z hzs v]
  rfl

/-- **`(f ∘ g)^* a = g^* (f^* a)`** geometrically. -/
theorem pullback_comp_geometricallyEq {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (a : SmoothRealForm n X p) :
    (pullback (hf.comp hg) a).GeometricallyEq (pullback hg (pullback hf a)) := by
  intro e z hz
  set x : Z := e.val.symm z with hx
  set d₂ := complexChartAt (n := n) (g x) with hd₂
  set d₁ := complexChartAt (n := n) (f (g x)) with hd₁
  have hgx : g x ∈ d₂.val.source := mem_complexChartAt_source _
  have hfgx : f (g x) ∈ d₁.val.source := mem_complexChartAt_source _
  -- the intermediate point in `d₂`-coordinates
  set w : ComplexModel n := coordinateMap g e d₂ z with hw
  have hwx : d₂.val.symm w = g x := by
    rw [hw]
    exact d₂.val.left_inv hgx
  have hzdom : z ∈ coordinateDomain g e d₂ := ⟨hz, by
    simpa only [mem_preimage, ← hx] using hgx⟩
  have hwdom : w ∈ coordinateDomain f d₂ d₁ :=
    ⟨d₂.val.map_source hgx, by simpa only [mem_preimage, hwx] using hfgx⟩
  have hzdom₁ : z ∈ coordinateDomain (f ∘ g) e d₁ := ⟨hz, by
    simpa only [mem_preimage, ← hx, Function.comp_apply] using hfgx⟩
  -- the chain rule for the coordinate representatives
  have heq : coordinateMap (f ∘ g) e d₁ =ᶠ[𝓝 z]
      (coordinateMap f d₂ d₁) ∘ (coordinateMap g e d₂) := by
    filter_upwards [(coordinateDomain_isOpen hg e d₂).mem_nhds hzdom] with y hy
    change d₁.val (f (g (e.val.symm y))) =
      d₁.val (f (d₂.val.symm (d₂.val (g (e.val.symm y)))))
    rw [d₂.val.left_inv hy.2]
  have hchain : fderiv ℝ (coordinateMap (f ∘ g) e d₁) z =
      (fderiv ℝ (coordinateMap f d₂ d₁) w).comp
        (fderiv ℝ (coordinateMap g e d₂) z) := by
    rw [heq.fderiv_eq]
    exact fderiv_comp z
      ((coordinateMap_contDiffAt_real hf d₂ d₁ hwdom).differentiableAt (by simp))
      ((coordinateMap_contDiffAt_real hg e d₂ hzdom).differentiableAt (by simp))
  have hpoint : coordinateMap f d₂ d₁ w = coordinateMap (f ∘ g) e d₁ z := by
    change d₁.val (f (d₂.val.symm w)) = d₁.val (f (g (e.val.symm z)))
    rw [hwx]
  ext v
  change (a.coeff d₁ (coordinateMap (f ∘ g) e d₁ z))
      (fun i => fderiv ℝ (coordinateMap (f ∘ g) e d₁) z (v i)) = _
  rw [hchain]
  change _ = ((pullback hf a).coeff d₂ w)
      (fun i => fderiv ℝ (coordinateMap g e d₂) z (v i))
  have hinner : (pullback hf a).coeff d₂ w =
      (a.coeff d₁ (coordinateMap f d₂ d₁ w)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap f d₂ d₁) w) := by
    change chartPullbackCoeff a f d₂ (complexChartAt (n := n) (f (d₂.val.symm w))) w = _
    rw [hwx, ← hd₁]
    rfl
  rw [hinner, hpoint]
  rfl

end SmoothRealForm

namespace ClosedRealOneOneForm

/-- `id^* θ = θ` as real Bott--Chern classes. -/
theorem ofRepresentative_pullback_id (θ : ClosedRealOneOneForm n X) :
    RealBottChern.ofRepresentative (pullback (f := (id : X → X))
        (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)) θ) =
      RealBottChern.ofRepresentative θ :=
  RealBottChern.ofRepresentative_eq_of_geometricallyEq
    (SmoothRealForm.pullback_id_geometricallyEq θ.val)

/-- `(f ∘ g)^* θ = g^* (f^* θ)` as real Bott--Chern classes. -/
theorem ofRepresentative_pullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (θ : ClosedRealOneOneForm n X) :
    RealBottChern.ofRepresentative (pullback (hf.comp hg) θ) =
      RealBottChern.ofRepresentative (pullback hg (pullback hf θ)) :=
  RealBottChern.ofRepresentative_eq_of_geometricallyEq
    (SmoothRealForm.pullback_comp_geometricallyEq hf hg θ.val)

end ClosedRealOneOneForm

end

end SGPT.Foundations.Analysis.FirstPass
