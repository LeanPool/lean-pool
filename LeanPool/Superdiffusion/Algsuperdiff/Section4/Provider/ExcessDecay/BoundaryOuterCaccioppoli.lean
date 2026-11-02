/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryAssemblyEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryDatumTransport

/-!
# BoundaryOuterCaccioppoli

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary Caccioppoli display at the *localized* boundary datum

This module re-proves the same display at the hypothesis the covering route can
actually discharge — CoarseGraining's own `LocalizedZeroTraceFunctionOn`
through the Dirichlet patch, which is *precisely* the field
`BoundaryForcedCaccioppoliDatum.zeroTraceOnBoundaryPatch` and no more.

The discharge itself is the point:

```text
  u - v  =  (u - h)  -  (v - h)
             ↑ H¹₀(□_m), localized on c+□_k through the patch
                          ↑ H¹₀(c+□_k), localized through anything
```

so `localizedZeroTraceFunctionOn_sub` closes it, and `BoundaryDatumTransport`
moves the whole thing into `□_k`'s own frame.

## Main results

* `boundaryForcedCaccioppoliDatumOfLocalizedDifference` — CoarseGraining's
  datum populated by a difference with only a localized zero trace.
* `exists_boundaryCaccioppoliEnergy_ofLocalizedDifference` — the printed
  `e.cgC.boundary.applied` at that hypothesis.
* `exists_boundaryCaccioppoliEnergy_withLocalizedBoundaryDatum` — with both
  legs (the `[g]_{B^r}` force leg and the `‖∇h‖_{B^r}` boundary leg), at the
  localized hypothesis.
* `localizedZeroTraceFunctionOn_wellPlacedDifference` — the discharge, in the
  covering cube's own frame.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`.
* CoarseGraining, `Book/Ch03/Theorems/CoarseCaccioppoli/Theory.lean`,
  `Book/Ch03/Theorems/Energy/Theory.lean`,
  `Sobolev/H1/LocalizedZeroTrace.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The datum at the localized hypothesis -/

/-- **CoarseGraining's boundary Caccioppoli datum, populated by a difference with
only a localized zero trace.**

On the covering cube only the localized statement is available, and only the
localized statement is needed: it *is* the field. -/
def boundaryForcedCaccioppoliDatumOfLocalizedDifference {Q : TriadicCube d}
    {a : CoeffFamily d} (x : Vec d) {g : Vec d → Vec d}
    {u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    (hu : IsForcedEquation Q a u g) (hv : IsForcedEquation Q a v g)
    (hdiff : Ch01.LocalizedZeroTraceFunctionOn (Ch02.cubeDomain Q : Set (Vec d))
      (openCubeAtScale x (Q.scale - 1)) (fun y => u.toFun y - v.toFun y)) :
    BoundaryForcedCaccioppoliDatum Q a x (fun _ => 0) where
  toH1 := u - v
  weakSolution := isForcedEquation_sub hu hv
  zeroTraceOnBoundaryPatch := by
    have hfun : (u - v).toFun = fun y => u.toFun y - v.toFun y :=
      H1Function.sub_toFun u v
    rw [hfun]
    exact hdiff

/-! ## 2. The printed boundary display at the localized hypothesis -/

/-- **`e.cgC.boundary.applied` at the localized boundary datum.** -/
theorem exists_boundaryCaccioppoliEnergy_ofLocalizedDifference (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} {x : Vec d}
        {g : Vec d → Vec d}
        (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))),
        IsForcedEquation Q a u g → IsForcedEquation Q a v g →
        Ch01.LocalizedZeroTraceFunctionOn (Ch02.cubeDomain Q : Set (Vec d))
          (openCubeAtScale x (Q.scale - 1)) (fun y => u.toFun y - v.toFun y) →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        x ∈ openCubeSet Q →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) (u - v) ≤
            caccioppoliWithRHSPrefactor C Q a s t *
              (Ch02.lambdaS Q t a *
                Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y => u.toFun y - v.toFun y)) := by
  obtain ⟨C, hCpos, hC⟩ := (coarseCaccioppoliRHSTheory (d := d)).exists_constant
  refine ⟨C, hCpos, ?_⟩
  intro Q a s t x g u v hu hv hdiff hs hs1 ht ht2 hst hx
  have hbound := hC (boundaryForcedCaccioppoliDatumOfLocalizedDifference x hu hv hdiff)
    hs hs1 ht ht2 hst hx (forceBesovRegularity_zero Q (2 * t))
  rw [boundaryForcedCaccioppoliCoreEnergy] at hbound
  rw [boundaryCaccioppoliWithRHSRHS, boundaryForcedCaccioppoliParentL2Sq] at hbound
  have hgradeq :
      (boundaryForcedCaccioppoliDatumOfLocalizedDifference x hu hv hdiff).toH1.grad =
        (u - v).grad := rfl
  have hfuneq :
      (boundaryForcedCaccioppoliDatumOfLocalizedDifference x hu hv hdiff).toH1.toFun =
        fun y => u.toFun y - v.toFun y := H1Function.sub_toFun u v
  rw [hfuneq] at hbound
  refine le_trans (le_of_eq ?_) (le_trans hbound (le_of_eq ?_))
  · rw [localizedCoeffEnergyValue, localizedCoeffEnergyValue, hgradeq]
  · rw [scaleNormalizedPositiveBesovVectorSeminormTwo]
    have hzero : cubeBesovPositiveVectorSeminormTwo Q (2 * t)
        (fun _ : Vec d => (0 : Vec d)) = 0 := by
      have h := cubeBesovPositiveVectorSeminormTwo_zero Q (2 * t)
      exact h
    rw [hzero]
    ring

/-- ** at the localized boundary datum: the boundary-regime coarse Caccioppoli
estimate with both `∇h` legs.** -/
theorem exists_boundaryCaccioppoliEnergy_withLocalizedBoundaryDatum
    (d : ℕ) [NeZero d] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t r : ℝ} {x : Vec d}
        {g : Vec d → Vec d} (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
        (v : DirichletForcedCubeSolution Q a g),
        IsForcedEquation Q a u g →
        Ch01.LocalizedZeroTraceFunctionOn (Ch02.cubeDomain Q : Set (Vec d))
          (openCubeAtScale x (Q.scale - 1))
          (fun y => u.toFun y - v.toH1.toFun y) →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        0 < r → r < 1 → ForceBesovRegularity Q r g →
        ForceBesovRegularity Q r (dirichletBoundaryGradientField v) →
        x ∈ openCubeSet Q →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            2 * (caccioppoliWithRHSPrefactor C₁ Q a s t *
                (Ch02.lambdaS Q t a *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q)
                    (fun y => u.toFun y - v.toH1.toFun y))) +
              2 * ((18 : ℝ) ^ d * dirichletEnergyWithRHSRHS C₂ Q a r g v ^ 2) := by
  obtain ⟨C₁, hC₁pos, hcacc⟩ := exists_boundaryCaccioppoliEnergy_ofLocalizedDifference d
  obtain ⟨C₂, hC₂pos, henergy⟩ :=
    exists_localizedCoeffEnergyValue_openCubeSet_le_dirichletEnergyWithRHSRHS_sq d
  refine ⟨C₁, C₂, hC₁pos, hC₂pos, ?_⟩
  intro Q a s t r x g u v hu hdiff hs hs1 ht ht2 hst hr hr1 hg hh hx
  have hdiffbound := hcacc u v.toH1 hu v.weakSolution hdiff hs hs1 ht ht2 hst hx
  have hvcore :=
    localizedCoeffEnergyValue_core_le_eighteen_pow_mul_parent (a := a) hx v.toH1
  have hvparent := henergy v hr hr1 hg hh
  have hgeom : (0 : ℝ) ≤ (18 : ℝ) ^ d := by positivity
  have hvbound : localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) v.toH1 ≤
      (18 : ℝ) ^ d * dirichletEnergyWithRHSRHS C₂ Q a r g v ^ 2 :=
    hvcore.trans (mul_le_mul_of_nonneg_left hvparent hgeom)
  have hmink := localizedCoeffEnergyValue_core_le_two_mul_sub_add (x := x) (a := a) u v.toH1
  linarith only [hmink, hdiffbound, hvbound]

/-! ## 3. The discharge, in the covering cube's own frame -/

omit [NeZero d] in
/-- **The localized zero trace of `u - v` on the well-placed covering cube.**

The anchor's own `H¹₀(□_m)` witness `ρ` (its boundary condition `u = h`) and
the comparison solution's own `H¹₀(□_k)` witness `σ` (`v = h` on `∂□_k`)
combine: `u - v = ρ(·+c) - σ` in the covering cube's frame, and the localized
zero trace is closed under subtraction. -/
theorem localizedZeroTraceFunctionOn_wellPlacedDifference {m k : ℤ} (x : Vec d)
    (hkm : k ≤ m) (rho : H10Function (openCubeSet (originCube d m)))
    (sigma : H10Function (openCubeSet (originCube d k))) {U V : Vec d → ℝ}
    (hUV : ∀ y, U y - V y =
      rho.toH1Function.toFun (y + wellPlacedCentre x m k) -
        sigma.toH1Function.toFun y) :
    Ch01.LocalizedZeroTraceFunctionOn (openCubeSet (originCube d k))
      (openCubeAtScale (x - wellPlacedCentre x m k) (k - 1))
      (fun y => U y - V y) := by
  have hrho := localizedZeroTraceFunctionOn_wellPlacedCube_untranslate x hkm rho
  have hsigma : Ch01.LocalizedZeroTraceFunctionOn (openCubeSet (originCube d k))
      (openCubeAtScale (x - wellPlacedCentre x m k) (k - 1))
      sigma.toH1Function.toFun :=
    localizedZeroTraceFunctionOn_of_h10_any sigma
  have hsub := localizedZeroTraceFunctionOn_sub hrho hsigma
  have hfun : (fun y => U y - V y) =
      fun y => rho.toH1Function.toFun (y + wellPlacedCentre x m k) -
        sigma.toH1Function.toFun y := by
    funext y
    exact hUV y
  rw [hfun]
  exact hsub

end

end Algsuperdiff.Section4.Provider.ExcessDecay
