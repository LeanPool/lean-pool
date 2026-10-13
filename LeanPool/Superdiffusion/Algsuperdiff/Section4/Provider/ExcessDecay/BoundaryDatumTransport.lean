/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringVolume
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportNorms

/-!
# BoundaryDatumTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `A4` sample transport of the boundary Caccioppoli datum

This module performs the `A4` move — translation in the *sample* — for all
three ingredients of the datum, so that the whole boundary display can be read
at `originCube d k` and at `Cutoff.translateCutoffSample c ω`:

```text
  equation        -∇·a_L(·,ω)∇u = ∇·g   on c + □_k
                    ↦  -∇·ã_{L,k}(·, τ_c ω)∇u(·+c) = ∇·(-g(·+c))   on □_k
  boundary datum  LocalizedZeroTrace (c+□_k) (patch at x)  ρ
                    ↦  LocalizedZeroTrace □_k (patch at x-c)  ρ(·+c)
  covering        ⨍_{(x+□_{k-2})∩□_m} f  ≤  3^d ⨍_{core □_k (x-c)} f(·+c)
```

Nothing analytic happens here: every step is an exact change of variables.

## The frame, spelled out (disclosed)

The Caccioppoli patch centre moves with the frame: in the translated frame the
anchor's window `(x+□_j)∩□_m` is centred at `x`, in `□_k`'s own frame it is
centred at `x - c`.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; the covering argument.
* CoarseGraining, `Sobolev/H1/Translation.lean`,
  `Sobolev/H1/LocalizedZeroTrace.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The covering cube in `translateSet` spelling -/

/-- **The well-placed covering cube fits inside the domain**, written with
CoarseGraining's `translateSet` — the spelling the translation transport is
stated at. -/
theorem translateSet_wellPlacedCentre_subset {m k : ℤ} (x : Vec d) (hkm : k ≤ m) :
    translateSet (wellPlacedCentre x m k) (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m) := by
  rw [← image_add_eq_translateSet]
  exact image_add_wellPlacedCentre_subset_openCubeSet x hkm

/-- The Dirichlet patch moves with the frame: `x + □_j` seen from `c` is
`(x - c) + □_j`. -/
theorem openCubeAtScale_eq_translateSet (c w : Vec d) (j : ℤ) :
    openCubeAtScale w j = translateSet c (openCubeAtScale (w - c) j) := by
  ext p
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · intro hp i
    have hi := hp i
    have hrw : (p - c) i - (w - c) i = p i - w i := by
      simp only [Pi.sub_apply]
      ring
    rw [hrw]
    exact hi
  · intro hp i
    have hi := hp i
    have hrw : (p - c) i - (w - c) i = p i - w i := by
      simp only [Pi.sub_apply]
      ring
    rw [hrw] at hi
    exact hi

/-! ## 2. The boundary datum transports -/

/-- **The localized zero trace untranslates.**

If `f` has the localized zero trace on `U + c` through the window `V + c`, then
`f(· + c)` has it on `U` through `V`.  The cutoffs correspond bijectively under
`η ↦ η(· - c)`, and CoarseGraining's `H10Function.untranslate` carries the
witness. -/
theorem localizedZeroTraceFunctionOn_untranslate {U V : Set (Vec d)} (c : Vec d)
    {f : Vec d → ℝ}
    (h : LocalizedZeroTraceFunctionOn (translateSet c U) (translateSet c V) f) :
    LocalizedZeroTraceFunctionOn U V (fun y => f (y + c)) := by
  intro eta heta heta_compact heta_sub
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) fun y : Vec d => eta (y - c) :=
    heta.comp (contDiff_id.sub contDiff_const)
  have hcompact : HasCompactSupport fun y : Vec d => eta (y - c) := by
    have h0 : HasCompactSupport (eta ∘ Homeomorph.subRight c) :=
      heta_compact.comp_homeomorph (Homeomorph.subRight c)
    exact h0
  have hsupp : tsupport (fun y : Vec d => eta (y - c)) ⊆ translateSet c V := by
    intro p hp
    have hp' : p - c ∈ tsupport eta := by
      have hcomp : (fun y : Vec d => eta (y - c)) = eta ∘ Homeomorph.subRight c := rfl
      rw [hcomp, tsupport_comp_eq_preimage eta (Homeomorph.subRight c)] at hp
      exact hp
    exact (mem_translateSet_iff_sub_mem).2 (heta_sub hp')
  obtain ⟨w, hw⟩ := h (fun y => eta (y - c)) hsmooth hcompact hsupp
  refine ⟨H10Function.untranslate c w, ?_⟩
  funext p
  rw [H10Function.untranslate_toH1Function, H1Function.untranslate_toFun]
  rw [hw]
  show eta (p + c - c) * f (p + c) = eta p * f (p + c)
  rw [add_sub_cancel_right]

/-- **The anchor's Dirichlet datum, on the covering cube, in its own frame.**

The `H¹₀(□_m)` witness `ρ = u - h` of the frozen theorem's boundary condition
gives the localized zero trace that CoarseGraining's
`BoundaryForcedCaccioppoliDatum` asks for at the outer cube `□_k` and patch
centre `x - c`. -/
theorem localizedZeroTraceFunctionOn_wellPlacedCube_untranslate {m k : ℤ}
    (x : Vec d) (hkm : k ≤ m)
    (rho : H10Function (openCubeSet (originCube d m))) :
    LocalizedZeroTraceFunctionOn (openCubeSet (originCube d k))
      (openCubeAtScale (x - wellPlacedCentre x m k) (k - 1))
      (fun y => rho.toH1Function.toFun (y + wellPlacedCentre x m k)) := by
  refine localizedZeroTraceFunctionOn_untranslate (wellPlacedCentre x m k) ?_
  rw [← image_add_eq_translateSet,
    ← openCubeAtScale_eq_translateSet (wellPlacedCentre x m k) x (k - 1)]
  exact localizedZeroTraceFunctionOn_wellPlacedCube x hkm rho

/-! ## 3. The equation transports -/

/-! ## 4. The covering inequality, in the covering cube's own frame -/

/-- **The covering step, transported.**

The normalized average of a nonnegative integrand over the frozen theorem's own
window `(x+□_{k-2}) ∩ □_m` is at most `3^d` times its normalized average over
CoarseGraining's Caccioppoli core `caccioppoliCoreSet (□_k) (x - c)` **in the
covering cube's own frame**, the integrand being read at the translated point. -/
theorem normalizedSetAverage_truncatedWindow_le_three_pow_mul_untranslatedCore
    {m k : ℤ} {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m)
    {f : Vec d → ℝ}
    (hf : ∀ y ∈ (fun y => wellPlacedCentre x m k + y) ''
      caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k), 0 ≤ f y)
    (hint : IntegrableOn f ((fun y => wellPlacedCentre x m k + y) ''
      caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k)) volume) :
    normalizedSetAverage (truncatedWindow x m (k - 2)) f ≤
      (3 : ℝ) ^ d *
        normalizedSetAverage
          (caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k))
          (fun y => f (y + wellPlacedCentre x m k)) := by
  have hbase :=
    normalizedSetAverage_truncatedWindow_le_three_pow_mul_wellPlacedCore hx hkm hf hint
  have hframe : normalizedSetAverage ((fun y => wellPlacedCentre x m k + y) ''
        caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k)) f =
      normalizedSetAverage
        (caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k))
        (fun y => f (y + wellPlacedCentre x m k)) := by
    rw [image_add_eq_translateSet,
      normalizedSetAverage_translateSet (wellPlacedCentre x m k)
        (caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k)) f]
  rwa [hframe] at hbase

/-! ## 5. The energy density is frame-inert -/

/-- The normalized average is homogeneous in a scalar factor. -/
theorem normalizedSetAverage_const_mul (V : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    normalizedSetAverage V (fun y => c * f y) = c * normalizedSetAverage V f := by
  rw [normalizedSetAverage, normalizedSetAverage, volumeAverage, volumeAverage,
    integral_const_mul]
  ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
