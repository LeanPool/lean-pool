/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepCornerSeam
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryComposeGlue

/-!
# OneStepBoundaryCompose

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary one-step excess-decay contraction at every met configuration

The composed endpoint of the boundary branch: the one-step contraction of
`l.excess.decay.good.scales`, conditional only on the harmonic-approximation
anchor, at **every** met configuration — one met face upper or lower, and every
edge/corner orientation.

```text
  E(u, U_k) ≤ C_t · C · κ · (3^{-k})^{1/2} · E(u, U_0)
              + C_r(d, C, k) · 3^{-n} · √((3²)^d) · ‖RHS‖
```

the same display as `OneStepConditional.excessDecay_oneStep_of_harmonicApprox`
with `K_h = 0`, i.e. with the Schauder slot discharged and **no**
boundary-datum leg.

## What is discharged here, relative to the proved one-face endpoint

* the odd-class defect is folded at every orientation
  (`OneStepCornerSeam.exists_gradientHolder_boundary_metSet`, which composes the
  transported `(★)`/`(★★)` of `OneStepCornerTransport*`);
* the oddness binder is the **window-pointwise** one, which is what the chain's
  Weyl representative satisfies — `faceOdd_eqOn_reflectedWindow_of_ae` below is
  the bridge from the a.e. oddness of 's reflection chain;
* the affine-minimizer datum `hmin` is **discharged**, not assumed
  (`OneStepBoundaryComposeGlue.exists_isAffineMinimizer_shifted_truncatedWindow`
  from the proved sandwich attainment), so the statement carries no affine
  parameters at all.

## What is left between this and `l.excess.decay.good.scales`

1. the **interior branch** (no met face), which is
   `OneStepSchauderComposeInterior`/`OneStepConditional`'s own gate;

No analytic input beyond the chain's own binders remains on the boundary
branch's Schauder side.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The bridge from the reflection chain's a.e. oddness.**  A classically
harmonic representative almost everywhere equal on the doubled window to a
globally met-face-odd datum — which is exactly what 's chain produces — is
pointwise odd about every met face at every point of the doubled window, the
binder shape `exists_gradientHolder_boundary_metSet` consumes. -/
theorem faceOdd_eqOn_reflectedWindow_of_ae {x : Vec d} {m k : ℤ} (hkm : k < m)
    {V O : Vec d → ℝ}
    (hharm : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m k))
    (hae : V =ᵐ[volume.restrict (reflectedWindow x m k)] O)
    (hupO : ∀ i : Fin d, MeetsUpperFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z)
    (hlowO : ∀ i : Fin d, MeetsLowerFace x m k i → ∀ z : Vec d,
      O (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -O z) :
    (∀ i : Fin d, MeetsUpperFace x m k i → ∀ y ∈ reflectedWindow x m k,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -V y) ∧
      (∀ i : Fin d, MeetsLowerFace x m k i → ∀ y ∈ reflectedWindow x m k,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -V y) := by
  have hcont : ContinuousOn V (reflectedWindow x m k) :=
    continuousOn_of_harmonicOnNhd hharm
  exact ⟨fun i hi => eqOn_faceOdd_upper_of_ae_eq hkm hi hcont hae (hupO i hi),
    fun i hi => eqOn_faceOdd_lower_of_ae_eq hkm hi hcont hae (hlowO i hi)⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

end

end Algsuperdiff.Section4.Provider.ExcessDecay
