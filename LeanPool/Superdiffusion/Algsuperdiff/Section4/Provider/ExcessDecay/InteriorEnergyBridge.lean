/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorRebase
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.NuIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportNorms

/-!
# InteriorEnergyBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The energy leg of the interior clause: child frame versus parent frame

The coarse-graining energy term of the child-frame composition carries
CoarseGraining's coefficient-energy norm at the **child's own frame**,

```text
  ‖∇u_tilde_x‖_{ã, L²(□_n)}  =  h1EnergyNormOnCube □_n ã u_tilde_x ,   u_tilde_x = u(· + x) ,
```

```text
  localizedCoeffEnergyValue ((x−z) + □_n) ã_{L,n+2} u_tilde_z ,       u_tilde_z = u(· + z) .
```

The two agree **exactly**.  Two facts, both identities:

* the flux increment is antisymmetric, so the quadratic form of the shifted
  coefficient is the quadratic form of `a_L`, i.e. exactly `ν |ξ|²`
  (`AntisymmetricShiftCutoff.vecDot_matVecMul_fluxCorrectedField_self`,
  `NuIdentification`); the *same* is true of the re-based family, whose
  subtracted constant is the parent's increment.  So both sides are `ν ⨍ |∇u|²`
  on their own window;
* only the volume average has to move, and Lebesgue measure is translation
  invariant (`TranslationTransportNorms`), so `⨍_{(x−z)+□_n} |∇u(·+z)|²` is
  `⨍_{□_n} |∇u(·+x)|²`.

No constant, no hypothesis, no good event.

## References

* ABK26, (the `ν|∇u|²` energy reading).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. The `ν`-identification at the re-based family -/

/-- The symmetric part of the re-based child-frame coefficient is exactly
`ν Id`: the subtracted constant is the parent's antisymmetric increment. -/
theorem symmPart_parentRebasedFamily (M : ABKModel d) (L k : ℤ) (x z : Vec d)
    (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) (y : Vec d) :
    symmPart (((parentRebasedFamily M L k x z omega).coeffOn Q).toCoeffField y) =
      (M.nu : ℝ) • (1 : Mat d) := by
  rw [parentRebasedFamily_coeffOn]
  exact Annular.symmPart_subConstCutoffField M L (parentFluxIncrement M L k z omega)
    (matTranspose_parentFluxIncrement M L k z omega)
    (Cutoff.translateCutoffSample x omega) y

/-- **The `ν`-identification at the re-based family.**  On any window, the
localized coefficient energy is exactly `ν` times the normalized gradient `L²`
square. -/
theorem localizedCoeffEnergyValue_parentRebasedFamily_eq (M : ABKModel d) (L k : ℤ)
    (x z : Vec d) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    (V : Set (Vec d)) (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    localizedCoeffEnergyValue V ((parentRebasedFamily M L k x z omega).coeffOn Q) u =
      (M.nu : ℝ) * normalizedSetAverage V (fun y => vecNormSq (u.grad y)) :=
  localizedCoeffEnergyValue_eq_mul_of_symmPart_eq V _ u M.nu
    (symmPart_parentRebasedFamily M L k x z omega Q)

/-- The coefficient-energy norm of the re-based family on the child cube. -/
theorem h1EnergyNormOnCube_parentRebasedFamily_eq (M : ABKModel d) (L k n : ℤ)
    (x z : Vec d) (omega : Cutoff.CutoffSample d)
    (u : H1Function (Ch02.cubeDomain (originCube d n) : Set (Vec d))) :
    h1EnergyNormOnCube (originCube d n) (parentRebasedFamily M L k x z omega) u =
      Real.sqrt ((M.nu : ℝ) *
        normalizedSetAverage (openCubeSet (originCube d n))
          (fun y => vecNormSq (u.grad y))) := by
  rw [h1EnergyNormOnCube,
    localizedCoeffEnergyValue_parentRebasedFamily_eq M L k x z omega (originCube d n)]

/-! ## 2. The volume average moves -/

/-- **The gradient energy average transports between the two frames.**

The normalized average of `|∇u(· + z)|²` over `(x−z) + □_n` is the normalized
average of `|∇u(· + x)|²` over `□_n`.  Exact. -/
theorem normalizedSetAverage_vecNormSq_grad_frame (n : ℤ) (x z : Vec d)
    (G : Vec d → Vec d) :
    normalizedSetAverage ((fun y => (x - z) + y) '' openCubeSet (originCube d n))
        (fun y => vecNormSq (G (y + z))) =
      normalizedSetAverage (openCubeSet (originCube d n))
        (fun y => vecNormSq (G (y + x))) := by
  rw [image_add_eq_translateSet (x - z) (openCubeSet (originCube d n)),
    normalizedSetAverage_vecNormSq_translateSet (x - z) (openCubeSet (originCube d n))
      (fun p => G (p + z))]
  refine congrArg (normalizedSetAverage (openCubeSet (originCube d n))) ?_
  funext y
  have hpt : y + (x - z) + z = y + x := by
    rw [add_assoc, sub_add_cancel]
  rw [hpt]

/-! ## 3. The energy leg -/

/-- **The energy leg of the interior clause.**

```text
  ‖∇u_tilde_x‖_{ã, L²(□_n)}  =  ( ⨍_{(x−z)+□_n} ∇u_tilde_z · ã_{L,n+2} ∇u_tilde_z )^{1/2} .
```
-/
theorem h1EnergyNormOnCube_parentRebasedFamily_eq_sqrt_localizedCoeffEnergyValue
    {n m k : ℤ} (M : ABKModel d) (L : ℤ) (x z : Vec d)
    (omega : Cutoff.CutoffSample d) (u : H1Function (openCubeSet (originCube d m)))
    (hx : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (hz : translateSet z (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m)) :
    h1EnergyNormOnCube (originCube d n) (parentRebasedFamily M L k x z omega)
        (H1Function.untranslate x
          (u.restrict (isOpen_translateSet_openCubeSet x n) hx)) =
      Real.sqrt (localizedCoeffEnergyValue
        ((fun y => (x - z) + y) '' openCubeSet (originCube d n))
        ((Support.fluxCorrectedCoeffFamily M L k (originCube d k)
          (Cutoff.translateCutoffSample z omega)).coeffOn (originCube d k))
        (H1Function.untranslate z
          (u.restrict (isOpen_translateSet_openCubeSet z k) hz))) := by
  rw [h1EnergyNormOnCube_parentRebasedFamily_eq M L k n x z omega,
    localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq M L k (originCube d k)
      (originCube d k) (Cutoff.translateCutoffSample z omega)]
  refine congrArg Real.sqrt (congrArg (fun t => (M.nu : ℝ) * t) ?_)
  exact (normalizedSetAverage_vecNormSq_grad_frame n x z u.grad).symm

end

end Algsuperdiff.Section4.Provider.ExcessDecay
