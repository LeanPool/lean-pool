/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SubConstFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorAssemblyLhs
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlueFrame
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlueWindow

/-!
# InteriorRebase

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The child frame, re-based on the **parent's** antisymmetric flux increment

The child-frame composition takes the coarse-graining estimate at the child's
*own* flux-corrected family `ã_{L,n}` — the cutoff coefficient at the
translated sample `translateCutoffSample x ω` minus the child's own increment
`(κ_L − κ_n)_{□_n}`.

This module supplies the re-basing.  The two families differ by a **constant
antisymmetric matrix**, so the equation does not see the difference:

```text
  ã_{L,n}(·, ω_x)  −  ã_{L,n+2}(· + (x−z), ω_z)  =  (κ_L−κ_{n+2})_{□_{n+2}}(ω_z)
                                                  − (κ_L−κ_n)_{□_n}(ω_x) ,
```

both increments skew.  Rather than compare the two, the family below is built
*directly* at the parent's constant, from the proved free-constant carrier
`Provider.Annular.subConstCutoffTriadicCoeffFamily` — so its representative is
literally

```text
  a_L(·, translateCutoffSample x ω) − (κ_L−κ_{n+2})_{□_{n+2}}(translateCutoffSample z ω)
      =  ã_{L,n+2}(· + (x−z), translateCutoffSample z ω) ,
```

which is exactly the hypothesis `InteriorGlueFrame` consumes: the family's
representative is `translateCoeffField (x−z)` of the parent's carrier field, on
**every** cube.  Both facts below are identities; no estimate is made.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the "differ by a constant
  anti-symmetric matrix" observation).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. The parent's constant -/

/-- The parent cube's averaged flux increment `(κ_L − κ_{n+2})_{□_{n+2}}`, read
at the anchor's own translated sample `translateCutoffSample z ω`. -/
def parentFluxIncrement (M : ABKModel d) (L k : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : Mat d :=
  Support.fluxIncrementAverage M L k (originCube d k) (Cutoff.translateCutoffSample z omega)

/-- The parent's increment is antisymmetric (`a.shell.antisymmetry`). -/
theorem matTranspose_parentFluxIncrement (M : ABKModel d) (L k : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) :
    matTranspose (parentFluxIncrement M L k z omega) = -parentFluxIncrement M L k z omega :=
  matTranspose_fluxIncrementAverage M L k (originCube d k)
    (Cutoff.translateCutoffSample z omega)

/-! ## 2. The re-based child-frame family -/

/-- **The child-frame coefficient family at the parent's flux correction.**

The cutoff coefficient at the child's translated sample, minus the *parent's*
antisymmetric increment.  Built from the proved free-constant carrier, so it is
a genuine `Ch03.CoeffFamily` with the same representative on every cube. -/
def parentRebasedFamily (M : ABKModel d) (L k : ℤ) (x z : Vec d)
    (omega : Cutoff.CutoffSample d) : Ch03.CoeffFamily d :=
  Annular.subConstCutoffTriadicCoeffFamily M L (parentFluxIncrement M L k z omega)
    (matTranspose_parentFluxIncrement M L k z omega)
    (Cutoff.translateCutoffSample x omega)

@[simp]
theorem parentRebasedFamily_coeffOn (M : ABKModel d) (L k : ℤ) (x z : Vec d)
    (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) :
    ((parentRebasedFamily M L k x z omega).coeffOn Q).toCoeffField =
      Annular.subConstCutoffField M L (parentFluxIncrement M L k z omega)
        (Cutoff.translateCutoffSample x omega) :=
  rfl

/-! ## 3. The frame identity -/

/-- The cutoff coefficient at the child's translated sample is the cutoff
coefficient at the parent's, moved by `x − z`. -/
theorem coefficientCutoff_translate_sub (M : ABKModel d) (L : ℤ) (x z : Vec d)
    (omega : Cutoff.CutoffSample d) (y : Vec d) :
    (Cutoff.coefficientCutoff M.nu L (Cutoff.translateCutoffSample z omega)).toCoeffField
        (y + (x - z)) =
      (Cutoff.coefficientCutoff M.nu L (Cutoff.translateCutoffSample x omega)).toCoeffField
        y := by
  have hz := congrFun (coefficientCutoff_comp_add_eq_translateCutoffSample M L z omega)
    (y + (x - z))
  have hx := congrFun (coefficientCutoff_comp_add_eq_translateCutoffSample M L x omega) y
  have hpt : y + (x - z) + z = y + x := by
    rw [add_assoc, sub_add_cancel]
  rw [← hz, ← hx, hpt]

/-- **The frame identity.**

The re-based family's representative is, on every cube, the `x−z` translate of
the *parent's* flux-corrected carrier field at the parent's translated sample. -/
theorem parentRebasedFamily_coeffOn_eq_translateCoeffField (M : ABKModel d) (L k : ℤ)
    (x z : Vec d) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) :
    ((parentRebasedFamily M L k x z omega).coeffOn Q).toCoeffField =
      translateCoeffField (x - z)
        (Support.fluxCorrectedRegField M L k (originCube d k)
          (Cutoff.translateCutoffSample z omega)).toFun := by
  funext y
  rw [parentRebasedFamily_coeffOn]
  show (Cutoff.coefficientCutoff M.nu L (Cutoff.translateCutoffSample x omega)).toCoeffField
      y - parentFluxIncrement M L k z omega = _
  have hRHS : translateCoeffField (x - z)
      (Support.fluxCorrectedRegField M L k (originCube d k)
        (Cutoff.translateCutoffSample z omega)).toFun y =
      (Cutoff.coefficientCutoff M.nu L (Cutoff.translateCutoffSample z omega)).toCoeffField
          (y + (x - z)) - parentFluxIncrement M L k z omega := by
    show (Support.fluxCorrectedRegField M L k (originCube d k)
      (Cutoff.translateCutoffSample z omega)).toFun (fun i => y i + (x - z) i) = _
    rw [Support.fluxCorrectedRegField_toFun]
    rfl
  rw [hRHS, coefficientCutoff_translate_sub M L x z omega y]

/-! ## 4. The equation at the re-based family -/

/-- **The anchor's equation, in the child's frame at the parent's correction.**

Restriction to `x + □_n`, untranslation to the child's own frame, and the
antisymmetric shift by the *parent's* constant, composed. -/
theorem isForcedEquation_parentRebasedFamily {n m k : ℤ} (M : ABKModel d) (L : ℤ)
    (x z : Vec d) (omega : Cutoff.CutoffSample d)
    {u : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsub : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (heq : Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (openCubeSet (originCube d m)) u g) :
    Ch03.IsForcedEquation (originCube d n) (parentRebasedFamily M L k x z omega)
      (H1Function.untranslate x
        (u.restrict (isOpen_translateSet_openCubeSet x n) hsub))
      (fun y => -g (y + x)) := by
  have hrestrict := isDivFormWeakSolutionOn_restrict
    (isOpen_translateSet_openCubeSet x n) hsub heq
  have huntrans := isDivFormWeakSolutionOn_translateCutoffSample M L x omega hrestrict
  have hshift := isDivFormWeakSolutionOn_sub_const_of_skew
    (matTranspose_parentFluxIncrement M L k z omega) huntrans
  refine isForcedEquation_neg_of_isDivFormWeakSolutionOn ?_
  rw [parentRebasedFamily_coeffOn]
  exact hshift

end

end Algsuperdiff.Section4.Provider.ExcessDecay
