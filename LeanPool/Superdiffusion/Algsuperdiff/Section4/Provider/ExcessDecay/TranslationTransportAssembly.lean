/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AntisymmetricShiftCutoff
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EquationRestriction
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedRepresentative

/-!
# TranslationTransportAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The equation leg of the interior clause, assembled

Starting from the frozen theorem's own datum

```text
  IsDirichletSolutionOn a_L(·,ω) □_m u h g
```



and its own interior gate `(z+□_{n+2}) ∩ ∂□_m = ∅`, it produces

```text
  IsForcedEquation □_{n+2}
    (fluxCorrectedCoeffFamily M L (n+2) □_{n+2} (translateCutoffSample z ω))
    (u(· + z))  (fun x => -g(x + z))
```

The three steps:

1. **restriction** to `z + □_{n+2}` — `EquationRestriction.lean`, driven by the
   anchor's frontier-empty gate;
2. **untranslation** to `□_{n+2}` at `translateCutoffSample z ω` —
   `TranslationTransport.lean`;
3. **the antisymmetric shift** `a_L ↦ ã_{L,n+2}` —
   `AntisymmetricShift{,Cutoff}.lean`.

Step 3 is performed *after* the untranslation, so the subtracted constant is
`(k_L − k_{n+2})_{□_{n+2}}` computed at the translated sample — which, by the
exact translation identity of step 2, is the manuscript's `(k_L −
k_{n+2})_{z+□_{n+2}}`.  The order is immaterial (the constant is
translation-inert), but this order is the one in which every proved cap is
stated.

## What the forcing becomes, exactly

The translated frame's forcing is `x ↦ -g(x + z)`; the sign is CoarseGraining's
`∇·g` convention (`Support/Dirichlet.lean`) and the translation is the A4 frame
move.  Both are invisible to the frozen theorem's right-hand side, whose
`g`-legs are seminorms (`[g]_{H^s}`), even and translation-covariant.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The coefficient field of the flux-corrected family -/

/-- The representative of `Support.fluxCorrectedCoeffFamily` on every cube is the
literal flux-corrected field. -/
theorem fluxCorrectedCoeffFamily_coeffOn_toCoeffField (M : ABKModel d) (L k : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    ((Support.fluxCorrectedCoeffFamily M L k Q omega).coeffOn R).toCoeffField =
      Support.fluxCorrectedField M L k Q omega := by
  rw [Support.fluxCorrectedCoeffFamily,
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField]
  exact Support.fluxCorrectedRegField_toFun M L k Q omega

/-! ## 2. The assembled equation leg -/

/-- **The interior clause's equation hypothesis, produced from the anchor's
own datum.**

Restriction to the parent window, the A4 untranslation, and the antisymmetric
shift, composed. -/
theorem isForcedEquation_fluxCorrectedCoeffFamily_translated {m n : ℤ}
    (M : ABKModel d) (L : ℤ) (z : Vec d) (omega : Cutoff.CutoffSample d)
    {u : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hfr : ((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
        frontier (openCubeSet (originCube d m)) = ∅)
    (heq : Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (openCubeSet (originCube d m)) u g) :
    IsForcedEquation (originCube d (n + 2))
      (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
        (Cutoff.translateCutoffSample z omega))
      (H1Function.untranslate z
        (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
          (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
      (fun x => -g (x + z)) := by
  have hrestrict := isDivFormWeakSolutionOn_restrict
    (isOpen_translateSet_openCubeSet z (n + 2))
    (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr) heq
  have huntrans := isDivFormWeakSolutionOn_translateCutoffSample M L z omega hrestrict
  have hshift := isDivFormWeakSolutionOn_fluxCorrectedField M L (n + 2)
    (originCube d (n + 2)) (Cutoff.translateCutoffSample z omega) huntrans
  refine isForcedEquation_neg_of_isDivFormWeakSolutionOn ?_
  rw [fluxCorrectedCoeffFamily_coeffOn_toCoeffField M L (n + 2)
    (originCube d (n + 2)) (originCube d (n + 2))
    (Cutoff.translateCutoffSample z omega)]
  exact hshift

/-- The same, entered at the frozen theorem's `IsDirichletSolutionOn` datum. -/
theorem isForcedEquation_fluxCorrectedCoeffFamily_of_isDirichletSolutionOn {m n : ℤ}
    (M : ABKModel d) (L : ℤ) (z : Vec d) (omega : Cutoff.CutoffSample d)
    {u hdat : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hfr : ((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
        frontier (openCubeSet (originCube d m)) = ∅)
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g) :
    IsForcedEquation (originCube d (n + 2))
      (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
        (Cutoff.translateCutoffSample z omega))
      (H1Function.untranslate z
        (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
          (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
      (fun x => -g (x + z)) :=
  isForcedEquation_fluxCorrectedCoeffFamily_translated M L z omega hz hfr hsol.2

/-! ## 3. The transported solution, read pointwise -/

/-- The transported solution's value: it is `u(· + z)`, with no modification. -/
theorem untranslate_restrict_toFun {m k : ℤ} {z : Vec d}
    (u : H1Function (openCubeSet (originCube d m)))
    (hsub : translateSet z (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m)) (x : Vec d) :
    (H1Function.untranslate z
        (u.restrict (isOpen_translateSet_openCubeSet z k) hsub)).toFun x =
      u.toFun (x + z) :=
  rfl

end

end Algsuperdiff.Section4.Provider.ExcessDecay
