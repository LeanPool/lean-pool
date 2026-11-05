/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumZeroTrace

/-!
# CubeSchauderBoundaryZeroTrace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the boundary zero-trace slot of the zero-datum competitor

The boundary regime's classical-competitor producer carries one structural slot
the interior regime does not have: the *localized zero trace* of the harmonic
competitor `v` on the truncated window, tested against the reflected window.
This is what licenses the odd reflection across the met faces.

For the **zero-datum** cube problem that slot is free.  The competitor of
`CubeSchauderResidue.exists_frozenHarmonicReplacement_truncatedWindow` is

```text
  v = u|_{(x+□_k) ∩ □_m} − w ,   u ∈ H¹₀(□_m) ,   w ∈ H¹₀((x+□_k) ∩ □_m) ,
```

and both summands carry the trace: `u` by
`OneStepDatumZeroTrace.localizedZeroTraceFunctionOn_truncatedWindow_of_memH10_cube`
(a cutoff supported in the reflected window localizes the *global* zero trace on
`□_m` to `reflectedWindow ∩ □_m = (x+□_k) ∩ □_m`), and `w` by
`localizedZeroTraceFunctionOn_of_memH10` because it is already `H¹₀` of the
window itself.  The subtraction closure `localizedZeroTraceFunctionOn_sub` does
the rest.

This module is that composition, stated pointwise on the value field so that it
applies to any concrete realization of the difference (an `H1Function` subtraction,
a `restrict`, or a hand-built carrier).

## References

* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- **The zero-datum boundary trace slot.**

If `u ∈ H¹₀(□_m)` and `v ∈ H¹₀((x+□_k) ∩ □_m)`, then their difference has the
face-only localized zero trace on the truncated window against the reflected
window.  This is the zero-trace slot the boundary producer asks for, here at the
frozen harmonic replacement of a zero-datum solution: no extra hypothesis is
needed beyond the two memberships. -/
theorem localizedZeroTraceFunctionOn_sub_memH10_cube {m k : ℤ} (x : Vec d)
    {u v : Vec d → ℝ}
    (hu : MemH10 (openCubeSet (originCube d m)) u)
    (hv : MemH10 (truncatedWindow x m k) v)
    {f : Vec d → ℝ} (hf : ∀ y, f y = u y - v y) :
    LocalizedZeroTraceFunctionOn (truncatedWindow x m k) (reflectedWindow x m k) f := by
  have h1 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) u :=
    localizedZeroTraceFunctionOn_truncatedWindow_of_memH10_cube x hu
  have h2 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) v :=
    localizedZeroTraceFunctionOn_of_memH10 hv
  exact localizedZeroTraceFunctionOn_congr (fun y => (hf y).symm)
    (localizedZeroTraceFunctionOn_sub h1 h2)

/-- The `H¹`-carrier form: the difference of the restriction of a global `H¹₀(□_m)`
datum and a window `H¹₀` corrector. -/
theorem localizedZeroTraceFunctionOn_h1Function_sub {m k : ℤ} (x : Vec d)
    {u : Vec d → ℝ} (hu : MemH10 (openCubeSet (originCube d m)) u)
    (w : H10Function (truncatedWindow x m k))
    {U : H1Function (truncatedWindow x m k)} (hU : ∀ y, U.toFun y = u y) :
    LocalizedZeroTraceFunctionOn (truncatedWindow x m k) (reflectedWindow x m k)
      (U - w.toH1Function).toFun := by
  refine localizedZeroTraceFunctionOn_sub_memH10_cube x hu ⟨w, rfl⟩ (fun y => ?_)
  simp only [H1Function.sub_toFun, hU y]

end

end Algsuperdiff.Section4.Provider.Schauder
