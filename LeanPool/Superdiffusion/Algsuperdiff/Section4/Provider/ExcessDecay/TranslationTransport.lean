/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Translation

/-!
# TranslationTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The A4 translation transport of the weak equation

The frozen theorem's own datum lives at the *untranslated* sample `ω` on the
window `z + □_{n+2}`.  This module moves the weak equation between the two
frames.

Two ingredients, both exact:

* **the function side** — `H1Function.untranslate z` / `H10Function.translate`,
  with the Lebesgue change of variables
  `setIntegral_comp_addRight_translateSet`.  The translated frame's solution is
  `x ↦ u(x + z)` and its forcing `x ↦ g(x + z)`.
* **the coefficient side** — `Cutoff.coefficientCutoff_translateCutoffSample`:
  `a_L(·, translateCutoffSample z ω) = a_L(· + z, ω)` *exactly*, as regular
  coefficient fields.  So the translated frame's coefficient field is the cutoff
  coefficient of the translated sample; nothing is lost or approximated.

## Main results

* `isDivFormWeakSolutionOn_untranslate` — the weak equation on `translateSet z U`
  becomes the weak equation on `U` for the back-translated data.
* `isOpen_translateSet_openCubeSet`,
  `translateSet_openCubeSet_subset_of_frontier_inter_empty` — the anchor's window
  and its interior gate in `translateSet` spelling.
* `coefficientCutoff_comp_add_eq_translateCutoffSample` — the coefficient side.
* `isDivFormWeakSolutionOn_translateCutoffSample` — the two combined: from the
  anchor's frame to the harmonic slot's frame in one step.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the frame of the good event
  `𝒢(n+2, z; s/8, 1/2)` and of `𝓔(z+□_{n+2})`).
* The translated-sample convention: a cube translate is realized by translating
  the sample, never the cube.
* CoarseGraining, `Homogenization/Sobolev/H1/Translation.lean`,
  `Homogenization/Geometry/Translation.lean`
  (`setIntegral_comp_addRight_translateSet`).
* Repo, `Algsuperdiff/Section3/Cutoff/Symmetry.lean`
  (`coefficientCutoff_translateCutoffSample`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The weak equation untranslates -/

/-- **The divergence-form weak equation in the back-translated frame.**

If `-∇·a∇u = ∇·g` weakly on `U + z`, then `-∇·ã∇u_tilde = ∇·g` weakly on `U`, where
every datum is precomposed with `x ↦ x + z`.  Exact: the change of variables is
measure preserving and the `H¹₀` test functions correspond bijectively. -/
theorem isDivFormWeakSolutionOn_untranslate {U : Set (Vec d)} (z : Vec d)
    {a : CoeffField d} {u : H1Function (translateSet z U)} {g : Vec d → Vec d}
    (h : Support.IsDivFormWeakSolutionOn a (translateSet z U) u g) :
    Support.IsDivFormWeakSolutionOn (fun x => a (x + z)) U
      (H1Function.untranslate z u) (fun x => g (x + z)) := by
  intro phi
  have hkey := h (H10Function.translate phi z)
  have hL := setIntegral_comp_addRight_translateSet z U
    (fun y => vecDot (matVecMul (a y) (u.grad y)) (phi.toH1Function.grad (y - z)))
  have hR := setIntegral_comp_addRight_translateSet z U
    (fun y => vecDot (g y) (phi.toH1Function.grad (y - z)))
  have hLform : (fun y : Vec d =>
        vecDot (matVecMul (a (y + z)) (u.grad (y + z)))
          (phi.toH1Function.grad (y + z - z))) =
      fun y : Vec d =>
        vecDot (matVecMul ((fun x => a (x + z)) y)
          ((H1Function.untranslate z u).grad y)) (phi.toH1Function.grad y) := by
    funext y
    rw [add_sub_cancel_right]
    rfl
  have hRform : (fun y : Vec d => vecDot (g (y + z)) (phi.toH1Function.grad (y + z - z))) =
      fun y : Vec d =>
        vecDot ((fun x => g (x + z)) y) (phi.toH1Function.grad y) := by
    funext y
    rw [add_sub_cancel_right]
  rw [hLform] at hL
  rw [hRform] at hR
  rw [hL, hR]
  exact hkey

/-! ## 2. The window in `translateSet` spelling -/

/-- The frozen theorem's translated window, written as CoarseGraining's
`translateSet`, is open. -/
theorem isOpen_translateSet_openCubeSet (z : Vec d) (k : ℤ) :
    IsOpen (translateSet z (openCubeSet (originCube d k))) := by
  rw [← image_add_eq_translateSet z (openCubeSet (originCube d k)),
    ← openCubeAtScale_eq_image_add z k]
  exact isOpen_openCubeAtScale z k

theorem translateSet_openCubeSet_subset_of_frontier_inter_empty {k m : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hfr : ((fun y => z + y) '' openCubeSet (originCube d k)) ∩
        frontier (openCubeSet (originCube d m)) = ∅) :
    translateSet z (openCubeSet (originCube d k)) ⊆ openCubeSet (originCube d m) := by
  rw [← image_add_eq_translateSet z (openCubeSet (originCube d k))]
  exact image_add_openCubeSet_subset_of_frontier_inter_empty hz hfr

/-! ## 3. The coefficient side -/

/-- **The cutoff coefficient of the translated sample is the translated cutoff
coefficient**, as raw coefficient fields.  This is what makes the translated
frame's coefficient field the manuscript's own `a_L` at `translateCutoffSample z ω`
rather than an approximation. -/
theorem coefficientCutoff_comp_add_eq_translateCutoffSample (M : ABKModel d) (L : ℤ)
    (z : Vec d) (omega : Cutoff.CutoffSample d) :
    (fun x : Vec d => (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (x + z)) =
      (Cutoff.coefficientCutoff M.nu L (Cutoff.translateCutoffSample z omega)).toCoeffField := by
  funext x
  have h := congrArg (fun A : RegCoeffField d => A x)
    (Cutoff.coefficientCutoff_translateCutoffSample M.nu L z omega)
  exact h.symm

/-! ## 4. The two frames, combined -/

/-- **From the anchor's frame to the harmonic slot's frame.**

The anchor's equation `-∇·a_L(·,ω)∇u = ∇·g` on the window `z + S` becomes, on
`S` itself, the equation for the cutoff coefficient at the **translated sample**
`translateCutoffSample z ω`, with solution `u(· + z)` and forcing `g(· + z)`.
This is the A4 transport of the equation leg. -/
theorem isDivFormWeakSolutionOn_translateCutoffSample {S : Set (Vec d)}
    (M : ABKModel d) (L : ℤ) (z : Vec d) (omega : Cutoff.CutoffSample d)
    {u : H1Function (translateSet z S)} {g : Vec d → Vec d}
    (h : Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (translateSet z S) u g) :
    Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L (Cutoff.translateCutoffSample z omega)).toCoeffField
      S (H1Function.untranslate z u) (fun x => g (x + z)) := by
  have hbase := isDivFormWeakSolutionOn_untranslate z h
  rwa [coefficientCutoff_comp_add_eq_translateCutoffSample M L z omega] at hbase

end

end Algsuperdiff.Section4.Provider.ExcessDecay
