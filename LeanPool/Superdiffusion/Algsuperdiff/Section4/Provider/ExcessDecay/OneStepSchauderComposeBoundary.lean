/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWeylRepresentative

/-!
# OneStepSchauderComposeBoundary

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary branch: the classical competitor on the doubled window

The interior branch obtains its classically harmonic competitor by applying
Weyl's lemma on the anchor's replacement cube
(`OneStepSchauderComposeInterior`).  On the **boundary** branch the replacement
window `V = (x + □_k) ∩ □_m` meets a face of `∂□_m`, and the competitor is
harmonic only up to that face.  The manuscript's device is the odd reflection:
`OddReflectionAssembly.isWeaklyHarmonicOn_reflectedWindow_of_meets{Upper,Lower}Face`
extends a weakly harmonic `v` on `V` to a weakly harmonic function on the
**doubled** window `reflectedWindow x m k`, which is again an open bounded convex
box.

That is exactly the hypothesis `OneStepWeylRepresentative.exists_harmonicRepresentative_full`
consumes — `IsOpen` plus `Support.IsWeaklyHarmonicOn` — so the classical
competitor on the doubled window is available with no new analysis:

* `exists_classicalCompetitor_reflectedWindow` — the generic form;
* `exists_classicalCompetitor_reflectedWindow_of_meetsUpperFace` and its
  lower-face twin — composed with the one-met-face transfer, i.e. starting from
  a weakly harmonic competitor on the *window* itself;
* `harmonicOnNhd_truncatedWindow_of_classicalCompetitor` — the restriction to
  the branch's own window, which is the shape the Schauder producer consumes.

## What is still open on the boundary branch (enumerated, not hidden)

1. **The boundary Schauder producer.**  `OneStepSchauderProducer.exists_gradientHolder_interior`
   is instantiated at the *interior* ball family
   (`OneStepSchauderWindow.metricBall_subset_truncatedWindow_of_interior`,
   radius `3^{n-3}/2`), which is available only under `x + □_{n-2} ⊆ □_m`.  On
   the boundary branch the doubled window supplies room across the **met**
   coordinate, but the **unmet** coordinates are still cut by `∂□_m` with no
   quantitative gap in the present hypotheses.  A boundary ball family — and
   hence a boundary analogue of `schauderWindowConst` — is the remaining
   geometric input.
3. **The multi-met-face regime.**  `OddReflectionAssembly` closes only the
   one-met-face case (its own scope note); the iteration over the intermediate
   partially reflected boxes is untouched.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. Weyl's lemma on the doubled window -/

/-- **The classical competitor on the doubled window.**  The reflected window is an open bounded
convex box, so Weyl's lemma applies verbatim: a variationally harmonic `H¹` function on it has a
globally square-integrable representative which is classically harmonic on the whole box and agrees
with it almost everywhere. -/
theorem exists_classicalCompetitor_reflectedWindow [NeZero d] (x : Vec d) (m k : ℤ)
    {w : H1Function (reflectedWindow x m k)}
    (hw : IsWeaklyHarmonicOn (reflectedWindow x m k) w) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m k) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (reflectedWindow x m k)] w.toFun := by
  obtain ⟨V, hVharm, hVmem, hVae⟩ :=
    exists_harmonicRepresentative_memLp (isOpen_reflectedWindow x m k) hw
  refine ⟨V, hVharm, hVmem, ?_⟩
  have h1 : V =ᵐ[volume.restrict (reflectedWindow x m k)]
      Set.indicator (reflectedWindow x m k) w.toFun :=
    MeasureTheory.ae_restrict_of_ae hVae
  filter_upwards [h1,
    MeasureTheory.self_mem_ae_restrict (isOpen_reflectedWindow x m k).measurableSet] with p hp hpR
  rw [hp, Set.indicator_of_mem hpR]

/-! ## 2. Restriction to the branch's own window -/

/-! ## 3. The one-met-face compositions -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
