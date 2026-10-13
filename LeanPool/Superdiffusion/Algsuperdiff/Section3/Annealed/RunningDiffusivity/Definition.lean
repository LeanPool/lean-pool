/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.WellDefinedness
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.Comparator

/-!
# Definition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The running diffusivity

The Section 3 running diffusivity is the unique positive scalar supplied by
`existsUnique_sigmaBar`. There is no fallback value or provisional branch.

## Main definition

* `sigmaBar`: the genuine running diffusivity of the coefficient cutoff.
-/

namespace Algsuperdiff.Section3.Annealed

noncomputable section

variable {d : ℕ}

/-- The genuine positive running diffusivity of the coefficient cutoff at
scale `m`, selected from its proved unique infinite-volume characterization. -/
noncomputable def sigmaBar (M : ABKModel d) (m : ℤ) :
    Observable.PositiveScalar :=
  ⟨Classical.choose (existsUnique_sigmaBar M m),
    (Classical.choose_spec (existsUnique_sigmaBar M m)).1.1⟩

end


end Algsuperdiff.Section3.Annealed
