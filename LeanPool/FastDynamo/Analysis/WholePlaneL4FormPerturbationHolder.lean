/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneH1L4Embedding

/-!
# The whole-plane `L⁴` interface for the form perturbation

The quotient-level setting of the single form perturbation (`eq:form-small`, in the proof of
`prop:local-seed`): the exponent instances for `(4,4,2)` Hölder multiplication on quotient
`Lᵖ` spaces and the space `WholePlaneC3L4`.

The module is separate from `FastDynamo/Analysis/WholePlaneH1L4Embedding.lean` for build
weight: that module has some one hundred and thirty dependents, and nothing in its
embedding proof refers to any declaration below.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- The finite exponent `4` lies in the normed range of Bochner `Lᵖ`. -/
instance instFactOneLeFour : Fact (1 ≤ (4 : ENNReal)) :=
  ⟨by norm_num⟩

/-- The exponent identity `1/4 + 1/4 = 1/2` used by Hölder multiplication. -/
instance instHolderTripleFourFourTwo :
    ENNReal.HolderTriple 4 4 2 :=
  ⟨by
    rw [show (4 : ENNReal) = (4 : NNReal) by norm_num,
      show (2 : ENNReal) = (2 : NNReal) by norm_num]
    norm_cast
    norm_num⟩

/-! ## Whole-plane `C3`-valued `L⁴` -/

/-- Whole-plane `C3`-valued `L⁴`. -/
abbrev WholePlaneC3L4 := Lp C3 4 (volume : Measure WholePlane)

end

end FastDynamo
