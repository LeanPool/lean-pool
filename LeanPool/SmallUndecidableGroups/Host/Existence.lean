/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.Tower

/-!
# Existence

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability
namespace Host

/-- A three-generator, nine-relator host with the extra normal-weight-one property. -/
theorem exists_threeNineHost :
    ∃ P : FP 3 9,
      (∃ z : Word 3, P.NormallyGenerates z) ∧
        ¬ ComputablePred P.wordProblem := by
  obtain ⟨datum⟩ := Thue.exists_standingDatum
  exact ⟨presentationOf datum, ⟨zWord, z_normallyGenerates datum⟩,
    wordProblem_unsolvable datum⟩

end Host
end Undecidability
