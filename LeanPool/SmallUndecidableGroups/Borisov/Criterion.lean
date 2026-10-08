/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Construction
public import LeanPool.SmallUndecidableGroups.Borisov.Mod5.Sparsity

/-!
# Borisov's simulation criterion

The forward implication is the relator calculation in `Construction.lean`.  The
converse is the complete normal-form argument, culminating in the mod-five
free-product syllable comparison that bounds a coefficient preimage by one
displayed rule letter.
-/

@[expose] public section

namespace Undecidability
namespace Borisov

/-- The deep normal-form direction in Borisov's simulation theorem. -/
theorem criterion_converse
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    (presentation datum).wordProblem (testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  BorisovModFiveSparsity.criterion_converse datum Q

/-- Borisov's simulation theorem, specialized to the standing datum. -/
theorem criterion
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    ThueEq (Thue.systemOf datum.F datum.E) Q datum.P ↔
      (presentation datum).wordProblem (testWord Q) :=
  ⟨criterion_forward datum Q, criterion_converse datum Q⟩

end Borisov
end Undecidability
