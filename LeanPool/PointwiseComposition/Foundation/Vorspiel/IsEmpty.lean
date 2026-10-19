/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Basic.IsEmpty.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace IsEmpty

variable {o : Sort u} (h : IsEmpty o)

lemma eq_elim' {α : Sort*} (f : o → α) : f = h.elim' :=
  funext h.elim

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim :=
  funext h.elim

end IsEmpty

end

end PointwiseComposition
