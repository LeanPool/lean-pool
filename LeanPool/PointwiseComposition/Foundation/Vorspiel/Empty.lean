/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Data.Fintype.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace Empty

open _root_.Empty

lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim :=
  funext (by rintro ⟨⟩)

end Empty

end

end PointwiseComposition
