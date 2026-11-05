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

namespace Classical



variable {α : Sort*} {p : α → Prop} {r : α → α → Prop}

/-- Choose the unique witness supplied by `h`. -/
noncomputable def chooseUnique (h : ∃! x, p x) : α :=
  _root_.Classical.choose h.exists

lemma chooseUnique_spec (h : ∃! x, p x) : p (chooseUnique h) :=
  _root_.Classical.choose_spec h.exists

lemma choose_uniq (h : ∃! x, p x) (hx : p x) : x = chooseUnique h :=
  h.unique hx (chooseUnique_spec h)

@[simp]
lemma chooseUnique_eq_iff_right (h : ∃! x, p x) : x = chooseUnique h ↔ p x :=
  ⟨by rintro rfl; exact chooseUnique_spec h, choose_uniq _⟩

@[simp]
lemma chooseUnique_eq_iff_left (h : ∃! x, p x) : chooseUnique h = x ↔ p x :=
  by
  rw [eq_comm]
  exact chooseUnique_eq_iff_right h

lemma exitsUnique_extend (h : ∀ x, p x → ∃! y, r x y) (default : α) (x : α) :
    ∃! y, (p x → r x y) ∧ (¬p x → y = default) :=
  by
  by_cases hx : p x
  · simpa [hx] using h _ hx
  · simp [hx]

/-- Choose the unique `r`-successor when `p x` holds, or return `default` otherwise. -/
noncomputable def extendedChooseUnique (h : ∀ x, p x → ∃! y, r x y) (default : α) (x : α) : α :=
  _root_.Classical.choose (exitsUnique_extend h default x).exists

lemma extendedChooseUnique_spec (h : ∀ x, p x → ∃! y, r x y) (default : α) (hx : p x) :
    r x (extendedChooseUnique h default x) :=
  _root_.Classical.choose_spec (exitsUnique_extend h default x).exists |>.1 hx

lemma extendedChooseUnique_spec_not (h : ∀ x, p x → ∃! y, r x y) (default : α) (hx : ¬p x) :
    extendedChooseUnique h default x = default :=
  _root_.Classical.choose_spec (exitsUnique_extend h default x).exists |>.2 hx

lemma extendedChooseUnique_uniq (h : ∀ x, p x → ∃! y, r x y) (default : α) (hpx : p x)
    (hrx : r x y) : y = extendedChooseUnique h default x :=
  (h x hpx).unique hrx (extendedChooseUnique_spec h default hpx)

lemma extendedChooseUnique_eq_iff (h : ∀ x, p x → ∃! y, r x y) (default : α) (hpx : p x) :
    y = extendedChooseUnique h default x ↔ r x y :=
  ⟨by rintro rfl; exact extendedChooseUnique_spec h default hpx,
    extendedChooseUnique_uniq h default hpx⟩

end Classical

end

end PointwiseComposition
