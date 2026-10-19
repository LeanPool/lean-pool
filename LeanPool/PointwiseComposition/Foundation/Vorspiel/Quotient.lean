/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Fin.Matrix

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace Quotient

open _root_.Matrix Matrix

variable {α : Type u} [s : Setoid α] {β : Sort v}

@[elab_as_elim]
lemma inductionOnVec {φ : (Fin n → Quotient s) → Prop} (v : Fin n → Quotient s)
    (h : ∀ v : Fin n → α, φ (fun i => Quotient.mk s (v i))) : φ v :=
  Quotient.induction_on_pi v h

/-- The lift Vec construction in `Quotient`. -/
def liftVec :
    ∀ {n} (f : (Fin n → α) → β),
      (∀ v₁ v₂ : Fin n → α, (∀ n, v₁ n ≈ v₂ n) → f v₁ = f v₂) → (Fin n → Quotient s) → β
  | 0, f, _, _ => f ![]
  | n + 1, f, h, v =>
    let ih : α → (Fin n → Quotient s) → β := fun a v =>
      liftVec (n := n) (fun v => f (a :> v))
        (fun v₁ v₂ hv =>
          h (a :> v₁) (a :> v₂) (Fin.cases (by simp [cons_val_zero, Setoid.refl]) hv))
        v
    Quot.liftOn (vecHead v) (ih · (vecTail v))
      (fun a b hab =>
        by
        have : ∀ v, f (a :> v) = f (b :> v) := fun v ↦
          h _ _ (Fin.cases hab (by simp [cons_val_succ, Setoid.refl]))
        simp [this, ih])

@[simp]
lemma liftVec_zero (f : (Fin 0 → α) → β) (h) (v : Fin 0 → Quotient s) : liftVec f h v = f ![] :=
  rfl

lemma liftVec_mk {n} (f : (Fin n → α) → β) (h) (v : Fin n → α) :
    liftVec f h (Quotient.mk s ∘ v) = f v := by
  induction n with
  | zero => simp [liftVec, empty_eq]
  | succ n ih =>
    simp [liftVec]
    simpa using!
      ih (fun v' => f (vecHead v :> v'))
        (fun v₁ v₂ hv => h (vecHead v :> v₁) (vecHead v :> v₂) (Fin.cases (refl _) hv))
        (vecTail v)

@[simp]
lemma liftVec_mk₁ (f : (Fin 1 → α) → β) (h) (a : α) : liftVec f h ![Quotient.mk s a] = f ![a] :=
  liftVec_mk f h ![a]

@[simp]
lemma liftVec_mk₂ (f : (Fin 2 → α) → β) (h) (a₁ a₂ : α) :
    liftVec f h ![Quotient.mk s a₁, Quotient.mk s a₂] = f ![a₁, a₂] :=
  liftVec_mk f h ![a₁, a₂]

end Quotient

end

end PointwiseComposition
