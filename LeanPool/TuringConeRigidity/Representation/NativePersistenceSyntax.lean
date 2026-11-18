/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/NativePersistenceSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTNativeComparison

/-!
# Native Persistence Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability ArithmeticTree
universe u
noncomputable section

/-- Rename variables recursively in internal formula syntax, lifting the renaming beneath set
quantifiers. -/
def InternalFormula.rename : InternalFormula → (ℕ → ℕ) → InternalFormula
  | .bounded p, v => .bounded (p.rename v)
  | .conj p q, v => .conj (p.rename v) (q.rename v)
  | .neg p, v => .neg (p.rename v)
  | .existsSet p, v => .existsSet (p.rename (liftMap v))

theorem InternalFormula.realize_rename (p : InternalFormula) (M : ZFSet.{u})
    (v : ℕ → ℕ) (e : ℕ → ZFSet.{u}) :
    (p.rename v).Realize M e ↔ p.Realize M (e ∘ v) := by
  induction p generalizing v e with
  | bounded p => exact p.realize_rename M v e
  | conj p q hp hq => exact and_congr (hp v e) (hq v e)
  | neg p hp => exact not_congr (hp v e)
  | existsSet p hp =>
    change (∃ x ∈ M, (p.rename (liftMap v)).Realize M (cons x e)) ↔ _
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    have he : cons x e ∘ liftMap v = cons x (e ∘ v) := by funext i; cases i <;> rfl
    exact (hp (liftMap v) (cons x e)).trans (he ▸ Iff.rfl)

/-- Bounded formula asserting that the set-coded action moves some element of `i`. -/
def setMovedFormula (f i : ℕ) : Formula :=
  .existsMem i (.existsMem (i+1) (.conj (.pairMem 1 0 (f+2)) (.neg (.equal 1 0))))

@[simp] theorem eval_setMovedFormula (f i : ℕ) (e : ℕ → ZFSet.{u}) :
    (setMovedFormula f i).Eval e ↔ SetMoved (e f) (e i) := by
  simp only [setMovedFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,SetMoved]

/-- Variable placement for the native nonidentity and persistence formula. -/
def nativeSlots : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | _+4 => 4

/-- An internal formula asserting existence of a nonidentity action satisfying the persistence
condition. -/
def nonidentityFormula : InternalFormula :=
  .existsSet (.conj (.bounded (actionFormula 0 3 2))
    (.conj (.bounded (setMovedFormula 0 3)) (persistenceFormula.rename nativeSlots)))

theorem realize_nonidentityFormula (M : ZFSet.{u}) (hM : Transitive M)
    (D L i : ZFSet.{u}) (hD : D ∈ M) (hL : L ∈ M) (hi : i ∈ M) (hω : ZFSet.omega.{u} ∈ M) :
    nonidentityFormula.Realize M (cons D (cons L (cons i (fun _ => ZFSet.omega)))) ↔
      NativeNonidentity M D L i := by
  change (∃ f ∈ M, _) ↔ ∃ f ∈ M, _
  apply exists_congr
  intro f
  apply and_congr_right
  intro hf
  let e := cons f (cons D (cons L (cons i (fun _ => ZFSet.omega))))
  have he : ∀ j, e j ∈ M := by
    intro j
    rcases j with _|_|_|_|j <;> simp [e,hf,hD,hL,hi,hω]
  have hr : e ∘ nativeSlots = cons D (cons L (cons i (cons f (fun _ => ZFSet.omega)))) := by
    funext j
    rcases j with _|_|_|_|j <;> rfl
  change ((actionFormula 0 3 2).Realize M e ∧
    (setMovedFormula 0 3).Realize M e ∧ (persistenceFormula.rename nativeSlots).Realize M e) ↔ _
  rw [(actionFormula 0 3 2).absolute M hM e he,eval_actionFormula,
    (setMovedFormula 0 3).absolute M hM e he,eval_setMovedFormula,
    InternalFormula.realize_rename,hr]
  rfl

end
end TuringRigidity.SetModelSatisfaction

end OAI
