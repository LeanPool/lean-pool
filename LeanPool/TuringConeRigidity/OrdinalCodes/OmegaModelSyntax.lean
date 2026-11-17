/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaModelSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaModelCollapse

/-!
# Omega Model Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OmegaModelCore.OmegaData
open BoundedSetTheory
universe u
noncomputable section
variable {α : Type u} (S : OmegaData α)

/-- Prepend a value to the variable environment. -/
def push {β : Type*} (x : β) (e : ℕ → β) : ℕ → β
  | 0 => x
  | n+1 => e n

/-- Evaluate a bounded formula in the abstract membership structure. -/
def Eval (e : ℕ → α) : Formula → Prop
  | .equal i j => e i = e j
  | .member i j => S.mem (e i) (e j)
  | .conj p q => Eval e p ∧ Eval e q
  | .neg p => ¬ Eval e p
  | .existsMem i p => ∃ x, S.mem x (e i) ∧ Eval (push x e) p

theorem collapse_eval (p : Formula) (e : ℕ → S.Core) :
    p.Eval (fun i => S.collapse (e i)) ↔ S.Eval (fun i => (e i).val) p := by
  induction p generalizing e with
  | equal i j =>
    change S.collapse (e i) = S.collapse (e j) ↔ (e i).val = (e j).val
    exact ⟨fun h => congrArg Subtype.val (S.collapse_injective h),
      fun h => congrArg S.collapse (Subtype.ext h)⟩
  | member i j => exact S.collapse_mem_iff (e i) (e j)
  | conj p q hp hq => exact and_congr (hp e) (hq e)
  | neg p hp => exact not_congr (hp e)
  | existsMem i p hp =>
    have hstep (y : S.Core) : p.Eval (cons (S.collapse y) (fun i => S.collapse (e i))) ↔
        S.Eval (push y.val (fun i => (e i).val)) p := by
      have he : (fun i => S.collapse (push y e i)) =
          cons (S.collapse y) (fun i => S.collapse (e i)) := by
        funext i
        cases i <;> rfl
      have hv : (fun i => (push y e i).val) = push y.val (fun i => (e i).val) := by
        funext i
        cases i <;> rfl
      simpa only [he,hv] using hp (push y e)
    constructor
    · rintro ⟨x,hx,hp'⟩
      obtain ⟨y,hy,rfl⟩ := (S.mem_collapse (e i) x).mp hx
      exact ⟨y.val,hy,(hstep y).mp hp'⟩
    · rintro ⟨x,hx,hp'⟩
      let y : S.Core := ⟨x,S.core_transitive (e i).property hx⟩
      exact ⟨S.collapse y,(S.mem_collapse (e i) _).mpr ⟨y,hx,rfl⟩,
        (hstep y).mpr hp'⟩

/-- The membership structure has a set containing exactly either of two supplied elements. -/
def PairingAxiom : Prop := ∀ a b : α, ∃ c, ∀ x, S.mem x c ↔ x=a ∨ x=b

/-- The membership structure has a union set for every element. -/
def UnionAxiom : Prop := ∀ a : α, ∃ b, ∀ x, S.mem x b ↔ ∃ y, S.mem y a ∧ S.mem x y

/-- The membership structure admits separation for each bounded formula and parameter
environment. -/
def SeparationAxiom : Prop := ∀ (p : Formula) (e : ℕ → α) (a : α),
  ∃ b, ∀ x, S.mem x b ↔ S.mem x a ∧ S.Eval (push x e) p

end
end TuringRigidity.OmegaModelCore.OmegaData

end OAI
