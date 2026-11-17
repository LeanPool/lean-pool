/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/JumpIterationFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.JumpSetFormula
public import LeanPool.TuringConeRigidity.SetModels.ModelIterationFormula

/-!
# Jump Iteration Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open UniformArithmetic OracleJump
universe u

def JumpFormula (φ : Formula) : Prop := ∀ o Q x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.oracleGraph φ o Q x y).Eval e ↔ B = jump A)

namespace Formula
def jumpIteration (φ : Formula) (o R Qf Qn n A B : ℕ) : Formula :=
  modelIteration o R Qf n A B (oracleGraph φ (o+3) (Qn+3) 1 0)

theorem jumpIteration_spec {φ : Formula} (hφ : JumpFormula.{u} φ)
    (o R Qf Qn n x y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQn : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Qn)
    (hQf : ∀ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ e R) → ∀ k, finiteModelGraph a k ∈ e Qf)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w)
    (A : Oracle) (hA : ∀ i, realCode (iterate A i) ∈ e R)
    (hx : e x = realCode A) (N : ℕ) (hn : e n = natSet N) :
    (jumpIteration φ o R Qf Qn n x y).Eval e ↔ e y = realCode (iterate A N) := by
  apply modelIteration_spec o R Qf n x y _ e ho hQf N hn
    (fun i => realCode (iterate A i)) hA hx
  intro i w hw
  obtain ⟨B,rfl⟩ := hR w hw
  rw [hφ (o+3) (Qn+3) 1 0 (cons (realCode B) (cons (realCode (iterate A i)) (cons (natSet i) e)))
    ho hQn (iterate A i) B rfl rfl]
  exact ⟨fun h => congrArg realCode h,fun h => realCode_injective h⟩
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
