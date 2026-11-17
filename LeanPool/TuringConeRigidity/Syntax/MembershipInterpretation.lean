/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/MembershipInterpretation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ExtensionBasicAxioms
public import LeanPool.TuringConeRigidity.SetModels.RecursiveNameSymmetry

/-!
# Membership Interpretation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
universe u

def Formula.toMembership : Formula → RecursiveNames.Formula
  | .equal i j => .equal i j
  | .member i j => .member i j
  | .conj φ ψ => .conj φ.toMembership ψ.toMembership
  | .neg φ => .neg φ.toMembership
  | .existsMem i φ => .existsSet (.conj (.member 0 (i+1)) φ.toMembership)

theorem Formula.realize_toMembership (φ : Formula) (M : ZFSet.{u})
    (env : ℕ → ZFSet.{u}) :
    φ.toMembership.Realize (M : Set ZFSet.{u}) env ↔ φ.Realize M env := by
  induction φ generalizing env with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ env) (ihψ env)
  | neg φ ih => exact not_congr (ih env)
  | existsMem i φ ih =>
    have hcons (x : ZFSet.{u}) : (fun n => if n = 0 then x else env (n-1)) = cons x env := by
      funext n
      cases n <;> simp [cons]
    simp [toMembership,RecursiveNames.Formula.Realize,Formula.Realize,hcons,ih]

end TuringRigidity.BoundedSetTheory

end OAI
