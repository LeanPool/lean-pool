/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteRealPacking.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GroundDegreePresentation

/-!
# Finite Real Packing
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory
universe u

def packedReal : {n : ℕ} → (Fin n → Oracle) → Oracle
  | 0, _ => FixedArithmetic.zero
  | n+1, v => join (v 0) (packedReal (fun i : Fin n => v i.succ))

def realPart (P : Oracle) : ℕ → Oracle
  | 0 => fun k => P (2*k)
  | i+1 => realPart (fun k => P (2*k+1)) i

theorem realPart_packed {n : ℕ} (v : Fin n → Oracle) (i : Fin n) :
    realPart (packedReal v) i = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · funext k
      simp [realPart,packedReal,join]
    · have ht : (fun k => packedReal v (2*k+1)) = packedReal (fun j : Fin n => v j.succ) := by
        funext k
        simp [packedReal,join,Nat.add_div]
      change realPart (fun k => packedReal v (2*k+1)) j = v j.succ
      rw [ht]
      exact ih _ j

theorem packedReal_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Oracle) (hv : ∀ i, v i ∈ modelReals M) :
    packedReal v ∈ modelReals M := by
  induction n with
  | zero => exact sourceT_zero_real M hM hT
  | succ n ih => exact sourceT_real_join M hM hT (hv 0) (ih _ (fun i => hv i.succ))

end TuringRigidity.RelativeConstructible

end OAI
