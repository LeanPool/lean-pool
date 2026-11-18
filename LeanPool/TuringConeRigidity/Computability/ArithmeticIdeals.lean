/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticIdeals.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticRelations
public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalIdeal

/-!
# Arithmetic Ideals
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable CommonIdeal IndexMatrix TableIndices OracleJump EncodedForcing
open IndexPresentation NumericalIdeal
noncomputable section

theorem columns_at {B : OracleFamily} (hB : ArithmeticOracle B)
    {c k : ℕ → ℕ} (hc : Primrec c) (hk : Primrec k) :
    ArithmeticOracle (fun O v => columns (B O (c v)) (k v)) :=
  column_arith (hB.comp hc) hk

theorem value_tableOracle {B : Oracle} {e : ℕ} (h : Dom B e) :
    value B e = degree (tableOracle B e) :=
  value_eq ((valid_tableOracle B e).mp h)

theorem lower_arith {H : OracleFamily} (hH : ArithmeticOracle H) :
    Arith (fun O v => ∀ n e, Dom (columns (H O v) n) e →
      ∃ m, value (columns (H O v) n) e = degree (columns (H O v) m)) := by
  let l := left_primrec
  let r := right_primrec
  have hc := columns_at hH (l.comp l) (r.comp l)
  have hd := valid_arith hc r
  have ho := tableOracle_arith hc r
  have he := (degree_equal_arith (ho.comp l) (columns_at hH (l.comp (l.comp l)) r)).ex
  exact (hd.imp he).all.all.congr (fun O v => by
    simp only [left,right,Nat.unpair_pair]
    constructor
    · intro h n e hd
      simpa only [value_tableOracle hd] using h n e hd
    · intro h n e hd
      simpa only [value_tableOracle hd] using h n e hd)

theorem join_closed_arith {H : OracleFamily} (hH : ArithmeticOracle H) :
    Arith (fun O v => ∀ n m, ∃ k,
      degree (columns (H O v) n) ⊔ degree (columns (H O v) m) = degree (columns (H O v) k)) := by
  let l := left_primrec
  let r := right_primrec
  let c := l.comp (l.comp l)
  have he := degree_equal_arith
    (join_arith (columns_at hH c (r.comp (l.comp l))) (columns_at hH c (r.comp l)))
    (columns_at hH c r)
  exact he.ex.all.all.congr (fun _ _ => by simp only [left,right,Nat.unpair_pair]; rfl)

theorem jump_closed_arith {H : OracleFamily} (hH : ArithmeticOracle H) :
    Arith (fun O v => ∀ n, ∃ m,
      degreeJump (degree (columns (H O v) n)) = degree (columns (H O v) m)) := by
  let l := left_primrec
  let r := right_primrec
  have he := degree_equal_arith (jump_arith (columns_at hH (l.comp l) (r.comp l)))
    (columns_at hH (l.comp l) r)
  exact he.ex.all.congr (fun _ _ => by simp only [left,right,Nat.unpair_pair,degreeJump_degree])

theorem jumpCode_arith {H : OracleFamily} (hH : ArithmeticOracle H) :
    Arith (fun O v => JumpCode (H O v)) := by
  apply ((lower_arith hH).and ((join_closed_arith hH).and (jump_closed_arith hH))).congr
  intro O v
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.lower,h.join,h.jump⟩⟩

theorem includes_arith {A H : OracleFamily} (hA : ArithmeticOracle A)
    (hH : ArithmeticOracle H) : Arith (fun O v => Includes (A O v) (H O v)) := by
  have he := degree_equal_arith
    (columns_at hA (left_primrec.comp left_primrec) (right_primrec.comp left_primrec))
    (columns_at hH (left_primrec.comp left_primrec) right_primrec)
  exact he.ex.all.congr (fun _ _ => by simp only [Includes,left,right,Nat.unpair_pair])

end
end TuringRigidity.UniformArithmetic

end OAI
