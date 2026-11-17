/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ParametricEval.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.OracleCode
public import Mathlib.Computability.PartrecCode

/-!
# Parametric Eval
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OracleCode
open Computable

theorem eval_partrec {α : Type*} [Primcodable α] {g : α → ℕ →. ℕ}
    (hg : Partrec₂ g) (c : OracleCode) : Partrec₂ (fun a n => eval (g a) c n) := by
  induction c with
  | zero => exact Computable.const 0
  | succ => exact Computable.succ.comp snd
  | left => exact (fst.comp Computable.unpair).comp snd
  | right => exact (snd.comp Computable.unpair).comp snd
  | query => exact hg
  | pair c d hc hd =>
    change Partrec (fun z : α × ℕ =>
      (eval (g z.1) c z.2).bind (fun a => (eval (g z.1) d z.2).map (Nat.pair a)))
    apply Partrec.bind hc
    apply Partrec.map (hd.comp (fst.comp fst) (snd.comp fst))
    exact Primrec₂.natPair.to_comp.comp (snd.comp fst) snd
  | comp c d hc hd =>
    exact hd.bind (hc.comp (fst.comp fst) snd)
  | prec c d hc hd =>
    exact Partrec.nat_rec ((snd.comp Computable.unpair).comp snd)
      (hc.comp fst ((fst.comp Computable.unpair).comp snd))
      (hd.comp (fst.comp fst)
        (Primrec₂.natPair.to_comp.comp ((fst.comp Computable.unpair).comp (snd.comp fst))
          (Primrec₂.natPair.to_comp.comp (fst.comp snd) (snd.comp snd)))).to₂
  | find c hc =>
    exact Partrec.rfind ((hc.comp (fst.comp fst)
      (Primrec₂.natPair.to_comp.comp (snd.comp fst) snd)).map
        ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).to_comp))

end TuringRigidity.OracleCode

end OAI
