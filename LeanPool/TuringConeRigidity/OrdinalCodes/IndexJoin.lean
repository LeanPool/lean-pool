/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/IndexJoin.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TableIndices

/-!
# Index Join
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IndexJoin
open Encodable Computable UniformOracle CommonIdeal TableIndices

/-- Evaluate the first or second indexed program according to the parity of the joined input. -/
def dispatch (v : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ) : Part ℕ :=
  let n := (Nat.unpair v.2).2
  let c := if n.bodd then v.1.2 else v.1.1
  c.eval (Nat.pair (Nat.unpair v.2).1 (n / 2))

theorem dispatch_partrec : Partrec dispatch := by
  let n : Computable (fun v : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ => (Nat.unpair v.2).2) :=
    snd.comp (Computable.unpair.comp snd)
  have hc : Computable (fun v : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ =>
      cond (Nat.unpair v.2).2.bodd v.1.2 v.1.1) :=
    Computable.cond (Computable.nat_bodd.comp n) (snd.comp fst) (fst.comp fst)
  have hi := Primrec₂.natPair.to_comp.comp (fst.comp (Computable.unpair.comp snd))
    ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp.comp n)
  exact (Nat.Partrec.Code.eval_part.comp hc hi).of_eq (fun v => by
    cases hb : (Nat.unpair v.2).2.bodd <;> simp [dispatch, hb])

/-- A selected partial-recursive code for the join dispatcher. -/
noncomputable def dispatcher : Nat.Partrec.Code := Classical.choose (partrec_code dispatch_partrec)

theorem dispatcher_spec (e f : Nat.Partrec.Code) (x : ℕ) :
    dispatcher.eval (Nat.pair (encode (e, f)) x) = dispatch ((e, f), x) :=
  Classical.choose_spec (partrec_code dispatch_partrec) ((e, f), x)

/-- The program code joining the outputs of the two supplied program codes. -/
noncomputable def joined (e f : Nat.Partrec.Code) : Nat.Partrec.Code :=
  dispatcher.curry (encode (e, f))

theorem joined_primrec : Primrec₂ joined :=
  Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const dispatcher) Primrec.encode

theorem joined_eval (e f : Nat.Partrec.Code) (L : List ℕ) (n : ℕ) :
    (joined e f).eval (Nat.pair (encode L) n) =
      if n.bodd then f.eval (Nat.pair (encode L) (n/2)) else e.eval (Nat.pair (encode L) (n/2)) :=
        by
  rw [joined, Nat.Partrec.Code.eval_curry, dispatcher_spec]
  simp only [dispatch, Nat.unpair_pair]
  split <;> rfl

theorem joined_represents {Y A B : Oracle} {e f : Nat.Partrec.Code}
    (he : Represents Y e A) (hf : Represents Y f B) :
    Represents Y (joined e f) (join A B) := by
  have hs : ∀ n m a, a ∈ (joined e f).eval
      (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n) → a = bit (join A B n) := by
    intro n m a ha
    rw [joined_eval] at ha
    cases hb : n.bodd with
    | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
      obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp ha
      have hh := he.1 (n/2) (Nat.pair m t) a (by simpa [TableIndices.run, trial] using ht)
      simpa [join, hb] using hh
    | true =>
      simp only [hb, ↓reduceIte] at ha
      obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp ha
      have hh := hf.1 (n/2) (Nat.pair m t) a (by simpa [TableIndices.run, trial] using ht)
      simpa [join, hb] using hh
  have ht : ∀ n, ∃ m a, a ∈ (joined e f).eval
      (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n) := by
    intro n
    cases hb : n.bodd with
    | false =>
      obtain ⟨z, a, ha⟩ := he.2 (n/2)
      exact ⟨(Nat.unpair z).1, a, by
        rw [joined_eval, hb]
        exact Nat.Partrec.Code.evaln_sound ha⟩
    | true =>
      obtain ⟨z, a, ha⟩ := hf.2 (n/2)
      exact ⟨(Nat.unpair z).1, a, by
        rw [joined_eval, hb]
        exact Nat.Partrec.Code.evaln_sound ha⟩
  refine ⟨?_, ?_⟩
  · intro n z a ha
    exact hs n (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound ha)
  · intro n
    obtain ⟨m, a, ha⟩ := ht n
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp ha
    exact ⟨Nat.pair m t, a, by simpa [TableIndices.run, trial] using ht⟩

end TuringRigidity.IndexJoin

end OAI
