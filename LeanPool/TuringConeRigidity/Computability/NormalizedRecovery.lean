/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/NormalizedRecovery.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.StageNormalization

/-!
# Normalized Recovery
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NormalizedRecovery
open EncodedForcing Encodable UniformOracle Introreducible StageNormalization

def trial (B : Oracle) (n c : ℕ) : Option ℕ :=
  if B (Nat.pair (Nat.unpair n).1 c) = true ∧ (Nat.unpair n).2 < codeLength c
    then some (codeBit (Nat.unpair n).2 c) else none

theorem trial_recursive (B : Oracle) :
    Nat.RecursiveIn {oracleFunction B} (fun v => Part.some (encode (trial B (Nat.unpair v).1
      (Nat.unpair v).2))) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hq : Nat.RecursiveIn {oracleFunction B} (oracleFunction B) := .oracle _ (Set.mem_singleton _)
  have hb := total_comp hq (total_primrec (Primrec₂.natPair.comp (f.comp f) r))
  let n := r.comp (f.comp f)
  let c := r.comp f
  have hpost := Primrec.encode.comp (Primrec.ite
    ((Primrec.eq.comp r (Primrec.const 1)).and (Primrec.nat_lt.comp n (codeLength_primrec.comp c)))
    (Primrec.option_some.comp (codeBit_primrec.comp n c)) (Primrec.const none))
  exact (total_comp (total_primrec hpost) (total_pair (total_primrec Primrec.id) hb)).of_eq
    (fun v => by cases h : B (Nat.pair (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair v).2) <;>
      simp [trial,h])

theorem normalized_inverse (A : Oracle) : Reduces A (normalized A) := by
  apply RecursiveIn.iff_nat.mpr
  change Nat.RecursiveIn {oracleFunction (normalized A)} (fun n => Part.some (bit A n))
  apply total_search (trial_recursive (normalized A)) (bit A)
  · intro n c a ha
    simp only [trial] at ha
    split at ha
    next h =>
      have he : prefixCode (columns A (Nat.unpair n).1) (codeLength c) = c := by
        simpa [normalized,prefixSet] using h.1
      have ha' : a = codeBit (Nat.unpair n).2 c := (Option.mem_some_iff.mp ha).symm
      rw [ha',← he,codeBit_prefix _ _ _ h.2]
      simp [bit,columns,Nat.pair_unpair]
    next h => simp at ha
  · intro n
    let c := prefixCode (columns A (Nat.unpair n).1) ((Nat.unpair n).2+1)
    refine ⟨c,codeBit (Nat.unpair n).2 c,?_⟩
    simp [trial,normalized,c]

end TuringRigidity.NormalizedRecovery

end OAI
