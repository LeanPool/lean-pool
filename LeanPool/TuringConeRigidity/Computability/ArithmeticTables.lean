/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticTables.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.UniformArithmetic
public import LeanPool.TuringConeRigidity.OrdinalCodes.IndexMatrix

/-!
# Arithmetic Tables
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable UniformOracle CommonIdeal IndexMatrix

/-- A family of oracles indexed by oracle environments and natural numbers. -/
abbrev OracleFamily := Oracles → ℕ → Oracle
/-- Arithmetic definability of all bits of the indexed oracle family. -/
abbrev ArithmeticOracle (B : OracleFamily) :=
  Arith (fun O v => B O (left v) (right v) = true)

theorem query_at {B : OracleFamily} (hB : ArithmeticOracle B)
    {c n : ℕ → ℕ} (hc : Primrec c) (hn : Primrec n) :
    Arith (fun O v => B O (c v) (n v) = true) :=
  (hB.comp _ (Primrec₂.natPair.comp hc hn)).congr
    (fun _ _ => by simp only [left,right,Nat.unpair_pair])

theorem bit_equal {B : OracleFamily} (hB : ArithmeticOracle B)
    {c n a : ℕ → ℕ} (hc : Primrec c) (hn : Primrec n) (ha : Primrec a) :
    Arith (fun O v => a v = bit (B O (c v) (n v))) := by
  have h := query_at hB hc hn
  exact ((h.and (equal ha (Primrec.const 1))).or
    (h.neg.and (equal ha (Primrec.const 0)))).congr (fun O v => by
      cases B O (c v) (n v) <;> simp [bit])

/-- Decode a finite table, using the empty table when decoding fails. -/
def table (c : ℕ) : List ℕ := (decode c).getD []
/-- Read a table entry, using zero outside the decoded table. -/
def item (c k : ℕ) : ℕ := (table c).getD k 0

theorem table_primrec : Primrec table :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])
theorem item_primrec : Primrec₂ item :=
  (Primrec.list_getD 0).comp (table_primrec.comp Primrec.fst) Primrec.snd

/-- The coded table is exactly the length-`m` Boolean prefix of the oracle. -/
def Prefix (B : Oracle) (m c : ℕ) : Prop :=
  (table c).length = m ∧ ∀ k, k < m → item c k = bit (B k)

theorem prefix_iff (B : Oracle) (m c : ℕ) :
    Prefix B m c ↔ table c = oraclePrefix (fun k => bit (B k)) m := by
  constructor
  · rintro ⟨hlen,he⟩
    apply List.ext_getElem
    · simpa [oraclePrefix, PrefixComputability.oraclePrefix] using hlen
    · intro k hk hk'
      have hkm : k < m := by simpa [oraclePrefix, PrefixComputability.oraclePrefix] using hk'
      have hh := he k hkm
      simpa [item,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,
        oraclePrefix, PrefixComputability.oraclePrefix] using hh
  · intro he
    constructor
    · simp [he,oraclePrefix, PrefixComputability.oraclePrefix]
    · intro k hk
      simp [item,he,oraclePrefix,
        PrefixComputability.oraclePrefix,List.getD_eq_getElem?_getD,List.getElem?_range hk]

theorem prefix_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c m l : ℕ → ℕ} (hc : Primrec c) (hm : Primrec m) (hl : Primrec l) :
    Arith (fun O v => Prefix (B O (c v)) (m v) (l v)) := by
  have hb := bit_equal hB (hc.comp left_primrec) right_primrec
    (item_primrec.comp (hl.comp left_primrec) right_primrec)
  have ht := ((less right_primrec (hm.comp left_primrec)).imp hb).all
  exact ((equal (Primrec.list_length.comp (table_primrec.comp hl)) hm).and ht).congr
    (fun _ _ => by simp only [Prefix,left,right,Nat.unpair_pair])

/-- A bounded execution of the indexed machine on the coded table and input returns `a`. -/
def trialTest (e n m t a : ℕ) : Prop :=
  (machine e).evaln t (Nat.pair (encode (table m)) n) = some a

theorem trialTest_arith {e n m t a : ℕ → ℕ}
    (he : Primrec e) (hn : Primrec n) (hm : Primrec m) (ht : Primrec t) (ha : Primrec a) :
    Arith (fun _ v => trialTest (e v) (n v) (m v) (t v) (a v)) := by
  apply Arith.pure
  exact Primrec.eq.comp
    (Nat.Partrec.Code.primrec_evaln.comp
      ((ht.pair (machine_primrec.comp he)).pair
        (Primrec₂.natPair.comp (Primrec.encode.comp (table_primrec.comp hm)) hn)))
    (Primrec.option_some.comp ha)

theorem run_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c e n z a : ℕ → ℕ} (hc : Primrec c) (he : Primrec e) (hn : Primrec n)
    (hz : Primrec z) (ha : Primrec a) :
    Arith (fun O v => TableIndices.run (B O (c v)) (machine (e v)) (n v) (z v) = some (a v)) := by
  have hp := prefix_arith hB (hc.comp left_primrec)
    ((left_primrec.comp hz).comp left_primrec) right_primrec
  have ht := trialTest_arith (he.comp left_primrec) (hn.comp left_primrec)
    right_primrec ((right_primrec.comp hz).comp left_primrec) (ha.comp left_primrec)
  apply (hp.and ht).ex.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨l,hp,ht⟩
    rw [prefix_iff] at hp
    simpa [trialTest,TableIndices.run,trial,hp] using ht
  · intro ht
    let L := oraclePrefix (fun k => bit (B O (c v) k)) (Nat.unpair (z v)).1
    refine ⟨encode L,?_,?_⟩
    · rw [prefix_iff]
      simp [table,L]
    · simpa [trialTest,table,L,TableIndices.run,trial] using ht

end TuringRigidity.UniformArithmetic

end OAI
