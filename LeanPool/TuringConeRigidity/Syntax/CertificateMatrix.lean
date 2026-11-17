/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/CertificateMatrix.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.IndexedOrder
public import LeanPool.TuringConeRigidity.Syntax.BoundedRecursive

/-!
# Certificate Matrix
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CertificateMatrix
open Encodable UniformOracle TableIndices IndexMatrix IndexedOrder BoundedRecursive

def table (c : ℕ) : List (ℕ × ℕ) := (decode c).getD []

theorem table_primrec : Primrec table := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

def entry (c j : ℕ) : ℕ × ℕ := (table c).getD j (0, 0)

theorem entry_primrec : Primrec₂ entry :=
  (Primrec.list_getD (0, 0)).comp (table_primrec.comp Primrec.fst) Primrec.snd

def entryCheck (Y : Oracle) (v : ℕ) : ℕ :=
  let e := (Nat.unpair (Nat.unpair v).1).1
  let c := (Nat.unpair (Nat.unpair v).1).2
  let j := (Nat.unpair v).2
  if TableIndices.run Y (machine e) j (entry c j).2 = some (entry c j).1 then 1 else 0

theorem entryCheck_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some (entryCheck Y v)) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  let e := fst.comp fst
  let c := snd.comp fst
  let j := snd
  let en := entry_primrec.comp c j
  have hv := total_comp (run_uniform_recursive Y)
    (total_pair (total_primrec e) (total_pair (total_primrec j)
      (total_primrec (Primrec.snd.comp en))))
  have hw := total_primrec (O := O) (Primrec.encode.comp (Primrec.option_some.comp
    (Primrec.fst.comp en)))
  have heq := total_primrec (O := O)
    (Primrec.ite (Primrec.eq.comp fst snd) (Primrec.const 1) (Primrec.const 0))
  exact (total_comp heq (total_pair hv hw)).of_eq (fun v => by
    simp only [entryCheck, Nat.unpair_pair, Encodable.encode_injective.eq_iff])

def readsCheck (Y : Oracle) (v : ℕ) : ℕ :=
  allBelow (entryCheck Y) v (table (Nat.unpair v).2).length

theorem readsCheck_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some (readsCheck Y v)) := by
  have ha := total_pair (O := {oracleFunction Y}) (total_primrec Primrec.id)
    (total_primrec (Primrec.list_length.comp (table_primrec.comp (Primrec.snd.comp
      Primrec.unpair))))
  exact (total_comp (allBelow_recursive (entryCheck_recursive Y)) ha).of_eq (fun v => by
    simp [readsCheck])

theorem readsCheck_spec (Y : Oracle) (e c : ℕ) :
    readsCheck Y (Nat.pair e c) = 1 ↔ Reads Y (machine e) (table c) := by
  rw [readsCheck, Nat.unpair_pair, allBelow_spec]
  simp only [entryCheck, Nat.unpair_pair, ite_eq_left_iff, Nat.zero_ne_one, imp_false, not_not]
  constructor
  · intro h j
    have hh := h j.val j.isLt
    simpa [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt] using hh
  · intro h j hj
    have hh := h ⟨j, hj⟩
    simpa [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hh

instance (Y : Oracle) (e : Nat.Partrec.Code) (L : List (ℕ × ℕ)) : Decidable (Reads Y e L) := by
  unfold Reads
  infer_instance

instance (Y : Oracle) (e d : Nat.Partrec.Code) (n a z : ℕ) : Decidable (Certificate Y e d n a z)
  := by
  unfold Certificate
  infer_instance

theorem certificate_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (if Certificate Y (machine (Nat.unpair v).1) (machine (Nat.unpair (Nat.unpair v).2).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).2 then 1 else 0)) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  let e := fst
  let d := fst.comp snd
  let n := fst.comp (snd.comp snd)
  let a := fst.comp (snd.comp (snd.comp snd))
  let z := snd.comp (snd.comp (snd.comp snd))
  let L := table_primrec.comp (fst.comp z)
  let vs := Primrec.list_map L (Primrec.fst.comp Primrec.snd).to₂
  have hread := total_comp (readsCheck_recursive Y)
    (total_pair (total_primrec e) (total_primrec (fst.comp z)))
  let ve := Nat.Partrec.Code.primrec_evaln.comp
    (((snd.comp z).pair (machine_primrec.comp d)).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp vs) n))
  have heval := total_primrec (O := O)
    (Primrec.ite (Primrec.eq.comp ve (Primrec.option_some.comp a)) (Primrec.const 1)
      (Primrec.const 0))
  have hand := total_primrec (O := O)
    (Primrec.ite ((Primrec.eq.comp fst (Primrec.const 1)).and (Primrec.eq.comp snd (Primrec.const
      1)))
      (Primrec.const 1) (Primrec.const 0))
  exact (total_comp hand (total_pair hread heval)).of_eq (fun v => by
    simp only [Nat.unpair_pair, readsCheck_spec, Certificate, values, table]
    split_ifs <;> simp_all)

end TuringRigidity.CertificateMatrix

end OAI
