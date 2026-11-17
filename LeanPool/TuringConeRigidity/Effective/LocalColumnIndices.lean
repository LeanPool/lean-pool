/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalColumnIndices.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalColumnCertificates

/-!
# Local Column Indices
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalColumnIndices
open Encodable UniformOracle EncodedForcing ArithmeticHierarchy

def specialized (d : Nat.Partrec.Code) (k : ℕ) : Nat.Partrec.Code :=
  (Nat.Partrec.Code.comp d (.pair (.comp .left .right) (.pair .left (.comp .right .right)))).curry k

theorem specialized_eval (d : Nat.Partrec.Code) (k L n : ℕ) :
    (specialized d k).eval (Nat.pair L n) = d.eval (Nat.pair L (Nat.pair k n)) := by
  simp only [specialized, Nat.Partrec.Code.eval_curry, Nat.Partrec.Code.eval, Seq.seq,
    PFun.coe_val, Nat.unpair_pair, Part.map_eq_map, Part.map_some, Part.bind_some, Part.bind_map]
  change (((Part.some (Nat.pair L n)).bind
    (fun input => Part.some (Nat.unpair input).1)).bind
    (fun left => Part.map (Nat.pair left) (Part.map (Nat.pair k)
      ((Part.some (Nat.pair L n)).bind (fun input => Part.some (Nat.unpair input).2))))).bind
    (fun input => d.eval input) = _
  simp

theorem specialized_primrec (d : Nat.Partrec.Code) : Primrec (fun k => encode (specialized d k)) :=
  Primrec.encode.comp (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const _) Primrec.id)

theorem uniform_indices {B A : Oracle} (h : Reduces A B) :
    ∃ index : ℕ → ℕ, Primrec index ∧
      ∀ k, TableIndices.Represents B (IndexMatrix.machine (index k)) (columns A k) := by
  obtain ⟨d,hd⟩ := TableIndices.reduces_represents h
  refine ⟨fun k => encode (specialized d k),specialized_primrec d,fun k => ?_⟩
  simp only [IndexMatrix.machine_encode]
  constructor
  · intro n z a hz
    have he := Nat.Partrec.Code.evaln_sound hz
    change a ∈ (specialized d k).eval
      (Nat.pair (encode (oraclePrefix (fun q => CommonIdeal.bit (B q)) (Nat.unpair z).1)) n) at he
    rw [specialized_eval] at he
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp he
    exact hd.1 (Nat.pair k n) (Nat.pair (Nat.unpair z).1 t) a (by
      simpa only [TableIndices.run,trial,Nat.unpair_pair] using ht)
  · intro n
    obtain ⟨z,a,hz⟩ := hd.2 (Nat.pair k n)
    have he := Nat.Partrec.Code.evaln_sound hz
    change a ∈ d.eval
      (Nat.pair (encode (oraclePrefix (fun q => CommonIdeal.bit (B q)) (Nat.unpair z).1))
        (Nat.pair k n)) at he
    rw [← specialized_eval d k] at he
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp he
    exact ⟨Nat.pair (Nat.unpair z).1 t,a,by
      simpa only [TableIndices.run,trial,Nat.unpair_pair] using ht⟩

theorem prefix_recursive_in {O : Set (ℕ →. ℕ)} (g : ℕ → ℕ)
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun m => Part.some (encode (oraclePrefix g m))) := by
  have hy := (total_primrec (O := O)) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := (total_primrec (O := O)) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp ((total_primrec (O := O)) (appendEncoded_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hg hy))
  have hp := Nat.RecursiveIn.prec ((total_primrec (O := O)) (Primrec.const (encode ([] : List
    ℕ)))) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair ((total_primrec (O := O)) (Primrec.const 0)) ((total_primrec (O := O)) Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [appendEncoded,oraclePrefix,List.range_succ]

theorem selected_prefixes {B A X : Oracle} (h : Reduces A B) (select : ℕ → ℕ)
    (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n))) :
    ∃ codes : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (codes n)) ∧
      ∀ n, LocalColumnCertificates.Presents B (fun k => columns A (select k)) (codes n) n := by
  obtain ⟨index,hi,hindex⟩ := uniform_indices h
  let g := fun k => index (select k)
  have hg : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (g n)) := by
    exact total_comp (f := index) (g := select) (total_primrec hi) hs
  refine ⟨fun n => encode (oraclePrefix g n),prefix_recursive_in g hg,?_⟩
  intro n k hk
  have he : item (encode (oraclePrefix g n)) k = g k := by
    simp [item,oraclePrefix,List.getD_eq_getElem?_getD,hk]
  rw [he]
  exact hindex (select k)

end TuringRigidity.LocalColumnIndices

end OAI
