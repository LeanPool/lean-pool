/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenHalting.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.EncodedForcing
public import LeanPool.TuringConeRigidity.Computability.ArithmeticAtoms
public import LeanPool.TuringConeRigidity.Computability.OracleJump

/-!
# Cohen Halting
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenHalting
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing IndexMatrix

/-- Decode a finite table of natural numbers, using the empty table for an invalid code. -/
def table (c : ℕ) : List ℕ := (decode c).getD []
theorem table_primrec : Primrec table := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- A computation table agrees with the fixed oracle and the finite Cohen word at every query. -/
def Agrees (Y : Oracle) (p : List Bool) (L : List ℕ) : Prop :=
  ∀ i < L.length, if i.bodd then i/2 < p.length ∧ L.getD i 0 = bit (p.getD (i/2) false)
    else L.getD i 0 = bit (Y (i/2))

theorem agrees_recursive (Y : Oracle) : RecursivePred Y (fun v =>
    Agrees Y (word (Nat.unpair v).1) (table (Nat.unpair v).2)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := word_primrec.comp (f.comp f)
  let L := table_primrec.comp (r.comp f)
  let i := r
  let half := Primrec.nat_div.comp i (Primrec.const 2)
  let val := (Primrec.list_getD 0).comp L i
  have ho := recursive_primrecPred Y (Primrec.eq.comp (Primrec.nat_bodd.comp i) (Primrec.const
    true))
  have hb := recursive_primrecPred Y (Primrec.nat_lt.comp half (Primrec.list_length.comp p))
  have hp := recursive_primrecPred Y (Primrec.eq.comp val
    (bit_primrec.comp ((Primrec.list_getD false).comp p half)))
  have hquery : Nat.RecursiveIn {oracleFunction Y} (oracleFunction Y) := .oracle _
    (Set.mem_singleton _)
  have hq : Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some (bit (Y ((Nat.unpair v).2/2))))
    := by
    exact total_comp (f := fun input => bit (Y input)) hquery (total_primrec half)
  have hv := total_pair (total_primrec val) hq
  have heq : Primrec (fun v : ℕ => if (Nat.unpair v).1 = (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp f r) (Primrec.const 1) (Primrec.const 0)
  have hy : RecursivePred Y (fun v => (table (Nat.unpair (Nat.unpair v).1).2).getD (Nat.unpair
    v).2 0 =
      bit (Y ((Nat.unpair v).2/2))) := by
    exact (total_comp (total_primrec heq) hv).of_eq (fun v => by simp [bit])
  have hi := Form.or (n := 0) (s := true) (recursive_and ho (recursive_and hb hp))
    (recursive_and (recursive_not ho) hy)
  apply Form.congr (n := 0) (s := true) (recursive_bounded_all hi (Primrec.list_length.comp
    (table_primrec.comp r)))
  intro v
  simp only [Agrees,Nat.unpair_pair]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  cases i.bodd <;> simp

/-- A coded, bounded halting computation with a table consistent with the oracle and finite
word. -/
def Certificate (Y : Oracle) (v : ℕ) : Prop :=
  Agrees Y (word (Nat.unpair (Nat.unpair v).1).2) (table (Nat.unpair (Nat.unpair v).2).1) ∧
    ((machine (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1).evaln
      (Nat.unpair (Nat.unpair v).2).2
      (Nat.pair (encode (table (Nat.unpair (Nat.unpair v).2).1))
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).2)).isSome = true

theorem certificate_recursive (Y : Oracle) : RecursivePred Y (Certificate Y) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have ha := recursive_comp (agrees_recursive Y) (Primrec₂.natPair.comp (r.comp f) (f.comp r))
  have he := Nat.Partrec.Code.primrec_evaln.comp
    (((r.comp r).pair (machine_primrec.comp (f.comp (f.comp f)))).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp (table_primrec.comp (f.comp r))) (r.comp (f.comp
        f))))
  unfold Certificate
  simpa only [Nat.unpair_pair] using recursive_and ha (recursive_primrecPred Y
    (Primrec.eq.comp (Primrec.option_isSome.comp he) (Primrec.const true)))

/-- A finite word admits a halting computation certificate for the specified machine input. -/
def OpenHalts (Y : Oracle) (x p : ℕ) : Prop := ∃ z, Certificate Y (Nat.pair (Nat.pair x p) z)

theorem openHalts_sigma (Y : Oracle) : Sigma Y 1 (fun v => OpenHalts Y (Nat.unpair v).1
  (Nat.unpair v).2) := by
  simpa only [OpenHalts,Nat.pair_unpair] using exists_form (n := 0) (certificate_recursive Y)

/-- The oracle extends the finite binary word. -/
def Prefix (G : Oracle) (p : List Bool) : Prop := ∀ i < p.length, G i = p.getD i false

/-- The initial word of length `m` of an oracle. -/
def initial (G : Oracle) (m : ℕ) : List Bool := (List.range m).map G

@[simp] theorem initial_length (G : Oracle) (m : ℕ) : (initial G m).length = m := by simp [initial]

theorem initial_getD (G : Oracle) {m i : ℕ} (hi : i < m) : (initial G m).getD i false = G i := by
  simp [initial,List.getD_eq_getElem?_getD,List.getElem?_range hi]

theorem initial_prefix (G : Oracle) (m : ℕ) : Prefix G (initial G m) := by
  intro i hi
  exact (initial_getD G (by simpa using hi)).symm

theorem prefix_initial {G : Oracle} {p : List Bool} (hp : Prefix G p) : p = initial G p.length := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h := hp i hi
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi, initial, hi] using h.symm

theorem initial_mono (G : Oracle) {m n : ℕ} (h : m ≤ n) : initial G m <+: initial G n := by
  exact (List.prefix_iff_eq_take.mpr (by simp [initial,← List.map_take,List.take_range,min_eq_left
    h]))

theorem agrees_table {Y G : Oracle} {p : List Bool} {L : List ℕ}
    (hp : Prefix G p) (h : Agrees Y p L) : L = oraclePrefix (fun i => bit (join Y G i)) L.length
      := by
  apply List.ext_getElem
  · simp [oraclePrefix, PrefixComputability.oraclePrefix]
  · intro i hi hj
    have hh := h i hi
    have he : L.getD i 0 = bit (join Y G i) := by
      cases hb : i.bodd with
      | false => simpa [hb,join] using hh
      | true =>
        simp only [hb,↓reduceIte] at hh
        simpa [join,hb,hp (i/2) hh.1] using hh.2
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,oraclePrefix,
      PrefixComputability.oraclePrefix,hi] using he

theorem openHalts_sound {Y G : Oracle} {x : ℕ} {p : List Bool}
    (hp : Prefix G p) (h : OpenHalts Y x (encode p)) : Halts (join Y G) (Nat.unpair x).1
      (Nat.unpair x).2 := by
  obtain ⟨z,ha,hh⟩ := h
  simp only [Nat.unpair_pair,word,encodek,Option.getD_some] at ha hh
  obtain ⟨a,ha'⟩ := Option.isSome_iff_exists.mp hh
  refine ⟨Nat.pair (table (Nat.unpair z).1).length (Nat.unpair z).2,a,?_⟩
  have ht := agrees_table hp ha
  simpa only [TableIndices.run,trial,Nat.unpair_pair,← ht] using Option.mem_def.mpr ha'

theorem openHalts_complete {Y G : Oracle} {x : ℕ}
    (h : Halts (join Y G) (Nat.unpair x).1 (Nat.unpair x).2) :
    ∃ m, OpenHalts Y x (encode (initial G m)) := by
  obtain ⟨z,a,ha⟩ := h
  let m := (Nat.unpair z).1
  let L := oraclePrefix (fun i => bit (join Y G i)) m
  refine ⟨m,Nat.pair (encode L) (Nat.unpair z).2,?_,?_⟩
  · simp only [Nat.unpair_pair,word,table,encodek,Option.getD_some]
    intro i hi
    have him : i < m := by simpa [L,oraclePrefix, PrefixComputability.oraclePrefix] using hi
    have hh : i/2 < m := (Nat.div_le_self i 2).trans_lt him
    have hv : L.getD i 0 = bit (join Y G i) := by
      simp [L,oraclePrefix,
        PrefixComputability.oraclePrefix,List.getD_eq_getElem?_getD,List.getElem?_range him]
    cases hb : i.bodd with
    | false => simpa only [hb,Bool.false_eq_true,↓reduceIte,join] using hv
    | true =>
      simp only [↓reduceIte]
      exact ⟨by simpa using hh, by rw [hv,join,ite_eq_left hb,initial_getD G hh]⟩
  · simp only [Nat.unpair_pair,table,encodek,Option.getD_some]
    exact Option.isSome_iff_exists.mpr ⟨a,ha⟩

theorem openHalts_mono {Y : Oracle} {x : ℕ} {p q : List Bool}
    (hpq : p <+: q) (h : OpenHalts Y x (encode p)) : OpenHalts Y x (encode q) := by
  obtain ⟨z,ha,hh⟩ := h
  refine ⟨z,?_,by simpa only [Nat.unpair_pair] using hh⟩
  simp only [Nat.unpair_pair,word,encodek,Option.getD_some] at ha ⊢
  intro i hi
  have hv := ha i hi
  cases hb : i.bodd with
  | false => simpa only [hb,Bool.false_eq_true,↓reduceIte] using hv
  | true =>
    simp only [hb,↓reduceIte] at hv ⊢
    exact ⟨hv.1.trans_le hpq.length_le,hv.2.trans (congrArg bit
      (CodingForcing.getD_of_prefix hpq hv.1).symm)⟩

end TuringRigidity.CohenHalting

end OAI
