/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/IndexedOrder.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TableIndices

/-!
# Indexed Order
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IndexedOrder
open Encodable CommonIdeal UniformOracle TableIndices

/-- Every recorded value and trial bound is a successful finite computation of the indexed
oracle. -/
def Reads (Y : Oracle) (e : Nat.Partrec.Code) (L : List (ℕ × ℕ)) : Prop :=
  ∀ j : Fin L.length, TableIndices.run Y e j.val (L[j].2) = some (L[j].1)

/-- Extract the output values from a finite list of value-and-trial records. -/
def values (L : List (ℕ × ℕ)) : List ℕ := L.map Prod.fst

theorem reads_values {Y A : Oracle} {e : Nat.Partrec.Code}
    (he : Represents Y e A) (L : List (ℕ × ℕ)) (hL : Reads Y e L) :
    values L = oraclePrefix (fun k => bit (A k)) L.length := by
  apply List.ext_getElem
  · simp [values, oraclePrefix]
  · intro j hj hj'
    have hjL : j < L.length := by simpa [values] using hj
    have hh := he.1 j (L[j].2) (L[j].1) (Option.mem_def.mpr (hL ⟨j, by simpa [values] using hj⟩))
    simpa [values, oraclePrefix] using hh

theorem exists_reads {Y A : Oracle} {e : Nat.Partrec.Code}
    (he : Represents Y e A) (m : ℕ) :
    ∃ L : List (ℕ × ℕ), L.length = m ∧ Reads Y e L := by
  have hh : ∀ j, ∃ z, TableIndices.run Y e j z = some (bit (A j)) := by
    intro j
    obtain ⟨z, a, ha⟩ := he.2 j
    exact ⟨z, by rw [← he.1 j z a ha]; exact Option.mem_def.mp ha⟩
  choose z hz using hh
  let L := (List.range m).map (fun j => (bit (A j), z j))
  refine ⟨L, by simp [L], ?_⟩
  intro j
  simpa [L] using hz j.val

/-- A bounded computation certificate using a finite table certified by the source oracle
program. -/
def Certificate (Y : Oracle) (e d : Nat.Partrec.Code) (n a z : ℕ) : Prop :=
  let L := (decode (α := List (ℕ × ℕ)) (Nat.unpair z).1).getD []
  Reads Y e L ∧ d.evaln (Nat.unpair z).2 (Nat.pair (encode (values L)) n) = some a

theorem certificate_iff_run {Y A : Oracle} {e : Nat.Partrec.Code}
    (he : Represents Y e A) (d : Nat.Partrec.Code) (n a : ℕ) :
    (∃ z, Certificate Y e d n a z) ↔ ∃ z, TableIndices.run A d n z = some a := by
  constructor
  · rintro ⟨z, hL, hd⟩
    let L := (decode (α := List (ℕ × ℕ)) (Nat.unpair z).1).getD []
    refine ⟨Nat.pair L.length (Nat.unpair z).2, ?_⟩
    have hv := reads_values he L hL
    change d.evaln (Nat.unpair z).2 (Nat.pair (encode (values L)) n) = some a at hd
    simpa only [TableIndices.run, trial, Nat.unpair_pair, ← hv] using hd
  · rintro ⟨z, hz⟩
    obtain ⟨L, hlen, hL⟩ := exists_reads he (Nat.unpair z).1
    refine ⟨Nat.pair (encode L) (Nat.unpair z).2, ?_⟩
    simp only [Certificate, Nat.unpair_pair, encodek, Option.getD_some]
    refine ⟨hL, ?_⟩
    rw [reads_values he L hL, hlen]
    exact hz

/-- A reduction program has consistent certificates and computes every value of the target
oracle program. -/
def OrderWitness (Y : Oracle) (e₀ e₁ d : Nat.Partrec.Code) : Prop :=
  (∀ n a b z w, Certificate Y e₁ d n a z → Certificate Y e₁ d n b w → a = b) ∧
    ∀ n, ∃ a z w, Certificate Y e₁ d n a z ∧ TableIndices.run Y e₀ n w = some a

theorem order_iff_witness {Y A₀ A₁ : Oracle} {e₀ e₁ : Nat.Partrec.Code}
    (h₀ : Represents Y e₀ A₀) (h₁ : Represents Y e₁ A₁) :
    Reduces A₀ A₁ ↔ ∃ d : Nat.Partrec.Code, OrderWitness Y e₀ e₁ d := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := reduces_represents h
    refine ⟨d, ?_, ?_⟩
    · intro n a b z w hz hw
      obtain ⟨u, hu⟩ := (certificate_iff_run h₁ d n a).mp ⟨z, hz⟩
      obtain ⟨v, hv⟩ := (certificate_iff_run h₁ d n b).mp ⟨w, hw⟩
      exact (hd.1 n u a (Option.mem_def.mpr hu)).trans
        (hd.1 n v b (Option.mem_def.mpr hv)).symm
    · intro n
      obtain ⟨u, a, hu⟩ := hd.2 n
      obtain ⟨z, hz⟩ := (certificate_iff_run h₁ d n a).mpr ⟨u, Option.mem_def.mp hu⟩
      obtain ⟨w, b, hw⟩ := h₀.2 n
      have hab : b = a := (h₀.1 n w b hw).trans (hd.1 n u a hu).symm
      exact ⟨a, z, w, hz, by rw [← hab]; exact Option.mem_def.mp hw⟩
  · rintro ⟨d, hc, ht⟩
    apply represents_reduces (d := d)
    constructor
    · intro n u a hu
      obtain ⟨z, hz⟩ := (certificate_iff_run h₁ d n a).mpr ⟨u, Option.mem_def.mp hu⟩
      obtain ⟨b, w, v, hw, hv⟩ := ht n
      exact (hc n a b z w hz hw).trans (h₀.1 n v b (Option.mem_def.mpr hv))
    · intro n
      obtain ⟨a, z, w, hz, _⟩ := ht n
      obtain ⟨u, hu⟩ := (certificate_iff_run h₁ d n a).mp ⟨z, hz⟩
      exact ⟨u, a, Option.mem_def.mpr hu⟩

end TuringRigidity.IndexedOrder

end OAI
