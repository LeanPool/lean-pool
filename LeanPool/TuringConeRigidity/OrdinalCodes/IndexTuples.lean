/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/IndexTuples.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.IndexPresentation

/-!
# Index Tuples
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IndexTuples
open Encodable IndexPresentation IndexMatrix TableIndices

/-- Read the indexed component from a nested natural-number tuple code. -/
def entry : ℕ → ℕ → ℕ
  | 0, t => (Nat.unpair t).1
  | i+1, t => entry i (Nat.unpair t).2

theorem entry_primrec (i : ℕ) : Primrec (entry i) := by
  induction i with
  | zero => exact Primrec.fst.comp Primrec.unpair
  | succ i ih => exact ih.comp (Primrec.snd.comp Primrec.unpair)

theorem tuple_surjective {n : ℕ} (v : Fin n → ℕ) : ∃ t, ∀ i, entry i.val t = v i := by
  induction n with
  | zero => exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (fun i => v i.succ)
    refine ⟨Nat.pair (v 0) t, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [entry]
    · simpa only [Fin.val_succ, entry, Nat.unpair_pair] using ht j

/-- The machine index for the zero program. -/
def zeroIndex : ℕ := encode Nat.Partrec.Code.zero

theorem zero_represents (Y : Oracle) : Represents Y (machine zeroIndex) (fun _ => false) := by
  simp only [zeroIndex, machine_encode]
  constructor
  · intro n z a ha
    have h := Nat.Partrec.Code.evaln_sound ha
    change a ∈ Part.some 0 at h
    exact Part.mem_some_iff.mp h
  · intro n
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp
      (show 0 ∈ Nat.Partrec.Code.zero.eval (Nat.pair (encode ([] : List ℕ)) n) from Part.mem_some 0)
    refine ⟨Nat.pair 0 t, 0, ?_⟩
    simpa [TableIndices.run, UniformOracle.trial, UniformOracle.oraclePrefix,
      PrefixComputability.oraclePrefix] using ht

theorem zero_dom (Y : Oracle) : Dom Y zeroIndex :=
  (valid_iff_represents _ _).mpr ⟨_, zero_represents Y⟩

theorem zero_value (Y : Oracle) : value Y zeroIndex = ⊥ := value_eq (zero_represents Y)

/-- The machine index for the join of the first `n` entries of an index tuple. -/
noncomputable def supIndex : ℕ → ℕ → ℕ
  | 0, _ => zeroIndex
  | n+1, t => joinIndex ((Nat.unpair t).1) (supIndex n (Nat.unpair t).2)

theorem supIndex_primrec (n : ℕ) : Primrec (supIndex n) := by
  induction n with
  | zero => exact Primrec.const _
  | succ n ih =>
    exact joinIndex_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (ih.comp (Primrec.snd.comp Primrec.unpair))

theorem sup_dom {Y : Oracle} {n t : ℕ} (h : ∀ i : Fin n, Dom Y (entry i.val t)) :
    Dom Y (supIndex n t) := by
  induction n generalizing t with
  | zero => exact zero_dom Y
  | succ n ih => exact join_dom (h 0) (ih (fun i => h i.succ))

theorem sup_value {Y : Oracle} {n t : ℕ} (h : ∀ i : Fin n, Dom Y (entry i.val t)) :
    value Y (supIndex n t) = Finset.univ.sup (fun i : Fin n => value Y (entry i.val t)) := by
  induction n generalizing t with
  | zero => simp [supIndex, zero_value]
  | succ n ih =>
    have h0 : Dom Y ((Nat.unpair t).1) := h 0
    rw [supIndex, join_value h0 (sup_dom (fun i : Fin n => h i.succ)),
      ih (fun i : Fin n => h i.succ)]
    apply le_antisymm
    · apply sup_le
      · exact Finset.le_sup (f := fun i : Fin (n+1) => value Y (entry i.val t)) (Finset.mem_univ 0)
      · apply Finset.sup_le
        intro i _
        exact Finset.le_sup (f := fun j : Fin (n+1) => value Y (entry j.val t))
          (Finset.mem_univ i.succ)
    · apply Finset.sup_le
      intro i _
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_sup_left
      · exact (Finset.le_sup (f := fun j : Fin n => value Y (entry j.val (Nat.unpair t).2))
          (Finset.mem_univ j)).trans le_sup_right

end TuringRigidity.IndexTuples

end OAI
