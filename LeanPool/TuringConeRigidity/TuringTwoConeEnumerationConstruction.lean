/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeEnumerationConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeRelativeUnary
public import LeanPool.TuringConeRigidity.TuringConeEnumeration
public import LeanPool.TuringConeRigidity.SetModels.EnumerationConstruction

/-!
# Relative enumeration of a presentation joined with its source base

The k-th output is deg(A) join deg(H_k). This avoids choosing a subsequence
of precisely those columns lying above deg(A). Every point of that cone in
the presented ideal still occurs. If A' is reducible to H, both coding
relations have all parameters between deg(A) and deg(H').
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeEnumeration

open EncodedForcing OracleJump ArithmeticHierarchy
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding
open ConeRelativeCoding

noncomputable section

/-- One relative code records the whole joined sequence, with one jump bound. -/
theorem enumeration_exists (A H : Oracle) (hAH : Reduces (jump A) H) :
    ∃ c : ConeEnumeration.Enumeration (degree A),
      (∀ k, c.output k = degree A ⊔ degree (columns H k)) ∧
      RelationAbove c.successor (degree A) ∧ RelationAbove c.payload (degree A) ∧
      RelationBelow c.successor (degree (jump H)) ∧
      RelationBelow c.payload (degree (jump H)) := by
  obtain ⟨C, _, hlow, hind⟩ := CohenColumns.uniform_low_independent A
  let N := pad A C
  let B := join A C
  have hNB : Reduces N B := pad_reduces A C
  have hNlow : Reduces (jump N) (jump A) := by
    change degree (jump N) ≤ degree (jump A)
    rw [← hlow]
    exact jump_mono hNB
  have hNH : Reduces N H := (reduces_jump N).trans (hNlow.trans hAH)
  have hAH₀ : Reduces A H := (reduces_jump A).trans hAH
  have hinj : Function.Injective (fun k => degree (columns N k)) := by
    intro i j he
    have hh := (hind (degree A) (degree A) le_rfl le_rfl i {j}).mp (by
      simpa only [N, pad_column, join_degree, Finset.sup_singleton] using he.le)
    simpa only [Finset.mem_singleton] using hh.2
  have hrows : Reduces (FixedArithmetic.rows N) B :=
    (FixedArithmetic.rows_reduces N).trans hNB
  have hbase : ∀ i : Fin 2, ∀ j,
      degree A ≤ degree (columns (FixedArithmetic.rows N) (Nat.pair i.val j)) := by
    intro i j
    fin_cases i
    · simpa only [FixedArithmetic.row_zero] using base_le_pad_column A C j
    · simpa only [FixedArithmetic.row_one] using base_le_pad_column A C (j + 1)
  obtain ⟨S, haS, hS, hs⟩ := relation_sequence A (FixedArithmetic.rows N) B
    (reduces_join_left A C) hrows 2 hbase
  have hS' : RelationBelow S (degree (jump H)) :=
    (hlow ▸ hS).mono (hAH.trans (reduces_jump H))
  have hspec (x y : Degree) : ConeCoding.Holds (degree A) S (two x y) ↔
      ∃ k, x = degree (columns N k) ∧ y = degree (columns N (k + 1)) := by
    rw [hs]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [two] using (hk 0).symm,
        by simpa [two] using (hk 1).symm⟩
    · rintro ⟨k, rfl, rfl⟩
      refine ⟨k, fun i => ?_⟩
      fin_cases i <;> simp [two]
  let V := pad A H
  have hVH : Reduces V H :=
    (pad_reduces A H).trans (join_reduces hAH₀ (reduces_refl H))
  have hRH : Reduces (EnumerationConstruction.rows N V) H :=
    (EnumerationConstruction.rows_reduces N V).trans (join_reduces hNH hVH)
  have hbaseP : ∀ i : Fin 2, ∀ j,
      degree A ≤ degree (columns (EnumerationConstruction.rows N V) (Nat.pair i.val j)) := by
    intro i j
    fin_cases i
    · simpa only [EnumerationConstruction.row_zero] using base_le_pad_column A C j
    · simpa only [EnumerationConstruction.row_one] using base_le_pad_column A H j
  obtain ⟨P, haP, hP, hp⟩ := relation_sequence A (EnumerationConstruction.rows N V) H
    hAH₀ hRH 2 hbaseP
  have hpspec (x y : Degree) : ConeCoding.Holds (degree A) P (two x y) ↔
      ∃ k, x = degree (columns N k) ∧ y = degree A ⊔ degree (columns H k) := by
    rw [hp]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [two] using (hk 0).symm,
        by simpa [two, V, pad_column, join_degree] using (hk 1).symm⟩
    · rintro ⟨k, rfl, rfl⟩
      refine ⟨k, fun i => ?_⟩
      fin_cases i <;> simp [two, V, pad_column, join_degree]
  let c : ConeEnumeration.Enumeration (degree A) :=
    ⟨fun k => degree (columns N k), hinj,
      fun k => degree A ⊔ degree (columns H k), S, P, hspec, hpspec⟩
  exact ⟨c, fun _ => rfl, haS, haP, hS', hP⟩

end
end OAI.TuringRigidity.TwoConeEnumeration
