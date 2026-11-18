/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/Joins.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.Degrees

/-!
# Joins
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

/-- The Turing join of two oracles, with the first in even positions and the second in odd
positions. -/
def join (A B : Oracle) (n : ℕ) : Bool := if n.bodd then B (n / 2) else A (n / 2)

private theorem total_comp {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (f (g n))) := by
  simpa using Nat.RecursiveIn.comp hf hg

private theorem total_pair {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
  simpa [Seq.seq] using Nat.RecursiveIn.pair hf hg

private theorem total_primrec {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Primrec f) : Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp hf.computableIn

@[simp] theorem join_even (A B : Oracle) (n : ℕ) : join A B (2*n) = A n := by
  simp [join, Nat.bodd_mul]

@[simp] theorem join_odd (A B : Oracle) (n : ℕ) : join A B (2*n+1) = B n := by
  simp [join, Nat.bodd_mul]
  congr 1
  omega

theorem reduces_join_left (A B : Oracle) : Reduces A (join A B) := by
  apply RecursiveIn.iff_nat.mpr
  have horacle : Nat.RecursiveIn {oracleFunction (join A B)} (oracleFunction (join A B)) :=
    .oracle _ (Set.mem_singleton _)
  have h := total_comp horacle (total_primrec (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
  change Nat.RecursiveIn {oracleFunction (join A B)} (fun n => Part.some (if A n then 1 else 0))
  simpa [oracleFunction] using h

theorem reduces_join_right (A B : Oracle) : Reduces B (join A B) := by
  apply RecursiveIn.iff_nat.mpr
  have horacle : Nat.RecursiveIn {oracleFunction (join A B)} (oracleFunction (join A B)) :=
    .oracle _ (Set.mem_singleton _)
  have h := total_comp horacle (total_primrec
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)))
  change Nat.RecursiveIn {oracleFunction (join A B)} (fun n => Part.some (if B n then 1 else 0))
  simpa [oracleFunction] using h

private def selectPair (k : ℕ) : ℕ :=
  if (Nat.unpair k).1.bodd then (Nat.unpair (Nat.unpair k).2).2
  else (Nat.unpair (Nat.unpair k).2).1

private theorem selectPair_primrec : Primrec selectPair := by
  apply (Primrec.cond (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).of_eq
  intro n
  cases hb : (Nat.unpair n).1.bodd <;> simp [selectPair, hb]

theorem join_reduces {A B C : Oracle} (hA : Reduces A C) (hB : Reduces B C) :
    Reduces (join A B) C := by
  apply RecursiveIn.iff_nat.mpr
  have hA' := RecursiveIn.iff_nat.mp hA
  have hB' := RecursiveIn.iff_nat.mp hB
  have hdiv : Nat.RecursiveIn {oracleFunction C} (fun n => Part.some (n / 2)) :=
    total_primrec (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  have hp := total_pair (total_primrec Primrec.id)
    (total_pair (total_comp hA' hdiv) (total_comp hB' hdiv))
  have h := total_comp (total_primrec selectPair_primrec) hp
  apply Nat.RecursiveIn.of_eq h
  intro n
  simp only [selectPair, Nat.unpair_pair, oracleFunction, join, id_eq]
  by_cases hb : n.bodd = true <;> simp [hb]

theorem join_reduces_iff (A B C : Oracle) :
    Reduces (join A B) C ↔ Reduces A C ∧ Reduces B C :=
  ⟨fun h => ⟨reduces_trans (reduces_join_left A B) h,
    reduces_trans (reduces_join_right A B) h⟩, fun h => join_reduces h.1 h.2⟩

theorem join_mono {A B C D : Oracle} (hA : Reduces A C) (hB : Reduces B D) :
    Reduces (join A B) (join C D) :=
  join_reduces (reduces_trans hA (reduces_join_left C D))
    (reduces_trans hB (reduces_join_right C D))

/-- The join operation on Turing degrees induced by interleaving oracle representatives. -/
def degreeJoin (a b : Degree) : Degree :=
  Quotient.liftOn₂ a b (fun A B => degree (join A B))
    (fun _ _ _ _ hA hB => (degree_eq_iff _ _).mpr
      ⟨join_mono hA.1 hB.1, join_mono hA.2 hB.2⟩)

@[simp] theorem degree_join (A B : Oracle) :
    degreeJoin (degree A) (degree B) = degree (join A B) := rfl

instance : SemilatticeSup Degree where
  sup := degreeJoin
  le_sup_left a b := by
    obtain ⟨A, rfl⟩ := degree_surjective a
    obtain ⟨B, rfl⟩ := degree_surjective b
    exact reduces_join_left A B
  le_sup_right a b := by
    obtain ⟨A, rfl⟩ := degree_surjective a
    obtain ⟨B, rfl⟩ := degree_surjective b
    exact reduces_join_right A B
  sup_le a b c := by
    obtain ⟨A, rfl⟩ := degree_surjective a
    obtain ⟨B, rfl⟩ := degree_surjective b
    obtain ⟨C, rfl⟩ := degree_surjective c
    exact join_reduces

instance : OrderBot Degree where
  bot := degree (fun _ => false)
  bot_le a := by
    obtain ⟨A, rfl⟩ := degree_surjective a
    apply RecursiveIn.iff_nat.mpr
    change Nat.RecursiveIn {oracleFunction A} (fun _ => Part.some 0)
    exact .zero

theorem automorphism_preserves_join (π : Degree ≃o Degree) (a b : Degree) :
    π (a ⊔ b) = π a ⊔ π b := π.map_sup a b

theorem automorphism_fixes_zero (π : Degree ≃o Degree) : π ⊥ = ⊥ := π.map_bot

end TuringRigidity

end OAI
