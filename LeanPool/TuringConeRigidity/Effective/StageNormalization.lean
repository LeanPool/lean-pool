/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/StageNormalization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.StageLimits
public import LeanPool.TuringConeRigidity.Computability.Introreducible

/-!
# Stage Normalization
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.StageNormalization
open Encodable UniformOracle EncodedForcing StageRecords

/-- Normalize every column by replacing it with the oracle coding its finite prefixes. -/
def normalized (A : Oracle) : Oracle := fun v =>
  Introreducible.prefixSet (columns A (Nat.unpair v).1) (Nat.unpair v).2

@[simp] theorem normalized_column (A : Oracle) (k : ℕ) :
    columns (normalized A) k = Introreducible.prefixSet (columns A k) := by
  funext n
  simp [normalized,columns]

/-- Append one selected oracle bit to a coded finite prefix. -/
def prefixStep (A : Oracle) (v : ℕ) : ℕ := UniformOracle.appendEncoded
  (Nat.unpair (Nat.unpair v).2).2
  (CommonIdeal.bit (A (Nat.pair (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1)))

private theorem prefixStep_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction A} (fun v => Part.some (prefixStep A v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) := .oracle _ (Set.mem_singleton _)
  have h := total_comp hq (total_primrec (Primrec₂.natPair.comp f (f.comp r)))
  have hh := total_comp (total_primrec (UniformOracle.appendEncoded_primrec.comp f r))
    (total_pair (total_primrec (r.comp r)) h)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

/-- The code of the first `n` bits of column `k`. -/
def columnPrefix (A : Oracle) (k n : ℕ) : ℕ :=
  recur (fun _ => encode ([] : List ℕ)) (prefixStep A) k n

theorem prefix_eq (A : Oracle) (k n : ℕ) :
    columnPrefix A k n = Introreducible.prefixCode (columns A k) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change prefixStep A (Nat.pair k (Nat.pair n (columnPrefix A k n))) = _
    simp only [prefixStep,Nat.unpair_pair,ih,UniformOracle.appendEncoded,
      Introreducible.prefixCode,encodek,Option.getD_some,
      PrefixComputability.oraclePrefix,List.range_succ,List.map_append,List.map_cons,List.map_nil]
    rfl

theorem prefix_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction A} (fun v => Part.some (columnPrefix A (Nat.unpair v).1
      (Nat.unpair v).2)) :=
  recur_recursive (total_primrec (Primrec.const (encode ([] : List ℕ)))) (prefixStep_recursive A)

theorem normalized_reduces (A : Oracle) : Reduces (normalized A) A := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := total_comp (prefix_recursive A) (total_primrec (Primrec₂.natPair.comp f
    (Introreducible.codeLength_primrec.comp r)))
  have he : Primrec (fun v : ℕ => if (Nat.unpair v).1 = (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp f r) (Primrec.const 1) (Primrec.const 0)
  have hh := total_comp (total_primrec he) (total_pair hp (total_primrec r))
  apply RecursiveIn.iff_nat.mpr
  exact hh.of_eq (fun v => by
    simp [Nat.unpair_pair, prefix_eq, normalized, Introreducible.prefixSet, oracleFunction])

theorem normalized_spec (A : Oracle) (k : ℕ) :
    degree (columns (normalized A) k) = degree (columns A k) ∧
      {n | columns (normalized A) k n = true}.Infinite ∧
      ∀ Z : Oracle, (∀ n, Z n = true → columns (normalized A) k n = true) →
        {n | Z n = true}.Infinite → Reduces (columns (normalized A) k) Z := by
  rw [normalized_column]
  exact ⟨Introreducible.prefixSet_degree _,Introreducible.prefixSet_infinite _,fun Z hs hi =>
    reduces_trans (Introreducible.prefixSet_reduces _) (Introreducible.reduces_of_infinite_subset
      hs hi)⟩

theorem effective_first_clause (A : Oracle) : ∃ G₀ G₁ : Oracle,
    Reduces (join G₀ G₁) (OracleJump.jump A) ∧
      ∀ k, ∃ C : Oracle, Reduces C (join G₀ (columns A k)) ∧
        Reduces C (join G₁ (columns A k)) ∧ ¬ Reduces C (columns A k) := by
  let B := normalized A
  obtain ⟨hbound,hcode⟩ := StageLimits.effective_first_clause B (fun k => (normalized_spec A k).2.1)
  refine ⟨StageLimits.G₀ B,StageLimits.G₁ B,?_,fun k => ?_⟩
  · exact reduces_trans hbound (OracleJump.jump_mono (normalized_reduces A))
  · obtain ⟨C,h₀,h₁,hn⟩ := hcode k
    obtain ⟨hBA,hAB⟩ := (degree_eq_iff _ _).mp (normalized_spec A k).1
    exact ⟨C,reduces_trans h₀ (join_mono (reduces_refl _) hBA),
      reduces_trans h₁ (join_mono (reduces_refl _) hBA),fun h => hn (reduces_trans h hAB)⟩

end TuringRigidity.StageNormalization

end OAI
