/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/EffectiveFamilies.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.GuardedCoding
public import LeanPool.TuringConeRigidity.Syntax.BoundedDecoding

/-!
# Effective Families
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectiveFamilies
open Encodable EncodedForcing UniformOracle SetCoding BoundedDecoding

theorem reindex_reduces (A : Oracle) {f : ℕ → ℕ} (hf : Primrec f) :
    Reduces (fun n => A (f n)) A := by
  apply RecursiveIn.iff_nat.mpr
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) := .oracle _ (Set.mem_singleton _)
  exact total_comp hq (total_primrec hf)

/-- Extract an indexed two-dimensional slice from the paired coordinates of `A`. -/
def slice (A : Oracle) (i : ℕ) : Oracle := fun m =>
  A (Nat.pair (Nat.pair i (Nat.unpair m).1) (Nat.unpair m).2)

@[simp] theorem slice_column (A : Oracle) (i j : ℕ) :
    columns (slice A i) j = columns A (Nat.pair i j) := by
  funext n
  simp [slice,columns]

theorem slice_reduces (A : Oracle) (i : ℕ) : Reduces (slice A i) A :=
  reindex_reduces A (Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (Primrec.const i) (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair))

/-- Join corresponding columns of two oracle families. -/
def mix (A B : Oracle) : Oracle := fun m =>
  join (columns A (Nat.unpair m).1) (columns B (Nat.unpair m).1) (Nat.unpair m).2

@[simp] theorem mix_column (A B : Oracle) (j : ℕ) :
    columns (mix A B) j = join (columns A j) (columns B j) := by
  funext n
  simp [mix,columns]

theorem mix_reduces (A B : Oracle) : Reduces (mix A B) (join A B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let q := Primrec₂.natPair.comp f (Primrec.nat_div.comp r (Primrec.const 2))
  have hp := Primrec.cond (Primrec.nat_bodd.comp r)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) q) (Primrec.const 1))
    (Primrec.nat_mul.comp (Primrec.const 2) q)
  have hh := reindex_reduces (join A B) hp
  convert hh using 1
  funext m
  cases hb : (Nat.unpair m).2.bodd <;> simp [mix,join,columns,hb]
  congr 1
  omega

/-- Iteratively combine the first `n` slices of `G`, starting with the zero oracle. -/
def tuples (G : Oracle) : ℕ → Oracle
  | 0 => fun _ => false
  | n+1 => mix (tuples G n) (slice G n)

theorem tuples_reduces (G : Oracle) (n : ℕ) : Reduces (tuples G n) G := by
  induction n with
  | zero => exact RecursiveIn.iff_nat.mpr .zero
  | succ n ih =>
    exact reduces_trans (mix_reduces _ _) (join_reduces ih (slice_reduces G n))

theorem tuples_degree (G : Oracle) (n j : ℕ) :
    degree (columns (tuples G n) j) = (Finset.range n).sup (fun i => degree (columns G (Nat.pair i
      j))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tuples,mix_column]
    change degree (columns (tuples G n) j) ⊔ degree (columns (slice G n) j) = _
    rw [ih,slice_column,Finset.range_add_one,Finset.sup_insert]
    exact sup_comm _ _

theorem antichainCode_below {F H : Oracle} (hF : Reduces F H)
    (hAnti : ∀ i j, degree (columns F i) ≤ degree (columns F j) →
      degree (columns F i) = degree (columns F j)) :
    ∃ p : AntichainCode, AntichainBelow p (degree (OracleJump.jump H)) ∧
      ∀ x, p.Holds x ↔ ∃ k, degree (columns F k) = x := by
  obtain ⟨g₀,g₁,hg,hcode⟩ := GuardedCoding.effective_antichain_parameters F hAnti
  have hj : OracleJump.degreeJump (degree F) ≤ degree (OracleJump.jump H) := OracleJump.jump_mono hF
  have hb : degree F ≤ degree (OracleJump.jump H) :=
    (show degree F ≤ degree H from hF).trans (OracleJump.degree_le_jump _)
  exact ⟨⟨degree F,g₀,g₁⟩,⟨hb,(le_sup_left.trans hg).trans hj,
    (le_sup_right.trans hg).trans hj⟩,hcode⟩

end TuringRigidity.EffectiveFamilies

end OAI
