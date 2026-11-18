/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/EffectiveRelations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.EffectiveFamilies
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumns

/-!
# Effective Relations
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectiveRelations
open EncodedForcing EffectiveFamilies CohenColumns EffectiveCohen SetCoding RelationCoding
  BoundedDecoding

private theorem data_below {A B : Oracle} (hA : Reduces A B) (i j : ℕ) :
    degree (columns A (Nat.pair i j)) ≤ degree B :=
  reduces_trans (CodingExtraction.column_projection_reduces A _) hA

theorem coordinate_code {A B G : Oracle} (hA : Reduces A B) (hg : OneGeneric B G) (i : ℕ) :
    ∃ p : SetCode, p.bound = degree B ∧ SetBelow p (degree (OracleJump.jump (join B G))) ∧
      ∀ x c, p.Graph x c ↔ ∃ j, degree (columns A (Nat.pair i j)) = x ∧
        degree (columns G (Nat.pair i j)) = c := by
  have htag (x y : Degree) (hx : x ≤ degree B) (hy : y ≤ degree B) (j k : ℕ) :
      x ⊔ degree (columns G (Nat.pair i j)) ≤ y ⊔ degree (columns G (Nat.pair i k)) ↔
        x ≤ y ∧ j = k := by
    simpa using independence hg x y hx hy (Nat.pair i j) {Nat.pair i k}
  have hanti : ∀ j k, degree (columns (slice G i) j) ≤ degree (columns (slice G i) k) →
      degree (columns (slice G i) j) = degree (columns (slice G i) k) := by
    intro j k hjk
    have he := (htag ⊥ ⊥ bot_le bot_le j k).mp (by simpa using hjk)
    rw [he.2]
  have had : ∀ j k, degree (columns (mix (slice A i) (slice G i)) j) ≤
      degree (columns (mix (slice A i) (slice G i)) k) →
      degree (columns (mix (slice A i) (slice G i)) j) = degree (columns (mix (slice A i) (slice G
        i)) k) := by
    intro j k hjk
    have he := (htag _ _ (data_below hA i j) (data_below hA i k) j k).mp (by
      simp only [mix_column,slice_column] at hjk
      exact hjk)
    rw [he.2]
  have htagBound : Reduces (slice G i) (join B G) :=
    reduces_trans (slice_reduces G i) (reduces_join_right B G)
  have hdecBound : Reduces (mix (slice A i) (slice G i)) (join B G) :=
    reduces_trans (mix_reduces _ _) (join_reduces
      (reduces_trans (slice_reduces A i) (reduces_trans hA (reduces_join_left B G))) htagBound)
  obtain ⟨pc,hpcBound,hpc⟩ := antichainCode_below htagBound hanti
  obtain ⟨pa,hpaBound,hpa⟩ := antichainCode_below hdecBound had
  refine ⟨⟨degree B,pc,pa⟩,rfl,?_,fun x c => ?_⟩
  · exact ⟨(le_sup_left : degree B ≤ degree B ⊔ degree G).trans (OracleJump.degree_le_jump
    _),hpcBound,hpaBound⟩
  · change (x ≤ degree B ∧ pc.Holds c ∧ pa.Holds (x ⊔ c)) ↔ _
    rw [hpc,hpa]
    simp only [slice_column,mix_column]
    constructor
    · rintro ⟨hx,⟨j,rfl⟩,⟨k,hk⟩⟩
      have hl := (htag _ x (data_below hA i k) hx k j).mp hk.le
      have hr := (htag x _ hx (data_below hA i k) j k).mp hk.ge
      have he := hl.2
      subst k
      exact ⟨j,le_antisymm hl.1 hr.1,rfl⟩
    · rintro ⟨j,rfl,rfl⟩
      exact ⟨data_below hA i j,⟨j,rfl⟩,⟨j,rfl⟩⟩

private theorem fin_sup (n : ℕ) (f : ℕ → Degree) :
    Finset.univ.sup (fun i : Fin n => f i.val) = (Finset.range n).sup f := by
  classical
  have he : (Finset.univ : Finset (Fin n)).image Fin.val = Finset.range n := by
    ext m
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_range]
    exact ⟨fun ⟨a,ha⟩ => ha ▸ a.isLt,fun hm => ⟨⟨m,hm⟩,rfl⟩⟩
  simpa only [Finset.sup_image,Function.comp_def] using congrArg (fun F : Finset ℕ => F.sup f) he

theorem tag_below_tuple {B G : Oracle} (hg : OneGeneric B G) {n i j k : ℕ}
    (h : degree (columns G (Nat.pair i j)) ≤ degree (columns (tuples G n) k)) : j = k := by
  classical
  let F := (Finset.range n).image (fun l => Nat.pair l k)
  have hh : degree (columns G (Nat.pair i j)) ≤ F.sup (fun l => degree (columns G l)) := by
    simpa only [tuples_degree,F,Finset.sup_image,Function.comp_def] using h
  have hm := (independence hg ⊥ ⊥ bot_le bot_le (Nat.pair i j) F).mp (by simpa using hh)
  obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hm.2
  simpa only [Nat.unpair_pair] using (congrArg (fun m => (Nat.unpair m).2) hl).symm

theorem tuples_antichain {B G : Oracle} (hg : OneGeneric B G) (n : ℕ) :
    ∀ j k, degree (columns (tuples G n) j) ≤ degree (columns (tuples G n) k) →
      degree (columns (tuples G n) j) = degree (columns (tuples G n) k) := by
  intro j k hjk
  cases n with
  | zero => rfl
  | succ n =>
    have htag : degree (columns G (Nat.pair 0 j)) ≤ degree (columns (tuples G (n+1)) j) := by
      rw [tuples_degree]
      exact Finset.le_sup (f := fun i => degree (columns G (Nat.pair i j))) (by simp)
    have he := tag_below_tuple hg (htag.trans hjk)
    rw [he]

theorem relation_code {A B G : Oracle} (hA : Reduces A B) (hg : OneGeneric B G) (n : ℕ) :
    ∃ p : RelationCode n, RelationBelow p (degree (OracleJump.jump (join B G))) ∧
      ∀ v, p.Holds v ↔ ∃ j, ∀ i : Fin n, degree (columns A (Nat.pair i.val j)) = v i := by
  classical
  choose pc hbound hpBound hp using fun i : Fin n => coordinate_code hA hg i.val
  obtain ⟨pt,htBound,ht⟩ := antichainCode_below
    (reduces_trans (tuples_reduces G n) (reduces_join_right B G)) (tuples_antichain hg n)
  refine ⟨⟨pc,pt⟩,⟨hpBound,htBound⟩,fun v => ?_⟩
  constructor
  · rintro ⟨c,hc,hT⟩
    obtain ⟨j,hj⟩ := (ht _).mp hT
    refine ⟨j,fun i => ?_⟩
    obtain ⟨k,hkv,hkc⟩ := (hp i _ _).mp (hc i)
    have hle : degree (columns G (Nat.pair i.val k)) ≤ degree (columns (tuples G n) j) := by
      rw [hkc,hj]
      exact Finset.le_sup (f := c) (Finset.mem_univ i)
    have he := tag_below_tuple hg hle
    simpa only [he] using hkv
  · rintro ⟨j,hj⟩
    let c := fun i : Fin n => degree (columns G (Nat.pair i.val j))
    refine ⟨c,fun i => (hp i _ _).mpr ⟨j,hj i,rfl⟩,(ht _).mpr ⟨j,?_⟩⟩
    rw [tuples_degree]
    exact (fin_sup n (fun i => degree (columns G (Nat.pair i j)))).symm

theorem effective_relation_sequence (A : Oracle) (n : ℕ) :
    ∃ p : RelationCode n, RelationBelow p (degree (OracleJump.jump A)) ∧
      ∀ v, p.Holds v ↔ ∃ j, ∀ i : Fin n, degree (columns A (Nat.pair i.val j)) = v i := by
  obtain ⟨G,hG,hgen,hlow⟩ := CohenLowness.relative_low_generic A
  obtain ⟨p,hp,hcode⟩ := relation_code (reduces_refl A) hgen n
  exact ⟨p,hlow ▸ hp,hcode⟩

end TuringRigidity.EffectiveRelations

end OAI
