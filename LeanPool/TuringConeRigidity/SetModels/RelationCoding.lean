/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RelationCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.SetCoding

/-!
# Relation Coding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelationCoding
open IndependentFamily SetCoding

theorem tuple_join_le_eq {n : ℕ} {S : Type*} (b : Degree)
    (index : (Fin n × S) → ℕ) (hinj : Function.Injective index)
    {v w : Fin n → S}
    (he : Finset.univ.sup (fun i => column b (index (i, v i))) ≤
      Finset.univ.sup (fun i => column b (index (i, w i)))) : v = w := by
  classical
  funext i
  let F := Finset.univ.image (fun j => index (j, w j))
  have hl : column b (index (i, v i)) ≤ F.sup (column b) := by
    have hv : column b (index (i, v i)) ≤
        Finset.univ.sup (fun j => column b (index (j, v j))) := Finset.le_sup (f := fun j =>
          column b (index (j, v j))) (Finset.mem_univ i)
    simpa [F, Finset.sup_image, Function.comp_def] using hv.trans he
  have hm := (independence b ⊥ ⊥ bot_le bot_le (index (i, v i)) F).mp (by simpa using hl)
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm.2
  have heij := hinj hj
  have hji : j = i := congrArg Prod.fst heij
  subst j
  exact (congrArg Prod.snd heij).symm

theorem tuple_join_injective {n : ℕ} {S : Type*} (b : Degree)
    (index : (Fin n × S) → ℕ) (hinj : Function.Injective index) :
    Function.Injective (fun v : Fin n → S =>
      Finset.univ.sup (fun i => column b (index (i, v i)))) :=
  fun _ _ h => tuple_join_le_eq b index hinj h.le

/-- A relation code using one set code per coordinate and an antichain code for the joined
tags. -/
structure RelationCode (n : ℕ) where
  /-- The set code governing the value and tag at each relation coordinate. -/
  coordinates : Fin n → SetCode
  /-- The antichain code governing the join of the coordinate tags. -/
  tuples : AntichainCode

/-- Choose a tag for each coordinate and test their join against the tuple antichain code. -/
def RelationCode.Holds {n : ℕ} (p : RelationCode n) (v : Fin n → Degree) : Prop :=
  ∃ c : Fin n → Degree,
    (∀ i, (p.coordinates i).Graph (v i) (c i)) ∧
      p.tuples.Holds (Finset.univ.sup c)

theorem countable_relation_coding (n : ℕ) (R : Set (Fin n → Degree))
    (hR : R.Countable) :
    ∃ p : RelationCode n, ∀ v, p.Holds v ↔ v ∈ R := by
  classical
  let P : Fin n → Set Degree := fun i => (fun v => v i) '' R
  let S : Set Degree := ⋃ i, P i
  have hP : ∀ i, (P i).Countable := fun i => hR.image _
  have hS : S.Countable := Set.countable_iUnion hP
  have hPS : ∀ i, P i ⊆ S := fun i => Set.subset_iUnion P i
  have : Countable S := hS.to_subtype
  let := Encodable.ofCountable (Fin n × S)
  let index : Fin n × S → ℕ := Encodable.encode
  have hinj : Function.Injective index := Encodable.encode_injective
  obtain ⟨b, hb⟩ := CountableBound.countable_bounded S hS
  let lift : ∀ i, P i → S := fun i a => ⟨a.val, hPS i a.property⟩
  let idx : ∀ i, P i → ℕ := fun i a => index (i, lift i a)
  have hidx : ∀ i, Function.Injective (idx i) := by
    intro i a d he
    apply Subtype.ext
    exact congrArg (fun t : Fin n × S => t.2.val) (hinj he)
  have hp : ∀ i, ∃ p : SetCode, p.bound = b ∧
      (∀ x c, p.Graph x c ↔ ∃ a : P i, a.val = x ∧ column b (idx i a) = c) ∧
      ∀ x, p.Holds x ↔ x ∈ P i := by
    intro i
    exact codes_with_tags (P i) (hP i) b (fun x hx => hb x (hPS i hx)) (idx i) (hidx i)
  choose p hpbound hpgraph hpholds using hp
  let tuple : R → (Fin n → S) := fun v i => ⟨v.val i, hPS i ⟨v.val, v.property, rfl⟩⟩
  let code : (Fin n → S) → Degree := fun v =>
    Finset.univ.sup (fun i => column b (index (i, v i)))
  let T : Set Degree := Set.range (fun v : R => code (tuple v))
  have : Countable R := hR.to_subtype
  have hT : T.Countable := Set.countable_range _
  have hanti : ∀ x ∈ T, ∀ y ∈ T, x ≤ y → x = y := by
    rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩ hle
    have he : tuple v = tuple w := tuple_join_le_eq b index hinj hle
    exact congrArg code he
  obtain ⟨pt, hpt⟩ := exists_antichainCode T hT hanti
  let q : RelationCode n := ⟨p, pt⟩
  refine ⟨q, ?_⟩
  intro v
  constructor
  · rintro ⟨c, hc, ht⟩
    have hh : ∀ i, ∃ a : P i, a.val = v i ∧ column b (idx i a) = c i := by
      intro i
      exact (hpgraph i _ _).mp (hc i)
    choose a ha hac using hh
    let u : Fin n → S := fun i => lift i (a i)
    have hu : code u = Finset.univ.sup c := by
      apply congrArg (fun f : Fin n → Degree => Finset.univ.sup f)
      funext i
      exact hac i
    obtain ⟨w, hw⟩ := (hpt _).mp ht
    have htu : tuple w = u := tuple_join_injective b index hinj (hw.trans hu.symm)
    have hvw : w.val = v := by
      funext i
      have he := congrArg (fun f : Fin n → S => (f i).val) htu
      exact he.trans (ha i)
    exact hvw ▸ w.property
  · intro hv
    let w : R := ⟨v, hv⟩
    let c : Fin n → Degree := fun i => column b (index (i, tuple w i))
    refine ⟨c, ?_, ?_⟩
    · intro i
      apply (hpgraph i _ _).mpr
      exact ⟨⟨v i, ⟨v, hv, rfl⟩⟩, rfl, rfl⟩
    · apply (hpt _).mpr
      exact ⟨w, rfl⟩

end TuringRigidity.RelationCoding

end OAI
