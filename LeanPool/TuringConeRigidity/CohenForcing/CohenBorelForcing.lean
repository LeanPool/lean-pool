/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenBorelForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CountableForcing
public import LeanPool.TuringConeRigidity.Representation.GenericTruth
public import LeanPool.TuringConeRigidity.Representation.GenericFiberIdeal
public import LeanPool.TuringConeRigidity.Representation.GenericSourceTransfer

/-!
# Cohen Borel Forcing
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenBorelForcing
open Set FiniteShuffle ShuffleRequirements GenericTopology GenericTruth CountableForcing

@[ext] structure Condition where
  word : List Bool

instance : PartialOrder Condition where
  le p q := q.word <+: p.word
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁
  le_antisymm _ _ h₁ h₂ := Condition.ext (List.Sublist.antisymm h₂.sublist h₁.sublist)

def realFilter (A : Oracle) : GenericFilter Condition where
  carrier := {p | Realizes p.word A}
  nonempty := ⟨⟨[]⟩,by intro i hi; simp at hi⟩
  upper := fun hpq hp => realizes_mono hpq hp
  directed := by
    intro p q hp hq
    let n := max p.word.length q.word.length
    refine ⟨⟨initial A n⟩,(realizes_initial A A n).mpr (fun _ _ => rfl),?_,?_⟩
    · change p.word <+: initial A n
      rw [←prefix_default p.word]
      exact initial_prefix (n := p.word.length) (m := n) (le_max_left _ _) hp
    · change q.word <+: initial A n
      rw [←prefix_default q.word]
      exact initial_prefix (n := q.word.length) (m := n) (le_max_right _ _) hq

def Family (a : Sentence Condition) (n : ℕ) (s : List Bool) : Prop :=
  (⟨s⟩ : Condition) ∈ a.Requirements n

theorem family_denseOpen (a : Sentence Condition) : ∀ n, DenseOpen (Family a n) := by
  intro n
  constructor
  · intro s
    obtain ⟨q,hq,hD⟩ := a.requirements_dense n (⟨s⟩ : Condition)
    exact ⟨q.word,hq,hD⟩
  · intro s t hst hs
    exact a.requirements_mono n (p := ⟨s⟩) (q := ⟨t⟩) hst hs

theorem realFilter_generic (a : Sentence Condition) (A : Oracle)
    (hA : ShuffleRequirements.GenericFor (Family a) A) :
    CountableForcing.GenericFor a.Requirements (realFilter A) := by
  intro n
  obtain ⟨s,hs,hAs⟩ := hA n
  exact ⟨⟨s⟩,hAs,hs⟩

def Represented (S : Set Oracle) : Prop :=
  ∃ a : Sentence Condition, ∀ A, a.Truth (realFilter A) ↔ A ∈ S

theorem open_represented (S : Set Oracle) (hS : IsOpen S) : Represented S := by
  let a : Sentence Condition := .existsNat (fun k => .conj
    (.ground (CylinderIn S (BorelGeneric.word k))) (.member ⟨BorelGeneric.word k⟩))
  refine ⟨a,?_⟩
  intro A
  constructor
  · rintro ⟨k,hk,hAk⟩
    exact hk A hAk
  · intro hA
    obtain ⟨n,hn⟩ := cylinder_basis S hS A hA
    obtain ⟨k,hk⟩ := BorelGeneric.word_surjective (initial A n)
    refine ⟨k,?_,?_⟩
    · change CylinderIn S (BorelGeneric.word k)
      rw [hk]
      exact fun B hB => hn B ((realizes_initial A B n).mp hB)
    · change Realizes (BorelGeneric.word k) A
      rw [hk]
      exact (realizes_initial A A n).mpr (fun _ _ => rfl)

theorem represented_empty : Represented (∅ : Set Oracle) :=
  ⟨.ground False,fun _ => Iff.rfl⟩

theorem Represented.compl {S : Set Oracle} (hS : Represented S) : Represented Sᶜ := by
  obtain ⟨a,ha⟩ := hS
  exact ⟨.neg a,fun A => not_congr (ha A)⟩

theorem represented_iUnion (S : ℕ → Set Oracle) (hS : ∀ n, Represented (S n)) :
    Represented (⋃ n, S n) := by
  classical
  choose a ha using hS
  refine ⟨.existsNat a,?_⟩
  intro A
  change (∃ n, (a n).Truth (realFilter A)) ↔ A ∈ ⋃ n, S n
  simp only [mem_iUnion]
  exact exists_congr (fun n => ha n A)

theorem borel_represented (S : Set Oracle) (hS : MeasurableSet S) : Represented S := by
  have hb : @MeasurableSet Oracle (borel Oracle) S := by
    rwa [←BorelSpace.measurable_eq]
  let m : MeasurableSpace Oracle := {
    MeasurableSet' := Represented
    measurableSet_empty := represented_empty
    measurableSet_compl := fun _ h => h.compl
    measurableSet_iUnion := represented_iUnion }
  have hm : borel Oracle ≤ m := MeasurableSpace.generateFrom_le (fun _ h => open_represented _ h)
  exact hm S hb

theorem borel_forcing_truth (S : Set Oracle) (hS : MeasurableSet S) :
    ∃ a : Sentence Condition, (∀ n, DenseOpen (Family a n)) ∧
      ∀ A, ShuffleRequirements.GenericFor (Family a) A →
        (A ∈ S ↔ ∃ p : Condition, Realizes p.word A ∧ Sentence.Forces p a) := by
  obtain ⟨a,ha⟩ := borel_represented S hS
  refine ⟨a,family_denseOpen a,?_⟩
  intro A hA
  rw [←ha A]
  exact a.generic_truth (realFilter A) (realFilter_generic a A hA)

theorem sourceEquation_forcing_truth (p : OracleCode) (P : Oracle) :
    ∃ a : Sentence Condition, (∀ n, DenseOpen (Family a n)) ∧
      ∀ A, ShuffleRequirements.GenericFor (Family a) A →
        (GenericIdentity.SourceEquation p P (GenericTruth.triple A) ↔
          ∃ q : Condition, Realizes q.word A ∧ Sentence.Forces q a) :=
  borel_forcing_truth _ ((GenericIdentity.sourceEquation_measurable p P).preimage
    GenericTruth.triple_measurable)

theorem selected_source_forcing (p : OracleCode) (P : Oracle)
    (E : ℕ → List Bool → Prop) (hE : ∀ n, DenseOpen (E n)) :
    ∃ a : Sentence Condition,
    ∃ F : ℕ → List Bool → Prop, (∀ n, DenseOpen (F n)) ∧
    ∃ Z : {Y : Oracle // ShuffleRequirements.GenericFor F Y} → Oracle, Measurable Z ∧
      (∀ Y b, ShuffleRequirements.GenericFor E (PairGenericSelection.column b (Z Y)) ∧
        GenericCoding.InfiniteOdd (PairGenericSelection.column b (Z Y)) ∧
        ∀ X, ShuffleRequirements.GenericFor E
          (GenericCoding.code X (PairGenericSelection.column b (Z Y)))) ∧
      (∀ Y d, d ≤ degree Y.val ↔
        d ≤ degree (join Y.val (PairGenericSelection.column false (Z Y))) ∧
        d ≤ degree (join Y.val (PairGenericSelection.column true (Z Y)))) ∧
      ∀ Y, GenericIdentity.SourceEquation p P
          (Y.val,PairGenericSelection.column false (Z Y),PairGenericSelection.column true (Z Y)) ↔
        ∃ q : Condition, Realizes q.word (join Y.val (Z Y)) ∧ Sentence.Forces q a := by
  obtain ⟨a,hD,htruth⟩ := sourceEquation_forcing_truth p P
  obtain ⟨hF,Z,hZ,hjoint,hgen,hI⟩ := GenericFactor.borel_joint_ideal_selection
    (Family a) E hD hE
  refine ⟨a,GenericFactor.FirstFamily (Family a),hF,Z,hZ,hgen,hI,?_⟩
  intro Y
  simpa only [GenericSourceTransfer.triple_join] using htruth (join Y.val (Z Y)) (hjoint Y)

end TuringRigidity.CohenBorelForcing

end OAI
