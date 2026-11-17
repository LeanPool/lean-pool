/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/IdealSelection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.ProgramSelection
public import LeanPool.TuringConeRigidity.Representation.Assembly

/-!
# Ideal Selection
-/


@[expose] public section

namespace OAI

open Set
namespace TuringRigidity

noncomputable def programOutput (c : OracleCode) (A : Oracle) : Oracle :=
  fun n => by classical exact decide (1 ∈ OracleCode.eval (oracleFunction A) c n)

theorem programOutput_measurable (c : OracleCode) : Measurable (programOutput c) := by
  apply Measurable.of_eval
  intro n
  apply measurable_to_countable'
  intro b
  cases b with
  | false =>
    convert (OracleCode.halting_set_open c n 1).measurableSet.compl using 1
    ext A
    simp [programOutput]
  | true =>
    convert (OracleCode.halting_set_open c n 1).measurableSet using 1
    ext A
    simp [programOutput]

theorem programOutput_eq (c : OracleCode) (A B : Oracle)
    (h : OracleCode.eval (oracleFunction A) c = oracleFunction B) :
    programOutput c A = B := by
  funext n
  simp only [programOutput, h, oracleFunction, Part.mem_some_iff]
  cases B n <;> simp

theorem reduces_measurable {X : Type*} [MeasurableSpace X]
    (A B : X → Oracle) (hA : Measurable A) (hB : Measurable B) :
    MeasurableSet {x | Reduces (A x) (B x)} := by
  have he : {x | Reduces (A x) (B x)} =
      ⋃ c : OracleCode, {x | OracleCode.eval (oracleFunction (B x)) c = oracleFunction (A x)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    exact OracleCode.turingReducible_iff_exists_code _ _
  rw [he]
  exact MeasurableSet.iUnion (fun c => OracleCode.success_measurable c B A hB hA)

theorem exists_programOutput (A B : Oracle) (h : Reduces B A) :
    ∃ n, programOutput (codeEnumeration n) A = B := by
  obtain ⟨c,hc⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
  obtain ⟨n,hn⟩ := codeEnumeration_surjective c
  exact ⟨n,by simpa [hn] using programOutput_eq c A B hc⟩

theorem borel_of_ideal_intersection {X : Type*} [MeasurableSpace X]
    (L R : X → Oracle) (hL : Measurable L) (hR : Measurable R)
    (d : X → Degree)
    (hd : ∀ x b, b ≤ d x ↔ b ≤ degree (L x) ∧ b ≤ degree (R x)) :
    ∃ F : X → Oracle, Measurable F ∧ ∀ x, degree (F x) = d x := by
  let C : ℕ → X → Oracle := fun n x => programOutput (codeEnumeration n) (L x)
  have hC (n : ℕ) : Measurable (C n) := (programOutput_measurable _).comp hL
  let S : X → ℕ → Prop := fun x n =>
    Reduces (C n x) (L x) ∧ Reduces (C n x) (R x) ∧
    ∀ k, Reduces (C k x) (L x) ∧ Reduces (C k x) (R x) → Reduces (C k x) (C n x)
  have hS (n : ℕ) : MeasurableSet {x | S x n} := by
    have hb (k : ℕ) : MeasurableSet {x | Reduces (C k x) (L x) ∧ Reduces (C k x) (R x)} :=
      (reduces_measurable _ _ (hC k) hL).inter (reduces_measurable _ _ (hC k) hR)
    have hm : MeasurableSet {x | ∀ k, Reduces (C k x) (L x) ∧ Reduces (C k x) (R x) → Reduces (C k
      x) (C n x)} := by
      simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro k
      have he : {x | Reduces (C k x) (L x) ∧ Reduces (C k x) (R x) → Reduces (C k x) (C n x)} =
          {x | Reduces (C k x) (L x) ∧ Reduces (C k x) (R x)}ᶜ ∪
          {x | Reduces (C k x) (C n x)} := by
        ext x
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
        tauto
      rw [he]
      exact (hb k).compl.union (reduces_measurable _ _ (hC k) (hC n))
    exact (reduces_measurable _ _ (hC n) hL).inter
      ((reduces_measurable _ _ (hC n) hR).inter hm)
  have hex : ∀ x, ∃ n, S x n := by
    intro x
    obtain ⟨B,hB⟩ := degree_surjective (d x)
    have hb : Reduces B (L x) ∧ Reduces B (R x) := (hd x (degree B)).mp (by rw [hB])
    obtain ⟨n,hn⟩ := exists_programOutput (L x) B hb.1
    have hc : C n x = B := hn
    refine ⟨n,?_,?_,?_⟩
    · simpa [hc] using hb.1
    · simpa [hc] using hb.2
    · intro k hk
      change degree (C k x) ≤ degree (C n x)
      rw [hc,hB]
      exact (hd x _).mpr hk
  let e := leastSuccess S hex
  have he : Measurable e := leastSuccess_measurable S hex hS
  have hout : Measurable (fun x => C (e x) x) := by
    apply Measurable.of_eval
    intro i
    apply measurable_to_countable'
    intro b
    have heq : {x | C (e x) x i = b} = ⋃ n : ℕ, {x | e x = n} ∩ {x | C n x i = b} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      exact ⟨fun h => ⟨e x,rfl,h⟩,fun ⟨n,hn,h⟩ => by simpa [hn] using h⟩
    change MeasurableSet {x | C (e x) x i = b}
    rw [heq]
    exact MeasurableSet.iUnion (fun n => (measurableSet_eq_fun he measurable_const).inter
      (measurableSet_eq_fun ((measurable_pi_apply i).comp (hC n)) measurable_const))
  refine ⟨fun x => C (e x) x,hout,?_⟩
  intro x
  have hs := leastSuccess_spec S hex x
  change S x (e x) at hs
  apply le_antisymm
  · exact (hd x _).mpr ⟨hs.1,hs.2.1⟩
  · obtain ⟨B,hB⟩ := degree_surjective (d x)
    have hb : Reduces B (L x) ∧ Reduces B (R x) := (hd x (degree B)).mp (by rw [hB])
    obtain ⟨n,hn⟩ := exists_programOutput (L x) B hb.1
    have hc : C n x = B := hn
    have hh := hs.2.2 n (by simpa [hc] using hb)
    change degree (C n x) ≤ degree (C (e x) x) at hh
    simpa [hc,hB] using hh

theorem common_lower_transport (π : Degree ≃o Degree) (a l r : Degree)
    (h : ∀ b, b ≤ a ↔ b ≤ l ∧ b ≤ r) :
    ∀ b, b ≤ π a ↔ b ≤ π l ∧ b ≤ π r := by
  intro b
  have hh := h (π.symm b)
  simpa only [π.symm_apply_le] using hh

theorem representation_of_ideal_generators
    (h : ∀ π : Degree ≃o Degree, ∃ L R : Oracle → Oracle,
      Measurable L ∧ Measurable R ∧
      ∀ A b, b ≤ π (degree A) ↔ b ≤ degree (L A) ∧ b ≤ degree (R A)) :
    BorelRepresentation := by
  intro π
  obtain ⟨L,R,hL,hR,hd⟩ := h π
  exact borel_of_ideal_intersection L R hL hR (fun A => π (degree A)) hd

end TuringRigidity

end OAI
