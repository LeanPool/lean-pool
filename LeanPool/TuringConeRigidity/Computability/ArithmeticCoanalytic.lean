/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticCoanalytic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticPresentationProperty
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Arithmetic Coanalytic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Set MeasureTheory

theorem Arith.measurable {P} (h : Arith P) (v : ℕ) : MeasurableSet {O | P O v} := by
  induction h generalizing v with
  | pure P hP =>
    by_cases hp : P v <;> simp [hp]
  | query i =>
    exact measurableSet_eq_fun ((measurable_pi_apply v).comp (measurable_pi_apply i))
      measurable_const
  | neg h ih => exact (ih v).compl
  | and h g ih ig => exact (ih v).inter (ig v)
  | @ex P h ih =>
    have he : {O | ∃ n, P O (Nat.pair v n)} = ⋃ n : ℕ, {O | P O (Nat.pair v n)} := by
      ext O
      simp
    rw [he]
    exact MeasurableSet.iUnion (fun n => ih (Nat.pair v n))
  | comp f h hf ih => exact ih (f v)

end TuringRigidity.UniformArithmetic

namespace TuringRigidity.ArithmeticPersistence
open Set MeasureTheory UniformArithmetic

theorem parameters_continuous :
    Continuous (fun x : (Oracle × Oracle) × Oracle => parameters x.1.1 x.1.2 x.2) := by
  apply continuous_pi
  intro i
  cases i with
  | zero => exact continuous_fst.fst
  | succ i =>
    cases i with
    | zero => exact continuous_fst.snd
    | succ i => exact continuous_snd

theorem PiOneOne.coanalytic {P : Oracle → Oracle → Prop} (h : PiOneOne P) :
    AnalyticSet ({x : Oracle × Oracle | P x.1 x.2}ᶜ) := by
  classical
  obtain ⟨Q,hQ,hiff⟩ := h
  let S : Set ((Oracle × Oracle) × Oracle) :=
    {x | ¬ Q (parameters x.1.1 x.1.2 x.2) 0}
  have hS : MeasurableSet S :=
    (hQ.neg.measurable 0).preimage parameters_continuous.measurable
  have he : ({x : Oracle × Oracle | P x.1 x.2}ᶜ) = Prod.fst '' S := by
    ext x
    simp only [mem_compl_iff,mem_ofPred_eq,hiff,not_forall,mem_image,S]
    constructor
    · rintro ⟨H,hH⟩
      exact ⟨(x,H),hH,rfl⟩
    · rintro ⟨⟨y,H⟩,hH,he⟩
      change y = x at he
      subst y
      exact ⟨H,hH⟩
  rw [he]
  exact hS.analyticSet_image measurable_fst

theorem source_4_2_1_coanalytic :
    AnalyticSet ({x : Oracle × Oracle | Property x.1 x.2}ᶜ) :=
  source_4_2_1.coanalytic

end TuringRigidity.ArithmeticPersistence

end OAI
