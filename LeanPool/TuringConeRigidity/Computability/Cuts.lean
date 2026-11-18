/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/Cuts.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module


public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import LeanPool.TuringConeRigidity.Computability.OracleCode

/-!
# Cuts
-/


@[expose] public section

namespace OAI

open Set Filter Topology
namespace TuringRigidity

/-- Enumerate the rational numbers by decoding natural codes, with zero as the fallback. -/
def rationalEnumeration (n : ℕ) : ℚ := (Encodable.decode (α := ℚ) n).getD 0

theorem rationalEnumeration_surjective : Function.Surjective rationalEnumeration := by
  intro q
  refine ⟨Encodable.encode q, ?_⟩
  simp [rationalEnumeration]

/-- The lower rational cut of a real, represented as a Boolean oracle. -/
noncomputable def cut (x : ℝ) : Oracle := fun n => decide ((rationalEnumeration n : ℝ) < x)

@[simp] theorem cut_eq_true (x : ℝ) (n : ℕ) :
    cut x n = true ↔ (rationalEnumeration n : ℝ) < x := by simp [cut]

theorem cut_injective : Function.Injective cut := by
  intro x y hxy
  apply le_antisymm
  · by_contra h
    have hyx : y < x := lt_of_not_ge h
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hyx
    obtain ⟨n, hn⟩ := rationalEnumeration_surjective q
    have hc : cut x n = true := (cut_eq_true x n).mpr (by simpa [hn] using hqx)
    rw [hxy] at hc
    have hqy := (cut_eq_true y n).mp hc
    rw [hn] at hqy
    exact (not_lt_of_gt hyq) hqy
  · by_contra h
    have hxy' : x < y := lt_of_not_ge h
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy'
    obtain ⟨n, hn⟩ := rationalEnumeration_surjective q
    have hc : cut y n = true := (cut_eq_true y n).mpr (by simpa [hn] using hqy)
    rw [← hxy] at hc
    have hqx := (cut_eq_true x n).mp hc
    rw [hn] at hqx
    exact (not_lt_of_gt hxq) hqx

theorem cut_measurable : Measurable cut := by
  apply Measurable.of_eval
  intro n
  have h : MeasurableSet {x : ℝ | (rationalEnumeration n : ℝ) < x} := measurableSet_Ioi
  have hm : Measurable (fun x : ℝ => if (rationalEnumeration n : ℝ) < x then true else false) :=
    Measurable.ite h measurable_const measurable_const
  convert hm using 1
  funext x
  by_cases hq : (rationalEnumeration n : ℝ) < x <;> simp [cut, hq]

/-- The Turing degree of the lower rational cut of a real. -/
noncomputable def realDegree (x : ℝ) : Degree := degree (cut x)

theorem represented_real_map_countable_fibers (π : Degree ≃o Degree) (F : ℝ → Oracle)
    (hF : ∀ x, degree (F x) = π (realDegree x)) :
    ∀ B : Oracle, {x : ℝ | F x = B}.Countable := by
  exact countable_lift_fiber cut cut_injective π π.injective F hF

end TuringRigidity

end OAI
