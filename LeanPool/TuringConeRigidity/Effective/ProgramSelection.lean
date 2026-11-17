/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/ProgramSelection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.ProgramTopology
public import LeanPool.TuringConeRigidity.Computability.Joins
public import LeanPool.TuringConeRigidity.Representation.Category

/-!
# Program Selection
-/


@[expose] public section

namespace OAI

open Set Filter Topology
namespace TuringRigidity

noncomputable def leastSuccess {X : Type*} (R : X → ℕ → Prop)
    (hex : ∀ x, ∃ n, R x n) (x : X) : ℕ := by
  classical
  exact Nat.find (hex x)

theorem leastSuccess_spec {X : Type*} (R : X → ℕ → Prop) (hex : ∀ x, ∃ n, R x n)
    (x : X) : R x (leastSuccess R hex x) := by
  classical
  exact Nat.find_spec (hex x)

theorem leastSuccess_eq_iff {X : Type*} (R : X → ℕ → Prop) (hex : ∀ x, ∃ n, R x n)
    (x : X) (n : ℕ) : leastSuccess R hex x = n ↔ R x n ∧ ∀ k < n, ¬ R x k := by
  classical
  exact Nat.find_eq_iff (hex x)

theorem leastSuccess_measurable {X : Type*} [MeasurableSpace X] (R : X → ℕ → Prop)
    (hex : ∀ x, ∃ n, R x n) (hR : ∀ n, MeasurableSet {x | R x n}) :
    Measurable (leastSuccess R hex) := by
  apply measurable_to_countable'
  intro n
  have heq : (leastSuccess R hex) ⁻¹' {n} =
      {x | R x n} ∩ ⋂ k : Fin n, {x | ¬ R x k.val} := by
    ext x
    constructor
    · intro h
      have hr := (leastSuccess_eq_iff R hex x n).mp h
      exact ⟨hr.1, Set.mem_iInter.mpr (fun k => hr.2 k.val k.isLt)⟩
    · rintro ⟨h,hmin⟩
      exact (leastSuccess_eq_iff R hex x n).mpr ⟨h,fun k hk => Set.mem_iInter.mp hmin ⟨k,hk⟩⟩
  rw [heq]
  exact (hR n).inter (MeasurableSet.iInter (fun k : Fin n => (hR k.val).compl))

def codeEnumeration (n : ℕ) : OracleCode :=
  (Encodable.decode (α := OracleCode) n).getD .zero

theorem codeEnumeration_surjective : Function.Surjective codeEnumeration := by
  intro c
  refine ⟨Encodable.encode c, ?_⟩
  simp [codeEnumeration]

theorem join_measurable {X : Type*} [MeasurableSpace X] (A B : X → Oracle)
    (hA : Measurable A) (hB : Measurable B) : Measurable (fun x => join (A x) (B x)) := by
  apply Measurable.of_eval
  intro n
  by_cases hn : n.bodd = true
  · simpa [join, hn, Function.comp_def] using (measurable_pi_apply (n/2)).comp hB
  · simpa [join, hn, Function.comp_def] using (measurable_pi_apply (n/2)).comp hA

theorem addition_program_selection (F : ℝ → Oracle) (hF : Measurable F)
    (hadd : ∀ x y, Reduces (F (x + y)) (join (F x) (F y))) :
    ∃ e : ℝ × ℝ → ℕ, Measurable e ∧ ∀ x y,
      OracleCode.eval (oracleFunction (join (F x) (F y))) (codeEnumeration (e (x,y))) =
        oracleFunction (F (x+y)) := by
  let R : (ℝ × ℝ) → ℕ → Prop := fun p n =>
    OracleCode.eval (oracleFunction (join (F p.1) (F p.2))) (codeEnumeration n) =
      oracleFunction (F (p.1+p.2))
  have hR : ∀ n, MeasurableSet {p | R p n} := by
    intro n
    exact OracleCode.success_measurable (codeEnumeration n)
      (fun p : ℝ × ℝ => join (F p.1) (F p.2)) (fun p : ℝ × ℝ => F (p.1+p.2))
      (join_measurable _ _ (hF.comp measurable_fst) (hF.comp measurable_snd))
      (hF.comp ((continuous_fst.add continuous_snd).measurable))
  have hex : ∀ p, ∃ n, R p n := by
    intro p
    obtain ⟨c,hc⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp (hadd p.1 p.2)
    obtain ⟨n,hn⟩ := codeEnumeration_surjective c
    refine ⟨n, ?_⟩
    dsimp [R]
    rw [hn]
    exact hc
  exact ⟨leastSuccess R hex, leastSuccess_measurable R hex hR,
    fun x y => leastSuccess_spec R hex (x,y)⟩

theorem addition_program_continuous_restriction (F : ℝ → Oracle) (hF : Measurable F)
    (hadd : ∀ x y, Reduces (F (x + y)) (join (F x) (F y))) :
    ∃ (e : ℝ × ℝ → ℕ) (E : Set (ℝ × ℝ)), E ∈ residual (ℝ × ℝ) ∧
      ContinuousOn e E ∧ ∀ x y,
      OracleCode.eval (oracleFunction (join (F x) (F y))) (codeEnumeration (e (x,y))) =
        oracleFunction (F (x+y)) := by
  obtain ⟨e, he, hs⟩ := addition_program_selection F hF hadd
  obtain ⟨E,hE,hcont⟩ := measurable_continuousOn_residual e he
  exact ⟨e,E,hE,hcont,hs⟩

end TuringRigidity

end OAI
