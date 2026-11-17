/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericalCohenSets.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenWordCodeGraph
public import LeanPool.TuringConeRigidity.SetModels.ModelArithmeticComprehension

/-!
# Numerical Cohen Sets
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable

noncomputable def wordPullback (D : ZFSet.{0}) : Oracle := fun n => by
  classical
  exact decide (wordCode (EncodedForcing.word n) ∈ D)

theorem wordPullback_true (D : ZFSet.{0}) (n : ℕ) :
    wordPullback D n = true ↔ wordCode (EncodedForcing.word n) ∈ D := by
  classical
  simp [wordPullback]

theorem wordPullback_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (D : ZFSet.{0}) (hD : D ∈ M) : realCode (wordPullback D) ∈ M := by
  let e := cons D (fun _ => wordCodeGraph)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i with
    | zero => exact hD
    | succ i => exact wordCodeGraph_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 1 0 3)) e he (sourceT_omega_mem M hM hT)
  have heq : ZFSet.sep (fun n =>
      (Formula.existsMem 1 (.pairMem 1 0 3)).Eval (cons n e)) ZFSet.omega =
      realCode (wordPullback D) := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_sep,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨hx,q,hq,hxq⟩
      obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      rw [(pair_mem_wordCodeGraph n q).mp hxq] at hq
      exact (natSet_mem_realCode _ _).mpr ((wordPullback_true D n).mpr hq)
    · intro hx
      obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
      exact ⟨(mem_omega _).mpr ⟨n,rfl⟩,wordCode (EncodedForcing.word n),
        (wordPullback_true D n).mp ((natSet_mem_realCode _ _).mp hx),
        (pair_mem_wordCodeGraph _ _).mpr rfl⟩
  exact heq ▸ hh

noncomputable def wordImage (A : Oracle) : ZFSet.{0} :=
  ZFSet.sep (fun q => ∃ n ∈ realCode A, ZFSet.pair n q ∈ wordCodeGraph) conditions

theorem wordImage_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : realCode A ∈ M) : wordImage A ∈ M := by
  let e := cons (realCode A) (fun _ => wordCodeGraph)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i with
    | zero => exact hA
    | succ i => exact wordCodeGraph_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 0 1 3)) e he (conditions_mem M hM hT)
  simpa only [wordImage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using hh

theorem wordImage_spec (P : List Bool → Prop) (A : Oracle)
    (hA : ∀ n, A n = true ↔ P (EncodedForcing.word n)) (p : List Bool) :
    wordCode p ∈ wordImage A ↔ P p := by
  rw [wordImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,hq⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
    have hp := wordCode_injective ((pair_mem_wordCodeGraph _ _).mp hq)
    rw [hp]
    exact (hA n).mp ((natSet_mem_realCode _ _).mp hx)
  · intro hp
    exact ⟨(mem_conditions _).mpr ⟨_,wordCode_function _⟩,natSet (encode p),
      (natSet_mem_realCode _ _).mpr ((hA _).mpr (by simpa [EncodedForcing.word] using hp)),
      (canonical_wordCodeGraph p _).mpr rfl⟩

end TuringRigidity.InternalCohen

end OAI
