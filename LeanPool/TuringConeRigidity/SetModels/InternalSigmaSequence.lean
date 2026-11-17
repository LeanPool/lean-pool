/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalSigmaSequence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaSequenceTrace

/-!
# Internal Sigma Sequence
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel BoundedDefinability SetModelFunctions SetModelIteration
  RelativeConstructible
universe u

theorem sequenceValue_sigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : SigmaDefinable M (fun e => S (e 1) (e 0)))
    (x : ZFSet.{u}) (hx : x ∈ M) :
    SigmaDefinable M (fun e => ∃ z ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
      SequenceTrace M S (e 1) x (e 0) d r f z) := by
  have ht := (sequenceTrace_sigma M hM hT S hS).subst
    (fun i => match i with | 0 => 5 | 1 => 6 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 2 | _ => 3)
  have hv := ht.existsSet.existsSet.existsSet.existsSet
  have hs := hv.subst (fun i => if i=0 then 1 else if i=1 then 2 else 0)
  have h := (((equal_param hx 0).toSigma hM).and hs).existsSet
  apply h.congr
  intro e _
  change (∃ x' ∈ M, x'=x ∧ ∃ z ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
    SequenceTrace M S (e 1) x' (e 0) d r f z) ↔ _
  exact ⟨fun ⟨_,_,he,hv⟩ => he ▸ hv,fun hv => ⟨x,hx,rfl,hv⟩⟩

theorem sigma_sequence_range_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : SigmaDefinable M (fun e => S (e 1) (e 0)))
    (s : ℕ → ZFSet.{u}) (hs : ∀ n, s n ∈ M)
    (hstep : ∀ n, S (s n) (s (n + 1)))
    (hunique : ∀ n y, S (s n) y → y = s (n + 1)) :
    ∃ B ∈ M, ∀ y, y ∈ B ↔ ∃ n, y = s n := by
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation
    (fun n y => ∃ z ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
      SequenceTrace M S n (s 0) y d r f z)
    (sequenceValue_sigma M hM hT S hS (s 0) (hs 0))
  have hω := sourceT_omega_mem M hM hT
  have hv (n : ℕ) (y : ZFSet.{u}) (hy : y ∈ M) :
      p.Realize M (cons y (cons (natSet n) e)) ↔ y = s n := by
    rw [hp _ (hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)) y hy]
    constructor
    · rintro ⟨z,_,f,_,r,_,d,_,h⟩
      exact SequenceTrace.correct M S s hunique n h
    · rintro rfl
      exact sequenceTrace_exists M hM hT S s hs hstep n
  obtain ⟨B,hB,hdef⟩ := hT.replacement.finitePrefix p e he ZFSet.omega hω (by
    intro n hn
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨s n,hs n,(hv n (s n) (hs n)).mpr rfl,
      fun y hy h => (hv n y hy).mp h⟩)
  refine ⟨B,hB,?_⟩
  intro y
  constructor
  · intro hy
    have hyM := hM B hB y hy
    obtain ⟨n,hn,h⟩ := (hdef y hyM).mp hy
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,(hv n y hyM).mp h⟩
  · rintro ⟨n,rfl⟩
    exact (hdef (s n) (hs n)).mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,
      (hv n (s n) (hs n)).mpr rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
