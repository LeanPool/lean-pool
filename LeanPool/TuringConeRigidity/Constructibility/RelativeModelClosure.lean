/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModel
public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleSeparation

/-!
# Relative Model Closure
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem finite_parameters_in_relative_level (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (e : ℕ → ZFSet.{u}) (n : ℕ)
    (he : ∀ i, i < n → InRelativeModel M R (e i)) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ ∀ i, i < n → e i ∈ level R o := by
  induction n with
  | zero => exact ⟨0,internal_ordinal_zero M hM hT,fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | succ n ih =>
    obtain ⟨o,ho,hoe⟩ := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    obtain ⟨p,hp,hpe⟩ := he n (Nat.lt_succ_self n)
    refine ⟨max o p,internal_ordinal_max M ho hp,fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
    · exact level_mono R (le_max_left o p) (hoe i hi)
    · exact level_mono R (le_max_right o p) hpe

theorem empty_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : InRelativeModel M R ∅ := by
  refine ⟨0+1,internal_ordinal_succ M hM hT 0 (internal_ordinal_zero M hM hT),?_⟩
  rw [level_succ]
  exact empty_mem_definablePower _

theorem pair_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {a b : ZFSet.{u}}
    (ha : InRelativeModel M R a) (hb : InRelativeModel M R b) :
    InRelativeModel M R ({a,b} : ZFSet.{u}) := by
  obtain ⟨i,hi,hia⟩ := ha
  obtain ⟨j,hj,hjb⟩ := hb
  refine ⟨max i j+1,internal_ordinal_succ M hM hT _ (internal_ordinal_max M hi hj),?_⟩
  rw [level_succ]
  exact pair_mem_definablePower _ a b (level_mono R (le_max_left i j) hia)
    (level_mono R (le_max_right i j) hjb)

theorem union_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {a : ZFSet.{u}} (ha : InRelativeModel M R a) :
    InRelativeModel M R (ZFSet.sUnion a) := by
  obtain ⟨i,hi,hia⟩ := ha
  refine ⟨i+1,internal_ordinal_succ M hM hT i hi,?_⟩
  rw [level_succ]
  exact union_mem_definablePower _ a (level_transitive R i) hia

theorem bounded_separation_in_relativeModel (M R a : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (ha : InRelativeModel M R a)
    (φ : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, i < (fromBounded φ).bound → InRelativeModel M R (e i)) :
    InRelativeModel M R (a.sep (fun x => φ.Eval (cons x e))) := by
  obtain ⟨i,hi,hia⟩ := ha
  obtain ⟨j,hj,hje⟩ := finite_parameters_in_relative_level M R hM hT e _ he
  let A := level R (max i j)
  have haA : a ∈ A := level_mono R (le_max_left i j) hia
  let e' : ℕ → ZFSet.{u} := fun n => if n < (fromBounded φ).bound then e n else a
  have heA : ∀ n, e' n ∈ A := by
    intro n
    dsimp [e']; split
    next hn => exact level_mono R (le_max_right i j) (hje n hn)
    next => exact haA
  have heval (x : ZFSet.{u}) : φ.Eval (cons x e') ↔ φ.Eval (cons x e) := by
    rw [← bounded_univ,← bounded_univ]
    apply (fromBounded φ).finite_support
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      change e' k = e k
      simp [e',show k < (fromBounded φ).bound by omega]
  have heq : a.sep (fun x => φ.Eval (cons x e')) = a.sep (fun x => φ.Eval (cons x e)) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,heval]
  refine ⟨max i j+1,internal_ordinal_succ M hM hT _ (internal_ordinal_max M hi hj),?_⟩
  rw [level_succ,← heq]
  exact bounded_separation_mem_definablePower A a (level_transitive R _) haA φ e' heA

theorem relativeModel_pairing (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : Pairing (relativeModel M R) := by
  intro a ha b hb
  have mem := mem_relativeModel M R
  refine ⟨{a,b},(mem _ hM hT hR).mpr (pair_in_relativeModel M R hM hT
    ((mem _ hM hT hR).mp ha) ((mem _ hM hT hR).mp hb)),?_⟩
  intro x _; exact ZFSet.mem_pair

theorem relativeModel_union (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : BoundedSetTheory.Union (relativeModel M R) := by
  intro a ha
  refine ⟨ZFSet.sUnion a,(mem_relativeModel M R _ hM hT hR).mpr
    (union_in_relativeModel M R hM hT ((mem_relativeModel M R a hM hT hR).mp ha)),?_⟩
  intro x _
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y,hy,hx⟩
    exact ⟨y,relativeModel_transitive M R hM a ha y hy,hy,hx⟩
  · rintro ⟨y,_,hy,hx⟩; exact ⟨y,hy,hx⟩

theorem relativeModel_bounded_separation (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : Separation (relativeModel M R) := by
  intro φ e he a ha
  have mem := mem_relativeModel M R
  refine ⟨a.sep (fun x => φ.Eval (cons x e)),(mem _ hM hT hR).mpr
    (bounded_separation_in_relativeModel M R a hM hT ((mem _ hM hT hR).mp ha)
      φ e (fun i _ => (mem _ hM hT hR).mp (he i))),?_⟩
  intro x hx
  rw [ZFSet.mem_sep,Formula.absolute φ _ (relativeModel_transitive M R hM) _ (by
    intro i
    cases i
    · exact hx
    · exact he _)]

theorem ground_relativeModel_omega (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : ZFSet.omega ∈ relativeModel M (groundReals M) := by
  exact (relativeModel_ground_reals M hM hT _ (fun _ hx => hx)).mpr
    (sourceT_omega_mem M hM hT)

theorem ground_relativeModel_infinity (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : Infinity (relativeModel M (groundReals M)) := by
  have hω := ground_relativeModel_omega M hM hT
  have ht := relativeModel_transitive M (groundReals M) hM
  refine ⟨ZFSet.omega,hω,⟨∅,ht _ hω _ ZFSet.omega_zero,ZFSet.omega_zero,
    fun z _ => ZFSet.notMem_empty z⟩,?_⟩
  intro x _ hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  have hs := (mem_omega _).mpr ⟨n+1,rfl⟩
  exact ⟨natSet (n+1),ht _ hω _ hs,hs,fun _ _ => ZFSet.mem_insert_iff⟩

end TuringRigidity.RelativeConstructible

end OAI
