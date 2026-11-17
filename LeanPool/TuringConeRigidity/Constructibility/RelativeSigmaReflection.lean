/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeSigmaReflection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeSigmaWitness

/-!
# Relative Sigma Reflection
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel InternalRank
universe u

theorem relative_sigma_reflection (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (i : Ordinal.{u}) (hi : i.toZFSet ∈ M)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ n, e n ∈ level R i)
    (a : ZFSet.{u}) (ha : a ∈ level R i) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ level R i ⊆ level R o ∧
      ∀ x ∈ a, φ.Realize (relativeModel M R) (cons x e) ↔
        φ.Realize (level R o) (cons x e) := by
  have ht := level_mem M R hM hT hR i hi
  have haM := hM _ ht a ha
  have heM : ∀ n, cons (level R i) e n ∈ M := by
    intro n
    cases n
    · exact ht
    · exact hM _ ht _ (he _)
  obtain ⟨W,hW,hw⟩ := sigmaDefinable_request_bound
    (relative_sigma_request_definable M R hM hT hR φ) hM hT (cons (level R i) e) heM haM
  have hr : W.rank.toZFSet ∈ M := by
    rw [← rankSet_eq_ordinal]
    exact rankSet_mem_ground M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hW
  let o := max i W.rank
  have ho : o.toZFSet ∈ M := internal_ordinal_max M hi hr
  have hio : level R i ⊆ level R o := level_mono R (le_max_left i W.rank)
  refine ⟨o,ho,hio,?_⟩
  intro x hx
  have heI : ∀ n, cons x e n ∈ level R i := by
    intro n
    cases n
    · exact level_transitive R i a ha x hx
    · exact he _
  constructor
  · intro hφ
    obtain ⟨j,hj,hij,hφj⟩ := relative_sigma_level_witness M R hM hT hR i hi φ (cons x e) heI hφ
    obtain ⟨z,hz,hord,htz,hφz⟩ := hw x hx ⟨j.toZFSet,hj,ZFSet.isOrdinal_toZFSet j,hij,hφj⟩
    change z.IsOrdinal at hord
    change level R i ⊆ stage R z at htz
    change φ.Realize (stage R z) (cons x e) at hφz
    have heq : stage R z = level R z.rank := by
      change stage R z = stage R z.rank.toZFSet
      rw [hord.toZFSet_rank_eq]
    rw [heq] at htz hφz
    exact φ.transitive_upward (level_transitive R _) (level_transitive R _)
      (level_mono R ((ZFSet.rank_lt_of_mem hz).le.trans (le_max_right i W.rank)))
      (cons x e) (fun n => htz (heI n)) hφz
  · intro hφ
    exact φ.transitive_upward (level_transitive R o) (relativeModel_transitive M R hM)
      (relative_level_subset M R hM hT hR ho) (cons x e) (fun n => hio (heI n)) hφ

theorem relative_sigma_parameter_bound (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (φ : SigmaFormula) (e : ℕ → ZFSet.{u})
    (he : ∀ n, InRelativeModel M R (e n)) (a : ZFSet.{u})
    (ha : InRelativeModel M R a) :
    ∃ i : Ordinal.{u}, i.toZFSet ∈ M ∧ a ∈ level R i ∧
      ∃ e' : ℕ → ZFSet.{u}, (∀ n, e' n ∈ level R i) ∧ (∀ n, n < φ.scope → e' n = e n) ∧
        ∀ N x : ZFSet.{u}, φ.Realize N (cons x e') ↔ φ.Realize N (cons x e) := by
  obtain ⟨i,hi,hia⟩ := ha
  obtain ⟨j,hj,hje⟩ := finite_parameters_in_relative_level M R hM hT e φ.scope (fun n _ => he n)
  let e' := fun n => if n < φ.scope then e n else a
  have haL : a ∈ level R (max i j) := level_mono R (le_max_left i j) hia
  refine ⟨max i j,internal_ordinal_max M hi hj,haL,e',?_,?_,?_⟩
  · intro n
    dsimp [e']; split
    next hn => exact level_mono R (le_max_right i j) (hje n hn)
    next => exact haL
  · intro n hn; exact ite_eq_left hn
  · intro N x
    apply φ.realize_congr; intro n hn
    cases n with
    | zero => rfl
    | succ n => exact ite_eq_left (show n < φ.scope by omega)

theorem relativeModel_sigma_collection (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaCollection (relativeModel M R) := by
  intro φ e he a ha htotal
  obtain ⟨i,hi,hia,e',he',heq,hcongr⟩ := relative_sigma_parameter_bound M R hM hT
    (.existsSet φ) e (fun n => (mem_relativeModel M R _ hM hT hR).mp (he n)) a
    ((mem_relativeModel M R _ hM hT hR).mp ha)
  obtain ⟨o,ho,hio,hφ⟩ := relative_sigma_reflection M R hM hT hR i hi (.existsSet φ) e' he' a hia
  have hlevel := relative_level_subset M R hM hT hR ho
  refine ⟨level R o,(mem_relativeModel M R _ hM hT hR).mpr
    (level_in_relativeModel M R hM hT o ho),?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := (hφ x hx).mp ((hcongr _ x).mpr (htotal x hx))
  have hup : φ.Realize (relativeModel M R) (cons y (cons x e')) :=
    φ.transitive_upward (level_transitive R o) (relativeModel_transitive M R hM)
      hlevel (cons y (cons x e')) (by
        intro n
        rcases n with _ | n
        · exact hy
        rcases n with _ | n
        · exact hio (level_transitive R i a hia x hx)
        exact hio (he' n)) hxy
  refine ⟨y,hy,?_⟩
  apply (φ.realize_congr (relativeModel M R) (cons y (cons x e')) (cons y (cons x e)) ?_).mp hup
  intro n hn
  rcases n with _ | n
  · rfl
  rcases n with _ | n
  · rfl
  exact heq n (by change n < φ.scope-1; omega)

end TuringRigidity.RelativeConstructible

end OAI
