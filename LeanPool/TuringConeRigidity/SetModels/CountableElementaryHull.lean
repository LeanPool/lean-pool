/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CountableElementaryHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementaryLanguage
public import Mathlib.Data.Set.Countable

/-!
# Countable Elementary Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

noncomputable def listEnv : List ZFSet.{u} → ℕ → ZFSet.{u}
  | [], _ => ∅
  | x :: _, 0 => x
  | _ :: xs, n+1 => listEnv xs n

noncomputable def envPrefix : ℕ → (ℕ → ZFSet.{u}) → List ZFSet.{u}
  | 0, _ => []
  | n+1, e => e 0 :: envPrefix n (fun i => e (i+1))

theorem prefix_agrees (n : ℕ) (e : ℕ → ZFSet.{u}) :
    ∀ i, i < n → listEnv (envPrefix n e) i = e i := by
  induction n generalizing e with
  | zero => omega
  | succ n ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => e (j+1)) i (by omega)

theorem prefix_members (n : ℕ) (e : ℕ → ZFSet.{u}) (D : Set ZFSet.{u})
    (he : ∀ i, e i ∈ D) : ∀ x ∈ envPrefix n e, x ∈ D := by
  induction n generalizing e with
  | zero => simp [envPrefix]
  | succ n ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact he 0
    · exact ih _ (fun i => he (i+1)) x hx

noncomputable def witness (p : SentenceForm) (xs : List ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ x : ZFSet.{u}, p.Sat Set.univ (cons x (listEnv xs)) then Classical.choose h else ∅

theorem witness_spec (p : SentenceForm) (xs : List ZFSet.{u})
    (h : ∃ x : ZFSet.{u}, p.Sat Set.univ (cons x (listEnv xs))) :
    p.Sat Set.univ (cons (witness p xs) (listEnv xs)) := by
  classical
  simp only [witness,dite_eq_left h]
  exact Classical.choose_spec h

noncomputable def stage (a : ℕ → ZFSet.{u}) : ℕ → Set ZFSet.{u}
  | 0 => Set.range a
  | n+1 => stage a n ∪ {x | ∃ p : SentenceForm, ∃ xs : List ZFSet.{u},
      (∀ y ∈ xs, y ∈ stage a n) ∧ x = witness p xs}

noncomputable def hull (a : ℕ → ZFSet.{u}) : Set ZFSet.{u} := ⋃ n, stage a n

theorem stage_mono (a : ℕ → ZFSet.{u}) : Monotone (stage a) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  exact Or.inl hx

theorem stage_countable (a : ℕ → ZFSet.{u}) (n : ℕ) : (stage a n).Countable := by
  induction n with
  | zero => exact Set.countable_range a
  | succ n ih =>
    apply ih.union
    let : Countable (stage a n) := ih.to_subtype
    have hc := Set.countable_range (fun z : SentenceForm × List (stage a n) =>
      witness z.1 (z.2.map Subtype.val))
    apply hc.mono
    rintro x ⟨p,xs,hxs,rfl⟩
    let ys : List (stage a n) := xs.attach.map (fun y => ⟨y.val,hxs y.val y.property⟩)
    have hy : ys.map Subtype.val = xs := by simp [ys,List.map_map]
    exact ⟨(p,ys),by simp only [hy]⟩

theorem hull_countable (a : ℕ → ZFSet.{u}) : (hull a).Countable :=
  Set.countable_iUnion (stage_countable a)

theorem parameter_mem (a : ℕ → ZFSet.{u}) (n : ℕ) : a n ∈ hull a :=
  Set.mem_iUnion.mpr ⟨0,⟨n,rfl⟩⟩

theorem list_in_stage (a : ℕ → ZFSet.{u}) (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ hull a) : ∃ n, ∀ x ∈ xs, x ∈ stage a n := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons x xs ih =>
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hxs x (by simp))
    obtain ⟨m,hm⟩ := ih (fun y hy => hxs y (by simp [hy]))
    refine ⟨max n m,?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl|hy
    · exact stage_mono a (Nat.le_max_left n m) hn
    · exact stage_mono a (Nat.le_max_right n m) (hm y hy)

theorem witness_mem (a : ℕ → ZFSet.{u}) (p : SentenceForm) (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ hull a) : witness p xs ∈ hull a := by
  obtain ⟨n,hn⟩ := list_in_stage a xs hxs
  exact Set.mem_iUnion.mpr ⟨n+1,Or.inr ⟨p,xs,hn,rfl⟩⟩

theorem hull_elementary (a : ℕ → ZFSet.{u}) : Elementary (hull a) := by
  intro p
  induction p with
  | equal => intros; rfl
  | member => intros; rfl
  | conj p q ihp ihq => intro e he; exact and_congr (ihp e he) (ihq e he)
  | neg p ih => intro e he; exact not_congr (ih e he)
  | ex p ih =>
    intro e he
    constructor
    · rintro ⟨x,hx,hp⟩
      exact ⟨x,Set.mem_univ x,(ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx])).mp hp⟩
    · rintro ⟨x,_,hp⟩
      let xs := envPrefix p.bound e
      have eq (y : ZFSet.{u}) : p.Sat Set.univ (cons y (listEnv xs)) ↔
          p.Sat Set.univ (cons y e) := by
        apply p.finite_support
        intro i hi
        cases i with
        | zero => rfl
        | succ i => exact prefix_agrees p.bound e i (by omega)
      have hw := witness_mem a p xs (prefix_members p.bound e (hull a) he)
      have hs := (eq _).mp (witness_spec p xs ⟨x,(eq x).mpr hp⟩)
      exact ⟨_,hw,(ih (cons (witness p xs) e)
        (by intro i; cases i <;> simp [cons,he,hw])).mpr hs⟩

end TuringRigidity.ElementaryModel

end OAI
