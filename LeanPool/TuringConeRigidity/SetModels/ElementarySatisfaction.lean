/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementarySatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementaryCollapse

/-!
# Elementary Satisfaction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

theorem SentenceForm.collapse_sat (p : SentenceForm) (d : ZFSet.{u})
    (hd : StructureExtensional d) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ d) :
    p.Sat (d : Set ZFSet) e ↔ p.Sat (collapsed d : Set ZFSet) (fun i => structureMap d (e i)) := by
  induction p generalizing e with
  | equal i j => exact ⟨congrArg (structureMap d),collapse_injective d hd _ (he i) _ (he j)⟩
  | member i j => exact (collapse_membership d hd _ (he i) _ (he j)).symm
  | conj p q ihp ihq => exact and_congr (ihp e he) (ihq e he)
  | neg p ih => exact not_congr (ih e he)
  | ex p ih =>
    have hen (x : ZFSet.{u}) (hx : x ∈ d) : ∀ i, cons x e i ∈ d := by
      intro i; cases i <;> simp [cons,he,hx]
    constructor
    · rintro ⟨x,hx,hp⟩
      refine ⟨_,(mem_collapsed d _).mpr ⟨x,hx,rfl⟩,?_⟩
      have h := (ih (cons x e) (hen x hx)).mp hp
      rwa [map_cons] at h
    · rintro ⟨y,hy,hp⟩
      obtain ⟨x,hx,rfl⟩ := (mem_collapsed d y).mp hy
      refine ⟨x,hx,(ih (cons x e) (hen x hx)).mpr ?_⟩
      rwa [map_cons]

def Valid (M : ZFSet.{u}) : Prop :=
  ∀ p : SentenceForm, (∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e) →
    ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) → p.Sat (M : Set ZFSet) e

theorem collapsed_hull_valid (a : ℕ → ZFSet.{u}) : Valid (collapsed (hullSet a)) := by
  intro p hp e he
  choose f hf heq using fun i => (mem_collapsed (hullSet a) (e i)).mp (he i)
  have hfe : (fun i => structureMap (hullSet a) (f i)) = e := by
    funext i; exact (heq i).symm
  have hh : (hullSet a : Set ZFSet) = hull a := by ext x; exact mem_hullSet a x
  have hs : p.Sat (hullSet a : Set ZFSet) f := by
    rw [hh]
    exact (hull_elementary a p f (fun i => (mem_hullSet a _).mp (hf i))).mpr (hp f)
  have ht := (p.collapse_sat (hullSet a) (hullSet_extensional a) f hf).mp hs
  rwa [hfe] at ht

noncomputable def fromBounded : Formula → SentenceForm
  | .equal i j => .equal i j
  | .member i j => .member i j
  | .conj p q => .conj (fromBounded p) (fromBounded q)
  | .neg p => .neg (fromBounded p)
  | .existsMem i p => .ex (.conj (.member 0 (i+1)) (fromBounded p))

theorem bounded_sat (p : Formula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromBounded p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp e) (ihq e)
  | neg p ih => exact not_congr (ih e)
  | existsMem i p ih =>
    simp only [fromBounded,SentenceForm.Sat,Formula.Realize,cons_zero,cons_succ]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => and_congr_right (fun _ => ih (cons x e)))

theorem bounded_univ (p : Formula) (e : ℕ → ZFSet.{u}) :
    (fromBounded p).Sat Set.univ e ↔ p.Eval e := by
  induction p generalizing e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp e) (ihq e)
  | neg p ih => exact not_congr (ih e)
  | existsMem i p ih =>
    simp only [fromBounded,SentenceForm.Sat,Formula.Eval,cons_zero,cons_succ,Set.mem_univ,true_and]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

noncomputable def fromSigma : SigmaFormula → SentenceForm
  | .bounded p => fromBounded p
  | .existsSet p => .ex (fromSigma p)

theorem sigma_sat (p : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromSigma p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | bounded p => exact bounded_sat p M e
  | existsSet p ih =>
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

end TuringRigidity.ElementaryModel

end OAI
