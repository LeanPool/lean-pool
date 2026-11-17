/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SentenceInlining.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.FiniteGraphSatisfaction
public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction

/-!
# Sentence Inlining
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def skipValue (i : ℕ) : ℕ := match i with | 0 => 0 | j+1 => j+2

theorem skipValue_env (x y : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fun i => cons x (cons y e) (skipValue i)) = cons x e := by
  funext i; cases i <;> rfl

def bindComputed : ℕ → (ℕ → SentenceForm) → SentenceForm → SentenceForm
  | 0, _, p => p
  | n+1, f, p => .ex (.conj (f n)
      (bindComputed n (fun i => (f i).rename skipValue) p))

theorem bindComputed_spec (M : ZFSet.{u}) (n : ℕ)
    (f : ℕ → SentenceForm) (p : SentenceForm) (e w : ℕ → ZFSet.{u})
    (hw : ∀ i, i < n → w i ∈ M)
    (hf : ∀ i, i < n → ∀ x ∈ M,
      (f i).Sat (M : Set ZFSet) (cons x e) ↔ x = w i) :
    (bindComputed n f p).Sat (M : Set ZFSet) e ↔
      p.Sat (M : Set ZFSet) (prependValues w n e) := by
  induction n generalizing f e with
  | zero => rfl
  | succ n ih =>
    have hf' (y : ZFSet.{u}) : ∀ i, i < n → ∀ x ∈ M,
        ((f i).rename skipValue).Sat (M : Set ZFSet) (cons x (cons y e)) ↔ x = w i := by
      intro i hi x hx
      rw [SentenceForm.sat_rename,skipValue_env]
      exact hf i (by omega) x hx
    change (∃ x ∈ M, (f n).Sat (M : Set ZFSet) (cons x e) ∧
      (bindComputed n (fun i => (f i).rename skipValue) p).Sat
        (M : Set ZFSet) (cons x e)) ↔ _
    constructor
    · rintro ⟨x,hx,hfx,hp⟩
      obtain rfl := (hf n (by omega) x hx).mp hfx
      exact (ih _ _ (fun i hi => hw i (by omega)) (hf' (w n))).mp hp
    · intro hp
      exact ⟨w n,hw n (by omega),(hf n (by omega) _ (hw n (by omega))).mpr rfl,
        (ih _ _ (fun i hi => hw i (by omega)) (hf' (w n))).mpr hp⟩

noncomputable def subsetBody (n out a : ℕ) (p : SentenceForm) : SentenceForm :=
  SentenceForm.all (SentenceForm.iff (.member 0 (n+out+1))
    (.conj (.member 0 (n+a+1)) (fromBounded (setBounded p (n+a+1) id))))

theorem subsetBody_spec (M : ZFSet.{u}) (hM : Transitive M)
    (n out a : ℕ) (p : SentenceForm) (hp : p.bound ≤ n + 1)
    (e w : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (hw : ∀ i, i < n → w i ∈ M) :
    (subsetBody n out a p).Sat (M : Set ZFSet) (prependValues w n e) ↔
      e out = definedSubset (e a) p (fun i : Fin n => w i) := by
  have hpre (i : ℕ) : prependValues w n e i ∈ M := by
    by_cases hi : i < n
    · rw [prependValues_lt _ _ _ _ hi]; exact hw i hi
    · have hi' : i = n+(i-n) := by omega
      rw [hi',prependValues_tail]; exact he _
  have htruth (x : ZFSet.{u}) (hx : x ∈ M) :
      (fromBounded (setBounded p (n+a+1) id)).Sat (M : Set ZFSet)
        (cons x (prependValues w n e)) ↔
      p.Sat (e a : Set ZFSet) (cons x (tupleEnv (fun i : Fin n => w i))) := by
    rw [bounded_sat,setBounded_absolute p M hM _ _ _
      (by
        intro i
        cases i
        · exact hx
        · exact hpre _)]
    simp only [cons_succ,prependValues_tail,id_eq]
    apply p.finite_support
    intro i hi
    cases i with
    | zero => rfl
    | succ i =>
      change prependValues w n e i = tupleEnv (fun j : Fin n => w j) i
      rw [prependValues_lt _ _ _ _ (by omega)]
      simp [tupleEnv,show i < n by omega]
  simp only [subsetBody,SentenceForm.sat_all,SentenceForm.sat_iff,SentenceForm.Sat,
    cons_zero,cons_succ,prependValues_tail]
  constructor
  · intro h
    apply ZFSet.ext; intro x
    rw [mem_definedSubset]
    constructor
    · intro hx
      have hxM := hM _ (he out) x hx
      obtain ⟨ha,ht⟩ := (h x hxM).mp hx
      exact ⟨ha,(htruth x hxM).mp ht⟩
    · rintro ⟨ha,ht⟩
      have hxM := hM _ (he a) x ha
      exact (h x hxM).mpr ⟨ha,(htruth x hxM).mpr ht⟩
  · intro h x hx
    rw [h,mem_definedSubset]
    exact and_congr Iff.rfl (htruth x hx).symm

end TuringRigidity.RelativeConstructible

end OAI
