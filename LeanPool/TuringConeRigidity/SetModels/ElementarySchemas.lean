/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementarySchemas.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementaryAxioms
public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Elementary Schemas
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel SentenceForm
universe u

private def sepMap : ℕ → ℕ | 0 => 0 | i+1 => i+3
private def relationMap : ℕ → ℕ | 0 => 0 | 1 => 1 | i+2 => i+3
private def uniqueMap : ℕ → ℕ | 0 => 0 | 1 => 2 | i+2 => i+4
private def imageMap : ℕ → ℕ | 0 => 1 | 1 => 0 | i+2 => i+4

private theorem sat_sepMap (q : SentenceForm) (D : Set ZFSet.{u})
    (x b a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (q.rename sepMap).Sat D (cons x (cons b (cons a e))) ↔ q.Sat D (cons x e) := by
  rw [sat_rename]
  have he : (fun i => cons x (cons b (cons a e)) (sepMap i)) = cons x e := by
    funext i; cases i <;> rfl
  rw [he]

private theorem sat_relationMap (q : SentenceForm) (D : Set ZFSet.{u})
    (y x a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (q.rename relationMap).Sat D (cons y (cons x (cons a e))) ↔ q.Sat D (cons y (cons x e)) := by
  rw [sat_rename]
  have he : (fun i => cons y (cons x (cons a e)) (relationMap i)) = cons y (cons x e) := by
    funext i; rcases i with _|_|i <;> rfl
  rw [he]

private theorem sat_uniqueMap (q : SentenceForm) (D : Set ZFSet.{u})
    (z y x a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (q.rename uniqueMap).Sat D (cons z (cons y (cons x (cons a e)))) ↔ q.Sat D (cons z (cons x e))
      := by
  rw [sat_rename]
  have he : (fun i => cons z (cons y (cons x (cons a e))) (uniqueMap i)) = cons z (cons x e) := by
    funext i; rcases i with _|_|i <;> rfl
  rw [he]

private theorem sat_imageMap (q : SentenceForm) (D : Set ZFSet.{u})
    (x y b a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (q.rename imageMap).Sat D (cons x (cons y (cons b (cons a e)))) ↔ q.Sat D (cons y (cons x e))
      := by
  rw [sat_rename]
  have he : (fun i => cons x (cons y (cons b (cons a e))) (imageMap i)) = cons y (cons x e) := by
    funext i; rcases i with _|_|i <;> rfl
  rw [he]

theorem Valid.separate {M : ZFSet.{u}} (hv : Valid M) (q : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a : ZFSet.{u}) (ha : a ∈ M) :
    ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ x ∈ a ∧ q.Sat (M : Set ZFSet) (cons x e) := by
  let p := ex (all (iff (.member 0 1) (.conj (.member 0 2) (q.rename sepMap))))
  have hp : ∀ v : ℕ → ZFSet.{u}, p.Sat Set.univ v := by
    intro v
    let e' := fun i => v (i+1)
    have hv' : v = cons (v 0) e' := by funext i; cases i <;> rfl
    rw [hv']
    simp only
      [p,Sat,sat_all,sat_iff,sat_sepMap,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨ZFSet.sep (fun x => q.Sat Set.univ (cons x e')) (v 0),fun x => ZFSet.mem_sep⟩
  have h := hv p hp (cons a e) (by intro i; cases i <;> simp [cons,he,ha])
  simpa only [p,Sat,sat_all,sat_iff,sat_sepMap,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem ambient_image (a : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (ht : ∀ x ∈ a, ∃ y, R x y ∧ ∀ z, R x z → z = y) :
    ∃ b : ZFSet.{u}, ∀ y, y ∈ b ↔ ∃ x ∈ a, R x y := by
  classical
  let f (i : Conditions a) := Classical.choose (ht (label a i) (label_mem a i))
  have hf (i : Conditions a) : R (label a i) (f i) ∧ ∀ z, R (label a i) z → z = f i :=
    Classical.choose_spec (ht _ (label_mem a i))
  refine ⟨ZFSet.range f,?_⟩
  intro y; rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨_,label_mem a i,(hf i).1⟩
  · rintro ⟨x,hx,hr⟩
    obtain ⟨i,rfl⟩ := label_surjective a hx
    exact ⟨i,((hf i).2 y hr).symm⟩

theorem Valid.replace {M : ZFSet.{u}} (hv : Valid M) (hM : Transitive M) (q : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a : ZFSet.{u}) (ha : a ∈ M)
    (ht : ∀ x ∈ a, ∃ y ∈ M, q.Sat (M : Set ZFSet) (cons y (cons x e)) ∧
      ∀ z ∈ M, q.Sat (M : Set ZFSet) (cons z (cons x e)) → z = y) :
    ∃ b ∈ M, ∀ y ∈ M, y ∈ b ↔ ∃ x ∈ a, q.Sat (M : Set ZFSet) (cons y (cons x e)) := by
  let p := imp
    (all (imp (.member 0 1) (ex (.conj (q.rename relationMap)
      (all (imp (q.rename uniqueMap) (.equal 0 1)))))))
    (ex (all (iff (.member 0 1) (ex (.conj (.member 0 3) (q.rename imageMap))))))
  have hp : ∀ v : ℕ → ZFSet.{u}, p.Sat Set.univ v := by
    intro v
    let e' := fun i => v (i+1)
    have hv' : v = cons (v 0) e' := by funext i; cases i <;> rfl
    rw [hv']
    simp only [p,Sat,sat_all,sat_iff,sat_imp,sat_relationMap,sat_uniqueMap,sat_imageMap,
      cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ambient_image (v 0) (fun x y => q.Sat Set.univ (cons y (cons x e')))
  have h := hv p hp (cons a e) (by intro i; cases i <;> simp [cons,he,ha])
  simp only [p,Sat,sat_all,sat_iff,sat_imp,sat_relationMap,sat_uniqueMap,sat_imageMap,
    cons_zero,cons_succ] at h
  obtain ⟨b,hb,hbdef⟩ := h (fun x _ hx => ht x hx)
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy]
  exact ⟨fun ⟨x,_,hx,hr⟩ => ⟨x,hx,hr⟩,fun ⟨x,hx,hr⟩ => ⟨x,hM a ha x hx,hx,hr⟩⟩

theorem Valid.sigmaSeparation {M : ZFSet.{u}} (hv : Valid M) : SigmaSeparation M := by
  intro p e he a ha
  obtain ⟨b,hb,h⟩ := hv.separate (fromSigma p) e he a ha
  exact ⟨b,hb,fun x hx => (h x hx).trans (and_congr_right (fun _ => sigma_sat p M _))⟩

theorem Valid.sigmaReplacement {M : ZFSet.{u}} (hv : Valid M) (hM : Transitive M) :
  SigmaReplacement M := by
  intro p e he a ha ht
  obtain ⟨b,hb,h⟩ := hv.replace hM (fromSigma p) e he a ha (by
    intro x hx
    obtain ⟨y,hy,hp,hu⟩ := ht x hx
    exact ⟨y,hy,(sigma_sat p M _).mpr hp,fun z hz hpz => hu z hz ((sigma_sat p M _).mp hpz)⟩)
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [h y hy]
  apply exists_congr; intro x
  exact and_congr_right (fun _ => sigma_sat p M _)

theorem Valid.sourceT {M : ZFSet.{u}} (hv : Valid M) (hM : Transitive M)
    (hne : ∃ a, a ∈ M) : SourceT M :=
  sourceT_of_finite_schemas M hM hv.pairing hv.union hv.powerSet hv.sigmaSeparation
    (hv.sigmaReplacement hM) (hv.infinity hne) (hv.choice hM)

end TuringRigidity.ElementaryModel

end OAI
