/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/FiniteSatisfactionCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalSatisfactionSlice
public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleSuccessorCode

/-!
# Finite Satisfaction Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- List the full formula and all its subformulas recursively. -/
def subformulas : SentenceForm → List SentenceForm
  | .equal i j => [.equal i j]
  | .member i j => [.member i j]
  | .conj p q => .conj p q :: (subformulas p ++ subformulas q)
  | .neg p => .neg p :: subformulas p
  | .ex p => .ex p :: subformulas p

theorem self_mem_subformulas (p : SentenceForm) : p ∈ subformulas p := by
  cases p <;> simp [subformulas]

theorem subformulas_closed (p q : SentenceForm) (hq : q ∈ subformulas p) :
    ∀ r ∈ subformulas q, r ∈ subformulas p := by
  induction p with
  | equal i j =>
    have he : q = .equal i j := by simpa [subformulas] using hq
    subst q; exact fun _ hr => hr
  | member i j =>
    have he : q = .member i j := by simpa [subformulas] using hq
    subst q; exact fun _ hr => hr
  | conj p s ihp ihs =>
    simp only [subformulas,List.mem_cons,List.mem_append] at hq ⊢
    rcases hq with rfl|hq|hq
    · intro r hr; simpa only [subformulas,List.mem_cons,List.mem_append] using hr
    · intro r hr; exact Or.inr (Or.inl (ihp hq r hr))
    · intro r hr; exact Or.inr (Or.inr (ihs hq r hr))
  | neg p ih =>
    simp only [subformulas,List.mem_cons] at hq ⊢
    rcases hq with rfl|hq
    · intro r hr; simpa only [subformulas,List.mem_cons] using hr
    · intro r hr; exact Or.inr (ih hq r hr)
  | ex p ih =>
    simp only [subformulas,List.mem_cons] at hq ⊢
    rcases hq with rfl|hq
    · intro r hr; simpa only [subformulas,List.mem_cons] using hr
    · intro r hr; exact Or.inr (ih hq r hr)

/-- The set-coded satisfaction relation for the formulas in the finite list over `A`. -/
noncomputable def finiteSatisfaction (A : ZFSet.{u}) (ps : List SentenceForm) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun i : Fin ps.length =>
    ZFSet.prod ({natSet (Encodable.encode ps[i])} : ZFSet.{u}) (truthSlice A ps[i])))

theorem mem_finiteSatisfaction (A z : ZFSet.{u}) (ps : List SentenceForm) :
    z ∈ finiteSatisfaction A ps ↔ ∃ p ∈ ps, ∃ t ∈ truthSlice A p,
      z = ZFSet.pair (natSet (Encodable.encode p)) t := by
  rw [finiteSatisfaction,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨s,hs,hz⟩
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hs
    obtain ⟨k,hk,t,ht,hz⟩ := ZFSet.mem_prod.mp hz
    rw [ZFSet.mem_singleton] at hk
    subst k
    exact ⟨ps[i],List.getElem_mem i.isLt,t,ht,hz⟩
  · rintro ⟨p,hp,t,ht,rfl⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hp
    refine ⟨_,ZFSet.mem_range_self ⟨i,hi⟩,?_⟩
    exact ZFSet.mem_prod.mpr ⟨_,ZFSet.mem_singleton.mpr rfl,t,ht,rfl⟩

theorem finiteSatisfaction_record (A : ZFSet.{u}) (ps : List SentenceForm)
    (p : SentenceForm) {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ finiteSatisfaction A ps ↔
      p ∈ ps ∧ p.bound ≤ n ∧ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  rw [mem_finiteSatisfaction]
  constructor
  · rintro ⟨q,hq,t,ht,he⟩
    obtain ⟨hc,ht'⟩ := ZFSet.pair_inj.mp he
    have hpq : p = q := Encodable.encode_injective (natSet_injective hc)
    subst q; subst t
    exact ⟨hq,(truthSlice_record A p v hv).mp ht⟩
  · rintro ⟨hp,hb,hs⟩
    exact ⟨p,hp,tupleCode v,(truthSlice_record A p v hv).mpr ⟨hb,hs⟩,rfl⟩

theorem finiteSatisfaction_mem (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (ps : List SentenceForm) : finiteSatisfaction A ps ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  apply union_mem M hM hT.union
  apply finite_range_mem M hM hT.pairing hT.union (hn 0)
  intro i
  exact product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing (hn _)) (truthSlice_mem M A hM hT hA ps[i])

theorem finiteSatisfaction_subset (A : ZFSet.{u}) (ps : List SentenceForm) :
    finiteSatisfaction A ps ⊆ satisfactionSet A := by
  intro z hz
  obtain ⟨p,_,t,ht,rfl⟩ := (mem_finiteSatisfaction A z ps).mp hz
  exact (ZFSet.mem_sep.mp ht).2

theorem finiteSatisfaction_covers (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ finiteSatisfaction A (subformulas p) ↔
      ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ satisfactionSet A := by
  rw [finiteSatisfaction_record A _ p v hv,satisfactionSet_record A p v hv]
  exact and_iff_right (self_mem_subformulas p)

/-- The formula-and-tuple code belongs to the supplied satisfaction relation. -/
def accepts (S : ZFSet.{u}) (p : SentenceForm) {n : ℕ} (v : Fin n → ZFSet.{u}) : Prop :=
  ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ S

theorem certificate_correct (A : ZFSet.{u}) (root p : SentenceForm)
    (hp : p ∈ subformulas root) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n) :
    accepts (finiteSatisfaction A (subformulas root)) p v ↔ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  rw [accepts,finiteSatisfaction_record A _ p v hv]
  exact ⟨fun h => h.2.2,fun h => ⟨hp,hb,h⟩⟩

theorem certificate_conj (A : ZFSet.{u}) (root p q : SentenceForm)
    (hp : SentenceForm.conj p q ∈ subformulas root) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) (hb : (SentenceForm.conj p q).bound ≤ n) :
    accepts (finiteSatisfaction A (subformulas root)) (.conj p q) v ↔
      accepts (finiteSatisfaction A (subformulas root)) p v ∧
      accepts (finiteSatisfaction A (subformulas root)) q v := by
  have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
  have hq' := subformulas_closed root _ hp q (by simp [subformulas,self_mem_subformulas])
  have hbp : p.bound ≤ n := by simp only [SentenceForm.bound] at hb; omega
  have hbq : q.bound ≤ n := by simp only [SentenceForm.bound] at hb; omega
  rw [certificate_correct A root _ hp v hv hb,certificate_correct A root p hp' v hv hbp,
    certificate_correct A root q hq' v hv hbq]
  rfl

theorem certificate_neg (A : ZFSet.{u}) (root p : SentenceForm)
    (hp : SentenceForm.neg p ∈ subformulas root) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n) :
    accepts (finiteSatisfaction A (subformulas root)) (.neg p) v ↔
      ¬ accepts (finiteSatisfaction A (subformulas root)) p v := by
  have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
  rw [certificate_correct A root _ hp v hv hb,certificate_correct A root p hp' v hv hb]
  rfl

theorem certificate_ex (A : ZFSet.{u}) (root p : SentenceForm)
    (hp : SentenceForm.ex p ∈ subformulas root) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) (hb : (SentenceForm.ex p).bound ≤ n) :
    accepts (finiteSatisfaction A (subformulas root)) (.ex p) v ↔
      ∃ x ∈ A, accepts (finiteSatisfaction A (subformulas root)) p (Fin.cases x v) := by
  have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
  have hbp : p.bound ≤ n+1 := by simp only [SentenceForm.bound] at hb; omega
  rw [certificate_correct A root _ hp v hv hb]
  change (∃ x ∈ A, p.Sat (A : Set ZFSet) (cons x (tupleEnv v))) ↔ _
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  rw [certificate_correct A root p hp' (Fin.cases x v) (fun i => Fin.cases hx hv i) hbp,
    tupleEnv_cons]

end TuringRigidity.RelativeConstructible

end OAI
