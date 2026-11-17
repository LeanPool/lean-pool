/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/SingleRealConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.RealProjectionSyntax

/-!
# Single Real Construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

def bitOracle (P : Oracle) (bs : List Bool) : Oracle := fun n => P (bitIndex bs n)

theorem bitOracle_part (P : Oracle) (bs : List Bool) (i : ℕ) :
    realPart (bitOracle P bs) i = bitOracle P (bs ++ partBits i) := by
  funext n
  rw [realPart_bits]
  simp only [bitOracle,bitIndex_append]

noncomputable def Construction.stageInputs (R : ZFSet.{u}) (t : Construction.{u}) (k : ℕ) :
  ZFSet.{u} :=
  match t.inputData k with
  | .stage o => level R o
  | _ => R

theorem Construction.stageInputs_child (R : ZFSet.{u})
    (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm) (c : Fin n → Construction.{u})
    (i : Fin n) (k : ℕ) :
    (Construction.define o n p c).stageInputs R (Nat.pair i k+1) = (c i).stageInputs R k := by
  simp only [Construction.stageInputs,Construction.inputData,Nat.unpair_pair]
  rw [dite_eq_left i.isLt]
  cases (c i).inputData k <;> rfl

theorem Construction.stageInputs_mem (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) (hi : t.Indexed M) :
    ∀ k, t.stageInputs R k ∈ M := by
  intro k
  have hk := t.inputData_indexed M hi k
  unfold Construction.stageInputs
  cases hd : t.inputData k with
  | reals => exact hR
  | realPath path => exact hR
  | stage o =>
    rw [hd] at hk
    exact level_mem M R hM hT hR o hk

noncomputable def Construction.singleFormula : Construction.{u} → List Bool →
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ) → SentenceForm
  | .reals, _, out, R, _, _, _, _, _ => .equal out R
  | .parameter, bs, out, _, P, w, a, d, _ => projectionFormula bs out w a d P
  | .define _ n p c, bs, out, R, P, w, a, d, r => bindComputed n
      (fun i => if h : i < n then
        (c ⟨i,h⟩).singleFormula (bs ++ partBits i) 0 (R+1) (P+1) (w+1) (a+1) (d+1)
          (fun k => r (Nat.pair i k+1)+1)
        else .equal 0 0)
      (subsetBody n out (r 0) p)

theorem Construction.singleFormula_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (P : Oracle) (bs : List Bool)
    (ht : t.Certified R (bitOracle P bs))
    (out rR rP w a d : ℕ) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hRR : e rR = R) (hPP : e rP = realCode P) (hw : e w = ZFSet.omega)
    (ha : e a = additionSet) (hd : e d = pairNumbers)
    (hr : ∀ k, e (r k) = t.stageInputs R k) :
    (t.singleFormula bs out rR rP w a d r).Sat (M : Set ZFSet) e ↔
      e out = t.value R (bitOracle P bs) := by
  induction t generalizing bs out rR rP w a d r e with
  | reals => exact Iff.of_eq (congrArg (e out = ·) hRR)
  | parameter => exact projectionFormula_spec M hM bs out w a d rP e he hw ha hd P hPP
  | define o n p c ih =>
    let v : ℕ → ZFSet.{u} := fun i => if h : i < n then
      (c ⟨i,h⟩).value R (realPart (bitOracle P bs) i) else R
    have hv (i : ℕ) (hin : i < n) : v i ∈ M := by
      dsimp [v]; rw [dite_eq_left hin]
      exact hM _ (show level R o ∈ M from (show e (r 0) = level R o from hr 0) ▸ he (r 0)) _ (ht.2
        ⟨i,hin⟩).2
    have hf (i : ℕ) (hin : i < n) (x : ZFSet.{u}) (hx : x ∈ M) :
        (if h : i < n then
          (c ⟨i,h⟩).singleFormula (bs ++ partBits i) 0 (rR+1) (rP+1) (w+1) (a+1) (d+1)
            (fun k => r (Nat.pair i k+1)+1) else .equal 0 0).Sat
          (M : Set ZFSet) (cons x e) ↔ x = v i := by
      rw [dite_eq_left hin,show v i = (c ⟨i,hin⟩).value R (realPart (bitOracle P bs) i) from
        dite_eq_left hin,
        bitOracle_part]
      have hc : (c ⟨i,hin⟩).Certified R (bitOracle P (bs ++ partBits i)) := by
        rw [← bitOracle_part]; exact (ht.2 ⟨i,hin⟩).1
      apply ih ⟨i,hin⟩ _ hc 0 (rR+1) (rP+1) (w+1) (a+1) (d+1)
        (fun k => r (Nat.pair i k+1)+1) (cons x e)
        (by
          intro k
          cases k
          · exact hx
          · exact he _) hRR hPP hw ha hd
      intro k
      change e (r (Nat.pair i k+1)) = _
      rw [hr,Construction.stageInputs_child R o n p c ⟨i,hin⟩ k]
    rw [Construction.singleFormula,bindComputed_spec M n _ _ e v hv hf,
      subsetBody_spec M hM n out (r 0) p ht.1 e v he hv]
    have hA : e (r 0) = level R o := hr 0
    rw [hA]
    have hvs : (fun i : Fin n => v i) =
        (fun i : Fin n => (c i).value R (realPart (bitOracle P bs) i)) := by
      funext i; exact dite_eq_left i.isLt
    rw [hvs]
    rfl

noncomputable def Construction.singleMembership (t : Construction.{u}) : SentenceForm :=
  .ex (.conj (t.singleFormula [] 0 2 3 4 5 6 (fun k => k+7)) (.member 1 0))

noncomputable def Construction.singleInputs (t : Construction.{u}) (R : ZFSet.{u}) (P : Oracle) :
  ℕ → ZFSet.{u} :=
  cons R (cons (realCode P) (cons ZFSet.omega (cons additionSet
    (cons pairNumbers (t.stageInputs R)))))

theorem Construction.singleInputs_mem (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) (P : Oracle)
    (hP : P ∈ modelReals M) (hi : t.Indexed M) : ∀ i, t.singleInputs R P i ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  intro i
  rcases i with _|_|_|_|_|i
  · exact hR
  · exact hP
  · exact hω
  · exact additionSet_mem M hM hT.pairing hT.union hT.powerSet hS hT.infinity
  · exact product_mem M hM hT.pairing hT.union hT.powerSet hS hω hω
  · exact t.stageInputs_mem M R hM hT hR hi i

theorem Construction.singleMembership_of_inputs (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (P : Oracle) (ht : t.Certified R P)
    (hinputs : ∀ i, t.singleInputs R P i ∈ M) (hvalue : t.value R P ∈ M)
    (z : ZFSet.{u}) (hz : z ∈ M) :
    t.singleMembership.Sat (M : Set ZFSet) (cons z (t.singleInputs R P)) ↔
      z ∈ t.value R P := by
  have hs (x : ZFSet.{u}) (hx : x ∈ M) :
      (t.singleFormula [] 0 2 3 4 5 6 (fun k => k+7)).Sat (M : Set ZFSet)
        (cons x (cons z (t.singleInputs R P))) ↔ x = t.value R P := by
    apply t.singleFormula_spec M R hM P [] ht
    · intro i
      rcases i with _|_|i
      · exact hx
      · exact hz
      · exact hinputs i
    all_goals first | rfl | exact fun _ => rfl
  change (∃ x ∈ M, (t.singleFormula [] 0 2 3 4 5 6 (fun k => k+7)).Sat
    (M : Set ZFSet) (cons x (cons z (t.singleInputs R P))) ∧ z ∈ x) ↔ _
  constructor
  · rintro ⟨x,hx,hf,hzx⟩; exact (hs x hx).mp hf ▸ hzx
  · intro hzv
    have hv := hvalue
    exact ⟨_,hv,(hs _ hv).mpr rfl,hzv⟩

theorem Construction.singleMembership_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) (P : Oracle)
    (hP : P ∈ modelReals M) (ht : t.Certified R P) (hi : t.Indexed M)
    (z : ZFSet.{u}) (hz : z ∈ M) :
    t.singleMembership.Sat (M : Set ZFSet) (cons z (t.singleInputs R P)) ↔
      z ∈ t.value R P := by
  have hs (x : ZFSet.{u}) (hx : x ∈ M) :
      (t.singleFormula [] 0 2 3 4 5 6 (fun k => k+7)).Sat (M : Set ZFSet)
        (cons x (cons z (t.singleInputs R P))) ↔ x = t.value R P := by
    apply t.singleFormula_spec M R hM P [] ht
    · intro i
      rcases i with _|_|i
      · exact hx
      · exact hz
      · exact t.singleInputs_mem M R hM hT hR P hP hi i
    all_goals first | rfl | exact fun _ => rfl
  change (∃ x ∈ M, (t.singleFormula [] 0 2 3 4 5 6 (fun k => k+7)).Sat
    (M : Set ZFSet) (cons x (cons z (t.singleInputs R P))) ∧ z ∈ x) ↔ _
  constructor
  · rintro ⟨x,hx,hf,hzx⟩; exact (hs x hx).mp hf ▸ hzx
  · intro hzv
    have hv := t.value_mem M R hM hT hR P ht hi
    exact ⟨_,hv,(hs _ hv).mpr rfl,hzv⟩

end TuringRigidity.RelativeConstructible

end OAI
