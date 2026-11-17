/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NameUnionCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelProducts

/-!
# Name Union Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open Set RecursiveNames BoundedSetTheory
universe u

def iterUnion : ℕ → ZFSet.{u} → ZFSet.{u}
  | 0, a => a
  | n+1, a => ZFSet.sUnion (iterUnion n a)

theorem iterUnion_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) {a : ZFSet.{u}} (ha : a ∈ M) (n : ℕ) :
    iterUnion n a ∈ M := by
  induction n with
  | zero => exact ha
  | succ n ih => exact union_mem M hM hU ih

theorem first_mem_doubleUnion {a b c : ZFSet.{u}} (h : ZFSet.pair a b ∈ c) :
    a ∈ iterUnion 2 c := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨({a} : ZFSet.{u}),?_,ZFSet.mem_singleton.mpr rfl⟩
  apply ZFSet.mem_sUnion.mpr
  exact ⟨ZFSet.pair a b,h,ZFSet.mem_pair.mpr (Or.inl rfl)⟩

theorem iterUnion_lift {a b : ZFSet.{u}} (h : a ∈ b) (n : ℕ) :
    iterUnion n a ⊆ iterUnion (n+1) b := by
  induction n with
  | zero => exact fun x hx => ZFSet.mem_sUnion.mpr ⟨a,h,hx⟩
  | succ n ih =>
    intro x hx
    obtain ⟨y,hy,hxy⟩ := ZFSet.mem_sUnion.mp hx
    exact ZFSet.mem_sUnion.mpr ⟨y,ih hy,hxy⟩

theorem iterUnion_add (m n : ℕ) (a : ZFSet.{u}) :
    iterUnion m (iterUnion n a) = iterUnion (m+n) a := by
  induction m with
  | zero => simp only [iterUnion,Nat.zero_add]
  | succ m ih => simp only [iterUnion,ih,Nat.succ_add]

theorem second_child_bound {a b c d t : ZFSet.{u}}
    (hab : ZFSet.pair a b ∈ t) (hcd : ZFSet.pair c d ∈ a) : c ∈ iterUnion 5 t := by
  have ha := first_mem_doubleUnion hab
  have hc := first_mem_doubleUnion hcd
  have ht := iterUnion_lift ha 2 hc
  simpa only [iterUnion_add] using ht

theorem label_surjective (p : ZFSet.{u}) {x : ZFSet.{u}} (hx : x ∈ p) :
    ∃ q : Conditions p, label p q = x := by
  exact ⟨equivShrink p ⟨x,hx⟩,by simp [label]⟩

theorem pair_mem_encode {P : Type u} (l : P → ZFSet.{u}) (τ : Name P)
    (x q : ZFSet.{u}) :
    ZFSet.pair x q ∈ τ.encode l ↔
      ∃ i, (τ.child i).encode l = x ∧ l (τ.tag i) = q := by
  cases τ with
  | mk ι child tag =>
    change ZFSet.pair x q ∈ ZFSet.range _ ↔ _
    rw [ZFSet.mem_range]
    simp only [ZFSet.pair_inj,Name.child,Name.tag]
    rfl

def unionPredicate (t p r z : ZFSet.{u}) : Prop :=
  ∃ d ∈ iterUnion 5 t, ∃ s ∈ p, z = ZFSet.pair d s ∧
    ∃ c ∈ iterUnion 2 t, ∃ q ∈ p, ∃ v ∈ p,
      ZFSet.pair c q ∈ t ∧ ZFSet.pair d v ∈ c ∧
        ZFSet.pair s q ∈ r ∧ ZFSet.pair s v ∈ r

def unionFormula : Formula :=
  .existsMem 3 (.existsMem 5
    (.conj (.orderedPair 2 1 0)
      (.existsMem 4 (.existsMem 7 (.existsMem 8
        (.conj (.pairMem 2 1 6) (.conj (.pairMem 4 0 2)
          (.conj (.pairMem 3 1 10) (.pairMem 3 0 10)))))))))

theorem eval_unionFormula (t p r z : ZFSet.{u}) (env : ℕ → ZFSet.{u}) :
    unionFormula.Eval (cons z (cons t (cons (iterUnion 2 t)
      (cons (iterUnion 5 t) (cons p (cons r env)))))) ↔ unionPredicate t p r z := by
  simp only [unionFormula,Formula.Eval,cons_succ,cons_zero,
    Formula.eval_orderedPair,Formula.eval_pairMem,unionPredicate]

noncomputable def unionCode (t p r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (unionPredicate t p r) (ZFSet.prod (iterUnion 5 t) p)

theorem mem_unionCode (t p r z : ZFSet.{u}) :
    z ∈ unionCode t p r ↔ unionPredicate t p r z := by
  rw [unionCode,ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    have hh := h
    obtain ⟨d,hd,s,hs,hz,_⟩ := hh
    exact ⟨ZFSet.mem_prod.mpr ⟨d,hd,s,hs,hz⟩,h⟩

theorem unionCode_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M)
    {t p r : ZFSet.{u}} (ht : t ∈ M) (hp : p ∈ M) (hr : r ∈ M) :
    unionCode t p r ∈ M := by
  let env := cons t (cons (iterUnion 2 t) (cons (iterUnion 5 t) (cons p (cons r (fun _ => t)))))
  have h2 := iterUnion_mem M hM hU ht 2
  have h5 := iterUnion_mem M hM hU ht 5
  have he : ∀ i, env i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|i <;> assumption
  have hs := sep_mem M hM hS unionFormula env he (product_mem M hM hP hU hPow hS h5 hp)
  have heq : ZFSet.sep (fun z => unionFormula.Eval (cons z env)) (ZFSet.prod (iterUnion 5 t) p) =
      unionCode t p r := by
    apply ZFSet.ext
    intro z
    simp only [unionCode,ZFSet.mem_sep]
    exact and_congr Iff.rfl (eval_unionFormula t p r z _)
  exact heq ▸ hs

theorem encode_union (p r : ZFSet.{u}) [Preorder (Conditions p)]
    (hr : ∀ q s : Conditions p, ZFSet.pair (label p q) (label p s) ∈ r ↔ q ≤ s)
    (τ : Name (Conditions p)) :
    (Name.union τ).encode (label p) = unionCode (τ.encode (label p)) p r := by
  apply ZFSet.ext
  intro z
  rw [mem_unionCode]
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨i,j,s,hsq,hsv⟩,hz⟩
    have hi : ZFSet.pair ((τ.child i).encode (label p)) (label p (τ.tag i)) ∈ τ.encode (label p) :=
      (pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩
    have hj : ZFSet.pair (((τ.child i).child j).encode (label p)) (label p ((τ.child i).tag j)) ∈
        (τ.child i).encode (label p) := (pair_mem_encode _ _ _ _).mpr ⟨j,rfl,rfl⟩
    exact ⟨_,second_child_bound hi hj,_,label_mem p s,hz.symm,
      _,first_mem_doubleUnion hi,_,label_mem p _,_,label_mem p _,hi,hj,
      (hr _ _).mpr hsq,(hr _ _).mpr hsv⟩
  · rintro ⟨d,_,s,hs,rfl,c,_,q,_,v,_,hc,hd,hq,hv⟩
    obtain ⟨i,rfl,rfl⟩ := (pair_mem_encode _ _ _ _).mp hc
    obtain ⟨j,rfl,rfl⟩ := (pair_mem_encode _ _ _ _).mp hd
    obtain ⟨s,rfl⟩ := label_surjective p hs
    exact ⟨⟨i,j,s,(hr _ _).mp hq,(hr _ _).mp hv⟩,rfl⟩

end TuringRigidity.TransitiveNameModel

end OAI
