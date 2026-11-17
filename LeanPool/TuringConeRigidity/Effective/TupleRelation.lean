/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/TupleRelation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TupleFormula
public import LeanPool.TuringConeRigidity.SetModels.InternalContainer

/-!
# Tuple Relation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

def outputFirst (n k : ℕ) : ℕ → ℕ
  | 0 => n
  | i+1 => if i < n then i else i+k+1

theorem prepend_outputFirst (xs junk : List ZFSet.{u}) (y : ZFSet.{u})
    (e : ℕ → ZFSet.{u}) :
    (fun i => prepend xs (cons y (prepend junk e)) (outputFirst xs.length junk.length i)) =
      cons y (prepend xs e) := by
  funext i
  cases i with
  | zero => exact prepend_tail xs (cons y (prepend junk e)) 0
  | succ i =>
    change prepend xs (cons y (prepend junk e))
      (if i < xs.length then i else i+junk.length+1) = prepend xs e i
    by_cases hi : i < xs.length
    · rw [ite_eq_left hi]; exact prepend_congr xs _ _ i hi
    · rw [ite_eq_right hi]
      obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      have harith : xs.length+j+junk.length+1 = xs.length+(junk.length+j+1) := by omega
      rw [harith,prepend_tail,prepend_tail,cons_succ,prepend_tail]

noncomputable def relation (d : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ xs : List ZFSet.{u}, xs.length = n ∧
    (∀ x ∈ xs, x ∈ d) ∧ ∃ y ∈ d, z = ZFSet.pair (code xs) y ∧
      φ.Eval (cons y (prepend xs e))) (ZFSet.prod (space d n) d)

theorem relation_pair (d y : ZFSet.{u}) (xs : List ZFSet.{u}) (φ : Formula)
    (e : ℕ → ZFSet.{u}) : ZFSet.pair (code xs) y ∈ relation d xs.length φ e ↔
      (∀ x ∈ xs, x ∈ d) ∧ y ∈ d ∧ φ.Eval (cons y (prepend xs e)) := by
  rw [relation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,ys,hlen,hys,z,hz,hpair,hφ⟩
    obtain ⟨hcode,rfl⟩ := ZFSet.pair_inj.mp hpair
    obtain rfl := code_injective_length xs ys hlen.symm hcode
    exact ⟨hys,hz,hφ⟩
  · rintro ⟨hxs,hy,hφ⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨_,code_mem_space d xs hxs,y,hy,rfl⟩,
      xs,rfl,hxs,y,hy,rfl,hφ⟩

def relationFormula (n : ℕ) (φ : Formula) : Formula :=
  .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (unpack n 1 5 6 (φ.rename (outputFirst n 6)))))

theorem eval_relationFormula (d c z : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (hc : Transitive c) (hspace : space d n ⊆ c) :
    (relationFormula n φ).Eval (cons z (cons (space d n) (cons d (cons c (cons ∅ e))))) ↔
      z ∈ relation d n φ e := by
  simp only [relationFormula,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨t,ht,y,hy,rfl,hφ⟩
    obtain ⟨xs,rfl,hxs,rfl⟩ := (mem_space d t n).mp ht
    apply (relation_pair d y xs φ e).mpr
    refine ⟨hxs,hy,?_⟩
    have h := (eval_unpack xs 1 5 6 (φ.rename (outputFirst xs.length 6))
      (cons y (cons (code xs) (cons (ZFSet.pair (code xs) y)
        (cons (space d xs.length) (cons d (cons c (cons ∅ e)))))))
      rfl hc (hspace ht) rfl).mp hφ
    rw [Formula.eval_rename] at h
    have he := prepend_outputFirst xs [code xs,ZFSet.pair (code xs) y,space d xs.length,d,c,∅] y e
    exact he ▸ h
  · intro hz
    obtain ⟨_,xs,hlen,hxs,y,hy,rfl,hφ⟩ := ZFSet.mem_sep.mp hz
    subst n
    have ht := code_mem_space d xs hxs
    refine ⟨code xs,ht,y,hy,rfl,?_⟩
    apply (eval_unpack xs 1 5 6 (φ.rename (outputFirst xs.length 6))
      (cons y (cons (code xs) (cons (ZFSet.pair (code xs) y)
        (cons (space d xs.length) (cons d (cons c (cons ∅ e)))))))
      rfl hc (hspace ht) rfl).mpr
    rw [Formula.eval_rename]
    have he := prepend_outputFirst xs [code xs,ZFSet.pair (code xs) y,space d xs.length,d,c,∅] y e
    exact he.symm ▸ hφ

theorem relation_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) : relation d n φ e ∈ M := by
  have hs := space_mem M hM hP hU hPow hS hd n
  obtain ⟨c,hc,hct,hsc⟩ := internal_transitive_container M hM hP hU hS hR hI hs
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ (omega_mem M hM hS hI) _ ZFSet.omega_zero
  let env := cons (space d n) (cons d (cons c (cons ∅ e)))
  have henv : ∀ i, env i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hs
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact h0
    exact he i
  have hsep := sep_mem M hM hS (relationFormula n φ) env henv
    (product_mem M hM hP hU hPow hS hs hd)
  have heq : ZFSet.sep (fun z => (relationFormula n φ).Eval (cons z env))
      (ZFSet.prod (space d n) d) = relation d n φ e := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,eval_relationFormula d c z n φ e hct (fun x hx => hct _ hsc x hx)]
    exact and_iff_right_of_imp (fun hz => (ZFSet.mem_sep.mp hz).1)
  exact heq ▸ hsep

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
