/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NameSupport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RestrictedName
public import LeanPool.TuringConeRigidity.Syntax.AtomicDefinability

/-!
# Name Support
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

def SupportPredicate (d c o x z : ZFSet.{u}) : Prop :=
  ∃ a ∈ d, ∃ q ∈ c, z = ZFSet.pair a q ∧ ∃ s ∈ c,
    ZFSet.pair a s ∈ x ∧ ZFSet.pair q s ∈ o

namespace AtomicFormula
open Formula

def support (d c o x z : ℕ) : Formula :=
  .existsMem d (.existsMem (c+1) (.conj (orderedPair (z+2) 1 0)
    (.existsMem (c+2) (.conj (pairMem 2 0 (x+3)) (pairMem 1 0 (o+3))))))

theorem eval_support (d c o x z : ℕ) (e : ℕ → ZFSet.{u}) :
    (support d c o x z).Eval e ↔ SupportPredicate (e d) (e c) (e o) (e x) (e z) := by
  simp only
    [support,Formula.Eval,eval_orderedPair,eval_pairMem,cons_zero,cons_succ,SupportPredicate]
end AtomicFormula

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem support_iff {d o : ZFSet.{u}} (a : Name (Conditions c))
    (hd : ∀ i, (a.child i).encode (label c) ∈ d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (z : ZFSet.{u}) : z ∈ a.support (label c) ↔ SupportPredicate d c o (a.encode (label c)) z := by
  constructor
  · intro hz
    obtain ⟨⟨i,q,hq⟩,hz⟩ := ZFSet.mem_range.mp hz
    exact ⟨_,hd i,_,label_mem c q,hz.symm,_,label_mem c (a.tag i),
      (pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩,(ho q (a.tag i)).mpr hq⟩
  · rintro ⟨x,hx,q,hq,rfl,s,hs,hxs,hqs⟩
    obtain ⟨i,hi,his⟩ := (pair_mem_encode _ _ _ _).mp hxs
    subst x
    subst s
    obtain ⟨r,rfl⟩ := label_surjective c hq
    exact ZFSet.mem_range.mpr ⟨⟨i,⟨r,(ho r (a.tag i)).mp hqs⟩⟩,rfl⟩

theorem support_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hc : c ∈ M) {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) : a.support (label c) ∈ M := by
  let d := iterUnion 2 (a.encode (label c))
  have hd : d ∈ M := iterUnion_mem M hM hU ha 2
  have hdi (i) : (a.child i).encode (label c) ∈ d :=
    first_mem_doubleUnion ((pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩)
  let e := cons d (cons c (cons o (cons (a.encode (label c)) (fun _ => c))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hoM
    rcases i with _ | i
    · exact ha
    exact hc
  let φ := AtomicFormula.support 1 2 3 4 0
  have hφ (z : ZFSet.{u}) : φ.Eval (cons z e) ↔ z ∈ a.support (label c) :=
    (AtomicFormula.eval_support 1 2 3 4 0 _).trans (support_iff a hdi ho z).symm
  have hcode : ZFSet.sep (fun z => φ.Eval (cons z e)) (ZFSet.prod d c) = a.support (label c) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,hφ]
    constructor
    · exact And.right
    · intro hz
      obtain ⟨x,hx,q,hq,hz',_⟩ := (support_iff a hdi ho z).mp hz
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,q,hq,hz'⟩,hz⟩
  exact hcode ▸ sep_mem M hM hS φ e he (product_mem M hM hP hU hPow hS hd hc)

end TuringRigidity.AtomicForcing

end OAI
