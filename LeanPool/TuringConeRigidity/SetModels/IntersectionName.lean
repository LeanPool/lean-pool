/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/IntersectionName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameSupport
public import LeanPool.TuringConeRigidity.SetModels.InternalAtomicTruth

/-!
# Intersection Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u

namespace AtomicFormula
open Formula

/-- Bounded formula selecting a child and condition witness for the atomic forcing relation. -/
def select (d c k o f y z : ℕ) : Formula :=
  .existsMem d (.existsMem (c+1) (.conj (orderedPair (z+2) 1 0)
    (witness (d+2) (c+2) (k+2) (o+2) (f+2) 1 (y+2) 0)))

theorem eval_select (d c k o f y z : ℕ) (e : ℕ → ZFSet.{u}) :
    (select d c k o f y z).Eval e ↔
      ∃ x ∈ e d, ∃ q ∈ e c, e z = ZFSet.pair x q ∧
        CodeWitness (e d) (e c) (e k) (e o) (e f) x (e y) q := by
  simp only [select,Formula.Eval,eval_orderedPair,eval_witness,cons_zero,cons_succ]
end AtomicFormula

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem internal_intersection_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (hb : b.encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧
      (a.restrict (label c) B).val G.carrier = a.val G.carrier ∩ b.val G.carrier := by
  obtain ⟨d,hd,hdT,hdab⟩ := internal_transitive_container M hM hP hU hS hR hI
    (pair_mem M hM hP ha hb)
  have had : a.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hbd : b.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  have hai (i) : (a.child i).encode (label c) ∈ d := by
    apply names_childClosed d c hdT a had
    cases a
    exact ⟨i,rfl⟩
  obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
  let k := ZFSet.prod d d
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  let e := cons d (cons c (cons k (cons o (cons f (cons (b.encode (label c)) (fun _ => c))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hk
    rcases i with _ | i
    · exact hoM
    rcases i with _ | i
    · exact hf
    rcases i with _ | i
    · exact hb
    exact hc
  let φ := AtomicFormula.select 1 2 3 4 5 6 0
  let B := ZFSet.sep (fun z => φ.Eval (cons z e)) (a.support (label c))
  have hBM : B ∈ M := sep_mem M hM hS φ e he (support_mem M hM hP hU hPow hS hc hoM ho a ha)
  have hBsub : B ⊆ a.support (label c) := fun z hz => (ZFSet.mem_sep.mp hz).1
  have hB (i : a.arity) (q : Conditions c) (hq : q ≤ a.tag i) :
      ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ B ↔ Witness (a.child i) b q := by
    have hs : ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ a.support (label c) :=
      ZFSet.mem_range.mpr ⟨⟨i,⟨q,hq⟩⟩,rfl⟩
    change _ ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep,and_iff_right hs]
    change (AtomicFormula.select 1 2 3 4 5 6 0).Eval (cons _ e) ↔ _
    rw [AtomicFormula.eval_select]
    change (∃ x ∈ d, ∃ r ∈ c,
      ZFSet.pair ((a.child i).encode (label c)) (label c q) = ZFSet.pair x r ∧
        CodeWitness d c k o f x (b.encode (label c)) r) ↔ _
    constructor
    · rintro ⟨x,hx,r,hr,hxr,hw⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxr
      exact (codeWitness_iff hdT ho hfG _ b (hai i) hbd q).mp hw
    · intro hw
      exact ⟨_,hai i,_,label_mem c q,rfl,(codeWitness_iff hdT ho hfG _ b (hai i) hbd q).mpr hw⟩
  have hg := groundGeneric_atomic M hM hP hU hPow hS hR hI hc hoM ho G hG
  have hiM (i) : a.child i ∈ names M c := by
    apply names_childClosed M c hM a ha
    cases a
    exact ⟨i,rfl⟩
  refine ⟨B,hBM,hBsub,?_⟩
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_inter]
  constructor
  · intro hx
    have hxa := a.val_restrict_subset (label c) B G hx
    obtain ⟨i,q,hqi,hqb,hqG,hix⟩ := (a.mem_val_restrict (label c) B G.carrier x).mp hx
    have hw := (hB i q hqi).mp hqb
    have hxb := (mem_truth (names_childClosed M c hM) G hg _ b (hiM i) hb).mpr
      ⟨q,hqG,witness_mem _ _ q hw⟩
    exact ⟨hxa,hix ▸ hxb⟩
  · rintro ⟨hxa,hxb⟩
    obtain ⟨i,hi,hix⟩ := (a.mem_val_children G.carrier x).mp hxa
    have hmem : (a.child i).val G.carrier ∈ b.val G.carrier := hix ▸ hxb
    obtain ⟨p,hp,hm⟩ := (mem_truth (names_childClosed M c hM) G hg _ b (hiM i) hb).mp hmem
    obtain ⟨q,hq,hw⟩ := generic_witness hg (hiM i) hb hp hm
    obtain ⟨r,hr,hrq,hri⟩ := G.directed hq hi
    exact (a.mem_val_restrict (label c) B G.carrier x).mpr
      ⟨i,r,hri,(hB i r hri).mpr (witness_mono _ _ hrq hw),hr,hix⟩

end TuringRigidity.AtomicForcing

end OAI
