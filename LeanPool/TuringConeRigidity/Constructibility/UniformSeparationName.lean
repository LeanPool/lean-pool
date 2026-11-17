/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformSeparationName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBoundedTruth
public import LeanPool.TuringConeRigidity.SetModels.NameSupport

/-!
# Uniform Separation Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem uniform_separation_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : BoundedSetTheory.Formula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧
      ∀ (G : GenericFilter (Conditions c)), GroundGeneric M G → ∀ x,
      x ∈ (a.restrict (label c) B).val G.carrier ↔ x ∈ a.val G.carrier ∧
        φ.Eval (cons x (fun i => (e i).val G.carrier)) := by
  obtain ⟨d,hd,hdT,had,hnd⟩ := finite_container M hM hP hU hS hR hI
    (fun i => (push a e i).encode (label c))
    (by
      intro i
      cases i with
      | zero => simpa only [push_zero] using ha
      | succ i => simpa only [push_succ] using he i) (bound φ+2)
  let e' := truncate (bound φ) e
  have he' (i) : (e' i).encode (label c) ∈ d := by
    dsimp only [e',truncate]
    split
    · exact hnd (i+1) (by omega)
    · exact hnd 1 (by omega)
  have hai (i) : (a.child i).encode (label c) ∈ d :=
    names_childClosed d c hdT a had _ (child_relation a i)
  have hpush (i) (n) : (push (a.child i) e' n).encode (label c) ∈ d := by
    cases n with
    | zero => exact hai i
    | succ n => exact he' n
  obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
  let k := ZFSet.prod d d
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  let env := cons d (cons c (cons k (cons o (cons f (fun i => (e' i).encode (label c))))))
  have henv : ∀ i, env i ∈ M := by
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
    exact hM d hd _ (he' i)
  let ψ := Formula.existsMem 1 (.existsMem 3 (.conj (Formula.orderedPair 2 1 0)
    (code φ 3 4 5 6 7 (push 1 (fun i => i+8)) 0)))
  let B := ZFSet.sep (fun z => ψ.Eval (cons z env)) (a.support (label c))
  have hBM : B ∈ M := sep_mem M hM hS ψ env henv
    (support_mem M hM hP hU hPow hS hc hoM ho a ha)
  have hBsub : B ⊆ a.support (label c) := fun z hz => (ZFSet.mem_sep.mp hz).1
  have query (i : a.arity) (q : Conditions c) (z : ZFSet.{u}) :=
    eval_code φ hdT ho hfG (push (a.child i) e') (hpush i) q
      (cons (label c q) (cons ((a.child i).encode (label c)) (cons z env)))
      3 4 5 6 7 (push 1 (fun n => n+8)) 0 ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (by intro n; cases n <;> rfl)
  have hB (i : a.arity) (q : Conditions c) (hq : q ≤ a.tag i) :
      ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ B ↔ Forces (push (a.child i) e') φ q
        := by
    have hs : ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ a.support (label c) :=
      ZFSet.mem_range.mpr ⟨⟨i,⟨q,hq⟩⟩,rfl⟩
    change _ ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep,and_iff_right hs]
    change (Formula.existsMem 1 _).Eval _ ↔ _
    simp only [Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,env]
    constructor
    · rintro ⟨x,hx,r,hr,hxr,hφ⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxr
      exact (query i q _).mp hφ
    · intro hφ
      exact ⟨_,hai i,_,label_mem c q,rfl,(query i q _).mpr hφ⟩
  refine ⟨B,hBM,hBsub,?_⟩
  intro G hG
  have ht (i : a.arity) :
      φ.Eval (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        ∃ p ∈ G.carrier, Forces (push (a.child i) e') φ p := by
    have hfinite : φ.Eval (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        φ.Eval (fun n => (push (a.child i) e' n).val G.carrier) := by
      apply eval_congr
      intro n hn
      cases n with
      | zero => rfl
      | succ n =>
        simp only [cons_succ,push_succ]
        dsimp only [e',truncate]
        rw [ite_eq_left (by omega)]
    exact hfinite.trans (internal_bounded_truth M hM hP hU hPow hS hR hI hc hoM ho G hG φ _
      (fun n => hM d hd _ (hpush i n)))
  intro x
  constructor
  · intro hx
    have hxa := a.val_restrict_subset (label c) B G hx
    obtain ⟨i,q,hqi,hqb,hqG,hix⟩ := (a.mem_val_restrict (label c) B G.carrier x).mp hx
    have hφ := (ht i).mpr ⟨q,hqG,(hB i q hqi).mp hqb⟩
    exact ⟨hxa,hix ▸ hφ⟩
  · rintro ⟨hxa,hφ⟩
    obtain ⟨i,hi,hix⟩ := (a.mem_val_children G.carrier x).mp hxa
    obtain ⟨p,hp,hf⟩ := (ht i).mp (hix ▸ hφ)
    obtain ⟨q,hq,hqp,hqi⟩ := G.directed hp hi
    exact (a.mem_val_restrict (label c) B G.carrier x).mpr
      ⟨i,q,hqi,(hB i q hqi).mpr (forces_mono φ _ hqp hf),hq,hix⟩

end TuringRigidity.BoundedForcing

end OAI
