/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBoundedTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedSupport
public import LeanPool.TuringConeRigidity.CohenForcing.BoundedForcingCode
public import LeanPool.TuringConeRigidity.SetModels.InternalAtomicTruth

/-!
# Internal Bounded Truth
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem internal_decision (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ D ∈ M, ∀ q, label c q ∈ D ↔ q ∈ Decision e φ := by
  obtain ⟨d,hd,hdT,he0,hen⟩ := finite_container M hM hP hU hS hR hI
    (fun i => (e i).encode (label c)) he (bound φ)
  let e' := truncate (bound φ) e
  have he' (i) : (e' i).encode (label c) ∈ d := by
    dsimp only [e',truncate]
    split
    · exact hen i ‹_›
    · exact he0
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
  let ψ := Formula.disj (code φ 1 2 3 4 5 (fun i => i+6) 0)
    (code (.neg φ) 1 2 3 4 5 (fun i => i+6) 0)
  have hψ (q : Conditions c) : ψ.Eval (cons (label c q) env) ↔ q ∈ Decision e φ := by
    have hcφ (χ : BoundedSetTheory.Formula) := eval_code χ hdT ho hfG e' he' q
      (cons (label c q) env) 1 2 3 4 5 (fun i => i+6) 0
      ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ (fun _ => rfl)
    rw [Formula.eval_disj,hcφ φ,hcφ (.neg φ)]
    exact or_congr (truncate_forces φ e q) (truncate_forces (.neg φ) e q)
  refine ⟨ZFSet.sep (fun q => ψ.Eval (cons q env)) c,sep_mem M hM hS ψ env henv hc,?_⟩
  intro q
  simp only [ZFSet.mem_sep,label_mem c q,true_and,hψ]

theorem groundGeneric_bounded (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) : Generic (names M c) G := by
  intro φ e he
  obtain ⟨D,hD,hDdef⟩ := internal_decision M hM hP hU hPow hS hR hI hc hoM ho φ e he
  have hd : Dense {q | label c q ∈ D} := by
    intro p
    obtain ⟨q,hq,hf⟩ := decision_dense e φ p
    exact ⟨q,hq,(hDdef q).mpr hf⟩
  obtain ⟨q,hq,hqd⟩ := hG D hD hd
  exact ⟨q,hq,(hDdef q).mp hqd⟩

theorem internal_bounded_truth (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M) :
    φ.Eval (fun i => (e i).val G.carrier) ↔ ∃ p ∈ G.carrier, Forces e φ p :=
  truth (names_childClosed M c hM) G
    (groundGeneric_atomic M hM hP hU hPow hS hR hI hc hoM ho G hG)
    (groundGeneric_bounded M hM hP hU hPow hS hR hI hc hoM ho G hG) φ e he

end TuringRigidity.BoundedForcing

end OAI
