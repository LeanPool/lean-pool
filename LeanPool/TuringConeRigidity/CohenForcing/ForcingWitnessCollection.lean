/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/ForcingWitnessCollection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaCollection
public import LeanPool.TuringConeRigidity.Syntax.SigmaDefinability

/-!
# Forcing Witness Collection
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]
namespace WitnessCode

/-- Variable placement for a forcing witness request, reserving slots for its new witnesses. -/
def vars : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | i+2 => i+6

/-- A sigma formula requesting a valid name together with the corresponding forcing witness. -/
def request (φ : SigmaFormula) : SigmaFormula :=
  .existsSet (.existsSet (SigmaFormula.andBounded (.orderedPair 3 1 0)
    (SigmaFormula.conj (NameValidity.Code.valid 4 2) (SigmaCode.forcing φ 4 5 0 vars))))
end WitnessCode

theorem realize_witnessRequest (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (p : Conditions c)
    {x : ZFSet.{u}} (hx : x ∈ M) :
    (WitnessCode.request φ).Realize M (cons x
      (cons (ZFSet.pair (a.encode (label c)) (label c p))
        (cons c (cons o (fun i => (e i).encode (label c)))))) ↔
      ∃ b : Name (Conditions c), b.encode (label c) = x ∧ SigmaForces M (push b (push a e)) φ p :=
        by
  let base := cons x (cons (ZFSet.pair (a.encode (label c)) (label c p))
    (cons c (cons o (fun i => (e i).encode (label c)))))
  have hpM := hM c hc _ (label_mem c p)
  have hreq := orderedPair_mem M hM hP ha hpM
  have hbM : ∀ i, base i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hx
    rcases i with _ | i
    · exact hreq
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hoM
    exact he i
  have envM (z q : ZFSet.{u}) (hz : z ∈ M) (hq : q ∈ M) : ∀ i, cons q (cons z base) i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hq
    rcases i with _ | i
    · exact hz
    exact hbM i
  have pair (z q : ZFSet.{u}) (hz : z ∈ M) (hq : q ∈ M) :
      (Formula.orderedPair 3 1 0).Realize M (cons q (cons z base)) ↔
        a.encode (label c) = z ∧ label c p = q := by
    rw [Formula.absolute _ M hM _ (envM z q hz hq),Formula.eval_orderedPair]
    exact ZFSet.pair_inj
  let env := cons (label c p) (cons (a.encode (label c)) base)
  have henv : ∀ i, env i ∈ M := envM _ _ ha hpM
  have valid : (NameValidity.Code.valid 4 2).Realize M env ↔
      ∃ b : Name (Conditions c), b.encode (label c) = x :=
    NameValidity.realize_valid M hM hP hU hPow hS hR hI env henv 4 2
  have forcing (b : Name (Conditions c)) (hb : b.encode (label c) = x) :
      (SigmaCode.forcing φ 4 5 0 WitnessCode.vars).Realize M env ↔
        SigmaForces M (push b (push a e)) φ p := by
    apply realize_sigmaForcing M hM hP hU hPow hS hR hI ho φ (push b (push a e)) p env henv 4 5 0
      WitnessCode.vars rfl rfl rfl
    intro i
    rcases i with _ | i
    · exact hb.symm
    rcases i with _ | i
    · rfl
    rfl
  change (∃ z ∈ M, ∃ q ∈ M, _) ↔ _
  simp only [SigmaFormula.realize_andBounded,SigmaFormula.realize_conj]
  constructor
  · rintro ⟨z,hz,q,hq,hpair,hvalid,hforce⟩
    obtain ⟨rfl,rfl⟩ := (pair z q hz hq).mp hpair
    obtain ⟨b,hb⟩ := valid.mp hvalid
    exact ⟨b,hb,(forcing b hb).mp hforce⟩
  · rintro ⟨b,hb,hforce⟩
    exact ⟨_,ha,_,hpM,(pair _ _ ha hpM).mpr ⟨rfl,rfl⟩,valid.mpr ⟨b,hb⟩,(forcing b hb).mpr hforce⟩

theorem forcing_witness_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c
      ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    {d : ZFSet.{u}} (hd : d ∈ M) :
    ∃ W ∈ M, ∀ a : Name (Conditions c), a.encode (label c) ∈ d → ∀ p : Conditions c,
      (∃ b : Name (Conditions c), b.encode (label c) ∈ M ∧ SigmaForces M (push b (push a e)) φ p) →
        ∃ b : Name (Conditions c), b.encode (label c) ∈ W ∧ SigmaForces M (push b (push a e)) φ p
          := by
  let env := cons c (cons o (fun i => (e i).encode (label c)))
  have henv : ∀ i, env i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hoM
    exact he i
  have hrequests := product_mem M hM hP hU hPow hS.bounded hd hc
  obtain ⟨W,hW,hbound⟩ := internal_sigma_request_bound M hM hP hU hPow hS hR hI hAC
    (WitnessCode.request φ) env henv hrequests
  refine ⟨W,hW,?_⟩
  intro a ha p hb
  have haM := hM d hd _ ha
  have hreq := ZFSet.mem_prod.mpr ⟨_,ha,_,label_mem c p,rfl⟩
  obtain ⟨x,hx,hφ⟩ := hbound _ hreq (by
    obtain ⟨b,hb,hφ⟩ := hb
    exact ⟨_,hb,(realize_witnessRequest M hM hP hU hPow hS.bounded hR hI hc hoM ho φ e he a haM p
      hb).mpr
      ⟨b,rfl,hφ⟩⟩)
  obtain ⟨b,hb,hforce⟩ := (realize_witnessRequest M hM hP hU hPow hS.bounded hR hI hc hoM ho φ e
    he a haM p
    (hM W hW x hx)).mp hφ
  exact ⟨b,hb ▸ hx,hforce⟩

end TuringRigidity.BoundedForcing

end OAI
