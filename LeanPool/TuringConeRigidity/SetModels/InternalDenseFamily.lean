/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalDenseFamily.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalGenericFilter

/-!
# Internal Dense Family
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalGeneric
open TransitiveNameModel CountableForcing
universe u

namespace Code
open Formula

def dense (c o t : ℕ) : Formula := allMem c (.existsMem (c+1)
  (.conj (.member 0 (t+2)) (.pairMem 0 1 (o+2))))

theorem eval_dense (c o t : ℕ) (e : ℕ → ZFSet.{u}) :
    (dense c o t).Eval e ↔ ∀ p ∈ e c, ∃ q ∈ e c, q ∈ e t ∧ ZFSet.pair q p ∈ e o := by
  simp only [dense,Formula.eval_allMem,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]
end Code

theorem dense_labels {c o t : ZFSet.{u}} [Preorder (Conditions c)]
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q) :
    (∀ p ∈ c, ∃ q ∈ c, q ∈ t ∧ ZFSet.pair q p ∈ o) ↔ Dense {p : Conditions c | label c p ∈ t} := by
  constructor
  · intro h p
    obtain ⟨q,hq,hqt,hqp⟩ := h (label c p) (label_mem c p)
    obtain ⟨j,rfl⟩ := label_surjective c hq
    exact ⟨j,(ho j p).mp hqp,hqt⟩
  · intro h p hp
    obtain ⟨i,rfl⟩ := label_surjective c hp
    obtain ⟨j,hji,hjt⟩ := h i
    exact ⟨_,label_mem c j,hjt,(ho j i).mpr hji⟩

theorem dense_family (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q) :
    ∃ D ∈ M, (∀ t, t ∈ D ↔ t ∈ M ∧ t ⊆ c ∧ Dense {p : Conditions c | label c p ∈ t}) ∧
      c ∈ D := by
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  let D := ZFSet.sep (fun t => (Code.dense 1 2 0).Eval (cons t (cons c (fun _ => o)))) Q
  have hDM : D ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded _
    (cons c (fun _ => o)) (by intro i; cases i <;> assumption) hQM
  have hD (t : ZFSet.{u}) : t ∈ D ↔ t ∈ M ∧ t ⊆ c ∧ Dense {p : Conditions c | label c p ∈ t} := by
    dsimp only [D]
    rw [ZFSet.mem_sep,hQ,Code.eval_dense]
    simp only [cons_zero,cons_succ]
    rw [dense_labels ho]
    exact and_assoc
  exact ⟨D,hDM,hD,(hD c).mpr ⟨hc,fun _ h => h,fun p => ⟨p,le_rfl,label_mem c p⟩⟩⟩

theorem internal_ground_generic (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    (hMN : M ⊆ N) {c o D : ZFSet.{u}} [Preorder (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M) (hDM : D ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q)
    (hD : ∀ t, t ∈ D ↔ t ∈ M ∧ t ⊆ c ∧ Dense {p : Conditions c | label c p ∈ t})
    (hcount : InternallyCountable N D) (p₀ : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p₀ ∈ G.carrier ∧ genericFilterSet c G.carrier ∈ N ∧
      AtomicForcing.GroundGeneric M G := by
  obtain ⟨G,hp,hGN,hmeet⟩ := internal_generic_filter N hN hTN (hMN hc) (hMN hoM) (hMN hDM) ho
    hcount (fun t ht => ((hD t).mp ht).2.2) p₀
  refine ⟨G,hp,hGN,?_⟩
  intro E hEM hE
  let t := ZFSet.sep (fun x => x ∈ E) c
  have htM : t ∈ M := sep_mem M hM hTM.separation.finitePrefix.bounded (.member 0 1)
    (fun _ => E) (fun _ => hEM) hc
  have htD : t ∈ D := by
    apply (hD t).mpr
    refine ⟨htM,fun _ h => (ZFSet.mem_sep.mp h).1,?_⟩
    intro p
    obtain ⟨q,hqp,hqE⟩ := hE p
    exact ⟨q,hqp,ZFSet.mem_sep.mpr ⟨label_mem c q,hqE⟩⟩
  obtain ⟨q,hq,hqt⟩ := hmeet t htD
  exact ⟨q,hq,(ZFSet.mem_sep.mp hqt).2⟩

end TuringRigidity.BoundedSetTheory.InternalGeneric

end OAI
