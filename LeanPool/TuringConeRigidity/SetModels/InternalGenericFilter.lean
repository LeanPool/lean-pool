/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalGenericFilter.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalGenericSequence
public import LeanPool.TuringConeRigidity.SetModels.InternalAtomicTruth

/-!
# Internal Generic Filter
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalGeneric
open TransitiveNameModel CountableForcing
universe u

namespace Code
open Formula

def reaches (ω c s g o p : ℕ) : Formula :=
  .existsMem ω (.existsMem (s+1) (.conj (.pairMem 1 0 (g+2))
    (.existsMem (ω+2) (.existsMem (c+3) (.conj (.orderedPair 2 1 0) (.pairMem 0 (p+4) (o+4)))))))
end Code

theorem sequence_filter_set (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} (hc : c ∈ M) (ho : o ∈ M)
    (a : ℕ → ZFSet.{u}) (ha : ∀ n, a n ∈ c)
    (hg : orbitGraph (fun n => ZFSet.pair (natSet n) (a n)) ∈ M) :
    ZFSet.sep (fun p => ∃ n, ZFSet.pair (a n) p ∈ o) c ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  let s := ZFSet.prod ZFSet.omega c
  have hs := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hω hc
  let g := orbitGraph (fun n => ZFSet.pair (natSet n) (a n))
  let e := cons ZFSet.omega (cons c (cons s (cons g (fun _ => o))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hs
    rcases i with _ | i
    · exact hg
    exact ho
  have eq (p : ZFSet.{u}) : (Code.reaches 1 2 3 4 5 0).Eval (cons p e) ↔
      ∃ n, ZFSet.pair (a n) p ∈ o := by
    simp only [Code.reaches,Formula.Eval,Formula.eval_pairMem,Formula.eval_orderedPair,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,st,_,hst,k,_,q,_,hpair,hqp⟩
      obtain ⟨i,rfl⟩ := (mem_omega n).mp hn
      have heq := (orbitGraph_pair _ i st).mp hst
      obtain ⟨_,hqa⟩ := ZFSet.pair_inj.mp (hpair.symm.trans heq)
      exact ⟨i,hqa ▸ hqp⟩
    · rintro ⟨n,hn⟩
      have hnω : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
      exact ⟨natSet n,hnω,ZFSet.pair (natSet n) (a n),ZFSet.mem_prod.mpr ⟨_,hnω,_,ha n,rfl⟩,
        (orbitGraph_pair _ n _).mpr rfl,natSet n,hnω,a n,ha n,rfl,hn⟩
  have hset := sep_mem M hM hT.separation.finitePrefix.bounded (Code.reaches 1 2 3 4 5 0) e he hc
  have heq : ZFSet.sep (fun p => (Code.reaches 1 2 3 4 5 0).Eval (cons p e)) c =
      ZFSet.sep (fun p => ∃ n, ZFSet.pair (a n) p ∈ o) c := by
    apply ZFSet.ext; intro p
    simp only [ZFSet.mem_sep,eq]
  exact heq ▸ hset

theorem internal_generic_filter (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o D : ZFSet.{u}} [Preorder (Conditions c)] (hc : c ∈ M) (hoM : o ∈ M) (hD : D ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q)
    (hcount : InternallyCountable M D)
    (hdense : ∀ t ∈ D, Dense {p : Conditions c | label c p ∈ t}) (p₀ : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p₀ ∈ G.carrier ∧ genericFilterSet c G.carrier ∈ M ∧
      ∀ t ∈ D, ∃ p ∈ G.carrier, label c p ∈ t := by
  classical
  obtain ⟨E,hEM,hEF,honto⟩ := hcount
  have hdense' : ∀ t ∈ D, ∀ p ∈ c, ∃ q ∈ c, q ∈ t ∧ ZFSet.pair q p ∈ o := by
    intro t ht p hp
    obtain ⟨i,rfl⟩ := label_surjective c hp
    obtain ⟨j,hji,hjt⟩ := hdense t ht i
    exact ⟨_,label_mem c j,hjt,(ho j i).mpr hji⟩
  obtain ⟨a,ha,ha0,hgraph,hstep⟩ := internal_dense_sequence M hM hT hc hEM hD hoM hEF hdense'
    (label_mem c p₀)
  choose q hq using fun n => label_surjective c (ha n)
  have hq0 : q 0 = p₀ := label_injective c ((hq 0).trans ha0)
  have hanti : Antitone q := by
    apply antitone_nat_of_succ_le
    intro n
    obtain ⟨t,_,_,_,hs⟩ := hstep n
    exact (ho _ _).mp (by simpa only [hq] using hs)
  let G : GenericFilter (Conditions c) := {
    carrier := {p | ∃ n, q n ≤ p}
    nonempty := ⟨q 0,0,le_rfl⟩
    upper := fun hpq ⟨n,hn⟩ => ⟨n,hn.trans hpq⟩
    directed := by
      rintro p r ⟨n,hn⟩ ⟨m,hm⟩
      exact ⟨q (max n m),⟨max n m,le_rfl⟩,
        (hanti (Nat.le_max_left n m)).trans hn,(hanti (Nat.le_max_right n m)).trans hm⟩ }
  have hset := sequence_filter_set M hM hT hc hoM a ha hgraph
  have heq : genericFilterSet c G.carrier = ZFSet.sep (fun p => ∃ n, ZFSet.pair (a n) p ∈ o) c := by
    apply ZFSet.ext; intro x
    rw [mem_genericFilterSet,ZFSet.mem_sep]
    constructor
    · rintro ⟨p,⟨n,hn⟩,rfl⟩
      exact ⟨label_mem c p,n,by simpa only [hq] using (ho (q n) p).mpr hn⟩
    · rintro ⟨hx,n,hn⟩
      obtain ⟨p,rfl⟩ := label_surjective c hx
      exact ⟨p,⟨n,(ho (q n) p).mp (by simpa only [hq] using hn)⟩,rfl⟩
  refine ⟨G,⟨0,by rw [hq0]⟩,heq.symm ▸ hset,?_⟩
  intro t ht
  obtain ⟨n,hn,hnt⟩ := honto t ht
  obtain ⟨i,rfl⟩ := (mem_omega n).mp hn
  obtain ⟨s,hs,hns,has,_⟩ := hstep i
  have he : t = s := hEF.functional ((mem_omega _).mpr ⟨i,rfl⟩) hnt hns
  exact ⟨q (i+1),⟨i+1,le_rfl⟩,by simpa only [hq,he] using has⟩

end TuringRigidity.BoundedSetTheory.InternalGeneric

end OAI
