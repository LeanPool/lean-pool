/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalGenericSequence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTDependentChoice

/-!
# Internal Generic Sequence
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalGeneric
open TransitiveNameModel
universe u

namespace Code
open Formula

/-- Bounded formula for one numbered condition step meeting the next enumerated dense
requirement. -/
def step (ω c E D o s z : ℕ) : Formula :=
  .existsMem ω (.existsMem (c+1) (.existsMem (ω+2) (.existsMem (c+3)
    (.existsMem (D+4) (.existsMem (s+5) (.existsMem (s+6)
      (.conj (.orderedPair (z+7) 0 1)
        (.conj (.orderedPair 1 6 5) (.conj (.orderedPair 0 4 3)
          (.conj (.successor 4 6) (.conj (.pairMem 6 2 (E+7))
            (.conj (.member 3 2) (.pairMem 3 5 (o+7))))))))))))))

theorem eval_step (ω c E D o s z : ℕ) (e : ℕ → ZFSet.{u})
    (hs : e s = ZFSet.prod (e ω) (e c)) :
    (step ω c E D o s z).Eval e ↔
      ∃ n ∈ e ω, ∃ p ∈ e c, ∃ m ∈ e ω, ∃ q ∈ e c, ∃ t ∈ e D,
        e z = ZFSet.pair (ZFSet.pair m q) (ZFSet.pair n p) ∧
        m = insert n n ∧ ZFSet.pair n t ∈ e E ∧ q ∈ t ∧ ZFSet.pair q p ∈ e o := by
  simp only [step,Formula.Eval,eval_orderedPair,eval_successor,eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨n,hn,p,hp,m,hm,q,hq,t,ht,v,_,w,_,hz,rfl,rfl,hrest⟩
    exact ⟨n,hn,p,hp,m,hm,q,hq,t,ht,hz,hrest⟩
  · rintro ⟨n,hn,p,hp,m,hm,q,hq,t,ht,hz,hrest⟩
    refine ⟨n,hn,p,hp,m,hm,q,hq,t,ht,ZFSet.pair n p,?_,ZFSet.pair m q,?_,hz,rfl,rfl,hrest⟩
    · rw [hs]; exact ZFSet.mem_prod.mpr ⟨n,hn,p,hp,rfl⟩
    · rw [hs]; exact ZFSet.mem_prod.mpr ⟨m,hm,q,hq,rfl⟩
end Code

/-- The set-coded transition relation for the internal generic-filter construction. -/
noncomputable def stepRelation (c E D o : ZFSet.{u}) : ZFSet.{u} :=
  let s := ZFSet.prod ZFSet.omega c
  ZFSet.sep (fun z => (Code.step 1 2 3 4 5 6 0).Eval
    (cons z (cons ZFSet.omega (cons c (cons E (cons D (cons o (fun _ => s))))))))
    (ZFSet.prod s s)

theorem step_pair (c E D o x y : ZFSet.{u}) :
    ZFSet.pair y x ∈ stepRelation c E D o ↔
      ∃ n ∈ ZFSet.omega, ∃ p ∈ c, ∃ m ∈ ZFSet.omega, ∃ q ∈ c, ∃ t ∈ D,
        x = ZFSet.pair n p ∧ y = ZFSet.pair m q ∧
        m = insert n n ∧ ZFSet.pair n t ∈ E ∧ q ∈ t ∧ ZFSet.pair q p ∈ o := by
  rw [stepRelation,ZFSet.mem_sep]
  rw [Code.eval_step _ _ _ _ _ _ _ _ rfl]
  simp only [cons_zero,cons_succ]
  constructor
  · rintro ⟨_,n,hn,p,hp,m,hm,q,hq,t,ht,hpair,hrest⟩
    obtain ⟨hy,hx⟩ := ZFSet.pair_inj.mp hpair
    exact ⟨n,hn,p,hp,m,hm,q,hq,t,ht,hx,hy,hrest⟩
  · rintro ⟨n,hn,p,hp,m,hm,q,hq,t,ht,rfl,rfl,hrest⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨_,ZFSet.mem_prod.mpr ⟨m,hm,q,hq,rfl⟩,
      _,ZFSet.mem_prod.mpr ⟨n,hn,p,hp,rfl⟩,rfl⟩,n,hn,p,hp,m,hm,q,hq,t,ht,rfl,hrest⟩

theorem stepRelation_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c E D o : ZFSet.{u}} (hc : c ∈ M) (hE : E ∈ M) (hD : D ∈ M) (ho : o ∈ M) :
    stepRelation c E D o ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  have hs := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hω hc
  apply sep_mem M hM hT.separation.finitePrefix.bounded
  · intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hE
    rcases i with _ | i
    · exact hD
    rcases i with _ | i
    · exact ho
    exact hs
  · exact product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hs hs

theorem internal_dense_sequence (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c E D o : ZFSet.{u}} (hc : c ∈ M) (hE : E ∈ M) (hD : D ∈ M) (ho : o ∈ M)
    (hEF : TransitiveNameModel.FunctionGraph ZFSet.omega D E)
    (hdense : ∀ t ∈ D, ∀ p ∈ c, ∃ q ∈ c, q ∈ t ∧ ZFSet.pair q p ∈ o)
    {p₀ : ZFSet.{u}} (hp₀ : p₀ ∈ c) :
    ∃ a : ℕ → ZFSet.{u}, (∀ n, a n ∈ c) ∧ a 0 = p₀ ∧
      orbitGraph (fun n => ZFSet.pair (natSet n) (a n)) ∈ M ∧
      ∀ n, ∃ t ∈ D, ZFSet.pair (natSet n) t ∈ E ∧
        a (n+1) ∈ t ∧ ZFSet.pair (a (n+1)) (a n) ∈ o := by
  classical
  let s := ZFSet.prod ZFSet.omega c
  have hs := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (sourceT_omega_mem M hM hT) hc
  have serial : ∀ x ∈ s, ∃ y ∈ s, ZFSet.pair y x ∈ stepRelation c E D o := by
    intro x hx
    obtain ⟨n,hn,p,hp,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨t,ht,hnt,_⟩ := hEF.2 n hn
    obtain ⟨q,hq,hqt,hqp⟩ := hdense t ht p hp
    refine ⟨ZFSet.pair (insert n n) q,ZFSet.mem_prod.mpr ⟨_,ZFSet.omega_succ hn,q,hq,rfl⟩,?_⟩
    exact (step_pair c E D o _ _).mpr ⟨n,hn,p,hp,_,ZFSet.omega_succ
      hn,q,hq,t,ht,rfl,rfl,rfl,hnt,hqt,hqp⟩
  obtain ⟨b,hb0,hb,hbM,hstep⟩ := sourceT_dependent_choice M hM hT hs
    (stepRelation_mem M hM hT hc hE hD ho)
    (ZFSet.mem_prod.mpr ⟨natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,p₀,hp₀,rfl⟩) serial
  have shape : ∀ n, ∃ p ∈ c, b n = ZFSet.pair (natSet n) p := by
    intro n
    induction n with
    | zero => exact ⟨p₀,hp₀,hb0⟩
    | succ n ih =>
      obtain ⟨p,hp,hbp⟩ := ih
      obtain ⟨k,_,q,_,m,_,r,hr,t,_,hbq,hbr,hm,_⟩ := (step_pair c E D o _ _).mp (hstep n)
      have heq := ZFSet.pair_inj.mp (hbp.symm.trans hbq)
      refine ⟨r,hr,?_⟩
      rw [hbr,hm,←heq.1]
      rfl
  choose a ha hab using shape
  have ha0 : a 0 = p₀ := (ZFSet.pair_inj.mp ((hab 0).symm.trans hb0)).2
  have heq : b = fun n => ZFSet.pair (natSet n) (a n) := funext hab
  refine ⟨a,ha,ha0,heq ▸ hbM,?_⟩
  intro n
  obtain ⟨k,hk,p,hp,m,hm,q,hq,t,ht,hbp,hbq,hsucc,hkt,hqt,hqp⟩ := (step_pair c E D o _ _).mp (hstep
    n)
  obtain ⟨hk',hp'⟩ := ZFSet.pair_inj.mp ((hab n).symm.trans hbp)
  obtain ⟨_,hq'⟩ := ZFSet.pair_inj.mp ((hab (n+1)).symm.trans hbq)
  exact ⟨t,ht,hk'.symm ▸ hkt,hq'.symm ▸ hqt,hq'.symm ▸ hp'.symm ▸ hqp⟩

end TuringRigidity.BoundedSetTheory.InternalGeneric

end OAI
