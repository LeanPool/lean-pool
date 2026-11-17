/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalContainer.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.UnionIteration

/-!
# Internal Container
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

/-- A sigma formula requesting a finite iteration certificate for the specified iterated union
value. -/
def unionCertificate : SigmaFormula := .existsSet (.existsSet (.existsSet (.bounded
  (.conj (.successor 2 4) (.conj (IterationFormula.iteration 2 1 0 5 6) (.pairMem 4 3 0))))))

theorem realize_unionCertificate (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {a v : ZFSet.{u}} (ha : a ∈ M) (hv : v ∈ M) (n : ℕ) :
    unionCertificate.Realize M (cons v (cons (natSet n)
      (cons a (cons ∅ (fun _ => a))))) ↔ v = iterUnion n a := by
  have hn (i : ℕ) : natSet.{u} i ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨i,rfl⟩)
  have h0 : (∅ : ZFSet.{u}) ∈ M := hn 0
  have matrix (k r f : ZFSet.{u}) (hk : k ∈ M) (hr : r ∈ M) (hf : f ∈ M) :
      (Formula.conj (.successor 2 4)
        (.conj (IterationFormula.iteration 2 1 0 5 6) (.pairMem 4 3 0))).Realize M
          (cons f (cons r (cons k (cons v (cons (natSet n)
            (cons a (cons ∅ (fun _ => a)))))))) ↔
      k = natSet (n+1) ∧ UnionIteration k r f a ∧ ZFSet.pair (natSet n) v ∈ f := by
    have he : ∀ i, (cons f (cons r (cons k (cons v (cons (natSet n)
        (cons a (cons ∅ (fun _ => a)))))))) i ∈ M := by
      intro i
      rcases i with _ | i
      · exact hf
      rcases i with _ | i
      · exact hr
      rcases i with _ | i
      · exact hk
      rcases i with _ | i
      · exact hv
      rcases i with _ | i
      · exact hn n
      rcases i with _ | i
      · exact ha
      rcases i with _ | i
      · exact h0
      exact ha
    rw [Formula.absolute _ M hM _ he]
    simp only [Formula.Eval,Formula.eval_successor,
      Formula.eval_pairMem,cons_zero,cons_succ]
    rw [IterationFormula.eval_iteration 2 1 0 5 6
      (cons f (cons r (cons k (cons v (cons (natSet n) (cons a (cons ∅ (fun _ => a)))))))) rfl]
    rfl
  change (∃ k ∈ M, ∃ r ∈ M, ∃ f ∈ M, _) ↔ _
  constructor
  · rintro ⟨k,hk,r,hr,f,hf,hc⟩
    obtain ⟨rfl,hg,hv⟩ := (matrix k r f hk hr hf).mp hc
    exact hg.correct n (le_refl n) v hv
  · intro hvEq
    have hf := unionGraph_mem M hM hP hU hω ha n
    refine ⟨natSet (n+1),hn (n+1),_,iterUnion_mem M hM hU hf 2,_,hf,?_⟩
    apply (matrix _ _ _ (hn (n+1)) (iterUnion_mem M hM hU hf 2) hf).mpr
    exact ⟨rfl,unionGraph_valid a n,(unionGraph_pair a _ v n).mpr ⟨n,le_refl n,rfl,hvEq⟩⟩

theorem collect_unionIterates (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hR : SigmaReplacement M)
    (hω : ZFSet.omega.{u} ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ b ∈ M, ∀ y, y ∈ b ↔ ∃ n : ℕ, y = iterUnion n a := by
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ hω _ ZFSet.omega_zero
  let e := cons a (cons ∅ (fun _ => a))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact h0
    exact ha
  obtain ⟨b,hb,hbdef⟩ := hR unionCertificate e he _ hω (by
    intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    have hv := iterUnion_mem M hM hU ha n
    refine ⟨_,hv,(realize_unionCertificate M hM hP hU hω ha hv n).mpr rfl,?_⟩
    intro z hz hφ
    exact (realize_unionCertificate M hM hP hU hω ha hz n).mp hφ)
  refine ⟨b,hb,fun y => ?_⟩
  constructor
  · intro hy
    have hyM := hM b hb y hy
    obtain ⟨x,hx,hφ⟩ := (hbdef y hyM).mp hy
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,(realize_unionCertificate M hM hP hU hω ha hyM n).mp hφ⟩
  · rintro ⟨n,rfl⟩
    have hv := iterUnion_mem M hM hU ha n
    exact (hbdef _ hv).mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,
      (realize_unionCertificate M hM hP hU hω ha hv n).mpr rfl⟩

theorem internal_transitive_container (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ d ∈ M, Transitive d ∧ a ∈ d := by
  have hω := omega_mem M hM hS hI
  obtain ⟨b,hb,hbdef⟩ := collect_unionIterates M hM hP hU hR hω ha
  let d := ({a} : ZFSet.{u}) ∪ ZFSet.sUnion b
  have hd : d ∈ M := binary_union_mem M hM hP hU
    (singleton_mem M hM hP ha) (union_mem M hM hU hb)
  refine ⟨d,hd,?_,ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_singleton.mpr rfl))⟩
  intro x hx y hy
  apply ZFSet.mem_union.mpr
  apply Or.inr
  rcases ZFSet.mem_union.mp hx with hx|hx
  · obtain rfl := ZFSet.mem_singleton.mp hx
    exact ZFSet.mem_sUnion.mpr ⟨x,(hbdef x).mpr ⟨0,rfl⟩,hy⟩
  · obtain ⟨c,hc,hxc⟩ := ZFSet.mem_sUnion.mp hx
    obtain ⟨n,rfl⟩ := (hbdef c).mp hc
    exact ZFSet.mem_sUnion.mpr ⟨iterUnion (n+1) a,(hbdef _).mpr ⟨n+1,rfl⟩,
      ZFSet.mem_sUnion.mpr ⟨x,hxc,hy⟩⟩

end TuringRigidity.TransitiveNameModel

end OAI
