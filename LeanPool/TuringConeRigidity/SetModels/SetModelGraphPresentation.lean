/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelGraphPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelActionSatisfaction
public import LeanPool.TuringConeRigidity.Constructibility.PersistentCountability
public import LeanPool.TuringConeRigidity.SetModels.SetModelColumns

/-!
# Set Model Graph Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions PersistentPresentation PersistentCountability
open SetModelSequences SetModelColumns SetModelArithmetic EncodedForcing
universe u
noncomputable section

/-- Bounded formula describing the numerical presentation of an ideal automorphism graph. -/
def graphPresentationFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 5 (.existsMem 6 (.existsMem 8 (.existsMem 9 (.existsMem 13
    (.conj (.orderedPair 0 6 5) (.conj (.pairMem 0 7 13)
      (.conj (.pairMem 6 4 9) (.conj (.pairMem 5 3 9)
        (.conj (.member 4 2) (.conj (.member 3 1) (.pairMem 2 1 12)))))))))))))

/-- The parameter environment for the automorphism-graph presentation formula. -/
def graphPresentationEnv (I : CountableIdeal) (A : Oracle) (ρ : I ≃o I) : ℕ → ZFSet.{u} :=
  cons ZFSet.omega (cons (sequenceSet (columns A)) (cons (columnRange A)
    (cons (idealSet I) (cons (automorphismSet ρ) (cons pairingSet (fun _ => pairNumbers))))))

theorem eval_graphPresentationFormula {I : CountableIdeal} {A : Oracle} (hA : Presented I A)
    (ρ : I ≃o I) (k : ℕ) :
    graphPresentationFormula.Eval (cons (natSet k) (graphPresentationEnv.{u} I A ρ)) ↔ Graph ρ hA
      k := by
  simp only [graphPresentationFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    graphPresentationEnv,cons_zero,cons_succ]
  constructor
  · rintro ⟨n,hn,m,hm,X,hX,Y,hY,a,ha,b,hb,t,ht,htnm,htk,hnX,hmY,hXa,hYb,hab⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨m,rfl⟩ := (mem_omega m).mp hm
    have hk : k = Nat.pair n m := (pairingSet_code n m k).mp (htnm ▸ htk)
    obtain rfl := (pair_mem_sequenceSet (columns A) n X).mp hnX
    obtain rfl := (pair_mem_sequenceSet (columns A) m Y).mp hmY
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I a).mp ha
    obtain ⟨b,hbc,rfl⟩ := (mem_idealSet I b).mp hb
    have hna := (real_mem_degreeSet (columns A n) a).mp hXa
    have hmb := (real_mem_degreeSet (columns A m) b).mp hYb
    have he := (action_code ρ ⟨a,hac⟩ ⟨b,hbc⟩).mp hab
    have hn' : entry hA n = ⟨a,hac⟩ := Subtype.ext hna
    simp only [hk,PersistentPresentation.Graph,Nat.unpair_pair,hn']
    exact (congrArg Subtype.val he).trans hmb.symm
  · intro hg
    obtain ⟨⟨n,m⟩,rfl⟩ := Nat.pairEquiv.surjective k
    have hn : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
    have hm : natSet.{u} m ∈ ZFSet.omega := (mem_omega _).mpr ⟨m,rfl⟩
    refine ⟨natSet n,hn,natSet m,hm,realSet (columns A n),(mem_columnRange _ _).mpr ⟨n,rfl⟩,
      realSet (columns A m),(mem_columnRange _ _).mpr ⟨m,rfl⟩,
      degreeSet (degree (columns A n)),(mem_idealSet I _).mpr ⟨_,(entry hA n).property,rfl⟩,
      degreeSet (degree (columns A m)),(mem_idealSet I _).mpr ⟨_,(entry hA m).property,rfl⟩,
      ZFSet.pair (natSet n) (natSet m),ZFSet.mem_prod.mpr ⟨_,hn,_,hm,rfl⟩,rfl,
      (pairingSet_code _ _ _).mpr rfl,(pair_mem_sequenceSet _ _ _).mpr rfl,
      (pair_mem_sequenceSet _ _ _).mpr rfl,(real_mem_degreeSet _ _).mpr rfl,
      (real_mem_degreeSet _ _).mpr rfl,?_⟩
    exact (action_code ρ (entry hA n) (entry hA m)).mpr
      (Subtype.ext (by simpa [PersistentPresentation.Graph,entry] using hg))

theorem internal_graph_presentation {M : ZFSet.{u}} (C : Context M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (hIM : idealSet I ∈ M) (ρ : I ≃o I) (hρM : automorphismSet ρ ∈ M) :
    graphOracle hA ρ ∈ reals M := by
  have hseq := columns_mem M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) C.pairing_mem pairingSet_code hAM
  have hcols : ∀ n, columns A n ∈ reals M :=
    fun n => lower_mem C hAM (CodingExtraction.column_projection_reduces A n)
  have hrange := columnRange_mem M C.transitive C.power C.separation C.infinity hcols hseq
  have hpairs := product_mem M C.transitive C.pairing C.union C.power C.separation C.omega_mem
    C.omega_mem
  have he : ∀ i, graphPresentationEnv.{u} I A ρ i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|_|i <;>
      simp [graphPresentationEnv,C.omega_mem,hseq,hrange,hIM,hρM,C.pairing_mem,hpairs,pairNumbers]
  have hs := sep_mem M C.transitive C.separation graphPresentationFormula _ he C.omega_mem
  have heq : ZFSet.sep (fun z => graphPresentationFormula.Eval (cons z (graphPresentationEnv.{u} I
    A ρ)))
      ZFSet.omega = realSet (graphOracle hA ρ) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,h⟩
      obtain ⟨n,rfl⟩ := (mem_omega z).mp hz
      exact (nat_mem_realSet _ _).mpr (by
        simpa [graphOracle] using (eval_graphPresentationFormula hA ρ n).mp h)
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_omega z).mp (realSet_subset _ hz)
      have hn := (nat_mem_realSet _ n).mp hz
      exact ⟨(mem_omega _).mpr ⟨n,rfl⟩,(eval_graphPresentationFormula hA ρ n).mpr (by
        simpa [graphOracle] using hn)⟩
  change realSet.{u} (graphOracle hA ρ) ∈ M
  exact heq ▸ hs

end
end TuringRigidity.SetModelSatisfaction

end OAI
