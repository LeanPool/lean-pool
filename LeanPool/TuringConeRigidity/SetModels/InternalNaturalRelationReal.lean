/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalNaturalRelationReal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTDependentChoice
public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalPairingFormula
public import LeanPool.TuringConeRigidity.SetModels.ModelReals

/-!
# Internal Natural Relation Real
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u

/-- The oracle representing the binary relation on naturals coded by the set `G`. -/
noncomputable def naturalRelationReal (G : ZFSet.{u}) : Oracle := fun v => by
  classical
  exact decide (ZFSet.pair (natSet (Nat.unpair v).1) (natSet (Nat.unpair v).2) ∈ G)

theorem naturalRelationReal_pair (G : ZFSet.{u}) (n k : ℕ) :
    naturalRelationReal G (Nat.pair n k) = true ↔ ZFSet.pair (natSet n) (natSet k) ∈ G := by
  classical
  simp [naturalRelationReal]

namespace Formula
/-- Bounded formula reading a bit of the oracle associated with a natural-number relation
graph. -/
def naturalRelationBit (o Q G v : ℕ) : Formula := .existsMem o (.existsMem (o+1)
  (.conj (naturalPair (o+2) (Q+2) 1 0 (v+2)) (.pairMem 1 0 (G+2))))

theorem naturalRelationBit_spec (o Q G v : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (N K : ℕ) (hv : e v = natSet (Nat.pair N K)) :
    (naturalRelationBit o Q G v).Eval e ↔ ZFSet.pair (natSet N) (natSet K) ∈ e G := by
  simp only [naturalRelationBit,Formula.Eval,eval_pairMem,cons_succ,cons_zero]
  rw [ho]
  constructor
  · rintro ⟨n,hn,k,hk,hp,hg⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨k,rfl⟩ := (mem_omega k).mp hk
    have hp' := (naturalPair_spec (o+2) (Q+2) 1 0 (v+2)
      (cons (natSet k) (cons (natSet n) e)) ho hQ n k rfl rfl).mp hp
    have hnk : Nat.pair N K = Nat.pair n k := natSet_injective (hv.symm.trans hp')
    have he := congrArg Nat.unpair hnk
    simp only [Nat.unpair_pair,Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    exact hg
  · intro h
    exact ⟨natSet N,(mem_omega _).mpr ⟨N,rfl⟩,natSet K,(mem_omega _).mpr ⟨K,rfl⟩,
      (naturalPair_spec (o+2) (Q+2) 1 0 (v+2)
        (cons (natSet K) (cons (natSet N) e)) ho hQ N K rfl rfl).mpr hv,h⟩
end Formula

theorem sourceT_naturalRelationReal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {G : ZFSet.{u}} (hG : G ∈ M) : naturalRelationReal G ∈ modelReals M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hS hω
  let e := cons ZFSet.omega (cons Q (fun _ => G))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    exact hG
  let B := ZFSet.sep (fun v => (Formula.naturalRelationBit 1 2 3 0).Eval (cons v e)) ZFSet.omega
  have hBM : B ∈ M := sep_mem M hM hS _ e he hω
  have hb (v : ℕ) : natSet.{u} v ∈ B ↔ naturalRelationReal G v = true := by
    obtain ⟨⟨n,k⟩,rfl⟩ := Nat.pairEquiv.surjective v
    change natSet (Nat.pair n k) ∈ B ↔ naturalRelationReal G (Nat.pair n k) = true
    rw [naturalRelationReal_pair]
    change natSet (Nat.pair n k) ∈ ZFSet.sep _ ZFSet.omega ↔ _
    rw [ZFSet.mem_sep,Formula.naturalRelationBit_spec 1 2 3 0
      (cons (natSet (Nat.pair n k)) e) rfl hQ n k rfl]
    exact and_iff_right ((mem_omega _).mpr ⟨Nat.pair n k,rfl⟩)
  have hEq : realCode (naturalRelationReal G) = B := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ ZFSet.omega.{u}
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      rw [natSet_mem_realCode,hb]
    · exact ⟨fun h => False.elim (hx (realCode_subset _ h)),fun h => False.elim (hx
      (ZFSet.mem_sep.mp h).1)⟩
  change realCode _ ∈ M
  rw [hEq]; exact hBM

theorem sourceT_natural_descent_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {r : ZFSet.{u}} (hr : r ∈ M) (hon : On ZFSet.omega r)
    (hw : ¬ WellFounded (Rel ZFSet.omega r)) :
    ∃ f : ℕ → ℕ, ∃ A ∈ modelReals M,
      (∀ n k, A (Nat.pair n k) = true ↔ k = f n) ∧
      ∀ n, ZFSet.pair (natSet (f (n+1))) (natSet (f n)) ∈ r := by
  classical
  obtain ⟨a,ha,hAM,hstep⟩ := sourceT_internal_descent M hM hT (sourceT_omega_mem M hM hT) hr hon hw
  have hn (n : ℕ) : ∃ k, a n = natSet k := (mem_omega _).mp (ha n)
  let f (n : ℕ) := (hn n).choose
  have hf (n : ℕ) : a n = natSet (f n) := (hn n).choose_spec
  refine ⟨f,naturalRelationReal (orbitGraph a),sourceT_naturalRelationReal M hM hT hAM,?_,?_⟩
  · intro n k
    rw [naturalRelationReal_pair,orbitGraph_pair,hf n]
    exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩
  · intro n
    rw [←hf (n+1),←hf n]
    exact hstep n

end TuringRigidity.BoundedSetTheory

end OAI
