/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CountableSetReal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeUniverse
public import LeanPool.TuringConeRigidity.SetModels.ModelPresentationSets

/-!
# Countable Set Real
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing
universe u

namespace Formula
/-- Bounded formula reading a bit from an oracle selected through an internal enumeration and
graph. -/
def selectedEnumerationBit (o Q I E F v : ℕ) : Formula :=
  .existsMem o (.existsMem (o+1) (.conj (naturalPair (o+2) (Q+2) 1 0 (v+2))
    (.existsMem (I+2) (.conj (.pairMem 2 0 (E+3))
      (.existsMem 0 (.conj (.pairMem 1 0 (F+4)) (.member 2 0)))))))

theorem selectedEnumerationBit_spec (o Q I E F v : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (N K : ℕ) (hv : e v = natSet (Nat.pair N K)) :
    (selectedEnumerationBit o Q I E F v).Eval e ↔
      ∃ D ∈ e I, ZFSet.pair (natSet N) D ∈ e E ∧
        ∃ A ∈ D, ZFSet.pair D A ∈ e F ∧ natSet K ∈ A := by
  simp only [selectedEnumerationBit,Formula.Eval,eval_pairMem,cons_zero,cons_succ]
  rw [ho]
  constructor
  · rintro ⟨n,hn,k,hk,hp,hrest⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨k,rfl⟩ := (mem_omega k).mp hk
    have hp' := (naturalPair_spec (o+2) (Q+2) 1 0 (v+2)
      (cons (natSet k) (cons (natSet n) e)) ho hQ n k rfl rfl).mp hp
    have hnk : Nat.pair N K = Nat.pair n k := natSet_injective (hv.symm.trans hp')
    have he := congrArg Nat.unpair hnk
    simp only [Nat.unpair_pair,Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    exact hrest
  · intro h
    refine ⟨natSet N,(mem_omega _).mpr ⟨N,rfl⟩,natSet K,(mem_omega _).mpr ⟨K,rfl⟩,?_,h⟩
    exact (naturalPair_spec (o+2) (Q+2) 1 0 (v+2)
      (cons (natSet K) (cons (natSet N) e)) ho hQ N K rfl rfl).mpr hv
end Formula

theorem internal_selected_enumeration_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {I E F : ZFSet.{u}} (hIM : I ∈ M) (hEM : E ∈ M) (hFM : F ∈ M)
    (hE : TransitiveNameModel.FunctionGraph ZFSet.omega I E) (hF : ChoiceGraph I F) :
    ∃ H ∈ modelReals M, ∀ n, ∀ D ∈ I, ZFSet.pair (natSet n) D ∈ E →
      ∀ A : Oracle, realCode A ∈ D → ZFSet.pair D (realCode A) ∈ F → columns H n = A := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hS hω
  let e := cons ZFSet.omega (cons Q (cons I (cons E (fun _ => F))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hIM
    rcases i with _ | i
    · exact hEM
    exact hFM
  let B := ZFSet.sep (fun v => (Formula.selectedEnumerationBit 1 2 3 4 5 0).Eval (cons v e))
    ZFSet.omega
  have hBM : B ∈ M := sep_mem M hM hS _ e he hω
  have hsub : B ⊆ ZFSet.omega := fun _ h => (ZFSet.mem_sep.mp h).1
  have hB : realCode (decodeReal B) = B := realCode_decodeReal hsub
  refine ⟨decodeReal B,?_,?_⟩
  · change realCode (decodeReal B) ∈ M
    rw [hB]; exact hBM
  · intro n D hD hn A hA hDA
    funext k
    have hbit : columns (decodeReal B) n k = true ↔ A k = true := by
      change decodeReal B (Nat.pair n k) = true ↔ A k = true
      rw [decodeReal_true]
      change natSet (Nat.pair n k) ∈ ZFSet.sep _ ZFSet.omega ↔ _
      rw [ZFSet.mem_sep,Formula.selectedEnumerationBit_spec 1 2 3 4 5 0
        (cons (natSet (Nat.pair n k)) e) rfl hQ n k rfl]
      constructor
      · rintro ⟨_,D',_,hn',A',_,hDA',hk⟩
        have hDD := hE.functional ((mem_omega _).mpr ⟨n,rfl⟩) hn hn'
        subst D'
        have hAA := hF.functional hDA hDA'
        rw [←hAA,natSet_mem_realCode] at hk
        exact hk
      · intro hk
        exact ⟨(mem_omega _).mpr ⟨Nat.pair n k,rfl⟩,D,hD,hn,realCode A,hA,hDA,
          (natSet_mem_realCode A k).mpr hk⟩
    cases hx : columns (decodeReal B) n k <;> cases hy : A k <;> simp_all

/-- The model contains a function graph from omega onto the set `I`. -/
def InternallyCountable (M I : ZFSet.{u}) : Prop :=
  ∃ E ∈ M, TransitiveNameModel.FunctionGraph ZFSet.omega I E ∧
    ∀ D ∈ I, ∃ n ∈ ZFSet.omega, ZFSet.pair n D ∈ E

theorem internal_countable_degree_presentation (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ w ∈ R, ∃ A : Oracle, realCode A = w)
    {I : ZFSet.{u}} (hIM : I ∈ M) (hI : I ⊆ degreeUniverse R)
    (hcount : InternallyCountable M I) :
    ∃ H ∈ modelReals M, presentationSet R H = I := by
  obtain ⟨E,hEM,hE,honto⟩ := hcount
  obtain ⟨F,hFM,hF⟩ := hT.choice I hIM (fun D hD => by
    obtain ⟨A,hA,_⟩ := degreeUniverse_nonempty_member R D (hI hD)
    exact ⟨realCode A,hA⟩)
  obtain ⟨H,hHM,hH⟩ := internal_selected_enumeration_real M hM hT hIM hEM hFM hE hF
  have hentry (n : ℕ) (D : ZFSet.{u}) (hD : D ∈ I) (hn : ZFSet.pair (natSet n) D ∈ E) :
      degreeCode R (columns H n) = D := by
    obtain ⟨a,ha,hDa,_⟩ := hF.2 D hD
    obtain ⟨B,hB,hDB⟩ := (mem_degreeUniverse R D).mp (hI hD)
    have har : a ∈ R := degreeCode_subset R B (hDB ▸ ha)
    obtain ⟨A,rfl⟩ := hR a har
    rw [hH n D hD hn A ha hDa]
    have heq := ((realCode_mem_degreeCode R B A).mp (hDB ▸ ha)).2
    exact ((degreeCode_equal R har).mpr heq).trans hDB.symm
  refine ⟨H,hHM,?_⟩
  apply ZFSet.ext; intro D
  constructor
  · intro hD
    obtain ⟨n,rfl⟩ := (mem_presentationSet R H D).mp hD
    obtain ⟨D,hD,hn,_⟩ := hE.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
    rw [hentry n D hD hn]
    exact hD
  · intro hD
    obtain ⟨n,hn,hDn⟩ := honto D hD
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact (mem_presentationSet R H D).mpr ⟨n,(hentry n D hD hDn).symm⟩

end TuringRigidity.BoundedSetTheory

end OAI
