/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeSetGraphs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistenceRealClosure
public import LeanPool.TuringConeRigidity.SetModels.SetDegreeDecoding
public import LeanPool.TuringConeRigidity.SetModels.SetModelGraphImage
public import LeanPool.TuringConeRigidity.TuringTwoConeGraphPresentation

/-!
# Native set graphs of partial two-cone isomorphisms

The source and target are both intersections of an ordinary ideal with a
principal cone. The graph is bounded by the square of the ordinary ideal.
Real-coded conventional graphs reconstruct exactly this set, with no pairs
outside the source cone and no assumption of persistence once codes are given.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeSetGraphs

open BoundedSetTheory TransitiveNameModel SetPresentationDecoding SetModelReals
open SetDegreeDecoding SetModelSequences SetModelColumns EncodedForcing
open PersistentRestrictions
open ConePersistence (Cone)
open ConePresentation (Presented)
open TwoConePresentation (RawGraph)

universe u
noncomputable section

/-- The set-coded graph of the isomorphism between the ideal's two principal cones. -/
def coneGraph {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x : Cone I a,
    z = ZFSet.pair (degreeSet x.val) (degreeSet (ρ x).val))
    (ZFSet.prod (idealSet I) (idealSet I))

@[simp] theorem mem_coneGraph {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (z : ZFSet.{u}) :
    z ∈ coneGraph ρ ↔ ∃ x : Cone I a,
      z = ZFSet.pair (degreeSet x.val) (degreeSet (ρ x).val) := by
  rw [coneGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x, rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr
      ⟨(mem_idealSet I _).mpr ⟨x.val, x.property.1, rfl⟩,
        (mem_idealSet I _).mpr ⟨(ρ x).val, (ρ x).property.1, rfl⟩⟩, ⟨x, rfl⟩⟩

theorem coneGraph_subset {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) :
    coneGraph.{u} ρ ⊆ ZFSet.prod (idealSet I) (idealSet I) :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem extends_graphs {I J : CountableIdeal} {a b : Degree}
    {hIJ : I.carrier ⊆ J.carrier} {ρ : Cone I a ≃o Cone I b}
    {σ : Cone J a ≃o Cone J b} (he : TwoConePersistence.Extends hIJ ρ σ) :
    coneGraph.{u} ρ ⊆ coneGraph σ := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_coneGraph ρ z).mp hz
  refine (mem_coneGraph σ _).mpr ⟨⟨x.val, hIJ x.property.1, x.property.2⟩, ?_⟩
  rw [he x]

/-- Quotient a real-valued graph to exactly the graph between the two cones. -/
theorem action_eq_coneGraph (M : ZFSet.{u})
    (hLower : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    {d E s R : ZFSet.{u}} (hd : ∀ x, x ∈ d ↔ ∃ A ∈ reals M, x = realSet A)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {a b : Degree} {A : Oracle}
    (hA : Presented I A) (ρ : Cone I a ≃o Cone I b)
    (hs : ∀ x, x ∈ s ↔ ∃ n, x = realSet (columns A n))
    (hcols : ∀ n, columns A n ∈ reals M)
    (hR : ∀ n m, ZFSet.pair (realSet (columns A n)) (realSet (columns A m)) ∈ R ↔
      RawGraph ρ A (Nat.pair n m)) :
    actionGraph d E s R = coneGraph ρ := by
  apply ZFSet.ext
  intro z
  rw [mem_actionGraph, mem_coneGraph]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨n, rfl⟩ := (hs x).mp hx
    obtain ⟨m, rfl⟩ := (hs y).mp hy
    rw [class_eq_degreeSet M hLower hd hE (hcols n),
      class_eq_degreeSet M hLower hd hE (hcols m)]
    have hg := (hR n m).mp hxy
    simp only [RawGraph, Nat.unpair_pair] at hg
    obtain ⟨x, hx, hy⟩ := hg
    exact ⟨x, by rw [hx, hy]⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨n, hn⟩ := (hA x.val).mp x.property.1
    obtain ⟨m, hm⟩ := (hA (ρ x).val).mp (ρ x).property.1
    refine ⟨_, (hs _).mpr ⟨n, rfl⟩, _, (hs _).mpr ⟨m, rfl⟩, ?_, ?_⟩
    · apply (hR n m).mpr
      simp only [RawGraph, Nat.unpair_pair]
      exact ⟨x, hn.symm, hm.symm⟩
    · rw [class_eq_degreeSet M hLower hd hE (hcols n),
        class_eq_degreeSet M hLower hd hE (hcols m), hn, hm]

theorem graphImage_action {I : CountableIdeal} {a b : Degree} {A G : Oracle}
    (ρ : Cone I a ≃o Cone I b)
    (hG : ∀ v, G v = true ↔ RawGraph ρ A v) (n m : ℕ) :
    ZFSet.pair (realSet.{u} (columns A n)) (realSet (columns A m)) ∈ graphImage A G ↔
      RawGraph ρ A (Nat.pair n m) := by
  rw [mem_graphImage]
  constructor
  · rintro ⟨i, j, hGij, hpair⟩
    obtain ⟨hi, hj⟩ := ZFSet.pair_inj.mp hpair
    have hi' := realSet_injective hi
    have hj' := realSet_injective hj
    have hh := (hG (Nat.pair i j)).mp hGij
    simpa only [RawGraph, Nat.unpair_pair, hi', hj'] using hh
  · intro h
    exact ⟨n, m, (hG _).mpr h, rfl⟩

/-- Internal real codes give the full internal set graph, not just its pairs.
Persistence and the internal axiom of Choice are not hypotheses here. -/
theorem coded_sets (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hC : PersistenceRealClosure.Closed (reals M))
    {p E : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p) (hEM : E ∈ M)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {a b : Degree} {A G : Oracle}
    (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : Cone I a ≃o Cone I b) (hGM : G ∈ reals M)
    (hG : ∀ v, G v = true ↔ RawGraph ρ A v) :
    idealSet I ∈ M ∧ coneGraph ρ ∈ M := by
  obtain ⟨r, hr, hrdef⟩ := internal_reals M hM hPow hS hI
  have hcols : ∀ n, columns A n ∈ reals M :=
    fun n => hC.lower hAM (CodingExtraction.column_projection_reduces A n)
  have hseq := columns_mem M hM hP hU hPow hS hI hC.lower hp hpdef hAM
  have hs := columnRange_mem M hM hPow hS hI hcols hseq
  have hi := quotient_mem M hM hPow hS hr hEM hs
  have hieq := quotient_eq_idealSet M hC.lower hrdef hE hA (mem_columnRange A) hcols
  refine ⟨hieq ▸ hi, ?_⟩
  have hR := graphImage_mem M hM hP hU hPow hS hI hp hpdef hseq hs hGM
  have hm := action_mem M hM hP hU hPow hS hr hEM hs hR
  have heq := action_eq_coneGraph M hC.lower hrdef hE hA ρ
    (mem_columnRange A) hcols (graphImage_action ρ hG)
  exact heq ▸ hm

end
end OAI.TuringRigidity.TwoConeSetGraphs
