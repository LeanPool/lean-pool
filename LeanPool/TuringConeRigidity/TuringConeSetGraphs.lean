/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeSetGraphs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistenceRealClosure
public import LeanPool.TuringConeRigidity.SetModels.SetDegreeDecoding
public import LeanPool.TuringConeRigidity.SetModels.SetModelGraphImage
public import LeanPool.TuringConeRigidity.TuringConePresentation

/-!
# Set-valued graphs of partial cone isomorphisms

The graph is a subset of the square of the ordinary ideal. Its range is the
principal cone, not the whole ideal. This representation lets the general
set-forcing descent theorems apply without pretending that a cone map is an
automorphism. Numerical graph codes are decoded to this precise set graph.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeSetGraphs

open BoundedSetTheory TransitiveNameModel SetPresentationDecoding SetModelReals
open SetDegreeDecoding SetModelSequences SetModelColumns EncodedForcing
open PersistentRestrictions ConePersistence ConePresentation

universe u
noncomputable section

/-- The set-coded graph of the ideal-to-cone isomorphism on degree-set representations. -/
def coneGraph {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ b : I, z = ZFSet.pair (degreeSet b.val) (degreeSet (ρ b).val))
    (ZFSet.prod (idealSet I) (idealSet I))

@[simp] theorem mem_coneGraph {I : CountableIdeal} {a : Degree}
    (ρ : I ≃o Cone I a) (z : ZFSet.{u}) :
    z ∈ coneGraph ρ ↔ ∃ b : I, z = ZFSet.pair (degreeSet b.val) (degreeSet (ρ b).val) := by
  rw [coneGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨b, rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr
      ⟨(mem_idealSet I _).mpr ⟨b.val, b.property, rfl⟩,
        (mem_idealSet I _).mpr ⟨(ρ b).val, (ρ b).property.1, rfl⟩⟩, ⟨b, rfl⟩⟩

theorem coneGraph_subset {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a) :
    coneGraph.{u} ρ ⊆ ZFSet.prod (idealSet I) (idealSet I) :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem extends_graphs {I J : CountableIdeal} {a : Degree}
    {hIJ : I.carrier ⊆ J.carrier} {ρ : I ≃o Cone I a} {σ : J ≃o Cone J a}
    (he : ConePersistence.Extends hIJ ρ σ) : coneGraph.{u} ρ ⊆ coneGraph σ := by
  intro z hz
  obtain ⟨b, rfl⟩ := (mem_coneGraph ρ z).mp hz
  refine (mem_coneGraph σ _).mpr ⟨⟨b.val, hIJ b.property⟩, ?_⟩
  rw [he b]

/-- Quotient the real-valued action graph to obtain exactly the cone graph. -/
theorem action_eq_coneGraph (M : ZFSet.{u})
    (hLower : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    {d E s R : ZFSet.{u}} (hd : ∀ x, x ∈ d ↔ ∃ A ∈ reals M, x = realSet A)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {a : Degree} {A : Oracle}
    (hA : ConePresentation.Presented I A) (ρ : I ≃o Cone I a)
    (hs : ∀ x, x ∈ s ↔ ∃ n, x = realSet (columns A n))
    (hcols : ∀ n, columns A n ∈ reals M)
    (hR : ∀ n m, ZFSet.pair (realSet (columns A n)) (realSet (columns A m)) ∈ R ↔
      (ρ (presentationEntry hA n)).val = degree (columns A m)) :
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
    exact ⟨presentationEntry hA n, by rw [(hR n m).mp hxy]; rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨n, hn⟩ := (hA b.val).mp b.property
    obtain ⟨m, hm⟩ := (hA (ρ b).val).mp (ρ b).property.1
    have hb : presentationEntry hA n = b := Subtype.ext hn
    refine ⟨_, (hs _).mpr ⟨n, rfl⟩, _, (hs _).mpr ⟨m, rfl⟩, ?_, ?_⟩
    · apply (hR n m).mpr
      rw [hb, hm]
    · rw [class_eq_degreeSet M hLower hd hE (hcols n),
        class_eq_degreeSet M hLower hd hE (hcols m), hn, hm]

theorem graphImage_action {I : CountableIdeal} {a : Degree} {A G : Oracle}
    (hA : ConePresentation.Presented I A) (ρ : I ≃o Cone I a)
    (hG : ∀ v, G v = true ↔ ConePresentation.Graph ρ hA v) (n m : ℕ) :
    ZFSet.pair (realSet.{u} (columns A n)) (realSet (columns A m)) ∈ graphImage A G ↔
      (ρ (presentationEntry hA n)).val = degree (columns A m) := by
  rw [mem_graphImage]
  constructor
  · rintro ⟨i, j, hGij, hpair⟩
    obtain ⟨hi, hj⟩ := ZFSet.pair_inj.mp hpair
    have hi' := realSet_injective hi
    have hj' := realSet_injective hj
    have he : presentationEntry hA n = presentationEntry hA i :=
      Subtype.ext (congrArg degree hi')
    have hh := (hG (Nat.pair i j)).mp hGij
    simpa only [ConePresentation.Graph, Nat.unpair_pair, he, hj'] using hh
  · intro h
    refine ⟨n, m, (hG _).mpr ?_, rfl⟩
    simpa only [ConePresentation.Graph, Nat.unpair_pair] using h

/-- Internal presentation and graph codes decode to internal set objects.
No persistence hypothesis is required once the graph code is supplied. -/
theorem coded_sets (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hC : PersistenceRealClosure.Closed (reals M))
    {p E : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p) (hEM : E ∈ M)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {a : Degree} {A G : Oracle}
    (hA : ConePresentation.Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o Cone I a) (hGM : G ∈ reals M)
    (hG : ∀ v, G v = true ↔ ConePresentation.Graph ρ hA v) :
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
    (mem_columnRange A) hcols (graphImage_action hA ρ hG)
  exact heq ▸ hm

end
end OAI.TuringRigidity.ConeSetGraphs
