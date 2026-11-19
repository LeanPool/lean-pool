/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCountableProduct.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalFiniteExhaustion

/-!
# Internal Countable Product
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCountableProduct
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteExhaustion

theorem finite_product (A B : ZFSet.{0})
    (hA : (A : Set ZFSet.{0}).Finite) (hB : (B : Set ZFSet.{0}).Finite) :
    (ZFSet.prod A B : Set ZFSet.{0}).Finite := by
  apply ((hA.prod hB).image (fun t => ZFSet.pair t.1 t.2)).subset
  intro z hz
  obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
  exact ⟨(x,y),⟨hx,hy⟩,hz.symm⟩

/-- Bounded formula pairing entries in two finite initial segments of enumeration graphs. -/
def rectangleFormula (A B f g n p : ℕ) : Formula :=
  .existsMem A (.existsMem (B+1) (.conj (.orderedPair (p+2) 1 0)
    (.conj (initialFormula (f+2) (n+2) 1) (initialFormula (g+2) (n+2) 0))))

theorem rectangleFormula_spec (A B f g n p : ℕ) (e : ℕ → ZFSet.{0})
    (F G : ℕ → ZFSet.{0}) (N : ℕ)
    (hF : ∀ k, F k ∈ e A) (hG : ∀ k, G k ∈ e B)
    (hf : e f = orbitGraph F) (hg : e g = orbitGraph G) (hn : e n = natSet N) :
    (rectangleFormula A B f g n p).Eval e ↔ e p ∈ ZFSet.prod (initial F N) (initial G N) := by
  simp only [rectangleFormula,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨x,_,y,_,hp,hx,hy⟩
    exact ZFSet.mem_prod.mpr ⟨x,
      (initialFormula_spec (f+2) (n+2) 1 _ F N hf hn).mp hx,y,
      (initialFormula_spec (g+2) (n+2) 0 _ G N hg hn).mp hy,hp⟩
  · intro hp
    obtain ⟨x,hx,y,hy,hp⟩ := ZFSet.mem_prod.mp hp
    exact ⟨x,initial_subset (e A) F hF N hx,y,initial_subset (e B) G hG N hy,hp,
      (initialFormula_spec (f+2) (n+2) 1 _ F N hf hn).mpr hx,
      (initialFormula_spec (g+2) (n+2) 0 _ G N hg hn).mpr hy⟩

theorem product_countable (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M)
    (hcA : InternallyCountable M A) (hcB : InternallyCountable M B) :
    InternallyCountable M (ZFSet.prod A B) := by
  obtain ⟨f,hf,hff,hfo⟩ := hcA
  obtain ⟨g,hg,hgf,hgo⟩ := hcB
  obtain ⟨F,hF,hFf⟩ := InternalCountableFamily.sequence_of_graph A f hff
  obtain ⟨G,hG,hGg⟩ := InternalCountableFamily.sequence_of_graph B g hgf
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA hB
  let E := fun n => ZFSet.prod (initial F n) (initial G n)
  have hsub (n : ℕ) : E n ⊆ ZFSet.prod A B := by
    intro z hz
    obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
    exact ZFSet.mem_prod.mpr ⟨x,initial_subset A F hF n hx,y,initial_subset B G hG n hy,hz⟩
  have hgraph : orbitGraph E ∈ M := by
    let e := cons A (cons B (cons f (fun _ => g)))
    have he : ∀ i, e i ∈ M := by
      intro i; rcases i with _|_|_|i
      · exact hA
      · exact hB
      · exact hf
      · exact hg
    exact InternalSubsetSequence.subset_sequence M _ hM hT hprod
      (rectangleFormula 2 3 4 5 1 0) e he E hsub
      (fun n _ _ => rectangleFormula_spec 2 3 4 5 1 0 _ F G n hF hG hFf.symm hGg.symm rfl)
  apply InternalCountableFiniteUnion.internally_countable_union M _ hM hT hprod E
    (fun n => (mem_finiteSubsets_iff _ (E n)).mpr
      ⟨hsub n,finite_product _ _ (initial_finite F n) (initial_finite G n)⟩) hgraph
  · intro z hz
    obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨i,hi,hix⟩ := hfo x hx
    obtain ⟨j,hj,hjy⟩ := hgo y hy
    obtain ⟨i,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨j,rfl⟩ := (mem_omega j).mp hj
    refine ⟨max i j + 1,ZFSet.mem_prod.mpr ⟨x,?_,y,?_,hz⟩⟩
    · exact (mem_initial F _ x).mpr
        ⟨i,Nat.lt_succ_of_le (Nat.le_max_left i j),(orbitGraph_pair F i x).mp (hFf.symm ▸ hix)⟩
    · exact (mem_initial G _ y).mpr
        ⟨j,Nat.lt_succ_of_le (Nat.le_max_right i j),(orbitGraph_pair G j y).mp (hGg.symm ▸ hjy)⟩
  · exact ⟨ZFSet.pair (F 0) (G 0),ZFSet.pair_mem_prod.mpr ⟨hF 0,hG 0⟩⟩

theorem product_empty_left (B : ZFSet.{0}) : ZFSet.prod ∅ B = ∅ := by
  apply ZFSet.ext; intro z; simp [ZFSet.mem_prod]

theorem product_empty_right (A : ZFSet.{0}) : ZFSet.prod A ∅ = ∅ := by
  apply ZFSet.ext; intro z; simp [ZFSet.mem_prod]

theorem product_countable_or_empty (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M)
    (hcA : A = ∅ ∨ InternallyCountable M A) (hcB : B = ∅ ∨ InternallyCountable M B) :
    ZFSet.prod A B = ∅ ∨ InternallyCountable M (ZFSet.prod A B) := by
  rcases hcA with rfl|hcA
  · exact Or.inl (product_empty_left B)
  rcases hcB with rfl|hcB
  · exact Or.inl (product_empty_right A)
  exact Or.inr (product_countable M A B hM hT hA hB hcA hcB)

theorem omega_countable (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    InternallyCountable M ZFSet.omega := by
  have hω := sourceT_omega_mem M hM hT
  have hn (n : ℕ) : natSet.{0} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  let e : ℕ → ZFSet.{0} := fun _ => ZFSet.omega
  let φ : Formula := .existsMem 1 (.orderedPair 1 0 0)
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph natSet := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e,mem_orbitGraph]
    exact ⟨fun ⟨x,hx,hz⟩ => by obtain ⟨n,rfl⟩ := (mem_omega x).mp hx; exact ⟨n,hz⟩,
      fun ⟨n,hz⟩ => ⟨natSet n,hn n,hz⟩⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e (fun _ => hω)
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hω)
  have heq : (ZFSet.prod ZFSet.omega ZFSet.omega).sep (fun z => φ.Eval (cons z e)) =
      orbitGraph natSet := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function _ natSet hn).1 z hz),hz⟩⟩
  refine ⟨orbitGraph natSet,heq ▸ hs,orbitGraph_function _ natSet hn,?_⟩
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact ⟨natSet n,hn n,(orbitGraph_pair natSet n _).mpr rfl⟩

end TuringRigidity.InternalCountableProduct

end OAI
