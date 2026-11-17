/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructibleTupleSpace.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleSatisfaction
public import LeanPool.TuringConeRigidity.SetModels.ModelNaturalNumbers

/-!
# Constructible Tuple Space
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- The natural-number-indexed graph of a finite tuple of sets. -/
noncomputable def tupleGraph {n : ℕ} (v : Fin n → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin n => ZFSet.pair (natSet i.val) (v i))

theorem tupleGraph_pair {n : ℕ} (v : Fin n → ZFSet.{u}) (i : Fin n) (x : ZFSet.{u}) :
    ZFSet.pair (natSet i.val) x ∈ tupleGraph v ↔ x = v i := by
  rw [tupleGraph,ZFSet.mem_range]
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨hji,hx⟩ := ZFSet.pair_inj.mp hj
    have he : j = i := Fin.ext (natSet_injective hji)
    subst j; exact hx.symm
  · rintro rfl; exact ⟨i,rfl⟩

theorem tupleGraph_function (A : ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) : FunctionGraph (natSet n) A (tupleGraph v) := by
  constructor
  · intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨natSet i.val,(natSet_mem_natSet _ _).mpr i.isLt,v i,hv i,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet n x).mp hx
    exact ⟨v ⟨i,hi⟩,hv _,(tupleGraph_pair v ⟨i,hi⟩ _).mpr rfl,
      fun y _ hy => (tupleGraph_pair v ⟨i,hi⟩ y).mp hy⟩

theorem functionGraph_tuple (A g : ZFSet.{u}) (n : ℕ)
    (hg : FunctionGraph (natSet n) A g) :
    ∃ v : Fin n → ZFSet.{u}, (∀ i, v i ∈ A) ∧ g = tupleGraph v := by
  classical
  have hex (i : Fin n) := hg.2 (natSet i.val) ((natSet_mem_natSet _ _).mpr i.isLt)
  choose v hv hp hu using hex
  refine ⟨v,hv,?_⟩
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := hg.1 z hz
    obtain ⟨i,hi,rfl⟩ := (mem_natSet n x).mp hx
    exact (tupleGraph_pair v ⟨i,hi⟩ y).mpr (hu ⟨i,hi⟩ y hy hz)
  · intro hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact hp i

theorem finite_range_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (n : ℕ) (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ M) : ZFSet.range v ∈ M := by
  induction n with
  | zero =>
    have he : ZFSet.range v = ∅ := by
      apply ZFSet.ext; intro x
      simp only [ZFSet.mem_range,ZFSet.notMem_empty,iff_false]
      rintro ⟨i,_⟩; exact Fin.elim0 i
    rwa [he]
  | succ n ih =>
    have he : ZFSet.range v = ({v 0} : ZFSet.{u}) ∪ ZFSet.range (fun i : Fin n => v i.succ) := by
      apply ZFSet.ext; intro x
      simp only [ZFSet.mem_range,ZFSet.mem_union,ZFSet.mem_singleton,Fin.exists_fin_succ]
      exact or_congr eq_comm Iff.rfl
    rw [he]
    exact binary_union_mem M hM hP hU (singleton_mem M hM hP (hv 0))
      (ih _ (fun i => hv i.succ))

theorem tupleGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ M) : tupleGraph v ∈ M := by
  have hn (k : ℕ) : natSet.{u} k ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨k,rfl⟩)
  exact finite_range_mem M hM hP hU (hn 0) n _
    (fun i => orderedPair_mem M hM hP (hn i.val) (hv i))

theorem tupleCode_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ M) : tupleCode v ∈ M :=
  orderedPair_mem M hM hP (hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩))
    (tupleGraph_mem M hM hP hU hω v hv)

/-- The set of codes of all finite tuples with entries in `A`. -/
noncomputable def tupleSpace (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun t : Σ n : ℕ, Fin n → Conditions A =>
    tupleCode (fun i => label A (t.2 i)))

theorem mem_tupleSpace (A t : ZFSet.{u}) :
    t ∈ tupleSpace A ↔ ∃ (n : ℕ) (v : Fin n → ZFSet.{u}),
      (∀ i, v i ∈ A) ∧ t = tupleCode v := by
  rw [tupleSpace,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨n,v⟩,ht⟩
    exact ⟨n,fun i => label A (v i),fun i => label_mem A (v i),ht.symm⟩
  · rintro ⟨n,v,hv,rfl⟩
    let w : Fin n → Conditions A := fun i => equivShrink A ⟨v i,hv i⟩
    refine ⟨⟨n,w⟩,?_⟩
    congr 1; funext i; simp [w,label]

/-- Bounded formula asserting that a code consists of a finite length and a tuple graph into
`A`. -/
def tupleFormula (o A Q t : ℕ) : Formula :=
  .existsMem o (.existsMem (Q+1)
    (.conj (.orderedPair (t+2) 1 0) (.functionGraph 0 1 (A+2))))

theorem tupleFormula_spec (o A Q t : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega)
    (hQ : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ e A) → tupleGraph v ∈ e Q) :
    (tupleFormula o A Q t).Eval e ↔ e t ∈ tupleSpace (e A) := by
  simp only [tupleFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_functionGraph,
    cons_zero,cons_succ]
  rw [ho,mem_tupleSpace]
  constructor
  · rintro ⟨n,hn,g,_,ht,hg⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨v,hv,rfl⟩ := functionGraph_tuple (e A) g n hg
    exact ⟨n,v,hv,ht⟩
  · rintro ⟨n,v,hv,ht⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ n v hv,ht,
      tupleGraph_function (e A) v hv⟩

theorem tupleSpace_mem (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : tupleSpace A ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,hQdef⟩ := internal_power M hM hT.powerSet
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hA)
  have hQ (n : ℕ) (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) : tupleGraph v ∈ Q := by
    apply (hQdef _).mpr
    refine ⟨tupleGraph_mem M hM hT.pairing hT.union hω v (fun i => hM A hA _ (hv i)),?_⟩
    intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i.val,rfl⟩,_,hv i,rfl⟩
  let e := cons ZFSet.omega (cons A (fun _ => Q))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i
    · exact hω
    · exact hA
    · exact hQM
  have hs := sep_mem M hM hS (tupleFormula 1 2 3 0) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hQM)
  have heq : (ZFSet.prod ZFSet.omega Q).sep
      (fun t => (tupleFormula 1 2 3 0).Eval (cons t e)) = tupleSpace A := by
    apply ZFSet.ext; intro t
    rw [ZFSet.mem_sep,tupleFormula_spec 1 2 3 0 (cons t e) rfl hQ]
    change (t ∈ ZFSet.prod ZFSet.omega Q ∧ t ∈ tupleSpace A) ↔ t ∈ tupleSpace A
    refine ⟨And.right,fun ht => ⟨?_,ht⟩⟩
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    exact ZFSet.mem_prod.mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ n v hv,rfl⟩
  exact heq ▸ hs

end TuringRigidity.RelativeConstructible

end OAI
