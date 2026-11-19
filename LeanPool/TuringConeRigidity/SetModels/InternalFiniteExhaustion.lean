/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalFiniteExhaustion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalSubsetSequence
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableFamily

/-!
# Internal Finite Exhaustion
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalFiniteExhaustion
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets

/-- The set of the first `n` values of a set-valued sequence. -/
noncomputable def initial (f : ℕ → ZFSet.{0}) (n : ℕ) : ZFSet.{0} :=
  ZFSet.range (fun i : Fin n => f i.val)

theorem mem_initial (f : ℕ → ZFSet.{0}) (n : ℕ) (x : ZFSet.{0}) :
    x ∈ initial f n ↔ ∃ k < n, x = f k := by
  rw [initial,ZFSet.mem_range]
  exact ⟨fun ⟨i,hi⟩ => ⟨i.val,i.isLt,hi.symm⟩,fun ⟨k,hk,hx⟩ => ⟨⟨k,hk⟩,hx.symm⟩⟩

theorem initial_finite (f : ℕ → ZFSet.{0}) (n : ℕ) :
    (initial f n : Set ZFSet.{0}).Finite := by
  rw [initial,ZFSet.coe_range]
  exact Set.finite_range _

theorem initial_subset (A : ZFSet.{0}) (f : ℕ → ZFSet.{0})
    (hf : ∀ n, f n ∈ A) (n : ℕ) : initial f n ⊆ A := by
  intro x hx
  obtain ⟨k,_,rfl⟩ := (mem_initial f n x).mp hx
  exact hf k

/-- Bounded formula asserting that `x` occurs in the graph before the index `n`. -/
def initialFormula (g n x : ℕ) : Formula := .existsMem n (.pairMem 0 (x+1) (g+1))

theorem initialFormula_spec (g n x : ℕ) (e : ℕ → ZFSet.{0})
    (f : ℕ → ZFSet.{0}) (N : ℕ) (hg : e g = orbitGraph f) (hn : e n = natSet N) :
    (initialFormula g n x).Eval e ↔ e x ∈ initial f N := by
  simp only [initialFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,hg,hn]
  rw [mem_initial]
  constructor
  · rintro ⟨k,hk,hkx⟩
    obtain ⟨k,hklt,rfl⟩ := (mem_natSet N k).mp hk
    exact ⟨k,hklt,(orbitGraph_pair f k _).mp hkx⟩
  · rintro ⟨k,hk,hkx⟩
    exact ⟨natSet k,(natSet_mem_natSet k N).mpr hk,(orbitGraph_pair f k _).mpr hkx⟩

theorem initial_sequence_mem (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (f : ℕ → ZFSet.{0}) (hf : ∀ n, f n ∈ A) (hg : orbitGraph f ∈ M) :
    orbitGraph (initial f) ∈ M := by
  exact InternalSubsetSequence.subset_sequence M A hM hT hA (initialFormula 2 1 0)
    (fun _ => orbitGraph f) (fun _ => hg) (initial f) (initial_subset A f hf)
    (fun n _ _ => initialFormula_spec 2 1 0 _ f n rfl rfl)

theorem finite_subsets_finite (A : ZFSet.{0}) (hA : (A : Set ZFSet.{0}).Finite) :
    (finiteSubsets A : Set ZFSet.{0}).Finite := by
  apply Set.Finite.of_injOn (f := fun x : ZFSet.{0} => (x : Set ZFSet.{0}))
    (t := Set.powerset (A : Set ZFSet.{0}))
  · intro x hx
    exact (mem_finiteSubsets_iff A x).mp hx |>.1
  · intro x _ y _ hxy
    exact ZFSet.ext (fun z => Set.ext_iff.mp hxy z)
  · exact hA.powerset

theorem finite_subset_initial (A : ZFSet.{0}) (f : ℕ → ZFSet.{0})
    (honto : ∀ x ∈ A, ∃ n, x = f n) (a : ZFSet.{0}) (ha : a ∈ finiteSubsets A) :
    ∃ n, a ⊆ initial f n := by
  classical
  obtain ⟨k,v,hv,rfl⟩ := (mem_finiteSubsets A a).mp ha
  choose idx hidx using fun i => honto (v i) (hv i)
  refine ⟨Finset.univ.sup idx + 1,?_⟩
  intro x hx
  obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hx
  apply (mem_initial f _ _).mpr
  exact ⟨idx i,Nat.lt_succ_of_le (Finset.le_sup (f := idx) (Finset.mem_univ i)),hidx i⟩

theorem finite_subsets_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hct : InternallyCountable M A) :
    InternallyCountable M (finiteSubsets A) := by
  obtain ⟨g,hg,hfun,honto⟩ := hct
  obtain ⟨f,hf,hfg⟩ := InternalCountableFamily.sequence_of_graph A g hfun
  have hgf : orbitGraph f ∈ M := hfg.symm ▸ hg
  have onto : ∀ x ∈ A, ∃ n, x = f n := by
    intro x hx
    obtain ⟨n,hn,hnx⟩ := honto x hx
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,(orbitGraph_pair f n x).mp (hfg.symm ▸ hnx)⟩
  let U := finiteSubsets A
  let E := fun n => finiteSubsets (initial f n)
  have hsub (n : ℕ) : E n ⊆ U := by
    intro a ha
    obtain ⟨hs,hfin⟩ := (mem_finiteSubsets_iff _ a).mp ha
    exact (mem_finiteSubsets_iff A a).mpr ⟨fun x hx => initial_subset A f hf n (hs hx),hfin⟩
  have hEM : orbitGraph E ∈ M := by
    apply InternalSubsetSequence.subset_sequence M U hM hT (finiteSubsets_mem M A hM hT hA)
      (.allMem 0 (initialFormula 3 2 0)) (fun _ => orbitGraph f) (fun _ => hgf) E hsub
    intro n a ha
    rw [Formula.eval_allMem]
    change (∀ x ∈ a, (initialFormula 3 2 0).Eval
      (cons x (cons a (cons (natSet n) (fun _ => orbitGraph f)))) ) ↔ _
    have heval (x : ZFSet.{0}) := initialFormula_spec 3 2 0
      (cons x (cons a (cons (natSet n) (fun _ => orbitGraph f)))) f n rfl rfl
    constructor
    · intro hs
      exact (mem_finiteSubsets_iff _ a).mpr
        ⟨fun x hx => (heval x).mp (hs x hx),((mem_finiteSubsets_iff A a).mp ha).2⟩
    · intro h x hx
      exact (heval x).mpr (((mem_finiteSubsets_iff _ a).mp h).1 hx)
  apply InternalCountableFiniteUnion.internally_countable_union M U hM hT
    (finiteSubsets_mem M A hM hT hA) E
    (fun n => (mem_finiteSubsets_iff U (E n)).mpr
      ⟨hsub n,finite_subsets_finite _ (initial_finite f n)⟩) hEM
  · intro a ha
    obtain ⟨n,hn⟩ := finite_subset_initial A f onto a ha
    exact ⟨n,(mem_finiteSubsets_iff _ a).mpr ⟨hn,((mem_finiteSubsets_iff A a).mp ha).2⟩⟩
  · exact ⟨∅,(mem_finiteSubsets_iff A ∅).mpr
      ⟨ZFSet.empty_subset A,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩⟩

end TuringRigidity.InternalFiniteExhaustion

end OAI
