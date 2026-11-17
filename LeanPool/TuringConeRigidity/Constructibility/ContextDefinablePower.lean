/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ContextDefinablePower.lean.
Also incorporates the shared Context definability proof from upstream
OAI/Computability/DegreeRigidity/Constructibility/ContextHierarchyGraph.lean
under the same Apache-2.0 terms.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.DefSystemCertificate
public import LeanPool.TuringConeRigidity.Syntax.SigmaParameterized

/-!
# Context Definable Power
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem tupleSpace_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) : tupleSpace A ∈
  M := by
  have hS := C.separation
  have hω := C.omega_mem
  obtain ⟨Q,hQM,hQdef⟩ := internal_power M C.transitive C.power
    (product_mem M C.transitive C.pairing C.union C.power hS hω hA)
  have hQ (n : ℕ) (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) : tupleGraph v ∈ Q := by
    apply (hQdef _).mpr
    refine ⟨tupleGraph_mem M C.transitive C.pairing C.union hω v (fun i => C.transitive A hA _ (hv
      i)),?_⟩
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
  have hs := sep_mem M C.transitive hS (tupleFormula 1 2 3 0) e he
    (product_mem M C.transitive C.pairing C.union C.power hS hω hQM)
  have heq : (ZFSet.prod ZFSet.omega Q).sep
      (fun t => (tupleFormula 1 2 3 0).Eval (cons t e)) = tupleSpace A := by
    apply ZFSet.ext; intro t
    rw [ZFSet.mem_sep,tupleFormula_spec 1 2 3 0 (cons t e) rfl hQ]
    change (t ∈ ZFSet.prod ZFSet.omega Q ∧ t ∈ tupleSpace A) ↔ t ∈ tupleSpace A
    refine ⟨And.right,fun ht => ⟨?_,ht⟩⟩
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    exact ZFSet.mem_prod.mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ n v hv,rfl⟩
  exact heq ▸ hs

theorem truthSlice_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) (p :
  SentenceForm) : truthSlice A p ∈ M := by
  have hS := C.separation
  have hω := C.omega_mem
  have hn (n : ℕ) : natSet.{u} n ∈ M := C.transitive _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  obtain ⟨Q,hQM,hQdef⟩ := internal_power M C.transitive C.power
    (product_mem M C.transitive C.pairing C.union C.power hS hω hA)
  have hQ {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) : tupleGraph v ∈ Q := by
    apply (hQdef _).mpr
    refine ⟨tupleGraph_mem M C.transitive C.pairing C.union hω v (fun i => C.transitive A hA _ (hv
      i)),?_⟩
    intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i.val,rfl⟩,_,hv i,rfl⟩
  let e := cons ZFSet.omega (cons A (cons Q (cons (natSet p.bound) natSet)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact hω
    · exact hA
    · exact hQM
    · exact hn _
    · exact hn _
  let φ := tupleTruth p 1 2 3 4 0 (fun i => i+5)
  have hs := sep_mem M C.transitive hS φ e he (tupleSpace_mem_of_context M A C hA)
  have heq : (tupleSpace A).sep (fun t => φ.Eval (cons t e)) = truthSlice A p := by
    apply ZFSet.ext; intro t
    rw [truthSlice,ZFSet.mem_sep,ZFSet.mem_sep]
    apply and_congr_right; intro ht
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    exact (tupleTruth_spec p 1 2 3 4 0 (fun i => i+5) (cons (tupleCode v) e)
      rfl rfl (fun _ _ => rfl) v hv rfl (hQ v hv)).trans (satisfactionSet_record A p v hv).symm
  exact heq ▸ hs

theorem finiteSatisfaction_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) (ps :
  List SentenceForm) : finiteSatisfaction A ps ∈ M := by
  have hω := C.omega_mem
  have hn (n : ℕ) : natSet.{u} n ∈ M := C.transitive _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  apply union_mem M C.transitive C.union
  apply finite_range_mem M C.transitive C.pairing C.union (hn 0)
  intro i
  exact product_mem M C.transitive C.pairing C.union C.power C.separation
    (singleton_mem M C.transitive C.pairing (hn _)) (truthSlice_mem_of_context M A C hA ps[i])

theorem internal_certificate_bound_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) :
    ∃ Q ∈ M,
      (∀ S, S ∈ Q ↔ S ∈ M ∧ S ⊆ ZFSet.prod ZFSet.omega (tupleSpace A)) ∧
      ∀ ps : List SentenceForm, finiteSatisfaction A ps ∈ Q := by
  obtain ⟨Q,hQ,hdef⟩ := internal_power M C.transitive C.power
    (product_mem M C.transitive C.pairing C.union C.power C.separation
      (C.omega_mem) (tupleSpace_mem_of_context M A C hA))
  refine ⟨Q,hQ,hdef,fun ps => (hdef _).mpr ⟨finiteSatisfaction_mem_of_context M A C hA ps,?_⟩⟩
  exact fun z hz => satisfactionSet_subset_product A (finiteSatisfaction_subset A ps hz)

theorem satisfactionSet_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) :
  satisfactionSet A ∈ M := by
  obtain ⟨Q,hQ,_,hf⟩ := internal_family_bound M C.transitive C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  obtain ⟨G,hG,hg⟩ := internal_tuple_graph_bound C hA
  obtain ⟨H,hH,_,hh⟩ := internal_certificate_bound_of_context M A C hA
  have ht := tupleSpace_mem_of_context M A C hA
  let e := cons A (cons (tupleSpace A) (fun _ => ZFSet.omega))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hA
    · exact ht
    · exact C.omega_mem
  have hd := satisfactionWitness_definable C hQ hB hG hH 1 2 0
  have hs := hd.sep_mem C e he (C.prod_mem C.omega_mem ht)
  have heq : (ZFSet.prod ZFSet.omega (tupleSpace A)).sep
      (fun z => SatisfactionWitness Q B G H A (tupleSpace A) z) = satisfactionSet A := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,satisfactionWitness_spec Q B G H A z hf hb hg (fun p => hh (subformulas p))]
    exact ⟨And.right,fun hz => ⟨satisfactionSet_subset_product A hz,hz⟩⟩
  exact heq ▸ hs

theorem definablePower_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) :
  definablePower A ∈ M := by
  obtain ⟨Q,hQ,_,hf⟩ := internal_family_bound M C.transitive C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  obtain ⟨G,hG,hg⟩ := internal_tuple_graph_bound C hA
  have ht := tupleSpace_mem_of_context M A C hA
  have hz := satisfactionSet_mem_of_context M A C hA
  obtain ⟨P,hP,_,hsub⟩ := definablePower_internal_bound M A C.transitive C.separation C.power hA
  let e := cons A (cons (tupleSpace A) (cons (satisfactionSet A) (fun _ => ZFSet.omega)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact hA
    · exact ht
    · exact hz
    · exact C.omega_mem
  have hd := definitionWitness_definable C hQ hB hG 1 2 3 0
  have hs := hd.sep_mem C e he hP
  have heq : P.sep (fun S => DefinitionWitness Q B G A (tupleSpace A) (satisfactionSet A) S) =
      definablePower A := by
    apply ZFSet.ext; intro S
    rw [ZFSet.mem_sep,definitionWitness_spec Q B G A S hf hb hg,← mem_definablePower]
    exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
  exact heq ▸ hs

theorem internal_defSystem_of_context (M : ZFSet.{u}) (C : Context M)
    (Q B A : ZFSet.{u}) (hA : A ∈ M)
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) :
    ∃ G ∈ M, ∃ T ∈ M, ∃ H ∈ M, ∃ Z ∈ M,
      DefSystem Q B A G T H Z (definablePower A) := by
  obtain ⟨G,hG,hg⟩ := internal_tuple_graph_bound C hA
  obtain ⟨H,hH,_,hh⟩ := internal_certificate_bound_of_context M A C hA
  exact ⟨G,hG,tupleSpace A,tupleSpace_mem_of_context M A C hA,H,hH,
    satisfactionSet A,satisfactionSet_mem_of_context M A C hA,
    defSystem_canonical Q B A G H hQ hB hg (fun p => hh (subformulas p))⟩

/-- Definable power is sigma definable under the bounded model Context alone. -/
theorem definablePower_sigmaDefinable_of_context (M : ZFSet.{u}) (C : Context M) :
    SigmaDefinable M (fun e => e 0 = definablePower (e 1)) := by
  obtain ⟨Q,hQ,_,hq⟩ := internal_family_bound M C.transitive C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  have hc := (defSystem_definable C hQ hB 5 3 2 1 0 4).toSigma C.transitive
  have hs := hc.existsSet.existsSet.existsSet.existsSet
  apply hs.congr
  intro e he
  change (∃ G ∈ M, ∃ T ∈ M, ∃ H ∈ M, ∃ Z ∈ M,
    DefSystem Q B (e 1) G T H Z (e 0)) ↔ e 0 = definablePower (e 1)
  constructor
  · rintro ⟨G,_,T,_,H,_,Z,_,h⟩
    exact h.exact hq hb
  · intro h
    rw [h]
    exact internal_defSystem_of_context M C Q B (e 1) (he 1) hq hb

end TuringRigidity.RelativeConstructible

end OAI
