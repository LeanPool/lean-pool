/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanExpressionAssembly.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanExpressionSyntax

/-!
# Boolean Expression Assembly
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalBooleanSyntax
open InternalRegularOperations InternalRegularAlgebra

theorem tag_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) {x : ZFSet.{0}} (hx : x ∈ M) : FiniteTerm.tag n x ∈ M :=
  orderedPair_mem M hM hT.pairing
    (hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)) hx

theorem witness_of_certificate (M c B Q S K g t U : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hKM : K ∈ M) (hgM : g ∈ M)
    (hg : Certificate c B Q S K g) (hp : ZFSet.pair t U ∈ g) :
    ∃ L ∈ M, Witness c B Q S L U := by
  obtain ⟨L,hLM,hL,hpair⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity
    (pair_mem M hM hT.pairing hKM hgM)
  have hKL := hL _ hpair K (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hgL := hL _ hpair g (ZFSet.mem_pair.mpr (Or.inr rfl))
  have hsub : K ⊆ L := fun x hx => hL K hKL x hx
  exact ⟨L,hLM,hL,g,hgL,hg.enlarge hsub,t,hsub (hg.step hp).1,hp⟩

theorem seed_certified (M c B Q S U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hUM : U ∈ M) (hUB : U ∈ B) (hUS : U ∈ S) : U ∈ certified M c B Q S := by
  let t := FiniteTerm.tag 0 U
  let K := ({t} : ZFSet.{0})
  let g := ({ZFSet.pair t U} : ZFSet.{0})
  have htM : t ∈ M := tag_mem M hM hT 0 hUM
  have htK : t ∈ K := ZFSet.mem_singleton.mpr rfl
  have hg : Certificate c B Q S K g := by
    intro z hz
    exact ⟨t,htK,U,hUB,ZFSet.mem_singleton.mp hz,Or.inl ⟨hUS,rfl⟩⟩
  exact ZFSet.mem_sep.mpr ⟨hUB,witness_of_certificate M c B Q S K g t U hM hT
    (singleton_mem M hM hT.pairing htM)
    (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing htM hUM)) hg
    (ZFSet.mem_singleton.mpr rfl)⟩

theorem neg_certified (M c B Q S U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hU : U ∈ certified M c B Q S) : neg c U ∈ certified M c B Q S := by
  obtain ⟨hUB,K,hKM,hK,g,hgK,hg,t,htK,hp⟩ := ZFSet.mem_sep.mp hU
  have hUM := ((hB U).mp hUB).1
  have hVM := neg_mem M c U hM hT hc hUM
  have hVB := internal_complement M c B hM hT hc hB hUB
  let s := FiniteTerm.tag 1 t
  have hsM : s ∈ M := tag_mem M hM hT 1 (hM K hKM t htK)
  let L := K ∪ ({s} : ZFSet.{0})
  have hKL : K ⊆ L := fun _ h => ZFSet.mem_union.mpr (Or.inl h)
  have hsL : s ∈ L := ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))
  have hs : Step c B Q S L g s (neg c U) :=
    Or.inr (Or.inl ⟨t,hKL htK,U,hUB,rfl,hp,rfl⟩)
  let f := g ∪ ({ZFSet.pair s (neg c U)} : ZFSet.{0})
  have hf := (hg.enlarge hKL).insert hsL hVB hs
  have hLM : L ∈ M := binary_union_mem M hM hT.pairing hT.union hKM
    (singleton_mem M hM hT.pairing hsM)
  have hfM : f ∈ M := binary_union_mem M hM hT.pairing hT.union (hM K hKM g hgK)
    (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing hsM hVM))
  exact ZFSet.mem_sep.mpr ⟨hVB,witness_of_certificate M c B Q S L f s _ hM hT hLM hfM hf
    (ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl)))⟩

theorem Certificate.sUnion {c B Q S K a : ZFSet.{0}}
    (ha : ∀ g ∈ a, Certificate c B Q S K g) : Certificate c B Q S K (ZFSet.sUnion a) := by
  intro z hz
  obtain ⟨g,hga,hzg⟩ := ZFSet.mem_sUnion.mp hz
  obtain ⟨t,ht,U,hU,he,hs⟩ := ha g hga z hzg
  exact ⟨t,ht,U,hU,he,hs.mono (fun _ h => h) (fun z hz => ZFSet.mem_sUnion.mpr ⟨g,hga,hz⟩)⟩

noncomputable def goodGraphs (a c B Q S K : ZFSet.{0}) : ZFSet.{0} :=
  a.sep (Certificate c B Q S K)

theorem goodGraphs_mem (M a c B Q S K : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) (hK : K ∈ M) :
    goodGraphs a c B Q S K ∈ M := by
  let e := cons K (parameters c B Q S)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i with
    | zero => exact hK
    | succ i => exact parameters_mem M c B Q S hM hT hc hB hQ hS i
  have spec (g : ZFSet.{0}) :
      (certificateFormula 2 3 4 5 1 0 6 7 8).Eval (cons g e) ↔ Certificate c B Q S K g :=
    certificateFormula_spec _ _ _ _ _ _ _ _ _ _ rfl rfl rfl
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (certificateFormula 2 3 4 5 1 0 6 7 8) e he ha
  simpa only [spec,goodGraphs] using hs

noncomputable def children (K F g : ZFSet.{0}) : ZFSet.{0} :=
  K.sep (fun t => ∃ U ∈ F, ZFSet.pair t U ∈ g)

theorem children_mem (M K F g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hF : F ∈ M) (hg : g ∈ M) : children K F g ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 1 0 3)) (cons F (fun _ => g))
    (by intro i; cases i <;> assumption) hK
  simpa only [children,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using hs

end TuringRigidity.BooleanExpressionCertificate

end OAI
