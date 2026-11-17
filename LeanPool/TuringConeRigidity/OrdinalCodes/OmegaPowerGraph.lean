/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaPowerGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
The weak omega-graph proofs are shared from upstream
OrdinalCodes/OmegaRecursionSchemas.lean.
The graph recognition proof with explicit value closure is shared from upstream
SetModels/ExactOmegaGraph.lean.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerStage
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductClosure
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductReplacement

/-!
# Omega Power Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem insert_self_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) {x : ZFSet.{u}} (hx : x ∈ M) : insert x x ∈ M := by
  have he : insert x x = ({x} : ZFSet.{u}) ∪ x := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  rw [he]
  exact binary_union_mem M hM hP hU (singleton_mem M hM hP hx) hx

/-- Product sigma semantics uses the explicit replacement schema. -/
theorem productSigma_of_context (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSigma.Realize M e ↔ e 0 = (a*b).toZFSet := by
  rw [← sigma_sat,productSigma_sentence]
  have haM : a.toZFSet ∈ M := ha ▸ he 1
  have hbM : b.toZFSet ∈ M := hb ▸ he 2
  obtain ⟨_,f,hf,hc⟩ := ordinal_mul_internal_schemas M C.transitive C.pairing C.union
    C.power C.separation hRep a b haM hbM
  exact productSentence_spec_of_certificate M C.transitive e he a b ha hb
    (product_mem M C.transitive C.pairing C.union C.power C.separation hbM haM)
    (productRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation haM hbM)
    ⟨f,hf,hc⟩

/-- Exact graph pairs and membership of their power values determine an omega graph. -/
theorem omegaGraph_of_exact_pairs_of_value_mem (M d f : ZFSet.{u}) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x))
    (hval : ∀ x ∈ d, (Ordinal.omega0 ^ x.rank).toZFSet ∈ M) :
    OmegaGraph M d (iterUnion 2 f) f := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = omegaNext x := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩; exact ⟨x,hx,rfl⟩
  refine ⟨hd,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,_,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    refine ⟨(Ordinal.omega0 ^ x.rank).toZFSet,
      hval x hx,?_,ZFSet.isOrdinal_toZFSet _,?_⟩
    · refine ⟨?_,?_,?_⟩
      · intro z hz; exact (omegaPower_members x.rank z).mpr (Or.inl hz)
      · intro z hz
        rcases (omegaPower_members x.rank z).mp hz with hz|⟨y,hy,hz⟩
        · exact Or.inl hz
        · rw [(hd.mem hx).toZFSet_rank_eq] at hy
          have hp := (hpair y _).mpr ⟨hd.subset_of_mem hx hy,rfl⟩
          exact Or.inr ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
      · intro y hy w _ hw z hz
        rw [(hpair y w).mp hw |>.2] at hz
        exact (omegaPower_members x.rank z).mpr
          (Or.inr ⟨y,(hd.mem hx).toZFSet_rank_eq.symm ▸ hy,hz⟩)
    · rw [omegaNext,Ordinal.opow_add_one,Ordinal.rank_toZFSet]

/-- An explicit omega graph is valid in a bounded context. -/
theorem omegaGraph_of_mem_iff_of_context (M d f : ZFSet.{u}) (C : Context M)
    (hdM : d ∈ M) (hfM : f ∈ M) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x)) :
    OmegaGraph M d (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.transitive _ (omega_mem M C.transitive C.separation C.infinity) _
      ((mem_omega _).mpr ⟨1,rfl⟩)
  apply omegaGraph_of_exact_pairs_of_value_mem M d f hd hf
  intro x hx
  have hA := omegaStageImage d f x hd hx hf
  exact hA ▸ stageImage_mem_of_context M C h1 (C.transitive d hdM x hx) hfM

/-- Omega multiplication is definable using replacement. -/
theorem mulOmega_sigmaDefinable_of_context (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
  M) :
    SigmaDefinable M (fun e => (e 1).IsOrdinal ∧ e 0 = ((e 1).rank*Ordinal.omega0).toZFSet) := by
  have ho := omega_mem M C.transitive C.separation C.infinity
  let p := SigmaFormula.conj (.bounded (ordinalFormula 2))
    (productSigma.rename (fun i => if i = 0 then 0 else if i = 1 then 2 else 1))
  refine ⟨p,fun _ => ZFSet.omega,fun _ => ho,?_⟩
  intro e he
  rw [SigmaFormula.realize_conj]
  have hoSem : (SigmaFormula.bounded (ordinalFormula 2)).Realize M
      (mix e (fun _ => ZFSet.omega)) ↔ (e 1).IsOrdinal := by
    rw [SigmaFormula.Realize,Formula.absolute _ M C.transitive _ (by
      intro i; unfold mix
      split
      · exact he _
      · exact ho),eval_ordinalFormula]
    rfl
  rw [hoSem]
  apply and_congr_right; intro heo
  rw [SigmaFormula.realize_rename]
  exact productSigma_of_context M C hRep _ (by
    intro i; change mix e (fun _ => ZFSet.omega)
      (if i = 0 then 0 else if i = 1 then 2 else 1) ∈ M
    split
    · exact he 0
    split
    · exact he 1
    exact ho) (e 1).rank Ordinal.omega0 heo.toZFSet_rank_eq.symm toZFSet_omega.symm

/-- Omega graphs are definable under replacement and collection. -/
theorem omegaGraph_sigmaDefinable_of_schemas (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (d r f : ℕ) : SigmaDefinable M (fun e => OmegaGraph M (e d) (e r) (e f)) := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.nat_mem 1
  have hs : SigmaDefinable M (fun e =>
      StageStep (1 : Ordinal.{u}).toZFSet (e (f+3)) (e (r+3)) (e 2) (e 0)) := by
    have hb := (stageStep_definable C 0 (f+4) (r+4) 3 1).toSigma C.transitive
    have hc := ((equal_param h1 0).toSigma C.transitive).and hb
    exact hc.existsSet.congr (fun e _ => by simp [h1])
  have hv : SigmaDefinable M (fun e => (e 0).IsOrdinal ∧
      e 1 = ((e 0).rank*Ordinal.omega0).toZFSet) :=
    (mulOmega_sigmaDefinable_of_context M C hRep).subst (fun i => if i = 0 then 1 else 0)
  have hi := SigmaDefinable.impBounded C (defPairMem C 1 0 (f+2)) (hs.and hv).existsSet
  exact ((ordinal_definable C d).toSigma C.transitive).and
    (((functionGraph_definable C d r f).toSigma C.transitive).and
      ((hi.allMem_collection C hRep hColl (r+1)).allMem_collection C hRep hColl d))

/-- One fixed formula and environment certify all successor omega graphs. -/
theorem uniform_omega_certificate_of_schemas (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ f ∈ M, p.Realize M (cons f (cons x e)) ↔
        ∃ r ∈ M, OmegaGraph M (insert x x) r f := by
  have hd : Definable M (fun e => e 0 = insert (e 3) (e 3)) := by
    refine ⟨.successor 0 6,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hg := (hd.toSigma C.transitive).and
    (omegaGraph_sigmaDefinable_of_schemas M C hRep hColl 0 1 2)
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation (fun x f => ∃ r ∈ M,
    ∃ d ∈ M, d = insert x x ∧ OmegaGraph M d r f) hg.existsSet.existsSet
  refine ⟨p,e,he,?_⟩
  intro x hx f hf
  rw [hp x hx f hf]
  constructor
  · rintro ⟨r,hr,d,_,rfl,h⟩; exact ⟨r,hr,h⟩
  · rintro ⟨r,hr,h⟩
    exact ⟨r,hr,insert x x,insert_self_mem M C.transitive C.pairing C.union hx,rfl,h⟩

theorem omegaGraph_of_mem_iff (M d f : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hdM : d ∈ M) (hfM : f ∈ M) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x)) :
    OmegaGraph M d (iterUnion 2 f) f := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  exact omegaGraph_of_mem_iff_of_context M d f C hdM hfM hd hf

theorem mulOmega_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    SigmaDefinable M (fun e => (e 1).IsOrdinal ∧ e 0 = ((e 1).rank*Ordinal.omega0).toZFSet) := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  exact mulOmega_sigmaDefinable_of_context M C hT.replacement.finitePrefix

theorem omegaGraph_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (d r f : ℕ) : SigmaDefinable M (fun e => OmegaGraph M (e d) (e r) (e f)) := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  exact omegaGraph_sigmaDefinable_of_schemas M C hT.replacement.finitePrefix hColl d r f

theorem uniform_omega_certificate (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ f ∈ M, p.Realize M (cons f (cons x e)) ↔
        ∃ r ∈ M, OmegaGraph M (insert x x) r f := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  exact uniform_omega_certificate_of_schemas M C hT.replacement.finitePrefix hColl

end TuringRigidity.OrdinalArithmetic

end OAI
