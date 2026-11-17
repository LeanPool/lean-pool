/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaRecursionSchemas.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerGraph
public import LeanPool.TuringConeRigidity.Constructibility.ContextHierarchyGraph

/-!
# Omega Recursion Schemas
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem productSigma_context (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
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

theorem omegaGraph_of_mem_iff_context (M d f : ZFSet.{u}) (C : Context M)
    (hdM : d ∈ M) (hfM : f ∈ M) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x)) :
    OmegaGraph M d (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.transitive _ (omega_mem M C.transitive C.separation C.infinity) _ ((mem_omega _).mpr
      ⟨1,rfl⟩)
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
    have hA := omegaStageImage d f x hd hx hf
    refine ⟨(Ordinal.omega0 ^ x.rank).toZFSet,
      hA ▸ stageImage_mem_context M C h1 (C.transitive d hdM x hx) hfM,?_,ZFSet.isOrdinal_toZFSet
        _,?_⟩
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

theorem mulOmega_sigmaDefinable_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
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
  exact productSigma_context M C hRep _ (by
    intro i; change mix e (fun _ => ZFSet.omega)
      (if i = 0 then 0 else if i = 1 then 2 else 1) ∈ M
    split
    · exact he 0
    split
    · exact he 1
    exact ho) (e 1).rank Ordinal.omega0 heo.toZFSet_rank_eq.symm toZFSet_omega.symm

theorem omegaGraph_sigmaDefinable_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
  M) (hColl : SigmaCollection M)
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
    (mulOmega_sigmaDefinable_schemas M C hRep).subst (fun i => if i = 0 then 1 else 0)
  have hi := SigmaDefinable.impBounded C (defPairMem C 1 0 (f+2)) (hs.and hv).existsSet
  exact ((ordinal_definable C d).toSigma C.transitive).and
    (((functionGraph_definable C d r f).toSigma C.transitive).and
      ((hi.allMem_collection C hRep hColl (r+1)).allMem_collection C hRep hColl d))

theorem uniform_omega_certificate_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
  M) (hColl : SigmaCollection M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ f ∈ M, p.Realize M (cons f (cons x e)) ↔
        ∃ r ∈ M, OmegaGraph M (insert x x) r f := by
  have hd : Definable M (fun e => e 0 = insert (e 3) (e 3)) := by
    refine ⟨.successor 0 6,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hg := (hd.toSigma C.transitive).and (omegaGraph_sigmaDefinable_schemas M C hRep hColl 0 1 2)
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation (fun x f => ∃ r ∈ M,
    ∃ d ∈ M, d = insert x x ∧ OmegaGraph M d r f) hg.existsSet.existsSet
  refine ⟨p,e,he,?_⟩
  intro x hx f hf
  rw [hp x hx f hf]
  constructor
  · rintro ⟨r,hr,d,_,rfl,h⟩; exact ⟨r,hr,h⟩
  · rintro ⟨r,hr,h⟩
    exact ⟨r,hr,insert x x,insert_self_mem M C.transitive C.pairing C.union hx,rfl,h⟩

end TuringRigidity.OrdinalArithmetic

end OAI
