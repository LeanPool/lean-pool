/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/HierarchySyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.HierarchyGraph
public import LeanPool.TuringConeRigidity.Syntax.SigmaParameterizedClosure
public import LeanPool.TuringConeRigidity.Constructibility.UniformDefSuccessor

/-!
# Hierarchy Syntax
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
variable {M : ZFSet.{u}}

theorem stageStep_definable (C : Context M) (s f r x A : ℕ) :
    Definable M (fun e => StageStep (e s) (e f) (e r) (e x) (e A)) := by
  have hn := defAllMem (defOr (member_definable C 0 (s+1))
    ((((defPairMem C 1 0 (f+3)).and (member_definable C 2 0)).existsMem (r+2)).existsMem (x+1))) A
  have hc := defAllMem (defAllMem (defImp (defPairMem C 1 0 (f+2))
    (defSubset C 0 (A+2))) (r+1)) x
  exact (defSubset C s A).and (hn.and hc)

theorem functionGraph_definable (C : Context M) (d r f : ℕ) :
    Definable M (fun e => FunctionGraph (e d) (e r) (e f)) := by
  refine ⟨.functionGraph (2*f) (2*d) (2*r),fun _ => ZFSet.omega,
    fun _ => C.omega_mem,?_⟩
  intro e
  simp only [Formula.eval_functionGraph,mix_even,FunctionGraph]

theorem hierarchyGraph_sigmaDefinable (hM : Transitive M) (hT : SourceT M) (s d r f : ℕ) :
    SigmaDefinable M (fun e => HierarchyGraph M (e s) (e d) (e r) (e f)) := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hd := (defAllMem (defSubset C 0 (d+1)) d).toSigma hM
  have hf := (functionGraph_definable C d r f).toSigma hM
  have hv : SigmaDefinable M (fun e => e 1 = definablePower (e 0)) :=
    (definablePower_sigmaDefinable M hM hT).subst (fun i => if i = 0 then 1 else 0)
  have hs := ((stageStep_definable C (s+3) (f+3) (r+3) 2 0).toSigma hM).and hv
  have hi := SigmaDefinable.impBounded C (defPairMem C 1 0 (f+2)) hs.existsSet
  exact hd.and (hf.and ((hi.allMem hM hT (r+1)).allMem hM hT d))

theorem sigma_binary_relation (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (h : SigmaDefinable M (fun e => P (e 1) (e 0))) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ M, ∀ y ∈ M, p.Realize M (cons y (cons x a)) ↔ P x y := by
  obtain ⟨p,a,ha,hp⟩ := h
  let r : ℕ → ℕ := fun i => if i % 2 = 0 then (if i / 2 = 0 then 0 else 1) else i/2+2
  refine ⟨p.rename r,a,ha,?_⟩
  intro x hx y hy
  rw [SigmaFormula.realize_rename]
  have he : cons y (cons x a) ∘ r = mix (cons y (fun _ => x)) a := by
    apply parity_ext
    · intro n
      cases n with
      | zero => rfl
      | succ n => simp [r,show ¬ 2 * (n+1) ≤ 1 by omega]
    · intro n; simp [r,Nat.add_div]
  change p.Realize M (cons y (cons x a) ∘ r) ↔ _
  rw [he]
  exact hp (cons y (fun _ => x)) (by
    intro i
    cases i
    · exact hy
    · exact hx)

theorem uniform_hierarchy_certificate (M R d q : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ d, ∀ f ∈ M, p.Realize M (cons f (cons x a)) ↔
        ∃ r ∈ M, HierarchyGraph M (seed R) (hull d q x) r f := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hh : Definable M (fun e => e 1 ∈ q ∧ Transitive (e 1) ∧ e 3 ∈ e 1 ∧
      ∀ b ∈ q, Transitive b → e 3 ∈ b → e 1 ⊆ b) := by
    refine ⟨.isHull 2 6 1 3,cons d (fun _ => q),?_,?_⟩
    · intro i
      cases i with
      | zero => exact hdM
      | succ i => exact hqM
    · intro e
      simp [Formula.eval_isHull,mix,cons]
  have hg : SigmaDefinable M (fun e => HierarchyGraph M (seed R) (e 1) (e 0) (e 2)) := by
    have h := hierarchyGraph_sigmaDefinable hM hT 0 2 1 3
    have eq := (equal_param hs 0).toSigma hM
    have hx := (eq.and h).existsSet
    exact hx.congr (fun e _ => by simp [hs])
  have hc := (hh.toSigma hM).and hg
  obtain ⟨p,a,ha,hp⟩ := sigma_binary_relation (fun x f =>
    ∃ c ∈ M, ∃ r ∈ M, (c ∈ q ∧ Transitive c ∧ x ∈ c ∧
      ∀ b ∈ q, Transitive b → x ∈ b → c ⊆ b) ∧ HierarchyGraph M (seed R) c r f)
    hc.existsSet.existsSet
  refine ⟨p,a,ha,?_⟩
  intro x hx f hf
  rw [hp x (hM d hdM x hx) f hf]
  constructor
  · rintro ⟨c,hc,r,hr,hh,hg⟩
    have he := (isHull_iff M d q hM C.separation hdM hqM hd hq hx hc).mp hh
    subst c
    exact ⟨r,hr,hg⟩
  · rintro ⟨r,hr,hg⟩
    have hc := hull_mem M d q hM C.separation hdM hqM (hM d hdM x hx)
    exact ⟨_,hc,r,hr,(isHull_iff M d q hM C.separation hdM hqM hd hq hx hc).mpr rfl,hg⟩

end TuringRigidity.RelativeConstructible

end OAI
