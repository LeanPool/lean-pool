/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaSeparationName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaDefinability
public import LeanPool.TuringConeRigidity.Syntax.SigmaInterpretation
public import LeanPool.TuringConeRigidity.SetModels.NameSupport

/-!
# Sigma Separation Name
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem sigma_sep_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : SigmaSeparation M)
    (φ : SigmaFormula) (env : ℕ → ZFSet.{u}) (he : ∀ i, env i ∈ M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ZFSet.sep (fun x => φ.Realize M (cons x env)) a ∈ M := by
  obtain ⟨b,hb,hdef⟩ := hS φ env he a ha
  have eq : b = ZFSet.sep (fun x => φ.Realize M (cons x env)) a := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · intro hx; exact (hdef x (hM b hb x hx)).mp hx
    · intro hx; exact (hdef x (hM a ha x hx.1)).mpr hx
  exact eq ▸ hb

end TuringRigidity.BoundedSetTheory

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem sigma_separation_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : SigmaSeparation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : SigmaFormula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧ ∀ x,
      x ∈ (a.restrict (label c) B).val G.carrier ↔ x ∈ a.val G.carrier ∧
        φ.Realize (genericExtensionSet M c G.carrier)
          (cons x (fun i => (e i).val G.carrier)) := by
  let env := cons c (cons o (fun i => (e i).encode (label c)))
  have henv : ∀ i, env i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hc
    rcases i with _ | i
    · exact hoM
    exact he i
  let ψ := SigmaFormula.existsSet (.existsSet
    (SigmaFormula.andBounded (.orderedPair 2 1 0)
      (SigmaCode.forcing φ 3 4 0 (push 1 (fun i => i+5)))))
  let B := ZFSet.sep (fun z => ψ.Realize M (cons z env)) (a.support (label c))
  have hBM : B ∈ M := sigma_sep_mem M hM hS ψ env henv
    (support_mem M hM hP hU hPow hS.bounded hc hoM ho a ha)
  have hBsub : B ⊆ a.support (label c) := fun z hz => (ZFSet.mem_sep.mp hz).1
  have hai (i) : (a.child i).encode (label c) ∈ M :=
    names_childClosed M c hM a ha _ (child_relation a i)
  have hpush (i) (n) : (push (a.child i) e n).encode (label c) ∈ M := by
    cases n with
    | zero => exact hai i
    | succ n => exact he n
  have hpair (z x q : ZFSet.{u}) (hz : z ∈ M) (hx : x ∈ M) (hq : q ∈ M) :
      (Formula.orderedPair 2 1 0).Realize M (cons q (cons x (cons z env))) ↔ z = ZFSet.pair x q :=
        by
    rw [Formula.absolute _ M hM _ (by
      intro n
      rcases n with _ | n
      · exact hq
      rcases n with _ | n
      · exact hx
      rcases n with _ | n
      · exact hz
      exact henv n)]
    exact Formula.eval_orderedPair 2 1 0 _
  have hB (i : a.arity) (q : Conditions c) (hq : q ≤ a.tag i) :
      ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ B ↔
        SigmaForces M (push (a.child i) e) φ q := by
    let z := ZFSet.pair ((a.child i).encode (label c)) (label c q)
    have hqM := hM c hc _ (label_mem c q)
    have hz : z ∈ M := orderedPair_mem M hM hP (hai i) hqM
    have query := realize_sigmaForcing M hM hP hU hPow hS.bounded hR hI ho φ
      (push (a.child i) e) q
      (cons (label c q) (cons ((a.child i).encode (label c)) (cons z env)))
      (by
        intro n
        rcases n with _ | n
        · exact hqM
        rcases n with _ | n
        · exact hai i
        rcases n with _ | n
        · exact hz
        exact henv n)
      3 4 0 (push 1 (fun n => n+5)) rfl rfl rfl
      (by intro n; cases n <;> rfl)
    have hs : z ∈ a.support (label c) := ZFSet.mem_range.mpr ⟨⟨i,⟨q,hq⟩⟩,rfl⟩
    change z ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep,and_iff_right hs]
    simp only [ψ,SigmaFormula.Realize,SigmaFormula.realize_andBounded]
    constructor
    · rintro ⟨x,hx,r,hr,hxr,hφ⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp ((hpair z x r hz hx hr).mp hxr)
      exact query.mp hφ
    · intro hφ
      exact ⟨_,hai i,_,hqM,(hpair z _ _ hz (hai i) hqM).mpr rfl,query.mpr hφ⟩
  have ht (i : a.arity) :
      φ.Realize (genericExtensionSet M c G.carrier)
        (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        ∃ p ∈ G.carrier, SigmaForces M (push (a.child i) e) φ p := by
    have hev : (fun n => (push (a.child i) e n).val G.carrier) =
        cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier) := by
      funext n; cases n <;> rfl
    rw [←hev]
    exact internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG φ _ (hpush i)
  refine ⟨B,hBM,hBsub,fun x => ?_⟩
  constructor
  · intro hx
    have hxa := a.val_restrict_subset (label c) B G hx
    obtain ⟨i,q,hqi,hqb,hqG,hix⟩ := (a.mem_val_restrict (label c) B G.carrier x).mp hx
    have hφ := (ht i).mpr ⟨q,hqG,(hB i q hqi).mp hqb⟩
    exact ⟨hxa,hix ▸ hφ⟩
  · rintro ⟨hxa,hφ⟩
    obtain ⟨i,hi,hix⟩ := (a.mem_val_children G.carrier x).mp hxa
    obtain ⟨p,hp,hf⟩ := (ht i).mp (hix ▸ hφ)
    obtain ⟨q,hq,hqp,hqi⟩ := G.directed hp hi
    exact (a.mem_val_restrict (label c) B G.carrier x).mpr
      ⟨i,q,hqi,(hB i q hqi).mpr (sigma_mono M φ _ hqp hf),hq,hix⟩

end TuringRigidity.BoundedForcing

end OAI
