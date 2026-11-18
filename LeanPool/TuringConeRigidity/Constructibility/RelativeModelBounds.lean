/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelBounds.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelSyntax

/-!
# Relative Model Bounds
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions InternalRank
universe u

theorem relative_level_bound (M R a : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (ha : a ∈ M)
    (h : ∀ x ∈ a, InRelativeModel M R x) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ a ⊆ level R o := by
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation
    (fun x o : ZFSet.{u} => o.IsOrdinal ∧ x ∈ stage R o)
    (relativeLevel_sigmaDefinable M R hM hT hR)
  obtain ⟨W,hW,hbound⟩ := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
    p e he a ha (by
      intro x hx
      obtain ⟨o,ho,hxo⟩ := h x hx
      exact ⟨o.toZFSet,ho,(hp x (hM a ha x hx) o.toZFSet ho).mpr
        ⟨ZFSet.isOrdinal_toZFSet o,hxo⟩⟩)
  have hr : W.rank.toZFSet ∈ M := by
    rw [← rankSet_eq_ordinal]
    exact rankSet_mem_ground M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hW
  refine ⟨W.rank,hr,?_⟩
  intro x hx
  obtain ⟨o,ho,hxo⟩ := hbound x hx
  obtain ⟨hord,hxo⟩ := (hp x (hM a ha x hx) o (hM W hW o ho)).mp hxo
  have hxl : x ∈ level R o.rank := by
    change x ∈ stage R o.rank.toZFSet
    rwa [hord.toZFSet_rank_eq]
  exact level_mono R (ZFSet.rank_lt_of_mem ho).le hxl

theorem SigmaDefinable.internal_separation {M : ZFSet.{u}}
    {P : (ℕ → ZFSet.{u}) → Prop} (h : SigmaDefinable M P)
    (hM : Transitive M) (hT : SourceT M) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    a.sep (fun x => P (cons x e)) ∈ M := by
  obtain ⟨p,d,hd,hp⟩ := h
  have hm : ∀ i, mix e d i ∈ M := by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _
  have hs := sigma_sep_mem M hM hT.separation.finitePrefix
    (p.rename bindSlots) (mix e d) hm ha
  have eq : a.sep (fun x => (p.rename bindSlots).Realize M (cons x (mix e d))) =
      a.sep (fun x => P (cons x e)) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep]
    apply and_congr_right; intro hx
    rw [SigmaFormula.realize_rename]
    change p.Realize M (cons x (mix e d) ∘ bindSlots) ↔ _
    rw [bind_mix]
    exact hp _ (by
      intro i
      cases i
      · exact hM a ha x hx
      · exact he _)
  exact eq ▸ hs

theorem relative_part_mem (M R a : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (ha : a ∈ M) :
    a.sep (InRelativeModel M R) ∈ M := by
  exact SigmaDefinable.internal_separation (relativeModel_sigmaDefinable M R hM hT hR)
    hM hT (fun _ => R) (fun _ => hR) ha

theorem relative_part_bounded (M R a : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (ha : a ∈ M) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧
      ∀ x ∈ a, InRelativeModel M R x ↔ x ∈ level R o := by
  obtain ⟨o,ho,hbound⟩ := relative_level_bound M R (a.sep (InRelativeModel M R))
    hM hT hR (relative_part_mem M R a hM hT hR ha)
    (fun _ hx => (ZFSet.mem_sep.mp hx).2)
  exact ⟨o,ho,fun x hx => ⟨fun h => hbound (ZFSet.mem_sep.mpr ⟨hx,h⟩),
    fun h => ⟨o,ho,h⟩⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
