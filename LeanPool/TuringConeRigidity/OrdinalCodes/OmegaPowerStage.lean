/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaPowerStage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.HierarchyGraph

/-!
# Omega Power Stage
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

/-- The set code of omega raised to the successor of the input set's rank. -/
noncomputable def omegaNext (x : ZFSet.{u}) : ZFSet.{u} :=
  (Ordinal.omega0 ^ (x.rank+1)).toZFSet

theorem omegaPower_members (a : Ordinal.{u}) (z : ZFSet.{u}) :
    z ∈ (Ordinal.omega0 ^ a).toZFSet ↔ z ∈ (1 : Ordinal.{u}).toZFSet ∨
      ∃ x ∈ a.toZFSet, z ∈ omegaNext x := by
  constructor
  · intro hz
    by_cases ha : a = 0
    · left; simpa [ha] using hz
    · obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨b,hb,n,hn⟩ := (Ordinal.lt_omega0_opow ha).mp hc
      refine Or.inr ⟨b.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hb,?_⟩
      rw [omegaNext,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
      exact hn.trans (Ordinal.opow_mul_lt_opow (Ordinal.natCast_lt_omega0 n) (lt_add_one b))
  · rintro (hz|⟨x,hx,hz⟩)
    · exact Ordinal.toZFSet_monotone (Order.one_le_iff_ne_zero.mpr (Ordinal.opow_ne_zero _
      Ordinal.omega0_ne_zero)) hz
    · obtain ⟨b,hb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      change z ∈ (Ordinal.omega0 ^ (b.toZFSet.rank+1)).toZFSet at hz
      rw [Ordinal.rank_toZFSet] at hz
      exact Ordinal.toZFSet_monotone
        (Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.succ_le_of_lt hb)) hz

/-- A function graph on an ordinal domain obeying the omega-power stage recursion. -/
def OmegaGraph (M d r f : ZFSet.{u}) : Prop :=
  d.IsOrdinal ∧ FunctionGraph d r f ∧
  ∀ x ∈ d, ∀ v ∈ r, ZFSet.pair x v ∈ f →
    ∃ A ∈ M, StageStep (1 : Ordinal.{u}).toZFSet f r x A ∧
      A.IsOrdinal ∧ v = (A.rank*Ordinal.omega0).toZFSet

theorem OmegaGraph.correct {M d r f : ZFSet.{u}} (h : OmegaGraph M d r f)
    (x : ZFSet.{u}) (hx : x ∈ d) (v : ZFSet.{u}) (hv : v ∈ r)
    (hfv : ZFSet.pair x v ∈ f) : v = omegaNext x := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    obtain ⟨A,_,hs,_,rfl⟩ := h.2.2 x hx v hv hfv
    have hxo := h.1.mem hx
    have he : A = (Ordinal.omega0 ^ x.rank).toZFSet := by
      apply ZFSet.ext; intro z
      rw [omegaPower_members,hxo.toZFSet_rank_eq]
      constructor
      · intro hz
        rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
        · exact Or.inl hz
        · exact Or.inr ⟨y,hy,(ih y hy (h.1.subset_of_mem hx hy) w hw hfw) ▸ hz⟩
      · rintro (hz|⟨y,hy,hz⟩)
        · exact hs.1 hz
        · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1.subset_of_mem hx hy)
          rw [← ih y hy (h.1.subset_of_mem hx hy) w hw hfw] at hz
          exact hs.2.2 y hy w hw hfw hz
    rw [he,Ordinal.rank_toZFSet,omegaNext,Ordinal.opow_add_one]

theorem OmegaGraph.mem_iff {M d r f : ZFSet.{u}} (h : OmegaGraph M d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := h.2.1.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx v hv hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := h.2.1.2 x hx
    rw [← h.correct x hx v hv hfv]
    exact hfv

theorem OmegaGraph.unique {M N d r t f g : ZFSet.{u}}
    (hf : OmegaGraph M d r f) (hg : OmegaGraph N d t g) : f = g := by
  apply ZFSet.ext; intro z
  exact (hf.mem_iff z).trans (hg.mem_iff z).symm

theorem omegaStageImage (d f x : ZFSet.{u}) (hd : d.IsOrdinal) (hx : x ∈ d)
    (hf : ∀ z, z ∈ f ↔ ∃ y ∈ d, z = ZFSet.pair y (omegaNext y)) :
    stageImage (1 : Ordinal.{u}).toZFSet x f = (Ordinal.omega0 ^ x.rank).toZFSet := by
  apply ZFSet.ext; intro z
  rw [mem_stageImage,omegaPower_members,(hd.mem hx).toZFSet_rank_eq]
  apply or_congr_right
  constructor
  · rintro ⟨y,hy,w,hfw,hz⟩
    obtain ⟨v,_,hp⟩ := (hf _).mp hfw
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact ⟨y,hy,hz⟩
  · rintro ⟨y,hy,hz⟩
    exact ⟨y,hy,_,(hf _).mpr ⟨y,hd.subset_of_mem hx hy,rfl⟩,hz⟩

end TuringRigidity.OrdinalArithmetic

end OAI
