/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicEncoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.AtomicForcing
public import LeanPool.TuringConeRigidity.SetModels.NameEncoding

/-!
# Atomic Encoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames
universe u
variable {P : Type u} [Preorder P]

theorem eq_of_encode_eq (l : P → ZFSet.{u}) (hl : Function.Injective l)
    (a b : Name P) (h : a.encode l = b.encode l) (p : P) : EqForces a b p := by
  induction a generalizing b p with
  | mk ι a s ih =>
    cases b with
    | mk κ b t =>
      constructor
      · intro i q _ hs
        have hx : ZFSet.pair ((a i).encode l) (l (s i)) ∈
            Name.encode l (.mk ι a s) := ZFSet.mem_range_self i
        rw [h] at hx
        obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hx
        obtain ⟨hc,ht⟩ := ZFSet.pair_inj.mp hj
        exact ⟨q,le_rfl,j,by simpa only [hl ht] using hs,ih i (b j) hc.symm q⟩
      · intro j q _ ht
        have hx : ZFSet.pair ((b j).encode l) (l (t j)) ∈
            Name.encode l (.mk κ b t) := ZFSet.mem_range_self j
        rw [←h] at hx
        obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hx
        obtain ⟨hc,hs⟩ := ZFSet.pair_inj.mp hi
        exact ⟨q,le_rfl,i,by simpa only [hl hs] using ht,ih i (b j) hc q⟩

theorem eq_encode_congr (l : P → ZFSet.{u}) (hl : Function.Injective l)
    {a b c d : Name P} (hac : a.encode l = c.encode l)
    (hbd : b.encode l = d.encode l) (p : P) : EqForces a b p ↔ EqForces c d p := by
  have ha := eq_of_encode_eq l hl a c hac p
  have hb := eq_of_encode_eq l hl b d hbd p
  exact ⟨fun h => eq_trans c b d p (eq_trans c a b p (eq_symm _ _ _ ha) h) hb,
    fun h => eq_trans a d b p (eq_trans a c d p ha h) (eq_symm _ _ _ hb)⟩

theorem mem_congr_left {a b c : Name P} {p : P} (he : EqForces a b p)
    (h : MemForces a c p) : MemForces b c p := by
  cases c with
  | mk κ c t =>
    intro q hq
    obtain ⟨r,hr,j,hj,hf⟩ := h q hq
    exact ⟨r,hr,j,hj,eq_trans _ _ _ r (eq_symm _ _ _ (eq_mono _ _ (hr.trans hq) he)) hf⟩

theorem mem_congr_right {a b c : Name P} {p : P} (he : EqForces b c p)
    (h : MemForces a b p) : MemForces a c p := by
  cases b with
  | mk κ b t =>
    cases c with
    | mk μ c v =>
      intro q hq
      obtain ⟨r,hr,j,hj,hf⟩ := h q hq
      obtain ⟨w,hw,k,hk,hg⟩ := he.1 j r (hr.trans hq) hj
      exact ⟨w,hw.trans hr,k,hk,eq_trans _ _ _ w (eq_mono _ _ hw hf) hg⟩

theorem mem_encode_congr (l : P → ZFSet.{u}) (hl : Function.Injective l)
    {a b c d : Name P} (hac : a.encode l = c.encode l)
    (hbd : b.encode l = d.encode l) (p : P) : MemForces a b p ↔ MemForces c d p := by
  have ha := eq_of_encode_eq l hl a c hac p
  have hb := eq_of_encode_eq l hl b d hbd p
  exact ⟨fun h => mem_congr_right hb (mem_congr_left ha h),
    fun h => mem_congr_right (eq_symm _ _ _ hb) (mem_congr_left (eq_symm _ _ _ ha) h)⟩

/-- Equality forcing between representatives chosen for two encoded names. -/
noncomputable def EncodedEq {l : P → ZFSet.{u}} (a b : EncodedName l) (p : P) : Prop :=
  EqForces a.property.choose b.property.choose p
/-- Membership forcing between representatives chosen for two encoded names. -/
noncomputable def EncodedMem {l : P → ZFSet.{u}} (a b : EncodedName l) (p : P) : Prop :=
  MemForces a.property.choose b.property.choose p

theorem encodedEq_toEncoded (l : P → ZFSet.{u}) (hl : Function.Injective l)
    (a b : Name P) (p : P) : EncodedEq (a.toEncoded l) (b.toEncoded l) p ↔ EqForces a b p :=
  eq_encode_congr l hl (a.toEncoded l).property.choose_spec
    (b.toEncoded l).property.choose_spec p

theorem encodedMem_toEncoded (l : P → ZFSet.{u}) (hl : Function.Injective l)
    (a b : Name P) (p : P) : EncodedMem (a.toEncoded l) (b.toEncoded l) p ↔ MemForces a b p :=
  mem_encode_congr l hl (a.toEncoded l).property.choose_spec
    (b.toEncoded l).property.choose_spec p

end TuringRigidity.AtomicForcing

end OAI
