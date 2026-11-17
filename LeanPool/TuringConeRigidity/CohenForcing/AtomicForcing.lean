/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/AtomicForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameEncoding

/-!
# Atomic Forcing
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames CountableForcing
universe u
variable {P : Type u} [Preorder P]

def Below (p t : P) (A : P → Prop) : Prop :=
  ∀ q, q ≤ p → q ≤ t → ∃ r, r ≤ q ∧ A r

def EqForces : Name P → Name P → P → Prop
  | .mk _ a s, .mk _ b t, p =>
    (∀ i, Below p (s i) (fun r => ∃ j, r ≤ t j ∧ EqForces (a i) (b j) r)) ∧
    (∀ j, Below p (t j) (fun r => ∃ i, r ≤ s i ∧ EqForces (a i) (b j) r))

def MemForces (a : Name P) : Name P → P → Prop
  | .mk _ b t, p => ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ j, r ≤ t j ∧ EqForces a (b j) r

theorem eq_mono (a b : Name P) {p q : P} (hqp : q ≤ p)
    (h : EqForces a b p) : EqForces a b q := by
  cases a with
  | mk ι a s =>
    cases b with
    | mk κ b t =>
      exact ⟨fun i r hr hs => h.1 i r (hr.trans hqp) hs,
        fun j r hr ht => h.2 j r (hr.trans hqp) ht⟩

theorem mem_mono (a b : Name P) {p q : P} (hqp : q ≤ p)
    (h : MemForces a b p) : MemForces a b q := by
  cases b with
  | mk κ b t => exact fun r hr => h r (hr.trans hqp)

theorem eq_refl (a : Name P) (p : P) : EqForces a a p := by
  induction a generalizing p with
  | mk ι a s ih =>
    exact ⟨fun i q _ hq => ⟨q,le_rfl,i,hq,ih i q⟩,
      fun i q _ hq => ⟨q,le_rfl,i,hq,ih i q⟩⟩

theorem eq_symm (a b : Name P) (p : P) : EqForces a b p → EqForces b a p := by
  induction a generalizing b p with
  | mk ι a s ih =>
    cases b with
    | mk κ b t =>
      intro h
      constructor
      · intro j q hq ht
        obtain ⟨r,hr,i,hi,he⟩ := h.2 j q hq ht
        exact ⟨r,hr,i,hi,ih i (b j) r he⟩
      · intro i q hq hs
        obtain ⟨r,hr,j,hj,he⟩ := h.1 i q hq hs
        exact ⟨r,hr,j,hj,ih i (b j) r he⟩

theorem eq_trans (a b c : Name P) (p : P)
    (hab : EqForces a b p) (hbc : EqForces b c p) : EqForces a c p := by
  induction a generalizing b c p with
  | mk ι a s ih =>
    cases b with
    | mk κ b t =>
      cases c with
      | mk μ c v =>
        constructor
        · intro i q hq hs
          obtain ⟨r,hr,j,hj,he⟩ := hab.1 i q hq hs
          obtain ⟨w,hw,k,hk,hf⟩ := hbc.1 j r (hr.trans hq) hj
          exact ⟨w,hw.trans hr,k,hk,ih i (b j) (c k) w (eq_mono _ _ hw he) hf⟩
        · intro k q hq hv
          obtain ⟨r,hr,j,hj,he⟩ := hbc.2 k q hq hv
          obtain ⟨w,hw,i,hi,hf⟩ := hab.2 j r (hr.trans hq) hj
          exact ⟨w,hw.trans hr,i,hi,ih i (b j) (c k) w hf (eq_mono _ _ hw he)⟩

theorem eq_of_dense (a b : Name P) (p : P)
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ EqForces a b r) : EqForces a b p := by
  cases a with
  | mk ι a s =>
    cases b with
    | mk κ b t =>
      constructor
      · intro i q hq hs
        obtain ⟨r,hr,he⟩ := h q hq
        obtain ⟨w,hw,j,hj,hf⟩ := he.1 i r le_rfl (hr.trans hs)
        exact ⟨w,hw.trans hr,j,hj,hf⟩
      · intro j q hq ht
        obtain ⟨r,hr,he⟩ := h q hq
        obtain ⟨w,hw,i,hi,hf⟩ := he.2 j r le_rfl (hr.trans ht)
        exact ⟨w,hw.trans hr,i,hi,hf⟩

theorem mem_of_dense (a b : Name P) (p : P)
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ MemForces a b r) : MemForces a b p := by
  cases b with
  | mk κ b t =>
    intro q hq
    obtain ⟨r,hr,he⟩ := h q hq
    obtain ⟨w,hw,j,hj,hf⟩ := he r le_rfl
    exact ⟨w,hw.trans hr,j,hj,hf⟩

end TuringRigidity.AtomicForcing

end OAI
