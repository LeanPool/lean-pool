/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/ForcingSymmetry.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CountableForcing

/-!
# Forcing Symmetry
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CountableForcing
open Set
namespace Sentence
variable {P Q : Type*} [Preorder P] [Preorder Q]

def rename (e : P ≃o Q) : Sentence P → Sentence Q
  | .ground a => .ground a
  | .member p => .member (e p)
  | .conj a b => .conj (rename e a) (rename e b)
  | .existsNat a => .existsNat (fun n => rename e (a n))
  | .neg a => .neg (rename e a)

theorem forces_rename (e : P ≃o Q) (a : Sentence P) (p : P) :
    Forces (e p) (rename e a) ↔ Forces p a := by
  induction a generalizing p with
  | ground a => exact Iff.rfl
  | member q => exact e.le_iff_le
  | conj a b ha hb => exact and_congr (ha p) (hb p)
  | existsNat a ha => exact exists_congr (fun n => ha n p)
  | neg a ha =>
    constructor
    · intro h q hq hf
      exact h (e q) (e.monotone hq) ((ha q).mpr hf)
    · intro h q hq hf
      have hle : e.symm q ≤ p := by
        apply e.le_iff_le.mp
        simpa using hq
      exact h (e.symm q) hle ((ha (e.symm q)).mp (by simpa using hf))

theorem weak_rename (e : P ≃o Q) (a : Sentence P) (p : P) :
    WeakForces (e p) (rename e a) ↔ WeakForces p a :=
  forces_rename e (.neg (.neg a)) p

theorem weak_iff_dense_below (p : P) (a : Sentence P) :
    WeakForces p a ↔ ∀ q, q ≤ p → ∃ r, r ≤ q ∧ Forces r a := by
  classical
  constructor
  · intro h q hq
    by_contra hn
    exact h q hq (fun r hr hf => hn ⟨r,hr,hf⟩)
  · intro h q hq hn
    obtain ⟨r,hr,hf⟩ := h q hq
    exact hn r hr hf

theorem forces_weak {p : P} {a : Sentence P} (h : Forces p a) : WeakForces p a := by
  intro q hq hn
  exact hn q le_rfl (forces_mono a hq h)

theorem weak_incompatible {a : Sentence P} {p q r : P}
    (hp : WeakForces p a) (hq : WeakForces q (.neg a))
    (hrp : r ≤ p) (hrq : r ≤ q) : False := by
  obtain ⟨s,hs,hsa⟩ := (weak_iff_dense_below p a).mp hp r hrp
  obtain ⟨t,ht,htn⟩ := (weak_iff_dense_below q (.neg a)).mp hq s (hs.trans hrq)
  exact htn t le_rfl (forces_mono a ht hsa)

def liftFirst [OrderTop Q] : Sentence P → Sentence (P × Q)
  | .ground a => .ground a
  | .member p => .member (p,⊤)
  | .conj a b => .conj (liftFirst a) (liftFirst b)
  | .existsNat a => .existsNat (fun n => liftFirst (a n))
  | .neg a => .neg (liftFirst a)

theorem forces_liftFirst [OrderTop Q] (a : Sentence P) (p : P) (q : Q) :
    Forces (p,q) (liftFirst a) ↔ Forces p a := by
  induction a generalizing p q with
  | ground a => exact Iff.rfl
  | member r => exact ⟨fun h => h.1,fun h => ⟨h,le_top⟩⟩
  | conj a b ha hb => exact and_congr (ha p q) (hb p q)
  | existsNat a ha => exact exists_congr (fun n => ha n p q)
  | neg a ha =>
    constructor
    · intro h r hr hf
      exact h (r,q) ⟨hr,le_rfl⟩ ((ha r q).mpr hf)
    · intro h r hr hf
      exact h r.1 hr.1 ((ha r.1 r.2).mp hf)

theorem weak_liftFirst [OrderTop Q] (a : Sentence P) (p : P) (q : Q) :
    WeakForces (p,q) (liftFirst a) ↔ WeakForces p a :=
  forces_liftFirst (.neg (.neg a)) p q

theorem remove_tail_of_transport (a : Sentence (P × Q))
    (transport : ∀ (p : P) (q r : Q), Forces (p, q) a →
      ∃ s : Q, s ≤ r ∧ Forces (p, s) a)
    (p : P) (q : Q) (h : WeakForces (p, q) a) :
    ∀ r : Q, WeakForces (p,r) a := by
  intro r
  apply (weak_iff_dense_below _ a).mpr
  intro t ht
  obtain ⟨u,hu,hua⟩ := (weak_iff_dense_below _ a).mp h (t.1,q) ⟨ht.1,le_rfl⟩
  obtain ⟨s,hs,hsa⟩ := transport u.1 u.2 t.2 hua
  exact ⟨(u.1,s),⟨hu.1,hs⟩,hsa⟩

end Sentence
end TuringRigidity.CountableForcing

end OAI
