/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericalAutomorphism.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentExtension

/-!
# Numerical Automorphism
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericalAutomorphism
open EncodedForcing PersistentRestrictions PersistentPresentation
noncomputable section

structure Action (H : Oracle) (P : ℕ → Prop) : Prop where
  total : ∀ n, ∃ m, P (Nat.pair n m)
  onto : ∀ m, ∃ n, P (Nat.pair n m)
  order : ∀ n m n' m', P (Nat.pair n m) → P (Nat.pair n' m') →
    (degree (columns H n) ≤ degree (columns H n') ↔
      degree (columns H m) ≤ degree (columns H m'))
  saturated : ∀ n m m', P (Nat.pair n m) →
    degree (columns H m) = degree (columns H m') → P (Nat.pair n m')

theorem action_of_automorphism {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) (ρ : I ≃o I) : Action H (Graph ρ hpres) := by
  constructor
  · intro n
    obtain ⟨m,hm⟩ := (hpres (ρ (entry hpres n)).val).mp (ρ (entry hpres n)).property
    exact ⟨m,by simpa only [PersistentPresentation.Graph,Nat.unpair_pair] using hm.symm⟩
  · intro m
    obtain ⟨n,hn⟩ := (hpres (ρ.symm (entry hpres m)).val).mp (ρ.symm (entry hpres m)).property
    have he : entry hpres n = ρ.symm (entry hpres m) := Subtype.ext hn
    refine ⟨n,?_⟩
    simp only [PersistentPresentation.Graph,Nat.unpair_pair]
    rw [he,ρ.apply_symm_apply]
    rfl
  · intro n m n' m' hp hq
    simp only [PersistentPresentation.Graph,Nat.unpair_pair] at hp hq
    rw [← hp,← hq]
    change entry hpres n ≤ entry hpres n' ↔ ρ (entry hpres n) ≤ ρ (entry hpres n')
    exact ρ.le_iff_le.symm
  · intro n m m' hp he
    simpa only [PersistentPresentation.Graph,Nat.unpair_pair,← he] using hp

theorem reconstruct {I : CountableIdeal} {H : Oracle} (hpres : Presented I H)
    {P : ℕ → Prop} (ha : Action H P) :
    ∃ ρ : I ≃o I, ∀ v, P v ↔ Graph ρ hpres v := by
  classical
  let idx (x : I) : ℕ := Classical.choose ((hpres x.val).mp x.property)
  have hidx (x : I) : degree (columns H (idx x)) = x.val :=
    Classical.choose_spec ((hpres x.val).mp x.property)
  let out (n : ℕ) : ℕ := Classical.choose (ha.total n)
  have hout (n : ℕ) : P (Nat.pair n (out n)) := Classical.choose_spec (ha.total n)
  let f (x : I) : I := entry hpres (out (idx x))
  have hf (x : I) (n m : ℕ) (hn : degree (columns H n) = x.val)
      (hp : P (Nat.pair n m)) : (f x).val = degree (columns H m) := by
    apply le_antisymm
    · exact (ha.order _ _ _ _ (hout (idx x)) hp).mp (by rw [hidx,hn])
    · exact (ha.order _ _ _ _ hp (hout (idx x))).mp (by rw [hidx,hn])
  have hle (x y : I) : f x ≤ f y ↔ x ≤ y := by
    have hh := (ha.order _ _ _ _ (hout (idx x)) (hout (idx y))).symm
    change degree (columns H (out (idx x))) ≤ degree (columns H (out (idx y))) ↔ x.val ≤ y.val
    simpa only [hidx] using hh
  have hinj : Function.Injective f := by
    intro x y he
    exact le_antisymm ((hle x y).mp (le_of_eq he)) ((hle y x).mp (le_of_eq he.symm))
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨n,hn⟩ := ha.onto (idx y)
    refine ⟨entry hpres n,Subtype.ext ?_⟩
    exact (hf (entry hpres n) n (idx y) rfl hn).trans (hidx y)
  let ρ : I ≃o I :=
    { toEquiv := Equiv.ofBijective f ⟨hinj,hsurj⟩
      map_rel_iff' := by intro x y; exact hle x y }
  refine ⟨ρ,fun v => ?_⟩
  obtain ⟨⟨n,m⟩,rfl⟩ := Nat.pairEquiv.surjective v
  change P (Nat.pair n m) ↔ Graph ρ hpres (Nat.pair n m)
  simp only [PersistentPresentation.Graph,Nat.unpair_pair]
  constructor
  · intro hp
    exact hf (entry hpres n) n m rfl hp
  · intro hg
    change (f (entry hpres n)).val = degree (columns H m) at hg
    have hnm := hf (entry hpres n) n (out n) rfl (hout n)
    exact ha.saturated n (out n) m (hout n) (hnm.symm.trans hg)

end
end TuringRigidity.NumericalAutomorphism

end OAI
