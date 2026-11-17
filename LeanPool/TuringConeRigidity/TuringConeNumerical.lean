/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeNumerical.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConePersistentExtension
public import LeanPool.TuringConeRigidity.Computability.ArithmeticActions

/-!
# Numerical graphs of partial cone isomorphisms

The target enumeration is a subcollection of the source enumeration. An action
must have outputs above the base, and is onto exactly those columns above the
base. Saturation handles repeated degrees. These numerical conditions are
proved equivalent to an actual order isomorphism; no existence is built into
the definition of a numerical action.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeNumerical

open EncodedForcing PersistentRestrictions ConePersistence ConePresentation

noncomputable section

structure Action (B H : Oracle) (P : ℕ → Prop) : Prop where
  total : ∀ n, ∃ m, P (Nat.pair n m)
  above : ∀ n m, P (Nat.pair n m) → degree B ≤ degree (columns H m)
  onto : ∀ m, degree B ≤ degree (columns H m) → ∃ n, P (Nat.pair n m)
  order : ∀ n m n' m', P (Nat.pair n m) → P (Nat.pair n' m') →
    (degree (columns H n) ≤ degree (columns H n') ↔
      degree (columns H m) ≤ degree (columns H m'))
  saturated : ∀ n m m', P (Nat.pair n m) →
    degree (columns H m) = degree (columns H m') → P (Nat.pair n m')

theorem action_congr {B H : Oracle} {P Q : ℕ → Prop} (h : ∀ v, P v ↔ Q v) :
    Action B H P ↔ Action B H Q := by
  have he : P = Q := funext (fun v => propext (h v))
  rw [he]

theorem action_of_iso {I : CountableIdeal} {B H : Oracle}
    (hpres : Presented I H) (ρ : I ≃o Cone I (degree B)) :
    Action B H (ConePresentation.Graph ρ hpres) := by
  constructor
  · intro n
    obtain ⟨m, hm⟩ := (hpres (ρ (presentationEntry hpres n)).val).mp
      (ρ (presentationEntry hpres n)).property.1
    exact ⟨m, by simpa only [ConePresentation.Graph, Nat.unpair_pair] using hm.symm⟩
  · intro n m hp
    simp only [ConePresentation.Graph, Nat.unpair_pair] at hp
    rw [← hp]
    exact (ρ (presentationEntry hpres n)).property.2
  · intro m hm
    let y : Cone I (degree B) :=
      ⟨degree (columns H m), (presentationEntry hpres m).property, hm⟩
    obtain ⟨n, hn⟩ := (hpres (ρ.symm y).val).mp (ρ.symm y).property
    have he : presentationEntry hpres n = ρ.symm y := Subtype.ext hn
    refine ⟨n, ?_⟩
    simp only [ConePresentation.Graph, Nat.unpair_pair]
    rw [he, ρ.apply_symm_apply]
  · intro n m n' m' hp hq
    simp only [ConePresentation.Graph, Nat.unpair_pair] at hp hq
    rw [← hp, ← hq]
    change presentationEntry hpres n ≤ presentationEntry hpres n' ↔
      ρ (presentationEntry hpres n) ≤ ρ (presentationEntry hpres n')
    exact ρ.le_iff_le.symm
  · intro n m m' hp he
    simpa only [ConePresentation.Graph, Nat.unpair_pair, ← he] using hp

/-- Reconstruct the isomorphism from natural-number conditions on its graph. -/
theorem reconstruct {I : CountableIdeal} {B H : Oracle} (hpres : Presented I H)
    {P : ℕ → Prop} (ha : Action B H P) :
    ∃ ρ : I ≃o Cone I (degree B), ∀ v, P v ↔ ConePresentation.Graph ρ hpres v := by
  classical
  let idx (x : I) : ℕ := Classical.choose ((hpres x.val).mp x.property)
  have hidx (x : I) : degree (columns H (idx x)) = x.val :=
    Classical.choose_spec ((hpres x.val).mp x.property)
  let out (n : ℕ) : ℕ := Classical.choose (ha.total n)
  have hout (n : ℕ) : P (Nat.pair n (out n)) := Classical.choose_spec (ha.total n)
  let f (x : I) : Cone I (degree B) :=
    ⟨degree (columns H (out (idx x))), (presentationEntry hpres _).property,
      ha.above _ _ (hout (idx x))⟩
  have hf (x : I) (n m : ℕ) (hn : degree (columns H n) = x.val)
      (hp : P (Nat.pair n m)) : (f x).val = degree (columns H m) := by
    apply le_antisymm
    · exact (ha.order _ _ _ _ (hout (idx x)) hp).mp (by rw [hidx, hn])
    · exact (ha.order _ _ _ _ hp (hout (idx x))).mp (by rw [hidx, hn])
  have hle (x y : I) : f x ≤ f y ↔ x ≤ y := by
    have hh := (ha.order _ _ _ _ (hout (idx x)) (hout (idx y))).symm
    change degree (columns H (out (idx x))) ≤ degree (columns H (out (idx y))) ↔ x.val ≤ y.val
    simpa only [hidx] using hh
  have hinj : Function.Injective f := by
    intro x y he
    exact le_antisymm ((hle x y).mp (le_of_eq he)) ((hle y x).mp (le_of_eq he.symm))
  have hsurj : Function.Surjective f := by
    intro y
    let yI : I := ⟨y.val, y.property.1⟩
    obtain ⟨n, hn⟩ := ha.onto (idx yI) (by rw [hidx]; exact y.property.2)
    refine ⟨presentationEntry hpres n, Subtype.ext ?_⟩
    exact (hf (presentationEntry hpres n) n (idx yI) rfl hn).trans (hidx yI)
  let ρ : I ≃o Cone I (degree B) :=
    { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
      map_rel_iff' := by intro x y; exact hle x y }
  refine ⟨ρ, fun v => ?_⟩
  obtain ⟨⟨n, m⟩, rfl⟩ := Nat.pairEquiv.surjective v
  change P (Nat.pair n m) ↔ ConePresentation.Graph ρ hpres (Nat.pair n m)
  simp only [ConePresentation.Graph, Nat.unpair_pair]
  constructor
  · exact fun hp => hf (presentationEntry hpres n) n m rfl hp
  · intro hg
    change (f (presentationEntry hpres n)).val = degree (columns H m) at hg
    have hnm := hf (presentationEntry hpres n) n (out n) rfl (hout n)
    exact ha.saturated n (out n) m (hout n) (hnm.symm.trans hg)

/-- The existing numerical compatibility predicate also works for cone maps. -/
theorem compatible_iff {I J : CountableIdeal} {a : Degree} {A H : Oracle}
    (hA : Presented I A) (hH : Presented J H) (hIJ : I.carrier ⊆ J.carrier)
    (ρ : I ≃o Cone I a) (σ : J ≃o Cone J a) :
    NumericalExtension.Compatible A H (ConePresentation.Graph ρ hA) (ConePresentation.Graph σ hH) ↔
      ConePersistence.Extends hIJ ρ σ := by
  constructor
  · intro hc x
    obtain ⟨i, hi⟩ := (hA x.val).mp x.property
    obtain ⟨j, hj⟩ := (hA (ρ x).val).mp (ρ x).property.1
    obtain ⟨n, hn⟩ := (hH x.val).mp (hIJ x.property)
    obtain ⟨m, hm⟩ := (hH (σ ⟨x.val, hIJ x.property⟩).val).mp
      (σ ⟨x.val, hIJ x.property⟩).property.1
    have heI : presentationEntry hA i = x := Subtype.ext hi
    have heJ : presentationEntry hH n = ⟨x.val, hIJ x.property⟩ := Subtype.ext hn
    have hR : ConePresentation.Graph ρ hA (Nat.pair i j) := by
      simp only [ConePresentation.Graph, Nat.unpair_pair]
      rw [heI, hj]
    have hP : ConePresentation.Graph σ hH (Nat.pair n m) := by
      simp only [ConePresentation.Graph, Nat.unpair_pair]
      rw [heJ, hm]
    exact hm.symm.trans ((hc i j n m hR hP (hi.trans hn.symm)).symm.trans hj)
  · intro he i j n m hR hP hin
    have hi : (⟨(presentationEntry hA i).val, hIJ (presentationEntry hA i).property⟩ : J) =
        presentationEntry hH n := Subtype.ext hin
    have hh := he (presentationEntry hA i)
    rw [hi] at hh
    simp only [ConePresentation.Graph, Nat.unpair_pair] at hR hP
    exact hR.symm.trans (hh.symm.trans hP)

end
end OAI.TuringRigidity.ConeNumerical
