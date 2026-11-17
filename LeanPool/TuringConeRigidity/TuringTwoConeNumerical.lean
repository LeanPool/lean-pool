/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeNumerical.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePersistentExtension
public import LeanPool.TuringConeRigidity.Computability.ArithmeticActions

/-!
# Numerical graphs between two cones

A graph is a predicate on pairs of natural-number indices in a column
presentation. Its totality is restricted to the source cone; its range is
exactly the target cone. All graph pairs must belong to both indicated cones.
Order reflection and output saturation handle repeated degree representatives.
These numerical clauses reconstruct an actual order isomorphism.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeNumerical

open EncodedForcing PersistentRestrictions
open ConePersistence (Cone)
open ConePresentation (Presented)
open TwoConePresentation (RawGraph)

noncomputable section
attribute [local instance] Classical.propDecidable

structure Action (B C H : Oracle) (P : ℕ → Prop) : Prop where
  total : ∀ n, degree B ≤ degree (columns H n) → ∃ m, P (Nat.pair n m)
  above : ∀ n m, P (Nat.pair n m) →
    degree B ≤ degree (columns H n) ∧ degree C ≤ degree (columns H m)
  onto : ∀ m, degree C ≤ degree (columns H m) → ∃ n, P (Nat.pair n m)
  order : ∀ n m n' m', P (Nat.pair n m) → P (Nat.pair n' m') →
    (degree (columns H n) ≤ degree (columns H n') ↔
      degree (columns H m) ≤ degree (columns H m'))
  saturated : ∀ n m m', P (Nat.pair n m) →
    degree (columns H m) = degree (columns H m') → P (Nat.pair n m')

theorem action_congr {B C H : Oracle} {P Q : ℕ → Prop} (h : ∀ v, P v ↔ Q v) :
    Action B C H P ↔ Action B C H Q := by
  have he : P = Q := funext (fun v => propext (h v))
  rw [he]

def entry {I : CountableIdeal} {H : Oracle} (hpres : Presented I H)
    {a : Degree} (n : ℕ) (hn : a ≤ degree (columns H n)) : Cone I a :=
  ⟨degree (columns H n), (hpres _).mpr ⟨n, rfl⟩, hn⟩

theorem action_of_iso {I : CountableIdeal} {B C H : Oracle}
    (hpres : Presented I H) (ρ : Cone I (degree B) ≃o Cone I (degree C)) :
    Action B C H (RawGraph ρ H) := by
  constructor
  · intro n hn
    let x := entry hpres n hn
    obtain ⟨m, hm⟩ := (hpres (ρ x).val).mp (ρ x).property.1
    refine ⟨m, ?_⟩
    simp only [RawGraph, Nat.unpair_pair]
    exact ⟨x, rfl, hm.symm⟩
  · intro n m hp
    simp only [RawGraph, Nat.unpair_pair] at hp
    obtain ⟨x, hx, hy⟩ := hp
    exact ⟨hx ▸ x.property.2, hy ▸ (ρ x).property.2⟩
  · intro m hm
    let y := entry hpres m hm
    obtain ⟨n, hn⟩ := (hpres (ρ.symm y).val).mp (ρ.symm y).property.1
    refine ⟨n, ?_⟩
    simp only [RawGraph, Nat.unpair_pair]
    exact ⟨ρ.symm y, hn.symm, congrArg Subtype.val (ρ.apply_symm_apply y)⟩
  · intro n m n' m' hp hq
    simp only [RawGraph, Nat.unpair_pair] at hp hq
    obtain ⟨x, hx, hy⟩ := hp
    obtain ⟨x', hx', hy'⟩ := hq
    rw [← hx, ← hx', ← hy, ← hy']
    exact ρ.le_iff_le.symm
  · intro n m m' hp he
    simp only [RawGraph, Nat.unpair_pair] at hp ⊢
    obtain ⟨x, hx, hy⟩ := hp
    exact ⟨x, hx, hy.trans he⟩

/-- Decode the graph clauses, rather than assuming the coded map exists. -/
theorem reconstruct {I : CountableIdeal} {B C H : Oracle} (hpres : Presented I H)
    {P : ℕ → Prop} (ha : Action B C H P) :
    ∃ ρ : Cone I (degree B) ≃o Cone I (degree C),
      ∀ v, P v ↔ RawGraph ρ H v := by
  classical
  let idx (x : Cone I (degree B)) : ℕ := Classical.choose ((hpres x.val).mp x.property.1)
  have hidx (x : Cone I (degree B)) : degree (columns H (idx x)) = x.val :=
    Classical.choose_spec ((hpres x.val).mp x.property.1)
  have habove (x : Cone I (degree B)) : degree B ≤ degree (columns H (idx x)) :=
    (hidx x).symm ▸ x.property.2
  let out (x : Cone I (degree B)) : ℕ := Classical.choose (ha.total (idx x) (habove x))
  have hout (x : Cone I (degree B)) : P (Nat.pair (idx x) (out x)) :=
    Classical.choose_spec (ha.total (idx x) (habove x))
  let f (x : Cone I (degree B)) : Cone I (degree C) :=
    entry hpres (out x) (ha.above _ _ (hout x)).2
  have hf (x : Cone I (degree B)) (n m : ℕ) (hn : degree (columns H n) = x.val)
      (hp : P (Nat.pair n m)) : (f x).val = degree (columns H m) := by
    apply le_antisymm
    · exact (ha.order _ _ _ _ (hout x) hp).mp (by rw [hidx, hn])
    · exact (ha.order _ _ _ _ hp (hout x)).mp (by rw [hidx, hn])
  have hle (x y : Cone I (degree B)) : f x ≤ f y ↔ x ≤ y := by
    have hh := (ha.order _ _ _ _ (hout x) (hout y)).symm
    change degree (columns H (out x)) ≤ degree (columns H (out y)) ↔ x.val ≤ y.val
    simpa only [hidx] using hh
  have hinj : Function.Injective f := by
    intro x y he
    exact le_antisymm ((hle x y).mp (le_of_eq he)) ((hle y x).mp (le_of_eq he.symm))
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨m, hm⟩ := (hpres y.val).mp y.property.1
    obtain ⟨n, hn⟩ := ha.onto m (hm.symm ▸ y.property.2)
    let x := entry hpres n (ha.above n m hn).1
    exact ⟨x, Subtype.ext ((hf x n m rfl hn).trans hm)⟩
  let ρ : Cone I (degree B) ≃o Cone I (degree C) :=
    { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
      map_rel_iff' := by intro x y; exact hle x y }
  refine ⟨ρ, fun v => ?_⟩
  obtain ⟨⟨n, m⟩, rfl⟩ := Nat.pairEquiv.surjective v
  change P (Nat.pair n m) ↔ RawGraph ρ H (Nat.pair n m)
  simp only [RawGraph, Nat.unpair_pair]
  constructor
  · intro hp
    let x := entry hpres n (ha.above n m hp).1
    exact ⟨x, rfl, hf x n m rfl hp⟩
  · rintro ⟨x, hx, hy⟩
    obtain ⟨t, ht⟩ := ha.total n (hx ▸ x.property.2)
    have hxt := hf x n t hx.symm ht
    exact ha.saturated n t m ht (hxt.symm.trans hy)

/-- Numerical compatibility of conventional graphs is precisely extension. -/
theorem compatible_iff {I J : CountableIdeal} {a b : Degree} {A H : Oracle}
    (hA : Presented I A) (hH : Presented J H) (hIJ : I.carrier ⊆ J.carrier)
    (ρ : Cone I a ≃o Cone I b) (σ : Cone J a ≃o Cone J b) :
    NumericalExtension.Compatible A H (RawGraph ρ A) (RawGraph σ H) ↔
      TwoConePersistence.Extends hIJ ρ σ := by
  constructor
  · intro hc x
    let xJ : Cone J a := ⟨x.val, hIJ x.property.1, x.property.2⟩
    obtain ⟨i, hi⟩ := (hA x.val).mp x.property.1
    obtain ⟨j, hj⟩ := (hA (ρ x).val).mp (ρ x).property.1
    obtain ⟨n, hn⟩ := (hH x.val).mp (hIJ x.property.1)
    obtain ⟨m, hm⟩ := (hH (σ xJ).val).mp (σ xJ).property.1
    have hR : RawGraph ρ A (Nat.pair i j) := by
      simp only [RawGraph, Nat.unpair_pair]
      exact ⟨x, hi.symm, hj.symm⟩
    have hP : RawGraph σ H (Nat.pair n m) := by
      simp only [RawGraph, Nat.unpair_pair]
      exact ⟨xJ, hn.symm, hm.symm⟩
    exact hm.symm.trans ((hc i j n m hR hP (hi.trans hn.symm)).symm.trans hj)
  · intro he i j n m hR hP hin
    simp only [RawGraph, Nat.unpair_pair] at hR hP
    obtain ⟨x, hx, hy⟩ := hR
    obtain ⟨y, hx', hy'⟩ := hP
    have hi : (⟨x.val, hIJ x.property.1, x.property.2⟩ : Cone J a) = y :=
      Subtype.ext (hx.trans (hin.trans hx'.symm))
    have hh := he x
    rw [hi] at hh
    exact hy.symm.trans (hh.symm.trans hy')

def graphOracle {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (H : Oracle) : Oracle := fun n => decide (RawGraph ρ H n)

@[simp] theorem graphOracle_true {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (H : Oracle) (n : ℕ) :
    graphOracle ρ H n = true ↔ RawGraph ρ H n := by simp [graphOracle]

theorem graphOracle_reduces {I : CountableIdeal} {a b : Degree} {H Y : Oracle}
    (ρ : Cone I a ≃o Cone I b) (hr : ArithmeticHierarchy.RecursivePred Y (RawGraph ρ H)) :
    Reduces (graphOracle ρ H) Y := by
  apply RecursiveIn.iff_nat.mpr
  exact hr.of_eq (fun n => by simp [oracleFunction, graphOracle])

end
end OAI.TuringRigidity.TwoConeNumerical
