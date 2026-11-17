/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CountableForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Data.Nat.Pairing


/-!
# Countable Forcing
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CountableForcing
open Set

/-- A nonempty upward-closed family of conditions directed toward common extensions. -/
structure GenericFilter (P : Type*) [Preorder P] where
  /-- The set of conditions belonging to the filter. -/
  carrier : Set P
  nonempty : carrier.Nonempty
  upper : ∀ {p q}, p ≤ q → p ∈ carrier → q ∈ carrier
  directed : ∀ {p q}, p ∈ carrier → q ∈ carrier → ∃ r ∈ carrier, r ≤ p ∧ r ≤ q

/-- Every condition has a stronger condition belonging to `D`. -/
def Dense {P : Type*} [Preorder P] (D : Set P) : Prop := ∀ p, ∃ q, q ≤ p ∧ q ∈ D

/-- The filter meets each member of the countable family of requirements `D`. -/
def GenericFor {P : Type*} [Preorder P] (D : ℕ → Set P) (G : GenericFilter P) : Prop :=
  ∀ n, ∃ p ∈ G.carrier, p ∈ D n

theorem exists_generic {P : Type*} [Preorder P] (D : ℕ → Set P)
    (hD : ∀ n, Dense (D n)) (p : P) :
    ∃ G : GenericFilter P, p ∈ G.carrier ∧ GenericFor D G := by
  classical
  choose step hs using hD
  let seq : ℕ → P := fun n => Nat.rec p (fun n q => step n q) n
  have hseq (n : ℕ) : seq (n+1) ≤ seq n ∧ seq (n+1) ∈ D n := hs n (seq n)
  have hanti : Antitone seq := antitone_nat_of_succ_le (fun n => (hseq n).1)
  let G : GenericFilter P := {
    carrier := {q | ∃ n, seq n ≤ q}
    nonempty := ⟨p,0,le_rfl⟩
    upper := fun hpq ⟨n,hn⟩ => ⟨n,hn.trans hpq⟩
    directed := by
      rintro q r ⟨n,hn⟩ ⟨m,hm⟩
      exact ⟨seq (max n m),⟨max n m,le_rfl⟩,
        (hanti (le_max_left _ _)).trans hn,(hanti (le_max_right _ _)).trans hm⟩ }
  exact ⟨G,⟨0,le_rfl⟩,fun n => ⟨seq (n+1),⟨n+1,le_rfl⟩,(hseq n).2⟩⟩

/-- Forcing sentences built from ground propositions, filter membership, conjunction,
countable existential quantification, and negation. -/
inductive Sentence (P : Type*) where
  | ground : Prop → Sentence P
  | member : P → Sentence P
  | conj : Sentence P → Sentence P → Sentence P
  | existsNat : (ℕ → Sentence P) → Sentence P
  | neg : Sentence P → Sentence P

namespace Sentence
variable {P : Type*} [Preorder P]

/-- Interpret a forcing sentence in a filter. -/
def Truth (G : GenericFilter P) : Sentence P → Prop
  | .ground a => a
  | .member p => p ∈ G.carrier
  | .conj a b => Truth G a ∧ Truth G b
  | .existsNat a => ∃ n, Truth G (a n)
  | .neg a => ¬ Truth G a

/-- Recursive forcing semantics for countable forcing sentences. -/
def Forces (p : P) : Sentence P → Prop
  | .ground a => a
  | .member q => p ≤ q
  | .conj a b => Forces p a ∧ Forces p b
  | .existsNat a => ∃ n, Forces p (a n)
  | .neg a => ∀ q, q ≤ p → ¬ Forces q a

theorem forces_mono (a : Sentence P) {p q : P} (hqp : q ≤ p)
    (h : Forces p a) : Forces q a := by
  induction a with
  | ground a => exact h
  | member r => exact hqp.trans h
  | conj a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | existsNat a ha => obtain ⟨n,hn⟩ := h; exact ⟨n,ha n hn⟩
  | neg a ha => exact fun r hr => h r (hr.trans hqp)

/-- Conditions forcing the sentence or its negation. -/
def Decision (a : Sentence P) : Set P := {p | Forces p a ∨ Forces p (.neg a)}

theorem decision_dense (a : Sentence P) : Dense (Decision a) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ Forces q a
  · obtain ⟨q,hqp,hq⟩ := h
    exact ⟨q,hqp,Or.inl hq⟩
  · exact ⟨p,le_rfl,Or.inr (fun q hq hf => h ⟨q,hq,hf⟩)⟩

/-- A countable family of decision requirements sufficient for the sentence's truth lemma. -/
def Requirements : Sentence P → ℕ → Set P
  | .ground _, _ => univ
  | .member _, _ => univ
  | .conj a b, n => if n % 2 = 0 then Requirements a (n/2) else Requirements b (n/2)
  | .existsNat a, n => Requirements (a (Nat.unpair n).1) (Nat.unpair n).2
  | .neg a, n => if n = 0 then Decision a else Requirements a (n-1)

theorem requirements_dense (a : Sentence P) : ∀ n, Dense (Requirements a n) := by
  induction a with
  | ground _ => exact fun _ p => ⟨p,le_rfl,mem_univ p⟩
  | member _ => exact fun _ p => ⟨p,le_rfl,mem_univ p⟩
  | conj a b ha hb => intro n; dsimp [Requirements]; split <;> first | exact ha _ | exact hb _
  | existsNat a ha => exact fun n => ha _ _
  | neg a ha =>
      intro n
      dsimp [Requirements]
      split
      · exact decision_dense a
      · exact ha _

theorem requirements_mono (a : Sentence P) (n : ℕ) {p q : P}
    (hqp : q ≤ p) (hp : p ∈ Requirements a n) : q ∈ Requirements a n := by
  induction a generalizing n with
  | ground _ => exact mem_univ q
  | member _ => exact mem_univ q
  | conj a b ha hb =>
    dsimp only [Requirements] at hp ⊢
    by_cases h : n % 2 = 0
    · simp only [ite_eq_left h] at hp ⊢
      exact ha _ hp
    · simp only [ite_eq_right h] at hp ⊢
      exact hb _ hp
  | existsNat a ha => exact ha _ _ hp
  | neg a ha =>
    dsimp only [Requirements] at hp ⊢
    by_cases h : n = 0
    · simp only [ite_eq_left h] at hp ⊢
      rcases hp with hp | hp
      · exact Or.inl (forces_mono a hqp hp)
      · exact Or.inr (forces_mono (.neg a) hqp hp)
    · simp only [ite_eq_right h] at hp ⊢
      exact ha _ hp

theorem generic_truth (a : Sentence P) (G : GenericFilter P)
    (hG : GenericFor (Requirements a) G) : Truth G a ↔ ∃ p ∈ G.carrier, Forces p a := by
  induction a with
  | ground a =>
    exact ⟨fun h => let ⟨p,hp⟩ := G.nonempty; ⟨p,hp,h⟩,fun ⟨_,_,h⟩ => h⟩
  | member p =>
    exact ⟨fun h => ⟨p,h,le_rfl⟩,fun ⟨q,hq,hqp⟩ => G.upper hqp hq⟩
  | conj a b ha hb =>
    have hA : GenericFor (Requirements a) G := by
      intro n; simpa [Requirements] using hG (2*n)
    have hB : GenericFor (Requirements b) G := by
      intro n; simpa [Requirements,Nat.add_div] using hG (2*n+1)
    constructor
    · rintro ⟨h₁,h₂⟩
      obtain ⟨p,hp,hpa⟩ := (ha hA).mp h₁
      obtain ⟨q,hq,hqb⟩ := (hb hB).mp h₂
      obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact ⟨r,hr,forces_mono a hrp hpa,forces_mono b hrq hqb⟩
    · rintro ⟨p,hp,hpa,hpb⟩
      exact ⟨(ha hA).mpr ⟨p,hp,hpa⟩,(hb hB).mpr ⟨p,hp,hpb⟩⟩
  | existsNat a ha =>
    have hn : ∀ n, GenericFor (Requirements (a n)) G := by
      intro n k; simpa [Requirements] using hG (Nat.pair n k)
    constructor
    · rintro ⟨n,h⟩
      obtain ⟨p,hp,hpa⟩ := (ha n (hn n)).mp h
      exact ⟨p,hp,n,hpa⟩
    · rintro ⟨p,hp,n,hpa⟩
      exact ⟨n,(ha n (hn n)).mpr ⟨p,hp,hpa⟩⟩
  | neg a ha =>
    have hA : GenericFor (Requirements a) G := by
      intro n; simpa [Requirements] using hG (n+1)
    constructor
    · intro hnot
      obtain ⟨p,hp,hpd⟩ := hG 0
      have hd : Forces p a ∨ Forces p (.neg a) := by simpa [Requirements,Decision] using hpd
      rcases hd with hpa | hpn
      · exact False.elim (hnot ((ha hA).mpr ⟨p,hp,hpa⟩))
      · exact ⟨p,hp,hpn⟩
    · rintro ⟨p,hp,hpn⟩ htrue
      obtain ⟨q,hq,hqa⟩ := (ha hA).mp htrue
      obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact hpn r hrp (forces_mono a hrq hqa)

/-- Double-negation forcing of the sentence. -/
def WeakForces (p : P) (a : Sentence P) : Prop := Forces p (.neg (.neg a))

theorem weak_iff_all_generic (p : P) (a : Sentence P) :
    WeakForces p a ↔ ∀ G : GenericFilter P,
      GenericFor (Requirements (.neg (.neg a))) G → p ∈ G.carrier → Truth G a := by
  classical
  constructor
  · intro hp G hG hpg
    have h := (generic_truth (.neg (.neg a)) G hG).mpr ⟨p,hpg,hp⟩
    exact Classical.not_not.mp h
  · intro h q hqp hq
    obtain ⟨G,hqG,hG⟩ := exists_generic (Requirements (.neg (.neg a)))
      (requirements_dense _) q
    have hsub : GenericFor (Requirements (.neg a)) G := by
      intro n
      simpa [Requirements] using hG (n+1)
    have hn := (generic_truth (.neg a) G hsub).mpr ⟨q,hqG,hq⟩
    exact hn (h G hG (G.upper hqp hqG))

end Sentence
end TuringRigidity.CountableForcing

end OAI
