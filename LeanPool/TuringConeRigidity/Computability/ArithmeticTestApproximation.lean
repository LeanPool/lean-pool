/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticTestApproximation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticFiniteTest

/-!
# Arithmetic Test Approximation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Approx := ℕ → Option ℕ

def Extends (s t : Approx) : Prop := ∀ i a, s i = some a → t i = some a

def Captures (s : Approx) (f : ℕ → ℕ) (N : ℕ) : Prop := ∀ i < N, s i = some (f i)

theorem Captures.mono {s f N K} (h : Captures s f N) (hK : K ≤ N) : Captures s f K :=
  fun i hi => h i (lt_of_lt_of_le hi hK)

namespace Term

def approx (s : Approx) (v : ℕ) : Term → Option ℕ
  | .input => some v
  | .const n => some n
  | .prim g _ t => (t.approx s v).bind (fun a => some (g a))
  | .pair t u => (t.approx s v).bind (fun a => (u.approx s v).bind (fun b => some (Nat.pair a b)))
  | .witness t => (t.approx s v).bind s

theorem approx_mono (t : Term) {s u : Approx} (h : Extends s u) (v a : ℕ)
    (ha : t.approx s v = some a) : t.approx u v = some a := by
  induction t generalizing a with
  | input => exact ha
  | const n => exact ha
  | prim g hg t ih =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,ih b hb,he⟩
  | pair t w ih ik =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,c,hc,he⟩ := ha
    exact ⟨b,ih b hb,c,ik c hc,he⟩
  | witness t ih =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,ih b hb,h b a he⟩

@[simp] theorem approx_full (t : Term) (f : ℕ → ℕ) (v : ℕ) :
    t.approx (fun i => some (f i)) v = some (t.eval f v) := by
  induction t <;> simp_all [approx,eval]

theorem approx_sound (t : Term) {s : Approx} {f : ℕ → ℕ}
    (h : Extends s (fun i => some (f i))) (v a : ℕ) (ha : t.approx s v = some a) :
    t.eval f v = a := by
  simpa only [approx_full,Option.some.injEq] using t.approx_mono h v a ha

theorem approx_complete (t : Term) (f : ℕ → ℕ) (v : ℕ) :
    ∃ N, ∀ s : Approx, Captures s f N → t.approx s v = some (t.eval f v) := by
  induction t with
  | input => exact ⟨0,fun _ _ => rfl⟩
  | const n => exact ⟨0,fun _ _ => rfl⟩
  | prim g hg t ih =>
    obtain ⟨N,hN⟩ := ih
    exact ⟨N,fun s hs => by simp [approx,eval,hN s hs]⟩
  | pair t u ih ik =>
    obtain ⟨N,hN⟩ := ih
    obtain ⟨K,hK⟩ := ik
    exact ⟨max N K,fun s hs => by
      simp [approx,eval,hN s (hs.mono (le_max_left _ _)),hK s (hs.mono (le_max_right _ _))]⟩
  | witness t ih =>
    obtain ⟨N,hN⟩ := ih
    refine ⟨max N (t.eval f v + 1),fun s hs => ?_⟩
    simp only [approx,hN s (hs.mono (le_max_left _ _)),Option.bind_some,eval]
    exact hs _ (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
end Term

namespace Test

def approx (O : Oracles) (s : Approx) (v : ℕ) : Test → Option Bool
  | .pure P _ t => (t.approx s v).bind (fun a => some (decide (P a)))
  | .query i t => (t.approx s v).bind (fun a => some (O i a))
  | .neg t => (t.approx O s v).bind (fun a => some (!a))
  | .and t u => (t.approx O s v).bind (fun a => (u.approx O s v).bind (fun b => some (a && b)))

private theorem approx_mono (t : Test) (O : Oracles) {s u : Approx} (h : Extends s u)
    (v : ℕ) (a : Bool) (ha : t.approx O s v = some a) : t.approx O u v = some a := by
  induction t generalizing a with
  | pure P hP t =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,t.approx_mono h v b hb,he⟩
  | query i t =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,t.approx_mono h v b hb,he⟩
  | neg t ih =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,ih b hb,he⟩
  | and t w ih ik =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,c,hc,he⟩ := ha
    exact ⟨b,ih b hb,c,ik c hc,he⟩

@[simp] theorem approx_full (t : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    t.approx O (fun i => some (f i)) v = some (decide (t.eval O f v)) := by
  induction t with
  | pure P hP t =>
    by_cases h : P (t.eval f v) <;> simp [approx,eval,h]
  | query i t => cases h : O i (t.eval f v) <;> simp [approx,eval,h]
  | neg t ih => by_cases h : t.eval O f v <;> simp [approx,eval,ih,h]
  | and t w ih ik =>
    by_cases ht : t.eval O f v <;> by_cases hw : w.eval O f v <;> simp [approx,eval,ih,ik,ht,hw]

theorem approx_sound (t : Test) (O : Oracles) {s : Approx} {f : ℕ → ℕ}
    (h : Extends s (fun i => some (f i))) (v : ℕ) (a : Bool)
    (ha : t.approx O s v = some a) : t.eval O f v ↔ a = true := by
  have he : decide (t.eval O f v) = a := by
    simpa only [approx_full,Option.some.injEq] using t.approx_mono O h v a ha
  rw [← he]
  simp

theorem approx_complete (t : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    ∃ N, ∀ s : Approx, Captures s f N →
      t.approx O s v = some (decide (t.eval O f v)) := by
  induction t with
  | pure P hP t =>
    obtain ⟨N,hN⟩ := t.approx_complete f v
    refine ⟨N,fun s hs => ?_⟩
    rw [← approx_full]
    simp only [approx,hN s hs,Term.approx_full]
  | query i t =>
    obtain ⟨N,hN⟩ := t.approx_complete f v
    refine ⟨N,fun s hs => ?_⟩
    rw [← approx_full]
    simp only [approx,hN s hs,Term.approx_full]
  | neg t ih =>
    obtain ⟨N,hN⟩ := ih
    refine ⟨N,fun s hs => ?_⟩
    rw [← approx_full]
    simp only [approx,hN s hs,approx_full]
  | and t u ih ik =>
    obtain ⟨N,hN⟩ := ih
    obtain ⟨K,hK⟩ := ik
    refine ⟨max N K,fun s hs => ?_⟩
    rw [← approx_full]
    simp only [approx,hN s (hs.mono (le_max_left _ _)),hK s (hs.mono (le_max_right _
      _)),approx_full]

theorem rejection_mono (t : Test) (O : Oracles) {s u : Approx} (h : Extends s u)
    (v : ℕ) (ha : t.approx O s v = some false) : t.approx O u v = some false :=
  t.approx_mono O h v false ha
end Test

end
end TuringRigidity.ArithmeticTree

end OAI
