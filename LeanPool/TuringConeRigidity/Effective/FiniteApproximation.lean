/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteApproximation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.OracleCode

/-!
# Finite Approximation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

def Approximates {α : Type*} (p : Part α) (ps : ℕ → Part α) : Prop :=
  (∀ m a, a ∈ ps m → a ∈ p) ∧
  (∀ a, a ∈ p → ∃ M, ∀ m, M ≤ m → a ∈ ps m)

namespace Approximates
variable {α β : Type*}

theorem const (p : Part α) : Approximates p (fun _ => p) :=
  ⟨fun _ _ h => h, fun _ h => ⟨0,fun _ _ => h⟩⟩

theorem bind {p : Part α} {ps : ℕ → Part α} {f : α → Part β}
    {fs : ℕ → α → Part β} (hp : Approximates p ps)
    (hf : ∀ a, Approximates (f a) (fun m => fs m a)) :
    Approximates (p.bind f) (fun m => (ps m).bind (fs m)) := by
  constructor
  · intro m b hb
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hb
    exact Part.mem_bind_iff.mpr ⟨a,hp.1 m a ha,(hf a).1 m b hb⟩
  · intro b hb
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hb
    obtain ⟨M,hM⟩ := hp.2 a ha
    obtain ⟨N,hN⟩ := (hf a).2 b hb
    exact ⟨max M N,fun m hm => Part.mem_bind_iff.mpr
      ⟨a,hM m ((le_max_left _ _).trans hm),hN m ((le_max_right _ _).trans hm)⟩⟩

theorem map {p : Part α} {ps : ℕ → Part α} (hp : Approximates p ps) (f : α → β) :
    Approximates (p.map f) (fun m => (ps m).map f) := by
  simpa only [Part.bind_some_eq_map] using hp.bind (fun a => const (Part.some (f a)))

theorem finite_bounds (P : ℕ → ℕ → Prop) (n : ℕ)
    (h : ∀ i, i < n → ∃ M, ∀ m, M ≤ m → P i m) :
    ∃ M, ∀ m, M ≤ m → ∀ i, i < n → P i m := by
  induction n with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    obtain ⟨M,hM⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨N,hN⟩ := h n (Nat.lt_succ_self n)
    refine ⟨max M N, fun m hm i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hM m ((le_max_left _ _).trans hm) i hi
    · exact hN m ((le_max_right _ _).trans hm)

theorem rfind {p : ℕ → Part Bool} {ps : ℕ → ℕ → Part Bool}
    (hp : ∀ n, Approximates (p n) (fun m => ps m n)) :
    Approximates (Nat.rfind p) (fun m => Nat.rfind (ps m)) := by
  constructor
  · intro m n hn
    obtain ⟨ht,hf⟩ := Nat.mem_rfind.mp hn
    exact Nat.mem_rfind.mpr ⟨(hp n).1 m true ht,fun {k} hk => (hp k).1 m false (hf hk)⟩
  · intro n hn
    obtain ⟨ht,hf⟩ := Nat.mem_rfind.mp hn
    obtain ⟨M,hM⟩ := (hp n).2 true ht
    obtain ⟨N,hN⟩ := finite_bounds (fun k m => false ∈ ps m k) n
      (fun k hk => (hp k).2 false (hf hk))
    exact ⟨max M N, fun m hm => Nat.mem_rfind.mpr
      ⟨hM m ((le_max_left _ _).trans hm),fun {k} hk => hN m ((le_max_right _ _).trans hm) k hk⟩⟩
end Approximates

namespace OracleCode

theorem eval_approximates {g : ℕ →. ℕ} {gs : ℕ → ℕ →. ℕ}
    (hg : ∀ n, Approximates (g n) (fun m => gs m n)) (c : OracleCode) :
    ∀ n, Approximates (eval g c n) (fun m => eval (gs m) c n) := by
  induction c with
  | zero => intro n; exact Approximates.const _
  | succ => intro n; exact Approximates.const _
  | left => intro n; exact Approximates.const _
  | right => intro n; exact Approximates.const _
  | query => exact hg
  | pair c d hc hd =>
    intro n
    exact (hc n).bind (fun a => (hd n).map (Nat.pair a))
  | comp c d hc hd => intro n; exact (hd n).bind hc
  | prec c d hc hd =>
    intro p
    have hr : ∀ k, Approximates
        (Nat.rec (eval g c (Nat.unpair p).1)
          (fun y ih => ih.bind (fun i => eval g d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k)
        (fun m => Nat.rec (eval (gs m) c (Nat.unpair p).1)
          (fun y ih => ih.bind (fun i => eval (gs m) d (Nat.pair (Nat.unpair p).1 (Nat.pair y
            i)))) k) := by
      intro k
      induction k with
      | zero => exact hc _
      | succ k ih => exact ih.bind (fun i => hd _)
    exact hr _
  | find c hc =>
    intro n
    exact Approximates.rfind (fun k => (hc (Nat.pair n k)).map (fun m => decide (m=0)))

end OracleCode
end TuringRigidity

end OAI
