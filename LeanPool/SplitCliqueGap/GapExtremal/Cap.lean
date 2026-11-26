/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.Prod

/-!
# Caps and separable caps (ledger §2)

* `IsCap A`: no three distinct collinear points of `A` (an affine cap).
* `IsSep A`: every point outside `A` lies on an affine hyperplane `{λ = b}` disjoint from `A`.
* `IsCap.prod`, `IsSep.prod` (ledger L2.1 for two factors) and the `Pi` versions `IsCap.pi`,
`IsSep.pi`
  (the power `A^j`).
-/

@[expose] public section

namespace GapExtremal

variable {K : Type*} [Field K]

section Defs

variable {V : Type*} [AddCommGroup V] [Module K V]

variable (K) in
/-- `A` is a cap: for distinct `P, R ∈ A` and `t ∉ {0, 1}`, the point `P + t • (R - P)` is not in
`A`. -/
def IsCap (A : Set V) : Prop :=
  ∀ ⦃P⦄, P ∈ A → ∀ ⦃R⦄, R ∈ A → P ≠ R → ∀ t : K, t ≠ 0 → t ≠ 1 → P + t • (R - P) ∉ A

variable (K) in
/-- `A` is separable: every point outside `A` is on an affine hyperplane disjoint from `A`. -/
def IsSep (A : Set V) : Prop :=
  ∀ z ∉ A, ∃ (l : V →ₗ[K] K) (b : K), l z = b ∧ ∀ a ∈ A, l a ≠ b

end Defs

section Prod

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem IsCap.prod {A : Set V} {B : Set W} (hA : IsCap K A) (hB : IsCap K B) :
    IsCap K (A ×ˢ B) := by
  rintro ⟨p₁, p₂⟩ ⟨hp₁, hp₂⟩ ⟨r₁, r₂⟩ ⟨hr₁, hr₂⟩ hne t ht0 ht1 ⟨h₁, h₂⟩
  by_cases e₁ : p₁ = r₁
  · have e₂ : p₂ ≠ r₂ := fun e₂ => hne (by rw [e₁, e₂])
    exact hB hp₂ hr₂ e₂ t ht0 ht1 (by simpa using h₂)
  · exact hA hp₁ hr₁ e₁ t ht0 ht1 (by simpa using h₁)

theorem IsSep.prod {A : Set V} {B : Set W} (hA : IsSep K A) (hB : IsSep K B) :
    IsSep K (A ×ˢ B) := by
  rintro ⟨z₁, z₂⟩ hz
  simp only [Set.mem_prod, not_and_or] at hz
  rcases hz with hz | hz
  · obtain ⟨l, b, hl, hlA⟩ := hA z₁ hz
    refine ⟨l.comp (LinearMap.fst K V W), b, by simpa using hl, ?_⟩
    rintro ⟨a₁, a₂⟩ ⟨ha₁, -⟩
    simpa using hlA a₁ ha₁
  · obtain ⟨l, b, hl, hlB⟩ := hB z₂ hz
    refine ⟨l.comp (LinearMap.snd K V W), b, by simpa using hl, ?_⟩
    rintro ⟨a₁, a₂⟩ ⟨-, ha₂⟩
    simpa using hlB a₂ ha₂

end Prod

section Pi

variable {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V]

theorem IsCap.pi {A : Set V} (hA : IsCap K A) :
    IsCap K (Set.pi Set.univ (fun _ : ι => A)) := by
  intro P hP R hR hne t ht0 ht1 hS
  obtain ⟨i, hi⟩ : ∃ i, P i ≠ R i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact hA (hP i (Set.mem_univ i)) (hR i (Set.mem_univ i)) hi t ht0 ht1
    (by simpa using hS i (Set.mem_univ i))

theorem IsSep.pi {A : Set V} (hA : IsSep K A) :
    IsSep K (Set.pi Set.univ (fun _ : ι => A)) := by
  intro z hz
  obtain ⟨i, hi⟩ : ∃ i, z i ∉ A := by
    by_contra h
    push Not at h
    exact hz (fun i _ => h i)
  obtain ⟨l, b, hl, hlA⟩ := hA (z i) hi
  refine ⟨l.comp (LinearMap.proj i), b, by simpa using hl, ?_⟩
  intro a ha
  simpa using hlA (a i) (ha i (Set.mem_univ i))

end Pi

end GapExtremal
