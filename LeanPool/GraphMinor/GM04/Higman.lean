/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Data.Finset.Defs
import Mathlib.Data.List.Forall2

/-!
# The theorem of Higman quoted as Graph Minors IV, (8.3)

Graph Minors IV, (8.3) (page 249), quoting G. Higman, *Ordering by divisibility in abstract
algebras*, Proc. London Math. Soc. (3) 2 (1952) 326–336: "(8.3) *Let $\Omega$ be a well-quasi
-order, and let $X_i$ ($i = 1, 2, \dots$) be a countable sequence of finite subsets of $E(\Omega)$.
Then there exists an infinite subset $I \subseteq \{1, 2, \dots\}$ with the property that for all
$i$, $i' \in I$ with $i < i'$ there is an injection $\alpha \colon X_i \to X_{i'}$ such that $x \le
\alpha(x)$ for all $x \in X_i$.*"

In the proof of (8.4) the paper applies (8.3) to sets of edges, each labelled by an element of a
well-quasi-order, where different edges may have the same label. `Higman83Statement` is therefore
stated for finite sets `Xᵢ` of a type `κ` with labels `ℓ i : κ → Ω`. The statement as printed is
the case `κ = Ω`, `ℓ i = id`.
-/

@[expose] public section

namespace GraphMinor.GM04

/-- Graph Minors IV, (8.3), for labelled finite sets: for every sequence of finite sets `X i` with
labels `ℓ i` in a well-quasi-order `Ω`, there is an infinite set `I` of indices such that for all
`i < i'` in `I` some injection `g : X i → X i'` satisfies `ℓ i x ≤ ℓ i' (g x)` for all `x ∈ X i`. -/
def Higman83Statement : Prop :=
  ∀ {κ Ω : Type*} [Preorder Ω], WellQuasiOrderedLE Ω → ∀ (X : ℕ → Finset κ) (ℓ : ℕ → κ → Ω),
    ∃ I : Set ℕ, I.Infinite ∧ ∀ i ∈ I, ∀ i' ∈ I, i < i' →
      ∃ g : κ → κ, Set.InjOn g (X i) ∧ Set.MapsTo g (X i) (X i') ∧
        ∀ x ∈ X i, ℓ i x ≤ ℓ i' (g x)

/-- A sublist relation between duplicate-free lists gives an injection between them. -/
theorem exists_inj_of_sublistForall₂ {κ Ω : Type*} {r : Ω → Ω → Prop} {l₁ l₂ : List κ}
    {ℓ₁ ℓ₂ : κ → Ω} (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup)
    (h : List.SublistForall₂ (fun x y ↦ r (ℓ₁ x) (ℓ₂ y)) l₁ l₂) :
    ∃ g : κ → κ, (∀ x ∈ l₁, ∀ y ∈ l₁, g x = g y → x = y) ∧
      (∀ x ∈ l₁, g x ∈ l₂) ∧ (∀ x ∈ l₁, r (ℓ₁ x) (ℓ₂ (g x))) := by
  classical
  induction h with
  | nil => exact ⟨id, by simp, by simp, by simp⟩
  | @cons a₁ a₂ t₁ t₂ hr hsub ih =>
    obtain ⟨ha₁, hnd₁'⟩ := List.nodup_cons.1 hnd₁
    obtain ⟨ha₂, hnd₂'⟩ := List.nodup_cons.1 hnd₂
    obtain ⟨g, hinj, hmem, hrel⟩ := ih hnd₁' hnd₂'
    have hg : ∀ x ∈ t₁, (if x = a₁ then a₂ else g x) = g x := fun x hx ↦
      ite_eq_right fun (h : x = a₁) ↦ ha₁ (h ▸ hx)
    refine ⟨fun x ↦ if x = a₁ then a₂ else g x, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [List.mem_cons] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · simp only [↓reduceIte, hg y hy] at hxy
        exact absurd (hxy ▸ hmem y hy) ha₂
      · simp only [↓reduceIte, hg x hx] at hxy
        exact absurd (hxy ▸ hmem x hx) ha₂
      · simp only [hg x hx, hg y hy] at hxy
        exact hinj x hx y hy hxy
    · intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · simp
      · simp only [hg x hx]
        exact Or.inr (hmem x hx)
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa using hr
      · simp only [hg x hx]
        exact hrel x hx
  | @cons_right a l₁ t₂ hsub ih =>
    obtain ⟨_, hnd₂'⟩ := List.nodup_cons.1 hnd₂
    obtain ⟨g, hinj, hmem, hrel⟩ := ih hnd₁ hnd₂'
    exact ⟨g, hinj, fun x hx ↦ List.mem_cons_of_mem a (hmem x hx), hrel⟩

end GraphMinor.GM04
