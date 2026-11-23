/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Generic.Krylov

/-!
# Rational functions on generic points and simultaneous non-vanishing

`RatOn f`: on every injective `θ`, `f θ = P(θ)/Q(θ)` with `Q(θ) ≠ 0`. Closed under constants, `+`,
`*`, finite sums/products and division by `θ i − θ j`. `exists_common_ne`: finitely many `RatOn`
functions, each nonzero at some injective point, are simultaneously nonzero at a common injective
point, which can also avoid finitely many nonzero polynomials.
-/

@[expose] public section

namespace DFT

section

open MvPolynomial

variable {M : ℕ}

/-- A polynomial quotient whose denominator is nonzero on injective site potentials. -/
def RatOn (f : (Fin M → ℝ) → ℝ) : Prop :=
  ∃ P Q : MvPolynomial (Fin M) ℝ, ∀ θ : Fin M → ℝ, Function.Injective θ →
    eval θ Q ≠ 0 ∧ f θ * eval θ Q = eval θ P

lemma RatOn.const (a : ℝ) : RatOn (M := M) (fun _ => a) :=
  ⟨C a, 1, fun θ _ => ⟨by simp, by simp⟩⟩

lemma RatOn.add {f g : (Fin M → ℝ) → ℝ} (hf : RatOn f) (hg : RatOn g) : RatOn
    (fun θ => f θ + g θ) := by
  obtain ⟨P1, Q1, h1⟩ := hf; obtain ⟨P2, Q2, h2⟩ := hg
  refine ⟨P1 * Q2 + P2 * Q1, Q1 * Q2, fun θ hθ => ?_⟩
  obtain ⟨n1, e1⟩ := h1 θ hθ; obtain ⟨n2, e2⟩ := h2 θ hθ
  refine ⟨by simp [n1, n2], ?_⟩
  simp only [map_add, map_mul]; rw [← e1, ← e2]; ring

lemma RatOn.mul {f g : (Fin M → ℝ) → ℝ} (hf : RatOn f) (hg : RatOn g) : RatOn
    (fun θ => f θ * g θ) := by
  obtain ⟨P1, Q1, h1⟩ := hf; obtain ⟨P2, Q2, h2⟩ := hg
  refine ⟨P1 * P2, Q1 * Q2, fun θ hθ => ?_⟩
  obtain ⟨n1, e1⟩ := h1 θ hθ; obtain ⟨n2, e2⟩ := h2 θ hθ
  refine ⟨by simp [n1, n2], ?_⟩
  simp only [map_mul]; rw [← e1, ← e2]; ring

lemma RatOn.div_sub {f : (Fin M → ℝ) → ℝ} (hf : RatOn f) (i j : Fin M) :
    RatOn (fun θ => f θ / (θ i - θ j)) := by
  by_cases hij : i = j
  · subst hij; simpa using RatOn.const (M := M) 0
  · obtain ⟨P, Q, h⟩ := hf
    refine ⟨P, Q * (X i - X j), fun θ hθ => ?_⟩
    obtain ⟨n, e⟩ := h θ hθ
    have hne : θ i - θ j ≠ 0 := sub_ne_zero.mpr (fun h' => hij (hθ h'))
    refine ⟨by simp [n, hne], ?_⟩
    simp only [map_mul, map_sub, eval_X]; rw [← e]; field_simp

lemma RatOn.sum {ι : Type*} (s : Finset ι) {f : ι → (Fin M → ℝ) → ℝ} (hf : ∀ i ∈ s, RatOn (f i)) :
    RatOn (fun θ => ∑ i ∈ s, f i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RatOn.const (M := M) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma RatOn.prod {ι : Type*} (s : Finset ι) {f : ι → (Fin M → ℝ) → ℝ} (hf : ∀ i ∈ s, RatOn (f i)) :
    RatOn (fun θ => ∏ i ∈ s, f i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RatOn.const (M := M) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma RatOn.ite (p : Prop) [Decidable p] {f g : (Fin M → ℝ) → ℝ} (hf : RatOn f) (hg : RatOn g) :
    RatOn (fun θ => if p then f θ else g θ) := by
  by_cases hp : p
  · simpa [hp] using hf
  · simpa [hp] using hg

lemma RatOn.congr {f g : (Fin M → ℝ) → ℝ} (hf : RatOn f)
    (h : ∀ θ, Function.Injective θ → f θ = g θ) :
    RatOn g := by
  obtain ⟨P, Q, hPQ⟩ := hf
  exact ⟨P, Q, fun θ hθ => by rw [← h θ hθ]; exact hPQ θ hθ⟩

/-- The pairwise-difference polynomial. -/
noncomputable def discPoly : MvPolynomial (Fin M) ℝ :=
  ∏ p ∈ (Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 ≠ p.2), (X p.1 - X p.2)

lemma discPoly_ne_zero : (discPoly : MvPolynomial (Fin M) ℝ) ≠ 0 := by
  unfold discPoly
  rw [Finset.prod_ne_zero_iff]
  intro p hp h0
  have hne := (Finset.mem_filter.mp hp).2
  have := congrArg (eval (fun k => if k = p.1 then (1 : ℝ) else 0)) h0
  simp [hne.symm] at this

lemma injective_of_disc {θ : Fin M → ℝ} (h : eval θ (discPoly : MvPolynomial (Fin M) ℝ) ≠ 0) :
    Function.Injective θ := by
  intro i j hij
  by_contra hne
  apply h
  unfold discPoly
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hne⟩)
  simp [hij]

/-- **Simultaneous non-vanishing.** -/
theorem exists_common_ne {ι κ : Type*} [Finite ι] [Finite κ] (f : ι → (Fin M → ℝ) → ℝ)
    (hrat : ∀ i, RatOn (f i)) (hpt : ∀ i, ∃ θ, Function.Injective θ ∧ f i θ ≠ 0)
    (R : κ → MvPolynomial (Fin M) ℝ) (hR : ∀ k, R k ≠ 0) :
    ∃ θ, Function.Injective θ ∧ (∀ i, f i θ ≠ 0) ∧ ∀ k, eval θ (R k) ≠ 0 := by
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  choose P Q hPQ using hrat
  have hP : ∀ i, P i ≠ 0 := by
    intro i h0
    obtain ⟨θ, hθ, hf⟩ := hpt i
    obtain ⟨hQ, he⟩ := hPQ i θ hθ
    rw [h0, map_zero] at he
    exact hf ((mul_eq_zero.mp he).resolve_right hQ)
  set T : MvPolynomial (Fin M) ℝ := discPoly * (∏ i, P i) * ∏ k, R k
  have hT : T ≠ 0 := mul_ne_zero (mul_ne_zero discPoly_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => hP i)) (Finset.prod_ne_zero_iff.mpr fun k _ => hR k)
  obtain ⟨θ, hθ⟩ : ∃ θ, eval θ T ≠ 0 := by
    by_contra hall; push Not at hall
    exact hT (MvPolynomial.funext fun θ => by simp [hall θ])
  simp only [T, map_mul, map_prod] at hθ
  have hd : eval θ discPoly ≠ 0 := fun h => hθ (by rw [h]; ring)
  have hinj := injective_of_disc hd
  refine ⟨θ, hinj, fun i => ?_, fun k => ?_⟩
  · intro hf
    obtain ⟨-, he⟩ := hPQ i θ hinj
    rw [hf, zero_mul] at he
    apply hθ
    rw [Finset.prod_eq_zero (Finset.mem_univ i) he.symm]; ring
  · intro hk
    apply hθ
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hk]; ring

end

end DFT
