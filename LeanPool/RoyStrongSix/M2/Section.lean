/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import LeanPool.RoyStrongSix.M2.Veronese

/-!
# Hyperplane sections for filtered Hilbert functions (Roy, Lemma 8.5)

* `hfun_mono`: `J ⊆ J'` implies `hfun J' ≤ hfun J`.
* `hfun_section`: if `P` has block degree `≤ D` and is a non-zero-divisor modulo `J`, then
  `hfun (J + (P)) (t+1) ≤ hfun J (t+1) − hfun J t`.
* `HasData.of_le_Δ`: from such an inequality, the data of `hfun (J + (P))` is lexicographically
  `≤ (a, c)` when `hfun J` has data `(a+1, c)`. If the dimension drops by exactly one, the degree
  does not
  increase.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

/-! ### A pure lemma on data -/

theorem HasData.shift {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c) : HasData (shift f) a c := by
  refine ⟨h.1, ?_⟩
  rw [iter_Δ_shift]
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp h.2
  exact Filter.eventually_atTop.mpr ⟨k0, fun k hk => hk0 (k + 1) (by omega)⟩

theorem HasData.fwd {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f (a + 1) c) : HasData (Δ f) a c :=
  ⟨h.1, by simpa [Function.iterate_succ_apply] using h.2⟩

/-- If `0 ≤ g (t+1) ≤ f (t+1) − f t`, `g` is eventually polynomial and `f` has data `(a+1, c)`, then
`g` is eventually zero or has data `(b, d)` with `(b, d) ≤ (a, c)` lexicographically. -/
theorem HasData.of_le_Δ {f g : ℕ → ℤ} {a : ℕ} {c : ℤ} (hf : HasData f (a + 1) c) (hg : EvPoly g)
    (hg0 : ∀ k, 0 ≤ g k) (hle : ∀ t, g (t + 1) ≤ f (t + 1) - f t) :
    (∀ᶠ k in Filter.atTop, g k = 0) ∨ ∃ b d, HasData g b d ∧ (b < a ∨ (b = a ∧ d ≤ c)) := by
  by_cases hz : ∀ᶠ k in Filter.atTop, g k = 0
  · exact Or.inl hz
  obtain ⟨b, d, hgd⟩ := HasData.exists hg hz
  refine Or.inr ⟨b, d, hgd, ?_⟩
  exact hgd.shift.compare hf.fwd (Filter.Eventually.of_forall fun t => hle t)
    (Filter.Eventually.of_forall fun t => hg0 (t + 1))

/-- In dimension `0`, a section is eventually zero. -/
theorem eventually_zero_of_le_Δ {f g : ℕ → ℤ} {c : ℤ} (hf : HasData f 0 c)
    (hg0 : ∀ k, 0 ≤ g k) (hle : ∀ t, g (t + 1) ≤ f (t + 1) - f t) :
    ∀ᶠ k in Filter.atTop, g k = 0 := by
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hf.2
  refine Filter.eventually_atTop.mpr ⟨k0 + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ k by omega)
  have h1 := hle j
  have h2 : f (j + 1) = c := hk0 _ (by omega)
  have h3 : f j = c := hk0 _ (by omega)
  rw [add_comm 1 j]
  linarith [hg0 (j + 1)]

/-! ### The section inequality -/

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
variable (β : σ → ι) (D : ι → ℕ) (K : Type*) [Field K]

omit [DecidableEq σ] [Fintype ι] in
theorem hfun_mono [Finite ι] {J J' : Ideal (MvPolynomial σ K)} (h : J ≤ J') (t : ℕ) :
    hfun β D K J' t ≤ hfun β D K J t := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  unfold hfun
  have := Submodule.finrank_mono (inf_le_inf_right (FLE K β (t • D))
    (Submodule.restrictScalars_mono K h))
  have := Submodule.finrank_mono (inf_le_right : J'.restrictScalars K ⊓ FLE K β (t • D) ≤ _)
  omega

omit [DecidableEq σ] [Fintype ι] in
theorem hfun_le (J : Ideal (MvPolynomial σ K)) (t : ℕ) : hfun β D K J t ≤ finrank K (FLE K β (t
  • D)) :=
  Nat.sub_le _ _

omit [DecidableEq σ] [Fintype ι] in
/-- **Roy, Lemma 8.5.** -/
theorem hfun_section [Finite ι] {J : Ideal (MvPolynomial σ K)} {P : MvPolynomial σ K} (hP : P ∈
  FLE K β D)
    (hnzd : ∀ Q, P * Q ∈ J → Q ∈ J) (t : ℕ) :
    (hfun β D K (J ⊔ Ideal.span {P}) (t + 1) : ℤ) ≤ hfun β D K J (t + 1) - hfun β D K J t := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  by_cases hP0 : P = 0
  · -- then `J = ⊤`
    have htop : J = ⊤ := (Ideal.eq_top_iff_one _).mpr (hnzd 1 (by simp [hP0]))
    have h0 : ∀ t, hfun β D K (⊤ : Ideal (MvPolynomial σ K)) t = 0 := fun t => by
      unfold hfun; rw [Submodule.restrictScalars_top, top_inf_eq, Nat.sub_self]
    have : J ⊔ Ideal.span {P} = ⊤ := by rw [htop, top_sup_eq]
    simp [htop, h0]
  set F0 := FLE K β (t • D)
  set F1 := FLE K β ((t + 1) • D)
  let mP : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := LinearMap.mulLeft K P
  have hinj : Function.Injective mP := fun x y hxy => mul_left_cancel₀ hP0 hxy
  set M := F0.map mP
  have hM : M ≤ F1 := by
    rintro _ ⟨Q, hQ, rfl⟩
    have := mul_mem_FLE K hP hQ
    rwa [show D + t • D = (t + 1) • D by rw [succ_nsmul, add_comm]] at this
  set J1 := J.restrictScalars K ⊓ F1
  set J0 := J.restrictScalars K ⊓ F0
  set J2 := (J ⊔ Ideal.span {P}).restrictScalars K ⊓ F1
  have : FiniteDimensional K J1 := Submodule.finiteDimensional_of_le inf_le_right
  have : FiniteDimensional K M := Submodule.finiteDimensional_of_le hM
  have : FiniteDimensional K J2 := Submodule.finiteDimensional_of_le inf_le_right
  have hsup : J1 ⊔ M ≤ J2 := by
    apply sup_le (inf_le_inf_right _ (Submodule.restrictScalars_mono K le_sup_left))
    intro x hx
    refine ⟨?_, hM hx⟩
    obtain ⟨Q, -, rfl⟩ := hx
    exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self P))
  have hinf : J1 ⊓ M = J0.map mP := by
    apply le_antisymm
    · rintro x ⟨⟨hxJ, -⟩, Q, hQ, rfl⟩
      exact ⟨Q, ⟨hnzd Q hxJ, hQ⟩, rfl⟩
    · rintro _ ⟨Q, ⟨hQJ, hQ⟩, rfl⟩
      exact ⟨⟨J.mul_mem_left P hQJ, hM ⟨Q, hQ, rfl⟩⟩, Q, hQ, rfl⟩
  have e1 : ∀ (U : Submodule K (MvPolynomial σ K)) [FiniteDimensional K U],
      finrank K (U.map mP) = finrank K U :=
    fun U _ => LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj U).symm
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq J1 M
  rw [hinf] at h1
  have eM : finrank K M = finrank K F0 := e1 F0
  have eJ0 : finrank K (J0.map mP) = finrank K J0 := e1 J0
  have h2 := Submodule.finrank_mono hsup
  have h3 : finrank K J2 ≤ finrank K F1 := Submodule.finrank_mono inf_le_right
  have h4 : finrank K J0 ≤ finrank K F0 := Submodule.finrank_mono inf_le_right
  have h5 : finrank K J1 ≤ finrank K F1 := Submodule.finrank_mono inf_le_right
  have f1 : hfun β D K (J ⊔ Ideal.span {P}) (t + 1) = finrank K F1 - finrank K J2 := rfl
  have f2 : hfun β D K J (t + 1) = finrank K F1 - finrank K J1 := rfl
  have f3 : hfun β D K J t = finrank K F0 - finrank K J0 := rfl
  rw [f1, f2, f3, Nat.cast_sub h3, Nat.cast_sub h4, Nat.cast_sub h5]
  omega

end StrongSix.M2

end LeanPool
