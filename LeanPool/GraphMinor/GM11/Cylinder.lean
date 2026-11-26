/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.SquareChart
public import LeanPool.GraphMinor.GM11.Section3

/-!
# A cylinder made of squares

Squares `G i : [0, 1] × [0, 1] → Σ` for `i < n`, such that the right side of each is the left side
of the
next and the right side of the last is the left side of the first, form one map on the cylinder
(`exists_cylinder`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The square that holds the point `x` of `[0, 1]`, of `n` squares. -/
noncomputable def slabIndex (n : ℕ) (x : I) : ℕ := min ⌊x.1 * n⌋₊ (n - 1)

/-- The map on `[0, 1] × [0, 1]` made of `n` squares side by side. -/
noncomputable def stack (n : ℕ) (G : ℕ → I × I → S) (p : I × I) : S :=
  G (slabIndex n p.1) (clamp (p.1.1 * n - slabIndex n p.1), p.2)

/-- The closed slab of the `i`-th square. -/
def slab (n i : ℕ) : Set (I × I) := {p | (i : ℝ) ≤ p.1.1 * n ∧ p.1.1 * n ≤ i + 1}

theorem isClosed_slab (n i : ℕ) : IsClosed (slab n i) := by
  have h : Continuous fun p : I × I => p.1.1 * (n : ℝ) :=
    (continuous_subtype_val.comp continuous_fst).mul continuous_const
  exact (isClosed_le continuous_const h).inter (isClosed_le h continuous_const)

omit [TopologicalSpace S] in
theorem stack_eq {n i : ℕ} {G : ℕ → I × I → S} (hi : i < n)
    (adj : ∀ i t, G i (1, t) = G (i + 1) (0, t)) {p : I × I} (hp : p ∈ slab n i) :
    stack n G p = G i (clamp (p.1.1 * n - i), p.2) := by
  obtain ⟨h₁, h₂⟩ := hp
  have hzero : clamp 0 = 0 := by
    have := clamp_coe (0 : I)
    simpa using this
  have hone : clamp 1 = 1 := by
    have := clamp_coe (1 : I)
    simpa using this
  have hn : (1 : ℕ) ≤ n := by omega
  rcases h₂.lt_or_eq with h₃ | h₃
  · have hf : ⌊p.1.1 * (n : ℝ)⌋₊ = i := by
      rw [Nat.floor_eq_iff (mul_nonneg p.1.2.1 (Nat.cast_nonneg n))]
      exact ⟨h₁, h₃⟩
    have hs : slabIndex n p.1 = i := by
      simp only [slabIndex, hf]
      omega
    simp only [stack, hs]
  · have hf : ⌊p.1.1 * (n : ℝ)⌋₊ = i + 1 := by
      rw [h₃]
      exact_mod_cast Nat.floor_natCast (i + 1)
    have hc : clamp (p.1.1 * n - i) = 1 := by
      rw [h₃, add_sub_cancel_left]
      exact hone
    rw [hc]
    by_cases hi' : i + 1 ≤ n - 1
    · have hs : slabIndex n p.1 = i + 1 := by
        simp only [slabIndex, hf]
        omega
      have hd : p.1.1 * n - ((i + 1 : ℕ) : ℝ) = 0 := by
        rw [h₃]
        push_cast
        ring
      simp only [stack, hs, hd, hzero]
      exact (adj i p.2).symm
    · have hs : slabIndex n p.1 = i := by
        simp only [slabIndex, hf]
        omega
      have hd : p.1.1 * n - (i : ℝ) = 1 := by
        rw [h₃]
        ring
      simp only [stack, hs, hd, hone]

theorem continuous_stack {n : ℕ} (hn : 0 < n) {G : ℕ → I × I → S} (hG : ∀ i, Continuous (G i))
    (adj : ∀ i t, G i (1, t) = G (i + 1) (0, t)) : Continuous (stack n G) := by
  let f : Fin n → Set (I × I) := fun i => slab n i
  have hcov : ⋃ i, f i = univ := by
    refine eq_univ_of_forall fun p => mem_iUnion.mpr ?_
    have hx₀ : 0 ≤ p.1.1 * (n : ℝ) := mul_nonneg p.1.2.1 (by positivity)
    have hx₁ : p.1.1 * (n : ℝ) ≤ n := by
      have : p.1.1 ≤ 1 := p.1.2.2
      have h₂ : (0 : ℝ) ≤ n := by positivity
      nlinarith
    by_cases hlt : ⌊p.1.1 * (n : ℝ)⌋₊ < n
    · exact ⟨⟨_, hlt⟩, Nat.floor_le hx₀, (Nat.lt_floor_add_one _).le⟩
    · have hfl : (n : ℝ) ≤ p.1.1 * n := by
        have := Nat.floor_le hx₀
        have h₂ : (n : ℝ) ≤ ⌊p.1.1 * (n : ℝ)⌋₊ := by exact_mod_cast not_lt.mp hlt
        linarith
      have hn' : ((n - 1 : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub hn]
        simp
      refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩ <;> simp only [hn'] <;> linarith
  refine LocallyFinite.continuous (locallyFinite_of_finite f) hcov
    (fun i => isClosed_slab n i) fun i => ?_
  have hc : Continuous fun p : I × I => G i (clamp (p.1.1 * n - i), p.2) := by
    refine (hG i).comp (Continuous.prodMk (continuous_clamp.comp ?_) continuous_snd)
    exact ((continuous_subtype_val.comp continuous_fst).mul continuous_const).sub continuous_const
  exact hc.continuousOn.congr fun p hp => stack_eq i.2 adj hp

/-- **A cylinder made of squares.** -/
theorem exists_cylinder {n : ℕ} (hn : 0 < n) {G : ℕ → I × I → S} (hG : ∀ i, Continuous (G i))
    (adj : ∀ i t, G i (1, t) = G (i + 1) (0, t)) (wrap : ∀ t, G n (0, t) = G 0 (0, t)) :
    ∃ h : C(Circle × I, S), ∀ i, i < n → ∀ u t : I,
      h (Circle.exp (2 * Real.pi * ((i + u.1) / n)), t) = G i (u, t) := by
  have hcn : (0 : ℝ) < n := by exact_mod_cast hn
  let F : C(I × I, S) := ⟨stack n G, continuous_stack hn hG adj⟩
  have hclamp : ∀ {i : ℕ} {u : I} {y : ℝ}, y - i = u.1 → clamp (y - i) = u := fun h => by
    rw [h, clamp_coe]
  have hx : ∀ i, i < n → ∀ u : I, ∃ x : I, x.1 = (i + u.1) / n ∧ ((x, (0 : I)) : I × I) ∈ slab n i
    := by
    intro i hi u
    have h₁ : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    have hu₀ := u.2.1
    have hu₁ := u.2.2
    have hx₀ : 0 ≤ ((i : ℝ) + u.1) / n := by positivity
    have hx₁ : ((i : ℝ) + u.1) / n ≤ 1 := by
      rw [div_le_one hcn]
      linarith
    refine ⟨⟨_, hx₀, hx₁⟩, rfl, ?_⟩
    have hm : ((i : ℝ) + u.1) / n * n = i + u.1 := by field_simp
    constructor <;> simp only [hm] <;> linarith
  have hslab : ∀ {x : I} {i : ℕ}, ((x, (0 : I)) : I × I) ∈ slab n i → ∀ t : I, (x, t) ∈ slab n i :=
    fun h _ => h
  have hF : ∀ i, i < n → ∀ (u t : I) (x : I), x.1 = (i + u.1) / n → F (x, t) = G i (u, t) := by
    intro i hi u t x hxe
    have hm : x.1 * n - i = u.1 := by
      rw [hxe]
      field_simp
      ring
    have hmem : (x, t) ∈ slab n i := by
      have hu₀ := u.2.1
      have hu₁ := u.2.2
      constructor <;> simp only <;> linarith
    change stack n G (x, t) = _
    rw [stack_eq hi adj hmem]
    simp only
    rw [hclamp hm]
  have hends : ∀ v, F (0, v) = F (1, v) := by
    intro v
    obtain ⟨hl, hr⟩ : (0 : I).1 = (0 + (0 : I).1) / n ∧ (1 : I).1 = (((n - 1 : ℕ) : ℝ) +
      (1 : I).1) / n := by
      constructor
      · simp
      · rw [Nat.cast_sub hn]
        simp only [Icc.coe_one, Nat.cast_one, sub_add_cancel]
        field_simp
    have h₁ := hF 0 hn 0 v 0 (by simp)
    have h₂ := hF (n - 1) (by omega) 1 v 1 hr
    rw [h₁, h₂, adj (n - 1) v]
    have : n - 1 + 1 = n := by omega
    rw [this, wrap]
  refine ⟨cylinderLift 1 F hends, ?_⟩
  intro i hi u t
  obtain ⟨x, hxe, -⟩ := hx i hi u
  have h₁ := cylinderLift_apply 1 F hends x t
  have h₂ : arcParam 1 x = Circle.exp (2 * Real.pi * (((i : ℝ) + u.1) / n)) := by
    rw [← hxe]
    rw [arcParam_apply, one_mul]
  rw [← h₂, h₁]
  exact hF i hi u t x hxe

/-- Each point of the circle is a point of one of the `n` arcs. -/
theorem exists_circle_param {n : ℕ} (hn : 0 < n) (z : Circle) :
    ∃ i, i < n ∧ ∃ u : I, u.1 < 1 ∧ z = Circle.exp (2 * Real.pi * ((i + u.1) / n)) := by
  have hcn : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨x, hx⟩ : ∃ x : ℝ, 0 ≤ x ∧ x < 1 ∧ z = Circle.exp (2 * Real.pi * x) := by
    obtain ⟨t, ht⟩ := arcParam_surjective 1 z
    have hz : z = Circle.exp (2 * Real.pi * t.1) := by
      rw [← ht, arcParam_apply, one_mul]
    by_cases h1 : t.1 = 1
    · refine ⟨0, le_rfl, one_pos, ?_⟩
      rw [hz, h1]
      simp [Circle.exp_two_pi]
    · exact ⟨t.1, t.2.1, lt_of_le_of_ne t.2.2 h1, hz⟩
  obtain ⟨h₀, h₁, hz⟩ := hx
  have hy₀ : 0 ≤ x * (n : ℝ) := by positivity
  have hyn : x * n < n := by nlinarith
  have hfl : ⌊x * (n : ℝ)⌋₊ < n := by
    rw [Nat.floor_lt hy₀]
    exact hyn
  have ha := Nat.floor_le hy₀
  have hb := Nat.lt_floor_add_one (x * (n : ℝ))
  refine ⟨_, hfl, ⟨x * n - ⌊x * (n : ℝ)⌋₊, by linarith, by linarith⟩, by simp only; linarith, ?_⟩
  rw [hz]
  congr 2
  simp only
  field_simp
  ring

end GraphMinor.GM11
