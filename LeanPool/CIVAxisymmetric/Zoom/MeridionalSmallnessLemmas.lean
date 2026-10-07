/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AnisotropicBounds
public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallness

/-!
# Meridional Smallness Lemmas

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- Monotonicity of `MeridionalSmallness` in the ball radius: if the condition holds
for radius `ρ`, it holds for every smaller radius `ρ'`. -/
theorem MeridionalSmallness.mono {ρ ρ' : ℝ} {u : ParabolicPoint → Vec3}
    (h : MeridionalSmallness ρ u) (hle : ρ' ≤ ρ) : MeridionalSmallness ρ' u := by
  intro ε hε
  rcases h ε hε with ⟨t₀, ht₀, h'⟩
  refine ⟨t₀, ht₀, fun t ht x₁ x₃ hball => ?_⟩
  apply h' t ht x₁ x₃
  rw [mem_vec3Ball] at hball ⊢
  linarith only [hle, hball]

/-- The meridional quantity is nonnegative everywhere. -/
theorem meridionalQuantity_nonneg (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    0 ≤ meridionalQuantity u z := by
  unfold meridionalQuantity
  positivity

/-- The negation of `MeridionalSmallness ρ u` is equivalent to the existence of a positive
constant `c₀` and sequences approaching the singular time at which the scaled quantity
exceeds `c₀`. This is the unfolding of the logical negation `eq:aniso:zoom:selected`. -/
theorem not_meridionalSmallness_iff {ρ : ℝ} {u : ParabolicPoint → Vec3} :
    ¬ MeridionalSmallness ρ u ↔ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t₀ ∈ Set.Ioo (-1 : ℝ) 0, ∃ t ∈ Set.Ioo t₀ 0,
      ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ ∧
        c₀ < (-t) * meridionalQuantity u (meridional x₁ x₃, t) := by
  constructor
  · intro h
    unfold MeridionalSmallness at h
    push Not at h
    exact h
  · intro h
    rcases h with ⟨c₀, hc₀, h⟩
    unfold MeridionalSmallness
    push Not
    exact ⟨c₀, hc₀, h⟩

/-- From the failure of `MeridionalSmallness ρ u` we can extract a positive constant `c₀`
and sequences `t n → 0⁻`, `x₁ n`, `x₃ n` such that the scaled meridional quantity
remains bounded below by `c₀`. -/
theorem exists_seq_of_not_meridionalSmallness {ρ : ℝ} {u : ParabolicPoint → Vec3}
    (h : ¬ MeridionalSmallness ρ u) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ t : ℕ → ℝ, ∃ x₁ x₃ : ℕ → ℝ, StrictMono t ∧
      (∀ n, t n ∈ Set.Ioo (-1 : ℝ) 0) ∧
      Filter.Tendsto t Filter.atTop (nhds 0) ∧
      ∀ n, meridional (x₁ n) (x₃ n) ∈ vec3Ball 0 ρ ∧
        c₀ < (-(t n)) * meridionalQuantity u (meridional (x₁ n) (x₃ n), t n) := by
  rcases (not_meridionalSmallness_iff.mp h) with ⟨c₀, hc₀, h_sel⟩
  -- Recursive step: given t ∈ Ioo(-1,0) and n : ℕ, produce t' > max t (-(1/(n+2)))
  -- with t' ∈ Ioo(-1,0) and (x₁', x₃') satisfying the ball and inequality.
  have h_next (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (n : ℕ) :
      ∃ t' : ℝ, max t (-(1 / ((n : ℝ) + 2))) < t' ∧ t' ∈ Set.Ioo (-1 : ℝ) 0 ∧
        (∃ x₁' x₃' : ℝ, meridional x₁' x₃' ∈ vec3Ball 0 ρ ∧
          c₀ < (-t') * meridionalQuantity u (meridional x₁' x₃', t')) := by
    let t₀ := max t (-(1 / ((n : ℝ) + 2)))
    have ht₀ : t₀ ∈ Set.Ioo (-1 : ℝ) 0 := by
      rcases ht with ⟨hlt_l, hlt_r⟩
      have h_left : -1 < t₀ := by
        have hmax : t ≤ t₀ := le_max_left _ _
        linarith only [hlt_l, hmax]
      have h_right : t₀ < 0 := by
        have hneg : -(1 / ((n : ℝ) + 2)) < 0 := by
          have hpos : 0 < 1 / ((n : ℝ) + 2) := div_pos (by norm_num) (by
            have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
            have hpos2 : (0 : ℝ) < 2 := by norm_num
            exact add_pos_of_nonneg_of_pos hn hpos2)
          linarith only [hpos]
        have ht_neg : t < 0 := hlt_r
        have hmax_lt' : max t (-(1 / ((n : ℝ) + 2))) < 0 := max_lt ht_neg hneg
        simpa [t₀] using hmax_lt'
      exact ⟨h_left, h_right⟩
    rcases h_sel t₀ ht₀ with ⟨t', ht'_mem, x₁', x₃', hball', hineq'⟩
    have ht'_ioo : t' ∈ Set.Ioo (-1 : ℝ) 0 := by
      rcases ht'_mem with ⟨hleft, hright⟩
      rcases ht₀ with ⟨ht₀_left, ht₀_right⟩
      exact ⟨by linarith only [ht₀_left, hleft], hright⟩
    exact ⟨t', ht'_mem.1, ht'_ioo, ⟨x₁', x₃', hball', hineq'⟩⟩
  -- Base triple: use h_sel at -(1/2) with t₀ = -(1/2).
  have h_base_ioo : (-(1/2 : ℝ)) ∈ Set.Ioo (-1 : ℝ) 0 := by
    constructor <;> norm_num
  rcases h_sel (-(1/2)) h_base_ioo with ⟨t0, ht0_mem, x10, x30, hball0, hineq0⟩
  -- t0 ∈ Ioo (-(1/2)) 0, but we need t0 ∈ Ioo (-1) 0 for the base of the recursion.
  have ht0_mem' : t0 ∈ Set.Ioo (-1 : ℝ) 0 := by
    rcases ht0_mem with ⟨hleft, hright⟩
    exact ⟨by linarith only [hleft], hright⟩
  -- Build the sequence by recursion on ℕ, carrying (t, x₁, x₃) and all proof obligations.
  -- We inline the step function directly in Nat.rec so that equation lemmas hold rfl.
  -- We use explicit Classical.choose to avoid pattern-matching-on-Exists issues
  -- inside the Nat.rec step (which constructs data in Sort, not Prop).
  let seq : ℕ → Σ' (p : ℝ × ℝ × ℝ),
      p.1 ∈ Set.Ioo (-1 : ℝ) 0 ∧
      meridional p.2.1 p.2.2 ∈ vec3Ball 0 ρ ∧
      c₀ < (-(p.1)) * meridionalQuantity u (meridional p.2.1 p.2.2, p.1) :=
    Nat.rec
      ⟨(t0, x10, x30), ht0_mem', hball0, hineq0⟩
      (fun n s =>
        let t := s.1.1
        let x₁ := s.1.2.1
        let x₃ := s.1.2.2
        let ht_mem := s.2.1
        let hball := s.2.2.1
        let hineq := s.2.2.2
        let t' := Classical.choose (h_next t ht_mem n)
        let h_t'_spec := Classical.choose_spec (h_next t ht_mem n)
        let ht'_ioo : t' ∈ Set.Ioo (-1 : ℝ) 0 := h_t'_spec.2.1
        let h_ex : ∃ x₁' x₃' : ℝ, meridional x₁' x₃' ∈ vec3Ball 0 ρ ∧
            c₀ < (-t') * meridionalQuantity u (meridional x₁' x₃', t') := h_t'_spec.2.2
        let x₁' := Classical.choose h_ex
        let h_x_spec := Classical.choose_spec h_ex
        let x₃' := Classical.choose h_x_spec
        let h_final := Classical.choose_spec h_x_spec
        ⟨(t', x₁', x₃'), ht'_ioo, h_final.1, h_final.2⟩)
  -- Extract components.
  let t_seq : ℕ → ℝ := fun n => (seq n).1.1
  let x₁_seq : ℕ → ℝ := fun n => (seq n).1.2.1
  let x₃_seq : ℕ → ℝ := fun n => (seq n).1.2.2
  have ht_seq_mem : ∀ n, t_seq n ∈ Set.Ioo (-1 : ℝ) 0 := fun n => (seq n).2.1
  have h_ball : ∀ n, meridional (x₁_seq n) (x₃_seq n) ∈ vec3Ball 0 ρ := fun n => (seq n).2.2.1
  have h_ineq : ∀ n, c₀ < (-(t_seq n)) * meridionalQuantity u (meridional (x₁_seq n) (x₃_seq n),
    t_seq n) :=
    fun n => (seq n).2.2.2
  -- The key inequality: max(t_n, -(1/(n+2))) < t_{n+1} for all n.
  -- Because the step function uses explicit projections (no pattern matching on seq n),
  -- t_seq (n+1) is definitionally Classical.choose (h_next (t_seq n) (ht_seq_mem n) n),
  -- so Classical.choose_spec applies directly.
  have hmax_lt : ∀ n, max (t_seq n) (-(1 / ((n : ℝ) + 2))) < t_seq (n + 1) := by
    intro n
    have hspec := Classical.choose_spec (h_next (t_seq n) (ht_seq_mem n) n)
    exact hspec.1
  -- StrictMono t_seq: follows from t_n < t_{n+1} which follows from hmax_lt.
  have h_lt_succ : ∀ n, t_seq n < t_seq (n + 1) := by
    intro n
    have hle : t_seq n ≤ max (t_seq n) (-(1 / ((n : ℝ) + 2))) := le_max_left _ _
    linarith only [hmax_lt n, hle]
  have h_strictMono : StrictMono t_seq :=
    strictMono_nat_of_lt_succ h_lt_succ
  -- Squeeze theorem: t_seq n → 0.
  -- We prove -(1/(n+1)) < t_seq n < 0 for all n.
  have h_upper : ∀ n, t_seq n < 0 := fun n => (ht_seq_mem n).2
  have h_lower : ∀ (n : ℕ), -(1 / ((n : ℝ) + 1)) < t_seq n := by
    intro n
    induction n with
    | zero =>
      -- n = 0: we need -(1/(0+1)) < t_seq 0, i.e., -1 < t0.
      have h := ht0_mem'
      rcases h with ⟨hleft, hright⟩
      -- hleft : -1 < t0, and -(1 / ((0 : ℝ) + 1)) = -1
      have h_eq : -(1 / (((0 : ℕ) : ℝ) + 1)) = (-1 : ℝ) := by norm_num
      rw [h_eq]
      dsimp [t_seq, seq]
      exact hleft
    | succ k ih =>
      -- n = k+1: we need -(1/((k+1)+1)) < t_seq (k+1), i.e., -(1/(k+2)) < t_seq (k+1).
      have hmax := hmax_lt k
      have hle : -(1 / ((k : ℝ) + 2)) ≤ max (t_seq k) (-(1 / ((k : ℝ) + 2))) := le_max_right _ _
      -- Goal: -(1 / (↑(k+1) + 1)) < t_seq (k+1) = -(1/(k+2)) < t_seq (k+1)
      -- hle gives -(1/(k+2)) ≤ max(...) and hmax gives max(...) < t_seq(k+1)
      have h_eq : ((k : ℕ) + 1 : ℝ) + 1 = (k : ℝ) + 2 := by
        ring
      simpa [Nat.cast_succ, h_eq] using lt_of_le_of_lt hle hmax
  -- Now use the squeeze theorem: -(1/(n+1)) < t_seq n < 0, and -(1/(n+1)) → 0.
  have h_tendsto : Filter.Tendsto t_seq Filter.atTop (nhds 0) := by
    have h_neg_one_div_tendsto : Filter.Tendsto (fun (n : ℕ) => -(1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
      have h_one_div : Filter.Tendsto (fun (n : ℕ) => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
        simpa [add_comm] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa [neg_zero] using h_one_div.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h_neg_one_div_tendsto tendsto_const_nhds
      (fun n => ?_) (fun n => ?_)
    · -- -(1/(n+1)) ≤ t_seq n
      linarith only [h_lower n]
    · -- t_seq n ≤ 0
      linarith only [h_upper n]
  -- Assemble the final result.
  refine ⟨c₀, hc₀, t_seq, x₁_seq, x₃_seq, h_strictMono, ht_seq_mem, h_tendsto, ?_⟩
  intro n
  exact ⟨h_ball n, h_ineq n⟩

end CIV
