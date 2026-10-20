/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Proofs.GeneralizedGradientStep
public import LeanPool.LongTails.Proofs.GeneralizedAcceleratedEnergy
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
omit [NormedAddCommGroup E] in
lemma tentativeWeight_pos (s : Iterate E) (hguess : 0 < s.guess) :
    0 < tentativeWeight s := by
  unfold tentativeWeight
  positivity

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
omit [NormedAddCommGroup E] in
lemma tentativeWeight_equation (s : Iterate E) (hA : 0 ≤ s.A)
    (hguess : 0 < s.guess) :
    s.guess * tentativeWeight s ^ 2 = s.A + tentativeWeight s := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 4 * s.guess * s.A by positivity)
  unfold tentativeWeight
  field_simp
  ring_nf at hs ⊢
  nlinarith

omit [CompleteSpace E] in
lemma coupling_same (A M : ℝ) (x : E) (hA : 0 ≤ A) (hM : 0 < M) :
    coupling (⟨A, x, x, M⟩ : Iterate E) = x := by
  have ha := tentativeWeight_pos (⟨A, x, x, M⟩ : Iterate E) hM
  have hsum : A + tentativeWeight (⟨A, x, x, M⟩ : Iterate E) ≠ 0 :=
    ne_of_gt (by linarith)
  unfold coupling
  simp only
  rw [← add_smul, ← add_div, div_self hsum, one_smul]

lemma damping_bounds {M G : ℝ} (hM : 0 < M) (hG : 0 < G) :
    0 < min 1 (G / M) ∧ min 1 (G / M) ≤ 1 ∧ min 1 (G / M) * M ≤ G := by
  refine ⟨lt_min zero_lt_one (div_pos hG hM), min_le_left _ _, ?_⟩
  calc
    min 1 (G / M) * M ≤ (G / M) * M :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
    _ = G := div_mul_cancel₀ _ hM.ne'

omit [CompleteSpace E] in
lemma finish_uniform (p : Pending E) (g : E)
    (hA : 0 ≤ p.previous.A) (ha : 0 < p.weight)
    (hM : 0 < p.curvature) (hG : 0 < p.previous.guess) :
    let γ := min 1 (p.previous.guess / p.curvature)
    let B := p.previous.A + γ * p.weight
    (finish p g).A = B ∧
    (finish p g).x = ((1 - γ) * p.previous.A / B) • p.previous.x +
      (γ * (p.previous.A + p.weight) / B) • p.point ∧
    (finish p g).z = p.previous.z - (γ * p.weight) • g ∧
    0 < (finish p g).guess := by
  dsimp only
  unfold finish
  split_ifs with h
  · have hd : 1 ≤ p.previous.guess / p.curvature := (le_div_iff₀ hM).mpr (by simpa)
    rw [min_eq_left hd]
    have hsum : p.previous.A + p.weight ≠ 0 := ne_of_gt (by linarith)
    simp [hsum, div_pos hG (by norm_num : (0 : ℝ) < 16)]
  · have hd : p.previous.guess / p.curvature ≤ 1 :=
      (div_le_one hM).mpr (le_of_lt (lt_of_not_ge h))
    rw [min_eq_right hd]
    exact ⟨rfl, rfl, rfl, by positivity⟩

omit [CompleteSpace E] in
lemma step_weights {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    let M := localCurvature L0 L1 (g (coupling s))
    let γ := min 1 (s.guess / M)
    (step L0 L1 g s).A = s.A + γ * tentativeWeight s ∧
    s.A < (step L0 L1 g s).A ∧
    (step L0 L1 g s).A ≤ s.A + tentativeWeight s ∧
    0 < (step L0 L1 g s).guess := by
  let p := prepare L0 L1 s (coupling s) (g (coupling s))
  have hM := localCurvature_pos hL0 hL1 (g (coupling s))
  have ha := tentativeWeight_pos s hG
  have hd := damping_bounds hM hG
  have hf := finish_uniform p (g p.point) hA ha hM hG
  refine ⟨hf.1, ?_, ?_, hf.2.2.2⟩
  · change s.A < (finish p (g p.point)).A
    rw [hf.1]
    exact lt_add_of_pos_right _ (mul_pos hd.1 ha)
  · change (finish p (g p.point)).A ≤ _
    rw [hf.1]
    have hm := mul_le_mul_of_nonneg_right hd.2.1 ha.le
    dsimp [p, prepare] at *
    linarith

lemma down_growth {G A a : ℝ} (hG : 0 < G) (hA : 0 ≤ A) (ha : 0 < a)
    (he : G * a ^ 2 = A + a) :
    1 / (2 * Real.sqrt G) ≤ Real.sqrt (A + a) - Real.sqrt A := by
  have hnew : 0 < A + a := by positivity
  have hroot := congrArg Real.sqrt he
  rw [Real.sqrt_mul hG.le, Real.sqrt_sq ha.le] at hroot
  have hGroot := Real.sqrt_pos.mpr hG
  have hnewroot := Real.sqrt_pos.mpr hnew
  have hsq := Real.sq_sqrt hA
  have hsqnew := Real.sq_sqrt hnew.le
  have hmon := Real.sqrt_le_sqrt (show A ≤ A + a by linarith)
  have hprod := mul_nonneg (Real.sqrt_nonneg G) (sq_nonneg (Real.sqrt (A + a) - Real.sqrt A))
  have hscaled : Real.sqrt (A + a) ≤
      (2 * Real.sqrt G * (Real.sqrt (A + a) - Real.sqrt A)) * Real.sqrt (A + a) := by
    nlinarith [mul_pos hGroot ha]
  have hcancel := (mul_le_mul_iff_left₀ hnewroot).mp
    (show 1 * Real.sqrt (A + a) ≤
        (2 * Real.sqrt G * (Real.sqrt (A + a) - Real.sqrt A)) * Real.sqrt (A + a) by
      nlinarith only [hscaled])
  apply (div_le_iff₀ (show 0 < 2 * Real.sqrt G by positivity)).mpr
  nlinarith only [hcancel]

lemma step_energy {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (s : Iterate E) (u : E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    let y := coupling s
    let M := localCurvature L0 L1 (g y)
    let w := y - (1 / M) • g y
    let γ := min 1 (s.guess / M)
    let next := step L0 L1 g s
    next.A * (f next.x - f u) + 1 / 2 * ‖next.z - u‖ ^ 2 +
        γ * (s.A + tentativeWeight s) * (3 * M / 8) * ‖w - y‖ ^ 2 ≤
      s.A * (f s.x - f u) + 1 / 2 * ‖s.z - u‖ ^ 2 := by
  let y := coupling s
  let M := localCurvature L0 L1 (g y)
  let w := y - (1 / M) • g y
  let γ := min 1 (s.guess / M)
  have hM : 0 < M := localCurvature_pos hL0 hL1 _
  have ha := tentativeWeight_pos s hG
  have hd := damping_bounds hM hG
  have hw : γ * tentativeWeight s ^ 2 * M ≤ s.A + tentativeWeight s := by
    have hm := mul_le_mul_of_nonneg_right hd.2.2 (sq_nonneg (tentativeWeight s))
    rw [← tentativeWeight_equation s hA hG]
    nlinarith only [hm]
  have hf := finish_uniform (prepare L0 L1 s y (g y)) (g w) hA ha hM hG
  dsimp only [prepare] at hf
  dsimp only
  change (finish _ _).A * (f (finish _ _).x - f u) +
    1 / 2 * ‖(finish _ _).z - u‖ ^ 2 + _ ≤ _
  dsimp only [prepare, y, M, w] at hf ⊢
  rw [hf.1, hf.2.1, hf.2.2.1]
  exact damped_step hM hc hg s.x s.z u w hA ha hd.1 hd.2.1 hw
    (local_step_residual hL0 hL1 hgd hH y)

/-- The objective-gap and squared-distance potential for accelerated convergence. -/
noncomputable def energy (f : E → ℝ) (u : E) (s : Iterate E) : ℝ :=
  s.A * (f s.x - f u) + 1 / 2 * ‖s.z - u‖ ^ 2

/-- The nonnegative energy decrease charged to one accelerated step. -/
noncomputable def dissipation (L0 L1 : ℝ) (g : E → E) (s : Iterate E) : ℝ :=
  let y := coupling s
  let M := localCurvature L0 L1 (g y)
  let w := y - (1 / M) • g y
  min 1 (s.guess / M) * (s.A + tentativeWeight s) * (3 * M / 8) * ‖w - y‖ ^ 2

omit [CompleteSpace E] in
lemma dissipation_nonneg {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    0 ≤ dissipation L0 L1 g s := by
  have hM := localCurvature_pos hL0 hL1 (g (coupling s))
  have ha := tentativeWeight_pos s hG
  dsimp [dissipation]
  positivity

omit [CompleteSpace E] in
lemma run_valid {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (n : ℕ) :
    0 ≤ (run L0 L1 g s n).A ∧ 0 < (run L0 L1 g s n).guess := by
  induction n with
  | zero => exact ⟨hA, hG⟩
  | succ n ih =>
    have hs := step_weights (g := g) hL0 hL1 (run L0 L1 g s n) ih.1 ih.2
    exact ⟨(ih.1.trans hs.2.1.le), hs.2.2.2⟩

lemma run_energy {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (s : Iterate E) (u : E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (n : ℕ) :
    energy f u (run L0 L1 g s n) +
      ∑ k ∈ Finset.range n, dissipation L0 L1 g (run L0 L1 g s k) ≤ energy f u s := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hv := run_valid (g := g) hL0 hL1 s hA hG n
    have hs := step_energy hL0 hL1 hc hg hgd hH (run L0 L1 g s n) u hv.1 hv.2
    change energy f u (run L0 L1 g s (n + 1)) +
      dissipation L0 L1 g (run L0 L1 g s n) ≤ energy f u (run L0 L1 g s n) at hs
    rw [Finset.sum_range_succ]
    linarith

omit [CompleteSpace E] in
lemma run_weight_mono {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    Monotone (fun n => (run L0 L1 g s n).A) := by
  apply monotone_nat_of_le_succ
  intro n
  have hv := run_valid (g := g) hL0 hL1 s hA hG n
  exact (step_weights (g := g) hL0 hL1 _ hv.1 hv.2).2.1.le

omit [CompleteSpace E] in
lemma step_guess {g : E → E} {L0 L1 : ℝ} (s : Iterate E) :
    (step L0 L1 g s).guess =
      if localCurvature L0 L1 (g (coupling s)) ≤ s.guess then s.guess / 16 else 16 * s.guess := by
  by_cases h : localCurvature L0 L1 (g (coupling s)) ≤ s.guess <;>
    simp [step, finish, prepare, h]

omit [CompleteSpace E] in
lemma step_inverse_sqrt_guess {g : E → E} {L0 L1 : ℝ}
    (s : Iterate E) (hG : 0 < s.guess) :
    1 / Real.sqrt (step L0 L1 g s).guess =
      if localCurvature L0 L1 (g (coupling s)) ≤ s.guess
      then 4 * (1 / Real.sqrt s.guess) else (1 / Real.sqrt s.guess) / 4 := by
  rw [step_guess]
  split_ifs <;> simp [Real.sqrt_div, Real.sqrt_mul, hG.le]
  <;> norm_num <;> ring

omit [CompleteSpace E] in
lemma step_down_growth {g : E → E} {L0 L1 : ℝ}
    (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hdown : localCurvature L0 L1 (g (coupling s)) ≤ s.guess) :
    1 / (2 * Real.sqrt s.guess) ≤
      Real.sqrt (step L0 L1 g s).A - Real.sqrt s.A := by
  have hweight : (step L0 L1 g s).A = s.A + tentativeWeight s := by
    simp [step, finish, prepare, hdown]
  rw [hweight]
  exact down_growth hG hA (tentativeWeight_pos s hG) (tentativeWeight_equation s hA hG)

omit [CompleteSpace E] in
lemma down_sum_le_sqrt {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (N : ℕ) :
    (∑ i ∈ Finset.range N,
      if localCurvature L0 L1 (g (coupling (run L0 L1 g s i))) ≤ (run L0 L1 g s i).guess
      then 1 / Real.sqrt (run L0 L1 g s i).guess else 0) ≤
        2 * Real.sqrt (run L0 L1 g s N).A := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hv := run_valid (g := g) hL0 hL1 s hA hG n
    split_ifs with hd
    · have hs := step_down_growth (run L0 L1 g s n) hv.1 hv.2 hd
      have he : 1 / (2 * Real.sqrt (run L0 L1 g s n).guess) =
          (1 / Real.sqrt (run L0 L1 g s n).guess) / 2 := by ring
      rw [he] at hs
      change _ ≤ 2 * Real.sqrt (step L0 L1 g (run L0 L1 g s n)).A
      linarith
    · have hs := Real.sqrt_le_sqrt
        (step_weights (g := g) hL0 hL1 (run L0 L1 g s n) hv.1 hv.2).2.1.le
      change _ ≤ 2 * Real.sqrt (step L0 L1 g (run L0 L1 g s n)).A
      linarith

omit [CompleteSpace E] in
lemma step_high_dissipation {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1)
    (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hup : s.guess ≤ localCurvature L0 L1 (g (coupling s)))
    (hhigh : 8 * L0 < localCurvature L0 L1 (g (coupling s))) :
    (step L0 L1 g s).A * s.guess ≤
      (512 / 3) * L1 ^ 2 * dissipation L0 L1 g s := by
  let M := localCurvature L0 L1 (g (coupling s))
  let d := ‖coupling s - (1 / M) • g (coupling s) - coupling s‖
  have hM : 0 < M := localCurvature_pos hL0 hL1.le _
  have hmin : min 1 (s.guess / M) = s.guess / M :=
    min_eq_right ((div_le_one hM).mpr hup)
  have hmove : 1 / (8 * L1) ≤ d :=
    (local_step_movement hL0 hL1 (coupling s) (g (coupling s))).resolve_left
      (not_le_of_gt hhigh)
  have hm : 1 ≤ 8 * L1 * d := by
    have ht := (div_le_iff₀ (show 0 < 8 * L1 by positivity)).mp hmove
    nlinarith only [ht]
  have hs : 1 ≤ 64 * L1 ^ 2 * d ^ 2 := by nlinarith [sq_nonneg (8 * L1 * d - 1)]
  have ha := tentativeWeight_pos s hG
  have hd : dissipation L0 L1 g s = (3 / 8) * s.guess * (s.A + tentativeWeight s) * d ^ 2 := by
    change min 1 (s.guess / M) * (s.A + tentativeWeight s) * (3 * M / 8) * d ^ 2 = _
    rw [hmin]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ s.guess * (s.A + tentativeWeight s) by positivity)
  have hw := mul_le_mul_of_nonneg_right
    (step_weights (g := g) hL0 hL1.le s hA hG).2.2.1 hG.le
  rw [hd]
  nlinarith only [hmul, hw]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma initial_energy {f : E → ℝ} {g : E → E} {L0 L1 R Δ : ℝ}
    (hΔ : 0 < Δ) (x0 u : E)
    (hdist : ‖x0 - u‖ ≤ R) (hgap : f x0 - f u ≤ Δ) :
    energy f u (initialIterate L0 L1 R Δ x0 g) ≤ R ^ 2 := by
  have hgap' := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ R ^ 2 / (2 * Δ) by positivity)
  have he : R ^ 2 / (2 * Δ) * Δ = R ^ 2 / 2 := by field_simp
  rw [he] at hgap'
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  dsimp [energy, initialIterate]
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma energy_nonneg {f : E → ℝ} {u : E} (hmin : IsMinOn f univ u)
    (s : Iterate E) (hA : 0 ≤ s.A) : 0 ≤ energy f u s := by
  have hg : 0 ≤ f s.x - f u := sub_nonneg.mpr (hmin (mem_univ _))
  exact add_nonneg (mul_nonneg hA hg) (by positivity)

lemma run_dissipation_le {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (s : Iterate E) (u : E) (hmin : IsMinOn f univ u)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess) (N : ℕ) :
    (∑ i ∈ Finset.range N, dissipation L0 L1 g (run L0 L1 g s i)) ≤ energy f u s := by
  have he := run_energy hL0 hL1 hc hg hgd hH s u hA hG N
  have hn := energy_nonneg hmin (run L0 L1 g s N) (run_valid (g := g) hL0 hL1 s hA hG N).1
  linarith

lemma run_high_sum_le {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (s : Iterate E) (u : E) (hmin : IsMinOn f univ u)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess) (N : ℕ)
    (Q : Finset ℕ) (hQ : Q ⊆ Finset.range N)
    (hup : ∀ i ∈ Q, (run L0 L1 g s i).guess ≤
      localCurvature L0 L1 (g (coupling (run L0 L1 g s i))))
    (hhigh : ∀ i ∈ Q, 8 * L0 < localCurvature L0 L1 (g (coupling (run L0 L1 g s i)))) :
    (∑ i ∈ Q, (run L0 L1 g s (i + 1)).A * (run L0 L1 g s i).guess) ≤
      (512 / 3) * L1 ^ 2 * energy f u s := by
  have hd := run_dissipation_le hL0 hL1.le hc hg hgd hH s u hmin hA hG N
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg hQ
    (fun i _ _ => dissipation_nonneg (g := g) hL0 hL1.le (run L0 L1 g s i)
      (run_valid (g := g) hL0 hL1.le s hA hG i).1
      (run_valid (g := g) hL0 hL1.le s hA hG i).2)
  calc
    _ ≤ ∑ i ∈ Q, (512 / 3) * L1 ^ 2 * dissipation L0 L1 g (run L0 L1 g s i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hv := run_valid (g := g) hL0 hL1.le s hA hG i
      exact step_high_dissipation hL0 hL1 _ hv.1 hv.2 (hup i hi) (hhigh i hi)
    _ = (512 / 3) * L1 ^ 2 * (∑ i ∈ Q, dissipation L0 L1 g (run L0 L1 g s i)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (512 / 3) * L1 ^ 2 * energy f u s :=
      mul_le_mul_of_nonneg_left (hsub.trans hd) (by positivity)

omit [CompleteSpace E] in
lemma initial_first_down {g : E → E} {L0 L1 R Δ : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hΔ : 0 < Δ) (x0 : E) :
    let s := initialIterate L0 L1 R Δ x0 g
    localCurvature L0 L1 (g (coupling s)) = s.guess := by
  have he := coupling_same (R ^ 2 / (2 * Δ)) (localCurvature L0 L1 (g x0)) x0
    (by positivity) (localCurvature_pos hL0 hL1 _)
  simp only [initialIterate, he]

/-- A failed target accuracy bounds the accumulated weight using the common energy estimate. -/
lemma run_weight_le_of_inaccurate {f : E → ℝ} {g : E → E} {L0 L1 R ε : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (s : Iterate E) (u : E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hE : energy f u s ≤ R ^ 2) (hε : 0 < ε) (N : ℕ)
    (hfail : ε < f (run L0 L1 g s N).x - f u) :
    (run L0 L1 g s N).A ≤ R ^ 2 / ε := by
  have hweight := (run_valid (g := g) hL0 hL1 s hA hG N).1
  have hm := mul_le_mul_of_nonneg_left hfail.le hweight
  have he := run_energy hL0 hL1 hc hg hgd hH s u hA hG N
  have hsum : 0 ≤ ∑ k ∈ Finset.range N, dissipation L0 L1 g (run L0 L1 g s k) := by
    apply Finset.sum_nonneg
    intro k _
    have hv := run_valid (g := g) hL0 hL1 s hA hG k
    exact dissipation_nonneg hL0 hL1 _ hv.1 hv.2
  dsimp only [energy] at he hE
  apply (le_div_iff₀ hε).mpr
  linarith only [hm, he, hE, hsum, sq_nonneg ‖(run L0 L1 g s N).z - u‖]

end LongTails.OracleTemplate.GeneralizedAccelerated
