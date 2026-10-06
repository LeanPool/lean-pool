/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.LevelTransfer
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.MajorantArith
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.CompactOrderBound
public import LeanPool.CIVAxisymmetric.Statements.LocallyUniformlyAnalyticOn
public import LeanPool.CIVAxisymmetric.Reduction.AnalyticBoundOnMonotone

/-!
# Interior spatial analyticity of classical solutions

The proof of `thm:analytic:interior`. On nested regions of depth `τ ∈ (0, 1]` inside a
compactly contained cylinder, the weighted derivatives `(τ d)^k |∂^α g|` of the velocity
components and the pressure are bounded by the majorant `b_k ≤ M K^k k!`, by induction on `k`:
the one-step estimate on a backward window one geometric step deeper, the absorption of the
provisional top-order bound, and the majorant arithmetic. At depth `1` this is the bound
`AnalyticBoundOn u R' [s₁, s₂] M (d / K)`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Compactness gives a finite bound at each fixed derivative order. -/
theorem kahane_compact_order_bound {g : ParabolicPoint → ℝ} {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I))
    {Kc : Set (Vec3 × ℝ)} (hK : IsCompact Kc) (hKS : ∀ z ∈ Kc, z.1 ∈ Ω ∧ z.2 ∈ I) (k : ℕ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ z ∈ Kc, ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k →
      |multiPartial g γ z| ≤ N := by
  refine exists_bound_multiPartial_of_continuousOn hK (fun γ => ?_) k
  exact ((contDiffOn_multiPartial_spaceTimeSet hΩ hI hg γ).continuousOn).mono
    fun z hz => hKS z hz

/-- A finite bound at each fixed order for the velocity components and the pressure on the
closed outer region. -/
theorem kahane_region_bound {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet Ω I)) {R' d s₁ s₂ : ℝ}
    (hreg : ∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t → t ≤ s₂ →
      x ∈ Ω ∧ t ∈ I) (k : ℕ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t →
      t ≤ s₂ → ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k →
        (∀ i : Fin 3, |multiPartial (fun w => u w i) γ (x, t)| ≤ N) ∧
          |multiPartial p γ (x, t)| ≤ N := by
  set Kc : Set (Vec3 × ℝ) := {x : Vec3 | vec3EuclideanNorm x ≤ R' + d} ×ˢ Icc (s₁ - d ^ 2) s₂
    with hKc_def
  have hnorm : ∀ x : Vec3, ‖x‖ ≤ vec3EuclideanNorm x := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg x)).2 fun i => ?_
    rw [Real.norm_eq_abs, vec3EuclideanNorm]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
  have hKc : IsCompact Kc := by
    refine IsCompact.prod ?_ isCompact_Icc
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hcont : Continuous vec3EuclideanNorm := by
        unfold vec3EuclideanNorm
        fun_prop
      exact isClosed_le hcont continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Vec3)) (r := R' + d)).subset ?_
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hnorm x).trans hx
  have hKS : ∀ z ∈ Kc, z.1 ∈ Ω ∧ z.2 ∈ I := fun z hz => hreg z.1 z.2 hz.1 hz.2.1 hz.2.2
  have hu : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z i) (spaceTimeSet Ω I) :=
    fun i => contDiffOn_pi.1 hsol.1 i
  have hui : ∀ i : Fin 3, ∃ N : ℝ, 0 ≤ N ∧ ∀ z ∈ Kc, ∀ γ : Fin 3 → ℕ,
      γ 0 + γ 1 + γ 2 = k → |multiPartial (fun w => u w i) γ z| ≤ N :=
    fun i => kahane_compact_order_bound hΩ hI (hu i) hKc hKS k
  choose Nu hNu hbu using hui
  obtain ⟨Np, hNp, hp⟩ := kahane_compact_order_bound hΩ hI hsol.2.1 hKc hKS k
  have hsum : 0 ≤ ∑ i, Nu i := Finset.sum_nonneg fun i _ => hNu i
  refine ⟨∑ i, Nu i + Np, by positivity, fun x t hx ht₁ ht₂ γ hγ => ⟨fun i => ?_, ?_⟩⟩
  · have h1 := hbu i (x, t) ⟨hx, ht₁, ht₂⟩ γ hγ
    have h2 : Nu i ≤ ∑ j, Nu j :=
      Finset.single_le_sum (f := Nu) (fun j _ => hNu j) (Finset.mem_univ i)
    linarith only [h1, h2, hNp]
  · have := hp (x, t) ⟨hx, ht₁, ht₂⟩ γ hγ
    linarith only [this, hsum]

/-- The weighted bound at order `k + 1` from the weighted bounds at orders `≤ k`, by absorbing
the provisional bound (the compactness bound halves at each iteration). -/
theorem kahane_level_step : ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (Ω : Set Vec3) (I : Set ℝ) (R' d s₁ s₂ M K Mf af : ℝ) (k : ℕ),
    IsOpen Ω → IsOpen I → IsClassicalSolutionOn u p f (spaceTimeSet Ω I) →
    0 < d → d ≤ 1 → 1 ≤ M → 0 < af → 0 ≤ Mf → Mf * (1 + 3 / af) ≤ M →
    12800 * C ^ 2 * (1 + M) ≤ K → 1 / af ≤ K → 1 ≤ K → 1 ≤ k →
    (∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t → t ≤ s₂ →
      x ∈ Ω ∧ t ∈ I) →
    (∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, ∀ i : Fin 3,
        |multiPartial (fun w => f w i) γ (x, t)| ≤
          Mf * af ^ (-((γ 0 + γ 1 + γ 2 : ℕ) : ℝ)) * ((γ 0 + γ 1 + γ 2).factorial : ℝ)) →
    (∀ j ≤ k, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = j →
        (∀ i : Fin 3, (τ * d) ^ j * |multiPartial (fun w => u w i) γ (x, t)| ≤
          kahaneMajorant M K j) ∧
          (τ * d) ^ j * |multiPartial p γ (x, t)| ≤ kahaneMajorant M K j) →
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k + 1 →
        (∀ i : Fin 3, (τ * d) ^ (k + 1) * |multiPartial (fun w => u w i) γ (x, t)| ≤
          kahaneMajorant M K (k + 1)) ∧
          (τ * d) ^ (k + 1) * |multiPartial p γ (x, t)| ≤ kahaneMajorant M K (k + 1) := by
  obtain ⟨C, hC, hlvl⟩ := kahane_level_transfer
  refine ⟨C, hC, ?_⟩
  intro u p f Ω I R' d s₁ s₂ M K Mf af k hΩ hI hsol hd hd1 hM haf hMf hMfM hKC hKaf hK1 hk
    hreg hforce hlev
  set θ : ℝ := 1 / (400 * C * (1 + M)) with hθ_def
  have hCpos : 0 < C := by linarith only [hC]
  have hθpos : 0 < θ := by positivity
  have hθ4 : θ ≤ 1 / 4 := by
    rw [hθ_def, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hC, hM]
  set A : ℕ → ℝ := kahaneMajorant M K with hA_def
  set F : ℕ → ℝ := fun j => Mf * af ^ (-((j : ℕ) : ℝ)) * (j.factorial : ℝ) with hF_def
  have hA : ∀ j, 0 ≤ A j := by
    intro j
    rcases j with _ | j
    · simp only [hA_def, kahaneMajorant]
      linarith only [hM]
    · simp only [hA_def, kahaneMajorant]
      have : 0 ≤ M := by linarith only [hM]
      have : 0 ≤ K := by linarith only [hK1]
      positivity
  have hA0 : A 0 = M := rfl
  have hA1 : A 1 = M / 2 := by simp [hA_def, kahaneMajorant]
  set X : ℝ := C * (θ / (k + 1) * (F k + 3 * F (k + 1) +
      6 * ∑ m ∈ Finset.Icc 1 k, (k.choose m : ℝ) * (A m * A (k + 1 - m)) +
      18 * ∑ m ∈ Finset.Icc 1 (k - 1), (k.choose m : ℝ) * (A (m + 1) * A (k + 1 - m))) +
      2 * (k + 1) * A k / θ) with hX_def
  set ε : ℝ := C * θ * (2 + 6 * A 0 + 36 * A 1) / (k + 1) with hε_def
  have hFnn : ∀ j, 0 ≤ F j := fun j => by simp only [hF_def]; positivity
  have hX : 0 ≤ X := by
    have h1 : 0 ≤ ∑ m ∈ Finset.Icc 1 k, (k.choose m : ℝ) * (A m * A (k + 1 - m)) :=
      Finset.sum_nonneg fun m _ => by have := hA m; have := hA (k + 1 - m); positivity
    have h2 : 0 ≤ ∑ m ∈ Finset.Icc 1 (k - 1), (k.choose m : ℝ) * (A (m + 1) * A (k + 1 - m)) :=
      Finset.sum_nonneg fun m _ => by have := hA (m + 1); have := hA (k + 1 - m); positivity
    have := hFnn k
    have := hFnn (k + 1)
    have := hA k
    positivity
  have hε0 : 0 ≤ ε := by
    have := hA 0
    have := hA 1
    positivity
  have hε2 : ε ≤ 1 / 2 := by
    have hCθ : C * θ = 1 / (400 * (1 + M)) := by
      rw [hθ_def]
      field_simp
    rw [hε_def, hCθ, hA0, hA1]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith only [this]
    rw [div_le_iff₀ (by positivity)]
    have hM0 : 0 ≤ M := by linarith only [hM]
    have hkey : 1 / (400 * (1 + M)) * (2 + 6 * M + 36 * (M / 2)) ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hM0]
    have hpos : 0 ≤ 1 / (400 * (1 + M)) * (2 + 6 * M + 36 * (M / 2)) := by positivity
    nlinarith only [hkey, hk1, hpos]
  obtain ⟨Y₀, hY₀, hY₀b⟩ := kahane_region_bound hΩ hI hsol hreg (k + 1)
  have hforce' : ∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t →
      t ≤ s₂ → ∀ γ : Fin 3 → ℕ, ∀ i : Fin 3,
        |multiPartial (fun w => f w i) γ (x, t)| ≤ F (γ 0 + γ 1 + γ 2) := hforce
  have hin : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t →
      vec3EuclideanNorm x ≤ R' + d ∧ s₁ - d ^ 2 ≤ t := by
    intro τ hτ hτ1 x t hx ht₁
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    exact ⟨by nlinarith only [hx, hτ, hd], by nlinarith only [ht₁, hτ, hd2]⟩
  have hZ : ∀ n : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k + 1 →
        (∀ i : Fin 3, (τ * d) ^ (k + 1) * |multiPartial (fun w => u w i) γ (x, t)| ≤
          2 * X + Y₀ / 2 ^ n) ∧
          (τ * d) ^ (k + 1) * |multiPartial p γ (x, t)| ≤ 2 * X + Y₀ / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro τ hτ hτ1 x t hx ht₁ ht₂ γ hγ
      obtain ⟨hx', ht₁'⟩ := hin τ hτ hτ1 x t hx ht₁
      have hb := hY₀b x t hx' ht₁' ht₂ γ hγ
      have hτd : 0 ≤ τ * d := by positivity
      have hτd1 : τ * d ≤ 1 := by nlinarith only [hτ1, hd1, hτ, hd]
      have hpow : (τ * d) ^ (k + 1) ≤ 1 := pow_le_one₀ hτd hτd1
      have hpow0 : 0 ≤ (τ * d) ^ (k + 1) := pow_nonneg hτd _
      simp only [pow_zero, div_one]
      refine ⟨fun i => ?_, ?_⟩
      · have h1 := hb.1 i
        have hnn := abs_nonneg (multiPartial (fun w => u w i) γ (x, t))
        nlinarith only [h1, hnn, hpow, hpow0, hX]
      · have h1 := hb.2
        have hnn := abs_nonneg (multiPartial p γ (x, t))
        nlinarith only [h1, hnn, hpow, hpow0, hX]
    | succ n ih =>
      have hZn : 0 ≤ 2 * X + Y₀ / 2 ^ n := by positivity
      have hnext : X + ε * (2 * X + Y₀ / 2 ^ n) ≤ 2 * X + Y₀ / 2 ^ (n + 1) := by
        have h1 : ε * (2 * X + Y₀ / 2 ^ n) ≤ 1 / 2 * (2 * X + Y₀ / 2 ^ n) :=
          mul_le_mul_of_nonneg_right hε2 hZn
        have h2 : Y₀ / 2 ^ (n + 1) = 1 / 2 * (Y₀ / 2 ^ n) := by
          rw [pow_succ]
          field_simp
        rw [h2]
        linarith only [h1]
      intro τ hτ hτ1 x t hx ht₁ ht₂ γ hγ
      have hstep := hlvl u p f Ω I R' d s₁ s₂ θ (2 * X + Y₀ / 2 ^ n) k A F hΩ hI hsol hd hd1
        hθpos hθ4 hk hZn hA hreg hforce' hlev ih τ hτ hτ1 x t hx ht₁ ht₂ γ hγ
      exact ⟨fun i => (hstep.1 i).trans hnext, hstep.2.trans hnext⟩
  have harith := kahaneMajorant_step_le (C := C) (M := M) (K := K) (θ := θ) (Mf := Mf) (af := af)
    hC hM haf hMf hMfM rfl hKC hKaf hK1 hk
  have h2X : 2 * X ≤ kahaneMajorant M K (k + 1) := by
    simpa only [hX_def, hF_def, hA_def] using harith
  intro τ hτ hτ1 x t hx ht₁ ht₂ γ hγ
  refine ⟨fun i => ?_, ?_⟩
  · exact (le_of_forall_le_add_div_two_pow (Y₀ := Y₀)
      fun n => (hZ n τ hτ hτ1 x t hx ht₁ ht₂ γ hγ).1 i).trans h2X
  · exact (le_of_forall_le_add_div_two_pow (Y₀ := Y₀)
      fun n => (hZ n τ hτ hτ1 x t hx ht₁ ht₂ γ hγ).2).trans h2X

/-- The weighted bounds `(τ d)^k |∂^α g| ≤ b_k` at every depth `τ` and every order `k`, by
strong induction on the order. -/
theorem kahane_levels {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet Ω I)) {R' d s₁ s₂ Mf af : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (haf : 0 < af) (hMf : 0 ≤ Mf)
    (hreg : ∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t → t ≤ s₂ →
      x ∈ Ω ∧ t ∈ I)
    (hforce : ∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, ∀ i : Fin 3,
        |multiPartial (fun w => f w i) γ (x, t)| ≤
          Mf * af ^ (-((γ 0 + γ 1 + γ 2 : ℕ) : ℝ)) * ((γ 0 + γ 1 + γ 2).factorial : ℝ)) :
    ∃ M K : ℝ, 1 ≤ M ∧ 1 ≤ K ∧ ∀ k : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
      ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k →
        (∀ i : Fin 3, (τ * d) ^ k * |multiPartial (fun w => u w i) γ (x, t)| ≤
          kahaneMajorant M K k) ∧
          (τ * d) ^ k * |multiPartial p γ (x, t)| ≤ kahaneMajorant M K k := by
  obtain ⟨C, hC, hstep⟩ := kahane_level_step
  have hbase := kahane_region_bound hΩ hI hsol hreg
  obtain ⟨N0, hN0, h0⟩ := hbase 0
  obtain ⟨N1, hN1, h1⟩ := hbase 1
  set M : ℝ := max (max 1 N0) (max (2 * N1) (Mf * (1 + 3 / af))) with hM_def
  set K : ℝ := max (max (12800 * C ^ 2 * (1 + M)) (1 / af)) 1 with hK_def
  have hM1 : 1 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMN0 : N0 ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hMN1 : 2 * N1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMf' : Mf * (1 + 3 / af) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKC : 12800 * C ^ 2 * (1 + M) ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKaf : 1 / af ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨M, K, hM1, hK1, ?_⟩
  have hmemK : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ x : Vec3, ∀ t : ℝ,
      vec3EuclideanNorm x < R' + (1 - τ) * d → s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
      vec3EuclideanNorm x ≤ R' + d ∧ s₁ - d ^ 2 ≤ t ∧ t ≤ s₂ := by
    intro τ hτ hτ1 x t hx ht₁ ht₂
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    refine ⟨?_, ?_, ht₂⟩
    · nlinarith only [hx, hτ, hd]
    · nlinarith only [ht₁, hτ, hd2]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · intro τ hτ hτ1 x t hx ht₁ ht₂ γ hγ
      obtain ⟨hx', ht₁', ht₂'⟩ := hmemK τ hτ hτ1 x t hx ht₁ ht₂
      have hb := h0 x t hx' ht₁' ht₂' γ hγ
      simp only [pow_zero, one_mul, kahaneMajorant]
      exact ⟨fun i => (hb.1 i).trans hMN0, hb.2.trans hMN0⟩
    rcases k with _ | k
    · intro τ hτ hτ1 x t hx ht₁ ht₂ γ hγ
      obtain ⟨hx', ht₁', ht₂'⟩ := hmemK τ hτ hτ1 x t hx ht₁ ht₂
      have hb := h1 x t hx' ht₁' ht₂' γ hγ
      have hτd : 0 ≤ τ * d := by positivity
      have hτd1 : τ * d ≤ 1 := by nlinarith only [hτ1, hd1, hτ, hd]
      have hmaj : kahaneMajorant M K 1 = M / 2 := by
        simp [kahaneMajorant]
      rw [hmaj, pow_one]
      refine ⟨fun i => ?_, ?_⟩
      · have := hb.1 i
        have hnn := abs_nonneg (multiPartial (fun w => u w i) γ (x, t))
        nlinarith only [this, hnn, hτd, hτd1, hMN1]
      · have := hb.2
        have hnn := abs_nonneg (multiPartial p γ (x, t))
        nlinarith only [this, hnn, hτd, hτd1, hMN1]
    · exact hstep u p f Ω I R' d s₁ s₂ M K Mf af (k + 1) hΩ hI hsol hd hd1 hM1 haf hMf hMf'
        hKC hKaf hK1 (by omega) hreg hforce (fun j hj => ih j (by omega))

/-- The analyticity bound of `thm:analytic:interior` on one compactly contained cylinder. -/
theorem kahane_analyticBoundOn {R t₁ t₂ : ℝ} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 R) (Ioo t₁ t₂)))
    (hf : LocallyUniformlyAnalyticOn f R t₁ t₂) {R' : ℝ} (hR' : R' < R) {s₁ s₂ : ℝ}
    (hs₁ : t₁ < s₁) (hs₂ : s₂ < t₂) :
    ∃ M a : ℝ, 0 < a ∧ AnalyticBoundOn u R' (Icc s₁ s₂) M a := by
  set d : ℝ := min 1 (min ((R - R') / 3) ((s₁ - t₁) / 2)) with hd_def
  have hd : 0 < d := lt_min one_pos (lt_min (by linarith only [hR']) (by linarith only [hs₁]))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdR : d ≤ (R - R') / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hdt : d ≤ (s₁ - t₁) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hd2 : d ^ 2 ≤ d := by nlinarith only [hd, hd1]
  obtain ⟨Mf, af, haf, hMfb⟩ :=
    hf (R' + 2 * d) (by linarith only [hdR, hR']) (s₁ - d ^ 2) s₂
      (by linarith only [hd2, hdt, hs₁]) hs₂
  have hMfb' := analyticBoundOn_mono_const haf (le_max_left Mf 0) hMfb
  have hreg : ∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t → t ≤ s₂ →
      x ∈ vec3Ball 0 R ∧ t ∈ Ioo t₁ t₂ := by
    intro x t hx ht₁ ht₂
    refine ⟨?_, ?_, ?_⟩
    · show vec3EuclideanNorm (x - 0) < R
      rw [sub_zero]
      linarith only [hx, hdR, hR', hd]
    · linarith only [ht₁, hd2, hdt, hs₁, hd]
    · linarith only [ht₂, hs₂]
  have hforce : ∀ x : Vec3, ∀ t : ℝ, vec3EuclideanNorm x ≤ R' + d → s₁ - d ^ 2 ≤ t →
      t ≤ s₂ → ∀ γ : Fin 3 → ℕ, ∀ i : Fin 3,
        |multiPartial (fun w => f w i) γ (x, t)| ≤
          max Mf 0 * af ^ (-((γ 0 + γ 1 + γ 2 : ℕ) : ℝ)) *
            ((γ 0 + γ 1 + γ 2).factorial : ℝ) := by
    intro x t hx ht₁ ht₂ γ i
    refine hMfb' γ t ⟨ht₁, ht₂⟩ x ?_ i
    show vec3EuclideanNorm (x - 0) < R' + 2 * d
    rw [sub_zero]
    linarith only [hx, hd]
  obtain ⟨M, K, hM, hK, hlev⟩ := kahane_levels (isOpen_vec3Ball 0 R) isOpen_Ioo hsol hd hd1 haf
    (le_max_right Mf 0) hreg hforce
  refine ⟨M, d / K, div_pos hd (by linarith only [hK]), ?_⟩
  intro α t ht x hx i
  have hxn : vec3EuclideanNorm x < R' + (1 - 1) * d := by
    have : vec3EuclideanNorm (x - 0) < R' := hx
    rw [sub_zero] at this
    linarith only [this]
  have hb := (hlev (α 0 + α 1 + α 2) 1 one_pos le_rfl x t hxn
    (by linarith only [ht.1]) ht.2 α rfl).1 i
  have hmaj := kahaneMajorant_le (by linarith only [hM]) hK (α 0 + α 1 + α 2)
  set k : ℕ := α 0 + α 1 + α 2 with hk
  have hdk : 0 < d ^ k := pow_pos hd k
  have hKpos : 0 < K := by linarith only [hK]
  have hrpow : (d / K) ^ (-(k : ℝ)) = K ^ k / d ^ k := by
    rw [Real.rpow_neg (div_pos hd hKpos).le, Real.rpow_natCast, div_pow, inv_div]
  rw [hrpow]
  rw [one_mul] at hb
  have h1 : d ^ k * |multiPartial (fun w => u w i) α (x, t)| ≤ M * K ^ k * (k.factorial : ℝ) :=
    hb.trans hmaj
  rw [show M * (K ^ k / d ^ k) * (k.factorial : ℝ) = (M * K ^ k * (k.factorial : ℝ)) / d ^ k by
    ring]
  rw [le_div_iff₀ hdk]
  linarith only [h1]

/-- `thm:analytic:interior`: a classical solution of `eq:nse:forced` on `B(R) × (t₁, t₂)` with
a locally uniformly spatially analytic force is locally uniformly spatially analytic. -/
theorem kahane_interiorAnalyticity (R t₁ t₂ : ℝ) (hR : 0 < R) (ht : t₁ < t₂)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 R) (Ioo t₁ t₂)))
    (hf : LocallyUniformlyAnalyticOn f R t₁ t₂) :
    LocallyUniformlyAnalyticOn u R t₁ t₂ := by
  -- the positivity of the radius and of the time interval are not needed by this route
  have _hRpos : 0 < R := hR
  have _htlt : t₁ < t₂ := ht
  intro R' hR' s₁ s₂ hs₁ hs₂
  exact kahane_analyticBoundOn hsol hf hR' hs₁ hs₂

end CIV
