/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection.Defs
import LeanPool.PLAcceleratedNesterovLean.Convergence.Bootstrap.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.Bootstrap.Step2

/-!
# Bootstrap via Total Displacement Control

Starting from a sufficiently small neighborhood of m⋆ with zero initial velocity,
all iterates remain in the controlled region Ω and the Lyapunov function
decays geometrically.
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold

/-- `√(c ^ m) = (√c) ^ m` for `0 ≤ c`. -/
private theorem sqrt_pow_eq_pow_sqrt {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    Real.sqrt (c ^ m) = Real.sqrt c ^ m := by
  induction m with
  | zero => simp only [pow_zero, Real.sqrt_one]
  | succ k ihk => rw [pow_succ, Real.sqrt_mul (pow_nonneg hc k), ihk, pow_succ]

/-- The contraction factor `c = 1 - (1 - θ)·√(μ'η)` satisfies `0 ≤ c ≤ 1` and `√c < 1`. -/
private theorem contraction_factor_bounds {μ' η θ : ℝ} (hμ' : 0 < μ') (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1) :
    0 ≤ 1 - (1 - θ) * Real.sqrt (μ' * η) ∧ 1 - (1 - θ) * Real.sqrt (μ' * η) ≤ 1 ∧
      Real.sqrt (1 - (1 - θ) * Real.sqrt (μ' * η)) < 1 := by
  have hμη_pos : 0 < μ' * η := mul_pos hμ' hη_pos
  have ha_pos : 0 < Real.sqrt (μ' * η) := Real.sqrt_pos_of_pos hμη_pos
  have ha_lt1 : Real.sqrt (μ' * η) < 1 := by
    calc Real.sqrt (μ' * η) < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt hμη_pos) hμη_lt1
      _ = 1 := Real.sqrt_one
  have hc_pos : 0 < 1 - (1 - θ) * Real.sqrt (μ' * η) := by
    nlinarith [mul_pos (sub_pos.mpr hθ_lt1) ha_pos]
  have hc_lt1 : 1 - (1 - θ) * Real.sqrt (μ' * η) < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hθ_lt1) ha_pos]
  refine ⟨le_of_lt hc_pos, le_of_lt hc_lt1, ?_⟩
  calc Real.sqrt (1 - (1 - θ) * Real.sqrt (μ' * η)) < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt (le_of_lt hc_pos) hc_lt1
    _ = 1 := Real.sqrt_one

/-- Triangle inequality for a translated point: `dist (y + h) m ≤ dist y m + ‖h‖`. -/
private theorem dist_add_le_dist_add_norm {d : ℕ} (y h m : E d) :
    dist (y + h) m ≤ dist y m + ‖h‖ := by
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖y + h - m‖ = ‖(y - m) + h‖ := by congr 1; abel
    _ ≤ ‖y - m‖ + ‖h‖ := norm_add_le _ _

/-- Triangle inequality for a translated point: `dist (y - v) m ≤ dist y m + ‖v‖`. -/
private theorem dist_sub_le_dist_add_norm {d : ℕ} (y v m : E d) :
    dist (y - v) m ≤ dist y m + ‖v‖ := by
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖y - v - m‖ = ‖(y - m) - v‖ := by congr 1; abel
    _ ≤ ‖y - m‖ + ‖v‖ := norm_sub_le _ _

/-- A geometric partial sum of displacements is bounded by `A·√L₀/(1-√c)`. -/
private theorem geometric_displacement_le {A L₀ c r : ℝ} (hA : 0 ≤ A)
    (hsqrt_c_lt1 : Real.sqrt c < 1)
    (hdisp : A * Real.sqrt L₀ / (1 - Real.sqrt c) ≤ r / 4) (n : ℕ) :
    A * Real.sqrt L₀ * (Finset.range n).sum (fun k => Real.sqrt c ^ k) ≤ r / 4 := by
  have hle := partial_geom_series_bound (Real.sqrt c) (Real.sqrt_nonneg c) hsqrt_c_lt1 n
  calc A * Real.sqrt L₀ * (Finset.range n).sum (fun k => Real.sqrt c ^ k)
      ≤ A * Real.sqrt L₀ * (1 / (1 - Real.sqrt c)) :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg hA (Real.sqrt_nonneg _))
    _ = A * Real.sqrt L₀ / (1 - Real.sqrt c) := by ring
    _ ≤ r / 4 := hdisp

/-- **Abstract displacement induction** behind both bootstrap theorems.

Let `X n` be the iterates, `Y n` the look-ahead points with steps `Y (n + 1) = Y n + H n`,
and `X n = Y n - V n`. If, while both stay in `Ω` with Lyapunov value `Lf n ≤ R²`, the
Lyapunov value contracts by `c` and the steps `H n`, `V (n + 1)` are controlled by `√(Lf n)`,
then a start close enough to `m_star` keeps every iterate in `ball m_star r ⊆ Ω` and
`Lf n ≤ c ^ n · Lf 0`. -/
private theorem bootstrap_displacement_induction {d : ℕ}
    (X Y H V : ℕ → E d) (Lf : ℕ → ℝ) (Ω : Set (E d)) (m_star : E d)
    (r R c A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) (hsqrt_c_lt1 : Real.sqrt c < 1)
    (hball_Ω : Metric.ball m_star r ⊆ Ω)
    (hY_step : ∀ n, Y (n + 1) = Y n + H n) (hX_eq : ∀ n, X n = Y n - V n)
    (hcontract : ∀ n, X n ∈ Ω → Y n ∈ Ω → Lf n ≤ R ^ 2 → Lf (n + 1) ≤ c * Lf n)
    (hH : ∀ n, X n ∈ Ω → Y n ∈ Ω → Lf n ≤ R ^ 2 → ‖H n‖ ≤ A * Real.sqrt (Lf n))
    (hV : ∀ n, X n ∈ Ω → Y n ∈ Ω → Lf n ≤ R ^ 2 → ‖V (n + 1)‖ ≤ B * Real.sqrt (Lf n))
    (hX0 : dist (X 0) m_star < r / 4) (hY0 : dist (Y 0) m_star < r / 4)
    (hL0_R : Lf 0 ≤ R ^ 2) (hL0_nonneg : 0 ≤ Lf 0)
    (hdisp : A * Real.sqrt (Lf 0) / (1 - Real.sqrt c) ≤ r / 4)
    (hvel : B * Real.sqrt (Lf 0) ≤ r / 4) (n : ℕ) :
    (X n ∈ Ω ∧ Y n ∈ Ω) ∧ (dist (X n) m_star < r ∧ dist (Y n) m_star < r) ∧
      Lf n ≤ c ^ n * Lf 0 := by
  have hr_pos : 0 < r := by linarith [dist_nonneg (x := X 0) (y := m_star)]
  -- While the displacement-sum bound holds, the look-ahead stays within `r / 2` of `m_star`.
  have hY_half : ∀ k, dist (Y k) m_star ≤ dist (Y 0) m_star + A * Real.sqrt (Lf 0) *
      (Finset.range k).sum (fun j => Real.sqrt c ^ j) → dist (Y k) m_star < r / 2 := by
    intro k hk
    linarith [geometric_displacement_le hA hsqrt_c_lt1 hdisp k]
  have hinv : ∀ n, dist (X n) m_star < r ∧ Lf n ≤ c ^ n * Lf 0 ∧
      dist (Y n) m_star ≤ dist (Y 0) m_star + A * Real.sqrt (Lf 0) *
        (Finset.range n).sum (fun k => Real.sqrt c ^ k) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by linarith, by simp only [pow_zero, one_mul, le_refl], ?_⟩
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, le_refl]
    | succ n ih =>
      obtain ⟨hXn, hLn, hYn⟩ := ih
      have hXn_Ω : X n ∈ Ω := hball_Ω (Metric.mem_ball.mpr hXn)
      have hYn_Ω : Y n ∈ Ω := hball_Ω (Metric.mem_ball.mpr (by linarith [hY_half n hYn]))
      have hLn_le : Lf n ≤ Lf 0 := by
        have := mul_le_of_le_one_left hL0_nonneg (pow_le_one₀ hc_nonneg hc_le_one (n := n))
        linarith
      have hLn_R : Lf n ≤ R ^ 2 := le_trans hLn_le hL0_R
      have hsqrt_Ln : Real.sqrt (Lf n) ≤ Real.sqrt c ^ n * Real.sqrt (Lf 0) := by
        calc Real.sqrt (Lf n) ≤ Real.sqrt (c ^ n * Lf 0) := Real.sqrt_le_sqrt hLn
          _ = Real.sqrt c ^ n * Real.sqrt (Lf 0) := by
              rw [Real.sqrt_mul (pow_nonneg hc_nonneg n), sqrt_pow_eq_pow_sqrt hc_nonneg]
      have hH_geom : ‖H n‖ ≤ A * Real.sqrt (Lf 0) * Real.sqrt c ^ n := by
        calc ‖H n‖ ≤ A * Real.sqrt (Lf n) := hH n hXn_Ω hYn_Ω hLn_R
          _ ≤ A * (Real.sqrt c ^ n * Real.sqrt (Lf 0)) :=
              mul_le_mul_of_nonneg_left hsqrt_Ln hA
          _ = A * Real.sqrt (Lf 0) * Real.sqrt c ^ n := by ring
      have hYn1 : dist (Y (n + 1)) m_star ≤ dist (Y 0) m_star + A * Real.sqrt (Lf 0) *
          (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) := by
        calc dist (Y (n + 1)) m_star ≤ dist (Y n) m_star + ‖H n‖ := by
              rw [hY_step n]; exact dist_add_le_dist_add_norm _ _ _
          _ ≤ (dist (Y 0) m_star + A * Real.sqrt (Lf 0) *
                (Finset.range n).sum (fun k => Real.sqrt c ^ k)) +
              A * Real.sqrt (Lf 0) * Real.sqrt c ^ n := by linarith
          _ = dist (Y 0) m_star + A * Real.sqrt (Lf 0) *
                (Finset.range (n + 1)).sum (fun k => Real.sqrt c ^ k) := by
              rw [Finset.sum_range_succ]; ring
      have hV_small : ‖V (n + 1)‖ ≤ r / 4 := by
        calc ‖V (n + 1)‖ ≤ B * Real.sqrt (Lf n) := hV n hXn_Ω hYn_Ω hLn_R
          _ ≤ B * Real.sqrt (Lf 0) :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLn_le) hB
          _ ≤ r / 4 := hvel
      refine ⟨?_, ?_, hYn1⟩
      · calc dist (X (n + 1)) m_star ≤ dist (Y (n + 1)) m_star + ‖V (n + 1)‖ := by
              rw [hX_eq (n + 1)]; exact dist_sub_le_dist_add_norm _ _ _
          _ < r := by linarith [hY_half (n + 1) hYn1]
      · calc Lf (n + 1) ≤ c * Lf n := hcontract n hXn_Ω hYn_Ω hLn_R
          _ ≤ c * (c ^ n * Lf 0) := mul_le_mul_of_nonneg_left hLn hc_nonneg
          _ = c ^ (n + 1) * Lf 0 := by ring
  obtain ⟨hXn, hLn, hYn⟩ := hinv n
  have hYn_lt : dist (Y n) m_star < r := by linarith [hY_half n hYn]
  exact ⟨⟨hball_Ω (Metric.mem_ball.mpr hXn), hball_Ω (Metric.mem_ball.mpr hYn_lt)⟩,
    ⟨hXn, hYn_lt⟩, hLn⟩

/-- **Bootstrap via total displacement control.**

There exists α > 0 such that for Ubar_{m⋆} = B(m⋆, α) ∩ U and every start point in
Ubar_{m⋆} with zero initial velocity:
  (1) x_n, x'_n ∈ Ω for every Lean index n
  (2) All iterates remain in U
  (3) L_n ≤ (1 - (1-θ)·a)^n · L_0

The budget-split parameter θ ∈ (0,1) is inherited from the contraction hypothesis.
-/
private theorem bootstrapTotalDisplacementProof
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ) (_hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Tubular neighborhood U
    (U : Set (E d))
    (_hTub : IsTubularNeighborhoodOfSubmanifold S U)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_in_S : ∀ x, π x ∈ S)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    (hπ_metric : ∀ x ∈ U, dist x (π x) = Metric.infDist x S)
    -- Tangent projector P
    (P : E d →L[ℝ] E d)
    -- Neighborhoods from `lyapunov_contraction`: Ω ⊂⊂ Ω⁺ ⊂⊂ U₊ ⊂ U
    (Ω : Set (E d)) (hΩ_open : IsOpen Ω) (hΩ_sub_U : Ω ⊆ U)
    -- R from `lyapunov_contraction`
    (R : ℝ) (hR : 0 < R)
    -- Base point
    (m_star : E d) (hm_star : m_star ∈ S) (hm_star_Ω : m_star ∈ Ω)
    -- Ψ continuity and vanishing at m⋆
    (hΨ_cont : ContinuousAt (psi f μ' S) m_star)
    (hΨ_zero : psi f μ' S m_star = 0)
    -- Quadratic growth (from `local_fiberwise_geometry`)
    (_hQG : ∀ x ∈ Ω, f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2)
    -- Lyapunov contraction (from `lyapunov_contraction`): whenever in Ω with L_n ≤ R²
    (hcontract : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let Ln := lyapunov P μ' π f η ρ x₁ n
      let Ln' := lyapunov P μ' π f η ρ x₁ (n + 1)
      let a := Real.sqrt (μ' * η)
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      Ln' ≤ (1 - (1 - θ) * a) * Ln)
    -- Motion bound on h_n (from `motion_bounds_curvature_error`)
    (C_h : ℝ) (hC_h : 0 < C_h)
    (hstep_bound : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let Ln := lyapunov P μ' π f η ρ x₁ n
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      ‖nesterovH f η ρ x₁ n‖ ≤ C_h * Real.sqrt η * Real.sqrt Ln)
    -- Motion bound on velocity (from `motion_bounds_curvature_error`)
    (C_mov : ℝ) (hC_mov : 0 < C_mov)
    (hvel_bound : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let s' := nesterovSeq f η ρ x₁ (n + 1)
      let Ln := lyapunov P μ' π f η ρ x₁ n
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      ‖Real.sqrt η • s'.v‖ ≤ C_mov * Real.sqrt Ln) :
    -- Conclusion: ∃ α > 0 with the bootstrap property
    ∃ (α : ℝ), 0 < α ∧
      ∀ x₁ ∈ Metric.ball m_star α ∩ U,
        -- (1) All iterates stay in Ω
        (∀ n : ℕ,
          (nesterovSeq f η ρ x₁ n).x ∈ Ω ∧
          (nesterovSeq f η ρ x₁ n).lookahead η ∈ Ω) ∧
        -- (2) All iterates remain in U
        (∀ n : ℕ, (nesterovSeq f η ρ x₁ n).x ∈ U) ∧
        -- (3) Geometric decay of Lyapunov function
        (∀ n : ℕ,
          let a := Real.sqrt (μ' * η)
          lyapunov P μ' π f η ρ x₁ (n + 1) ≤
            (1 - (1 - θ) * a) ^ (n + 1) * lyapunov P μ' π f η ρ x₁ 0) := by
  -- ── Contraction rate and auxiliary constants ────────────────────────────
  obtain ⟨hc_nonneg, hc_le_one, hsqrt_c_lt1⟩ :=
    contraction_factor_bounds hμ' hη_pos hμη_lt1 hθ_pos hθ_lt1
  set a := Real.sqrt (μ' * η) with ha_def
  set c := 1 - (1 - θ) * a with hc_def
  have h1_sub_sqrt_c_pos : (0 : ℝ) < 1 - Real.sqrt c := by linarith
  -- ── Step 1: Get r from Ω being open at m⋆ ──────────────────────────────
  obtain ⟨r, hr_pos, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ_open m_star hm_star_Ω
  -- ── Step 2: Displacement bound constant ─────────────────────────────────
  -- K = C_h·√η/(1-√c) + C_mov bounds total displacement per unit √L₀.
  -- We need K·√(L₀) < r/2 so that both x' and x iterates stay in ball(m⋆,r).
  set K := C_h * Real.sqrt η / (1 - Real.sqrt c) + C_mov with hK_def
  have hK_pos : (0 : ℝ) < K := by positivity
  -- ── Step 3: Choose T so that Ψ(x₁) < T² with T ≤ R and K·T < r/2 ─────
  set T := min R (r / (4 * K)) with hT_def
  have hT_pos : (0 : ℝ) < T := lt_min hR (by positivity)
  -- ── Step 4: Get α₁ so that Ψ(x) < T² in B(m⋆, α₁) ────────────────────
  obtain ⟨α₁, hα₁_pos, hα₁_small⟩ := exists_alpha_psi_small m_star (psi f μ' S)
    hΨ_cont hΨ_zero T hT_pos
  -- ── Step 5: Set α = min(α₁, r/4) ───────────────────────────────────────
  set α := min α₁ (r / 4) with hα_def
  refine ⟨α, lt_min hα₁_pos (by linarith), fun x₁ hx₁ => ?_⟩
  -- ── Base‑case setup ─────────────────────────────────────────────────────
  have hx₁_ball : x₁ ∈ Metric.ball m_star α₁ :=
    Metric.ball_subset_ball (min_le_left α₁ (r / 4)) hx₁.1
  have hx₁_dist : dist x₁ m_star < r / 4 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hx₁.1) (min_le_right α₁ (r / 4))
  have hx₁_Ω : x₁ ∈ Ω := by
    apply hball_Ω; exact Metric.mem_ball.mpr (by linarith)
  have hx₁_U : x₁ ∈ U := hx₁.2
  -- Ψ(x₁) < T²
  have hΨ_small : psi f μ' S x₁ < T ^ 2 :=
    hα₁_small x₁ (Metric.mem_ball.mp hx₁_ball)
  set L := fun n => lyapunov P μ' π f η ρ x₁ n with hL_def
  -- L 0 ≤ Ψ(x₁) (when v₁ = 0, the kinetic term vanishes)
  have hL0_le_Ψ : L 0 ≤ psi f μ' S x₁ := by
    change lyapunov P μ' π f η ρ x₁ 0 ≤ psi f μ' S x₁
    simp only [lyapunov, nesterovSeq, auxVar, normalDisp, NesterovState.lookahead,
      map_zero, smul_zero, sub_self, zero_add, add_zero, norm_zero, psi]
    have hπ_dist : dist x₁ (π x₁) = Metric.infDist x₁ S :=
      hπ_metric x₁ (hΩ_sub_U hx₁_Ω)
    rw [dist_eq_norm] at hπ_dist
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg μ')]
    rw [mul_pow, Real.sq_sqrt (le_of_lt hμ'), hπ_dist]
    linarith [sq_nonneg ((1 + Real.sqrt (μ' * η)) ^ 2 / (2 * (1 - Real.sqrt (μ' * η))))]
  -- L 0 ≤ T² ≤ R²
  have hL0_le_T2 : L 0 ≤ T ^ 2 := le_of_lt (lt_of_le_of_lt hL0_le_Ψ hΨ_small)
  have hT_le_R : T ≤ R := min_le_left R _
  have hL0_bound : L 0 ≤ R ^ 2 := le_trans hL0_le_T2 (by nlinarith)
  -- L 0 ≥ 0
  have hL0_nonneg : (0 : ℝ) ≤ L 0 := by
    have hmin : ∀ y, f m_star ≤ f y := by
      have : m_star ∈ argminSet f := by rw [← hM_argmin]; exact hm_star
      exact this
    have hbdd : BddBelow (Set.range f) :=
      ⟨f m_star, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
    have h1 : 0 ≤ f x₁ - fStar f := sub_nonneg.mpr (ciInf_le hbdd x₁)
    change 0 ≤ lyapunov P μ' π f η ρ x₁ 0
    simp only [lyapunov, nesterovSeq, auxVar, normalDisp, NesterovState.lookahead,
      map_zero, smul_zero, sub_self, zero_add, add_zero, norm_zero]
    linarith [sq_nonneg ‖Real.sqrt μ' • (x₁ - π x₁)‖]
  -- Key bound: √(L 0) ≤ T
  have hsqrt_L0_le_T : Real.sqrt (L 0) ≤ T := by
    calc Real.sqrt (L 0) ≤ Real.sqrt (T ^ 2) := Real.sqrt_le_sqrt hL0_le_T2
      _ = T := Real.sqrt_sq (le_of_lt hT_pos)
  -- Key bound: K · √(L 0) ≤ r / 4  (since K·T ≤ K·r/(4K) = r/4)
  have hKL0 : K * Real.sqrt (L 0) ≤ r / 4 := by
    calc K * Real.sqrt (L 0)
        ≤ K * T := by apply mul_le_mul_of_nonneg_left hsqrt_L0_le_T (le_of_lt hK_pos)
      _ ≤ K * (r / (4 * K)) := by
          apply mul_le_mul_of_nonneg_left (min_le_right R _) (le_of_lt hK_pos)
      _ = r / 4 := by field_simp
  -- Displacement component: C_h·√η·√(L 0)/(1-√c) ≤ r/4
  have hdisp_bound : C_h * Real.sqrt η * Real.sqrt (L 0) / (1 - Real.sqrt c) ≤ r / 4 := by
    have : C_h * Real.sqrt η / (1 - Real.sqrt c) ≤ K :=
      le_add_of_nonneg_right (le_of_lt hC_mov)
    calc C_h * Real.sqrt η * Real.sqrt (L 0) / (1 - Real.sqrt c)
        = C_h * Real.sqrt η / (1 - Real.sqrt c) * Real.sqrt (L 0) := by ring
      _ ≤ K * Real.sqrt (L 0) := by
          apply mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ ≤ r / 4 := hKL0
  -- Velocity component: C_mov · √(L 0) ≤ r/4
  have hvel_comp : C_mov * Real.sqrt (L 0) ≤ r / 4 := by
    have : C_mov ≤ K := le_add_of_nonneg_left (by positivity)
    calc C_mov * Real.sqrt (L 0) ≤ K * Real.sqrt (L 0) :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ ≤ r / 4 := hKL0
  -- ── Main induction (abstract displacement argument) ───────────────────
  have hmain := bootstrap_displacement_induction
    (fun n => (nesterovSeq f η ρ x₁ n).x) (fun n => (nesterovSeq f η ρ x₁ n).lookahead η)
    (nesterovH f η ρ x₁) (fun n => Real.sqrt η • (nesterovSeq f η ρ x₁ n).v) L Ω m_star
    r R c (C_h * Real.sqrt η) C_mov (by positivity) hC_mov.le hc_nonneg hc_le_one hsqrt_c_lt1
    hball_Ω
    (fun n => by
      have hH_def : nesterovH f η ρ x₁ n = (nesterovSeq f η ρ x₁ (n + 1)).lookahead η -
          (nesterovSeq f η ρ x₁ n).lookahead η := rfl
      rw [hH_def]; abel)
    (fun n => by simp only [NesterovState.lookahead, add_sub_cancel_right])
    (fun n h₁ h₂ h₃ => hcontract x₁ n h₁ h₂ h₃) (fun n h₁ h₂ h₃ => hstep_bound x₁ n h₁ h₂ h₃)
    (fun n h₁ h₂ h₃ => hvel_bound x₁ n h₁ h₂ h₃) hx₁_dist
    (by simp only [NesterovState.lookahead, nesterovSeq, smul_zero, add_zero]; exact hx₁_dist)
    hL0_bound hL0_nonneg hdisp_bound hvel_comp
  exact ⟨fun n => (hmain n).1, fun n => hΩ_sub_U (hmain n).1.1, fun n => (hmain (n + 1)).2.2⟩


/-- **Generalized bootstrap via total displacement control.**

For any state s₀ near m⋆ with sufficiently small Lyapunov value,
all iterates of `nesterovSeqGen` stay in the controlled region Ω and the
Lyapunov function decays geometrically.

Generalization of `bootstrap_total_displacement` supporting nonzero initial velocity,
which is essential for the Nesterov algorithm where velocity carries across
iterations.
-/
private theorem bootstrapTotalDisplacementGenProof
    {d : ℕ}
    (f : E d → ℝ)
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ)
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    (π : E d → E d)
    (P : E d →L[ℝ] E d)
    (Ω : Set (E d)) (hΩ_open : IsOpen Ω)
    (R : ℝ) (hR : 0 < R)
    (m_star : E d) (hm_star : m_star ∈ S) (hm_star_Ω : m_star ∈ Ω)
    -- Contraction (from lyapunov_contraction_gen)
    (hcontract : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
        (1 - (1 - θ) * Real.sqrt (μ' * η)) *
        lyapunovOfState P μ' π f η s)
    -- Step displacement bound
    (C_h : ℝ) (hC_h : 0 < C_h)
    (hstep_bound : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      ‖stepDispOfState f η ρ s‖ ≤
        C_h * Real.sqrt η *
        Real.sqrt (lyapunovOfState P μ' π f η s))
    -- Velocity bound
    (C_mov : ℝ) (hC_mov : 0 < C_mov)
    (hvel_bound : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ ≤
        C_mov * Real.sqrt (lyapunovOfState P μ' π f η s)) :
    ∃ (δ r_ball : ℝ), 0 < δ ∧ 0 < r_ball ∧
      Metric.ball m_star r_ball ⊆ Ω ∧
      ∀ s₀ : NesterovState d,
        s₀.x ∈ Metric.ball m_star δ →
        s₀.lookahead η ∈ Metric.ball m_star δ →
        lyapunovOfState P μ' π f η s₀ ≤ δ ^ 2 →
        -- (1) All iterates stay in Ω
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Ω ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Ω) ∧
        -- (2) Ball containment: iterates stay in ball(m_star, r_ball)
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball m_star r_ball ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball m_star r_ball) ∧
        -- (3) Geometric decay
        (∀ n : ℕ,
          let a := Real.sqrt (μ' * η)
          lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
            (1 - (1 - θ) * a) ^ (n + 1) *
            lyapunovOfState P μ' π f η s₀) := by
  -- ── Contraction rate and auxiliary constants ────────────────────────────
  obtain ⟨hc_nonneg, hc_le_one, hsqrt_c_lt1⟩ :=
    contraction_factor_bounds hμ' hη_pos hμη_lt1 hθ_pos hθ_lt1
  set a := Real.sqrt (μ' * η) with ha_def
  set c := 1 - (1 - θ) * a with hc_def
  have h1_sub_sqrt_c_pos : (0 : ℝ) < 1 - Real.sqrt c := by linarith
  -- ── Step 1: Get r from Ω being open at m⋆ ──────────────────────────────
  obtain ⟨r, hr_pos, hball_Ω⟩ := Metric.isOpen_iff.mp hΩ_open m_star hm_star_Ω
  -- ── Step 2: Displacement bound constant ─────────────────────────────────
  set K := C_h * Real.sqrt η / (1 - Real.sqrt c) + C_mov with hK_def
  have hK_pos : (0 : ℝ) < K := by positivity
  -- ── Step 3: Choose δ so that iterates stay within ball(m⋆, r) ⊆ Ω ──────
  set δ := min R (min (r / 4) (r / (4 * K))) with hδ_def
  have hδ_pos : (0 : ℝ) < δ := by
    apply lt_min hR; apply lt_min (by linarith) (by positivity)
  have hδ_le_R : δ ≤ R := min_le_left R _
  have hδ_le_r4 : δ ≤ r / 4 := le_trans (min_le_right R _) (min_le_left _ _)
  have hδ_le_rK : δ ≤ r / (4 * K) := le_trans (min_le_right R _) (min_le_right _ _)
  refine ⟨δ, r, hδ_pos, hr_pos, hball_Ω, fun s₀ hs₀_x hs₀_la hL₀_small => ?_⟩
  -- ── Starting state bounds ───────────────────────────────────────────────
  have hs₀_x_dist : dist s₀.x m_star < r / 4 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hs₀_x) hδ_le_r4
  have hs₀_la_dist : dist (s₀.lookahead η) m_star < r / 4 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hs₀_la) hδ_le_r4
  -- L₀ ≤ R²
  have hL₀_R : lyapunovOfState P μ' π f η s₀ ≤ R ^ 2 :=
    le_trans hL₀_small (by nlinarith [hδ_le_R])
  -- L₀ ≥ 0
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨f m_star, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hM_argmin ▸ hm_star : m_star ∈ argminSet f) x
  set L₀ := lyapunovOfState P μ' π f η s₀ with hL₀_def
  have hL₀_nonneg : 0 ≤ L₀ :=
    lyapunovOfState_nonneg P μ' π f η s₀ hμ' hη_pos hμη_lt1 hbdd
  -- √L₀ ≤ δ
  have hsqrt_L₀_le_δ : Real.sqrt L₀ ≤ δ := by
    calc Real.sqrt L₀ ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hL₀_small
      _ = δ := Real.sqrt_sq (le_of_lt hδ_pos)
  -- K · √L₀ ≤ r/4
  have hKL₀ : K * Real.sqrt L₀ ≤ r / 4 := by
    calc K * Real.sqrt L₀
        ≤ K * δ := mul_le_mul_of_nonneg_left hsqrt_L₀_le_δ (le_of_lt hK_pos)
      _ ≤ K * (r / (4 * K)) := mul_le_mul_of_nonneg_left hδ_le_rK (le_of_lt hK_pos)
      _ = r / 4 := by field_simp
  -- C_h·√η·√L₀/(1-√c) ≤ r/4
  have hdisp_bound : C_h * Real.sqrt η * Real.sqrt L₀ / (1 - Real.sqrt c) ≤ r / 4 := by
    have : C_h * Real.sqrt η / (1 - Real.sqrt c) ≤ K :=
      le_add_of_nonneg_right (le_of_lt hC_mov)
    calc C_h * Real.sqrt η * Real.sqrt L₀ / (1 - Real.sqrt c)
        = C_h * Real.sqrt η / (1 - Real.sqrt c) * Real.sqrt L₀ := by ring
      _ ≤ K * Real.sqrt L₀ :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ ≤ r / 4 := hKL₀
  -- C_mov · √L₀ ≤ r/4
  have hvel_comp : C_mov * Real.sqrt L₀ ≤ r / 4 := by
    have : C_mov ≤ K := le_add_of_nonneg_left (by positivity)
    calc C_mov * Real.sqrt L₀ ≤ K * Real.sqrt L₀ :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ ≤ r / 4 := hKL₀
  -- ── Main induction (abstract displacement argument) ───────────────────
  set Ln := fun n => lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ n) with hLn_def
  have hmain := bootstrap_displacement_induction
    (fun n => (nesterovSeqGen f η ρ s₀ n).x) (fun n => (nesterovSeqGen f η ρ s₀ n).lookahead η)
    (fun n => stepDispOfState f η ρ (nesterovSeqGen f η ρ s₀ n))
    (fun n => Real.sqrt η • (nesterovSeqGen f η ρ s₀ n).v) Ln Ω m_star
    r R c (C_h * Real.sqrt η) C_mov (by positivity) hC_mov.le hc_nonneg hc_le_one hsqrt_c_lt1
    hball_Ω (fun n => by simp only [stepDispOfState, nesterovSeqGen]; abel)
    (fun n => by simp only [NesterovState.lookahead, add_sub_cancel_right])
    (fun n h₁ h₂ h₃ => hcontract s₀ n h₁ h₂ h₃) (fun n h₁ h₂ h₃ => hstep_bound s₀ n h₁ h₂ h₃)
    (fun n h₁ h₂ h₃ => hvel_bound s₀ n h₁ h₂ h₃) hs₀_x_dist hs₀_la_dist
    hL₀_R hL₀_nonneg hdisp_bound hvel_comp
  exact ⟨fun n => (hmain n).1, fun n => (hmain n).2.1, fun n => (hmain (n + 1)).2.2⟩


/-- Public theorem wrapper for `bootstrapTotalDisplacementProof`. -/
theorem bootstrap_total_displacement
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ) (_hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Tubular neighborhood U
    (U : Set (E d))
    (_hTub : IsTubularNeighborhoodOfSubmanifold S U)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_in_S : ∀ x, π x ∈ S)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    (hπ_metric : ∀ x ∈ U, dist x (π x) = Metric.infDist x S)
    -- Tangent projector P
    (P : E d →L[ℝ] E d)
    -- Neighborhoods from `lyapunov_contraction`: Ω ⊂⊂ Ω⁺ ⊂⊂ U₊ ⊂ U
    (Ω : Set (E d)) (hΩ_open : IsOpen Ω) (hΩ_sub_U : Ω ⊆ U)
    -- R from `lyapunov_contraction`
    (R : ℝ) (hR : 0 < R)
    -- Base point
    (m_star : E d) (hm_star : m_star ∈ S) (hm_star_Ω : m_star ∈ Ω)
    -- Ψ continuity and vanishing at m⋆
    (hΨ_cont : ContinuousAt (psi f μ' S) m_star)
    (hΨ_zero : psi f μ' S m_star = 0)
    -- Quadratic growth (from `local_fiberwise_geometry`)
    (_hQG : ∀ x ∈ Ω, f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2)
    -- Lyapunov contraction (from `lyapunov_contraction`): whenever in Ω with L_n ≤ R²
    (hcontract : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let Ln := lyapunov P μ' π f η ρ x₁ n
      let Ln' := lyapunov P μ' π f η ρ x₁ (n + 1)
      let a := Real.sqrt (μ' * η)
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      Ln' ≤ (1 - (1 - θ) * a) * Ln)
    -- Motion bound on h_n (from `motion_bounds_curvature_error`)
    (C_h : ℝ) (hC_h : 0 < C_h)
    (hstep_bound : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let Ln := lyapunov P μ' π f η ρ x₁ n
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      ‖nesterovH f η ρ x₁ n‖ ≤ C_h * Real.sqrt η * Real.sqrt Ln)
    -- Motion bound on velocity (from `motion_bounds_curvature_error`)
    (C_mov : ℝ) (hC_mov : 0 < C_mov)
    (hvel_bound : ∀ (x₁ : E d) (n : ℕ),
      let s := nesterovSeq f η ρ x₁ n
      let s' := nesterovSeq f η ρ x₁ (n + 1)
      let Ln := lyapunov P μ' π f η ρ x₁ n
      s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
      ‖Real.sqrt η • s'.v‖ ≤ C_mov * Real.sqrt Ln) :
    -- Conclusion: ∃ α > 0 with the bootstrap property
    ∃ (α : ℝ), 0 < α ∧
      ∀ x₁ ∈ Metric.ball m_star α ∩ U,
        -- (1) All iterates stay in Ω
        (∀ n : ℕ,
          (nesterovSeq f η ρ x₁ n).x ∈ Ω ∧
          (nesterovSeq f η ρ x₁ n).lookahead η ∈ Ω) ∧
        -- (2) All iterates remain in U
        (∀ n : ℕ, (nesterovSeq f η ρ x₁ n).x ∈ U) ∧
        -- (3) Geometric decay of Lyapunov function
        (∀ n : ℕ,
          let a := Real.sqrt (μ' * η)
          lyapunov P μ' π f η ρ x₁ (n + 1) ≤
            (1 - (1 - θ) * a) ^ (n + 1) * lyapunov P μ' π f η ρ x₁ 0) := by
  exact bootstrapTotalDisplacementProof (d := d) (_hd := _hd) (f := f) (L := L) (_hL := _hL)
    (μ' := μ') (hμ' := hμ') (θ := θ) (hθ_pos := hθ_pos) (hθ_lt1 := hθ_lt1) (η := η) (_hη := _hη)
    (hη_pos := hη_pos) (hμη_lt1 := hμη_lt1) (ρ := ρ) (_hρ := _hρ) (S := S) (hM_argmin := hM_argmin)
    (U := U) (_hTub := _hTub) (π := π) (_hπ_in_S := _hπ_in_S) (_hπ_proj := _hπ_proj)
    (hπ_metric := hπ_metric) (P := P) (Ω := Ω) (hΩ_open := hΩ_open) (hΩ_sub_U := hΩ_sub_U) (R := R)
    (hR := hR) (m_star := m_star) (hm_star := hm_star) (hm_star_Ω := hm_star_Ω) (hΨ_cont := hΨ_cont)
    (hΨ_zero := hΨ_zero) (_hQG := _hQG) (hcontract := hcontract) (C_h := C_h) (hC_h := hC_h)
    (hstep_bound := hstep_bound) (C_mov := C_mov) (hC_mov := hC_mov) (hvel_bound := hvel_bound)

/-- Public theorem wrapper for `bootstrapTotalDisplacementGenProof`. -/
theorem bootstrap_total_displacement_gen
    {d : ℕ}
    (f : E d → ℝ)
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη_pos : 0 < η)
    (hμη_lt1 : μ' * η < 1)
    (ρ : ℝ)
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    (π : E d → E d)
    (P : E d →L[ℝ] E d)
    (Ω : Set (E d)) (hΩ_open : IsOpen Ω)
    (R : ℝ) (hR : 0 < R)
    (m_star : E d) (hm_star : m_star ∈ S) (hm_star_Ω : m_star ∈ Ω)
    -- Contraction (from lyapunov_contraction_gen)
    (hcontract : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
        (1 - (1 - θ) * Real.sqrt (μ' * η)) *
        lyapunovOfState P μ' π f η s)
    -- Step displacement bound
    (C_h : ℝ) (hC_h : 0 < C_h)
    (hstep_bound : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      ‖stepDispOfState f η ρ s‖ ≤
        C_h * Real.sqrt η *
        Real.sqrt (lyapunovOfState P μ' π f η s))
    -- Velocity bound
    (C_mov : ℝ) (hC_mov : 0 < C_mov)
    (hvel_bound : ∀ (s₀ : NesterovState d) (n : ℕ),
      let s := nesterovSeqGen f η ρ s₀ n
      s.x ∈ Ω → s.lookahead η ∈ Ω →
      lyapunovOfState P μ' π f η s ≤ R ^ 2 →
      ‖Real.sqrt η • (nesterovSeqGen f η ρ s₀ (n + 1)).v‖ ≤
        C_mov * Real.sqrt (lyapunovOfState P μ' π f η s)) :
    ∃ (δ r_ball : ℝ), 0 < δ ∧ 0 < r_ball ∧
      Metric.ball m_star r_ball ⊆ Ω ∧
      ∀ s₀ : NesterovState d,
        s₀.x ∈ Metric.ball m_star δ →
        s₀.lookahead η ∈ Metric.ball m_star δ →
        lyapunovOfState P μ' π f η s₀ ≤ δ ^ 2 →
        -- (1) All iterates stay in Ω
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Ω ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Ω) ∧
        -- (2) Ball containment: iterates stay in ball(m_star, r_ball)
        (∀ n : ℕ,
          (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball m_star r_ball ∧
          (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball m_star r_ball) ∧
        -- (3) Geometric decay
        (∀ n : ℕ,
          let a := Real.sqrt (μ' * η)
          lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ (n + 1)) ≤
            (1 - (1 - θ) * a) ^ (n + 1) *
            lyapunovOfState P μ' π f η s₀) := by
  exact bootstrapTotalDisplacementGenProof (d := d) (f := f) (μ' := μ') (hμ' := hμ') (θ := θ)
    (hθ_pos := hθ_pos) (hθ_lt1 := hθ_lt1) (η := η) (hη_pos := hη_pos) (hμη_lt1 := hμη_lt1) (ρ := ρ)
    (S := S) (hM_argmin := hM_argmin) (π := π) (P := P) (Ω := Ω) (hΩ_open := hΩ_open) (R := R)
    (hR := hR) (m_star := m_star) (hm_star := hm_star) (hm_star_Ω := hm_star_Ω)
    (hcontract := hcontract) (C_h := C_h) (hC_h := hC_h) (hstep_bound := hstep_bound)
    (C_mov := C_mov) (hC_mov := hC_mov) (hvel_bound := hvel_bound)

end PLAcceleratedNesterovLean
