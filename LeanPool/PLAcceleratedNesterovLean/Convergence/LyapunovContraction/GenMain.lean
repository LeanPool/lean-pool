/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.FlatCaseArithmetic
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.FlatCaseHelper
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step2
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.Step3
import LeanPool.PLAcceleratedNesterovLean.Convergence.StateContraction.AuxVarRecursion


/-!
# State-Based Lyapunov Contraction

Generalization of `lyapunov_contraction` (Main.lean) to arbitrary `NesterovState`,
supporting nonzero initial velocity. Used by `GenLocalArgument.lean`.
-/

@[expose] public section


noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


/-- Descent at the look-ahead point: a gradient step from a point well inside the ball
`B(m⋆, r₀) ⊆ U₊` decreases `f` by at least `(η/2)·‖∇f‖²`. -/
private theorem descent_at_lookahead {d : ℕ} (f : E d → ℝ)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (η : ℝ) (hη : η = 1 / (L : ℝ))
    (U_plus : Set (E d)) (hU_open : IsOpen U_plus)
    (hf_diff_on : DifferentiableOn ℝ f U_plus)
    (hf_lip : LipschitzOnWith L (gradient f) U_plus)
    (m_star : E d) (hm_star_Up : m_star ∈ U_plus) (hg_zero : gradient f m_star = 0)
    (r₀ : ℝ) (hball_sub : Metric.ball m_star r₀ ⊆ U_plus)
    (x'n : E d) (hx'_r09 : dist x'n m_star < r₀ / 9) :
    f (x'n - η • gradient f x'n) ≤ f x'n - η / 2 * ‖gradient f x'n‖ ^ 2 := by
  have hdist_nn := dist_nonneg (x := x'n) (y := m_star)
  have hx'_Up : x'n ∈ U_plus :=
    hball_sub (Metric.mem_ball.mpr (by linarith only [hx'_r09, hdist_nn]))
  have hgrad_lip' : ‖gradient f x'n‖ ≤ (↑L : ℝ) * dist x'n m_star := by
    have h := hf_lip.dist_le_mul x'n hx'_Up m_star hm_star_Up
    rwa [hg_zero, dist_zero_right] at h
  have hseg_x'n : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      x'n + t • (-(((1 : ℝ) / (L : ℝ)) • gradient f x'n)) ∈ U_plus := by
    intro t ht0 ht1
    apply hball_sub; rw [Metric.mem_ball]
    have h_step_bound : dist (x'n + t • (-(((1 : ℝ) / (↑L : ℝ)) • gradient f x'n))) x'n ≤
        dist x'n m_star := by
      rw [dist_eq_norm,
          show (x'n + t • (-(((1 : ℝ) / (↑L : ℝ)) • gradient f x'n))) - x'n =
              t • (-(((1 : ℝ) / (↑L : ℝ)) • gradient f x'n)) from by abel,
          norm_smul, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ht0, Real.norm_eq_abs,
          abs_of_pos (div_pos one_pos hL)]
      calc t * ((1 : ℝ) / (↑L : ℝ) * ‖gradient f x'n‖)
          ≤ 1 * ((1 : ℝ) / (↑L : ℝ) * ((↑L : ℝ) * dist x'n m_star)) :=
            mul_le_mul ht1
              (mul_le_mul_of_nonneg_left hgrad_lip'
                (le_of_lt (div_pos one_pos hL)))
              (mul_nonneg (le_of_lt (div_pos one_pos hL)) (norm_nonneg _))
              one_pos.le
        _ = dist x'n m_star := by
            rw [one_mul, ← mul_assoc, one_div_mul_cancel (ne_of_gt hL), one_mul]
    calc dist (x'n + t • (-(((1 : ℝ) / (↑L : ℝ)) • gradient f x'n))) m_star
        ≤ dist (x'n + t • (-(((1 : ℝ) / (↑L : ℝ)) • gradient f x'n))) x'n +
            dist x'n m_star :=
          dist_triangle _ _ _
      _ ≤ 2 * dist x'n m_star := by linarith only [h_step_bound]
      _ < 2 * (r₀ / 9) := by linarith only [hx'_r09]
      _ < r₀ := by linarith only [hx'_r09, hdist_nn]
  exact lsmooth_descent_at f L hL hU_open hf_diff_on hf_lip x'n hx'_Up hseg_x'n η hη

/-- The gradient step moves the position by at most the distance of the look-ahead point
to `m⋆`: `dist(x_{n+1}, m⋆) ≤ 2·dist(x'_n, m⋆)`. -/
private theorem nesterovStep_dist_le_two_mul {d : ℕ} (f : E d → ℝ)
    (L : ℝ≥0) (η ρ : ℝ) (hη_pos : 0 < η) (hηL : η * (L : ℝ) = 1)
    (U_plus : Set (E d)) (hf_lip : LipschitzOnWith L (gradient f) U_plus)
    (m_star : E d) (hm_star_Up : m_star ∈ U_plus) (hg_zero : gradient f m_star = 0)
    (sn : NesterovState d) (hx'_Up : sn.lookahead η ∈ U_plus) :
    dist (nesterovStep f η ρ sn).x m_star ≤ 2 * dist (sn.lookahead η) m_star := by
  have h_sn1_x : (nesterovStep f η ρ sn).x =
      sn.lookahead η - η • gradient f (sn.lookahead η) := rfl
  rw [h_sn1_x]
  generalize sn.lookahead η = x'n at hx'_Up ⊢
  have hgrad_lip : ‖gradient f x'n‖ ≤ (L : ℝ) * dist x'n m_star := by
    have h := hf_lip.dist_le_mul x'n hx'_Up m_star hm_star_Up
    rwa [hg_zero, dist_zero_right] at h
  have h_step_dist : dist (x'n - η • gradient f x'n) x'n = η * ‖gradient f x'n‖ := by
    rw [dist_eq_norm]
    have : (x'n - η • gradient f x'n) - x'n = -(η • gradient f x'n) := by abel
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη_pos]
  calc dist (x'n - η • gradient f x'n) m_star
      ≤ dist (x'n - η • gradient f x'n) x'n + dist x'n m_star := dist_triangle _ _ _
    _ = η * ‖gradient f x'n‖ + dist x'n m_star := by rw [h_step_dist]
    _ ≤ η * ((L : ℝ) * dist x'n m_star) + dist x'n m_star := by
        linarith only [hη_pos, hgrad_lip, mul_le_mul_of_nonneg_left hgrad_lip (le_of_lt hη_pos)]
    _ = 2 * dist x'n m_star := by
        have : η * ((L : ℝ) * dist x'n m_star) = dist x'n m_star := by
          rw [← mul_assoc, hηL, one_mul]
        linarith only [this]

/-- Distance bound for the next look-ahead point. Uses the identity
`x'_{n+1} = (1+ρ)·x_{n+1} - ρ·x_n` and the triangle inequality:
`dist(x'_{n+1}, m⋆) ≤ (1+ρ)·dist(x_{n+1}, m⋆) + ρ·dist(x_n, m⋆) < (2 + 3ρ)·r < 5r`. -/
private theorem nesterovStep_lookahead_dist_lt {d : ℕ} (f : E d → ℝ)
    (η ρ : ℝ) (hη_pos : 0 < η) (hρ_pos : 0 < ρ) (hρ_lt1 : ρ < 1)
    (m_star : E d) (r : ℝ) (sn : NesterovState d)
    (hx : dist sn.x m_star < r) (hx1 : dist (nesterovStep f η ρ sn).x m_star < 2 * r) :
    dist ((nesterovStep f η ρ sn).lookahead η) m_star < 5 * r := by
  set sn1 := nesterovStep f η ρ sn with hsn1
  set x'n := sn.lookahead η with hx'n
  set gn := gradient f x'n with hgn
  have hr_pos : 0 < r := lt_of_le_of_lt dist_nonneg hx
  -- Key identity: x'_{n+1} = (1+ρ)·x_{n+1} - ρ·x_n
  have h_conv : sn1.lookahead η = (1 + ρ) • sn1.x - ρ • sn.x := by
    change sn1.x + Real.sqrt η • sn1.v = (1 + ρ) • sn1.x - ρ • sn.x
    have hsq : Real.sqrt η * Real.sqrt η = η :=
      Real.mul_self_sqrt (le_of_lt hη_pos)
    have h5 : Real.sqrt η • (ρ • (sn.v - Real.sqrt η • gn)) =
        ρ • (Real.sqrt η • sn.v - η • gn) := by
      rw [smul_comm (Real.sqrt η) ρ, smul_sub, ← mul_smul, hsq]
    change (x'n - η • gn) + Real.sqrt η • (ρ • (sn.v - Real.sqrt η • gn)) =
      (1 + ρ) • (x'n - η • gn) - ρ • sn.x
    rw [h5]
    change (sn.x + Real.sqrt η • sn.v - η • gn) +
        ρ • (Real.sqrt η • sn.v - η • gn) =
      (1 + ρ) • (sn.x + Real.sqrt η • sn.v - η • gn) - ρ • sn.x
    module
  -- Subtract m_star using the convex combination identity
  have h_sub : sn1.lookahead η - m_star =
      (1 + ρ) • (sn1.x - m_star) - ρ • (sn.x - m_star) := by
    rw [h_conv]; module
  calc dist (sn1.lookahead η) m_star
      = ‖sn1.lookahead η - m_star‖ := dist_eq_norm _ _
    _ = ‖(1 + ρ) • (sn1.x - m_star) - ρ • (sn.x - m_star)‖ := by
        rw [h_sub]
    _ ≤ ‖(1 + ρ) • (sn1.x - m_star)‖ + ‖ρ • (sn.x - m_star)‖ :=
        norm_sub_le _ _
    _ = (1 + ρ) * ‖sn1.x - m_star‖ + ρ * ‖sn.x - m_star‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs,
            abs_of_pos (by linarith only [hρ_pos] : (0:ℝ) < 1 + ρ),
            Real.norm_eq_abs, abs_of_pos hρ_pos]
    _ = (1 + ρ) * dist sn1.x m_star + ρ * dist sn.x m_star := by
        simp only [dist_eq_norm]
    _ < (1 + ρ) * (2 * r) + ρ * r := by
        have h1 : (1 + ρ) * dist sn1.x m_star < (1 + ρ) * (2 * r) :=
          mul_lt_mul_of_pos_left hx1 (by linarith only [hρ_pos, hρ_lt1] : (0:ℝ) < 1 + ρ)
        have h2 : ρ * dist sn.x m_star < ρ * r :=
          mul_lt_mul_of_pos_left hx hρ_pos
        linarith only [h1, h2]
    _ < 5 * r := by
        have h3 : ρ * r < r := mul_lt_of_lt_one_left hr_pos hρ_lt1
        linarith only [h3]

/-- **Flat-case assembly.** The heart of the Lyapunov contraction in the flat case:
with `w = (1-a)·P⊥v + √μ'·e - √η·P⊥g`, combining descent, aiming, the segment estimate
and the tangential identity yields
`F_{n+1} + ‖w‖²/2 + T_{n+1} ≤ (1-a)·(F_n + U_n/2 + T_n) + a·|⟨g, Pe⟩|`. -/
private theorem flat_case_bound {d : ℕ} (P : E d →L[ℝ] E d)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    (hP_idem : ∀ x : E d, P (P x) = P x)
    (μ' η ε a : ℝ) (hμ' : 0 < μ') (hη_pos : 0 < η) (hε_pos : 0 < ε)
    (hε_bound : ε * η ≤ a) (ha : a = Real.sqrt (μ' * η)) (ha_lt1 : a < 1)
    (v g e w : E d)
    (hwn_eq : w = (1 - a) • (v - P v) + Real.sqrt μ' • e - Real.sqrt η • (g - P g))
    (Fn Fn1 Fnprime : ℝ) (hgap_nn : 0 ≤ Fn) (hgap'_nn : 0 ≤ Fn1) (hFnprime_nn : 0 ≤ Fnprime)
    (h_f_upper : Fn1 ≤ Fnprime - η / 2 * ‖g‖ ^ 2)
    (h_aim : @inner ℝ _ _ g e ≥ Fnprime + μ' / 2 * ‖e‖ ^ 2)
    (h_seg : @inner ℝ _ _ g (Real.sqrt η • v) ≥
      Fnprime - Fn - ε / 2 * ‖Real.sqrt η • v‖ ^ 2) :
    Fn1 + ‖w‖ ^ 2 / 2 + (1 - a) / 2 * ‖P v - Real.sqrt η • P g‖ ^ 2 ≤
      (1 - a) * (Fn + ‖(v - P v) + Real.sqrt μ' • e‖ ^ 2 / 2 +
        (1 + a) ^ 2 / (2 * (1 - a)) * ‖P v‖ ^ 2) + a * |@inner ℝ _ _ g (P e)| := by
  have ha_pos : 0 < a := ha ▸ Real.sqrt_pos_of_pos (mul_pos hμ' hη_pos)
  -- ═══ B: Projector-freezing decomposition ═══
  -- ⟨g, e⟩ = ⟨P⊥g, e⟩ + ⟨g, Pe⟩ (via self-adjointness of P)
  have h_ipGE_decomp : @inner ℝ _ _ g e =
      @inner ℝ _ _ (g - P g) e + @inner ℝ _ _ g (P e) := by
    have hsplit : g = (g - P g) + P g := by abel
    conv_lhs => rw [hsplit]
    rw [inner_add_left, hP_self_adj g e]
  have hG_pyth := pythagorean_proj P hP_self_adj hP_idem g
  have hV_pyth := pythagorean_proj P hP_self_adj hP_idem v
  have h_ip_decomp := inner_proj_decomp P hP_self_adj hP_idem g v
  -- ═══ D: Norm expansions ═══
  have h_wn_sq : ‖w‖ ^ 2 =
      (1 - a) ^ 2 * ‖v - P v‖ ^ 2 + μ' * ‖e‖ ^ 2 +
      η * ‖g - P g‖ ^ 2 +
      2 * (1 - a) * Real.sqrt μ' * @inner ℝ _ _ (v - P v) e -
      2 * (1 - a) * Real.sqrt η * @inner ℝ _ _ (v - P v) (g - P g) -
      2 * Real.sqrt μ' * Real.sqrt η * @inner ℝ _ _ e (g - P g) := by
    rw [hwn_eq]
    exact norm_three_term_sq _ _ _ _ _ _ (le_of_lt hμ') (le_of_lt hη_pos)
  have h_un_eq : ‖(v - P v) + Real.sqrt μ' • e‖ ^ 2 = ‖v - P v‖ ^ 2 +
      2 * Real.sqrt μ' * @inner ℝ _ _ (v - P v) e + μ' * ‖e‖ ^ 2 := by
    rw [norm_two_term_sq _ _ _ (le_of_lt hμ')]; ring
  have h_sqrt_prod : Real.sqrt μ' * Real.sqrt η = a := by
    rw [ha, ← Real.sqrt_mul (le_of_lt hμ')]
  -- Key coefficient identity: 2·√μ'·√η = 2·a (for norm simplification)
  have h2a : 2 * Real.sqrt μ' * Real.sqrt η = 2 * a := by
    have : (2 : ℝ) * Real.sqrt μ' * Real.sqrt η =
        2 * (Real.sqrt μ' * Real.sqrt η) := by ring
    rw [this, h_sqrt_prod]
  -- ═══ H: Apply flat_case_arithmetic ═══
  -- Descent bound: Fn1 ≤ Fnprime - η/2·(‖Pg‖² + ‖P⊥g‖²)
  have hFn1_descent : Fn1 ≤ Fnprime - η / 2 * (‖P g‖ ^ 2 + ‖g - P g‖ ^ 2) := by
    rw [← hG_pyth]; exact h_f_upper
  -- Segment: √η·(⟨Pg,Pv⟩ + ⟨P⊥g,P⊥v⟩) ≥ Fnprime - Fn - εη/2·(‖Pv‖² + ‖P⊥v‖²)
  have h_segment_arith :
      Real.sqrt η * (@inner ℝ _ _ (P g) (P v) +
        @inner ℝ _ _ (g - P g) (v - P v)) ≥
      Fnprime - Fn - ε * η / 2 * (‖P v‖ ^ 2 + ‖v - P v‖ ^ 2) := by
    have h1 := h_seg
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg η), mul_pow, Real.sq_sqrt (le_of_lt hη_pos)] at h1
    rw [h_ip_decomp, hV_pyth] at h1
    linarith only [h1]
  -- Aiming: ⟨P⊥g, e⟩ ≥ Fnprime + μ'/2·‖e‖² − |⟨g, Pe⟩| (projector-freezing error)
  have h_aiming_arith : @inner ℝ _ _ (g - P g) e ≥
      Fnprime + μ' / 2 * ‖e‖ ^ 2 - abs (@inner ℝ _ _ g (P e)) := by
    have hle := le_abs_self (@inner ℝ _ _ g (P e))
    linarith only [h_aim, h_ipGE_decomp, hle]
  -- w norm identity (with √μ'·√η = a)
  have hwn_sq_arith : ‖w‖ ^ 2 =
      (1 - a) ^ 2 * ‖v - P v‖ ^ 2 + μ' * ‖e‖ ^ 2 +
      η * ‖g - P g‖ ^ 2 +
      2 * (1 - a) * Real.sqrt μ' * @inner ℝ _ _ (v - P v) e -
      2 * (1 - a) * Real.sqrt η * @inner ℝ _ _ (g - P g) (v - P v) -
      2 * a * @inner ℝ _ _ (g - P g) e := by
    rw [h_wn_sq, h2a, real_inner_comm (g - P g) e, real_inner_comm (g - P g) (v - P v)]
  -- T_{n+1} identity (matching flat_case_arithmetic parameter order)
  have hTn1_arith : (1 - a) / 2 * ‖P v - Real.sqrt η • P g‖ ^ 2 =
      (1 - a) / 2 * ‖P v‖ ^ 2 - (1 - a) * Real.sqrt η * @inner ℝ _ _ (P g) (P v) +
      (1 - a) * η / 2 * ‖P g‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (le_of_lt hη_pos),
      real_inner_comm (P g) (P v)]
    ring
  exact flat_case_arithmetic a ha_pos ha_lt1
    η μ' (Real.sqrt μ') (Real.sqrt η)
    hη_pos hμ' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sq_sqrt (le_of_lt hμ')) (Real.sq_sqrt (le_of_lt hη_pos))
    h_sqrt_prod
    (ε * η) (mul_nonneg (le_of_lt hε_pos) (le_of_lt hη_pos)) hε_bound
    Fn Fn1 Fnprime hgap_nn hgap'_nn hFnprime_nn
    (‖P v‖ ^ 2) (‖v - P v‖ ^ 2) (‖P g‖ ^ 2) (‖g - P g‖ ^ 2) (‖e‖ ^ 2)
    (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
    (@inner ℝ _ _ (g - P g) e) (@inner ℝ _ _ (P g) (P v))
    (@inner ℝ _ _ (g - P g) (v - P v)) (@inner ℝ _ _ (v - P v) e)
    (abs (@inner ℝ _ _ g (P e))) (abs_nonneg _)
    hFn1_descent h_segment_arith h_aiming_arith
    (‖w‖ ^ 2) hwn_sq_arith
    _ h_un_eq
    _ hTn1_arith
    _ rfl

/-- **One-step contraction for a single state.** Given the descent, aiming and segment
estimates at the look-ahead point and the perturbation absorption bound for the state `sn`,
the Lyapunov function contracts: `L(s_{n+1}) ≤ (1 - (1-θ)·a)·L(sₙ)`. -/
private theorem lyapunovOfState_step_le {d : ℕ} (f : E d → ℝ)
    (μ' : ℝ) (hμ' : 0 < μ') (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη_pos : 0 < η) (ha_lt1 : Real.sqrt (μ' * η) < 1)
    (ρ : ℝ) (hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    (π : E d → E d) (P : E d →L[ℝ] E d)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    (hP_idem : ∀ x : E d, P (P x) = P x)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_bound : ε * η ≤ Real.sqrt (μ' * η))
    (hbdd : BddBelow (Set.range f)) (sn : NesterovState d)
    (h_descent : f (nesterovStep f η ρ sn).x ≤
      f (sn.lookahead η) - η / 2 * ‖gradient f (sn.lookahead η)‖ ^ 2)
    (h_aim : @inner ℝ _ _ (gradient f (sn.lookahead η)) (sn.lookahead η - π (sn.lookahead η)) ≥
      f (sn.lookahead η) - fStar f + μ' / 2 * ‖sn.lookahead η - π (sn.lookahead η)‖ ^ 2)
    (h_seg : @inner ℝ _ _ (gradient f (sn.lookahead η)) (sn.lookahead η - sn.x) ≥
      f (sn.lookahead η) - f sn.x - ε / 2 * ‖sn.lookahead η - sn.x‖ ^ 2)
    (h_absorb :
      let gn := gradient f (sn.lookahead η)
      let en := sn.lookahead η - π (sn.lookahead η)
      let ξn := curvatureErrorOfState (↑P) π f η ρ sn
      let wn := auxVarOfState P μ' π η (nesterovStep f η ρ sn) - Real.sqrt μ' • ξn
      let a := Real.sqrt (μ' * η)
      Real.sqrt μ' * @inner ℝ _ _ wn ξn + (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2 +
        a * |@inner ℝ _ _ gn (P en)| ≤ θ * a * lyapunovOfState P μ' π f η sn) :
    let a := Real.sqrt (μ' * η)
    lyapunovOfState P μ' π f η (nesterovStep f η ρ sn) ≤
      (1 - (1 - θ) * a) * lyapunovOfState P μ' π f η sn := by
  intro a
  set sn1 := nesterovStep f η ρ sn with hsn1
  set x'n := sn.lookahead η with hx'n
  set gn := gradient f x'n with hgn
  have ha_pos : 0 < a := Real.sqrt_pos_of_pos (mul_pos hμ' hη_pos)
  have hρ_pos : 0 < ρ := by
    rw [hρ]
    exact div_pos (sub_pos.mpr ha_lt1) (by linarith only [ha_pos])
  have hgap_nn : 0 ≤ f sn.x - fStar f :=
    sub_nonneg.mpr (ciInf_le hbdd sn.x)
  have hgap'_nn : 0 ≤ f sn1.x - fStar f :=
    sub_nonneg.mpr (ciInf_le hbdd sn1.x)
  -- Parameter positivity
  have h1a_pos : (0 : ℝ) < 1 + a := by linarith only [hθ_pos, hθ_lt1, ha_pos]
  have h1a_ne : (1 + a : ℝ) ≠ 0 := ne_of_gt h1a_pos
  have h1ma_ne : (1 - a : ℝ) ≠ 0 := ne_of_gt (by linarith only [ha_lt1])
  -- λ = (1+a)²/(2(1-a)) > 0
  have hlam_pos : (0 : ℝ) < (1 + a) ^ 2 / (2 * (1 - a)) :=
    div_pos (sq_pos_of_pos h1a_pos) (by linarith only [ha_lt1])
  -- Ln ≥ 0
  have hLn_nn : 0 ≤ lyapunovOfState P μ' π f η sn := by
    simp only [lyapunovOfState]
    have hlam_nn : 0 ≤ (1 + Real.sqrt (μ' * η)) ^ 2 / (2 * (1 - Real.sqrt (μ' * η))) :=
      le_of_lt hlam_pos
    have h1 := sq_nonneg ‖auxVarOfState P μ' π η sn‖
    have h2 := mul_nonneg hlam_nn (sq_nonneg ‖P sn.v‖)
    linarith only [hgap_nn, h1, h2]
  -- ══════════════ Tangential velocity identity ══════════════
  -- P is a CLM, so P(sn1.v) = ρ • (P sn.v - √η • P gn)
  have hPv1 : P sn1.v = ρ • (P sn.v - Real.sqrt η • P gn) := by
    change P (ρ • (sn.v - Real.sqrt η • gn)) = ρ • (P sn.v - Real.sqrt η • P gn)
    rw [map_smul, map_sub, map_smul]
  -- λ‖P sn1.v‖² = ((1-a)/2) ‖P sn.v - √η • P gn‖²
  have hTn1_eq : (1 + a) ^ 2 / (2 * (1 - a)) * ‖P sn1.v‖ ^ 2 =
      (1 - a) / 2 * ‖P sn.v - Real.sqrt η • P gn‖ ^ 2 := by
    rw [hPv1, norm_smul, Real.norm_eq_abs, abs_of_pos hρ_pos, mul_pow, ← mul_assoc]
    congr 1
    exact lambda_rho_sq a ρ _ h1a_ne h1ma_ne hρ rfl
  -- ══════════════ Lyapunov decomposition ══════════════
  -- Abbreviate the Lyapunov components at steps n and n+1.
  set lam := (1 + a) ^ 2 / (2 * (1 - a)) with hlam_def
  set Fn  := f sn.x - fStar f  with hFn_def
  set Un  := ‖auxVarOfState P μ' π η sn‖ ^ 2 with hUn_def
  set Tn  := lam * ‖P sn.v‖ ^ 2 with hTn_def
  set un1 := auxVarOfState P μ' π η sn1 with hun1_def
  set Fn1 := f sn1.x - fStar f   with hFn1_def
  set Un1 := ‖un1‖ ^ 2            with hUn1_def
  set Tn1 := lam * ‖P sn1.v‖ ^ 2  with hTn1_def
  -- Lyapunov decomposition identities
  have hLn_eq : lyapunovOfState P μ' π f η sn = Fn + Un / 2 + Tn := by
    unfold lyapunovOfState; rfl
  have hLn'_eq : lyapunovOfState P μ' π f η sn1 = Fn1 + Un1 / 2 + Tn1 := by
    unfold lyapunovOfState; rfl
  -- ── Define intermediate quantities ──
  let ξn := curvatureErrorOfState (↑P) π f η ρ sn
  let wn := un1 - Real.sqrt μ' • ξn
  -- ── AuxVar decomposition: u_{n+1} = w_n + √μ'·ξ_n ──
  have h_un1_eq : un1 = wn + Real.sqrt μ' • ξn := by
    change un1 = (un1 - Real.sqrt μ' • ξn) + Real.sqrt μ' • ξn
    abel
  -- ── Perturbation expansion ──
  have h_Un1_expand : Un1 =
      ‖wn‖ ^ 2 + 2 * Real.sqrt μ' * @inner ℝ _ _ wn ξn +
      (Real.sqrt μ') ^ 2 * ‖ξn‖ ^ 2 := by
    change ‖un1‖ ^ 2 = _
    rw [h_un1_eq]
    exact perturbation_expansion wn ξn (Real.sqrt μ')
  -- ── Curvature perturbation δ ──
  set δ_curv := Real.sqrt μ' * @inner ℝ _ _ wn ξn +
                (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2 with hδ_def
  -- ── Perturbation splitting: Un1/2 = ‖wn‖²/2 + δ_curv ──
  have h_Un1_half : Un1 / 2 = ‖wn‖ ^ 2 / 2 + δ_curv := by
    rw [h_Un1_expand]; ring
  -- ── Flat-case assembly (Step A core) ──
  have h_flat : Fn1 + ‖wn‖ ^ 2 / 2 + Tn1 ≤
      (1 - a) * (Fn + Un / 2 + Tn) + a * abs (@inner ℝ _ _ gn (P (x'n - π x'n))) := by
    -- wn decomposition via the auxiliary-variable recursion
    have hwn_eq : (wn : E d) = (1 - a) • (sn.v - P sn.v) +
        Real.sqrt μ' • (x'n - π x'n) - Real.sqrt η • (gn - P gn) := by
      change un1 - Real.sqrt μ' • ξn = _
      have h_av := auxVarOfState_step P μ' η ρ π f sn hρ ha_pos hη_pos hμ'
      have : (un1 : E d) = ((1 - a) • (sn.v - P sn.v) + Real.sqrt μ' • (x'n - π x'n) -
          Real.sqrt η • (gn - P gn)) + Real.sqrt μ' • ξn := by
        change auxVarOfState P μ' π η (nesterovStep f η ρ sn) = _; exact h_av
      rw [this]; abel
    have h_diff_eq : x'n - sn.x = Real.sqrt η • sn.v := by
      change sn.x + Real.sqrt η • sn.v - sn.x = _; abel
    have hTn1_val : Tn1 = (1 - a) / 2 * ‖P sn.v - Real.sqrt η • P gn‖ ^ 2 := by
      rw [hTn1_def]; exact hTn1_eq
    rw [hTn1_val]
    refine flat_case_bound P hP_self_adj hP_idem μ' η ε a hμ' hη_pos hε_pos hε_bound rfl
      ha_lt1 sn.v gn (x'n - π x'n) wn hwn_eq Fn Fn1 (f x'n - fStar f) hgap_nn hgap'_nn
      (sub_nonneg.mpr (ciInf_le hbdd x'n)) (by linarith only [h_descent])
      (by linarith only [h_aim]) ?_
    rw [← h_diff_eq]; linarith only [h_seg]
  -- ── Final assembly ──
  apply two_step_contraction_general a θ _ _
    (δ_curv + a * abs (@inner ℝ _ _ gn (P (x'n - π x'n))))
    ha_pos ha_lt1 hθ_pos hθ_lt1 hLn_nn
  · -- Goal: Ln' ≤ (1-a) * Ln + (δ_curv + proj_err_n)
    rw [hLn'_eq, hLn_eq]
    linarith only [h_Un1_expand, hδ_def, h_flat, h_Un1_half]
  · -- Goal: (δ_curv + proj_err_n) ≤ θ * a * Ln
    exact h_absorb

/-- **State-based Lyapunov contraction.**

After shrinking Ω and R if necessary, for every state `sₙ` satisfying the perturbation
absorption bound, whenever xₙ, x'ₙ ∈ Ω and Lₙ ≤ R²:
  L_{n+1} ≤ (1 - (1-θ)·a) · L_n
and x_{n+1}, x'_{n+1} ∈ Ω⁺. Both `lyapunov_contraction_gen` and `lyapunov_contraction`
are instances of this single-step statement. -/
theorem lyapunov_contraction_of_state
    {d : ℕ}
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (ρ : ℝ) (hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Nearest-point projection
    (π : E d → E d)
    -- Gradient vanishes on S
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    -- Tangent projector P = Dπ(m⋆)
    (P : E d →L[ℝ] E d)
    -- Base point
    (m_star : E d) (hm_star : m_star ∈ S)
    -- ε from `local_fiberwise_geometry`
    (ε : ℝ) (hε_pos : 0 < ε) (hε_bound : ε * η ≤ Real.sqrt (μ' * η))
    (hμη_lt1 : μ' * η < 1)
    -- Strong aiming on U₊ (from `local_fiberwise_geometry`)
    (U_plus : Set (E d))
    (hU_open : IsOpen U_plus)
    (hm_star_Up : m_star ∈ U_plus)
    -- Local smoothness on U₊
    (hf_diff_on : DifferentiableOn ℝ f U_plus)
    (hf_lip : LipschitzOnWith L (gradient f) U_plus)
    (hStrAim : ∀ x ∈ U_plus,
      @inner ℝ _ _ (gradient f x) (x - π x) ≥
        f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2)
    -- Hessian lower bound on U₊ (from `local_fiberwise_geometry`)
    (_hHess_lower : ∀ x ∈ U_plus, ∀ ξ : E d,
      hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2)
    -- P is self-adjoint (orthogonal projector property)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    -- P is idempotent (orthogonal projector property)
    (hP_idem : ∀ x : E d, P (P x) = P x)
    -- Segment estimate (from D²f ≽ -εI and C² regularity):
    --   ⟨∇f(x), x - z⟩ ≥ f(x) - f(z) - ε/2 · ‖x - z‖²
    (hSegment : ∀ x z : E d, x ∈ U_plus → z ∈ U_plus →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • z + t • x ∈ U_plus) →
      @inner ℝ _ _ (gradient f x) (x - z) ≥
        f x - f z - ε / 2 * ‖x - z‖ ^ 2)
    -- R_abs is the energy/spatial radius on which the absorption bound is available.
    (R_abs : ℝ) (hR_abs : 0 < R_abs) :
    ∃ (Ω Ω_plus : Set (E d)) (R : ℝ),
      IsOpen Ω ∧ IsOpen Ω_plus ∧ 0 < R ∧
      m_star ∈ Ω ∧ Ω ⊆ Ω_plus ∧ Ω_plus ⊆ U_plus ∧
      ∀ (sn : NesterovState d),
        let sn1 := nesterovStep f η ρ sn
        let Ln := lyapunovOfState P μ' π f η sn
        let Ln' := lyapunovOfState P μ' π f η sn1
        let a := Real.sqrt (μ' * η)
        -- Total perturbation absorption (curvature + projector-freezing error) at `sn`
        (sn.x ∈ Metric.ball m_star R_abs → sn.lookahead η ∈ Metric.ball m_star R_abs →
          Ln ≤ R_abs ^ 2 →
          let gn := gradient f (sn.lookahead η)
          let en := sn.lookahead η - π (sn.lookahead η)
          let ξn := curvatureErrorOfState (↑P) π f η ρ sn
          let wn := auxVarOfState P μ' π η sn1 - Real.sqrt μ' • ξn
          Real.sqrt μ' * @inner ℝ _ _ wn ξn + (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2 +
            a * |@inner ℝ _ _ gn (P en)| ≤ θ * a * Ln) →
        sn.x ∈ Ω → sn.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
        -- Contraction
        Ln' ≤ (1 - (1 - θ) * a) * Ln ∧
        -- Next iterates in Ω⁺
        sn1.x ∈ Ω_plus ∧ sn1.lookahead η ∈ Ω_plus := by
  -- ═══════════════════════════════════════════════════════════════
  -- Neighborhood construction
  -- ═══════════════════════════════════════════════════════════════
  -- Extract r₀ > 0 with B(m⋆, r₀) ⊆ U₊
  obtain ⟨r₀, hr₀_pos, hball_sub⟩ : ∃ r₀ > 0, Metric.ball m_star r₀ ⊆ U_plus := by
    exact Metric.isOpen_iff.mp hU_open m_star hm_star_Up
  -- Auxiliary inequalities for the chosen radii
  have hr₀9 : (0 : ℝ) < r₀ / 9 := by linarith only [hr₀_pos]
  have hR_min : (0 : ℝ) < min (r₀ / 9) R_abs := lt_min hr₀9 hR_abs
  -- Ω = B(m⋆, min(r₀/9, R_abs)) — ensures iterates are in B(m⋆, R_abs) for the absorption
  have hΩ_sub_r09 : Metric.ball m_star (min (r₀ / 9) R_abs) ⊆
      Metric.ball m_star (r₀ / 9) :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hΩ_sub_Rabs : Metric.ball m_star (min (r₀ / 9) R_abs) ⊆
      Metric.ball m_star R_abs :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hΩ_sub_Ωp : Metric.ball m_star (min (r₀ / 9) R_abs) ⊆
      Metric.ball m_star (2 * r₀ / 3) :=
    hΩ_sub_r09.trans (Metric.ball_subset_ball (by linarith only [hr₀_pos]))
  have h23_le : 2 * r₀ / 3 ≤ r₀ := by linarith only [hr₀_pos]
  have hΩp_sub_Up : Metric.ball m_star (2 * r₀ / 3) ⊆ U_plus :=
    (Metric.ball_subset_ball h23_le).trans hball_sub
  -- Provide the existential witnesses:
  --   Ω   := B(m⋆, min(r₀/9, R_abs))
  --   Ω₊  := B(m⋆, 2r₀/3)
  --   R   := min(r₀/9, R_abs)
  refine ⟨Metric.ball m_star (min (r₀ / 9) R_abs),
          Metric.ball m_star (2 * r₀ / 3),
          min (r₀ / 9) R_abs,
          Metric.isOpen_ball,
          Metric.isOpen_ball,
          hR_min,
          Metric.mem_ball_self hR_min,
          hΩ_sub_Ωp,
          hΩp_sub_Up,
          ?_⟩
  -- ═══════════════════════════════════════════════════════════════
  -- Main contraction argument
  -- ═══════════════════════════════════════════════════════════════
  intro sn sn1 Ln Ln' a h_curv_absorb hx_in hx'_in hLn_bound
  have hg_zero_mstar : gradient f m_star = 0 := hgrad_zero m_star hm_star
  have hηL : η * (L : ℝ) = 1 := by rw [hη]; field_simp
  have hx'_ball_r09 : dist (sn.lookahead η) m_star < r₀ / 9 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hx'_in) (min_le_left _ _)
  have hx_ball_r09 : dist sn.x m_star < r₀ / 9 :=
    lt_of_lt_of_le (Metric.mem_ball.mp hx_in) (min_le_left _ _)
  have hx'n_Up : sn.lookahead η ∈ U_plus := hΩp_sub_Up (hΩ_sub_Ωp hx'_in)
  have ha_pos : 0 < a := Real.sqrt_pos_of_pos (mul_pos hμ' hη_pos)
  have ha_lt1 : a < 1 := by
    have hle : (0 : ℝ) ≤ μ' * η := le_of_lt (mul_pos hμ' hη_pos)
    calc a = Real.sqrt (μ' * η) := rfl
      _ < Real.sqrt 1 := Real.sqrt_lt_sqrt hle hμη_lt1
      _ = 1 := Real.sqrt_one
  have hρ_pos : 0 < ρ := by
    rw [hρ]
    exact div_pos (sub_pos.mpr ha_lt1) (by linarith only [ha_pos])
  -- Step 1 (Descent): f(x_{n+1}) ≤ f(x'_n) − (η/2)·‖g_n‖²
  have h_descent := descent_at_lookahead f L hL η hη U_plus hU_open hf_diff_on hf_lip
    m_star hm_star_Up hg_zero_mstar r₀ hball_sub (sn.lookahead η) hx'_ball_r09
  -- Distance bound on x_{n+1}: dist(x_{n+1}, m⋆) ≤ 2·dist(x'_n, m⋆)
  have h_sn1_dist := nesterovStep_dist_le_two_mul f L η ρ hη_pos hηL U_plus hf_lip
    m_star hm_star_Up hg_zero_mstar sn hx'n_Up
  refine ⟨?contraction, ?x_next_in, ?x'_next_in⟩
  case contraction =>
    -- BddBelow for fStar
    have hbdd : BddBelow (Set.range f) :=
      ⟨f m_star, by rintro _ ⟨x, rfl⟩; exact (hM_argmin ▸ hm_star : m_star ∈ argminSet f) x⟩
    -- Segment estimate along [xₙ, x'ₙ] ⊆ Ω ⊆ U₊
    have hxn_Up : sn.x ∈ U_plus := hΩp_sub_Up (hΩ_sub_Ωp hx_in)
    have h_path : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (1 - t) • sn.x + t • sn.lookahead η ∈ U_plus := by
      intro t ht0 ht1
      exact hΩp_sub_Up (hΩ_sub_Ωp
        ((convex_ball m_star (min (r₀ / 9) R_abs)) hx_in hx'_in
          (by linarith only [ht1] : (0 : ℝ) ≤ 1 - t) ht0
          (by linarith only [] : (1 : ℝ) - t + t = 1)))
    -- Derive Ln ≤ R_abs² from Ln ≤ (min(r₀/9, R_abs))² ≤ R_abs²
    have hLn_le_Rabs : Ln ≤ R_abs ^ 2 := by
      calc Ln ≤ (min (r₀ / 9) R_abs) ^ 2 := hLn_bound
        _ ≤ R_abs ^ 2 := by
          apply pow_le_pow_left₀ (le_min (le_of_lt hr₀9) (le_of_lt hR_abs))
            (min_le_right _ _)
    exact lyapunovOfState_step_le f μ' hμ' θ hθ_pos hθ_lt1 η hη_pos ha_lt1 ρ hρ π P
      hP_self_adj hP_idem ε hε_pos hε_bound hbdd sn h_descent
      (hStrAim _ hx'n_Up) (hSegment _ _ hx'n_Up hxn_Up h_path)
      (h_curv_absorb (hΩ_sub_Rabs hx_in) (hΩ_sub_Rabs hx'_in) hLn_le_Rabs)
  case x_next_in =>
    rw [Metric.mem_ball]
    exact h_sn1_dist.trans_lt (by linarith only [hr₀_pos, hx'_ball_r09])
  case x'_next_in =>
    rw [Metric.mem_ball]
    have hρ_lt1 : ρ < 1 := by
      rw [hρ, div_lt_one (by linarith only [ha_pos] : (0 : ℝ) < 1 + a)]
      linarith only [ha_pos]
    exact (nesterovStep_lookahead_dist_lt f η ρ hη_pos hρ_pos hρ_lt1 m_star (r₀ / 9) sn
      hx_ball_r09 (h_sn1_dist.trans_lt (by linarith only [hx'_ball_r09]))).trans_le
        (by linarith only [hr₀_pos])

/-- **State-based Lyapunov contraction along `nesterovSeqGen`.**

Generalization of `lyapunov_contraction` (Main.lean) to arbitrary initial
`NesterovState`, supporting nonzero initial velocity. -/
theorem lyapunov_contraction_gen
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Parameters
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ' : ℝ) (hμ' : 0 < μ')
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt1 : θ < 1)
    (η : ℝ) (hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    (ρ : ℝ) (hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    -- S = argmin set
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Nearest-point projection
    (π : E d → E d)
    (_hπ_in_S : ∀ x, π x ∈ S)
    (_hπ_proj : ∀ x ∈ S, π x = x)
    -- Gradient vanishes on S
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    -- Tangent projector P = Dπ(m⋆)
    (P : E d →L[ℝ] E d)
    -- Base point
    (m_star : E d) (hm_star : m_star ∈ S)
    -- ε from `local_fiberwise_geometry`
    (ε : ℝ) (hε_pos : 0 < ε) (hε_bound : ε * η ≤ Real.sqrt (μ' * η))
    (hμη_lt1 : μ' * η < 1)
    -- Strong aiming on U₊ (from `local_fiberwise_geometry`)
    (U_plus : Set (E d))
    (hU_open : IsOpen U_plus)
    (hm_star_Up : m_star ∈ U_plus)
    -- Local smoothness on U₊
    (hf_diff_on : DifferentiableOn ℝ f U_plus)
    (hf_lip : LipschitzOnWith L (gradient f) U_plus)
    (hStrAim : ∀ x ∈ U_plus,
      @inner ℝ _ _ (gradient f x) (x - π x) ≥
        f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2)
    -- Hessian lower bound on U₊ (from `local_fiberwise_geometry`)
    (hHess_lower : ∀ x ∈ U_plus, ∀ ξ : E d,
      hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2)
    -- Normal Hessian on projection fibers: Dπ(π x) · e = 0 → e lies in normal space
    (_hπ_kills_normal : ∀ x ∈ U_plus,
      fderiv ℝ π (π x) (x - π x) = 0)
    -- P is self-adjoint (orthogonal projector property)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    -- P is idempotent (orthogonal projector property)
    (hP_idem : ∀ x : E d, P (P x) = P x)
    -- Segment estimate (from D²f ≽ -εI and C² regularity):
    --   ⟨∇f(x), x - z⟩ ≥ f(x) - f(z) - ε/2 · ‖x - z‖²
    (hSegment : ∀ x z : E d, x ∈ U_plus → z ∈ U_plus →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • z + t • x ∈ U_plus) →
      @inner ℝ _ _ (gradient f x) (x - z) ≥
        f x - f z - ε / 2 * ‖x - z‖ ^ 2)
    -- Total perturbation absorption (curvature + projector-freezing error)
    -- δ_curv = curvature perturbation, proj_err = a·|⟨g, Pe⟩| from projector freezing
    -- R_abs is the energy/spatial radius: iterates must be in B(m⋆, R_abs) with Ln ≤ R_abs².
    (R_abs : ℝ) (hR_abs : 0 < R_abs)
    (h_curv_absorb : ∀ (s₀ : NesterovState d) (n : ℕ),
      (nesterovSeqGen f η ρ s₀ n).x ∈ Metric.ball m_star R_abs →
      (nesterovSeqGen f η ρ s₀ n).lookahead η ∈ Metric.ball m_star R_abs →
      lyapunovOfState P μ' π f η (nesterovSeqGen f η ρ s₀ n) ≤ R_abs ^ 2 →
      let sn := nesterovSeqGen f η ρ s₀ n
      let gn := gradient f (sn.lookahead η)
      let en := sn.lookahead η - π (sn.lookahead η)
      let ξn := curvatureErrorOfState (↑P) π f η ρ sn
      let un1 := auxVarOfState P μ' π η (nesterovStep f η ρ sn)
      let wn := un1 - Real.sqrt μ' • ξn
      let δ_curv := Real.sqrt μ' * @inner ℝ _ _ wn ξn +
                    (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2
      let a := Real.sqrt (μ' * η)
      let Ln := lyapunovOfState P μ' π f η sn
      let proj_err := a * |@inner ℝ _ _ gn (P en)|
      δ_curv + proj_err ≤ θ * a * Ln)
    :
    -- Conclusion: ∃ Ω, R (independent of starting point) such that contraction holds
    ∃ (Ω Ω_plus : Set (E d)) (R : ℝ),
      IsOpen Ω ∧ IsOpen Ω_plus ∧ 0 < R ∧
      m_star ∈ Ω ∧ Ω ⊆ Ω_plus ∧ Ω_plus ⊆ U_plus ∧
      -- For all starting points and iterations with the right preconditions
      ∀ (s₀ : NesterovState d) (n : ℕ),
        let s := nesterovSeqGen f η ρ s₀ n
        let s' := nesterovSeqGen f η ρ s₀ (n + 1)
        let Ln := lyapunovOfState P μ' π f η s
        let Ln' := lyapunovOfState P μ' π f η s'
        let a := Real.sqrt (μ' * η)
        s.x ∈ Ω → s.lookahead η ∈ Ω → Ln ≤ R ^ 2 →
        -- Contraction
        Ln' ≤ (1 - (1 - θ) * a) * Ln ∧
        -- Next iterates in Ω⁺
        s'.x ∈ Ω_plus ∧ s'.lookahead η ∈ Ω_plus := by
  obtain ⟨Ω, Ω_plus, R, hΩ, hΩp, hR, hm, hsub, hsubp, h⟩ :=
    lyapunov_contraction_of_state f L hL μ' hμ' θ hθ_pos hθ_lt1 η hη hη_pos ρ hρ S hM_argmin
      π hgrad_zero P m_star hm_star ε hε_pos hε_bound hμη_lt1 U_plus hU_open hm_star_Up
      hf_diff_on hf_lip hStrAim hHess_lower hP_self_adj hP_idem hSegment R_abs hR_abs
  exact ⟨Ω, Ω_plus, R, hΩ, hΩp, hR, hm, hsub, hsubp,
    fun s₀ n => h (nesterovSeqGen f η ρ s₀ n) (h_curv_absorb s₀ n)⟩

end PLAcceleratedNesterovLean
