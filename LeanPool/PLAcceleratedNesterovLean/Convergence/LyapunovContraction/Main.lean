/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction.GenMain


/-!
# Lyapunov Contraction

After shrinking the neighborhood Ω and the energy radius R, one step of the
modified Nesterov scheme contracts the Lyapunov function by a factor 1 - a/2,
where a = √(μ'·η).
-/

@[expose] public section


noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


/-- **Lyapunov contraction.**

After shrinking Ω and R if necessary, whenever x_n, x'_n ∈ Ω and L_n ≤ R²:
  L_{n+1} ≤ (1 - (1-θ)·a) · L_n
and x_{n+1}, x'_{n+1} ∈ Ω⁺.

The budget-split parameter θ ∈ (0,1) controls what fraction of the contraction
rate a is consumed by perturbation absorption. When θ = 1/2 this gives (1 - a/2).
-/
theorem lyapunov_contraction
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
    (h_curv_absorb : ∀ (x₁ : E d) (n : ℕ),
      (nesterovSeq f η ρ x₁ n).x ∈ Metric.ball m_star R_abs →
      (nesterovSeq f η ρ x₁ n).lookahead η ∈ Metric.ball m_star R_abs →
      lyapunov P μ' π f η ρ x₁ n ≤ R_abs ^ 2 →
      let sn := nesterovSeq f η ρ x₁ n
      let gn := gradient f (sn.lookahead η)
      let en := sn.lookahead η - π (sn.lookahead η)
      let ξn := curvatureError (↑P) π f η ρ x₁ n
      let un1 := auxVar P μ' π f η ρ x₁ (n + 1)
      let wn := un1 - Real.sqrt μ' • ξn
      let δ_curv := Real.sqrt μ' * @inner ℝ _ _ wn ξn +
                    (Real.sqrt μ') ^ 2 / 2 * ‖ξn‖ ^ 2
      let a := Real.sqrt (μ' * η)
      let Ln := lyapunov P μ' π f η ρ x₁ n
      let proj_err := a * |@inner ℝ _ _ gn (P en)|
      δ_curv + proj_err ≤ θ * a * Ln)
    :
    -- Conclusion: ∃ Ω, R (independent of starting point) such that contraction holds
    ∃ (Ω Ω_plus : Set (E d)) (R : ℝ),
      IsOpen Ω ∧ IsOpen Ω_plus ∧ 0 < R ∧
      m_star ∈ Ω ∧ Ω ⊆ Ω_plus ∧ Ω_plus ⊆ U_plus ∧
      -- For all starting points and iterations with the right preconditions
      ∀ (x₁ : E d) (n : ℕ),
        let s := nesterovSeq f η ρ x₁ n
        let s' := nesterovSeq f η ρ x₁ (n + 1)
        let Ln := lyapunov P μ' π f η ρ x₁ n
        let Ln' := lyapunov P μ' π f η ρ x₁ (n + 1)
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
    fun x₁ n => h (nesterovSeq f η ρ x₁ n) (h_curv_absorb x₁ n)⟩

end PLAcceleratedNesterovLean
