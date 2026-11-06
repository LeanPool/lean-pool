/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection.Defs
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.SegmentEstimate
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Step2
import LeanPool.PLAcceleratedNesterovLean.MorseBott.Bridge
import LeanPool.PLAcceleratedNesterovLean.MorseBott.Submanifold
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul


/-!
# Local Fiberwise Geometry from PL near M

Given a base point m⋆ ∈ M and any μ' ∈ (0, μ), there exists a fiber-saturated open
neighborhood U₊ of m⋆ with U₊ ⊂⊂ U, and ε > 0 with ε ≤ √(μ'/η), such that:

(a) Normal Hessian lower bound: ξᵀ D²f(x)ξ ≥ μ'‖ξ‖² for x ∈ U₊, ξ ∈ N_{π(x)}M
(b) Quadratic growth: f(x) - f⋆ ≥ (μ'/2) dist(x, M)²
(c) Strong aiming: ⟨∇f(x), x - π(x)⟩ ≥ f(x) - f⋆ + (μ'/2)‖x - π(x)‖²
(d) Hessian lower bound: D²f(x) ≽ -εI
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


/-- Fiber-path second derivative lower bound.

Given f C² on an open set V containing the segment {m + t·e | t ∈ ℝ},
the fiber path φ(t) = f(m + t·e) satisfies φ''(t) ≥ μ' * ‖e‖² for t ∈ [0,1],
where e = x − π(x) is a normal direction.
This is used for both quadratic growth and strong aiming. -/
private theorem fiber_path_hessian_lower_bound
    {d : ℕ} (f : E d → ℝ) (μ' : ℝ)
    (m e : E d)
    {V : Set (E d)} (hV : IsOpen V) (hf_C2 : ContDiffOn ℝ 2 f V)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc 0 1 → m + t • e ∈ V)
    (hbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → hessianQuadForm f (m + t • e) e ≥ μ' * ‖e‖ ^ 2) :
    let φ : ℝ → ℝ := fun t => f (m + t • e)
    ∀ t, 0 ≤ t → t ≤ 1 →
      deriv (deriv φ) t ≥ μ' * ‖e‖ ^ 2 := by
  intro φ t ht0 ht1
  have hf_at : ContDiffAt ℝ 2 f (m + t • e) :=
    hf_C2.contDiffAt (hV.mem_nhds (hseg t ⟨ht0, ht1⟩))
  rw [fiber_path_second_deriv f m e t hf_at]
  exact hbound t ht0 ht1
/-- Two nearest-point projections onto `S` agree on a tubular neighborhood `U`,
by uniqueness of the nearest point. -/
private theorem projection_eq_of_isTubular {d : ℕ} {S U : Set (E d)}
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U) {π π' : E d → E d}
    (hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hπ'_proj : ∀ x ∈ U, π' x ∈ S ∧ ‖x - π' x‖ = Metric.infDist x S) :
    ∀ x ∈ U, π x = π' x := by
  intro x hxU
  obtain ⟨p, hp, huniq⟩ := hTub_sub.uniqueProj x hxU
  exact (huniq (π x) (hπ_proj x hxU)).trans
    (huniq (π' x) ⟨(hπ'_proj x hxU).1,
      by rw [dist_eq_norm]; exact (hπ'_proj x hxU).2⟩).symm

/-- If `S` is locally a graph over `T` at `m` and `π'` is a map fixing `S` that is
differentiable at `m`, then `Dπ'(m)` fixes every tangent vector `w ∈ T`: differentiate
`π' ∘ γ = γ` along the curve `γ(t) = m + t w + ψ(t w)` in `S`. -/
private theorem fderiv_apply_eq_self_of_mem_tangent {d : ℕ} {S : Set (E d)} {m : E d}
    {T : Submodule ℝ (E d)} (hsub : IsLocalSubmanifoldAt S m T)
    {π' : E d → E d} (hπ'_fix : ∀ x ∈ S, π' x = x) (hπ_diff_m : DifferentiableAt ℝ π' m)
    {w : E d} (hw : w ∈ T) :
    fderiv ℝ π' m w = w := by
  obtain ⟨U_chart, hU_chart_nhds, ψ, hψ_C1, hψ0, hDψ0, hgraph⟩ := hsub.2
  set w_T : ↥T := ⟨w, hw⟩
  set γ : ℝ → E d :=
    fun t => m + t • w + (↑(ψ (t • w_T)) : E d)
  -- HasDerivAt γ w 0
  have hψ_diff : DifferentiableAt ℝ ψ 0 :=
    hψ_C1.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hβ : HasDerivAt (fun t : ℝ => t • w_T) w_T 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w_T
  have hψβ : HasDerivAt (fun t : ℝ => ψ (t • w_T)) 0 0 := by
    have h := hψ_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hβ (zero_smul ℝ w_T).symm
    rwa [hDψ0, zero_apply] at h
  have hγ_deriv : HasDerivAt γ w 0 := by
    have h1 : HasDerivAt (fun t : ℝ => m + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add m
    have h2 : HasDerivAt
        (fun t : ℝ => (↑(ψ (t • w_T)) : E d)) (0 : E d) 0 := by
      have h := (ContinuousLinearMap.hasFDerivAt
        T.orthogonal.subtypeL).comp_hasDerivAt (0 : ℝ) hψβ
      simp only [map_zero] at h
      exact h
    have h3 := h1.add h2
    rwa [add_zero] at h3
  -- γ(t) ∈ S for small t
  have hγ0 : γ 0 = m := by
    change m + (0 : ℝ) • w + (↑(ψ ((0 : ℝ) • w_T)) : E d) = m
    rw [zero_smul, zero_smul, hψ0]; simp only [add_zero, ZeroMemClass.coe_zero]
  have hγ_cont := hγ_deriv.continuousAt
  have hpre : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U_chart := by
    exact hγ_cont.preimage_mem_nhds (by rw [hγ0]; exact hU_chart_nhds)
  have hγ_in_S : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S := by
    filter_upwards [hpre] with t ht
    have hgr := (hgraph (γ t) ht).mpr
    apply hgr
    -- γ(t) - m = t•(w_T : E d) + ↑(ψ(t•w_T))
    have hγ_sub : γ t - m = t • (w_T : E d) + (↑(ψ (t • w_T)) : E d) := by
      simp only [γ]; abel
    have hψ_proj : T.orthogonalProjectionOnto (ψ (t • w_T) : E d) = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (ψ (t • w_T)).property
    have hw_perp_proj : Tᗮ.orthogonalProjectionOnto (w_T : E d) = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        (Submodule.le_orthogonal_orthogonal T w_T.property)
    rw [hγ_sub, map_add, map_smul, map_add, map_smul]
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self w_T,
      hψ_proj,
      add_zero,
      hw_perp_proj,
      smul_zero, zero_add,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (ψ (t • w_T))]
  -- Differentiate π' ∘ γ = γ to get fderiv ℝ π' m w = w
  have hπγ_eq : (π' ∘ γ) =ᶠ[𝓝 (0 : ℝ)] γ := by
    filter_upwards [hγ_in_S] with t ht
    exact hπ'_fix (γ t) ht
  have hπγ_deriv1 : HasDerivAt (π' ∘ γ) w 0 :=
    hπγ_eq.hasDerivAt_iff.mpr hγ_deriv
  have hπγ_deriv2 : HasDerivAt (π' ∘ γ) ((fderiv ℝ π' m) w) 0 :=
    hπ_diff_m.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ_deriv hγ0.symm
  exact hπγ_deriv2.unique hπγ_deriv1

/-- PL ⟹ Morse–Bott: at a minimizer `m ∈ S`, the Hessian quadratic form is at least
`μ‖ξ‖²` on normal directions `ξ ∈ ker Dπ(m)`. The Hessian kernel is the tangent space
of `S` (fixed by the self-adjoint `Dπ(m)`), so `ξ ⊥ ker H`, and the PL Rayleigh-quotient
bound (Rebjock & Boumal, Cor 2.17) applies. -/
private theorem normal_hessian_bound_at_minimizer {d : ℕ} (f : E d → ℝ) (μ : ℝ)
    (hμ : 0 < μ) {S U : Set (E d)} (hM_argmin : S = argminSet f)
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U)
    (hPL : PolyakLojasiewicz f μ U) (hf_C2 : ContDiffOn ℝ 2 f U) {π : E d → E d}
    (hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    {m : E d} (hmS : m ∈ S) {ξ : E d} (hξ_normal : fderiv ℝ π m ξ = 0) :
    hessianQuadForm f m ξ ≥ μ * ‖ξ‖ ^ 2 := by
  have hmin : ∀ y, f m ≤ f y := by rw [hM_argmin] at hmS; exact hmS
  have hmin_local : IsLocalMin f m := Filter.Eventually.of_forall hmin
  have hmU : m ∈ U := hTub_sub.subset hmS
  have hf_C2_at_m : ContDiffAt ℝ 2 f m :=
    hf_C2.contDiffAt (hTub_sub.isOpen.mem_nhds hmU)
  have hPL_ext : ExternalThm3.PolyakLojasiewicz f μ U :=
    ⟨hμ, fun x hxU => by
      have := hPL.2.2 x hxU
      rw [norm_mathlibGradient_eq_norm_fderiv] at this
      exact this⟩
  -- Canonical projection π' (differentiable, self-adjoint derivative) agreeing with π
  obtain ⟨π', hπ'_proj, hπ'_fix, _, _, _, _, _, hπ'_diff, hπ'_sa, _⟩ :=
    tubular_neighborhood_projection_Ed hTub_sub ⟨m, hmS⟩
  have hπ_ev : π =ᶠ[𝓝 m] π' :=
    Filter.eventually_of_mem (hTub_sub.isOpen.mem_nhds hmU)
      (projection_eq_of_isTubular hTub_sub hπ_proj hπ'_proj)
  have hfderiv_eq : fderiv ℝ π m = fderiv ℝ π' m := hπ_ev.fderiv_eq
  -- PL → MuPL → S = localMinSet f m is a submanifold with tangent space ker H
  have hMuPL : MuPL f μ m :=
    ExternalThm3.pl_to_muPL f μ U m
      (by rw [hM_argmin] at hmS; exact hmS)
      (hTub_sub.isOpen.mem_nhds hmU) hPL_ext
  have hsub' : IsLocalSubmanifoldAt (localMinSet f m) m (hessianKer f m) :=
    MuPL.implies_submanifold f μ m hμ hf_C2_at_m hmin_local hMuPL
  have hS_eq : S = localMinSet f m := by
    ext x; constructor
    · intro hxS; rw [hM_argmin] at hxS
      exact ⟨Filter.Eventually.of_forall hxS, le_antisymm (hxS m) (hmin x)⟩
    · intro ⟨_, hfx⟩; rw [hM_argmin]
      intro z; linarith [hmin z]
  rw [← hS_eq] at hsub'
  -- ξ ⊥ ker H: ⟪w, ξ⟫ = ⟪Dπ'(m) w, ξ⟫ = ⟪w, Dπ(m) ξ⟫ = 0
  have hξ_hess_orth : ξ ∈ (hessianKer f m).orthogonal := by
    rw [(hessianKer f m).mem_orthogonal]
    intro w hw
    have hPw : fderiv ℝ π' m w = w :=
      fderiv_apply_eq_self_of_mem_tangent hsub' hπ'_fix (hπ'_diff m hmS) hw
    rw [← hPw, hπ'_sa m hmS w ξ, ← hfderiv_eq, hξ_normal, inner_zero_right]
  have hm_ext : m ∈ ExternalThm3.argminSet f := by
    rw [hM_argmin] at hmS
    exact hmS
  have hbound := ExternalThm3.hessianQuadForm_bound f μ U m ξ
    hf_C2_at_m hPL_ext hm_ext (hTub_sub.isOpen.mem_nhds hmU) hξ_hess_orth
  have hgrad_fun : ExternalThm3.gradient f = gradient f := by
    funext x
    exact externalThm3_gradient_eq_gradient f x
  simpa [ExternalThm3.hessianQuadForm, hessianQuadForm, hgrad_fun] using hbound

/-- The Hessian quadratic form `(x, ξ) ↦ ξᵀ D²f(x) ξ` is continuous on `U × E`
when `f` is C² on the open set `U`. -/
private theorem hessianQuadForm_continuousOn {d : ℕ} {f : E d → ℝ} {U : Set (E d)}
    (hU_is_open : IsOpen U) (hf_C2 : ContDiffOn ℝ 2 f U) :
    ContinuousOn (fun p : E d × E d => hessianQuadForm f p.1 p.2) (U ×ˢ Set.univ) := by
  have hfderiv_C1 : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    hf_C2.fderiv_of_isOpen hU_is_open (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
  have hgrad_C1 : ContDiffOn ℝ 1 (gradient f) U :=
    ((InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv.contDiff.of_le
      le_top).comp_contDiffOn hfderiv_C1
  have hDgrad_cont : ContinuousOn (fderiv ℝ (gradient f)) U :=
    (hgrad_C1.fderiv_of_isOpen hU_is_open
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn
  simp only [hessianQuadForm]
  exact ((hDgrad_cont.comp continuousOn_fst (fun p hp => hp.1)).clm_apply
    continuousOn_snd).inner continuousOn_snd

/-- A lower bound `a` for the Hessian quadratic form on unit vectors satisfying a
scaling-invariant condition `P` extends to `a‖ξ‖²` for all `ξ` satisfying `P`. -/
private theorem hessianQuadForm_ge_of_unit_sphere {d : ℕ} {f : E d → ℝ} {x : E d} {a : ℝ}
    {P : E d → Prop} (hP_smul : ∀ (c : ℝ) (ξ : E d), P ξ → P (c • ξ))
    (hunit : ∀ ξ₀ ∈ Metric.sphere (0 : E d) 1, P ξ₀ → hessianQuadForm f x ξ₀ ≥ a)
    {ξ : E d} (hξP : P ξ) :
    hessianQuadForm f x ξ ≥ a * ‖ξ‖ ^ 2 := by
  by_cases hξ : ξ = 0
  · subst hξ; simp only [hessianQuadForm, map_zero, inner_self_eq_norm_sq_to_K, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, ge_iff_le, le_refl]
  · have hξ_norm_pos : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
    set c := ‖ξ‖ with hc_def
    set ξ₀ := c⁻¹ • ξ with hξ₀_def
    have hξ₀_norm : ‖ξ₀‖ = 1 := by
      rw [hξ₀_def, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (ne_of_gt hξ_norm_pos)]
    have hξ₀_sphere : ξ₀ ∈ Metric.sphere (0 : E d) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]; exact hξ₀_norm
    have hbound₀ : hessianQuadForm f x ξ₀ ≥ a := hunit ξ₀ hξ₀_sphere (hP_smul _ _ hξP)
    -- ξ = c • ξ₀
    have hξ_eq : ξ = c • ξ₀ := by
      rw [hξ₀_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hξ_norm_pos), one_smul]
    -- Homogeneity: hessianQuadForm f x ξ = c² * hessianQuadForm f x ξ₀
    have hhomog : hessianQuadForm f x ξ = c ^ 2 * hessianQuadForm f x ξ₀ := by
      conv_lhs => rw [hξ_eq]
      simp only [hessianQuadForm, map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hhomog]
    exact (mul_comm a (c ^ 2)).trans_le
      (mul_le_mul_of_nonneg_left hbound₀ (sq_nonneg c))

/-- Local compactness of `S` near `m⋆`: some closed ball piece of `S` is compact. -/
private theorem exists_compact_local_piece {d : ℕ} {S U : Set (E d)}
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U) {m_star : E d}
    (hm_star : m_star ∈ S) :
    ∃ r > 0, IsCompact (S ∩ Metric.closedBall m_star r) := by
  obtain ⟨r_U, hr_U_pos, hr_U_sub⟩ :=
    Metric.isOpen_iff.mp hTub_sub.isOpen m_star (hTub_sub.subset hm_star)
  refine ⟨r_U / 2, half_pos hr_U_pos, hTub_sub.isCompact_inter_closedBall ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hr_U_pos)).trans hr_U_sub

/-- Step 2a: the normal Hessian bound `≥ μ` on `S` extends, with the slack `μ' < μ`,
to a neighborhood `V₁` of `m⋆` (compactness of `S_loc × sphere` + thickening). -/
private theorem exists_normal_hessian_neighborhood {d : ℕ} (f : E d → ℝ) {μ μ' : ℝ}
    (hμ'_lt : μ' < μ) {S U : Set (E d)}
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U) (hf_C2 : ContDiffOn ℝ 2 f U)
    {π : E d → E d} (hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (h_normal_hess_M : ∀ m ∈ S, ∀ ξ : E d,
      fderiv ℝ π m ξ = 0 → hessianQuadForm f m ξ ≥ μ * ‖ξ‖ ^ 2)
    {m_star : E d} (hm_star : m_star ∈ S) :
    ∃ V₁ : Set (E d), IsOpen V₁ ∧ m_star ∈ V₁ ∧
      ∀ x ∈ V₁, ∀ ξ : E d,
        fderiv ℝ π (π x) ξ = 0 →
        hessianQuadForm f x ξ ≥ μ' * ‖ξ‖ ^ 2 := by
  have hU_is_open : IsOpen U := hTub_sub.isOpen
  set g : E d × E d → ℝ := fun p => hessianQuadForm f p.1 p.2 with hg_def
  have hg_contOn : ContinuousOn g (U ×ˢ Set.univ) :=
    hessianQuadForm_continuousOn hU_is_open hf_C2
  -- ── Local compactness: S ∩ closedBall(m⋆, r_loc) is compact ──
  obtain ⟨r_loc, hr_loc_pos, hS_loc_compact⟩ := exists_compact_local_piece hTub_sub hm_star
  set S_loc := S ∩ Metric.closedBall m_star r_loc
  have hSphere_compact' : IsCompact (Metric.sphere (0 : E d) 1) := isCompact_sphere 0 1
  have hSlxS_compact := hS_loc_compact.prod hSphere_compact'
  have hSlxS_closed := hSlxS_compact.isClosed
  have hSlxS_sub : S_loc ×ˢ Metric.sphere (0 : E d) 1 ⊆ U ×ˢ Set.univ :=
    Set.prod_mono (Set.inter_subset_left.trans hTub_sub.subset) (Set.subset_univ _)
  -- ── N = {(m,ξ) ∈ S_loc × sphere | hessianQuadForm f m ξ ≥ μ} is compact ──
  set N : Set (E d × E d) :=
    (S_loc ×ˢ Metric.sphere (0 : E d) 1) ∩ g ⁻¹' Set.Ici μ with hN_def
  have hN_compact : IsCompact N :=
    hSlxS_compact.of_isClosed_subset
      ((hg_contOn.mono hSlxS_sub).preimage_isClosed_of_isClosed hSlxS_closed isClosed_Ici)
      Set.inter_subset_left
  -- ── V_nbhd = (U ×ˢ univ) ∩ {(x,ξ) | hessianQuadForm f x ξ > μ'} is open ──
  set V_nbhd : Set (E d × E d) :=
    (U ×ˢ Set.univ) ∩ g ⁻¹' Set.Ioi μ' with hV_def
  have hV_open : IsOpen V_nbhd :=
    hg_contOn.isOpen_inter_preimage (hU_is_open.prod isOpen_univ) isOpen_Ioi
  have hN_sub : N ⊆ V_nbhd := by
    intro ⟨x, ξ⟩ ⟨hmem, hge⟩
    exact ⟨hSlxS_sub hmem, by
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Ici] at hge ⊢; linarith⟩
  -- ── Thickening: ∃ δ > 0, thickening δ N ⊆ V_nbhd ──
  obtain ⟨δ, hδ_pos, hthick⟩ := hN_compact.exists_thickening_subset_open hV_open hN_sub
  -- ── V₁ = U ∩ ball(m⋆, min(δ, r_loc/2)) ──
  set δ' := min δ (r_loc / 2) with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min hδ_pos (half_pos hr_loc_pos)
  refine ⟨U ∩ Metric.ball m_star δ',
          hTub_sub.isOpen.inter Metric.isOpen_ball,
          ⟨hTub_sub.subset hm_star, Metric.mem_ball_self hδ'_pos⟩,
          fun x ⟨hxU, hx_near⟩ ξ hξ_normal => ?_⟩
  refine hessianQuadForm_ge_of_unit_sphere (P := fun ξ => fderiv ℝ π (π x) ξ = 0)
    (fun c ξ h => by simp only [map_smul, h, smul_zero]) (fun ξ₀ hξ₀_sphere hξ₀_normal => ?_)
    hξ_normal
  have hξ₀_norm : ‖ξ₀‖ = 1 := mem_sphere_zero_iff_norm.mp hξ₀_sphere
  -- π(x) ∈ S, and dist(x, m_star) < δ' ≤ r_loc/2, so π(x) ∈ S_loc
  have hπ_in_S : π x ∈ S := (hπ_proj x hxU).1
  have hx_dist : dist x m_star < δ' := Metric.mem_ball.mp hx_near
  have hinfDist_le : Metric.infDist x S ≤ dist x m_star :=
    Metric.infDist_le_dist_of_mem hm_star
  have hπ_in_S_loc : π x ∈ S_loc := by
    refine ⟨hπ_in_S, Metric.mem_closedBall.mpr ?_⟩
    have h1 := dist_triangle (π x) x m_star
    rw [dist_comm (π x) x] at h1
    have h2 : dist x (π x) = Metric.infDist x S := (hπ_proj x hxU).2
    linarith [min_le_right δ (r_loc / 2)]
  -- hessianQuadForm f (π x) ξ₀ ≥ μ (by h_normal_hess_M)
  have hge_mu : hessianQuadForm f (π x) ξ₀ ≥ μ := by
    have := h_normal_hess_M (π x) hπ_in_S ξ₀ hξ₀_normal
    rw [hξ₀_norm, one_pow, mul_one] at this; exact this
  have hπξ_in_N : (π x, ξ₀) ∈ N := by
    refine ⟨Set.mk_mem_prod hπ_in_S_loc hξ₀_sphere, ?_⟩
    simp only [Set.mem_preimage, Set.mem_Ici]; exact hge_mu
  -- dist((x, ξ₀), (π(x), ξ₀)) = dist(x, π(x)) < δ
  have hdist_pair : dist (x, ξ₀) (π x, ξ₀) = dist x (π x) := by
    simp only [Prod.dist_eq, dist_self, dist_nonneg, sup_of_le_left]
  have hx_near_π : dist x (π x) = Metric.infDist x S := (hπ_proj x hxU).2
  have h_in_thick : (x, ξ₀) ∈ Metric.thickening δ N := by
    rw [Metric.mem_thickening_iff]
    exact ⟨(π x, ξ₀), hπξ_in_N, by
      rw [hdist_pair, hx_near_π]; linarith [min_le_left δ (r_loc / 2)]⟩
  have hmem := (hthick h_in_thick).2
  simp only [Set.mem_preimage, Set.mem_Ioi] at hmem
  exact le_of_lt hmem

/-- Step 2b: `D²f ≽ 0` on `S` extends to `D²f ≽ -ε₀ I` on a neighborhood `V₂` of `m⋆`
(tube lemma on `S_loc × sphere`). -/
private theorem exists_hessian_lower_neighborhood {d : ℕ} (f : E d → ℝ) {ε₀ : ℝ}
    (hε₀_pos : 0 < ε₀) {S U : Set (E d)}
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U) (hf_C2 : ContDiffOn ℝ 2 f U)
    (h_hess_psd_M : ∀ m ∈ S, ∀ ξ : E d, hessianQuadForm f m ξ ≥ 0)
    {m_star : E d} (hm_star : m_star ∈ S) :
    ∃ V₂ : Set (E d), IsOpen V₂ ∧ m_star ∈ V₂ ∧
      ∀ x ∈ V₂, ∀ ξ : E d,
        hessianQuadForm f x ξ ≥ -ε₀ * ‖ξ‖ ^ 2 := by
  have hU_is_open : IsOpen U := hTub_sub.isOpen
  set g₂ : E d × E d → ℝ := fun p => hessianQuadForm f p.1 p.2 with hg₂_def
  have hg₂_contOn : ContinuousOn g₂ (U ×ˢ Set.univ) :=
    hessianQuadForm_continuousOn hU_is_open hf_C2
  -- S_loc₂ = S ∩ closedBall(m⋆, r_loc₂) is compact (local compactness)
  obtain ⟨r_loc₂, hr_loc₂_pos, hS_loc₂_compact⟩ := exists_compact_local_piece hTub_sub hm_star
  set S_loc₂ := S ∩ Metric.closedBall m_star r_loc₂
  have hSphere_compact : IsCompact (Metric.sphere (0 : E d) 1) := isCompact_sphere 0 1
  -- hessianQuadForm ≥ 0 on S × sphere (PSD at minimizers)
  have hg_K : ∀ p ∈ S ×ˢ Metric.sphere (0 : E d) 1,
      (0 : ℝ) ≤ g₂ p := by
    rintro ⟨x, ξ⟩ ⟨hx, -⟩
    exact h_hess_psd_M x hx ξ
  -- V_prod = (U ×ˢ univ) ∩ {p | g₂ p > -ε₀} is open, contains S × sphere
  set V_prod : Set (E d × E d) :=
    (U ×ˢ Set.univ) ∩ g₂ ⁻¹' Set.Ioi (-ε₀) with hVp_def
  have hV_prod_open : IsOpen V_prod :=
    hg₂_contOn.isOpen_inter_preimage (hU_is_open.prod isOpen_univ) isOpen_Ioi
  have hK_V_prod : S ×ˢ Metric.sphere (0 : E d) 1 ⊆ V_prod := by
    intro ⟨x, ξ⟩ ⟨hx, hξ⟩
    exact ⟨⟨hTub_sub.subset hx, Set.mem_univ _⟩,
      by simp only [Set.mem_preimage, Set.mem_Ioi]; linarith [hg_K (x, ξ) ⟨hx, hξ⟩]⟩
  have hK_V_prod_loc : S_loc₂ ×ˢ Metric.sphere (0 : E d) 1 ⊆ V_prod :=
    (Set.prod_mono Set.inter_subset_left (le_refl _)).trans hK_V_prod
  have hg_bound : ∀ p ∈ V_prod, (0 : ℝ) - ε₀ ≤ g₂ p := by
    intro p ⟨_, hmem⟩
    simp only [Set.mem_preimage, Set.mem_Ioi] at hmem; linarith
  -- Apply generalized_tube_lemma with S_loc₂ (local compactness)
  obtain ⟨V₂, W, hV₂_open, _, hSloc_V₂, hSphere_W, hVW⟩ :=
    generalized_tube_lemma hS_loc₂_compact hSphere_compact hV_prod_open hK_V_prod_loc
  have hm_V₂ : m_star ∈ V₂ :=
    hSloc_V₂ ⟨hm_star, Metric.mem_closedBall_self (le_of_lt hr_loc₂_pos)⟩
  refine ⟨V₂, hV₂_open, hm_V₂, fun x hx ξ => ?_⟩
  -- (x, ξ₀) ∈ V₂ ×ˢ W ⊆ V_prod for unit ξ₀, so hessianQuadForm f x ξ₀ ≥ -ε₀
  refine hessianQuadForm_ge_of_unit_sphere (P := fun _ => True) (fun _ _ _ => trivial)
    (fun ξ₀ hξ₀_sphere _ => ?_) trivial
  have := hg_bound (x, ξ₀) (hVW (Set.mk_mem_prod hx (hSphere_W hξ₀_sphere)))
  simp only [g₂] at this
  linarith

/-- Step 3: a ball `U₊` around `m⋆` with compact closure inside an open `W ⊆ U`
whose fiber segments `[π(x), x]` stay in `W`. -/
private theorem exists_fiber_saturated_ball {d : ℕ} {S U W : Set (E d)} {π : E d → E d}
    (hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hW_open : IsOpen W) (hW_U : W ⊆ U) {m_star : E d} (hm_star : m_star ∈ S)
    (hm_W : m_star ∈ W) :
    ∃ U_plus : Set (E d), IsOpen U_plus ∧ m_star ∈ U_plus ∧
      IsCompact (closure U_plus) ∧ closure U_plus ⊆ W ∧ Convex ℝ U_plus ∧
      ∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → π x + t • (x - π x) ∈ W := by
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hW_open m_star hm_W
  -- Take U₊ = B(m⋆, r/2)
  refine ⟨Metric.ball m_star (r / 2), Metric.isOpen_ball,
          Metric.mem_ball_self (by linarith), Metric.isBounded_ball.isCompact_closure, ?_,
          convex_ball _ _, ?_⟩
  -- closure (ball m⋆ (r/2)) ⊆ W
  · intro y hy
    have h_in_cl : y ∈ Metric.closedBall m_star (r / 2) :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hy
    have : dist y m_star < r :=
      lt_of_le_of_lt (Metric.mem_closedBall.mp h_in_cl) (by linarith)
    exact hball_sub (Metric.mem_ball.mpr this)
  -- fiber segments from ball(m_star, r/2) stay in ball(m_star, r) ⊆ W
  · intro x hx t ht0 ht1
    have hx_ball_r : x ∈ Metric.ball m_star r :=
      Metric.ball_subset_ball (by linarith : r / 2 ≤ r) hx
    have hxU : x ∈ U := hW_U (hball_sub hx_ball_r)
    have hπx_ball : π x ∈ Metric.ball m_star r := by
      rw [Metric.mem_ball]
      have h1 : dist x (π x) < r / 2 := by
        calc dist x (π x) = Metric.infDist x S := (hπ_proj x hxU).2
          _ ≤ dist x m_star := Metric.infDist_le_dist_of_mem hm_star
          _ < r / 2 := Metric.mem_ball.mp hx
      have h2 : dist x m_star < r / 2 := Metric.mem_ball.mp hx
      linarith [dist_triangle (π x) x m_star, dist_comm (π x) x]
    apply hball_sub
    have hy_eq : π x + t • (x - π x) = (1 - t) • π x + t • x := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [hy_eq]
    exact convex_ball m_star r hπx_ball hx_ball_r (by linarith) ht0 (by linarith)

/-- Regularity of the fiber path `φ(t) = f(m + t e)` needed by the Step 2 helpers. -/
private theorem fiber_path_regularity {d : ℕ} (f : E d → ℝ) (m e : E d) {U : Set (E d)}
    (hU : IsOpen U) (hf_C2 : ContDiffOn ℝ 2 f U)
    (hseg_U : ∀ t : ℝ, t ∈ Set.Icc 0 1 → m + t • e ∈ U) :
    ContinuousOn (fun t : ℝ => f (m + t • e)) (Set.Icc 0 1) ∧
      DifferentiableOn ℝ (fun t : ℝ => f (m + t • e)) (Set.Ioo 0 1) ∧
      ContinuousOn (deriv fun t : ℝ => f (m + t • e)) (Set.Icc 0 1) ∧
      DifferentiableOn ℝ (deriv fun t : ℝ => f (m + t • e)) (Set.Ioo 0 1) := by
  set φ : ℝ → ℝ := fun t => f (m + t • e) with hφ_def
  have hφ_C2at := fiber_path_C2at_on_segment f m e hU hf_C2 hseg_U
  have h_eq : deriv φ = fun s => fderiv ℝ φ s 1 := by
    ext s; exact fderiv_apply_one_eq_deriv.symm
  refine ⟨fun t ht => (hφ_C2at t ht).continuousAt.continuousWithinAt,
    fun t ht => ((hφ_C2at t (Set.Ioo_subset_Icc_self ht)).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableWithinAt, ?_, ?_⟩
  · intro t ht
    have hfda := (hφ_C2at t ht).fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    rw [h_eq]; exact (hfda.continuousAt.clm_apply continuousAt_const).continuousWithinAt
  · intro t ht
    have hfda := (hφ_C2at t (Set.Ioo_subset_Icc_self ht)).fderiv_right
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    have hfda_diff := hfda.differentiableAt (show (1 : WithTop ℕ∞) ≠ 0 by norm_num)
    rw [h_eq]; exact (hfda_diff.clm_apply (differentiableAt_const _)).differentiableWithinAt

/-- Derivative of the fiber path `t ↦ f(m + t e)` at `s`: `⟨∇f(m + s e), e⟩`. -/
private theorem fiber_path_deriv_eq_inner {d : ℕ} (f : E d → ℝ) (m e : E d) (s : ℝ)
    (hf : DifferentiableAt ℝ f (m + s • e)) :
    deriv (fun t : ℝ => f (m + t • e)) s = @inner ℝ _ _ (gradient f (m + s • e)) e := by
  have hg : HasDerivAt (fun t : ℝ => m + t • e) e s := by
    simpa using ((hasDerivAt_id s).smul_const e).const_add m
  have key := hf.hasFDerivAt.comp_hasDerivAt s hg
  simp only [Function.comp_def] at key
  rw [key.deriv]
  exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := m + s • e) (y := e)).symm

/-- Steps (b)–(c): along a fiber `t ↦ m + t(x − m)` from a minimizer `m` with
second derivative `≥ μ'‖x − m‖²`, the function has quadratic growth and satisfies
the strong aiming inequality. -/
private theorem fiber_growth_and_aiming {d : ℕ} (f : E d → ℝ) {U : Set (E d)}
    (hU : IsOpen U) (hf_C2 : ContDiffOn ℝ 2 f U) {μ' : ℝ} {m x : E d}
    (hm_min : ∀ y, f m ≤ f y) (hgrad_m : gradient f m = 0)
    (hseg_U : ∀ t : ℝ, t ∈ Set.Icc 0 1 → m + t • (x - m) ∈ U)
    (hbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      hessianQuadForm f (m + t • (x - m)) (x - m) ≥ μ' * ‖x - m‖ ^ 2) :
    f x - fStar f ≥ μ' / 2 * ‖x - m‖ ^ 2 ∧
      @inner ℝ _ _ (gradient f x) (x - m) ≥ f x - fStar f + μ' / 2 * ‖x - m‖ ^ 2 := by
  set e := x - m with he_def
  set φ : ℝ → ℝ := fun t => f (m + t • e) with hφ_def
  -- φ(0) = f(m) = f⋆ since m minimizes f
  have hφ0 : φ 0 = fStar f := by
    simp only [hφ_def, zero_smul, add_zero]
    unfold fStar
    exact le_antisymm (le_ciInf hm_min)
      (ciInf_le ⟨f m, fun _ ⟨y, hy⟩ => hy ▸ hm_min y⟩ m)
  have hme1 : m + (1 : ℝ) • e = x := by simp only [he_def, one_smul, add_sub_cancel]
  have hφ1 : φ 1 = f x := by simp only [hφ_def, hme1]
  have hf_diff_on : DifferentiableOn ℝ f U := hf_C2.differentiableOn two_ne_zero
  have hm_U : m + (0 : ℝ) • e ∈ U := hseg_U 0 ⟨le_rfl, zero_le_one⟩
  have hx_U : m + (1 : ℝ) • e ∈ U := hseg_U 1 ⟨zero_le_one, le_rfl⟩
  -- φ'(0) = ⟨∇f(m), e⟩ = 0 and φ'(1) = ⟨∇f(x), e⟩
  have hφ'0 : deriv φ 0 = 0 := by
    rw [fiber_path_deriv_eq_inner f m e 0 (hf_diff_on.differentiableAt (hU.mem_nhds hm_U)),
      zero_smul, add_zero, hgrad_m, inner_zero_left]
  have hφ'1 : deriv φ 1 = @inner ℝ _ _ (gradient f x) e := by
    rw [fiber_path_deriv_eq_inner f m e 1 (hf_diff_on.differentiableAt (hU.mem_nhds hx_U)),
      hme1]
  obtain ⟨hφ_cont, hφ_diffon, hφ'_cont, hφ'_diffon⟩ :=
    fiber_path_regularity f m e hU hf_C2 hseg_U
  have hφ''_lb : ∀ t, 0 ≤ t → t ≤ 1 → deriv (deriv φ) t ≥ μ' * ‖e‖ ^ 2 :=
    fiber_path_hessian_lower_bound f μ' m e hU hf_C2 hseg_U hbound
  have hgrowth := quadratic_growth_from_hessian φ (μ' * ‖e‖ ^ 2)
    hφ_cont hφ_diffon hφ'_cont hφ'_diffon hφ'0 hφ''_lb
  have hsa := strong_aiming_from_hessian φ (μ' * ‖e‖ ^ 2)
    hφ_cont hφ_diffon hφ'_cont hφ'_diffon hφ'0 hφ''_lb
  rw [hφ1, hφ0] at hgrowth
  rw [hφ1, hφ0, hφ'1] at hsa
  have : μ' * ‖e‖ ^ 2 / 2 = μ' / 2 * ‖e‖ ^ 2 := by ring
  constructor <;> linarith


/-- **Local fiberwise geometry from PL near M.**

Fix m⋆ ∈ M and any μ' ∈ (0, μ). There exists a fiber-saturated open neighborhood U₊
of m⋆ with U₊ ⊂⊂ U, and ε > 0 with ε ≤ √(μ'/η), satisfying:
  (a) normal Hessian bound ≥ μ' in normal directions,
  (b) quadratic growth of f above f⋆,
  (c) strong aiming inequality,
  (d) global Hessian bound ≥ -ε.
-/
private theorem localFiberwiseGeometryProof
    -- Dimensions
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Smoothness parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ)
    -- Slack parameter μ' ∈ (0, μ), used to leave room for local perturbations.
    (μ' : ℝ) (hμ' : 0 < μ') (hμ'_lt : μ' < μ)
    -- Step size
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    -- The minimizer set S = argmin f
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Tubular neighborhood U ⊃ S (open set with unique projection + C² submanifold structure)
    (U : Set (E d))
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U)
    -- PL condition on U
    (hPL : PolyakLojasiewicz f μ U)
    -- f is C² on U
    (hf_C2 : ContDiffOn ℝ 2 f U)
    -- Nearest-point projection on U
    (π : E d → E d)
    (hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    -- Gradient vanishes on S
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    -- Base point on M
    (m_star : E d) (hm_star : m_star ∈ S) :
    -- Conclusion: ∃ neighborhood U₊ and ε with all four properties for μ'
    ∃ (U_plus : Set (E d)) (ε : ℝ),
      -- U₊ is open, contains m⋆, and U₊ ⊂⊂ U (compact closure inside U)
      IsOpen U_plus ∧ m_star ∈ U_plus ∧
      IsCompact (closure U_plus) ∧ closure U_plus ⊆ U ∧
      Convex ℝ U_plus ∧
      -- ε > 0 with ε ≤ √(μ/(4η))
      0 < ε ∧ ε ≤ Real.sqrt (μ' / η) ∧
      -- (a) Normal Hessian lower bound: for ξ in ker(Dπ(π x))
      (∀ x ∈ U_plus, ∀ ξ : E d,
        fderiv ℝ π (π x) ξ = 0 →
        hessianQuadForm f x ξ ≥ μ' * ‖ξ‖ ^ 2) ∧
      -- (b) Quadratic growth
      (∀ x ∈ U_plus,
        f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2) ∧
      -- (c) Strong aiming
      (∀ x ∈ U_plus,
        @inner ℝ _ _ (gradient f x) (x - π x) ≥
          f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2) ∧
      -- (d) Hessian lower bound D²f(x) ≽ -εI
      (∀ x ∈ U_plus, ∀ ξ : E d,
        hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2) ∧
      -- (e) Normal Hessian ≥ μ at m_star (full μ bound at the base point)
      (∀ ξ : E d,
        fderiv ℝ π m_star ξ = 0 →
        hessianQuadForm f m_star ξ ≥ μ * ‖ξ‖ ^ 2) ∧
      -- (f) Fiber segments from U₊ stay in U
      (∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        π x + t • (x - π x) ∈ U) := by
  /-
    PROOF OUTLINE (`local_fiberwise_geometry`):
    1. PL ⟹ Morse-Bott: on M, normal Hessian ξᵀD²f(m)ξ ≥ μ‖ξ‖².
    2. By continuity of D²f and local compactness near m⋆, extend to ≥ μ' on a
       neighborhood V₁ (using the gap μ - μ' > 0).
    3. D²f(m) ≽ 0 at minimizers + continuity ⟹ D²f(x) ≽ -ε₀I on V₂.
    4. Construct fiber-saturated U₊ ⊂⊂ V₁ ∩ V₂ ∩ U.
    5. Quadratic growth and strong aiming by integrating φ(t) = f(m+te)
       along fibers (Step2 helpers).
  -/
  have hU_is_open : IsOpen U := hTub_sub.isOpen
  -- ================================================================
  -- Step 1: Hessian bounds on M (from PL + Morse-Bott structure)
  -- ================================================================
  -- PL ⟹ Morse-Bott: normal Hessian ξᵀD²f(m)ξ ≥ μ‖ξ‖² on M
  have h_normal_hess_M : ∀ m ∈ S, ∀ ξ : E d,
      fderiv ℝ π m ξ = 0 →
      hessianQuadForm f m ξ ≥ μ * ‖ξ‖ ^ 2 := fun m hmS ξ hξ_normal =>
    normal_hessian_bound_at_minimizer f μ hμ hM_argmin hTub_sub hPL hf_C2 hπ_proj hmS
      hξ_normal
  -- D²f(m) ≽ 0 at global minimizers (PSD, by hessian_psd_at_minimizer)
  have h_hess_psd_M : ∀ m ∈ S, ∀ ξ : E d,
      hessianQuadForm f m ξ ≥ 0 := by
    intro m hmS ξ
    have hmin : ∀ y, f m ≤ f y := by rw [hM_argmin] at hmS; exact hmS
    have hmU : m ∈ U := hTub_sub.subset hmS
    have hf_m_C2 : ContDiffAt ℝ 2 f m :=
      hf_C2.contDiffAt (hU_is_open.mem_nhds hmU)
    exact hessian_psd_at_minimizer f m hmin hf_m_C2 ξ
  -- ================================================================
  -- Step 2: Extend bounds to neighborhoods by continuity + compactness
  -- ================================================================
  -- V₁: neighborhood of m⋆ where normal Hessian ≥ μ'‖ξ‖² (uses the gap μ - μ' > 0)
  obtain ⟨V₁, hV₁_open, hm_V₁, h_normal_V₁⟩ :=
    exists_normal_hessian_neighborhood f hμ'_lt hTub_sub hf_C2 hπ_proj h_normal_hess_M hm_star
  -- Choose ε₀ = min 1 (√(μ'/η)), which satisfies 0 < ε₀ ≤ √(μ'/η)
  let ε₀ : ℝ := min 1 (Real.sqrt (μ' / η))
  have hε₀_pos : 0 < ε₀ := by
    exact lt_min one_pos (Real.sqrt_pos_of_pos (div_pos hμ' hη_pos))
  have hε₀_le : ε₀ ≤ Real.sqrt (μ' / η) := min_le_right _ _
  -- V₂: neighborhood of m⋆ where D²f(x) ≽ -ε₀·I
  obtain ⟨V₂, hV₂_open, hm_V₂, h_hess_V₂⟩ :=
    exists_hessian_lower_neighborhood f hε₀_pos hTub_sub hf_C2 h_hess_psd_M hm_star
  -- ================================================================
  -- Step 3: Construct fiber-saturated U₊ ⊂⊂ V₁ ∩ V₂ ∩ U
  -- ================================================================
  obtain ⟨U_plus, hU_open, hm_in, hU_compact, hU_cl_W, hU_convex, hU_fiber_W⟩ :=
    exists_fiber_saturated_ball hπ_proj ((hV₁_open.inter hV₂_open).inter hU_is_open)
      Set.inter_subset_right hm_star ⟨⟨hm_V₁, hm_V₂⟩, hTub_sub.subset hm_star⟩
  have hU_cl_U : closure U_plus ⊆ U := fun y hy => (hU_cl_W hy).2
  have hU_fiber_U : ∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      π x + t • (x - π x) ∈ U := fun x hx t ht0 ht1 => (hU_fiber_W x hx t ht0 ht1).2
  obtain ⟨π', hπ'_proj, _, _, _, _, hπ'_fiber_dist, hπ'_normal, _, _, _⟩ :=
    tubular_neighborhood_projection_Ed hTub_sub ⟨m_star, hm_star⟩
  have hπ_eq_U : ∀ x ∈ U, π x = π' x :=
    projection_eq_of_isTubular hTub_sub hπ_proj hπ'_proj
  have hfderiv_normal : ∀ x ∈ U_plus, fderiv ℝ π (π x) (x - π x) = 0 := by
    intro x hx
    have hxU : x ∈ U := hU_cl_U (subset_closure hx)
    have hm_S := (hπ_proj x hxU).1
    have hmU : π x ∈ U := hTub_sub.subset hm_S
    have hπ_eq_nhds : π =ᶠ[𝓝 (π x)] π' :=
      Filter.eventually_of_mem (hTub_sub.isOpen.mem_nhds hmU) hπ_eq_U
    rw [hπ_eq_nhds.fderiv_eq, hπ_eq_U x hxU]
    exact hπ'_normal x hxU
  have hπ_fiber_const : ∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      π (π x + t • (x - π x)) = π x := by
    intro x hx t ht0 ht1
    have hxU : x ∈ U := hU_cl_U (subset_closure hx)
    have hm_S := (hπ_proj x hxU).1
    set y := π x + t • (x - π x) with hy_def
    -- Local fiber-in-U proof: convexity of ball ensures y ∈ U
    have hyU : y ∈ U := hU_fiber_U x hx t ht0 ht1
    have hy_conv : y = (1 - t) • π' x + t • x := by
      rw [hy_def, hπ_eq_U x hxU]; simp only [smul_sub, sub_smul, one_smul]; abel
    have h_realizes : ‖y - π x‖ = Metric.infDist y S := by
      rw [hy_conv, hπ_eq_U x hxU]; exact hπ'_fiber_dist x hxU t ⟨ht0, ht1⟩
    obtain ⟨p, hp, huniq⟩ := hTub_sub.uniqueProj y hyU
    exact (huniq (π y) (hπ_proj y hyU)).trans
      (huniq (π x) ⟨hm_S, by rw [dist_eq_norm]; exact h_realizes⟩).symm
  -- Fiber path φ(t) = f(π(x) + t·(x − π(x))): quadratic growth and strong aiming,
  -- since φ''(t) = eᵀ D²f(π x + t e) e ≥ μ'‖e‖² (e = x − π(x) is normal and the
  -- fiber point lies in V₁ with the same projection π(x)).
  have hfiber : ∀ x ∈ U_plus,
      f x - fStar f ≥ μ' / 2 * ‖x - π x‖ ^ 2 ∧
        @inner ℝ _ _ (gradient f x) (x - π x) ≥
          f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2 := by
    intro x hx
    have hxU : x ∈ U := hU_cl_U (subset_closure hx)
    have hm_S : π x ∈ S := (hπ_proj x hxU).1
    have hm_min : ∀ y, f (π x) ≤ f y := by rw [hM_argmin] at hm_S; exact hm_S
    exact fiber_growth_and_aiming f hU_is_open hf_C2 hm_min (hgrad_zero _ hm_S)
      (fun t ⟨ht0, ht1⟩ => hU_fiber_U x hx t ht0 ht1)
      (fun t ht0 ht1 => h_normal_V₁ _ (hU_fiber_W x hx t ht0 ht1).1.1 (x - π x) (by
        rw [hπ_fiber_const x hx t ht0 ht1]
        exact hfderiv_normal x hx))
  -- ================================================================
  -- Step 4: Assemble the conclusion
  -- ================================================================
  refine ⟨U_plus, ε₀, hU_open, hm_in, hU_compact, hU_cl_U, hU_convex,
          hε₀_pos, hε₀_le, ?_, ?_, ?_, ?_, ?_, hU_fiber_U⟩
  -- (a) Normal Hessian lower bound: inherited from V₁
  · exact fun x hx ξ hξ => h_normal_V₁ x (hU_cl_W (subset_closure hx)).1.1 ξ hξ
  -- (b) Quadratic growth: dist(x, S) = ‖x − π(x)‖ by the projection property
  · intro x hx
    have hxU : x ∈ U := hU_cl_U (subset_closure hx)
    rw [← (hπ_proj x hxU).2, dist_eq_norm]
    exact (hfiber x hx).1
  -- (c) Strong aiming
  · exact fun x hx => (hfiber x hx).2
  -- (d) Hessian lower bound D²f(x) ≽ −ε₀·I: inherited from V₂
  · exact fun x hx ξ => h_hess_V₂ x (hU_cl_W (subset_closure hx)).1.2 ξ
  -- (e) Normal Hessian ≥ μ at m_star (from Step 1)
  · exact h_normal_hess_M m_star hm_star


/-- Public theorem wrapper for `localFiberwiseGeometryProof`. -/
theorem local_fiberwise_geometry
    -- Dimensions
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Smoothness parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ)
    -- Slack parameter μ' ∈ (0, μ), used to leave room for local perturbations.
    (μ' : ℝ) (hμ' : 0 < μ') (hμ'_lt : μ' < μ)
    -- Step size
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    -- The minimizer set S = argmin f
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Tubular neighborhood U ⊃ S (open set with unique projection + C² submanifold structure)
    (U : Set (E d))
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U)
    -- PL condition on U
    (hPL : PolyakLojasiewicz f μ U)
    -- f is C² on U
    (hf_C2 : ContDiffOn ℝ 2 f U)
    -- Nearest-point projection on U
    (π : E d → E d)
    (hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    -- Gradient vanishes on S
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    -- Base point on M
    (m_star : E d) (hm_star : m_star ∈ S) :
    -- Conclusion: ∃ neighborhood U₊ and ε with all four properties for μ'
    ∃ (U_plus : Set (E d)) (ε : ℝ),
      -- U₊ is open, contains m⋆, and U₊ ⊂⊂ U (compact closure inside U)
      IsOpen U_plus ∧ m_star ∈ U_plus ∧
      IsCompact (closure U_plus) ∧ closure U_plus ⊆ U ∧
      Convex ℝ U_plus ∧
      -- ε > 0 with ε ≤ √(μ/(4η))
      0 < ε ∧ ε ≤ Real.sqrt (μ' / η) ∧
      -- (a) Normal Hessian lower bound: for ξ in ker(Dπ(π x))
      (∀ x ∈ U_plus, ∀ ξ : E d,
        fderiv ℝ π (π x) ξ = 0 →
        hessianQuadForm f x ξ ≥ μ' * ‖ξ‖ ^ 2) ∧
      -- (b) Quadratic growth
      (∀ x ∈ U_plus,
        f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2) ∧
      -- (c) Strong aiming
      (∀ x ∈ U_plus,
        @inner ℝ _ _ (gradient f x) (x - π x) ≥
          f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2) ∧
      -- (d) Hessian lower bound D²f(x) ≽ -εI
      (∀ x ∈ U_plus, ∀ ξ : E d,
        hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2) ∧
      -- (e) Normal Hessian ≥ μ at m_star (full μ bound at the base point)
      (∀ ξ : E d,
        fderiv ℝ π m_star ξ = 0 →
        hessianQuadForm f m_star ξ ≥ μ * ‖ξ‖ ^ 2) ∧
      -- (f) Fiber segments from U₊ stay in U
      (∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        π x + t • (x - π x) ∈ U) := by
  exact localFiberwiseGeometryProof (d := d) (_hd := _hd) (f := f) (L := L) (_hL := _hL) (μ := μ)
    (hμ := hμ) (μ' := μ') (hμ' := hμ') (hμ'_lt := hμ'_lt) (η := η) (_hη := _hη) (hη_pos := hη_pos)
    (S := S) (hM_argmin := hM_argmin) (U := U) (hTub_sub := hTub_sub) (hPL := hPL) (hf_C2 := hf_C2)
    (π := π) (hπ_proj := hπ_proj) (hgrad_zero := hgrad_zero) (m_star := m_star) (hm_star := hm_star)

end PLAcceleratedNesterovLean
