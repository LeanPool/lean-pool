/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Complex differentiability in several variables implies `C^∞`

Mathlib proves that a complex differentiable function of one complex variable on an open
set is analytic (`DifferentiableOn.analyticOnNhd`), hence `C^∞`. This file proves the
corresponding smoothness statement for maps `f : E → F` with `E` a finite-dimensional
complex normed space and `F` a complex Banach space.

The argument only uses one-variable Cauchy estimates along complex lines:

* `norm_fderiv_le_of_forall_norm_le`: if `f` is complex differentiable and bounded by `C`
  on `ball z R`, then `‖fderiv ℂ f z‖ ≤ C / r` for `0 < r < R`.
* `differentiableAt_of_tendstoUniformlyOn_ball`: a uniform limit on a ball of complex
  differentiable functions is complex differentiable at the centre (Weierstrass), obtained
  from the Cauchy estimate and `hasFDerivAt_of_tendstoUniformlyOnFilter`.
* `differentiableOn_fderiv_apply_of_isOpen`: for fixed `v`, `z ↦ fderiv ℂ f z v` is the
  locally uniform limit of the difference quotients `(n+1) • (f (z + (n+1)⁻¹ • v) - f z)`,
  hence complex differentiable.
* `contDiffOn_of_differentiableOn_complex`: induction on the order, using
  `contDiffOn_succ_iff_fderiv_of_isOpen` and `contDiffOn_clm_apply`.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Cauchy estimate for the Fréchet derivative of a complex differentiable map bounded on
a ball. -/
theorem norm_fderiv_le_of_forall_norm_le {f : E → F} {z : E} {R C r : ℝ}
    (hf : DifferentiableOn ℂ f (ball z R)) (hC : ∀ w ∈ ball z R, ‖f w‖ ≤ C)
    (hr : 0 < r) (hrR : r < R) :
    ‖fderiv ℂ f z‖ ≤ C / r := by
  have hzR : z ∈ ball z R := mem_ball_self (hr.trans hrR)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hzR)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hC0 hr.le) fun v hv => ?_
  set g : ℂ → F := fun ζ => f (z + ζ • v) with hg
  have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ r → z + ζ • v ∈ ball z R := fun ζ hζ => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one]; linarith
  have hline : ∀ ζ : ℂ, HasDerivAt (fun ζ : ℂ => z + ζ • v) v ζ := fun ζ => by
    simpa using ((hasDerivAt_id ζ).smul_const v).const_add z
  have hgd : ∀ ζ : ℂ, ‖ζ‖ ≤ r → DifferentiableAt ℂ g ζ := fun ζ hζ =>
    (hf.differentiableAt (isOpen_ball.mem_nhds (hmem ζ hζ))).comp ζ (hline ζ).differentiableAt
  have hdiff : DiffContOnCl ℂ g (ball 0 r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball (0 : ℂ) hr.ne']
    intro ζ hζ
    exact (hgd ζ (by simpa using hζ)).differentiableWithinAt
  have hderiv : deriv g 0 = fderiv ℂ f z v := by
    have h0 : HasFDerivAt f (fderiv ℂ f z) ((fun ζ : ℂ => z + ζ • v) 0) := by
      simpa using (hf.differentiableAt (isOpen_ball.mem_nhds hzR)).hasFDerivAt
    exact (h0.comp_hasDerivAt (0 : ℂ) (hline 0)).deriv
  have hsphere : ∀ ζ ∈ sphere (0 : ℂ) r, ‖g ζ‖ ≤ C := fun ζ hζ =>
    hC _ (hmem ζ (by simp_all))
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff hsphere
  rwa [hderiv] at this

/-- Weierstrass theorem in several variables: a uniform limit on a ball of complex
differentiable maps is complex differentiable at the centre of the ball. -/
theorem differentiableAt_of_tendstoUniformlyOn_ball [CompleteSpace F]
    {g : ℕ → E → F} {G : E → F} {x : E} {R : ℝ} (hR : 0 < R)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (g n) (ball x R))
    (hu : TendstoUniformlyOn g G atTop (ball x R)) : DifferentiableAt ℂ G x := by
  have hR2 : 0 < R / 2 := half_pos hR
  have hsub : ∀ w ∈ ball x (R / 2), ball w (R / 2) ⊆ ball x R := fun w hw =>
    ball_subset_ball' (by rw [mem_ball] at hw; linarith)
  have hcauchy : UniformCauchySeqOn (fun n => fderiv ℂ (g n)) atTop (ball x (R / 2)) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hu' := hu.uniformCauchySeqOn
    rw [Metric.uniformCauchySeqOn_iff] at hu'
    obtain ⟨N₁, hN₁⟩ := hu' (ε * (R / 4) / 2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hd
    refine ⟨max N₁ N₂, fun m hm n hn w hw => ?_⟩
    have hdm := (hN₂ m (le_of_max_le_right hm)).mono (hsub w hw)
    have hdn := (hN₂ n (le_of_max_le_right hn)).mono (hsub w hw)
    have hwm : DifferentiableAt ℂ (g m) w := hdm.differentiableAt (ball_mem_nhds w hR2)
    have hwn : DifferentiableAt ℂ (g n) w := hdn.differentiableAt (ball_mem_nhds w hR2)
    rw [dist_eq_norm, ← fderiv_sub hwm hwn]
    calc ‖fderiv ℂ (fun y => g m y - g n y) w‖ ≤ (ε * (R / 4) / 2) / (R / 4) :=
          norm_fderiv_le_of_forall_norm_le (hdm.sub hdn)
            (fun y hy => by
              rw [← dist_eq_norm]
              exact (hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn) y
                (hsub w hw hy)).le)
            (by positivity) (by linarith)
      _ < ε := by field_simp; linarith
  have hlim : ∀ w ∈ ball x (R / 2), Tendsto (fun n => fderiv ℂ (g n) w) atTop
      (𝓝 (limUnder atTop fun n => fderiv ℂ (g n) w)) := fun w hw =>
    (hcauchy.cauchySeq hw).tendsto_limUnder
  have hTU := hcauchy.tendstoUniformlyOn_of_tendsto hlim
  have hf' := hTU.tendstoUniformlyOnFilter.mono_right
    (le_principal_iff.2 (ball_mem_nhds x hR2))
  have hf : ∀ᶠ p : ℕ × E in atTop ×ˢ 𝓝 x,
      HasFDerivAt (g p.1) (fderiv ℂ (g p.1) p.2) p.2 := by
    filter_upwards [hd.prod_mk (ball_mem_nhds x hR)] with p hp
    exact (hp.1.differentiableAt (isOpen_ball.mem_nhds hp.2)).hasFDerivAt
  have hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n => g n y) atTop (𝓝 (G y)) :=
    eventually_of_mem (ball_mem_nhds x hR) fun y hy => hu.tendsto_at hy
  exact (hasFDerivAt_of_tendstoUniformlyOnFilter hf' hf hfg).differentiableAt

/-- A complex differentiable map has locally bounded Fréchet derivative on an open set. -/
theorem exists_ball_forall_norm_fderiv_le {f : E → F} {U : Set E}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) {z₀ : E} (hz₀ : z₀ ∈ U) :
    ∃ δ > 0, ball z₀ δ ⊆ U ∧ ∃ L, ∀ w ∈ ball z₀ δ, ‖fderiv ℂ f w‖ ≤ L := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hcont : ContinuousAt f z₀ := (hf.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  obtain ⟨σ, hσ, hσf⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  set ρ' := min ρ σ
  have hρ' : 0 < ρ' := lt_min hρ hσ
  have hρ'U : ball z₀ ρ' ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hρU
  refine ⟨ρ' / 2, by positivity, (ball_subset_ball (by linarith)).trans hρ'U,
    (‖f z₀‖ + 1) / (ρ' / 4), fun w hw => ?_⟩
  have hsub : ball w (ρ' / 2) ⊆ ball z₀ ρ' :=
    ball_subset_ball' (by rw [mem_ball] at hw; linarith)
  refine norm_fderiv_le_of_forall_norm_le (hf.mono (hsub.trans hρ'U)) (fun y hy => ?_)
    (by positivity) (by linarith)
  have hy' := mem_ball.1 (hsub hy)
  have h1 := hσf (lt_of_lt_of_le hy' (min_le_right _ _))
  rw [dist_eq_norm] at h1
  calc ‖f y‖ = ‖(f y - f z₀) + f z₀‖ := by rw [sub_add_cancel]
    _ ≤ ‖f y - f z₀‖ + ‖f z₀‖ := norm_add_le _ _
    _ ≤ ‖f z₀‖ + 1 := by linarith

/-- Local Lipschitz estimate for the Fréchet derivative, from the Cauchy estimate applied to
`y ↦ f (y + d) - f y`. -/
theorem norm_fderiv_add_sub_le {f : E → F} {z₀ : E} {δ L : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball z₀ δ)) (hL : ∀ w ∈ ball z₀ δ, ‖fderiv ℂ f w‖ ≤ L)
    {w d : E} (hw : w ∈ ball z₀ (δ / 4)) (hd : ‖d‖ < δ / 4) :
    ‖fderiv ℂ f (w + d) - fderiv ℂ f w‖ ≤ L * ‖d‖ / (δ / 4) := by
  have hdiff : ∀ y ∈ ball z₀ δ, DifferentiableAt ℂ f y := fun y hy =>
    hf.differentiableAt (isOpen_ball.mem_nhds hy)
  have hlip : ∀ y ∈ ball z₀ δ, ∀ y' ∈ ball z₀ δ, ‖f y' - f y‖ ≤ L * ‖y' - y‖ :=
    fun y hy y' hy' => (convex_ball z₀ δ).norm_image_sub_le_of_norm_fderiv_le hdiff hL hy hy'
  rw [mem_ball] at hw
  have hA : ∀ y ∈ ball w (δ / 2), y ∈ ball z₀ δ ∧ y + d ∈ ball z₀ δ := fun y hy => by
    rw [mem_ball] at hy
    rw [mem_ball, mem_ball]
    have : dist (y + d) y = ‖d‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    constructor
    · linarith [dist_triangle y w z₀]
    · linarith [dist_triangle (y + d) y z₀, dist_triangle y w z₀]
  have hshift : ∀ y ∈ ball w (δ / 2), DifferentiableAt ℂ (fun y => f (y + d)) y := fun y hy =>
    DifferentiableAt.comp (g := f) y (hdiff _ (hA y hy).2) (differentiableAt_id.add_const d)
  have hφ : DifferentiableOn ℂ (fun y => f (y + d) - f y) (ball w (δ / 2)) := fun y hy =>
    ((hshift y hy).sub (hdiff _ (hA y hy).1)).differentiableWithinAt
  have hw' : w ∈ ball w (δ / 2) := mem_ball_self (by positivity)
  have heq : fderiv ℂ (fun y => f (y + d) - f y) w = fderiv ℂ f (w + d) - fderiv ℂ f w := by
    rw [fderiv_fun_sub (hshift w hw') (hdiff _ (hA w hw').1), fderiv_comp_add_right]
  rw [← heq]
  refine norm_fderiv_le_of_forall_norm_le hφ (fun y hy => ?_) (by positivity) (by linarith)
  have := hlip y (hA y hy).1 (y + d) (hA y hy).2
  rwa [add_sub_cancel_left] at this

/-- Second-order Taylor estimate for a complex differentiable map. -/
theorem norm_sub_sub_fderiv_le {f : E → F} {z₀ : E} {δ L : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball z₀ δ)) (hL : ∀ w ∈ ball z₀ δ, ‖fderiv ℂ f w‖ ≤ L)
    {z u : E} (hz : z ∈ ball z₀ (δ / 8)) (hu : ‖u‖ < δ / 8) :
    ‖f (z + u) - f z - fderiv ℂ f z u‖ ≤ L / (δ / 4) * ‖u‖ * ‖u‖ := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL z₀ (mem_ball_self hδ))
  rw [mem_ball] at hz
  have hs : ∀ y ∈ closedBall z ‖u‖, y ∈ ball z₀ δ ∧ ‖y - z‖ < δ / 4 := fun y hy => by
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball]
    constructor
    · linarith [dist_triangle y z z₀, dist_eq_norm y z]
    · linarith
  have hdiff : ∀ y ∈ closedBall z ‖u‖,
      DifferentiableAt ℂ (fun y => f y - fderiv ℂ f z y) y := fun y hy =>
    (hf.differentiableAt (isOpen_ball.mem_nhds (hs y hy).1)).sub
      (fderiv ℂ f z).differentiableAt
  have hzq : z ∈ ball z₀ (δ / 4) := by rw [mem_ball]; linarith
  have hbound : ∀ y ∈ closedBall z ‖u‖,
      ‖fderiv ℂ (fun y => f y - fderiv ℂ f z y) y‖ ≤ L / (δ / 4) * ‖u‖ := fun y hy => by
    rw [fderiv_fun_sub (hf.differentiableAt (isOpen_ball.mem_nhds (hs y hy).1))
      (fderiv ℂ f z).differentiableAt, ContinuousLinearMap.fderiv]
    have := norm_fderiv_add_sub_le hδ hf hL hzq (hs y hy).2
    rw [add_sub_cancel] at this
    rw [mem_closedBall, dist_eq_norm] at hy
    calc _ ≤ L * ‖y - z‖ / (δ / 4) := this
      _ ≤ L * ‖u‖ / (δ / 4) := by gcongr
      _ = L / (δ / 4) * ‖u‖ := by ring
  have hmem1 : z ∈ closedBall z ‖u‖ := mem_closedBall_self (norm_nonneg _)
  have hmem2 : z + u ∈ closedBall z ‖u‖ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have := (convex_closedBall z ‖u‖).norm_image_sub_le_of_norm_fderiv_le hdiff hbound hmem1 hmem2
  rw [add_sub_cancel_left] at this
  convert this using 2
  simp only [map_add]
  abel

/-- For fixed `v`, the directional derivative `z ↦ fderiv ℂ f z v` of a complex
differentiable map on an open set is complex differentiable there. It is the locally uniform
limit of the difference quotients `(n + 1) • (f (z + (n + 1)⁻¹ • v) - f z)`. -/
theorem differentiableOn_fderiv_apply_of_isOpen [CompleteSpace F] {f : E → F} {U : Set E}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (v : E) :
    DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U := by
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨δ, hδ, hδU, L, hL⟩ := exists_ball_forall_norm_fderiv_le hf hU hz₀
  have hfδ : DifferentiableOn ℂ f (ball z₀ δ) := hf.mono hδU
  set K := L / (δ / 4)
  have hK0 : 0 ≤ K :=
    div_nonneg ((norm_nonneg _).trans (hL z₀ (mem_ball_self hδ))) (by positivity)
  let c : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ)
  have hc : ∀ n, c n ≠ 0 := fun n => Nat.cast_ne_zero.2 n.succ_ne_zero
  have hcn : ∀ n, ‖c n‖ = (n : ℝ) + 1 := fun n => by
    simp only [c]; rw [Complex.norm_natCast]; push_cast; ring
  have hu_norm : ∀ n, ‖(c n)⁻¹ • v‖ = ‖v‖ / ((n : ℝ) + 1) := fun n => by
    rw [norm_smul, norm_inv, hcn, inv_mul_eq_div]
  obtain ⟨N, hN⟩ := exists_nat_gt (‖v‖ / (δ / 8))
  have hsmall : ∀ n ≥ N, ‖(c n)⁻¹ • v‖ < δ / 8 := fun n hn => by
    rw [hu_norm, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hN
    have : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    nlinarith
  refine differentiableAt_of_tendstoUniformlyOn_ball
    (g := fun n z => c n • (f (z + (c n)⁻¹ • v) - f z)) (R := δ / 8) (by positivity) ?_ ?_
  · filter_upwards [eventually_ge_atTop N] with n hn
    intro z hz
    have hz' : z ∈ ball z₀ δ := ball_subset_ball (by linarith) hz
    have hzv : z + (c n)⁻¹ • v ∈ ball z₀ δ := by
      rw [mem_ball] at hz ⊢
      have := hsmall n hn
      calc dist (z + (c n)⁻¹ • v) z₀ ≤ dist (z + (c n)⁻¹ • v) z + dist z z₀ :=
            dist_triangle _ _ _
        _ < δ := by rw [dist_eq_norm, add_sub_cancel_left]; linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.const_smul (DifferentiableAt.sub ?_ ?_) _
    · exact DifferentiableAt.comp (g := f) z (hfδ.differentiableAt (isOpen_ball.mem_nhds hzv))
        (differentiableAt_id.add_const _)
    · exact hfδ.differentiableAt (isOpen_ball.mem_nhds hz')
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_gt (K * ‖v‖ ^ 2 / ε)
    filter_upwards [eventually_ge_atTop (max N M)] with n hn z hz
    have hnN : N ≤ n := le_of_max_le_left hn
    have hnM : (M : ℝ) ≤ n := Nat.cast_le.2 (le_of_max_le_right hn)
    have htaylor := norm_sub_sub_fderiv_le hδ hfδ hL hz (hsmall n hnN)
    have heq : c n • (f (z + (c n)⁻¹ • v) - f z) - fderiv ℂ f z v =
        c n • (f (z + (c n)⁻¹ • v) - f z - fderiv ℂ f z ((c n)⁻¹ • v)) := by
      rw [map_smul, smul_sub (c n) _ ((c n)⁻¹ • _), smul_inv_smul₀ (hc n)]
    rw [dist_comm, dist_eq_norm, heq, norm_smul, hcn]
    rw [hu_norm] at htaylor
    have hpos : (0 : ℝ) < n + 1 := by positivity
    calc _ ≤ ((n : ℝ) + 1) * (K * (‖v‖ / (n + 1)) * (‖v‖ / (n + 1))) := by gcongr
      _ = K * ‖v‖ ^ 2 / (n + 1) := by field_simp
      _ < ε := by
        rw [div_lt_iff₀ hpos]
        rw [div_lt_iff₀ hε] at hM
        nlinarith [mul_le_mul_of_nonneg_right hnM hε.le]

/-- **Complex differentiability implies smoothness in several variables.** A map from a
finite-dimensional complex normed space to a complex Banach space which is complex
differentiable on an open set is `C^∞` (over `ℂ`) there. -/
theorem contDiffOn_of_differentiableOn_complex [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {U : Set E} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    ContDiffOn ℂ ∞ f U := by
  have key : ∀ n : ℕ, ∀ g : E → F, DifferentiableOn ℂ g U → ContDiffOn ℂ n g U := by
    intro n
    induction n with
    | zero => intro g hg; exact contDiffOn_zero.2 hg.continuousOn
    | succ n ih =>
      intro g hg
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨hg, by simp, ?_⟩
      exact contDiffOn_clm_apply.2 fun v =>
        ih _ (differentiableOn_fderiv_apply_of_isOpen hg hU v)
  exact contDiffOn_infty.2 fun n => key n f hf

/-- Real-smooth version of `contDiffOn_of_differentiableOn_complex`. -/
theorem contDiffOn_real_of_differentiableOn_complex [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {U : Set E} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ f U :=
  (contDiffOn_of_differentiableOn_complex hf hU).restrict_scalars ℝ

/-- Pointwise version of `contDiffOn_of_differentiableOn_complex`. -/
theorem contDiffAt_of_differentiableOn_complex [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {U : Set E} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) : ContDiffAt ℂ ∞ f x :=
  (contDiffOn_of_differentiableOn_complex hf hU).contDiffAt (hU.mem_nhds hx)

/-- Pointwise real-smooth version of `contDiffOn_of_differentiableOn_complex`. -/
theorem contDiffAt_real_of_differentiableOn_complex [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {U : Set E} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) : ContDiffAt ℝ ∞ f x :=
  (contDiffOn_real_of_differentiableOn_complex hf hU).contDiffAt (hU.mem_nhds hx)

end SGPT.Foundations.Analysis.FirstPass
