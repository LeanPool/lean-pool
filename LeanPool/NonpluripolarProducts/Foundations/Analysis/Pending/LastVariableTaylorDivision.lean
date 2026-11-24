/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Taylor division by `t ^ d` in the last variable

Let `h : E × ℂ → ℂ` be complex differentiable on `ball 0 δ ×ˢ ball 0 R` and `0 < ρ < R`.
For fixed `z`, the Cauchy integrals
`lastCoeff h ρ k z = (2πi)⁻¹ ∮_{|ζ| = ρ} h (z, ζ) / ζ ^ (k + 1) dζ`
are the Taylor coefficients of `h (z, ·)` at `0`, and `lastQuot h ρ d` is
`(h (z, t) - ∑_{k < d} lastCoeff h ρ k z * t ^ k) / t ^ d`, extended by `lastCoeff h ρ d z`
at `t = 0`. We prove:

* `differentiableOn_lastCoeff`: `z ↦ lastCoeff h ρ k z` is holomorphic. By the Cauchy formula
  for derivatives it equals `(k!)⁻¹ ∂ₜᵏ h (z, 0)`, and the iterated partial derivatives
  `x ↦ fderiv ℂ (·) x (0, 1)` are holomorphic by
  `FirstPass.differentiableOn_fderiv_apply_of_isOpen` (no finite-dimensionality needed).
* `eq_lastQuot_mul_add`: `h = lastQuot h ρ d * t ^ d + ∑_{k < d} lastCoeff h ρ k z * t ^ k`.
* `differentiableOn_lastQuot`: `lastQuot h ρ d` is jointly holomorphic. Away from `t = 0` it is
  an explicit quotient. Near `(z₀, 0)` it is the sum of the series
  `∑ₖ lastCoeff h ρ (k + d) z * t ^ k`, which converges uniformly on a small ball by the Cauchy
  estimates (using a tube-lemma bound for `h` on `ball z₀ ε × sphere 0 ρ`) and the Weierstrass
  M-test, so `FirstPass.differentiableAt_of_tendstoUniformlyOn_ball` applies.
* `norm_lastCoeff_le`, `exists_norm_lastQuot_le`: sup-norm estimates `M / ρ ^ k` and `C * M`,
  with `C = (1 + ∑_{k < d} (R / ρ) ^ k) / ρ ^ d`. For `ρ ≤ ‖t‖` the bound is direct; for
  `‖t‖ < ρ` it follows from the maximum modulus principle on `closedBall 0 ρ`.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.Pending

open Complex Metric Set Filter
open scoped Real Topology Nat

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `k`-th Taylor coefficient of `h (z, ·)` at `0`, computed on the circle of radius `ρ`. -/
def lastCoeff (h : E × ℂ → ℂ) (ρ : ℝ) (k : ℕ) (z : E) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, ρ), h (z, ζ) / ζ ^ (k + 1)

/-- `h` minus its Taylor polynomial of degree `< d` in the last variable, divided by `t^d`. -/
def lastQuot (h : E × ℂ → ℂ) (ρ : ℝ) (d : ℕ) (x : E × ℂ) : ℂ :=
  if x.2 = 0 then lastCoeff h ρ d x.1
  else (h x - ∑ k ∈ Finset.range d, lastCoeff h ρ k x.1 * x.2 ^ k) / x.2 ^ d

/-! ### One-variable Cauchy theory -/

/-- The Cauchy coefficient of a one-variable function on the circle of radius `ρ`. -/
private def coeff1 (f : ℂ → ℂ) (ρ : ℝ) (k : ℕ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, ρ), f ζ / ζ ^ (k + 1)

private lemma norm_coeff1_le {f : ℂ → ℂ} {ρ B : ℝ} (hρ : 0 < ρ)
    (hB : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖f ζ‖ ≤ B) (k : ℕ) :
    ‖coeff1 f ρ k‖ ≤ B / ρ ^ k := by
  have := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun ζ => f ζ / ζ ^ (k + 1)) (c := 0) (C := B / ρ ^ (k + 1)) hρ.le
    (fun ζ hζ => by
      have hn : ‖ζ‖ = ρ := by simpa using hζ
      rw [norm_div, norm_pow, hn]
      gcongr
      exact hB ζ hζ)
  rw [smul_eq_mul] at this
  calc ‖coeff1 f ρ k‖ ≤ ρ * (B / ρ ^ (k + 1)) := this
    _ = B / ρ ^ k := by field_simp; ring

private lemma coeff1_eq_iteratedDeriv {f : ℂ → ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (k : ℕ) :
    coeff1 f ρ k = (k ! : ℂ)⁻¹ * iteratedDeriv k f 0 := by
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have := Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    (c := 0) hρ k countable_empty (hf.mono hcl).continuousOn
    (fun z hz => hf.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hρR.le hz.1)))
  simp only [sub_zero, smul_eq_mul] at this
  unfold coeff1
  have hint : (∮ ζ in C(0, ρ), f ζ / ζ ^ (k + 1)) = ∮ ζ in C(0, ρ), 1 / ζ ^ (k + 1) * f ζ := by
    congr 1; funext ζ; ring
  rw [hint, this]
  have : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

private lemma hasSum_coeff1 {f : ℂ → ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) {t : ℂ} (ht : t ∈ ball (0 : ℂ) ρ) :
    HasSum (fun k => coeff1 f ρ k * t ^ k) (f t) := by
  have := Complex.hasSum_taylorSeries_on_ball (hf.mono (ball_subset_ball hρR.le)) ht
  simp only [sub_zero, smul_eq_mul] at this
  have e : (fun k => coeff1 f ρ k * t ^ k) =
      fun n : ℕ => (n ! : ℂ)⁻¹ * (t ^ n * iteratedDeriv n f 0) := by
    funext k; rw [coeff1_eq_iteratedDeriv hρ hρR hf]; ring
  rw [e]; exact this

private lemma coeff1_zero {f : ℂ → ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) : coeff1 f ρ 0 = f 0 := by
  have := hasSum_coeff1 hρ hρR hf (mem_ball_self hρ)
  refine this.unique ?_ |>.symm
  convert hasSum_single (f := fun k => coeff1 f ρ k * (0 : ℂ) ^ k) 0 ?_ using 1
  · simp
  · intro b hb; simp [hb]

/-! ### Holomorphy of the coefficients -/

/-- Iterated partial derivatives in the last variable. -/
private def lastIter (h : E × ℂ → ℂ) : ℕ → E × ℂ → ℂ
  | 0 => h
  | j + 1 => fun x => fderiv ℂ (lastIter h j) x (0, 1)

private lemma differentiableOn_lastIter {h : E × ℂ → ℂ} {U : Set (E × ℂ)} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) : ∀ j, DifferentiableOn ℂ (lastIter h j) U
  | 0 => hh
  | j + 1 => FirstPass.differentiableOn_fderiv_apply_of_isOpen
      (differentiableOn_lastIter hU hh j) hU (0, 1)

private lemma iteratedDeriv_eq_lastIter {h : E × ℂ → ℂ} {δ R : ℝ}
    (hh : DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R)) :
    ∀ (j : ℕ), ∀ z ∈ ball (0 : E) δ, ∀ t ∈ ball (0 : ℂ) R,
      iteratedDeriv j (fun t => h (z, t)) t = lastIter h j (z, t)
  | 0, z, _, t, _ => by simp [lastIter]
  | j + 1, z, hz, t, ht => by
    have hU : IsOpen (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j (fun t => h (z, t)) =ᶠ[𝓝 t] fun s => lastIter h j (z, s) :=
      eventually_of_mem (isOpen_ball.mem_nhds ht) fun s hs =>
        iteratedDeriv_eq_lastIter hh j z hz s hs
    rw [heq.deriv_eq]
    have hd : HasFDerivAt (lastIter h j) (fderiv ℂ (lastIter h j) (z, t)) (z, t) :=
      ((differentiableOn_lastIter hU hh j).differentiableAt
        (hU.mem_nhds ⟨hz, ht⟩)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℂ => (z, s)) ((0 : E), (1 : ℂ)) t :=
      (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
    exact (hd.comp_hasDerivAt t hl).deriv

private lemma lastCoeff_eq_lastIter {h : E × ℂ → ℂ} {δ ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R)) (k : ℕ) {z : E}
    (hz : z ∈ ball (0 : E) δ) :
    lastCoeff h ρ k z = (k ! : ℂ)⁻¹ * lastIter h k (z, 0) := by
  have hf : DifferentiableOn ℂ (fun t => h (z, t)) (ball 0 R) :=
    hh.comp ((differentiableOn_const z).prodMk differentiableOn_id) fun t ht => ⟨hz, ht⟩
  have := coeff1_eq_iteratedDeriv hρ hρR hf k
  rw [iteratedDeriv_eq_lastIter hh k z hz 0 (mem_ball_self (hρ.trans hρR))] at this
  exact this

/-- The Taylor coefficients in the last variable depend holomorphically on the other
variables. -/
theorem differentiableOn_lastCoeff {h : E × ℂ → ℂ} {δ ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R)) (k : ℕ) :
    DifferentiableOn ℂ (lastCoeff h ρ k) (ball (0 : E) δ) := by
  have hU : IsOpen (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
  have hd : DifferentiableOn ℂ (fun z : E => (k ! : ℂ)⁻¹ * lastIter h k (z, 0))
      (ball (0 : E) δ) :=
    ((differentiableOn_lastIter hU hh k).comp (differentiableOn_id.prodMk
      (differentiableOn_const 0)) fun z hz => ⟨hz, mem_ball_self (hρ.trans hρR)⟩).const_mul _
  exact hd.congr fun z hz => lastCoeff_eq_lastIter hρ hρR hh k hz

/-- Cauchy estimate for the Taylor coefficients in the last variable. -/
theorem norm_lastCoeff_le {h : E × ℂ → ℂ} {δ ρ R M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R))
    (hM : ∀ x ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R, ‖h x‖ ≤ M) (k : ℕ) :
    ∀ z ∈ ball (0 : E) δ, ‖lastCoeff h ρ k z‖ ≤ M / ρ ^ k := by
  -- Only the bound on the circle `‖ζ‖ = ρ` is used, not the holomorphy of `h`.
  have _ := hh
  intro z hz
  exact norm_coeff1_le hρ (fun ζ hζ => hM (z, ζ) ⟨hz, sphere_subset_ball hρR hζ⟩) k

/-- Taylor division by `t ^ d` in the last variable:
`h = lastQuot h ρ d * t ^ d + ∑_{k < d} lastCoeff h ρ k z * t ^ k`. -/
theorem eq_lastQuot_mul_add {h : E × ℂ → ℂ} {δ ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R)) (d : ℕ) :
    ∀ x ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R,
      h x = lastQuot h ρ d x * x.2 ^ d + ∑ k ∈ Finset.range d, lastCoeff h ρ k x.1 * x.2 ^ k := by
  rintro ⟨z, t⟩ ⟨hz, ht⟩
  by_cases ht0 : t = 0
  · subst ht0
    have hf : DifferentiableOn ℂ (fun t => h (z, t)) (ball 0 R) :=
      hh.comp ((differentiableOn_const z).prodMk differentiableOn_id) fun t ht => ⟨hz, ht⟩
    have h0 : lastCoeff h ρ 0 z = h (z, 0) := coeff1_zero hρ hρR hf
    rcases d with _ | d
    · simp [lastQuot, h0]
    · rw [Finset.sum_range_succ']
      simp [h0]
  · simp only [lastQuot, ht0, ite_false]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ ht0), sub_add_cancel]

/-! ### Holomorphy of the quotient -/

omit [NormedSpace ℂ E] in
/-- Tube lemma: `h` is bounded on `ball z₀ ε × sphere 0 ρ` for some `ε > 0`. -/
private lemma exists_ball_forall_sphere_norm_le {h : E × ℂ → ℂ} {δ ρ R : ℝ} (hρR : ρ < R)
    (hc : ContinuousOn h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R)) {z₀ : E}
    (hz₀ : z₀ ∈ ball (0 : E) δ) :
    ∃ ε > 0, ball z₀ ε ⊆ ball (0 : E) δ ∧
      ∃ B, ∀ z ∈ ball z₀ ε, ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖h (z, ζ)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_bound_of_continuousOn
    (f := fun ζ => h (z₀, ζ)) (hc.comp (continuousOn_const.prodMk continuousOn_id)
      fun ζ hζ => ⟨hz₀, sphere_subset_ball hρR hζ⟩)
  have hev : ∀ᶠ z in 𝓝 z₀, ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖h (z, ζ)‖ < B + 1 := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually
      fun ζ hζ => ?_
    have hmem : (z₀, ζ) ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R :=
      ⟨hz₀, sphere_subset_ball hρR hζ⟩
    have hca : ContinuousAt h (z₀, ζ) :=
      hc.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)
    exact hca.norm.eventually_lt continuousAt_const (by linarith [hB ζ hζ])
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.1 (hev.and (isOpen_ball.mem_nhds hz₀))
  exact ⟨ε, hε, fun z hz => (hεP z hz).2, B + 1, fun z hz ζ hζ => ((hεP z hz).1 ζ hζ).le⟩

private lemma hasSum_lastQuot {h : E × ℂ → ℂ} {δ ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R)) (d : ℕ) {z : E}
    (hz : z ∈ ball (0 : E) δ) {t : ℂ} (ht : t ∈ ball (0 : ℂ) ρ) :
    HasSum (fun k => lastCoeff h ρ (k + d) z * t ^ k) (lastQuot h ρ d (z, t)) := by
  have hf : DifferentiableOn ℂ (fun t => h (z, t)) (ball 0 R) :=
    hh.comp ((differentiableOn_const z).prodMk differentiableOn_id) fun t ht => ⟨hz, ht⟩
  have hs : HasSum (fun k => lastCoeff h ρ k z * t ^ k) (h (z, t)) := hasSum_coeff1 hρ hρR hf ht
  by_cases ht0 : t = 0
  · subst ht0
    simp only [lastQuot]
    convert hasSum_single (f := fun k => lastCoeff h ρ (k + d) z * (0 : ℂ) ^ k) 0 ?_ using 1
    · simp
    · intro b hb; simp [hb]
  · rw [← hasSum_nat_add_iff' d] at hs
    simp only [lastQuot, ht0, ite_false]
    have e : (fun k => lastCoeff h ρ (k + d) z * t ^ k) =
        fun k => lastCoeff h ρ (k + d) z * t ^ (k + d) / t ^ d := by
      funext k; rw [pow_add, mul_div_assoc, mul_div_cancel_right₀ _ (pow_ne_zero d ht0)]
    rw [e]
    exact hs.div_const (t ^ d)

private lemma differentiableAt_lastQuot_zero {h : E × ℂ → ℂ} {δ ρ R : ℝ} (hρ : 0 < ρ)
    (hρR : ρ < R) (hh : DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R)) (d : ℕ)
    {z₀ : E} (hz₀ : z₀ ∈ ball (0 : E) δ) :
    DifferentiableAt ℂ (lastQuot h ρ d) (z₀, 0) := by
  obtain ⟨ε, hε, hεδ, B, hB⟩ := exists_ball_forall_sphere_norm_le hρR hh.continuousOn hz₀
  set r := min ε (ρ / 2) with hr_def
  have hr : 0 < r := lt_min hε (by positivity)
  have hmem : ∀ x ∈ ball (z₀, (0 : ℂ)) r, x.1 ∈ ball (0 : E) δ ∧ ‖x.2‖ ≤ ρ / 2 := by
    rintro ⟨z, t⟩ hx
    rw [← ball_prod_same] at hx
    obtain ⟨hz, ht⟩ := hx
    refine ⟨hεδ (ball_subset_ball (min_le_left _ _) hz), ?_⟩
    rw [mem_ball_zero_iff] at ht
    exact ht.le.trans (min_le_right _ _)
  have hcoeff : ∀ k, ∀ x ∈ ball (z₀, (0 : ℂ)) r, ‖lastCoeff h ρ k x.1‖ ≤ B / ρ ^ k := by
    rintro k ⟨z, t⟩ hx
    rw [← ball_prod_same] at hx
    exact norm_coeff1_le hρ (hB z (ball_subset_ball (min_le_left _ _) hx.1)) k
  refine FirstPass.differentiableAt_of_tendstoUniformlyOn_ball
    (g := fun n x => ∑ k ∈ Finset.range n, lastCoeff h ρ (k + d) x.1 * x.2 ^ k) hr
    (Eventually.of_forall fun n => ?_) ?_
  · refine DifferentiableOn.fun_sum fun k _ => ?_
    refine DifferentiableOn.mul ?_ (differentiableOn_snd.pow k)
    exact (differentiableOn_lastCoeff hρ hρR hh (k + d)).comp differentiableOn_fst
      fun x hx => (hmem x hx).1
  · have hu := tendstoUniformlyOn_tsum_nat (summable_geometric_two.mul_left (B / ρ ^ d))
      (f := fun k (x : E × ℂ) => lastCoeff h ρ (k + d) x.1 * x.2 ^ k)
      (s := ball (z₀, (0 : ℂ)) r) fun k x hx => by
        rw [norm_mul, norm_pow]
        have h1 := hcoeff (k + d) x hx
        calc ‖lastCoeff h ρ (k + d) x.1‖ * ‖x.2‖ ^ k ≤ B / ρ ^ (k + d) * (ρ / 2) ^ k :=
              mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) (hmem x hx).2 k)
                (by positivity) ((norm_nonneg _).trans h1)
          _ = B / ρ ^ d * (1 / 2) ^ k := by
              rw [pow_add, div_pow, one_div, inv_pow]; field_simp
    refine hu.congr_right fun x hx => ?_
    have hx2 : x.2 ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff]; linarith [(hmem x hx).2]
    exact (hasSum_lastQuot hρ hρR hh d (hmem x hx).1 hx2).tsum_eq

/-- The Taylor quotient `lastQuot h ρ d` is jointly holomorphic. -/
theorem differentiableOn_lastQuot {h : E × ℂ → ℂ} {δ ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R)) (d : ℕ) :
    DifferentiableOn ℂ (lastQuot h ρ d) (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) := by
  have hU : IsOpen (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
  rintro ⟨z, t⟩ ⟨hz, ht⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases ht0 : t = 0
  · subst ht0
    exact differentiableAt_lastQuot_zero hρ hρR hh d hz
  · have hQ : DifferentiableAt ℂ
        (fun x : E × ℂ => (h x - ∑ k ∈ Finset.range d, lastCoeff h ρ k x.1 * x.2 ^ k) *
          (x.2 ^ d)⁻¹) (z, t) := by
      refine DifferentiableAt.mul ?_
        ((differentiableAt_snd.pow d).inv (pow_ne_zero d ht0))
      refine (hh.differentiableAt (hU.mem_nhds ⟨hz, ht⟩)).sub ?_
      refine DifferentiableAt.fun_sum fun k _ => ?_
      refine DifferentiableAt.mul ?_ (differentiableAt_snd.pow k)
      exact ((differentiableOn_lastCoeff hρ hρR hh k).differentiableAt
        (isOpen_ball.mem_nhds hz)).comp (z, t) differentiableAt_fst
    refine hQ.congr_of_eventuallyEq ?_
    have hopen : IsOpen {x : E × ℂ | x.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    filter_upwards [hopen.mem_nhds (show (z, t) ∈ {x : E × ℂ | x.2 ≠ 0} from ht0)] with x hx
    simp [lastQuot, show x.2 ≠ 0 from hx, div_eq_mul_inv]

/-! ### Sup-norm estimate for the quotient -/

/-- Sup-norm estimate for the Taylor quotient, with a constant depending only on `d`, `ρ`,
`R`. -/
theorem exists_norm_lastQuot_le (d : ℕ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ M : ℝ) (h : E × ℂ → ℂ),
      DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) →
      (∀ x ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R, ‖h x‖ ≤ M) →
      ∀ x ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R, ‖lastQuot h ρ d x‖ ≤ C * M := by
  have hR : 0 < R := hρ.trans hρR
  set S : ℝ := ∑ k ∈ Finset.range d, (R / ρ) ^ k with hS_def
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  refine ⟨(1 + S) / ρ ^ d, by positivity, fun δ M h hh hM => ?_⟩
  have hout : ∀ z ∈ ball (0 : E) δ, ∀ t : ℂ, ρ ≤ ‖t‖ → ‖t‖ < R →
      ‖lastQuot h ρ d (z, t)‖ ≤ (1 + S) / ρ ^ d * M := by
    intro z hz t hρt htR
    have ht0 : t ≠ 0 := by rintro rfl; rw [norm_zero] at hρt; linarith
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (z, t) ⟨hz, mem_ball_zero_iff.2 htR⟩)
    simp only [lastQuot, ht0, ite_false, norm_div, norm_pow]
    rw [div_le_iff₀ (by positivity)]
    calc ‖h (z, t) - ∑ k ∈ Finset.range d, lastCoeff h ρ k z * t ^ k‖
        ≤ ‖h (z, t)‖ + ‖∑ k ∈ Finset.range d, lastCoeff h ρ k z * t ^ k‖ := norm_sub_le _ _
      _ ≤ M + ∑ k ∈ Finset.range d, M / ρ ^ k * R ^ k := by
          refine add_le_add (hM (z, t) ⟨hz, mem_ball_zero_iff.2 htR⟩)
            ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
          rw [norm_mul, norm_pow]
          exact mul_le_mul (norm_lastCoeff_le hρ hρR hh hM k z hz)
            (pow_le_pow_left₀ (norm_nonneg _) htR.le k) (by positivity) (by positivity)
      _ = (1 + S) / ρ ^ d * M * ρ ^ d := by
          rw [hS_def, div_mul_eq_mul_div, div_mul_cancel₀ _ (by positivity), add_mul, one_mul,
            Finset.sum_mul]
          refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
          rw [div_pow]; field_simp
      _ ≤ (1 + S) / ρ ^ d * M * ‖t‖ ^ d := by
          gcongr
  rintro ⟨z, t⟩ ⟨hz, ht⟩
  by_cases hρt : ρ ≤ ‖t‖
  · exact hout z hz t hρt (mem_ball_zero_iff.1 ht)
  rw [not_le] at hρt
  have hdiff : DifferentiableOn ℂ (fun s => lastQuot h ρ d (z, s)) (closure (ball 0 ρ)) := by
    rw [closure_ball (0 : ℂ) hρ.ne']
    exact (differentiableOn_lastQuot hρ hρR hh d).comp
      ((differentiableOn_const z).prodMk differentiableOn_id)
      fun s hs => ⟨hz, closedBall_subset_ball hρR hs⟩
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff.diffContOnCl
    (fun s hs => ?_) (subset_closure (mem_ball_zero_iff.2 hρt))
  rw [frontier_ball (0 : ℂ) hρ.ne', mem_sphere_zero_iff_norm] at hs
  exact hout z hz s hs.ge (hs ▸ hρR)

end

end SGPT.Foundations.Analysis.Pending
