/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Multiplication of an `L²` class by an almost everywhere bounded multiplier

Two operations are needed whenever a closed differential operator is tested against a smooth
compactly supported function: multiplying a vector-valued `L²` class by a bounded **scalar**
multiplier, and multiplying a scalar `L²` class by a bounded **vector** multiplier. Both are
bounded linear maps on `L²`, and both are packaged here as continuous linear maps so that the
usual `map_sub` and operator-norm estimates are available without repeating the pointwise
argument.

`bddSmulL c` sends `u : Lp H 2 μ` to the class of `x ↦ c x • u x`, and `bddSmulRightL β` sends
`u : Lp ℝ 2 μ` to the class of `x ↦ u x • β x`. In both cases the multiplier is only assumed
a.e. strongly measurable and a.e. bounded by a constant `M`, and the operator norm bound is
`|M|`. No reverse inequality is claimed: `|M|` is a bound, not the operator norm.

`tendsto_integral_mul_of_tendsto` is the corresponding convergence statement for testing: a
family of multipliers that converges in `L²` and is uniformly a.e. bounded tests every
integrable function, not only square-integrable ones.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

section BddSmul

variable {c : α → ℝ} {M : ℝ}

/-- An a.e. bounded scalar multiplier preserves `L²`. -/
theorem memLp_bddSmul (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : MemLp (fun x => c x • (u x)) 2 μ := by
  refine MemLp.of_le ((Lp.memLp u).const_smul M) (hc.smul (Lp.aestronglyMeasurable u)) ?_
  filter_upwards [hM] with x hx
  have h1 : ‖c x • (u x)‖ = |c x| * ‖u x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖(M • (u : α → H)) x‖ = |M| * ‖u x‖ := by
    simp [norm_smul, Real.norm_eq_abs]
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self M)) (norm_nonneg _)

/-- Multiplication by an a.e. bounded scalar multiplier, as a linear map on `L²`. -/
def bddSmulₗ (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M) :
    Lp H 2 μ →ₗ[ℝ] Lp H 2 μ where
  toFun u := (memLp_bddSmul hc hM u).toLp _
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmul hc hM (u + v)).coeFn_toLp, Lp.coeFn_add
      ((memLp_bddSmul hc hM u).toLp _) ((memLp_bddSmul hc hM v).toLp _),
      (memLp_bddSmul hc hM u).coeFn_toLp, (memLp_bddSmul hc hM v).coeFn_toLp,
      Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' a u := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmul hc hM (a • u)).coeFn_toLp, Lp.coeFn_smul a
      ((memLp_bddSmul hc hM u).toLp _), (memLp_bddSmul hc hM u).coeFn_toLp,
      Lp.coeFn_smul a u] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
    exact smul_comm _ _ _

theorem coeFn_bddSmulₗ (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) :
    (bddSmulₗ hc hM u : α → H) =ᵐ[μ] fun x => c x • (u x) :=
  (memLp_bddSmul hc hM u).coeFn_toLp

theorem norm_bddSmulₗ_le (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : ‖bddSmulₗ hc hM u‖ ≤ |M| * ‖u‖ := by
  have hle : ‖bddSmulₗ hc hM u‖ ≤ ‖(|M| • u : Lp H 2 μ)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_bddSmulₗ hc hM u, Lp.coeFn_smul (|M|) u, hM] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_abs]
    exact mul_le_mul_of_nonneg_right (h3.trans (le_abs_self M)) (norm_nonneg _)
  refine hle.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_abs]

/-- Multiplication by an a.e. bounded scalar multiplier, as a continuous linear map on `L²`. -/
def bddSmulL (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M) :
    Lp H 2 μ →L[ℝ] Lp H 2 μ :=
  LinearMap.mkContinuous (bddSmulₗ hc hM) |M| (norm_bddSmulₗ_le hc hM)

@[simp]
theorem bddSmulL_apply (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : bddSmulL hc hM u = bddSmulₗ hc hM u := rfl

theorem coeFn_bddSmulL (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) :
    (bddSmulL hc hM u : α → H) =ᵐ[μ] fun x => c x • (u x) :=
  coeFn_bddSmulₗ hc hM u

theorem norm_bddSmulL_sub_le (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u v : Lp H 2 μ) : ‖bddSmulL hc hM u - bddSmulL hc hM v‖ ≤ |M| * ‖u - v‖ := by
  rw [← map_sub]
  exact norm_bddSmulₗ_le hc hM (u - v)

end BddSmul

section BddSmulRight

variable {β : α → H} {M : ℝ}

/-- An a.e. bounded vector multiplier sends a scalar `L²` class to a vector `L²` class. -/
theorem memLp_bddSmulRight (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : MemLp (fun x => (u x) • β x) 2 μ := by
  refine MemLp.of_le ((Lp.memLp u).const_smul M) ((Lp.aestronglyMeasurable u).smul hβ) ?_
  filter_upwards [hM] with x hx
  have h1 : ‖(u x) • β x‖ = |u x| * ‖β x‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖(M • (u : α → ℝ)) x‖ = |M| * ‖u x‖ := by
    simp [Real.norm_eq_abs]
  rw [h1, h2, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self M)) (abs_nonneg _)

/-- Multiplication by an a.e. bounded vector multiplier, as a linear map `L²(ℝ) → L²(H)`. -/
def bddSmulRightₗ (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp H 2 μ where
  toFun u := (memLp_bddSmulRight hβ hM u).toLp _
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmulRight hβ hM (u + v)).coeFn_toLp, Lp.coeFn_add
      ((memLp_bddSmulRight hβ hM u).toLp _) ((memLp_bddSmulRight hβ hM v).toLp _),
      (memLp_bddSmulRight hβ hM u).coeFn_toLp, (memLp_bddSmulRight hβ hM v).coeFn_toLp,
      Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, add_smul]
  map_smul' a u := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmulRight hβ hM (a • u)).coeFn_toLp, Lp.coeFn_smul a
      ((memLp_bddSmulRight hβ hM u).toLp _), (memLp_bddSmulRight hβ hM u).coeFn_toLp,
      Lp.coeFn_smul a u] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, smul_assoc]

theorem coeFn_bddSmulRightₗ (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) :
    (bddSmulRightₗ hβ hM u : α → H) =ᵐ[μ] fun x => (u x) • β x :=
  (memLp_bddSmulRight hβ hM u).coeFn_toLp

theorem norm_bddSmulRightₗ_le (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : ‖bddSmulRightₗ hβ hM u‖ ≤ |M| * ‖u‖ := by
  have hle : ‖bddSmulRightₗ hβ hM u‖ ≤ ‖(|M| • u : Lp ℝ 2 μ)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_bddSmulRightₗ hβ hM u, Lp.coeFn_smul (|M|) u, hM] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_abs, mul_comm (|M|)]
    exact mul_le_mul_of_nonneg_left (h3.trans (le_abs_self M)) (abs_nonneg _)
  refine hle.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_abs]

/-- Multiplication by an a.e. bounded vector multiplier, as a continuous linear map. -/
def bddSmulRightL (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) :
    Lp ℝ 2 μ →L[ℝ] Lp H 2 μ :=
  LinearMap.mkContinuous (bddSmulRightₗ hβ hM) |M| (norm_bddSmulRightₗ_le hβ hM)

@[simp]
theorem bddSmulRightL_apply (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : bddSmulRightL hβ hM u = bddSmulRightₗ hβ hM u := rfl

theorem coeFn_bddSmulRightL (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) :
    (bddSmulRightL hβ hM u : α → H) =ᵐ[μ] fun x => (u x) • β x :=
  coeFn_bddSmulRightₗ hβ hM u

theorem norm_bddSmulRightL_sub_le (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u v : Lp ℝ 2 μ) :
    ‖bddSmulRightL hβ hM u - bddSmulRightL hβ hM v‖ ≤ |M| * ‖u - v‖ := by
  rw [← map_sub]
  exact norm_bddSmulRightₗ_le hβ hM (u - v)

end BddSmulRight

section Symmetry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : α → ℝ} {M : ℝ}

/-- **A real a.e. bounded scalar multiplier is symmetric on `L²`.** Multiplication by `c` may be
moved from one side of the `L²` inner product to the other; this is the pointwise identity
`⟪c • a, b⟫ = ⟪a, c • b⟫` integrated. The multiplier is real valued, so no conjugation occurs. -/
theorem inner_bddSmulL_left (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u v : Lp E 2 μ) :
    inner ℝ (bddSmulL hc hM u) v = inner ℝ u (bddSmulL hc hM v) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bddSmulL hc hM u, coeFn_bddSmulL hc hM v] with x h1 h2
  rw [h1, h2, real_inner_smul_left, real_inner_smul_right]

end Symmetry

section Testing

open scoped RealInnerProductSpace

private theorem continuous_clamp (M : ℝ) : Continuous fun y : ℝ => max (-M) (min M y) :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem abs_sub_clamp_le {M y : ℝ} (hM : 0 ≤ M) : |y - max (-M) (min M y)| ≤ |y| := by
  rcases le_total y 0 with h | h
  · have h1 : y ≤ max (-M) (min M y) := le_max_of_le_right (le_min (by linarith) le_rfl)
    have h2 : max (-M) (min M y) ≤ 0 := max_le (by linarith) (min_le_of_right_le h)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos h]; linarith
  · have h1 : 0 ≤ max (-M) (min M y) := le_max_of_le_right (le_min hM h)
    have h2 : max (-M) (min M y) ≤ y := max_le (by linarith) (min_le_right _ _)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg h]; linarith

/-- Truncation at level `M`, `max (-M) (min M G)`, approximates an integrable `G` in `L¹`. -/
theorem exists_clamp_integral_lt {G : α → ℝ} (hG : Integrable G μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∫ x, |G x - max (-M) (min M (G x))| ∂μ < ε := by
  have hlim : Tendsto (fun n : ℕ => ∫ x, |G x - max (-(n : ℝ)) (min n (G x))| ∂μ) atTop
      (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |G x|) (fun n => ?_) hG.abs
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (hG.aestronglyMeasurable.sub
        ((continuous_clamp _).comp_aestronglyMeasurable hG.aestronglyMeasurable)).norm
    · rw [Real.norm_eq_abs, abs_abs]
      exact abs_sub_clamp_le (Nat.cast_nonneg n)
    · obtain ⟨N, hN⟩ := exists_nat_ge |G x|
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have h1 : |G x| ≤ n := hN.trans (by exact_mod_cast hn)
      rw [abs_le] at h1
      rw [min_eq_right h1.2, max_eq_right h1.1, sub_self, abs_zero]
  rw [integral_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨n, n.cast_nonneg, hn⟩

variable [IsFiniteMeasure μ]

/-- **Uniformly bounded `L²` convergence tests integrable functions.** If `qᵢ → q₀` in `L²(μ)`
along any filter and all of them are a.e. bounded by one constant `D`, then
`∫ qᵢ G dμ → ∫ q₀ G dμ` for every integrable `G`, which need not be square integrable. The
proof truncates `G` at a level `M` chosen from its `L¹` tail. -/
theorem tendsto_integral_mul_of_tendsto {ι : Type*} {l : Filter ι} {q : ι → Lp ℝ 2 μ}
    {q₀ : Lp ℝ 2 μ} (hq : Tendsto q l (𝓝 q₀)) {D : ℝ}
    (hD : ∀ᶠ i in l, ∀ᵐ x ∂μ, |q i x| ≤ D) (hD₀ : ∀ᵐ x ∂μ, |q₀ x| ≤ D) {G : α → ℝ}
    (hG : Integrable G μ) :
    Tendsto (fun i => ∫ x, q i x * G x ∂μ) l (𝓝 (∫ x, q₀ x * G x ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K := 2 * |D| + 1 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨M, hM0, hM⟩ := exists_clamp_integral_lt hG (ε := ε / (2 * K)) (by positivity)
  set c : α → ℝ := fun x => max (-M) (min M (G x)) with hc
  have hcm : AEStronglyMeasurable c μ :=
    (continuous_clamp M).comp_aestronglyMeasurable hG.aestronglyMeasurable
  have hcb : ∀ x, |c x| ≤ M := fun x => by
    rw [abs_le]; exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcL : MemLp c 2 μ := MemLp.of_bound hcm M (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hcb x)
  have hcI : Integrable c μ := hcL.integrable one_le_two
  have hint (p : Lp ℝ 2 μ) (hp : ∀ᵐ x ∂μ, |p x| ≤ D) (g : α → ℝ) (hg : Integrable g μ) :
      Integrable (fun x => p x * g x) μ :=
    hg.bdd_mul (Lp.aestronglyMeasurable p) (by
      filter_upwards [hp] with x hx; rwa [Real.norm_eq_abs])
  set cL := hcL.toLp c
  have hlim : Tendsto (fun i => ‖q i - q₀‖ * ‖cL‖) l (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp hq).mul_const ‖cL‖)
  filter_upwards [hD, hlim.eventually (gt_mem_nhds (half_pos hε))] with i hi hi'
  rw [Real.dist_eq]
  have hinner : ⟪q i - q₀, cL⟫ = ∫ x, (q i x - q₀ x) * c x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (q i) q₀, hcL.coeFn_toLp] with x h1 h2
    rw [h1, h2, Pi.sub_apply, real_inner_eq_re_inner, RCLike.re_to_real, RCLike.inner_apply,
      conj_trivial, mul_comm]
  have hsplit (p : Lp ℝ 2 μ) (hp : ∀ᵐ x ∂μ, |p x| ≤ D) :
      ∫ x, p x * G x ∂μ = ∫ x, p x * c x ∂μ + ∫ x, p x * (G x - c x) ∂μ := by
    rw [← integral_add (hint _ hp c hcI) (hint _ hp (fun x => G x - c x) (hG.sub hcI))]
    congr 1; funext x; ring
  have hsub (g : α → ℝ) (hg : Integrable g μ) :
      ∫ x, (q i x - q₀ x) * g x ∂μ = ∫ x, q i x * g x ∂μ - ∫ x, q₀ x * g x ∂μ := by
    rw [← integral_sub (hint _ hi g hg) (hint _ hD₀ g hg)]
    congr 1; funext x; ring
  have hdiff : ∫ x, q i x * G x ∂μ - ∫ x, q₀ x * G x ∂μ =
      ∫ x, (q i x - q₀ x) * c x ∂μ + ∫ x, (q i x - q₀ x) * (G x - c x) ∂μ := by
    rw [hsub c hcI, hsub (fun x => G x - c x) (hG.sub hcI), hsplit _ hi, hsplit _ hD₀]; ring
  have h1 : |∫ x, (q i x - q₀ x) * c x ∂μ| < ε / 2 := by
    rw [← hinner]
    exact (abs_real_inner_le_norm _ _).trans_lt hi'
  have h2 : |∫ x, (q i x - q₀ x) * (G x - c x) ∂μ| ≤ ε / 2 := by
    calc |∫ x, (q i x - q₀ x) * (G x - c x) ∂μ|
        ≤ ∫ x, |(q i x - q₀ x) * (G x - c x)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, K * |G x - c x| ∂μ := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            ((hG.sub hcI).abs.const_mul K)
          filter_upwards [hi, hD₀] with x hx hx₀
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          calc |q i x - q₀ x| ≤ |q i x| + |q₀ x| := abs_sub _ _
            _ ≤ K := by linarith [le_abs_self D]
      _ = K * ∫ x, |G x - c x| ∂μ := integral_const_mul _ _
      _ ≤ K * (ε / (2 * K)) := mul_le_mul_of_nonneg_left hM.le hKpos.le
      _ = ε / 2 := by field_simp
  rw [hdiff]
  calc _ ≤ |∫ x, (q i x - q₀ x) * c x ∂μ| + |∫ x, (q i x - q₀ x) * (G x - c x) ∂μ| :=
        abs_add_le _ _
    _ < ε := by linarith

end Testing

end FunctionalInequalities.L2
