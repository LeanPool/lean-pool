/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Spectrum.RellichW12
public import LeanPool.EllipticPDE.Embedding.ConstOfGradZero


/-!
# Poincaré's inequality with the mean subtracted

On a bounded connected open domain with `C¹` boundary, an element of `H¹(Ω)` is within a
constant times the `L²` norm of its gradient of its mean. This is Evans §5.8.1 Theorem 1 at
`p = 2`. Only the gradient appears on the right, which is what distinguishes it from the
Poincaré inequality on `H₀¹(Ω)` the library runs existence on, where the boundary condition
replaces the subtraction of the mean.

The proof is Evans's, by contradiction. Were the estimate false, a sequence of elements of unit
`L²` norm, zero mean and gradient tending to zero would exist; Rellich-Kondrachov on the graph
space makes a subsequence converge in `L²`, the limit has zero weak gradient because the graph
space is closed, so it is constant on the connected domain, its mean is zero, so it vanishes,
against its unit norm.

## Main declarations

* `EllipticPdes.Sobolev.constGraph`: the graph of a constant, with zero gradient, and
  `constGraph_mem_W12`.
* `EllipticPdes.Sobolev.meanL2`: the mean over the domain as a continuous linear functional on
  `L²(Ω)`.
* `EllipticPdes.Sobolev.poincare_wirtinger`: the inequality.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.8.1 Theorem 1 (p. 290).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding (HasWeakGradOn isFiniteMeasure_restrict_of_isBounded
  ae_const_of_hasWeakGradOn_zero)
open EllipticPdes.Extension (HasC1Boundary hasWeakGradOn_of_mem_W12 inner_L2D_eq_integral
  hasC1Boundary_ball)

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Constants -/

section Constants

variable (hΩb : Bornology.IsBounded Ω)

/-- The class of a constant in `L²(Ω)`. -/
def constL2 (c : ℝ) : L2D Ω :=
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  (memLp_const c).toLp _

theorem coeFn_constL2 (c : ℝ) :
    (constL2 hΩb c : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] fun _ => c :=
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  (memLp_const c).coeFn_toLp

theorem constL2_zero : constL2 hΩb 0 = 0 :=
  Lp.ext ((coeFn_constL2 hΩb 0).trans (Lp.coeFn_zero ℝ 2 _).symm)

/-- The graph of a constant: the constant as function coordinate and zero as gradient. -/
def constGraph (c : ℝ) : H1amb Ω :=
  WithLp.toLp 2 (Fin.cons (constL2 hΩb c) fun _ => 0)

@[simp] theorem constGraph_zero (c : ℝ) : constGraph hΩb c 0 = constL2 hΩb c := by
  rw [constGraph, PiLp.toLp_apply, Fin.cons_zero]

@[simp] theorem constGraph_succ (c : ℝ) (k : Fin d) : constGraph hΩb c k.succ = 0 := by
  rw [constGraph, PiLp.toLp_apply, Fin.cons_succ]

/-- **Membership of a constant in the graph space**, with zero weak gradient: a test
function's partial derivative integrates to zero. -/
theorem constGraph_mem_W12 (c : ℝ) : constGraph hΩb c ∈ W12 Ω := by
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  rw [mem_W12_iff]
  intro ψ g i
  rw [constGraph_zero, constGraph_succ, inner_zero_right, add_zero]
  simp only [IsTestFn.partialCls, constL2]
  rw [inner_toLp_eq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport
      (fun hc => hx (g.2.2 (tsupport_partialD_subset i ψ hc))), zero_mul])]
  simp only [partialD]
  have hib := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : EuclideanSpace ℝ (Fin d) => c) (g := ψ) (v := EuclideanSpace.single i 1)
    (by simp) (by
      have : Continuous fun x => c * partialD i ψ x :=
        continuous_const.mul (g.continuous_partialD i)
      exact this.integrable_of_hasCompactSupport (g.hasCompactSupport_partialD i).mul_left)
    ((continuous_const.mul g.continuous).integrable_of_hasCompactSupport g.2.1.mul_left)
    (fun x _ => differentiableAt_const _)
    (fun x _ => (g.1.differentiable (by simp)).differentiableAt)
  simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, zero_mul,
    integral_zero, neg_zero] at hib
  rw [← hib]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- **Mean as a functional.** The mean over `Ω` of an `L²(Ω)` class, read as the inner
product against the constant one over the measure of the domain. -/
def meanL2 : L2D Ω →L[ℝ] ℝ :=
  ((volume Ω).toReal)⁻¹ • innerSL ℝ (constL2 hΩb 1)

theorem meanL2_apply (f : L2D Ω) :
    meanL2 hΩb f = ((volume Ω).toReal)⁻¹ * ∫ x in Ω, f x := by
  simp only [meanL2, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul]
  congr 1
  rw [inner_L2D_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_constL2 hΩb 1] with x hx
  rw [hx, one_mul]

theorem meanL2_constL2 (hΩ0 : volume Ω ≠ 0) (c : ℝ) : meanL2 hΩb (constL2 hΩb c) = c := by
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  rw [meanL2_apply, integral_congr_ae (coeFn_constL2 hΩb c), setIntegral_const, smul_eq_mul,
    measureReal_def]
  have htop : volume Ω ≠ ⊤ := by
    rw [← Measure.restrict_apply_univ]; exact measure_ne_top _ _
  have hm : (volume Ω).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hΩ0, htop⟩
  field_simp

end Constants

/-! ### The inequality -/

/-- **Poincaré's inequality with the mean subtracted** (Evans §5.8.1 Theorem 1 at `p = 2`).
On a bounded, connected, open domain with `C¹` boundary, one constant bounds the `L²`
distance of every element of `H¹(Ω)` from its mean by the `L²` norm of its gradient. -/
theorem poincare_wirtinger (hd : 0 < d) (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) :
    ∃ C : ℝ, ∀ U : W12 Ω,
      ‖embW12 Ω U - constL2 hΩb (meanL2 hΩb (embW12 Ω U))‖
        ≤ C * Real.sqrt (∑ k : Fin d, ‖(U : H1amb Ω) k.succ‖ ^ 2) := by
  classical
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  have hΩ0 : volume Ω ≠ 0 := (hΩopen.measure_pos volume hne).ne'
  set g : W12 Ω → ℝ := fun U => Real.sqrt (∑ k : Fin d, ‖(U : H1amb Ω) k.succ‖ ^ 2) with hg
  set P : W12 Ω → L2D Ω :=
    fun U => embW12 Ω U - constL2 hΩb (meanL2 hΩb (embW12 Ω U)) with hP
  have hg0 : ∀ U, 0 ≤ g U := fun U => Real.sqrt_nonneg _
  by_contra hC
  simp only [not_exists, not_forall, not_le] at hC
  choose Useq hU using fun k : ℕ => hC ((k : ℝ) + 1)
  have hPpos : ∀ k, 0 < ‖P (Useq k)‖ := fun k =>
    lt_of_le_of_lt (mul_nonneg (by positivity) (hg0 _)) (hU k)
  -- the renormalised sequence
  let V : ℕ → W12 Ω := fun k => ‖P (Useq k)‖⁻¹ •
    (Useq k - ⟨constGraph hΩb (meanL2 hΩb (embW12 Ω (Useq k))), constGraph_mem_W12 hΩb _⟩)
  have hV0 : ∀ k, embW12 Ω (V k) = ‖P (Useq k)‖⁻¹ • P (Useq k) := by
    intro k
    simp only [V, map_smul, map_sub]
    congr 2
  have hVnorm : ∀ k, ‖embW12 Ω (V k)‖ = 1 := by
    intro k
    rw [hV0, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hPpos k).ne']
  have hVsucc : ∀ k (j : Fin d), ((V k : W12 Ω) : H1amb Ω) j.succ
      = ‖P (Useq k)‖⁻¹ • ((Useq k : W12 Ω) : H1amb Ω) j.succ := by
    intro k j
    simp only [V, Submodule.coe_smul, Submodule.coe_sub, PiLp.smul_apply, PiLp.sub_apply,
      constGraph_succ, sub_zero]
  have hgV : ∀ k, g (V k) = ‖P (Useq k)‖⁻¹ * g (Useq k) := by
    intro k
    simp only [hg, hVsucc, norm_smul, norm_inv, norm_norm, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hgV_lt : ∀ k : ℕ, ((k : ℝ) + 1) * g (V k) < 1 := by
    intro k
    rw [hgV, mul_left_comm, ← div_eq_inv_mul, div_lt_one (hPpos k)]
    exact hU k
  have hgV_le : ∀ k : ℕ, g (V k) ≤ 1 / ((k : ℝ) + 1) := fun k => by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (hgV_lt k).le
  have hgV_tend : Tendsto (fun k => g (V k)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun k => hg0 _) hgV_le
  have hVsucc_le : ∀ k (j : Fin d), ‖((V k : W12 Ω) : H1amb Ω) j.succ‖ ≤ g (V k) := by
    intro k j
    rw [hg, ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum
      (f := fun i : Fin d => ‖((V k : W12 Ω) : H1amb Ω) i.succ‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hVmean : ∀ k, meanL2 hΩb (embW12 Ω (V k)) = 0 := by
    intro k
    rw [hV0, map_smul, hP, map_sub, meanL2_constL2 hΩb hΩ0, sub_self, smul_zero]
  -- the sequence is bounded in the graph space
  have hVbdd : ∀ k, ‖V k‖ ≤ 2 := by
    intro k
    have hsq : ‖V k‖ ^ 2 = 1 + g (V k) ^ 2 := by
      rw [show ‖V k‖ = ‖((V k : W12 Ω) : H1amb Ω)‖ from rfl,
        PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, ← embW12_apply, hVnorm, one_pow, hg,
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have hg1 : g (V k) ≤ 1 := (hgV_le k).trans (by
      rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
    have : ‖V k‖ ^ 2 ≤ 2 ^ 2 := by
      rw [hsq]; nlinarith [hg0 (V k)]
    exact le_of_sq_le_sq this (by norm_num)
  -- Rellich-Kondrachov: a subsequence converges in `L²`
  have hcpt := (embW12_isCompact hd hΩopen hΩb hC1).isCompact_closure_image_closedBall 2
  have hmem : ∀ k, embW12 Ω (V k) ∈ closure (embW12 Ω '' closedBall (0 : W12 Ω) 2) :=
    fun k => subset_closure ⟨V k, mem_closedBall_zero_iff.mpr (hVbdd k), rfl⟩
  obtain ⟨v, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  -- the limit in the graph space
  set Vlim : H1amb Ω := WithLp.toLp 2 (Fin.cons v fun _ => 0) with hVlim
  have hVlim0 : Vlim 0 = v := by rw [hVlim, PiLp.toLp_apply, Fin.cons_zero]
  have hVlimsucc : ∀ j : Fin d, Vlim j.succ = 0 := fun j => by
    rw [hVlim, PiLp.toLp_apply, Fin.cons_succ]
  have htend : Tendsto (fun j => ((V (φ j) : W12 Ω) : H1amb Ω)) atTop (𝓝 Vlim) := by
    have hcoord : Tendsto (fun j => WithLp.toLp 2 fun i => ((V (φ j) : W12 Ω) : H1amb Ω) i)
        atTop (𝓝 (WithLp.toLp 2 (Fin.cons v fun _ => 0))) := by
      refine ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.mpr ?_)
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        have : (fun j => ((V (φ j) : W12 Ω) : H1amb Ω) 0) = fun j => embW12 Ω (V (φ j)) := by
          funext j; rw [embW12_apply]
        rw [this]
        exact hlim
      · simp only [Fin.cons_succ]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (hgV_tend.comp hφ.tendsto_atTop) (fun k => norm_nonneg _) fun k => ?_
        exact hVsucc_le (φ k) j
    simpa only [WithLp.toLp_ofLp] using hcoord
  have hclosed : IsClosed ((W12 Ω : Submodule ℝ (H1amb Ω)) : Set (H1amb Ω)) :=
    Submodule.isClosed_orthogonal _
  have hVlimW : Vlim ∈ W12 Ω :=
    hclosed.mem_of_tendsto htend (Eventually.of_forall fun j => (V (φ j)).2)
  -- the limit has zero weak gradient, so it is constant
  have hwg : HasWeakGradOn Ω (fun x => (v : EuclideanSpace ℝ (Fin d) → ℝ) x) fun _ _ => 0 := by
    have h := hasWeakGradOn_of_mem_W12 hVlimW
    rw [hVlim0] at h
    simp only [hVlimsucc] at h
    exact h.congr_ae EventuallyEq.rfl fun _ => Lp.coeFn_zero ℝ 2 _
  obtain ⟨c, hc⟩ := ae_const_of_hasWeakGradOn_zero hΩopen hconn
    ((Lp.memLp v).integrable one_le_two) hwg
  have hvc : v = constL2 hΩb c := Lp.ext (hc.trans (coeFn_constL2 hΩb c).symm)
  -- its mean is zero, so the constant is zero
  have hmean : meanL2 hΩb v = 0 := by
    have h1 : Tendsto (fun j => meanL2 hΩb (embW12 Ω (V (φ j)))) atTop (𝓝 (meanL2 hΩb v)) :=
      ((meanL2 hΩb).continuous.tendsto v).comp hlim
    have h2 : Tendsto (fun j => meanL2 hΩb (embW12 Ω (V (φ j)))) atTop (𝓝 0) := by
      simp only [hVmean]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  rw [hvc, meanL2_constL2 hΩb hΩ0] at hmean
  rw [hmean, constL2_zero] at hvc
  -- against the unit norm of the limit
  have hnorm1 : ‖v‖ = 1 := by
    have h1 : Tendsto (fun j => ‖embW12 Ω (V (φ j))‖) atTop (𝓝 ‖v‖) := hlim.norm
    have h2 : Tendsto (fun j => ‖embW12 Ω (V (φ j))‖) atTop (𝓝 1) := by
      simp only [hVnorm]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  rw [hvc, norm_zero] at hnorm1
  exact zero_ne_one hnorm1

/-- **Inequality on the unit ball**, every hypothesis discharged: the ball is open, bounded,
convex hence connected, nonempty, and has `C¹` boundary. -/
theorem poincare_wirtinger_ball (hd : 0 < d) :
    ∃ C : ℝ, ∀ U : W12 (ball (0 : EuclideanSpace ℝ (Fin d)) 1),
      ‖embW12 _ U - constL2 isBounded_ball (meanL2 isBounded_ball (embW12 _ U))‖
        ≤ C * Real.sqrt (∑ k : Fin d, ‖(U : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
          k.succ‖ ^ 2) :=
  poincare_wirtinger hd isOpen_ball isBounded_ball (hasC1Boundary_ball hd)
    (convex_ball _ _).isPreconnected ⟨0, mem_ball_self one_pos⟩

end EllipticPdes.Sobolev
