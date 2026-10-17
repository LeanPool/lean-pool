/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.C0FromVanishing

/-!
# C0AllShifts

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Extending analytic `C₀` vanishing from large shifts

For a positive shift `mu`, the resolvent identity with `mu + 1` expands the
`mu`-resolvent into a finite geometric sum of `(mu + 1)`-resolvents and a
remainder.  The sharp resolvent bound makes the remainder uniformly geometric.
Consequently it suffices to prove vanishing at infinity for shifts at least
one.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

omit [NeZero d] in
theorem abs_le_norm_c0_allShifts (f : C₀(Vec d, ℝ)) (x : Vec d) :
    |f x| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

/-- Vanishing at infinity for the analytic minimal resolvent at every shift
at least one. -/
def HasVanishingAnalyticMinimalResolventAboveOne : Prop :=
  ∀ (mu : PositiveShift), 1 ≤ (mu : ℝ) → ∀ (f : C₀(Vec d, ℝ)),
    Tendsto (A.analyticMinimalResolventReal mu f f.continuous.measurable
      (D := ‖f‖) (abs_le_norm_c0_allShifts f))
      (cocompact (Vec d)) (nhds 0)

/-- Large-shift `C₀` vanishing extends to every positive shift by the
resolvent identity and its geometric remainder. -/
theorem hasVanishingAnalyticMinimalResolvent_of_aboveOne
    (hHigh : A.HasVanishingAnalyticMinimalResolventAboveOne) :
    A.HasVanishingAnalyticMinimalResolvent := by
  intro mu f
  by_cases hmu : 1 ≤ (mu : ℝ)
  · simpa only [HasVanishingAnalyticMinimalResolvent,
      abs_le_norm_c0_allShifts] using hHigh mu hmu f
  · let lam : PositiveShift :=
      ⟨(mu : ℝ) + 1, Set.mem_Ioi.mpr
        (add_pos_of_pos_of_nonneg mu.property zero_le_one)⟩
    have hlam : 1 ≤ (lam : ℝ) := by
      dsimp only [lam]
      have hmu0 : 0 < (mu : ℝ) := mu.property
      linarith only [hmu0]
    let T : C₀(Vec d, ℝ) → C₀(Vec d, ℝ) := fun g ↦
      { toFun := A.analyticMinimalResolventReal lam g g.continuous.measurable
          (D := ‖g‖) (abs_le_norm_c0_allShifts g)
        continuous_toFun := A.continuous_analyticMinimalResolventReal lam g
        zero_at_infty' := hHigh lam hlam g }
    let u : ℕ → C₀(Vec d, ℝ) := fun n ↦ (T ^[n]) f
    have hu_zero : u 0 = f := by rfl
    have hu_succ : ∀ n, u (n + 1) = T (u n) := by
      intro n
      simp only [u, Function.iterate_succ_apply']
    have hTnorm : ∀ g : C₀(Vec d, ℝ), ‖T g‖ ≤ (lam : ℝ)⁻¹ * ‖g‖ := by
      intro g
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      apply (BoundedContinuousFunction.norm_le
        (mul_nonneg (inv_nonneg.mpr lam.property.le) (norm_nonneg g))).2
      intro x
      rw [Real.norm_eq_abs]
      simpa only [T, div_eq_inv_mul] using!
        A.abs_analyticMinimalResolventReal_le lam g.continuous.measurable
          (abs_le_norm_c0_allShifts g) x
    have hunorm : ∀ n, ‖u n‖ ≤ (lam : ℝ)⁻¹ ^ n * ‖f‖ := by
      intro n
      induction n with
      | zero => simpa only [hu_zero, pow_zero, one_mul] using le_refl ‖f‖
      | succ n ih =>
          rw [hu_succ]
          calc
            ‖T (u n)‖ ≤ (lam : ℝ)⁻¹ * ‖u n‖ := hTnorm (u n)
            _ ≤ (lam : ℝ)⁻¹ * ((lam : ℝ)⁻¹ ^ n * ‖f‖) :=
              mul_le_mul_of_nonneg_left ih (inv_nonneg.mpr lam.property.le)
            _ = (lam : ℝ)⁻¹ ^ (n + 1) * ‖f‖ := by
              rw [pow_succ]
              ring
    have hstep : ∀ (g : C₀(Vec d, ℝ)) (x : Vec d),
        A.analyticMinimalResolventReal mu g g.continuous.measurable
            (abs_le_norm_c0_allShifts g) x =
          T g x + A.analyticMinimalResolventReal mu (T g)
            (T g).continuous.measurable (abs_le_norm_c0_allShifts (T g)) x := by
      intro g x
      have hEq := A.analyticMinimalResolventReal_resolventEquation mu lam
        g.continuous.measurable (abs_le_norm_c0_allShifts g) x
      have hbound : ∀ y,
          |A.analyticMinimalResolventReal lam g g.continuous.measurable
            (abs_le_norm_c0_allShifts g) y| ≤ ‖g‖ / (lam : ℝ) :=
        A.abs_analyticMinimalResolventReal_le lam g.continuous.measurable
          (abs_le_norm_c0_allShifts g)
      have hinner : A.analyticMinimalResolventReal mu
          (A.analyticMinimalResolventReal lam g g.continuous.measurable
            (abs_le_norm_c0_allShifts g))
          (A.measurable_analyticMinimalResolventReal lam
            g.continuous.measurable (abs_le_norm_c0_allShifts g)) hbound x =
          A.analyticMinimalResolventReal mu (T g)
            (T g).continuous.measurable (abs_le_norm_c0_allShifts (T g)) x := by
        apply A.analyticMinimalResolventReal_bound_irrel mu
      have hdiff : (lam : ℝ) - (mu : ℝ) = 1 := by
        dsimp only [lam]
        ring
      rw [hdiff, one_mul] at hEq
      change _ = T g x + _
      rw [← hinner]
      convert hEq using 1
    have hexpand : ∀ n x,
        A.analyticMinimalResolventReal mu f f.continuous.measurable
            (abs_le_norm_c0_allShifts f) x =
          (∑ k ∈ Finset.range n, u (k + 1)) x +
            A.analyticMinimalResolventReal mu (u n)
              (u n).continuous.measurable (abs_le_norm_c0_allShifts (u n)) x := by
      intro n
      induction n with
      | zero =>
          intro x
          simp only [Finset.range_zero, Finset.sum_empty, ZeroAtInftyContinuousMap.coe_zero,
            Pi.zero_apply, zero_add, hu_zero]
      | succ n ih =>
          intro x
          rw [ih x, hstep (u n) x]
          simp only [Finset.sum_range_succ, ZeroAtInftyContinuousMap.coe_add,
            Pi.add_apply]
          rw [← hu_succ n]
          ring
    have hlamInv0 : 0 ≤ (lam : ℝ)⁻¹ := inv_nonneg.mpr lam.property.le
    have hlamInv1 : (lam : ℝ)⁻¹ < 1 := by
      apply (inv_lt_one₀ lam.property).2
      dsimp only [lam]
      have hmu0 : 0 < (mu : ℝ) := mu.property
      linarith only [hmu0]
    have hgeom : Tendsto (fun n : ℕ ↦
        (lam : ℝ)⁻¹ ^ n * ‖f‖ / (mu : ℝ)) atTop (nhds 0) := by
      simpa only [zero_mul, zero_div] using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hlamInv0 hlamInv1).mul_const ‖f‖).div_const
          (mu : ℝ)
    rw [Metric.tendsto_nhds]
    intro eps heps
    have heventGeom := (Metric.tendsto_atTop.mp hgeom) (eps / 2) (half_pos heps)
    obtain ⟨n, hn⟩ := heventGeom
    let v : C₀(Vec d, ℝ) := ∑ k ∈ Finset.range n, u (k + 1)
    have hvzero := v.zero_at_infty'
    have heventV := (Metric.tendsto_nhds.mp hvzero) (eps / 2) (half_pos heps)
    filter_upwards [heventV] with x hx
    rw [Real.dist_eq, sub_zero] at hx ⊢
    have hrem := A.abs_analyticMinimalResolventReal_le mu
      (u n).continuous.measurable (abs_le_norm_c0_allShifts (u n)) x
    have hrem' :
        |A.analyticMinimalResolventReal mu (u n) (u n).continuous.measurable
          (abs_le_norm_c0_allShifts (u n)) x| ≤
            (lam : ℝ)⁻¹ ^ n * ‖f‖ / (mu : ℝ) :=
      hrem.trans (div_le_div_of_nonneg_right (hunorm n) mu.property.le)
    have htail : (lam : ℝ)⁻¹ ^ n * ‖f‖ / (mu : ℝ) < eps / 2 := by
      have hnonneg : 0 ≤ (lam : ℝ)⁻¹ ^ n * ‖f‖ / (mu : ℝ) :=
        div_nonneg (mul_nonneg (pow_nonneg hlamInv0 n) (norm_nonneg f)) mu.property.le
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hn n le_rfl
    rw [hexpand n x]
    exact (abs_add_le _ _).trans_lt (by
      simpa only [add_halves] using! add_lt_add hx (hrem'.trans_lt htail))

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
