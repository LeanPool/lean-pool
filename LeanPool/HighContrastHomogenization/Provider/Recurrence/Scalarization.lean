/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenEntries
public import LeanPool.HighContrastHomogenization.Annealed.SchattenDefinedness
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# High-contrast homogenization: Provider.Recurrence.Scalarization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalarization of the mixed norm

`l.fixed.geometry.matrix.averaging` proves a matrix estimate by proving
`4d²` scalar ones, and the passage between the two runs through the two
displays recorded here.

Downwards, the mixed norm of a random symmetric doubled block is controlled by
the `L^Q` norms of its entries,
`‖H‖_{L^Q(S_Q)} ≤ (Σ_{a,b}‖H_{ab}‖_{L^Q}²)^{1/2}`.  The proof is the printed
one: the Hilbert–Schmidt comparison `|H|_{S_Q} ≤ (Σ_{a,b}H_{ab}²)^{1/2}`
pointwise, then Minkowski's inequality in `L^{Q/2}` for the sum of the `4d²`
squares — the exponent `Q/2` is at least `1` exactly because `Q ≥ 2`.

Upwards, each entry is controlled by the mixed norm,
`‖H_{ab}‖_{L^Q} ≤ ‖H‖_{L^Q(S_Q)}`, which is the entrywise spectral bound
integrated.  The two together are what let the scalar independent-sum estimate
be applied entry by entry and reassembled.

The normalized form is the one the fixed-grid moments are written in: the
centered moment `v_r^q` is a mixed norm of a normalized block, and the
normalization of a symmetric block is symmetric with no hypothesis.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The entry is dominated by the mixed norm -/

/-- **`‖H_{ab}‖_{L^Q} ≤ ‖H‖_{L^Q(S_Q)}`.**  The entrywise spectral bound of a
symmetric matrix holds pointwise, so it holds after taking `L^Q` norms. -/
theorem lqNorm_le_eLpNorm_schattenNorm (P : Measure (CoeffSpace d)) {Q : ℝ} (hQ : 0 < Q)
    {H : CoeffSpace d → BlockMat d} (hH : ∀ a, IsSymmetricBlockMat (H a))
    (α β : BlockCoord d) (hmeas : AEStronglyMeasurable (fun a => toFullBlockMat (H a) α β) P) :
    lqNorm P Q (fun a => toFullBlockMat (H a) α β)
      ≤ eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P := by
  simp only [lqNorm]
  refine eLpNorm_mono_real hmeas fun a => ?_
  rw [Real.norm_eq_abs]
  exact abs_toFullBlockMat_le_schattenNorm (hH a) hQ α β

/-! ## The mixed norm is dominated by the entries -/

/-- The Schatten norm of a random symmetric doubled block with measurable entries is
measurable, at every real exponent: the power `x ↦ x^{Q/2}` is a locally uniform limit of
polynomials (Weierstrass), and the functional calculus of a polynomial is a polynomial
in the entries. -/
private theorem aestronglyMeasurable_schattenNorm_of_entries {P : Measure (CoeffSpace d)} {Q : ℝ}
    (hQ : 0 ≤ Q) {H : CoeffSpace d → BlockMat d} (hH : ∀ a, IsSymmetricBlockMat (H a))
    (hmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (H a) α β) P) :
    AEStronglyMeasurable (fun a => schattenNorm Q (H a)) P := by
  classical
  set f : ℝ → ℝ := fun x => x ^ (Q / 2) with hf
  have hfc : Continuous f := Real.continuous_rpow_const (by positivity)
  choose p hp using fun n : ℕ => exists_polynomial_near_of_continuousOn (-(n : ℝ)) n f
    hfc.continuousOn (1 / ((n : ℝ) + 1)) (by positivity)
  set S : CoeffSpace d → FullBlockMat d := fun a => toFullBlockMat (H a) * toFullBlockMat (H a)
    with hS
  have hSsa : ∀ a, IsSelfAdjoint (S a) :=
    fun a => isSelfAdjoint_mul_self (isSelfAdjoint_toFullBlockMat (hH a))
  have hm : AEMeasurable (fun a => (toFullBlockMat (H a) : BlockCoord d → BlockCoord d → ℝ)) P :=
    AEMeasurable.of_eval fun α => AEMeasurable.of_eval fun β => (hmeas α β).aemeasurable
  have happrox : ∀ n : ℕ, AEStronglyMeasurable
      (fun a => Matrix.trace (Polynomial.aeval (S a) (p n))) P := by
    intro n
    have hc : Continuous fun M : FullBlockMat d => Matrix.trace (Polynomial.aeval (M * M) (p n)) :=
      Continuous.matrix_trace ((p n).continuous_aeval.comp (continuous_id.matrix_mul continuous_id))
    have hc' : Continuous fun M : BlockCoord d → BlockCoord d → ℝ =>
        Matrix.trace (Polynomial.aeval (Matrix.of M * Matrix.of M) (p n)) := hc
    exact (hc'.measurable.comp_aemeasurable hm).aestronglyMeasurable
  have hlim : ∀ a, Tendsto (fun n : ℕ => Matrix.trace (Polynomial.aeval (S a) (p n))) atTop
      (𝓝 (Matrix.trace (cfc f (S a)))) := by
    intro a
    have hfin : (spectrum ℝ (S a)).Finite := Matrix.finite_real_spectrum
    obtain ⟨R, hR⟩ := hfin.isBounded.exists_norm_le
    have hunif : TendstoUniformlyOn (fun n : ℕ => fun x : ℝ => (p n).eval x) f atTop
        (spectrum ℝ (S a)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (max R (1 / ε))
      filter_upwards [eventually_ge_atTop N] with n hn x hx
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hxR : |x| ≤ R := by simpa [Real.norm_eq_abs] using hR x hx
      have hxn : x ∈ Set.Icc (-(n : ℝ)) n := by
        rw [Set.mem_Icc, ← abs_le]
        linarith [le_max_left R (1 / ε)]
      have h1 := hp n x hxn
      have hεn : 1 / ((n : ℝ) + 1) < ε := by
        rw [div_lt_iff₀ (by positivity)]
        have : 1 / ε < (n : ℝ) + 1 := by linarith [le_max_right R (1 / ε)]
        rw [div_lt_iff₀ hε] at this
        linarith
      rw [Real.dist_eq, abs_sub_comm]
      exact h1.trans hεn
    have hcfc := tendsto_cfc_fun (a := S a) hunif
      (Eventually.of_forall fun n => (p n).continuousOn)
    have hpoly : ∀ n : ℕ, cfc (fun x : ℝ => (p n).eval x) (S a) = Polynomial.aeval (S a) (p n) :=
      fun n => cfc_polynomial (p n) (S a) (hSsa a)
    simp only [hpoly] at hcfc
    exact ((continuous_id.matrix_trace).tendsto _).comp hcfc
  have htr : AEStronglyMeasurable (fun a => Matrix.trace (cfc f (S a))) P :=
    aestronglyMeasurable_of_tendsto_ae atTop happrox (ae_of_all _ hlim)
  exact (Real.continuous_rpow_const (inv_nonneg.mpr hQ)).comp_aestronglyMeasurable htr


/-- **The scalarization display of `l.fixed.geometry.matrix.averaging`**,
`‖H‖_{L^Q(S_Q)} ≤ (Σ_{a,b}‖H_{ab}‖_{L^Q}²)^{1/2}`, for a random symmetric
doubled block with measurable entries.  The Hilbert–Schmidt comparison is
applied pointwise and Minkowski's inequality is applied in `L^{Q/2}` to the
`4d²` squared entries. -/
theorem eLpNorm_schattenNorm_le (P : Measure (CoeffSpace d)) {Q : ℝ} (hQ : 2 ≤ Q)
    {H : CoeffSpace d → BlockMat d} (hH : ∀ a, IsSymmetricBlockMat (H a))
    (hmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (H a) α β) P) :
    eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P
      ≤ (∑ α : BlockCoord d, ∑ β : BlockCoord d,
          lqNorm P Q (fun a => toFullBlockMat (H a) α β) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
  simp only [lqNorm]
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hS0 : ∀ a : CoeffSpace d,
      (0 : ℝ) ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2 :=
    fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P
      ≤ eLpNorm (fun a =>
          (∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2) ^ (2⁻¹ : ℝ))
        (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_real (aestronglyMeasurable_schattenNorm_of_entries hQ0 hH hmeas)
      fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_schattenNorm (hH a) Q)]
    exact schattenNorm_le_sum_sq_rpow (hH a) hQ
  have h2 : eLpNorm (fun a =>
        (∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2) ^ (2⁻¹ : ℝ))
        (ENNReal.ofReal Q) P
      = eLpNorm (fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2)
          (ENNReal.ofReal (Q / 2)) P ^ (2⁻¹ : ℝ) := by
    have hfun : (fun a =>
          (∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2) ^ (2⁻¹ : ℝ))
        = fun a => ‖∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2‖
            ^ (2⁻¹ : ℝ) := by
      funext a
      rw [Real.norm_eq_abs, abs_of_nonneg (hS0 a)]
    have hp : ENNReal.ofReal Q * ENNReal.ofReal (2⁻¹ : ℝ) = ENNReal.ofReal (Q / 2) := by
      rw [← ENNReal.ofReal_mul hQ0, div_eq_mul_inv]
    have hsm : AEStronglyMeasurable
        (fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2) P :=
      Finset.aestronglyMeasurable_fun_sum _ fun α _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun β _ => (hmeas α β).pow 2
    rw [hfun, eLpNorm_norm_rpow _ hsm (by norm_num : (0 : ℝ) < 2⁻¹), hp]
  have hsum : (fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2)
      = ∑ i : BlockCoord d × BlockCoord d, fun a => toFullBlockMat (H a) i.1 i.2 ^ 2 := by
    funext a
    rw [Finset.sum_apply]
    exact (Fintype.sum_prod_type fun i : BlockCoord d × BlockCoord d =>
      toFullBlockMat (H a) i.1 i.2 ^ 2).symm
  have h3 : eLpNorm (fun a =>
        ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2)
        (ENNReal.ofReal (Q / 2)) P
      ≤ ∑ i : BlockCoord d × BlockCoord d,
          eLpNorm (fun a => toFullBlockMat (H a) i.1 i.2 ^ 2) (ENNReal.ofReal (Q / 2)) P := by
    rw [hsum]
    refine eLpNorm_sum_le ?_
    rw [ENNReal.one_le_ofReal]
    linarith only [hQ]
  have h4 : ∀ i : BlockCoord d × BlockCoord d,
      eLpNorm (fun a => toFullBlockMat (H a) i.1 i.2 ^ 2) (ENNReal.ofReal (Q / 2)) P
        = eLpNorm (fun a => toFullBlockMat (H a) i.1 i.2) (ENNReal.ofReal Q) P ^ (2 : ℝ) := by
    intro i
    have hfun : (fun a => toFullBlockMat (H a) i.1 i.2 ^ 2)
        = fun a => ‖toFullBlockMat (H a) i.1 i.2‖ ^ (2 : ℝ) := by
      funext a
      rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hp : ENNReal.ofReal (Q / 2) * ENNReal.ofReal (2 : ℝ) = ENNReal.ofReal Q := by
      rw [← ENNReal.ofReal_mul (by linarith only [hQ] : (0 : ℝ) ≤ Q / 2)]
      congr 1
      ring
    rw [hfun, eLpNorm_norm_rpow _ (hmeas i.1 i.2) (by norm_num : (0 : ℝ) < 2), hp]
  refine le_trans h1 (le_trans (le_of_eq h2) ?_)
  refine ENNReal.rpow_le_rpow (le_trans h3 ?_) (by norm_num)
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun α _ =>
    Finset.sum_le_sum fun β _ => le_of_eq (h4 (α, β))

/-! ## The normalized form -/

/-- **The scalarization display in the normalized carrier of the fixed-grid
estimates.**  The mixed norm `‖F^{-1/2}·F^{-1/2}‖_{L^Q(S_Q)}` of a random
symmetric block is bounded by the `L^Q` norms of the entries of the normalized
block; the normalization of a symmetric block is symmetric whatever the
normalizing block, so no extra symmetry is assumed of it. -/
theorem lqSchattenSize_le (P : Measure (CoeffSpace d)) {Q : ℝ} (hQ : 2 ≤ Q)
    {A : CoeffSpace d → BlockMat d} (F : BlockMat d) (hA : ∀ a, IsSymmetricBlockMat (A a))
    (hmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (normalizedBlock (A a) F) α β) P) :
    lqSchattenSize P Q A F
      ≤ (∑ α : BlockCoord d, ∑ β : BlockCoord d,
          lqNorm P Q (fun a => toFullBlockMat (normalizedBlock (A a) F) α β) ^ (2 : ℝ))
        ^ (2⁻¹ : ℝ) :=
  eLpNorm_schattenNorm_le P hQ
    (fun a => isSymmetricBlockMat_normalizedBlock (F := F) (hA a)) hmeas

end

end Recurrence
end HighContrast
end HCPolySupport
