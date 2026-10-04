/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg
public import LeanPool.EllipticPDE.Embedding.WeakDerivBridge


/-!
# Interior Hölder continuity of a weak solution

The interior `H²` estimate and the Morrey embedding are joined here, so that a weak solution of
`L u = f` is shown to have a Hölder continuous representative on a ball compactly contained in
the domain, with the Hölder constant controlled by `‖f‖ + ‖u‖`.

Three dimensions are covered, each with Hölder exponent `1/2`.

* `d = 1`. Morrey applies at `p = 2 > 1 = d` to the first-order weak gradient, so the
  first-order energy estimate alone suffices and the exponent is `1 - 1/2 = 1/2`.
* `d = 2`. The Sobolev conjugate of `2` degenerates at `d = 2`, so the bootstrap of
  `EllipticPdes.Embedding.GagliardoNirenberg` takes its step at `p = 4/3`, whose conjugate is
  `4`. The ball has finite measure, so the `L²` second derivatives of the interior `H²` estimate
  are `L^{4/3}` data, and Morrey applies at `p = 4 > 2 = d` with exponent `1 - 2/4 = 1/2`.
* `d = 3`. Morrey needs `p > 3`, and the interior `H²` estimate supplies second derivatives in
  `L²`. The bootstrap raises the gradient from `L²` to `L⁶`, and Morrey then applies at `p = 6 >
  3 = d` with exponent `1 - 3/6 = 1/2`.

`d ≥ 4` stays open. Reaching Morrey from `L²` second derivatives asks for an exponent `p` with
`d/2 < p ≤ 2`, since `1/p' = 1/p - 1/d` gives `p' > d` exactly when `p > d/2`, and the ball
turns `L²` data into `Lᵖ` data only for `p ≤ 2`. That range is empty once `d ≥ 4`, so one
Sobolev step never reaches Morrey there. Those dimensions require iteration through the `H^k`
ladder, which this library does not yet have.

## Main declarations

* `interior_holder_estimate_one`: the one-dimensional statement.
* `interior_holder_estimate_two`: the two-dimensional statement.
* `interior_holder_estimate`: the three-dimensional statement.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev EllipticPdes.Regularity

variable {d : ℕ}

/-! ### Morrey exponent at the two exponent pairs used here -/

/-- At `d = 1` and `p = 2` the Morrey exponent is `1/2`. -/
theorem morreyExponent_one_two : morreyExponent 1 2 = (1 / 2 : ℝ≥0) := by
  refine NNReal.coe_injective ?_
  rw [morreyExponent, Real.coe_toNNReal _ (by norm_num)]
  push_cast
  norm_num

/-- At `d = 2` and `p = 4` the Morrey exponent is `1/2`. -/
theorem morreyExponent_two_four : morreyExponent 2 4 = (1 / 2 : ℝ≥0) := by
  refine NNReal.coe_injective ?_
  rw [morreyExponent, Real.coe_toNNReal _ (by norm_num)]
  push_cast
  norm_num

/-- At `d = 3` and `p = 6` the Morrey exponent is `1/2`. -/
theorem morreyExponent_three_six : morreyExponent 3 6 = (1 / 2 : ℝ≥0) := by
  refine NNReal.coe_injective ?_
  rw [morreyExponent, Real.coe_toNNReal _ (by norm_num)]
  push_cast
  norm_num

/-! ### Restriction of a whole-space `L²` class to a ball -/

/-- The restricted class has the same `L²` seminorm as the class it restricts, measured against
the restricted measure. -/
theorem eLpNorm_restrictL2 (B : Set (EuclideanSpace ℝ (Fin d))) (X : EucL2 d) :
    eLpNorm (restrictL2 (Ω := B) X : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict B)
      = eLpNorm (X : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict B) :=
  eLpNorm_congr_ae (coeFn_restrictL2 X)

/-- Restricting a whole-space `L²` class to a set does not increase its norm. -/
theorem nnnorm_restrictL2_le (B : Set (EuclideanSpace ℝ (Fin d))) (X : EucL2 d) :
    ‖restrictL2 (Ω := B) X‖₊ ≤ ‖X‖₊ := by
  rw [Lp.nnnorm_def, Lp.nnnorm_def]
  refine ENNReal.toNNReal_mono (Lp.eLpNorm_ne_top X) ?_
  rw [eLpNorm_restrictL2]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- The `L²` seminorm of a whole-space class over a set is bounded by the class norm. -/
theorem eLpNorm_restrict_toNNReal_le (B : Set (EuclideanSpace ℝ (Fin d))) (X : EucL2 d) :
    (eLpNorm (X : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict B)).toNNReal ≤ ‖X‖₊ := by
  rw [Lp.nnnorm_def]
  exact ENNReal.toNNReal_mono (Lp.eLpNorm_ne_top X)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- The `L²` seminorm of a class on a set, measured over a smaller set, is bounded by the class
norm. -/
theorem eLpNorm_restrict_mono_toNNReal_le {S T : Set (EuclideanSpace ℝ (Fin d))} (hST : S ⊆ T)
    (X : Lp ℝ 2 (volume.restrict T)) :
    (eLpNorm (X : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict S)).toNNReal ≤ ‖X‖₊ := by
  rw [Lp.nnnorm_def]
  exact ENNReal.toNNReal_mono (Lp.eLpNorm_ne_top X)
    (eLpNorm_mono_measure _ (Measure.restrict_mono hST le_rfl))

/-! ### One-dimensional estimate -/

/-- **Interior Hölder estimate in one dimension (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.2 Thm 5).** A weak solution `u ∈ H₀¹(Ω)` of `L u = f` has, on every ball, a
representative that is Hölder continuous with exponent `1/2` and constant a multiple of
`‖f‖ + ‖u‖`, the multiplier being quantified before the solution and the datum, so it depends
only on the operator and the ball. In one dimension the first-order weak gradient already lies
in `L²` and `2 > 1`, so Morrey applies to it directly and only the first-order energy estimate
is used: neither the interior `H²` estimate nor any hypothesis on the geometry of `Ω` is
needed. -/
theorem interior_holder_estimate_one (Op : FullEllipticOp 1)
    {Ω : Set (EuclideanSpace ℝ (Fin 1))} (hΩm : MeasurableSet Ω)
    (c : EuclideanSpace ℝ (Fin 1)) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ u' : EuclideanSpace ℝ (Fin 1) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin 1) → ℝ) ∧
          HolderOnWith (C * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖)) (1 / 2 : ℝ≥0) u'
            (Metric.ball c r) := by
  classical
  have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  let dcoef: ℝ := Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam))
  have hdcoefdef : dcoef = Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) := rfl
  obtain ⟨C₀, hC₀⟩ := morrey_ball (d := 1) one_pos (by norm_num : ((1 : ℕ) : ℝ) < 2) c hr
  refine ⟨C₀ * Real.toNNReal dcoef, fun u f hu => ?_⟩
  let P: ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖
  have hPdef : P = ‖f‖ + ‖(u : H1amb Ω) 0‖ := rfl
  let X: EucL2 1 := extendL2 hΩm ((u : H1amb Ω) 0)
  have hXdef : X = extendL2 hΩm ((u : H1amb Ω) 0) := rfl
  let Y: Fin 1 → EucL2 1 := fun k => extendL2 hΩm ((u : H1amb Ω) k.succ)
  have hYdef : Y = fun k => extendL2 hΩm ((u : H1amb Ω) k.succ) := rfl
  let B: Set (EuclideanSpace ℝ (Fin 1)) := Metric.ball c r
  have hBdef : B = Metric.ball c r := rfl
  have hwg : HasWeakGradOn B (fun x => (restrictL2 (Ω := B) X x : ℝ))
      (fun k x => (restrictL2 (Ω := B) (Y k) x : ℝ)) :=
    hasWeakGradOn_of_hasWeakDerivOn fun k =>
      hasWeakDerivOn_of_hasWeakDeriv k (hasWeakDeriv_extendL2_of_mem_H01 hΩm k u.2)
  have hint : IntegrableOn (fun x => (restrictL2 (Ω := B) X x : ℝ)) B volume :=
    (Lp.memLp (restrictL2 (Ω := B) X)).integrable (by norm_num)
  have hmem : ∀ k, MemLp (fun x => (restrictL2 (Ω := B) (Y k) x : ℝ)) (ENNReal.ofReal 2)
      (volume.restrict B) := by
    intro k
    rw [h2]
    exact Lp.memLp _
  obtain ⟨u', hu'ae, hHol⟩ := hC₀ _ _ hint hmem hwg
  refine ⟨u', hu'ae.trans (coeFn_restrictL2 X), ?_⟩
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  have hd0 : (0 : ℝ) ≤ dcoef := Real.sqrt_nonneg _
  -- Each gradient component is bounded in `L²` by the first-order energy estimate.
  have hterm : ∀ k : Fin 1,
      (eLpNorm (fun x => (restrictL2 (Ω := B) (Y k) x : ℝ)) (ENNReal.ofReal 2)
        (volume.restrict B)).toNNReal ≤ Real.toNNReal dcoef * Real.toNNReal P := by
    intro k
    have hstep : (eLpNorm (fun x => (restrictL2 (Ω := B) (Y k) x : ℝ)) (ENNReal.ofReal 2)
        (volume.restrict B)).toNNReal = ‖restrictL2 (Ω := B) (Y k)‖₊ := by
      rw [h2, Lp.nnnorm_def]
    have hle : ‖restrictL2 (Ω := B) (Y k)‖₊ ≤ ‖(u : H1amb Ω) k.succ‖₊ :=
      (nnnorm_restrictL2_le B (Y k)).trans
        (le_of_eq (NNReal.coe_injective (by simp [hYdef])))
    have hbd : ‖(u : H1amb Ω) k.succ‖₊ ≤ Real.toNNReal dcoef * Real.toNNReal P := by
      rw [← Real.toNNReal_mul hd0, ← NNReal.coe_le_coe, coe_nnnorm,
        Real.coe_toNNReal _ (mul_nonneg hd0 hP0)]
      exact firstOrder_gradNorm_le Op u f hu k
    rw [hstep]
    exact hle.trans hbd
  rw [← morreyExponent_one_two]
  refine hHol.mono_const ?_
  calc C₀ * ∑ k : Fin 1, (eLpNorm (fun x => (restrictL2 (Ω := B) (Y k) x : ℝ))
          (ENNReal.ofReal 2) (volume.restrict B)).toNNReal
      ≤ C₀ * ∑ _k : Fin 1, Real.toNNReal dcoef * Real.toNNReal P :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun k _ => hterm k)
    _ = C₀ * Real.toNNReal dcoef * Real.toNNReal P := by simp [mul_assoc]

/-! ### Two-dimensional estimate -/

/-- **Interior Hölder estimate in two dimensions (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.2 Thm 5, applied to the interior `H²` estimate of §6.3.1 Thm 1).** A weak
solution `u ∈ H₀¹(Ω)` of `L u = f` with `W^{1,∞}` principal coefficients has, on every ball
`B(c, r)` with `r < R` and `closedBall c R ⊆ Ω`, a representative that is Hölder continuous with
exponent `1/2` and constant a multiple of `‖f‖ + ‖u‖`, the multiplier being quantified before
the solution and the datum, so it depends only on the operator and the two radii. The interior
`H²` estimate puts the second derivatives in `L²`; at `d = 2` the Sobolev conjugate of `2`
degenerates, so the bootstrap `exists_eLpNorm_four_le` takes its step at `p = 4/3`, paying the
finite measure of the ball, and raises the gradient from `L²` to `L⁴`. `morrey_ball` then
applies at `p = 4 > 2 = d`. -/
theorem interior_holder_estimate_two (Op : FullEllipticOp 2)
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    (c : EuclideanSpace ℝ (Fin 2)) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRΩ : Metric.closedBall c R ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ u' : EuclideanSpace ℝ (Fin 2) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin 2) → ℝ) ∧
          HolderOnWith (C * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖)) (1 / 2 : ℝ≥0) u'
            (Metric.ball c r) := by
  classical
  have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have h4 : ENNReal.ofReal (4 : ℝ) = 4 := by simp
  let dcoef: ℝ := Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam))
  have hdcoefdef : dcoef = Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) := rfl
  have hd0 : (0 : ℝ) ≤ dcoef := Real.sqrt_nonneg _
  -- The compact set of the interior `H²` estimate, and the two balls inside it.
  let V: Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall c R
  have hVdef : V = Metric.closedBall c R := rfl
  have hVc : IsCompact V := isCompact_closedBall c R
  have hballV : Metric.ball c R ⊆ V := Metric.ball_subset_closedBall
  obtain ⟨C₁, hC₁0, hC₁⟩ := interior_H2_estimate (n := 1) Op hΩm hΩo hA hVc hRΩ
  -- Morrey at `p = 4 > 2 = d`, and the bootstrap constant, both before the solution.
  obtain ⟨K, hK⟩ := exists_eLpNorm_four_le c hr hrR
  obtain ⟨C₀, hC₀⟩ := morrey_ball (d := 2) (by norm_num) (by norm_num : ((2 : ℕ) : ℝ) < 4) c hr
  refine ⟨C₀ * (2 * K * (Real.toNNReal dcoef + 2 * Real.toNNReal C₁)), fun u f hu => ?_⟩
  let P: ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖
  have hPdef : P = ‖f‖ + ‖(u : H1amb Ω) 0‖ := rfl
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  let Q: ℝ≥0 := Real.toNNReal P
  have hQdef : Q = Real.toNNReal P := rfl
  choose W hW hWb using hC₁ u f hu
  -- Names for the extension-by-zero representatives.
  let X0 : EuclideanSpace ℝ (Fin 2) → ℝ := (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin
    2) → ℝ)
  have hX0def : X0 = (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin 2) → ℝ) := rfl
  let X : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ := fun i => (extendL2 hΩm ((u : H1amb Ω) i.succ) :
    EuclideanSpace ℝ (Fin 2) → ℝ)
  have hXdef : X = fun i => (extendL2 hΩm ((u : H1amb Ω) i.succ) : EuclideanSpace ℝ (Fin 2) → ℝ) :=
    rfl
  -- The first-order weak gradient of `u` on the inner ball.
  have hgrad0 : HasWeakGradOn (Metric.ball c r) X0 X :=
    (hasWeakGradOn_of_hasWeakDerivOn fun k =>
      hasWeakDerivOn_of_hasWeakDeriv k (hasWeakDeriv_extendL2_of_mem_H01 hΩm k u.2)).congr_ae
      (coeFn_restrictL2 _) (fun k => coeFn_restrictL2 _)
  -- The second weak derivatives on the outer ball, in the `L²` form the bootstrap consumes.
  have hgradi : ∀ i, HasWeakGradOn (Metric.ball c R) (X i)
      (fun k => ((W k i : EuclideanSpace ℝ (Fin 2) → ℝ))) := by
    intro i
    exact ((hasWeakGradOn_of_hasWeakDerivOn fun k => hW k i).congr_ae
      (coeFn_restrictL2 _) (fun k => Filter.EventuallyEq.rfl)).mono hballV
  have hXL2 : ∀ i, MemLp (X i) 2 (volume.restrict (Metric.ball c R)) :=
    fun i => (Lp.memLp (extendL2 hΩm ((u : H1amb Ω) i.succ))).restrict _
  have hWL2 : ∀ (k i : Fin 2), MemLp ((W k i : EuclideanSpace ℝ (Fin 2) → ℝ)) 2
      (volume.restrict (Metric.ball c R)) :=
    fun k i => (Lp.memLp (W k i)).mono_measure (Measure.restrict_mono hballV le_rfl)
  -- The bootstrap raises each gradient component from `L²` to `L⁴` on the inner ball.
  have hfour : ∀ i, MemLp (X i) 4 (volume.restrict (Metric.ball c r))
      ∧ eLpNorm (X i) 4 (volume.restrict (Metric.ball c r))
        ≤ (K : ℝ≥0∞) * (eLpNorm (X i) 2 (volume.restrict (Metric.ball c R))
            + ∑ k, eLpNorm ((W k i : EuclideanSpace ℝ (Fin 2) → ℝ)) 2
                (volume.restrict (Metric.ball c R))) :=
    fun i => hK (X i) _ (hXL2 i) (fun k => hWL2 k i) (hgradi i)
  have hint : IntegrableOn X0 (Metric.ball c r) volume :=
    ((Lp.memLp (extendL2 hΩm ((u : H1amb Ω) 0))).restrict _).integrable (by norm_num)
  have hmem : ∀ i, MemLp (X i) (ENNReal.ofReal 4) (volume.restrict (Metric.ball c r)) := by
    intro i; rw [h4]; exact (hfour i).1
  obtain ⟨u', hu'ae, hHol⟩ := hC₀ X0 X hint hmem hgrad0
  refine ⟨u', hu'ae, ?_⟩
  -- Each `L⁴` seminorm is bounded by the data through the two energy estimates.
  have hXbd : ∀ i, (eLpNorm (X i) 2 (volume.restrict (Metric.ball c R))).toNNReal
      ≤ Real.toNNReal dcoef * Q := by
    intro i
    refine (eLpNorm_restrict_toNNReal_le _ _).trans ?_
    have : ‖extendL2 hΩm ((u : H1amb Ω) i.succ)‖₊ = ‖(u : H1amb Ω) i.succ‖₊ :=
      NNReal.coe_injective (by simp)
    rw [this, hQdef, ← Real.toNNReal_mul hd0, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ (mul_nonneg hd0 hP0)]
    exact firstOrder_gradNorm_le Op u f hu i
  have hWbd : ∀ k i : Fin 2,
      (eLpNorm ((W k i : EuclideanSpace ℝ (Fin 2) → ℝ)) 2
        (volume.restrict (Metric.ball c R))).toNNReal ≤ Real.toNNReal C₁ * Q := by
    intro k i
    refine (eLpNorm_restrict_mono_toNNReal_le hballV _).trans ?_
    rw [hQdef, ← Real.toNNReal_mul hC₁0, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ (mul_nonneg hC₁0 hP0)]
    have hpos := hWb k i
    have h1 : (0 : ℝ) ≤ ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖ :=
      norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖ :=
      norm_nonneg _
    linarith [hpos, h1, h2]
  have hterm : ∀ i, (eLpNorm (X i) (ENNReal.ofReal 4)
      (volume.restrict (Metric.ball c r))).toNNReal
      ≤ K * (Real.toNNReal dcoef + 2 * Real.toNNReal C₁) * Q := by
    intro i
    rw [h4]
    have hfin : ((K : ℝ≥0∞) * (eLpNorm (X i) 2 (volume.restrict (Metric.ball c R))
        + ∑ k, eLpNorm ((W k i : EuclideanSpace ℝ (Fin 2) → ℝ)) 2
            (volume.restrict (Metric.ball c R)))) ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr
        ⟨(hXL2 i).eLpNorm_lt_top, ENNReal.sum_lt_top.mpr fun k _ => (hWL2 k i).eLpNorm_lt_top⟩)).ne
    refine (ENNReal.toNNReal_mono hfin (hfour i).2).trans ?_
    rw [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe,
      ENNReal.toNNReal_add (hXL2 i).eLpNorm_lt_top.ne (ENNReal.sum_lt_top.mpr fun k _ => (hWL2
          k i).eLpNorm_lt_top).ne,
      ENNReal.toNNReal_sum fun k _ => (hWL2 k i).eLpNorm_lt_top.ne]
    refine le_trans (mul_le_mul' le_rfl
      (add_le_add (hXbd i) (Finset.sum_le_sum fun k _ => hWbd k i))) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [← morreyExponent_two_four]
  refine hHol.mono_const ?_
  calc C₀ * ∑ i : Fin 2, (eLpNorm (X i) (ENNReal.ofReal 4)
          (volume.restrict (Metric.ball c r))).toNNReal
      ≤ C₀ * ∑ _i : Fin 2, K * (Real.toNNReal dcoef + 2 * Real.toNNReal C₁) * Q :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hterm i)
    _ = C₀ * (2 * K * (Real.toNNReal dcoef + 2 * Real.toNNReal C₁)) * Q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ### Three-dimensional estimate -/

/-- **Interior Hölder estimate in three dimensions (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.2 Thm 5, applied to the interior `H²` estimate of §6.3.1 Thm 1).** A weak
solution `u ∈ H₀¹(Ω)` of `L u = f` with `W^{1,∞}` principal coefficients has, on every ball
`B(c, r)` with `r < R` and `closedBall c R ⊆ Ω`, a representative that is Hölder continuous with
exponent `1/2` and constant a multiple of `‖f‖ + ‖u‖`, the multiplier being quantified before
the solution and the datum, so it depends only on the operator and the two radii. The interior
`H²` estimate puts the second derivatives in `L²`, the Gagliardo-Nirenberg-Sobolev bootstrap
`exists_eLpNorm_six_le` raises the gradient from `L²` to `L⁶`, and `morrey_ball` applies at
`p = 6 > 3 = d`, so the weak solution is classically differentiable in the Hölder sense. -/
theorem interior_holder_estimate (Op : FullEllipticOp 3)
    {Ω : Set (EuclideanSpace ℝ (Fin 3))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    (c : EuclideanSpace ℝ (Fin 3)) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRΩ : Metric.closedBall c R ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ u' : EuclideanSpace ℝ (Fin 3) → ℝ,
        u' =ᵐ[volume.restrict (Metric.ball c r)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin 3) → ℝ) ∧
          HolderOnWith (C * Real.toNNReal (‖f‖ + ‖(u : H1amb Ω) 0‖)) (1 / 2 : ℝ≥0) u'
            (Metric.ball c r) := by
  classical
  have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have h6 : ENNReal.ofReal (6 : ℝ) = 6 := by simp
  let dcoef : ℝ := Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam))
  have hdcoefdef : dcoef = Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) := rfl
  have hd0 : (0 : ℝ) ≤ dcoef := Real.sqrt_nonneg _
  -- The compact set of the interior `H²` estimate, and the two balls inside it.
  let V: Set (EuclideanSpace ℝ (Fin 3)) := Metric.closedBall c R
  have hVdef : V = Metric.closedBall c R := rfl
  have hVc : IsCompact V := isCompact_closedBall c R
  have hballV : Metric.ball c R ⊆ V := Metric.ball_subset_closedBall
  obtain ⟨C₁, hC₁0, hC₁⟩ := interior_H2_estimate (n := 2) Op hΩm hΩo hA hVc hRΩ
  -- Morrey at `p = 6 > 3 = d`, and the bootstrap constant, both before the solution.
  obtain ⟨K, hK⟩ := exists_eLpNorm_six_le c hr hrR
  obtain ⟨C₀, hC₀⟩ := morrey_ball (d := 3) (by norm_num) (by norm_num : ((3 : ℕ) : ℝ) < 6) c hr
  refine ⟨C₀ * (3 * K * (Real.toNNReal dcoef + 3 * Real.toNNReal C₁)), fun u f hu => ?_⟩
  let P: ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖
  have hPdef : P = ‖f‖ + ‖(u : H1amb Ω) 0‖ := rfl
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  let Q: ℝ≥0 := Real.toNNReal P
  have hQdef : Q = Real.toNNReal P := rfl
  choose W hW hWb using hC₁ u f hu
  -- Names for the extension-by-zero representatives.
  let X0 : EuclideanSpace ℝ (Fin 3) → ℝ := (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin
    3) → ℝ)
  have hX0def : X0 = (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin 3) → ℝ) := rfl
  let X : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ := fun i => (extendL2 hΩm ((u : H1amb Ω) i.succ) :
    EuclideanSpace ℝ (Fin 3) → ℝ)
  have hXdef : X = fun i => (extendL2 hΩm ((u : H1amb Ω) i.succ) : EuclideanSpace ℝ (Fin 3) → ℝ) :=
    rfl
  -- The first-order weak gradient of `u` on the inner ball.
  have hgrad0 : HasWeakGradOn (Metric.ball c r) X0 X :=
    (hasWeakGradOn_of_hasWeakDerivOn fun k =>
      hasWeakDerivOn_of_hasWeakDeriv k (hasWeakDeriv_extendL2_of_mem_H01 hΩm k u.2)).congr_ae
      (coeFn_restrictL2 _) (fun k => coeFn_restrictL2 _)
  -- The second weak derivatives on the outer ball, in the `L²` form the bootstrap consumes.
  have hgradi : ∀ i, HasWeakGradOn (Metric.ball c R) (X i)
      (fun k => ((W k i : EuclideanSpace ℝ (Fin 3) → ℝ))) := by
    intro i
    exact ((hasWeakGradOn_of_hasWeakDerivOn fun k => hW k i).congr_ae
      (coeFn_restrictL2 _) (fun k => Filter.EventuallyEq.rfl)).mono hballV
  have hXL2 : ∀ i, MemLp (X i) 2 (volume.restrict (Metric.ball c R)) :=
    fun i => (Lp.memLp (extendL2 hΩm ((u : H1amb Ω) i.succ))).restrict _
  have hWL2 : ∀ (k i : Fin 3), MemLp ((W k i : EuclideanSpace ℝ (Fin 3) → ℝ)) 2
      (volume.restrict (Metric.ball c R)) :=
    fun k i => (Lp.memLp (W k i)).mono_measure (Measure.restrict_mono hballV le_rfl)
  -- The bootstrap raises each gradient component from `L²` to `L⁶` on the inner ball.
  have hsix : ∀ i, MemLp (X i) 6 (volume.restrict (Metric.ball c r))
      ∧ eLpNorm (X i) 6 (volume.restrict (Metric.ball c r))
        ≤ (K : ℝ≥0∞) * (eLpNorm (X i) 2 (volume.restrict (Metric.ball c R))
            + ∑ k, eLpNorm ((W k i : EuclideanSpace ℝ (Fin 3) → ℝ)) 2
                (volume.restrict (Metric.ball c R))) :=
    fun i => hK (X i) _ (hXL2 i) (fun k => hWL2 k i) (hgradi i)
  have hint : IntegrableOn X0 (Metric.ball c r) volume :=
    ((Lp.memLp (extendL2 hΩm ((u : H1amb Ω) 0))).restrict _).integrable (by norm_num)
  have hmem : ∀ i, MemLp (X i) (ENNReal.ofReal 6) (volume.restrict (Metric.ball c r)) := by
    intro i; rw [h6]; exact (hsix i).1
  obtain ⟨u', hu'ae, hHol⟩ := hC₀ X0 X hint hmem hgrad0
  refine ⟨u', hu'ae, ?_⟩
  -- Each `L⁶` seminorm is bounded by the data through the two energy estimates.
  have hXbd : ∀ i, (eLpNorm (X i) 2 (volume.restrict (Metric.ball c R))).toNNReal
      ≤ Real.toNNReal dcoef * Q := by
    intro i
    refine (eLpNorm_restrict_toNNReal_le _ _).trans ?_
    have : ‖extendL2 hΩm ((u : H1amb Ω) i.succ)‖₊ = ‖(u : H1amb Ω) i.succ‖₊ :=
      NNReal.coe_injective (by simp)
    rw [this, hQdef, ← Real.toNNReal_mul hd0, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ (mul_nonneg hd0 hP0)]
    exact firstOrder_gradNorm_le Op u f hu i
  have hWbd : ∀ k i : Fin 3,
      (eLpNorm ((W k i : EuclideanSpace ℝ (Fin 3) → ℝ)) 2
        (volume.restrict (Metric.ball c R))).toNNReal ≤ Real.toNNReal C₁ * Q := by
    intro k i
    refine (eLpNorm_restrict_mono_toNNReal_le hballV _).trans ?_
    rw [hQdef, ← Real.toNNReal_mul hC₁0, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ (mul_nonneg hC₁0 hP0)]
    have hpos := hWb k i
    have h1 : (0 : ℝ) ≤ ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖ :=
      norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖ :=
      norm_nonneg _
    linarith [hpos, h1, h2]
  have hterm : ∀ i, (eLpNorm (X i) (ENNReal.ofReal 6)
      (volume.restrict (Metric.ball c r))).toNNReal
      ≤ K * (Real.toNNReal dcoef + 3 * Real.toNNReal C₁) * Q := by
    intro i
    rw [h6]
    have hfin : ((K : ℝ≥0∞) * (eLpNorm (X i) 2 (volume.restrict (Metric.ball c R))
        + ∑ k, eLpNorm ((W k i : EuclideanSpace ℝ (Fin 3) → ℝ)) 2
            (volume.restrict (Metric.ball c R)))) ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr
        ⟨(hXL2 i).eLpNorm_lt_top, ENNReal.sum_lt_top.mpr fun k _ => (hWL2 k i).eLpNorm_lt_top⟩)).ne
    refine (ENNReal.toNNReal_mono hfin (hsix i).2).trans ?_
    rw [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe,
      ENNReal.toNNReal_add (hXL2 i).eLpNorm_lt_top.ne (ENNReal.sum_lt_top.mpr fun k _ => (hWL2
          k i).eLpNorm_lt_top).ne,
      ENNReal.toNNReal_sum fun k _ => (hWL2 k i).eLpNorm_lt_top.ne]
    refine le_trans (mul_le_mul' le_rfl
      (add_le_add (hXbd i) (Finset.sum_le_sum fun k _ => hWbd k i))) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [← morreyExponent_three_six]
  refine hHol.mono_const ?_
  calc C₀ * ∑ i : Fin 3, (eLpNorm (X i) (ENNReal.ofReal 6)
          (volume.restrict (Metric.ball c r))).toNNReal
      ≤ C₀ * ∑ _i : Fin 3, K * (Real.toNNReal dcoef + 3 * Real.toNNReal C₁) * Q :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hterm i)
    _ = C₀ * (3 * K * (Real.toNNReal dcoef + 3 * Real.toNNReal C₁)) * Q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end EllipticPdes.Embedding
