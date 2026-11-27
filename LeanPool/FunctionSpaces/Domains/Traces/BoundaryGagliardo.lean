/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Traces.TraceSpaceNorm
public import LeanPool.FunctionSpaces.Rd.Differences.SobolevSlobodeckij

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Sobolev–Slobodeckij norm on the boundary of a bounded Lipschitz domain

Let `Ω` be a bounded Lipschitz domain in `V`, `dim V = n`, with boundary `Γ`, surface measure `σ`,
charts `γ_j : H_j → V` and a resolution of unity `(ψ_j)` on `Γ`.

* **The Gagliardo form on `Γ`** (`Rd.BoundedLipschitzDomain.boundarySlobodeckijForm`; Gagliardo
  1957): `∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ(y) dσ(x)`, chart-free. Double integrals
  over a boundary ball are double integrals in the chart
  (`Rd.BoundedLipschitzDomain.lintegral_lintegral_surfaceMeasure_of_support`).
* **The upper bound** (`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`): for
  `1 ≤ p < ∞` and `s > 0` the form is at most `C ‖g‖_{B^s_{p,p}(Γ)}^p` for the chart-wise norm
  (`Rd.BoundedLipschitzDomain.boundaryBesovNorm`). The pieces `ψ_j g` are localised in the balls
  `B_j`, and in the chart the Gagliardo form of `H_j` is bounded by the first-difference norm
  (`Rd.slobodeckijForm_le`).
* **The lower bound** (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le`): for
  `0 < s < 1`, `‖g‖_{B^s_{p,p}(Γ)}^p ≤ C (‖g‖_{L_p(Γ)}^p + ∫_Γ ∫_Γ …)`. The Gagliardo form on
  `H_j` of each chart piece `(ψ_j g) ∘ γ_j` is split into a part inside `B_j`, a part with the
  Lipschitz differences of `ψ_j` and a tail
  (`Rd.BoundedLipschitzDomain.slobodeckijForm_chartPiece_le`), and it bounds the first-difference
  norm (`Rd.lqNorm_modulus_rpow_le_slobodeckijForm`).
* **Gagliardo's description of the boundary spaces**: for `g ∈ L_p(Γ)`, `g ∈ B^s_{p,p}(Γ)` iff
  the form is finite
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top`), so
  `W^{s,p}(Γ) = B^s_{p,p}(Γ)`. For `p = 2`, `s = 1/2`, the norm of `H^{1/2}(Γ)` is equivalent to
  `(‖τ t‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |τ t(y) - τ t(x)|² / |y - x|^n dσ dσ)^(1/2)`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`), and the range of
  `τ : H^{1/2}(Γ) → L_2(Γ)` is the set where the form is finite
  (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff_slobodeckij`).

The constants depend on `Ω`, `ψ`, `p` and `s` and are fixed before the functions. The results
hold in every dimension `n ≥ 1`; for `n = 1` the hyperplanes are points and `Γ` is finite.
-/

@[expose] public section

open MeasureTheory Filter Metric Module Set
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### Gagliardo integrands and double integrals -/

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

/-- **Points inside and outside two concentric balls are far apart**: for `y ∈ B(c, r)` and
`x ∉ B(c, R)`, `R - r ≤ |y - x|`, by the triangle inequality. -/
theorem sub_le_norm_sub_of_mem_ball {c x y : E} {r R : ℝ} (hy : y ∈ ball c r)
    (hx : x ∉ ball c R) : R - r ≤ ‖y - x‖ := by
  rw [mem_ball] at hy hx
  have h := dist_triangle x y c
  rw [dist_eq_norm x y, norm_sub_rev] at h
  linarith

/-- **The Gagliardo integrand of a function supported in a ball**: if `f` vanishes outside
`B(c, r)` and `r ≤ R`, then for all `x, y`, `P > 0` and `a ≥ 0`,
`|f(y) - f(x)|^P / |y - x|^a ≤ 1_{B(c,R)²}(x, y) |f(y) - f(x)|^P / |y - x|^a +
|f(x)|^P / (R - r)^a + |f(y)|^P / (R - r)^a`. If one point lies outside `B(c, R)`, then `f`
vanishes there, and the other point is at distance at least `R - r` where `f` does not vanish
(`Rd.sub_le_norm_sub_of_mem_ball`). -/
theorem slobodeckijIntegrand_le_of_support {c : E} {r R : ℝ} (hr : r ≤ R) {f : E → ℂ}
    (hf0 : ∀ y, f y ≠ 0 → y ∈ ball c r) {P : ℝ} (hP : 0 < P) {a : ℝ} (ha : 0 ≤ a) (x y : E) :
    ‖f y - f x‖ₑ ^ P / ‖y - x‖ₑ ^ a ≤
      (ball c R ×ˢ ball c R).indicator (fun z : E × E => ‖f z.2 - f z.1‖ₑ ^ P / ‖z.2 - z.1‖ₑ ^ a)
          (x, y) + ‖f x‖ₑ ^ P / ENNReal.ofReal (R - r) ^ a +
        ‖f y‖ₑ ^ P / ENNReal.ofReal (R - r) ^ a := by
  have hfar : ∀ {u v : E}, f u ≠ 0 → v ∉ ball c R →
      ‖f u‖ₑ ^ P / ‖u - v‖ₑ ^ a ≤ ‖f u‖ₑ ^ P / ENNReal.ofReal (R - r) ^ a := fun hu hv => by
    refine ENNReal.div_le_div_left (ENNReal.rpow_le_rpow ?_ ha) _
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (sub_le_norm_sub_of_mem_ball (hf0 _ hu) hv)
  have hzero : ∀ {u : E}, u ∉ ball c R → f u = 0 := fun hu =>
    by_contra fun h => hu (ball_subset_ball hr (hf0 _ h))
  by_cases hxy : (x, y) ∈ ball c R ×ˢ ball c R
  · rw [indicator_of_mem hxy, add_assoc]
    exact le_self_add
  rw [indicator_of_notMem hxy, zero_add]
  rcases not_and_or.1 (mem_prod.not.1 hxy) with hx | hy
  · rw [hzero hx, sub_zero]
    by_cases hfy : f y = 0
    · rw [hfy, eNorm_zero, ENNReal.zero_rpow_of_pos hP, ENNReal.zero_div]
      exact zero_le
    · exact (hfar hfy hx).trans le_add_self
  · rw [hzero hy, zero_sub, eNorm_neg, eNorm_sub_rev]
    by_cases hfx : f x = 0
    · rw [hfx, eNorm_zero, ENNReal.zero_rpow_of_pos hP, ENNReal.zero_div]
      exact zero_le
    · exact (hfar hfx hy).trans le_self_add

end NormedGroup

/-- **The difference of two products**: `|a b - c d| ≤ |a| |b - d| + |a - c| |d|` for complex
numbers, from `a b - c d = a (b - d) + (a - c) d`. -/
theorem enorm_mul_sub_mul_le (a b c d : ℂ) :
    ‖a * b - c * d‖ₑ ≤ ‖a‖ₑ * ‖b - d‖ₑ + ‖a - c‖ₑ * ‖d‖ₑ := by
  rw [show a * b - c * d = a * (b - d) + (a - c) * d by ring, ← eNorm_mul, ← eNorm_mul]
  exact eNorm_add_le _ _

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : BoundedLipschitzDomain V)

/-! ### The Gagliardo form on the boundary -/

/-- **The Gagliardo form on the boundary** `Γ` of a bounded Lipschitz domain in `V`, `dim V = n`:
`∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n - 1 + sp) dσ(y) dσ(x)` with the surface measure `σ`, for
`0 < p < ∞` the `p`-th power of the Gagliardo seminorm of the Sobolev–Slobodeckij space
`W^{s,p}(Γ)` of the `(n-1)`-dimensional surface `Γ` (Gagliardo 1957). For `p = 2`, `s = 1/2` the
exponent is `n`. -/
noncomputable def boundarySlobodeckijForm (p : ℝ≥0∞) (s : ℝ) (g : V → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ‖g y - g x‖ₑ ^ p.toReal /
    ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ∂Ω.surfaceMeasure ∂Ω.surfaceMeasure

omit [FiniteDimensional ℝ V] in
/-- The Gagliardo form on the boundary depends only on the class of `g` modulo null sets of the
surface measure. -/
theorem boundarySlobodeckijForm_congr_ae {g h : V → ℂ} (hgh : g =ᵐ[Ω.surfaceMeasure] h)
    (p : ℝ≥0∞) (s : ℝ) : Ω.boundarySlobodeckijForm p s g = Ω.boundarySlobodeckijForm p s h :=
  lintegral_congr_ae (hgh.mono fun x hx => lintegral_congr_ae (hgh.mono fun y hy => by
    simp only [hx, hy]))

/-- **Double integrals over a boundary ball in the chart**: for every `F : V → V → [0, ∞]` that
vanishes unless both points lie in `B_j`,
`∫_Γ ∫_Γ F(x, y) dσ(y) dσ(x) = ∫_{H_j} ∫_{H_j} F(γ_j x', γ_j y') w(y') w(x') dy' dx'` with the
density `w = √(1 + ‖∇φ_j‖²)`, by the chart formula
`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure_of_support` twice. It holds for every `F`,
measurable or not. -/
theorem lintegral_lintegral_surfaceMeasure_of_support (j : Fin Ω.N) (F : V → V → ℝ≥0∞)
    (hF : ∀ x y, F x y ≠ 0 →
      x ∈ ball (Ω.center j) (Ω.radius j) ∧ y ∈ ball (Ω.center j) (Ω.radius j)) :
    ∫⁻ x, ∫⁻ y, F x y ∂Ω.surfaceMeasure ∂Ω.surfaceMeasure =
      ∫⁻ x', ∫⁻ y', F ((Ω.graph j).graphMap x') ((Ω.graph j).graphMap y') *
        ENNReal.ofReal ((Ω.graph j).gram y') * ENNReal.ofReal ((Ω.graph j).gram x') := by
  have hin : ∀ x, ∫⁻ y, F x y ∂Ω.surfaceMeasure =
      ∫⁻ y', F x ((Ω.graph j).graphMap y') * ENNReal.ofReal ((Ω.graph j).gram y') := fun x =>
    Ω.lintegral_surfaceMeasure_of_support j (F x) fun y hy => (hF x y hy).2
  simp_rw [hin]
  rw [Ω.lintegral_surfaceMeasure_of_support j _ fun x hx => by_contra fun hxB => hx (by
    have h0 : ∀ y, F x y = 0 := fun y => by_contra fun h => hxB (hF x y h).1
    simp only [h0, zero_mul, lintegral_zero])]
  exact lintegral_congr fun x' => (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm

/-- **Double integrals in the chart are at most those over `Γ`**: for every `F : V → V → [0, ∞]`
that vanishes unless both points lie in `B_j`,
`∫_{H_j} ∫_{H_j} F(γ_j x', γ_j y') dy' dx' ≤ ∫_Γ ∫_Γ F dσ dσ`, since the density
`√(1 + ‖∇φ_j‖²)` is at least `1` (`Rd.LipschitzGraph.one_le_ofReal_gram`). -/
theorem lintegral_lintegral_chart_le (j : Fin Ω.N) (F : V → V → ℝ≥0∞)
    (hF : ∀ x y, F x y ≠ 0 →
      x ∈ ball (Ω.center j) (Ω.radius j) ∧ y ∈ ball (Ω.center j) (Ω.radius j)) :
    ∫⁻ x', ∫⁻ y', F ((Ω.graph j).graphMap x') ((Ω.graph j).graphMap y') ≤
      ∫⁻ x, ∫⁻ y, F x y ∂Ω.surfaceMeasure ∂Ω.surfaceMeasure := by
  rw [Ω.lintegral_lintegral_surfaceMeasure_of_support j F hF]
  exact lintegral_mono fun x' => lintegral_mono fun y' =>
    le_mul_of_one_le_right' ((Ω.graph j).one_le_ofReal_gram x') |>.trans'
      (le_mul_of_one_le_right' ((Ω.graph j).one_le_ofReal_gram y'))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The functions of `B^s_{p,q}(Γ)` are measurable on `Γ`**: every `g ∈ B^s_{p,q}(Γ)` is
almost everywhere strongly measurable for the surface measure. On `B_j`, `ψ_j g` is
`σ`-almost everywhere the chart piece `G_j ∈ L_p(H_j)` composed with the projection `P_j`
(`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_ball_iff`), it vanishes outside `B_j`, and
`g = ∑_j ψ_j g` on `Γ`. -/
theorem aestronglyMeasurable_of_memBoundaryBesov (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    {g : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g) :
    AEStronglyMeasurable g Ω.surfaceMeasure := by
  choose G hG _ using hg
  have hj : ∀ j, (fun y => ψ.toComplex j y * g y) =ᵐ[Ω.surfaceMeasure]
      (ball (Ω.center j) (Ω.radius j)).indicator fun y => G j ((Ω.graph j).proj y) := by
    intro j
    have h1 := (Ω.ae_surfaceMeasure_ball_iff j (P := fun y => ψ.toComplex j y * g y =
      (ball (Ω.center j) (Ω.radius j)).indicator (fun y => G j ((Ω.graph j).proj y)) y)).2
      ((hG j).mono fun x' hx' hB => by
        rw [indicator_of_mem hB, (Ω.graph j).proj_graphMap, hx'])
    filter_upwards [h1] with y hy
    by_cases hyB : y ∈ ball (Ω.center j) (Ω.radius j)
    · exact hy hyB
    · have hψ : ψ.toFun j y = 0 := by_contra fun h => hyB (ψ.mem_ball_of_ne_zero h)
      rw [ψ.toComplex_of_eq_zero hψ, zero_mul, indicator_of_notMem hyB]
  refine AEStronglyMeasurable.congr (f := fun y => ∑ j, (ball (Ω.center j) (Ω.radius j)).indicator
    (fun y => G j ((Ω.graph j).proj y)) y) (Finset.stronglyMeasurable_fun_sum Finset.univ fun j _ =>
    ((Lp.stronglyMeasurable (G j)).comp_measurable
      (Ω.graph j).proj.continuous.measurable).indicator measurableSet_ball).aestronglyMeasurable ?_
  filter_upwards [ae_all_iff.2 hj, Ω.ae_eq_sum_mul ψ g] with y h1 h2
  rw [h2]
  exact Finset.sum_congr rfl fun j _ => (h1 j).symm

/-- **The Gagliardo form of a finite sum**: for `1 ≤ p < ∞` and measurable `f_i`, the Gagliardo
form on `Γ` of `∑_{i ∈ t} f_i` is at most `(#t)^(p-1)` times the sum of the forms of the `f_i`, by
the triangle inequality and Hölder's inequality for finite sums (Mathlib's
`ENNReal.rpow_sum_le_const_mul_sum_rpow`). -/
theorem boundarySlobodeckijForm_finsetSum_le (hp : p ≠ ∞) (s : ℝ) {ι : Type*} (t : Finset ι)
    {f : ι → V → ℂ} (hf : ∀ i, Measurable (f i)) :
    Ω.boundarySlobodeckijForm p s (fun y => ∑ i ∈ t, f i y) ≤
      (t.card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ i ∈ t, Ω.boundarySlobodeckijForm p s (f i) := by
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  have hc : (t.card : ℝ≥0∞) ^ (p.toReal - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _)
  have hpt : ∀ x y : V, ‖(∑ i ∈ t, f i y) - ∑ i ∈ t, f i x‖ₑ ^ p.toReal /
      ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ≤
      (t.card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ i ∈ t, ‖f i y - f i x‖ₑ ^ p.toReal /
        ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) := fun x y => by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i ∈ t, (f i y - f i x)‖ₑ ^ p.toReal /
          ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)
        ≤ ((t.card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ i ∈ t, ‖f i y - f i x‖ₑ ^ p.toReal) /
          ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) :=
          ENNReal.div_le_div_right ((ENNReal.rpow_le_rpow (eNorm_sum_le _ _) (by linarith)).trans
            (ENNReal.rpow_sum_le_const_mul_sum_rpow (s := t)
              (f := fun i => ‖f i y - f i x‖ₑ) hP1)) _
      _ = _ := by simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]
  have hm := fun i => measurable_slobodeckijIntegrand (hf i) p.toReal
    (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)
  have hy : ∀ i (x : V), Measurable fun y : V => ‖f i y - f i x‖ₑ ^ p.toReal /
      ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) := fun i x =>
    (hm i).comp measurable_prodMk_left
  have hx : ∀ i, Measurable fun x : V => ∫⁻ y, ‖f i y - f i x‖ₑ ^ p.toReal /
      ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ∂Ω.surfaceMeasure := fun i =>
    (hm i).lintegral_prod_right'
  calc Ω.boundarySlobodeckijForm p s (fun y => ∑ i ∈ t, f i y)
      ≤ ∫⁻ x, ∫⁻ y, (t.card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ i ∈ t, ‖f i y - f i x‖ₑ ^ p.toReal /
          ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ∂Ω.surfaceMeasure
            ∂Ω.surfaceMeasure := lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = _ := by
        rw [lintegral_congr fun x => (lintegral_const_mul' _ _ hc).trans (congrArg _
          (lintegral_finsetSum t fun i _ => hy i x)), lintegral_const_mul' _ _ hc,
          lintegral_finsetSum t fun i _ => hx i]
        rfl

/-! ### The upper bound by the chart-wise Besov norm -/

/-- **The part of the Gagliardo form inside one boundary ball**: for every `f : V → ℂ` and
`s ≥ 0`, `∫_Γ ∫_Γ 1_{B_j²}(x, y) |f(y) - f(x)|^p / |y - x|^(n-1+sp) dσ(y) dσ(x)` is at most
`(1 + M_j²)` times the Gagliardo form on `H_j` of `f ∘ γ_j`: the chart formula
(`Rd.BoundedLipschitzDomain.lintegral_lintegral_surfaceMeasure_of_support`), the bound
`√(1 + M_j²)` of the density, and `|y' - x'| ≤ |γ_j y' - γ_j x'|`. -/
theorem lintegral_lintegral_indicator_le_slobodeckijForm (j : Fin Ω.N) (f : V → ℂ) (p : ℝ≥0∞)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ x, ∫⁻ y, (ball (Ω.center j) (Ω.radius j) ×ˢ ball (Ω.center j) (Ω.radius j)).indicator
        (fun z : V × V => ‖f z.2 - f z.1‖ₑ ^ p.toReal /
          ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) (x, y)
        ∂Ω.surfaceMeasure ∂Ω.surfaceMeasure ≤
      ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ^ 2 *
        slobodeckijForm p s (fun x' => f ((Ω.graph j).graphMap x')) := by
  have ha : 0 ≤ ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by positivity
  have hc : ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [Ω.lintegral_lintegral_surfaceMeasure_of_support j _ fun x y h =>
      mem_prod.1 (mem_of_indicator_ne_zero h),
    slobodeckijForm, (Ω.graph j).finrank_hyperplane_eq_sub_one, sq,
    ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hc hc)]
  refine lintegral_mono fun x' => ?_
  rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hc hc)]
  refine lintegral_mono fun y' => ?_
  have h1 := (Set.indicator_le_self (ball (Ω.center j) (Ω.radius j) ×ˢ
    ball (Ω.center j) (Ω.radius j)) (fun z : V × V => ‖f z.2 - f z.1‖ₑ ^ p.toReal /
      ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)))
    ((Ω.graph j).graphMap x', (Ω.graph j).graphMap y')
  have h2 := ENNReal.div_le_div_left (ENNReal.rpow_le_rpow
    ((Ω.graph j).enorm_sub_le_enorm_graphMap_sub y' x') ha)
    (‖f ((Ω.graph j).graphMap y') - f ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal)
  calc _ ≤ (‖f ((Ω.graph j).graphMap y') - f ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal /
        ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) *
          ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) * ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) :=
        mul_le_mul' (mul_le_mul' (h1.trans h2)
          (ENNReal.ofReal_le_ofReal ((Ω.graph j).gram_le y')))
          (ENNReal.ofReal_le_ofReal ((Ω.graph j).gram_le x'))
    _ = _ := by ring

omit [Fact (1 ≤ p)] in
/-- **The Gagliardo form of a function supported in a boundary ball**: let `f : V → ℂ` be
measurable and vanish outside `B(c_j, r)` with `r < r_j`, the radius of `B_j`. For `0 < p < ∞`
and `s ≥ 0`, `∫_Γ ∫_Γ |f(y) - f(x)|^p / |y - x|^(n-1+sp) dσ dσ` is at most
`(1 + M_j²) [f ∘ γ_j]_{W^{s,p}(H_j)}^p + 2 σ(Γ) (r_j - r)^(-(n-1+sp)) ∫_Γ |f|^p dσ`: the pairs in
`B_j²` go to the chart
(`Rd.BoundedLipschitzDomain.lintegral_lintegral_indicator_le_slobodeckijForm`), the other pairs
are at distance at least `r_j - r` (`Rd.slobodeckijIntegrand_le_of_support`). -/
theorem boundarySlobodeckijForm_le_of_support (j : Fin Ω.N) {r : ℝ} (hr : r < Ω.radius j)
    {f : V → ℂ} (hf : Measurable f) (hf0 : ∀ y, f y ≠ 0 → y ∈ ball (Ω.center j) r)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {s : ℝ} (hs : 0 ≤ s) :
    Ω.boundarySlobodeckijForm p s f ≤ ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ^ 2 *
        slobodeckijForm p s (fun x' => f ((Ω.graph j).graphMap x')) +
      2 * Ω.surfaceMeasure univ /
          ENNReal.ofReal (Ω.radius j - r) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
        ∫⁻ y, ‖f y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure := by
  have hP := ENNReal.toReal_pos hp0 hp
  have ha : 0 ≤ ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by positivity
  have hm : Measurable fun x : V => ‖f x‖ₑ ^ p.toReal /
      ENNReal.ofReal (Ω.radius j - r) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) :=
    (hf.eNorm.pow_const _).div_const _
  refine (lintegral_lintegral_le_add_two_mul hm fun x y =>
    slobodeckijIntegrand_le_of_support hr.le hf0 hP ha x y).trans
    (add_le_add (Ω.lintegral_lintegral_indicator_le_slobodeckijForm j f p hs) (le_of_eq ?_))
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ (hf.eNorm.pow_const _)]
  ring

/-- **The Gagliardo form of one localised piece, by its chart piece**: for `1 ≤ p < ∞`, `s > 0`,
a resolution of unity `ψ` and a chart `j` there is `C < ∞` such that for every measurable `g` and
every `G ∈ L_p(H_j)` with `G = (ψ_j g) ∘ γ_j` almost everywhere,
`[ψ_j g]_{W^{s,p}(Γ)}^p ≤ C (‖G‖_p + ‖(2^(ks) ω_1(G, 2^(-k))_p)_k‖_{ℓ_p})^p`, by
`Rd.BoundedLipschitzDomain.boundarySlobodeckijForm_le_of_support` and the bound of the Gagliardo
form on `H_j` (`Rd.slobodeckijForm_le`). -/
theorem exists_boundarySlobodeckijForm_mul_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, Measurable g →
      ∀ G : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane),
        (G : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
          (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) →
        Ω.boundarySlobodeckijForm p s (fun y => ψ.toComplex j y * g y) ≤
          C * (‖G‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k)) ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport _) (ψ.tsupport_subset j)
  have hf0 : ∀ g : V → ℂ, ∀ y, ψ.toComplex j y * g y ≠ 0 → y ∈ ball (Ω.center j) r :=
    fun g y hy => hsub (subset_tsupport _ fun h =>
      left_ne_zero_of_mul hy (ψ.toComplex_of_eq_zero h))
  have hδ : ENNReal.ofReal (Ω.radius j - r) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (sub_pos.2 hr)) ENNReal.ofReal_ne_top).ne'
  refine ⟨ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ^ 2 *
      slobodeckijConstLower (Ω.graph j).hyperplane p s +
    2 * Ω.surfaceMeasure univ /
      ENNReal.ofReal (Ω.radius j - r) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
      ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2), ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (slobodeckijConstLower_ne_top hp0 hp hs),
      ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (measure_ne_top _ _)) hδ) ENNReal.ofReal_ne_top⟩, fun g hg G hG => ?_⟩
  have hGP : ‖G‖ₑ ^ p.toReal = ∫⁻ x', ‖ψ.toComplex j ((Ω.graph j).graphMap x') *
      g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal := by
    rw [Lp.eNorm_def, eLpNorm_rpow_eq (Lp.aestronglyMeasurable G) hp0 hp]
    exact lintegral_congr_ae (hG.mono fun x' hx' => by dsimp only; rw [hx'])
  have hL : ∫⁻ y, ‖ψ.toComplex j y * g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure ≤
      ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) * ‖G‖ₑ ^ p.toReal := by
    rw [hGP]
    refine Ω.lintegral_le_chart j _ fun y hy => ball_subset_ball hr.le (hf0 g y fun h => hy ?_)
    rw [h, eNorm_zero, ENNReal.zero_rpow_of_pos hP]
  have hS : slobodeckijForm p s (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
      g ((Ω.graph j).graphMap x')) ≤ slobodeckijConstLower (Ω.graph j).hyperplane p s *
        (‖G‖ₑ ^ p.toReal +
          lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k) ^ p.toReal) := by
    rw [← slobodeckijForm_congr_ae hG]
    exact slobodeckijForm_le hp hs G
  have hsum := ENNReal.add_rpow_le_rpow_add ‖G‖ₑ
    (lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k)) hP1
  have hone : ‖G‖ₑ ^ p.toReal ≤
      (‖G‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k)) ^ p.toReal :=
    ENNReal.rpow_le_rpow le_self_add hP.le
  calc Ω.boundarySlobodeckijForm p s (fun y => ψ.toComplex j y * g y)
      ≤ _ := Ω.boundarySlobodeckijForm_le_of_support j hr
        ((ψ.contDiff_toComplex j).continuous.measurable.mul hg) (hf0 g) hp0 hp hs.le
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (hS.trans (mul_le_mul' le_rfl hsum)))
        (mul_le_mul' le_rfl (hL.trans (mul_le_mul' le_rfl hone)))
    _ = _ := by ring

/-- **The Gagliardo form by the chart-wise Besov norm** (the upper half of Gagliardo's description
of `B^s_{p,p}(Γ)`): for `1 ≤ p < ∞`, `s > 0` and a resolution of unity `ψ` there is `C < ∞` with
`∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ dσ ≤ C ‖g‖_{B^s_{p,p}(Γ)}^p` for every `g`. For
`g ∈ B^s_{p,p}(Γ)`, `g` is measurable on `Γ`
(`Rd.BoundedLipschitzDomain.aestronglyMeasurable_of_memBoundaryBesov`), `g = ∑_j ψ_j g` on `Γ`,
the form of the sum is at most `N^(p-1)` times the sum of the forms
(`Rd.BoundedLipschitzDomain.boundarySlobodeckijForm_finsetSum_le`), and each piece is bounded by
its chart piece (`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_mul_le`); otherwise the
right side is `∞`. -/
theorem exists_boundarySlobodeckijForm_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 < s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ,
      Ω.boundarySlobodeckijForm p s g ≤ C * Ω.boundaryBesovNorm p ψ s p g ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  choose C hC hle using fun j => Ω.exists_boundarySlobodeckijForm_mul_le ψ j hp hs
  refine ⟨((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ j, C j + 1,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.natCast_ne_top _)) (ENNReal.sum_ne_top.2 fun j _ => hC j), ENNReal.one_ne_top⟩,
    fun g => ?_⟩
  by_cases hg : Ω.MemBoundaryBesov p ψ s p g
  swap
  · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hg, ENNReal.top_rpow_of_pos hP,
      ENNReal.mul_top (by positivity)]
    exact le_top
  have hm := Ω.aestronglyMeasurable_of_memBoundaryBesov ψ hg
  have hae := Ω.ae_surfaceMeasure_iff_aeBoundary.1 hm.ae_eq_mk
  have hmk : Measurable (hm.mk g) := hm.stronglyMeasurable_mk.measurable
  rw [Ω.boundarySlobodeckijForm_congr_ae hm.ae_eq_mk, Ω.boundaryBesovNorm_congr ψ hae]
  choose G hG _ using hg.congr hae
  have hpiece : ∀ j, (‖G j‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 (G j) k)) ^
      p.toReal ≤ Ω.boundaryBesovNorm p ψ s p (hm.mk g) ^ p.toReal := fun j => by
    rw [Ω.boundaryBesovNorm_eq_sum ψ G hG]
    exact ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun j =>
      ‖G j‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 (G j) k))
      (fun _ _ => zero_le) (Finset.mem_univ j)) hP.le
  calc Ω.boundarySlobodeckijForm p s (hm.mk g)
      = Ω.boundarySlobodeckijForm p s (fun y => ∑ j, ψ.toComplex j y * hm.mk g y) :=
        Ω.boundarySlobodeckijForm_congr_ae (Ω.ae_eq_sum_mul ψ _) p s
    _ ≤ ((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) *
          ∑ j, Ω.boundarySlobodeckijForm p s (fun y => ψ.toComplex j y * hm.mk g y) :=
        Ω.boundarySlobodeckijForm_finsetSum_le hp s _ fun j =>
          (ψ.contDiff_toComplex j).continuous.measurable.mul hmk
    _ ≤ ((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) *
          ∑ j, C j * Ω.boundaryBesovNorm p ψ s p (hm.mk g) ^ p.toReal :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ =>
          (hle j _ hmk (G j) (hG j)).trans (mul_le_mul' le_rfl (hpiece j)))
    _ ≤ _ := by
        rw [← Finset.sum_mul, ← mul_assoc]
        exact mul_le_mul' le_self_add le_rfl

/-! ### The lower bound by the Gagliardo form -/

/-- **The `L_p` norm of a chart piece**: for `P > 0`,
`∫_{H_j} |ψ_j(γ_j x') g(γ_j x')|^P dx' ≤ D_j^P ∫_Γ |g|^P dσ` with `D_j = ψ.derivBound j`
(`Rd.BoundedLipschitzDomain.lintegral_chart_le`). -/
theorem lintegral_chartPiece_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {P : ℝ} (hP : 0 < P)
    (g : V → ℂ) :
    ∫⁻ x', ‖ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P ≤
      ENNReal.ofReal (ψ.derivBound j) ^ P * ∫⁻ y, ‖g y‖ₑ ^ P ∂Ω.surfaceMeasure := by
  refine (Ω.lintegral_chart_le j (fun y => ‖ψ.toComplex j y * g y‖ₑ ^ P) fun y hy =>
    ψ.mem_ball_of_ne_zero fun h => hy ?_).trans ?_
  · rw [ψ.toComplex_of_eq_zero h, zero_mul, eNorm_zero, ENNReal.zero_rpow_of_pos hP]
  · rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun y => ?_
    rw [eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hP.le]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (ψ.enorm_toComplex_le j y) hP.le) le_rfl

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The integrand of a chart piece, by the product rule for differences**: for `P ≥ 1`,
`a ≥ 0`, the chart piece `G = (ψ_j g) ∘ γ_j` and all `x', y' ∈ H_j`,
`|G(y') - G(x')|^P / |y' - x'|^a ≤ 2^(P-1) (D_j^P (1 + M_j)^a |g(γ y') - g(γ x')|^P /
|γ y' - γ x'|^a + |g(γ x')|^P |ψ_j(γ y') - ψ_j(γ x')|^P / |y' - x'|^a)`, from
`G(y') - G(x') = ψ_j(γ y') (g(γ y') - g(γ x')) + (ψ_j(γ y') - ψ_j(γ x')) g(γ x')` and
`|γ y' - γ x'| ≤ (1 + M_j) |y' - x'|`. -/
theorem chartPiece_integrand_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {P : ℝ} (hP1 : 1 ≤ P)
    {a : ℝ} (ha : 0 ≤ a) (g : V → ℂ) (x' y' : (Ω.graph j).hyperplane) :
    ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y') -
        ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P /
        ‖y' - x'‖ₑ ^ a ≤
      2 ^ (P - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ P * ENNReal.ofReal (1 + (Ω.graph j).M) ^ a *
          (‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ ^ P /
            ‖(Ω.graph j).graphMap y' - (Ω.graph j).graphMap x'‖ₑ ^ a) +
        ‖g ((Ω.graph j).graphMap x')‖ₑ ^ P *
          (‖ψ.toComplex j ((Ω.graph j).graphMap y') -
            ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ P / ‖y' - x'‖ₑ ^ a)) := by
  have hP : 0 ≤ P := by linarith
  have hM : 0 < 1 + (Ω.graph j).M := by linarith [(Ω.graph j).M_nonneg]
  have h2 : ‖ψ.toComplex j ((Ω.graph j).graphMap y')‖ₑ ^ P *
      (‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ ^ P / ‖y' - x'‖ₑ ^ a) ≤
      ENNReal.ofReal (ψ.derivBound j) ^ P * ENNReal.ofReal (1 + (Ω.graph j).M) ^ a *
        (‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ ^ P /
          ‖(Ω.graph j).graphMap y' - (Ω.graph j).graphMap x'‖ₑ ^ a) := by
    rw [mul_assoc]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (ψ.enorm_toComplex_le j _) hP)
      (ENNReal.div_rpow_le_rpow_mul_div_rpow (ENNReal.ofReal_pos.2 hM).ne' ENNReal.ofReal_ne_top
        ((Ω.graph j).enorm_graphMap_sub_le y' x') ha)
  calc _ ≤ 2 ^ (P - 1) * ((‖ψ.toComplex j ((Ω.graph j).graphMap y')‖ₑ *
          ‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ) ^ P +
        (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ *
          ‖g ((Ω.graph j).graphMap x')‖ₑ) ^ P) / ‖y' - x'‖ₑ ^ a :=
        ENNReal.div_le_div_right ((ENNReal.rpow_le_rpow (enorm_mul_sub_mul_le _ _ _ _) hP).trans
          (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hP1)) _
    _ = 2 ^ (P - 1) * (‖ψ.toComplex j ((Ω.graph j).graphMap y')‖ₑ ^ P *
          (‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ ^ P / ‖y' - x'‖ₑ ^ a) +
        ‖g ((Ω.graph j).graphMap x')‖ₑ ^ P *
          (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^
            P / ‖y' - x'‖ₑ ^ a)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hP, ENNReal.mul_rpow_of_nonneg _ _ hP, mul_div_assoc,
          ENNReal.add_div, mul_comm (‖ψ.toComplex j ((Ω.graph j).graphMap y') -
            ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ P), mul_div_assoc, mul_div_assoc]
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add h2 le_rfl)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The integrand of a chart piece, with one point outside the chart ball**: if `ψ_j` vanishes
outside `B(c_j, r)`, `r ≤ r_j`, and `γ_j x' ∉ B_j`, then for the chart piece
`G = (ψ_j g) ∘ γ_j`, `|G(y') - G(x')|^P / |y' - x'|^a ≤ |G(y')|^P 1_{|x' - y'| ≥ η} |x' - y'|^(-a)`
with `η = (r_j - r) / (1 + M_j)`: `G(x') = 0`, and `G(y') ≠ 0` puts `γ_j y'` in `B(c_j, r)`, at
distance at least `r_j - r` from `γ_j x'`. -/
theorem chartPiece_integrand_le_of_notMem (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {r : ℝ}
    (hr : r ≤ Ω.radius j) (hsub : ∀ y, ψ.toFun j y ≠ 0 → y ∈ ball (Ω.center j) r) {P : ℝ}
    (hP : 0 < P) (a : ℝ) (g : V → ℂ) {x' y' : (Ω.graph j).hyperplane}
    (hx : (Ω.graph j).graphMap x' ∉ ball (Ω.center j) (Ω.radius j)) :
    ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y') -
        ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P /
        ‖y' - x'‖ₑ ^ a ≤
      ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y')‖ₑ ^ P *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-a)) (x' - y') := by
  have hφx : ψ.toComplex j ((Ω.graph j).graphMap x') = 0 :=
    ψ.toComplex_of_eq_zero (by_contra fun h => hx (ball_subset_ball hr (hsub _ h)))
  rw [hφx, zero_mul, sub_zero]
  by_cases hφy : ψ.toFun j ((Ω.graph j).graphMap y') = 0
  · rw [ψ.toComplex_of_eq_zero hφy, zero_mul, eNorm_zero, ENNReal.zero_rpow_of_pos hP,
      ENNReal.zero_div, zero_mul]
  have hfar := sub_le_norm_sub_of_mem_ball (hsub _ hφy) hx
  have hlip := (Ω.graph j).norm_graphMap_sub_le y' x'
  have hM : 0 < 1 + (Ω.graph j).M := by linarith [(Ω.graph j).M_nonneg]
  have hη : (Ω.radius j - r) / (1 + (Ω.graph j).M) ≤ ‖x' - y'‖ := by
    rw [div_le_iff₀ hM, norm_sub_rev]
    linarith
  rw [indicator_of_mem (by simpa [mem_ball_zero_iff] using hη), ENNReal.rpow_neg,
    ← div_eq_mul_inv, eNorm_sub_rev x' y']

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The integrand of a chart piece, bounded by four parts**: if `ψ_j` vanishes outside
`B(c_j, r)` with `r ≤ r_j`, then for `P ≥ 1`, `a ≥ 0`, the chart piece `G = (ψ_j g) ∘ γ_j` and all
`x', y' ∈ H_j`, `|G(y') - G(x')|^P / |y' - x'|^a` is at most
`2^(P-1) (A(x', y') + B(x', y')) + |G(x')|^P k(y' - x') + |G(y')|^P k(x' - y')` with the kernel
`k(z) = 1_{|z| ≥ η} |z|^(-a)`, `η = (r_j - r) / (1 + M_j)`, the part
`A = D_j^P (1 + M_j)^a 1_{B_j²}(γ x', γ y') |g(γ y') - g(γ x')|^P / |γ y' - γ x'|^a` and the part
`B = 1_{B_j}(γ x') |g(γ x')|^P |ψ_j(γ y') - ψ_j(γ x')|^P / |y' - x'|^a`
(`Rd.BoundedLipschitzDomain.chartPiece_integrand_le`,
`Rd.BoundedLipschitzDomain.chartPiece_integrand_le_of_notMem`). -/
theorem chartPiece_integrand_le_add (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {r : ℝ}
    (hr : r ≤ Ω.radius j) (hsub : ∀ y, ψ.toFun j y ≠ 0 → y ∈ ball (Ω.center j) r) {P : ℝ}
    (hP1 : 1 ≤ P) {a : ℝ} (ha : 0 ≤ a) (g : V → ℂ) (x' y' : (Ω.graph j).hyperplane) :
    ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y') -
        ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P /
        ‖y' - x'‖ₑ ^ a ≤
      2 ^ (P - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ P * ENNReal.ofReal (1 + (Ω.graph j).M) ^ a *
          (ball (Ω.center j) (Ω.radius j) ×ˢ ball (Ω.center j) (Ω.radius j)).indicator
            (fun z : V × V => ‖g z.2 - g z.1‖ₑ ^ P / ‖z.2 - z.1‖ₑ ^ a)
            ((Ω.graph j).graphMap x', (Ω.graph j).graphMap y') +
        (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ P) ((Ω.graph j).graphMap x') *
          (‖ψ.toComplex j ((Ω.graph j).graphMap y') -
            ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ P / ‖y' - x'‖ₑ ^ a)) +
      ‖ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-a)) (y' - x') +
      ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y')‖ₑ ^ P *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-a)) (x' - y') := by
  have hP : 0 < P := by linarith
  by_cases hx : (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j)
  · by_cases hy : (Ω.graph j).graphMap y' ∈ ball (Ω.center j) (Ω.radius j)
    · rw [indicator_of_mem (mk_mem_prod hx hy), indicator_of_mem hx]
      exact (Ω.chartPiece_integrand_le ψ j hP1 ha g x' y').trans (le_self_add.trans le_self_add)
    · have h := Ω.chartPiece_integrand_le_of_notMem ψ j hr hsub hP a g (x' := y') (y' := x') hy
      rw [eNorm_sub_rev, eNorm_sub_rev x' y'] at h
      exact h.trans (le_add_right le_add_self)
  · exact (Ω.chartPiece_integrand_le_of_notMem ψ j hr hsub hP a g hx).trans le_add_self

/-- **The inside part of a chart piece**: for every `g`,
`∫_{H_j} ∫_{H_j} 1_{B_j²}(γ x', γ y') |g(γ y') - g(γ x')|^p / |γ y' - γ x'|^(n-1+sp) dy' dx'` is at
most the Gagliardo form of `g` on `Γ` (`Rd.BoundedLipschitzDomain.lintegral_lintegral_chart_le`). -/
theorem lintegral_lintegral_inside_le (j : Fin Ω.N) (g : V → ℂ) (p : ℝ≥0∞) (s : ℝ) :
    ∫⁻ x', ∫⁻ y', (ball (Ω.center j) (Ω.radius j) ×ˢ ball (Ω.center j) (Ω.radius j)).indicator
        (fun z : V × V => ‖g z.2 - g z.1‖ₑ ^ p.toReal /
          ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))
        ((Ω.graph j).graphMap x', (Ω.graph j).graphMap y') ≤
      Ω.boundarySlobodeckijForm p s g :=
  (Ω.lintegral_lintegral_chart_le j (fun x y => (ball (Ω.center j) (Ω.radius j) ×ˢ
    ball (Ω.center j) (Ω.radius j)).indicator (fun z : V × V => ‖g z.2 - g z.1‖ₑ ^ p.toReal /
      ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) (x, y))
    fun _ _ h => mem_prod.1 (mem_of_indicator_ne_zero h)).trans
    (lintegral_mono fun x => lintegral_mono fun y => Set.indicator_le_self _ _ (x, y))

/-- The constant `(D_j (1 + M_j))^p c_1 + (2 D_j)^p c_2` of the Lipschitz part of a chart piece,
with `c_1 = Rd.ballRpowConst H_j (n - 1 + sp - p)`, `c_2 = Rd.complBallRpowConst H_j (n - 1 + sp)`
and the derivative bound `D_j = ψ.derivBound j`. -/
noncomputable def chartLipschitzConst (p : ℝ≥0∞) (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) (s : ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (ψ.derivBound j * (1 + (Ω.graph j).M)) ^ p.toReal *
      ballRpowConst (Ω.graph j).hyperplane
        (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal - p.toReal) +
    ENNReal.ofReal (2 * ψ.derivBound j) ^ p.toReal *
      complBallRpowConst (Ω.graph j).hyperplane (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)

omit [Fact (1 ≤ p)] in
/-- The constant `Rd.BoundedLipschitzDomain.chartLipschitzConst` is finite for `0 < p < ∞` and
`0 < s < 1`. -/
theorem chartLipschitzConst_ne_top (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) : Ω.chartLipschitzConst p ψ j s ≠ ∞ := by
  have hP := ENNReal.toReal_pos hp0 hp
  have hm := (Ω.graph j).finrank_hyperplane_eq_sub_one
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hP.le
    ENNReal.ofReal_ne_top) (ballRpowConst_ne_top ?_), ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top) (complBallRpowConst_ne_top ?_)⟩
  · rw [hm]
    nlinarith
  · rw [hm]
    nlinarith

omit [Fact (1 ≤ p)] in
/-- **The Lipschitz part of a chart piece**: for `0 < p < ∞` and `0 < s < 1`,
`∫_{H_j} ∫_{H_j} 1_{B_j}(γ x') |g(γ x')|^p |ψ_j(γ y') - ψ_j(γ x')|^p / |y' - x'|^(n-1+sp) dy' dx'`
is at most `K ∫_Γ |g|^p dσ` with `K = Rd.BoundedLipschitzDomain.chartLipschitzConst p ψ j s`: the
inner integral is at most `K` (`Rd.lintegral_rpow_div_norm_rpow_le`, with
`|ψ_j(γ y') - ψ_j(γ x')| ≤ min(D_j (1 + M_j) |y' - x'|, 2 D_j)`). -/
theorem lintegral_lintegral_lipschitz_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (g : V → ℂ) :
    ∫⁻ x', ∫⁻ y', (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
        ((Ω.graph j).graphMap x') *
        (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^
          p.toReal / ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) ≤
      Ω.chartLipschitzConst p ψ j s * ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure := by
  have hP := ENNReal.toReal_pos hp0 hp
  have hm := (Ω.graph j).finrank_hyperplane_eq_sub_one
  have hφγ : Continuous fun y' => ψ.toComplex j ((Ω.graph j).graphMap y') :=
    (ψ.contDiff_toComplex j).continuous.comp (Ω.graph j).continuous_graphMap
  have hin : ∀ x', ∫⁻ y', ‖ψ.toComplex j ((Ω.graph j).graphMap y') -
      ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal /
        ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ≤
      Ω.chartLipschitzConst p ψ j s := fun x' => by
    rw [← lintegral_add_right_eq_self _ x']
    simp only [add_sub_cancel_right]
    refine lintegral_rpow_div_norm_rpow_le (fun z => ?_) (fun z => ?_) hP ?_ ?_
    · refine (ψ.enorm_toComplex_sub_le j _ _).trans ?_
      rw [ENNReal.ofReal_mul (norm_nonneg _ |>.trans (norm_le_of_iteratedFDeriv_le
        (ψ.derivBound_spec j) 0)), mul_assoc]
      refine mul_le_mul' le_rfl ((Ω.graph j).enorm_graphMap_sub_le (z + x') x' |>.trans ?_)
      rw [add_sub_cancel_right]
    · refine eNorm_sub_le.trans ?_
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, two_mul]
      exact add_le_add (ψ.enorm_toComplex_le j _) (ψ.enorm_toComplex_le j _)
    · rw [hm]
      nlinarith
    · rw [hm]
      nlinarith
  have hK : Ω.chartLipschitzConst p ψ j s ≠ ∞ := Ω.chartLipschitzConst_ne_top ψ j hp0 hp hs hs1
  calc _ = ∫⁻ x', (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
        ((Ω.graph j).graphMap x') * ∫⁻ y', ‖ψ.toComplex j ((Ω.graph j).graphMap y') -
          ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal /
            ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) :=
        lintegral_congr fun x' => lintegral_const_mul _ (((hφγ.measurable.sub
          measurable_const).eNorm.pow_const _).div
            ((measurable_id.sub measurable_const).eNorm.pow_const _))
    _ ≤ ∫⁻ x', (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
        ((Ω.graph j).graphMap x') * Ω.chartLipschitzConst p ψ j s :=
        lintegral_mono fun x' => mul_le_mul' le_rfl (hin x')
    _ ≤ (∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure) * Ω.chartLipschitzConst p ψ j s := by
        rw [lintegral_mul_const' _ _ hK]
        exact mul_le_mul' ((Ω.lintegral_chart_le j _ fun _ h => mem_of_indicator_ne_zero h).trans
          (lintegral_mono (Set.indicator_le_self _ _))) le_rfl
    _ = _ := mul_comm _ _

/-- **The Gagliardo form of a chart piece, split into its parts**: if `ψ_j` vanishes outside
`B(c_j, r)` with `r ≤ r_j` and `g` is measurable, then for `1 ≤ p < ∞` and `s ≥ 0` the Gagliardo
form on `H_j` of `G = (ψ_j g) ∘ γ_j` is at most `2^(p-1) (∫∫ A + ∫∫ B) + 2 ∫∫ |G(x')|^p k(y' - x')`
for the parts of `Rd.BoundedLipschitzDomain.chartPiece_integrand_le_add`; the last part appears
twice by Tonelli's theorem. -/
theorem slobodeckijForm_chartPiece_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {r : ℝ}
    (hr : r ≤ Ω.radius j) (hsub : ∀ y, ψ.toFun j y ≠ 0 → y ∈ ball (Ω.center j) r) (hp : p ≠ ∞)
    {s : ℝ} (hs : 0 ≤ s) {g : V → ℂ} (hg : Measurable g) :
    slobodeckijForm p s (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
        g ((Ω.graph j).graphMap x')) ≤
      2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
          ENNReal.ofReal (1 + (Ω.graph j).M) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
          (∫⁻ x', ∫⁻ y', (ball (Ω.center j) (Ω.radius j) ×ˢ
              ball (Ω.center j) (Ω.radius j)).indicator
            (fun z : V × V => ‖g z.2 - g z.1‖ₑ ^ p.toReal /
              ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))
            ((Ω.graph j).graphMap x', (Ω.graph j).graphMap y')) +
        ∫⁻ x', ∫⁻ y', (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
            ((Ω.graph j).graphMap x') *
          (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^
            p.toReal / ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) +
      2 * ∫⁻ x', ∫⁻ y', ‖ψ.toComplex j ((Ω.graph j).graphMap x') *
          g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-(((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) (y' - x') := by
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  have ha : 0 ≤ ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by positivity
  have hγ := (Ω.graph j).continuous_graphMap.measurable
  have hφγ : Measurable fun y' => ψ.toComplex j ((Ω.graph j).graphMap y') :=
    (ψ.contDiff_toComplex j).continuous.measurable.comp hγ
  have hG : Measurable fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
      g ((Ω.graph j).graphMap x') := hφγ.mul (hg.comp hγ)
  have hk : Measurable ((ball (0 : (Ω.graph j).hyperplane)
      ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
        fun z => ‖z‖ₑ ^ (-(((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) :=
    (measurable_eNorm.pow_const _).indicator measurableSet_ball.compl
  have hT : Measurable (Function.uncurry fun x' y' : (Ω.graph j).hyperplane =>
      ‖ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-(((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) (y' - x')) :=
    ((hG.comp measurable_fst).eNorm.pow_const p.toReal).mul
      (hk.comp (measurable_snd.sub measurable_fst))
  have hT' : Measurable (Function.uncurry fun x' y' : (Ω.graph j).hyperplane =>
      ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y')‖ₑ ^ p.toReal *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-(((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) (x' - y')) :=
    ((hG.comp measurable_snd).eNorm.pow_const p.toReal).mul
      (hk.comp (measurable_fst.sub measurable_snd))
  have hB : Measurable (Function.uncurry fun x' y' : (Ω.graph j).hyperplane =>
      (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
        ((Ω.graph j).graphMap x') *
        (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^
          p.toReal / ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) :=
    ((((hg.eNorm.pow_const p.toReal).indicator measurableSet_ball).comp hγ).comp
      measurable_fst).mul ((((hφγ.comp measurable_snd).sub
        (hφγ.comp measurable_fst)).eNorm.pow_const p.toReal).div
          ((measurable_snd.sub measurable_fst).eNorm.pow_const _))
  rw [slobodeckijForm, (Ω.graph j).finrank_hyperplane_eq_sub_one]
  refine (lintegral_mono fun x' => lintegral_mono fun y' =>
    Ω.chartPiece_integrand_le_add ψ j hr hsub hP1 ha g x' y').trans (le_of_eq ?_)
  rw [lintegral_lintegral_add_right _ hT', lintegral_lintegral_add_right _ hT,
    lintegral_lintegral_swap hT'.aemeasurable,
    lintegral_lintegral_const_mul' (ENNReal.two_rpow_ne_top _), lintegral_lintegral_add_right _ hB,
    lintegral_lintegral_const_mul' (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg ha ENNReal.ofReal_ne_top)), add_assoc, ← two_mul]

/-- **The Gagliardo form of a chart piece by the form on `Γ`**: for `1 ≤ p < ∞`, `0 < s < 1`, a
resolution of unity `ψ` and a chart `j` there is `K < ∞` such that for every measurable `g` the
Gagliardo form on `H_j` of `G = (ψ_j g) ∘ γ_j` is at most
`K (∫_Γ |g|^p dσ + ∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ dσ)`. The parts of
`Rd.BoundedLipschitzDomain.slobodeckijForm_chartPiece_le` are bounded by
`Rd.BoundedLipschitzDomain.lintegral_lintegral_inside_le`,
`Rd.BoundedLipschitzDomain.lintegral_lintegral_lipschitz_le`,
`Rd.lintegral_lintegral_mul_indicator_le` and
`Rd.BoundedLipschitzDomain.lintegral_chartPiece_le`. -/
theorem exists_slobodeckijForm_chartPiece_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : V → ℂ, Measurable g →
      slobodeckijForm p s (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
          g ((Ω.graph j).graphMap x')) ≤
        K * (∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure + Ω.boundarySlobodeckijForm p s g) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  have ha : 0 ≤ ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by positivity
  have hM : 0 < 1 + (Ω.graph j).M := by linarith [(Ω.graph j).M_nonneg]
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport _) (ψ.tsupport_subset j)
  have hη : 0 < (Ω.radius j - r) / (1 + (Ω.graph j).M) := div_pos (sub_pos.2 hr) hM
  have hma : (finrank ℝ (Ω.graph j).hyperplane : ℝ) <
      ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by
    rw [(Ω.graph j).finrank_hyperplane_eq_sub_one]
    exact lt_add_of_pos_right _ (mul_pos hs hP)
  have h2 : (2 : ℝ≥0∞) ^ (p.toReal - 1) ≠ ∞ :=
    ENNReal.two_rpow_ne_top _
  have hD : ENNReal.ofReal (ψ.derivBound j) ^ p.toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal (1 + (Ω.graph j).M) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg ha ENNReal.ofReal_ne_top
  have hI : complBallRpowConst (Ω.graph j).hyperplane
      (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
      ENNReal.ofReal ((Ω.radius j - r) / (1 + (Ω.graph j).M)) ^
        ((finrank ℝ (Ω.graph j).hyperplane : ℝ) -
          (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) ≠ ∞ :=
    ENNReal.mul_ne_top (complBallRpowConst_ne_top hma)
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.2 hη).ne' ENNReal.ofReal_ne_top)
  refine ⟨2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
      ENNReal.ofReal (1 + (Ω.graph j).M) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) +
    2 ^ (p.toReal - 1) * Ω.chartLipschitzConst p ψ j s +
    2 * (complBallRpowConst (Ω.graph j).hyperplane (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
      ENNReal.ofReal ((Ω.radius j - r) / (1 + (Ω.graph j).M)) ^
        ((finrank ℝ (Ω.graph j).hyperplane : ℝ) - (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) *
      ENNReal.ofReal (ψ.derivBound j) ^ p.toReal,
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top h2 (ENNReal.mul_ne_top hD hc),
      ENNReal.mul_ne_top h2 (Ω.chartLipschitzConst_ne_top ψ j hp0 hp hs hs1)⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hI) hD⟩, fun g hg => ?_⟩
  have hT := (lintegral_lintegral_mul_indicator_le (fun x' => ‖ψ.toComplex j
    ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal) hη hma).trans
    (mul_le_mul' le_rfl (Ω.lintegral_chartPiece_le ψ j hP g))
  refine (Ω.slobodeckijForm_chartPiece_le ψ j hr.le (fun y hy => hsub (subset_tsupport _ hy)) hp
    hs.le hg).trans ?_
  calc _ ≤ 2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
          ENNReal.ofReal (1 + (Ω.graph j).M) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
          Ω.boundarySlobodeckijForm p s g +
        Ω.chartLipschitzConst p ψ j s * ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure) +
      2 * (complBallRpowConst (Ω.graph j).hyperplane
          (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
        ENNReal.ofReal ((Ω.radius j - r) / (1 + (Ω.graph j).M)) ^
          ((finrank ℝ (Ω.graph j).hyperplane : ℝ) -
            (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) *
        (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
          ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure)) :=
        add_le_add (mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' le_rfl (Ω.lintegral_lintegral_inside_le j g p s))
          (Ω.lintegral_lintegral_lipschitz_le ψ j hp0 hp hs hs1 g))) (mul_le_mul' le_rfl hT)
    _ ≤ _ := (le_of_eq (by ring)).trans (ENNReal.mul_add_mul_add_mul_le _ _ _ _ _)

/-- **The chart-wise Besov norm by the Gagliardo form** (the lower half of Gagliardo's description
of `B^s_{p,p}(Γ)`): for `1 ≤ p < ∞`, `0 < s < 1` and a resolution of unity `ψ` there is `C < ∞`
with `‖g‖_{B^s_{p,p}(Γ)}^p ≤ C (‖g‖_{L_p(Γ)}^p + ∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ dσ)`
for every `g` measurable on `Γ`. If `g ∈ L_p(Γ)`, every chart piece `G_j = (ψ_j g) ∘ γ_j` lies in
`L_p(H_j)` (`Rd.BoundedLipschitzDomain.lintegral_chartPiece_le`), its first-difference norm is
bounded by its Gagliardo form on `H_j` (`Rd.lqNorm_modulus_rpow_le_slobodeckijForm`), and that by
the form on `Γ` (`Rd.BoundedLipschitzDomain.exists_slobodeckijForm_chartPiece_le`). -/
theorem exists_boundaryBesovNorm_rpow_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, AEStronglyMeasurable g Ω.surfaceMeasure →
      Ω.boundaryBesovNorm p ψ s p g ^ p.toReal ≤
        C * (eLpNorm g p Ω.surfaceMeasure ^ p.toReal + Ω.boundarySlobodeckijForm p s g) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  choose K hK hle using fun j => Ω.exists_slobodeckijForm_chartPiece_le ψ j hp hs hs1
  refine ⟨((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) *
      ∑ j, 2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal +
        slobodeckijConstUpper (Ω.graph j).hyperplane p s * K j) + 1,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.natCast_ne_top _)) (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top
        (ENNReal.two_rpow_ne_top _)
        (ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top,
          ENNReal.mul_ne_top (slobodeckijConstUpper_ne_top hp0 hp hs) (hK j)⟩)),
      ENNReal.one_ne_top⟩, fun g hg => ?_⟩
  have hgm : Measurable (hg.mk g) := hg.stronglyMeasurable_mk.measurable
  rw [Ω.boundaryBesovNorm_congr ψ (Ω.ae_surfaceMeasure_iff_aeBoundary.1 hg.ae_eq_mk),
    eLpNorm_congr_ae hg.ae_eq_mk, Ω.boundarySlobodeckijForm_congr_ae hg.ae_eq_mk,
    eLpNorm_rpow_eq hgm.aestronglyMeasurable hp0 hp]
  by_cases hX : ∫⁻ y, ‖hg.mk g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure = ∞
  · rw [hX, top_add, ENNReal.mul_top (by positivity)]
    exact le_top
  have hmem : ∀ j, MemLp (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
      hg.mk g ((Ω.graph j).graphMap x')) p volume := fun j =>
    memLp_iff.2 ((eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp0 hp
      ((((ψ.contDiff_toComplex j).continuous.comp (Ω.graph j).continuous_graphMap).measurable.mul
        (hgm.comp (Ω.graph j).continuous_graphMap.measurable)).aestronglyMeasurable)).2
      ((Ω.lintegral_chartPiece_le ψ j hP _).trans_lt (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg hP.le ENNReal.ofReal_ne_top) (lt_top_iff_ne_top.2 hX))))
  have hj : ∀ j (G : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane)),
      (G : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume] (fun x' => ψ.toComplex j
        ((Ω.graph j).graphMap x') * hg.mk g ((Ω.graph j).graphMap x')) →
      (‖G‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k)) ^ p.toReal ≤
        2 ^ (p.toReal - 1) * ((ENNReal.ofReal (ψ.derivBound j) ^ p.toReal +
          slobodeckijConstUpper (Ω.graph j).hyperplane p s * K j) *
          (∫⁻ y, ‖hg.mk g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure +
            Ω.boundarySlobodeckijForm p s (hg.mk g))) := by
    intro j G hG
    have hGP : ‖G‖ₑ ^ p.toReal ≤ ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
        ∫⁻ y, ‖hg.mk g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure := by
      have hGP' : ∫⁻ x', ‖G x'‖ₑ ^ p.toReal = ∫⁻ x', ‖ψ.toComplex j ((Ω.graph j).graphMap x') *
          hg.mk g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal :=
        lintegral_congr_ae (hG.mono fun x' hx' => by dsimp only; rw [hx'])
      rw [Lp.eNorm_def, eLpNorm_rpow_eq (Lp.aestronglyMeasurable G) hp0 hp, hGP']
      exact Ω.lintegral_chartPiece_le ψ j hP _
    have hL := (lqNorm_modulus_rpow_le_slobodeckijForm hp hs G).trans (mul_le_mul' le_rfl
      ((slobodeckijForm_congr_ae hG p s).trans_le (hle j _ hgm)))
    calc _ ≤ 2 ^ (p.toReal - 1) * (‖G‖ₑ ^ p.toReal +
          lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k) ^ p.toReal) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hP1
      _ ≤ _ := mul_le_mul' le_rfl ((add_le_add hGP hL).trans (by
          rw [add_mul, mul_assoc]
          exact add_le_add (mul_le_mul' le_rfl le_self_add) le_rfl))
  rw [Ω.boundaryBesovNorm_eq_sum ψ (fun j => (hmem j).toLp _) fun j => (hmem j).coeFn_toLp]
  calc _ ≤ ((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ j,
        (‖(hmem j).toLp _‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1
          ((hmem j).toLp _) k)) ^ p.toReal :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ) (f := fun j =>
          ‖(hmem j).toLp _‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1
            ((hmem j).toLp _) k)) hP1
    _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => hj j _ (hmem j).coeFn_toLp)
    _ = (((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) *
        ∑ j, 2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal +
          slobodeckijConstUpper (Ω.graph j).hyperplane p s * K j)) *
        (∫⁻ y, ‖hg.mk g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure +
          Ω.boundarySlobodeckijForm p s (hg.mk g)) := by
        simp only [← mul_assoc, ← Finset.sum_mul]
    _ ≤ _ := mul_le_mul' le_self_add le_rfl

/-! ### Gagliardo's description of `B^s_{p,p}(Γ)` and of the trace space -/

/-- **Gagliardo's description of `B^s_{p,p}(Γ)`** (Gagliardo 1957): for `1 ≤ p < ∞`, `0 < s < 1`,
a resolution of unity `ψ` and `g ∈ L_p(Γ)`, `g ∈ B^s_{p,p}(Γ)` iff
`∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ(y) dσ(x) < ∞`, that is, the chart-wise space
`B^s_{p,p}(Γ)` is the Sobolev–Slobodeckij space `W^{s,p}(Γ)` defined by the surface measure
(`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`,
`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le`). -/
theorem memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top (ψ : Ω.BoundaryPartition)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {g : V → ℂ}
    (hg : MemLp g p Ω.surfaceMeasure) :
    Ω.MemBoundaryBesov p ψ s p g ↔ Ω.boundarySlobodeckijForm p s g < ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_boundarySlobodeckijForm_le ψ hp hs
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundaryBesovNorm_rpow_le ψ hp hs hs1
  rw [Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ]
  refine ⟨fun h => (h₁ g).trans_lt (ENNReal.mul_lt_top hC₁.lt_top
    (ENNReal.rpow_lt_top_of_nonneg hP.le h.ne)), fun h => ?_⟩
  rw [← ENNReal.rpow_lt_top_iff_of_pos hP]
  exact (h₂ g hg.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top hC₂.lt_top
    (ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg hP.le hg.eLpNorm_lt_top.ne, h⟩))

/-- **The norm of `H^{1/2}(Γ)` by the Sobolev–Slobodeckij norm**: there is `C < ∞` with
`‖t‖² ≤ C (‖τ t‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |τ t(y) - τ t(x)|² / |y - x|^n dσ(y) dσ(x))` and the reverse
bound `‖τ t‖²_{L_2(Γ)} + ∫_Γ ∫_Γ … ≤ C ‖t‖²` for every `t ∈ H^{1/2}(Γ)` and its trace
`τ t ∈ L_2(Γ)`, `n = dim V`: the norm of the trace space is equivalent to Gagliardo's norm of
`W^{1/2,2}(Γ)`. It combines the equivalence with the chart-wise norm of `B^{1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`) with
`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`,
`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le` and the boundedness of `τ`. -/
theorem exists_traceL2_norm_equiv_slobodeckij :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : Ω.TraceSpace,
      ‖t‖ₑ ^ 2 ≤ C * (‖Ω.traceL2 t‖ₑ ^ 2 + Ω.boundarySlobodeckijForm 2 (1 / 2) (Ω.traceL2 t)) ∧
        ‖Ω.traceL2 t‖ₑ ^ 2 + Ω.boundarySlobodeckijForm 2 (1 / 2) (Ω.traceL2 t) ≤
          C * ‖t‖ₑ ^ 2 := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_traceL2_norm_equiv Ω.boundaryPartition
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundarySlobodeckijForm_le (p := 2) Ω.boundaryPartition
    two_ne_top (s := 1 / 2) (by norm_num)
  obtain ⟨C₃, hC₃, h₃⟩ := Ω.exists_boundaryBesovNorm_rpow_le (p := 2) Ω.boundaryPartition
    two_ne_top (s := 1 / 2) (by norm_num) (by norm_num)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h₂ h₃
  refine ⟨C₁ ^ 2 * C₃ + (‖Ω.traceL2‖ₑ ^ 2 + C₂ * C₁ ^ 2), ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.pow_ne_top hC₁) hC₃, ENNReal.add_ne_top.2
      ⟨ENNReal.pow_ne_top eNorm_ne_top, ENNReal.mul_ne_top hC₂ (ENNReal.pow_ne_top hC₁)⟩⟩,
    fun t => ⟨?_, ?_⟩⟩
  · calc ‖t‖ₑ ^ 2 ≤ (C₁ * Ω.boundaryBesovNorm 2 Ω.boundaryPartition (1 / 2) 2 (Ω.traceL2 t)) ^ 2 :=
          pow_le_pow_left₀ zero_le (h₁ t).1 2
      _ ≤ C₁ ^ 2 * (C₃ * (‖Ω.traceL2 t‖ₑ ^ 2 +
            Ω.boundarySlobodeckijForm 2 (1 / 2) (Ω.traceL2 t))) := by
          rw [mul_pow, Lp.eNorm_def]
          exact mul_le_mul' le_rfl (h₃ _ (Lp.aestronglyMeasurable _))
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · calc _ ≤ (‖Ω.traceL2‖ₑ * ‖t‖ₑ) ^ 2 + C₂ * (C₁ * ‖t‖ₑ) ^ 2 :=
          add_le_add (pow_le_pow_left₀ zero_le (Ω.traceL2.le_opENorm t) 2)
            ((h₂ _).trans (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le (h₁ t).2 2)))
      _ = (‖Ω.traceL2‖ₑ ^ 2 + C₂ * C₁ ^ 2) * ‖t‖ₑ ^ 2 := by ring
      _ ≤ _ := mul_le_mul' le_add_self le_rfl

/-- **The range of `H^{1/2}(Γ) → L_2(Γ)` by the Gagliardo form**: `g ∈ L_2(Γ)` is the trace `τ t`
of some `t ∈ H^{1/2}(Γ)` iff `∫_Γ ∫_Γ |g(y) - g(x)|² / |y - x|^n dσ(y) dσ(x) < ∞`
(`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`,
`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top`). -/
theorem mem_range_traceL2_iff_slobodeckij (g : Ω.BoundaryL2) :
    g ∈ LinearMap.range (Ω.traceL2 : Ω.TraceSpace →ₗ[ℂ] Ω.BoundaryL2) ↔
      Ω.boundarySlobodeckijForm 2 (1 / 2) g < ∞ := by
  rw [Ω.mem_range_traceL2_iff Ω.boundaryPartition]
  exact Ω.memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top _ two_ne_top (by norm_num)
    (by norm_num) (Lp.memLp g)

end BoundedLipschitzDomain

end Rd
