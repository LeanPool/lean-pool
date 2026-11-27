/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy
public import LeanPool.FunctionSpaces.Analysis.Lp.LintegralForm
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Average

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Mixed norms

For a countable family of functions `g_i : α → [0, ∞]` on a measure space, the mixed norm
`‖g‖_{L_p(ℓ_q)} = ‖ x ↦ ‖(g_i(x))_i‖_{ℓ_q} ‖_{L_p}` takes the `ℓ_q` norm at each point before
the `L_p` norm, and `‖g‖_{ℓ_q(L_p)} = ‖(‖g_i‖_p)_i‖_{ℓ_q}` takes them in the other order.
Triebel–Lizorkin spaces use the first, Besov spaces the second. This file compares the two:

* `L_p(ℓ_p) = ℓ_p(L_p)` by Tonelli's theorem (`MeasureTheory.eLpNorm_lqNorm_eq_lqNorm_eLpNorm`);
* `ℓ_q(L_p) ≤ L_p(ℓ_q)` for `0 < p ≤ q` (`MeasureTheory.lqNorm_eLpNorm_le_eLpNorm_lqNorm`) and
  `L_p(ℓ_q) ≤ ℓ_q(L_p)` for `0 < q ≤ p < ∞` (`MeasureTheory.eLpNorm_lqNorm_le_lqNorm_eLpNorm`);
* the sandwich `ℓ_{max(p,q)}(L_p) ≤ L_p(ℓ_q) ≤ ℓ_{min(p,q)}(L_p)`
  (`MeasureTheory.lqNorm_max_le_eLpNorm_lqNorm`, `MeasureTheory.eLpNorm_lqNorm_le_lqNorm_min`),
  and the same for the weighted families `w_j ‖u_j‖` of any functions `u_j` with values in a
  normed group (`MeasureTheory.lqNorm_max_weighted_le`,
  `MeasureTheory.eLpNorm_lqNorm_weighted_le_min`), such as the families `2^(js) ‖u_j‖` of
  Littlewood–Paley blocks (`MeasureTheory.lqNorm_max_dyadicWeight_le`,
  `MeasureTheory.eLpNorm_lqNorm_dyadicWeight_le_min`).

The tools are the `L_p` norms of `[0, ∞]`-valued functions of `ApproximationSpaces.Sequences.Lq`
(powers, homogeneity, monotone convergence and Minkowski's inequality for series) and
Minkowski's integral inequality for `ℓ_u`-valued functions,
`‖(∫ g_i)_i‖_{ℓ_u} ≤ ∫ ‖(g_i)_i‖_{ℓ_u}` (`MeasureTheory.lqNorm_lintegral_le`), proved by
Hölder's inequality on finite sets, also for means (`MeasureTheory.lqNorm_laverage_le`) and, on
a probability space, with the `L_p` norm on the right (`MeasureTheory.lqNorm_lintegral_le_eLpNorm`).
Finally, a pointwise bound `u ≤ v + w_J` with `‖w_J‖_p → 0` gives `u ≤ v` almost everywhere
(`MeasureTheory.ae_le_of_le_add_of_tendsto_eLpNorm`), and a bound `|G_J| ≤ v` almost everywhere
passes to the limit of `G_J` in `L_p` (`MeasureTheory.ae_enorm_le_of_tendsto_Lp`). Setting
terms of a family to zero decreases its mixed norm (`MeasureTheory.eLpNorm_lqNorm_ite_le`,
`MeasureTheory.eLpNorm_lqNorm_ite_mono`), and one member is bounded by the mixed norm,
`2^(js) ‖h_j‖_p ≤ ‖ x ↦ ‖(2^(is) |h_i(x)|)_i‖_{ℓ_q} ‖_p`
(`MeasureTheory.dyadicWeight_mul_enorm_le_eLpNorm_lqNorm`,
`MeasureTheory.enorm_le_dyadicWeight_neg_mul_eLpNorm_lqNorm`). For
a family with a finite mixed norm, the tails `x ↦ ‖(g_j(x))_{j ≥ N}‖_{ℓ_q}` tend to zero in `L_p`
by dominated convergence (`MeasureTheory.tendsto_eLpNorm_lqNorm_ite_le`), since the tails of a
single sequence in `ℓ_q` do (`ENNReal.tendsto_lqNorm_ite_le`); a sequence whose differences are
bounded by these tails is a Cauchy sequence (`MeasureTheory.cauchySeq_of_edist_le_lqNorm_ite`).

Three steps of the embeddings of Sobolev spaces into Triebel–Lizorkin spaces hold for all
families: the first term splits off,
`‖x ↦ ‖(2^(js) b_j(x))_j‖_{ℓ_q}‖_p ≤ ‖b_0‖_p + ‖x ↦ ‖(2^((n+1)s) b_{n+1}(x))_n‖_{ℓ_q}‖_p`
(`MeasureTheory.eLpNorm_lqNorm_dyadicWeight_le_zero_add_succ`), a pointwise bound by a finite
sum passes to `L_p` by Minkowski's inequality
(`MeasureTheory.eLpNorm_le_const_mul_sum_of_ae_le`), and `2^(nm) b_n ≤ ∑_i c_{i,n}` gives
`‖(2^((n+1)m) b_n)_n‖_{ℓ_q} ≤ 2^m ∑_i ‖c_i‖_{ℓ_q}` (`ENNReal.lqNorm_dyadicWeight_succ_le_sum`).

The mixed norm `‖x ↦ ‖(u_j(x))_j‖_{ℓ_q}‖_p` of a family `u_j : α → [0, ∞]` satisfies the
triangle inequality for `w_j ≤ u_j + v_j`, is homogeneous and decreases in `q`
(`MeasureTheory.eLpNorm_lqNorm_le_add`, `MeasureTheory.eLpNorm_lqNorm_eq_const_mul`,
`MeasureTheory.eLpNorm_lqNorm_mono_exponent`). For the weighted family `(2^(js) u_j)_j`, which
gives the Triebel–Lizorkin quasi-norm for `u_j = |ψ_j ⋆ f|` on `ℝ^d` and on the torus, the weights
are `1` for `s = 0` and the norm increases in `s`
(`MeasureTheory.eLpNorm_lqNorm_dyadicWeight_zero_left`,
`MeasureTheory.eLpNorm_lqNorm_dyadicWeight_mono_smoothness`).

Two facts on conjugate exponents serve the duality arguments: a power cancels in Hölder's
inequality, `X ≤ K A^{1/u} X^{1/u'}` with `X < ∞` gives `X ≤ K^u A`
(`ENNReal.le_rpow_mul_of_le_mul_rpow`), and the conjugate exponent of `p > 2` is below `2`
(`ENNReal.HolderConjugate.lt_two_of_two_lt`).
-/

@[expose] public section

open Filter Topology
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight)

namespace ENNReal

/-! ### Tails of sequences -/

/-- **The tails of a sequence in `ℓ_q` tend to zero**: for `0 < q < ∞` and `‖a‖_{ℓ_q} < ∞`,
`‖(0, …, 0, a_N, a_{N+1}, …)‖_{ℓ_q} → 0` as `N → ∞`, since the tails `∑_{k ≥ N} a_k^q` of a
convergent series tend to zero (Mathlib's `ENNReal.tendsto_sum_nat_add`). -/
theorem tendsto_lqNorm_ite_le {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) {a : ℕ → ℝ≥0∞}
    (ha : lqNorm q a ≠ ∞) :
    Tendsto (fun N => lqNorm q (fun j => if N ≤ j then a j else 0)) atTop (𝓝 0) := by
  have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hsum : ∑' j, a j ^ q.toReal ≠ ∞ := by
    rw [← lqNorm_rpow hq0 hq]
    exact ENNReal.rpow_ne_top_of_nonneg hpos.le ha
  have h := ((ENNReal.continuous_rpow_const (y := 1 / q.toReal)).tendsto 0).comp
    (ENNReal.tendsto_sum_nat_add _ hsum)
  rw [ENNReal.zero_rpow_of_pos (one_div_pos.2 hpos)] at h
  refine h.congr fun N => ?_
  rw [Function.comp_apply, lqNorm_ite_le_eq hq0 hq, lqNorm_eq_tsum hq0 hq]
  simp_rw [add_comm N]

/-! ### Powers in `[0, ∞]` -/

/-- Every term of a finite family is bounded by its `ℓ_r` norm:
`a_i ≤ (∑_{j ∈ S} a_j^r)^(1/r)` for `i ∈ S` and `r > 0`. -/
theorem le_rpow_sum_rpow {ι : Type*} {S : Finset ι} {a : ι → ℝ≥0∞} {i : ι}
    (hi : i ∈ S) {r : ℝ} (hr : 0 < r) : a i ≤ (∑ j ∈ S, a j ^ r) ^ (1 / r) := by
  calc a i = (a i ^ r) ^ (1 / r) := by rw [one_div, ENNReal.rpow_rpow_inv hr.ne']
    _ ≤ _ := ENNReal.rpow_le_rpow
          (Finset.single_le_sum (f := fun j => a j ^ r) (fun j _ => zero_le) hi) (by positivity)

/-- **Conjugate exponents of exponents above `2`**: if `1/p + 1/q = 1` and `p > 2`, then
`q < 2`, since `1/q = 1 - 1/p > 1/2`. -/
theorem HolderConjugate.lt_two_of_two_lt {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : 2 < p) :
    q < 2 := by
  have h1 : p⁻¹ < 2⁻¹ := ENNReal.inv_lt_inv.2 hp
  refine ENNReal.inv_lt_inv.1 (lt_of_not_ge fun hle => ?_)
  have h2 : p⁻¹ + q⁻¹ < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_of_lt_of_le
    (ENNReal.inv_ne_top.2 (HolderConjugate.ne_zero q p)) h1 hle
  rw [HolderConjugate.inv_add_inv_eq_one p q, ENNReal.inv_two_add_inv_two] at h2
  exact lt_irrefl _ h2

/-- **Cancellation in Hölder's inequality**: for conjugate exponents `u, u'` and `X < ∞`, the
bound `X ≤ K A^{1/u} X^{1/u'}` implies `X ≤ K^u A`, since `X = X^{1/u} X^{1/u'}`. -/
theorem le_rpow_mul_of_le_mul_rpow {X K A : ℝ≥0∞} {u u' : ℝ} (h : u.HolderConjugate u')
    (hX : X ≠ ∞) (hle : X ≤ K * A ^ (1 / u) * X ^ (1 / u')) : X ≤ K ^ u * A := by
  rcases eq_or_ne X 0 with rfl | hX0
  · exact zero_le
  have hu : 0 < u := h.pos
  have hsplit : X = X ^ (1 / u) * X ^ (1 / u') := by
    rw [← ENNReal.rpow_add _ _ hX0 hX, one_div, one_div, h.inv_add_inv_eq_one, ENNReal.rpow_one]
  have hc0 : X ^ (1 / u') ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hX0) hX).ne'
  have hct : X ^ (1 / u') ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 h.symm.pos.le) hX
  have h1 : X ^ (1 / u) ≤ K * A ^ (1 / u) := by
    refine (ENNReal.mul_le_mul_iff_left hc0 hct).1 ?_
    rw [← hsplit]
    exact hle
  calc X = (X ^ (1 / u)) ^ u := by rw [one_div, ENNReal.rpow_inv_rpow hu.ne']
    _ ≤ (K * A ^ (1 / u)) ^ u := ENNReal.rpow_le_rpow h1 hu.le
    _ = K ^ u * A := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hu.le, one_div, ENNReal.rpow_inv_rpow hu.ne']

/-! ### Shifted dyadic weights -/

/-- **Shifted dyadic weights against a finite sum**: for `m ∈ ℕ`, `1 ≤ q ≤ ∞`, a sequence
`b : ℕ → [0, ∞]` and finitely many sequences `c_i : ℕ → [0, ∞]` with
`2^(nm) b_n ≤ ∑_i c_{i,n}` for every `n`,
`‖(2^((n+1)m) b_n)_n‖_{ℓ_q} ≤ 2^m ∑_i ‖c_i‖_{ℓ_q}`, since `2^((n+1)m) = 2^m 2^(nm)`, by the
homogeneity of the `ℓ_q` norm and Minkowski's inequality (`ENNReal.lqNorm_sum_le`). -/
theorem lqNorm_dyadicWeight_succ_le_sum {q : ℝ≥0∞} (hq : 1 ≤ q) {m : ℕ} {ι : Type*}
    (s : Finset ι) {b : ℕ → ℝ≥0∞} {c : ι → ℕ → ℝ≥0∞}
    (h : ∀ n, 2 ^ (n * m) * b n ≤ ∑ i ∈ s, c i n) :
    lqNorm q (fun n => dyadicWeight (m : ℝ) (n + 1) * b n) ≤
      2 ^ m * ∑ i ∈ s, lqNorm q (c i) := by
  calc lqNorm q (fun n => dyadicWeight (m : ℝ) (n + 1) * b n)
      ≤ lqNorm q (fun n => 2 ^ m * ∑ i ∈ s, c i n) := by
        refine lqNorm_mono fun n => ?_
        rw [dyadicWeight_eq_pow, ENNReal.rpow_natCast, ← pow_mul,
          show m * (n + 1) = m + n * m by ring, pow_add, mul_assoc]
        gcongr
        exact h n
    _ = 2 ^ m * lqNorm q (fun n => ∑ i ∈ s, c i n) := lqNorm_const_mul _ _
    _ ≤ 2 ^ m * ∑ i ∈ s, lqNorm q (c i) := by
        gcongr
        exact lqNorm_sum_le hq _ _

end ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}

/-! ### `L_p` norms of functions with values in `[0, ∞]` -/

/-- **One weighted term of a family is bounded by the mixed norm**: for `q ≠ 0`, a family
`h_i ∈ L_p(μ)` and every `j`, `2^(js) ‖h_j‖_p ≤ ‖ x ↦ ‖(2^(is) |h_i(x)|)_i‖_{ℓ_q} ‖_p`, since
pointwise `2^(js) |h_j(x)|` is at most the `ℓ_q` norm (`ENNReal.le_lqNorm`). -/
theorem dyadicWeight_mul_enorm_le_eLpNorm_lqNorm {E : Type*} [NormedAddCommGroup E]
    (hq : q ≠ 0) (s : ℝ) (h : ℕ → Lp E p μ) (j : ℕ) :
    dyadicWeight s j * ‖h j‖ₑ ≤
      eLpNorm (fun x => lqNorm q (fun i => dyadicWeight s i * ‖h i x‖ₑ)) p μ := by
  rw [Lp.eNorm_def, ← eLpNorm_eNorm _ (Lp.aestronglyMeasurable (h j)),
    ← eLpNorm_const_mul_ennreal (Lp.aestronglyMeasurable (h j)).eNorm.aestronglyMeasurable]
  refine eLpNorm_mono_eNorm
    (((Lp.aestronglyMeasurable (h j)).eNorm.const_mul _).aestronglyMeasurable) fun x => ?_
  simp only [eNorm_eq_self]
  exact ENNReal.le_lqNorm hq (fun i => dyadicWeight s i * ‖h i x‖ₑ) j

/-- **One term of a family is bounded by the mixed norm**: for `q ≠ 0`, a family `h_i ∈ L_p(μ)`
and every `j`, `‖h_j‖_p ≤ 2^(-js) ‖ x ↦ ‖(2^(is) |h_i(x)|)_i‖_{ℓ_q} ‖_p`
(`MeasureTheory.dyadicWeight_mul_enorm_le_eLpNorm_lqNorm`). -/
theorem enorm_le_dyadicWeight_neg_mul_eLpNorm_lqNorm {E : Type*} [NormedAddCommGroup E]
    (hq : q ≠ 0) (s : ℝ) (h : ℕ → Lp E p μ) (j : ℕ) :
    ‖h j‖ₑ ≤ dyadicWeight (-s) j *
      eLpNorm (fun x => lqNorm q (fun i => dyadicWeight s i * ‖h i x‖ₑ)) p μ :=
  calc ‖h j‖ₑ = dyadicWeight (-s) j * (dyadicWeight s j * ‖h j‖ₑ) := by
        rw [← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
    _ ≤ _ := by gcongr; exact dyadicWeight_mul_enorm_le_eLpNorm_lqNorm hq s h j

/-! ### Minkowski's integral inequality for `ℓ_u`-valued functions -/

/-- The **duality step** of Minkowski's integral inequality on a finite set `S`, for `r > 1`
with conjugate exponent `r'`: `∑_{i ∈ S} (∫ g_i)^r ≤ (∫ (∑_{i ∈ S} g_i^r)^(1/r)) ·
(∑_{i ∈ S} (∫ g_i)^r)^(1/r')`. Write `(∫ g_i)^r = ∫ g_i · (∫ g_i)^(r-1)`, exchange the finite
sum with the integral and apply Hölder's inequality at every point. -/
theorem sum_rpow_lintegral_le_mul {ι : Type*} {g : ι → α → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) μ) {r : ℝ} (hr : 1 < r) (S : Finset ι) :
    ∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r ≤ (∫⁻ x, (∑ i ∈ S, g i x ^ r) ^ (1 / r) ∂μ) *
      (∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r) ^ (1 / r.conjExponent) := by
  have hpq := Real.HolderConjugate.conjExponent hr
  have hconj : ∑ i ∈ S, ((∫⁻ x, g i x ∂μ) ^ (r - 1)) ^ r.conjExponent =
      ∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r :=
    Finset.sum_congr rfl fun i _ => by rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
  calc ∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r
      = ∑ i ∈ S, (∫⁻ x, g i x ∂μ) * (∫⁻ x, g i x ∂μ) ^ (r - 1) :=
        Finset.sum_congr rfl fun i _ => ENNReal.rpow_eq_mul_rpow_sub_one _ hr.le
    _ = ∫⁻ x, ∑ i ∈ S, g i x * (∫⁻ y, g i y ∂μ) ^ (r - 1) ∂μ := by
        rw [lintegral_finsetSum' S fun i _ => (hg i).mul_const _]
        exact Finset.sum_congr rfl fun i _ => (lintegral_mul_const'' _ (hg i)).symm
    _ ≤ ∫⁻ x, (∑ i ∈ S, g i x ^ r) ^ (1 / r) *
          (∑ i ∈ S, ((∫⁻ y, g i y ∂μ) ^ (r - 1)) ^ r.conjExponent) ^ (1 / r.conjExponent) ∂μ :=
        lintegral_mono fun x => ENNReal.inner_le_Lp_mul_Lq S (fun i => g i x) _ hpq
    _ = (∫⁻ x, (∑ i ∈ S, g i x ^ r) ^ (1 / r) ∂μ) *
          (∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r) ^ (1 / r.conjExponent) := by
        rw [hconj, lintegral_mul_const'' _ (by fun_prop)]

/-- **Minkowski's integral inequality on a finite set**: for `r > 1` and measurable
`g_i : α → [0, ∞]`, `(∑_{i ∈ S} (∫ g_i)^r)^(1/r) ≤ ∫ (∑_{i ∈ S} g_i^r)^(1/r)`. If the left side is
finite and nonzero, cancel the factor `(∑_{i ∈ S} (∫ g_i)^r)^(1/r')` in
`MeasureTheory.sum_rpow_lintegral_le_mul`; if it is infinite, some `∫ g_i` is infinite and so is
the right side. -/
theorem rpow_sum_rpow_lintegral_le {ι : Type*} {g : ι → α → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) μ) {r : ℝ} (hr : 1 < r) (S : Finset ι) :
    (∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r) ^ (1 / r) ≤ ∫⁻ x, (∑ i ∈ S, g i x ^ r) ^ (1 / r) ∂μ := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hpq := Real.HolderConjugate.conjExponent hr
  rcases eq_or_ne (∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r) 0 with h0 | h0
  · rw [h0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  rcases eq_or_ne (∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r) ∞ with htop | htop
  · obtain ⟨i, hi, hgi⟩ := ENNReal.sum_eq_top.1 htop
    have hgi' : ∫⁻ x, g i x ∂μ = ∞ := by
      rcases ENNReal.rpow_eq_top_iff.1 hgi with ⟨_, h⟩ | ⟨h, _⟩
      · linarith
      · exact h
    have hI : ∫⁻ x, (∑ j ∈ S, g j x ^ r) ^ (1 / r) ∂μ = ∞ :=
      top_unique (hgi' ▸ lintegral_mono fun x =>
        ENNReal.le_rpow_sum_rpow (a := fun j => g j x) hi hr0)
    rw [hI]
    exact le_top
  have hc0 : (∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r) ^ (1 / r.conjExponent) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) htop).ne'
  have hctop : (∑ i ∈ S, (∫⁻ x, g i x ∂μ) ^ r) ^ (1 / r.conjExponent) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by have := hpq.symm.pos; positivity) htop
  refine (ENNReal.mul_le_mul_iff_left hc0 hctop).1 ?_
  rw [← ENNReal.rpow_add _ _ h0 htop, one_div, one_div, hpq.inv_add_inv_eq_one, ENNReal.rpow_one,
    ← one_div, ← one_div]
  exact sum_rpow_lintegral_le_mul hg hr S

section Countable

variable {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- **Minkowski's integral inequality for `ℓ_u`-valued functions**, `1 ≤ u ≤ ∞`: for measurable
`g_i : α → [0, ∞]` indexed by a countable set, `‖(∫ g_i)_i‖_{ℓ_u} ≤ ∫ ‖(g_i(x))_i‖_{ℓ_u} dx`. For
`u = 1` both sides are equal (Tonelli), for `u = ∞` the supremum of integrals is at most the
integral of the supremum, and for `1 < u < ∞` the finite sums are bounded by
`MeasureTheory.rpow_sum_rpow_lintegral_le`. -/
theorem lqNorm_lintegral_le {u : ℝ≥0∞} (hu : 1 ≤ u) {g : ι → α → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) μ) :
    lqNorm u (fun i => ∫⁻ x, g i x ∂μ) ≤ ∫⁻ x, lqNorm u (fun i => g i x) ∂μ := by
  rcases eq_or_ne u ∞ with rfl | hu'
  · simp only [ENNReal.lqNorm_top]
    exact iSup_le fun i => lintegral_mono fun x => le_iSup (fun j => g j x) i
  rcases eq_or_lt_of_le hu with rfl | hu1
  · simp only [ENNReal.lqNorm_one]
    exact (lintegral_tsum hg).ge
  have hu0 : u ≠ 0 := (zero_lt_one.trans hu1).ne'
  have hr : 1 < u.toReal := ENNReal.one_lt_toReal hu1 hu'
  have hr0 : 0 < u.toReal := zero_lt_one.trans hr
  simp only [ENNReal.lqNorm_eq_tsum hu0 hu']
  rw [one_div, ENNReal.rpow_inv_le_iff hr0, tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  rw [← ENNReal.rpow_inv_le_iff hr0, ← one_div]
  refine (rpow_sum_rpow_lintegral_le hg hr S).trans (lintegral_mono fun x => ?_)
  exact ENNReal.rpow_le_rpow (sum_le_tsum S) (by positivity)

/-- The pointwise `ℓ_q` norm `x ↦ ‖(g_i(x))_i‖_{ℓ_q}` of a countable family of measurable
functions is measurable: it is a constant for `q = 0`, a countable supremum for `q = ∞` and a
power of a series otherwise. -/
theorem aemeasurable_lqNorm_comp {g : ι → α → ℝ≥0∞} (hg : ∀ i, AEMeasurable (g i) μ)
    (q : ℝ≥0∞) : AEMeasurable (fun x => lqNorm q (fun i => g i x)) μ := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp only [ENNReal.lqNorm_zero_left]
    exact aemeasurable_const
  rcases eq_or_ne q ∞ with rfl | hq
  · simp only [ENNReal.lqNorm_top]
    exact AEMeasurable.iSup hg
  simp only [ENNReal.lqNorm_eq_tsum hq0 hq]
  exact (AEMeasurable.tsum fun i => (hg i).pow_const _).pow_const _

/-- The pointwise `ℓ_q` norm `x ↦ ‖(g_i(x))_i‖_{ℓ_q}` of a countable family of measurable
functions is measurable, as in `MeasureTheory.aemeasurable_lqNorm_comp`. -/
theorem measurable_lqNorm_comp {g : ι → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i)) (q : ℝ≥0∞) :
    Measurable fun x => lqNorm q (fun i => g i x) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp only [ENNReal.lqNorm_zero_left]
    exact measurable_const
  rcases eq_or_ne q ∞ with rfl | hq
  · simp only [ENNReal.lqNorm_top]
    exact Measurable.iSup hg
  simp only [ENNReal.lqNorm_eq_tsum hq0 hq]
  exact (Measurable.tsum fun i => (hg i).pow_const _).pow_const _

/-- **Minkowski's integral inequality on a probability space, in `L_p`**: for a probability
measure `μ`, `1 ≤ p ≤ ∞`, `1 ≤ q ≤ ∞` and almost everywhere measurable `g_i : α → [0, ∞]`
indexed by a countable set, `‖(∫ g_i dμ)_i‖_{ℓ_q} ≤ ‖ x ↦ ‖(g_i(x))_i‖_{ℓ_q} ‖_{L_p(μ)}`, by
`MeasureTheory.lqNorm_lintegral_le` and `‖·‖_1 ≤ ‖·‖_p` (Mathlib's
`eLpNorm_le_eLpNorm_of_exponent_le`). -/
theorem lqNorm_lintegral_le_eLpNorm [IsProbabilityMeasure μ] (hp1 : 1 ≤ p) (hq : 1 ≤ q)
    {g : ι → α → ℝ≥0∞} (hg : ∀ i, AEMeasurable (g i) μ) :
    lqNorm q (fun i => ∫⁻ x, g i x ∂μ) ≤ eLpNorm (fun x => lqNorm q (fun i => g i x)) p μ :=
  calc lqNorm q (fun i => ∫⁻ x, g i x ∂μ)
      ≤ ∫⁻ x, lqNorm q (fun i => g i x) ∂μ := lqNorm_lintegral_le hq hg
    _ = eLpNorm (fun x => lqNorm q (fun i => g i x)) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_eNorm (aemeasurable_lqNorm_comp hg q).aestronglyMeasurable]
        simp only [eNorm_eq_self]
    _ ≤ _ := eLpNorm_le_eLpNorm_of_exponent_le hp1

/-- **Minkowski's integral inequality for means**: for `1 ≤ u ≤ ∞` and almost everywhere
measurable `g_i : α → [0, ∞]` indexed by a countable set,
`‖(⨍ g_i dμ)_i‖_{ℓ_u} ≤ ⨍ ‖(g_i(x))_i‖_{ℓ_u} dμ(x)`. The mean is the integral for the normalised
measure `μ(α)⁻¹ μ`, so this is `MeasureTheory.lqNorm_lintegral_le`. -/
theorem lqNorm_laverage_le {u : ℝ≥0∞} (hu : 1 ≤ u) {g : ι → α → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) μ) :
    lqNorm u (fun i => ⨍⁻ x, g i x ∂μ) ≤ ⨍⁻ x, lqNorm u (fun i => g i x) ∂μ := by
  simp only [laverage_eq']
  exact lqNorm_lintegral_le hu fun i => (hg i).smul_measure _

/-! ### Comparison of `L_p(ℓ_q)` and `ℓ_q(L_p)` -/

/-- **`L_p(ℓ_p) = ℓ_p(L_p)`** for `0 < p < ∞`:
`‖ x ↦ ‖(g_i(x))_i‖_{ℓ_p} ‖_p = ‖(‖g_i‖_p)_i‖_{ℓ_p}`. Both sides to the power `p` equal
`∑_i ∫ g_i^p`, by Tonelli's theorem for series (`lintegral_tsum`). -/
theorem eLpNorm_lqNorm_eq_lqNorm_eLpNorm (hp0 : p ≠ 0) (hp : p ≠ ∞) {g : ι → α → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) μ) :
    eLpNorm (fun x => lqNorm p (fun i => g i x)) p μ = lqNorm p (fun i => eLpNorm (g i) p μ) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine ENNReal.rpow_left_injective hr.ne' ?_
  change eLpNorm _ p μ ^ p.toReal = lqNorm p _ ^ p.toReal
  rw [eLpNorm_rpow_eq_lintegral hp0 hp (aemeasurable_lqNorm_comp hg p),
    ENNReal.lqNorm_rpow hp0 hp]
  simp_rw [ENNReal.lqNorm_rpow hp0 hp]
  rw [lintegral_tsum fun i => (hg i).pow_const _]
  exact tsum_congr fun i => (eLpNorm_rpow_eq_lintegral hp0 hp (hg i)).symm

/-- **`ℓ_q(L_p) ≤ L_p(ℓ_q)` for `0 < p ≤ q ≤ ∞`**:
`‖(‖g_i‖_p)_i‖_{ℓ_q} ≤ ‖ x ↦ ‖(g_i(x))_i‖_{ℓ_q} ‖_p`. For `q = ∞` every `g_i` is at most the
pointwise supremum. For `q < ∞`, with `U = q/p ≥ 1`, the `p`-th power of the left side is
`‖(∫ g_i^p)_i‖_{ℓ_U}`, and Minkowski's integral inequality for `ℓ_U`-valued functions
(`MeasureTheory.lqNorm_lintegral_le`) bounds it by `∫ ‖(g_i^p)_i‖_{ℓ_U}`, the `p`-th power of the
right side. -/
theorem lqNorm_eLpNorm_le_eLpNorm_lqNorm (hp0 : p ≠ 0) (hpq : p ≤ q)
    {g : ι → α → ℝ≥0∞} (hg : ∀ i, AEMeasurable (g i) μ) :
    lqNorm q (fun i => eLpNorm (g i) p μ) ≤ eLpNorm (fun x => lqNorm q (fun i => g i x)) p μ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [ENNReal.lqNorm_top]
    refine iSup_le fun i => eLpNorm_mono_eNorm_ae (hg i).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [eNorm_eq_self]
    exact ENNReal.le_lqNorm ENNReal.top_ne_zero (fun j => g j x) i
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hU : q / p * ENNReal.ofReal p.toReal = q := by
    rw [ENNReal.ofReal_toReal hp, ENNReal.div_mul_cancel hp0 hp]
  have hU1 : 1 ≤ q / p :=
    (ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl hp)).2 (by rwa [one_mul])
  rw [← ENNReal.rpow_le_rpow_iff hr]
  calc lqNorm q (fun i => eLpNorm (g i) p μ) ^ p.toReal
      = lqNorm (q / p) (fun i => eLpNorm (g i) p μ ^ p.toReal) := by
        rw [ENNReal.lqNorm_fun_rpow _ hr, hU]
    _ = lqNorm (q / p) (fun i => ∫⁻ x, g i x ^ p.toReal ∂μ) := by
        congr 1
        funext i
        exact eLpNorm_rpow_eq_lintegral hp0 hp (hg i)
    _ ≤ ∫⁻ x, lqNorm (q / p) (fun i => g i x ^ p.toReal) ∂μ :=
        lqNorm_lintegral_le hU1 fun i => (hg i).pow_const _
    _ = ∫⁻ x, lqNorm q (fun i => g i x) ^ p.toReal ∂μ := by
        congr 1
        funext x
        rw [ENNReal.lqNorm_fun_rpow _ hr, hU]
    _ = eLpNorm (fun x => lqNorm q (fun i => g i x)) p μ ^ p.toReal :=
        (eLpNorm_rpow_eq_lintegral hp0 hp (aemeasurable_lqNorm_comp hg q)).symm

/-- **`L_p(ℓ_q) ≤ ℓ_q(L_p)` for `0 < q ≤ p < ∞`**:
`‖ x ↦ ‖(g_i(x))_i‖_{ℓ_q} ‖_p ≤ ‖(‖g_i‖_p)_i‖_{ℓ_q}`. If some `g_i` is not measurable, then
`‖g_i‖_p = ∞` and so is the right side. Otherwise, with `U = p/q ≥ 1`, the `q`-th power of the
left side is `‖∑_i g_i^q‖_U`, and Minkowski's inequality for series in `L_U`
(`MeasureTheory.eLpNorm_tsum_le`) bounds it by `∑_i ‖g_i^q‖_U = ∑_i ‖g_i‖_p^q`, the `q`-th power of
the right side. -/
theorem eLpNorm_lqNorm_le_lqNorm_eLpNorm (hq0 : q ≠ 0) (hqp : q ≤ p) (hp : p ≠ ∞)
    {g : ι → α → ℝ≥0∞} :
    eLpNorm (fun x => lqNorm q (fun i => g i x)) p μ ≤ lqNorm q (fun i => eLpNorm (g i) p μ) := by
  by_cases hg : ∀ i, AEMeasurable (g i) μ
  swap
  · obtain ⟨i, hi⟩ := not_forall.1 hg
    have h : eLpNorm (g i) p μ = ∞ :=
      eLpNorm_of_not_aestronglyMeasurable fun h => hi h.aemeasurable
    have hle := ENNReal.le_lqNorm hq0 (fun j => eLpNorm (g j) p μ) i
    rw [h, top_le_iff] at hle
    rw [hle]
    exact le_top
  have hq : q ≠ ∞ := ne_top_of_le_ne_top hp hqp
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hU : p / q * ENNReal.ofReal q.toReal = p := by
    rw [ENNReal.ofReal_toReal hq, ENNReal.div_mul_cancel hq0 hq]
  have hU1 : 1 ≤ p / q :=
    (ENNReal.le_div_iff_mul_le (Or.inl hq0) (Or.inl hq)).2 (by rwa [one_mul])
  rw [← ENNReal.rpow_le_rpow_iff hr]
  calc eLpNorm (fun x => lqNorm q (fun i => g i x)) p μ ^ q.toReal
      = eLpNorm (fun x => lqNorm q (fun i => g i x) ^ q.toReal) (p / q) μ := by
        rw [eLpNorm_fun_rpow (aemeasurable_lqNorm_comp hg q) hr, hU]
    _ = eLpNorm (fun x => ∑' i, g i x ^ q.toReal) (p / q) μ := by
        simp_rw [ENNReal.lqNorm_rpow hq0 hq]
    _ ≤ ∑' i, eLpNorm (fun x => g i x ^ q.toReal) (p / q) μ := eLpNorm_tsum_le hU1
    _ = ∑' i, eLpNorm (g i) p μ ^ q.toReal := by
        refine tsum_congr fun i => ?_
        rw [eLpNorm_fun_rpow (hg i) hr, hU]
    _ = lqNorm q (fun i => eLpNorm (g i) p μ) ^ q.toReal := (ENNReal.lqNorm_rpow hq0 hq _).symm

/-- **The upper half of the sandwich**:
`‖ x ↦ ‖(g_i(x))_i‖_{ℓ_q} ‖_p ≤ ‖(‖g_i‖_p)_i‖_{ℓ_{min(p,q)}}` for `1 ≤ p < ∞` and `1 ≤ q ≤ ∞`.
For `p ≤ q` the pointwise bound `‖·‖_{ℓ_q} ≤ ‖·‖_{ℓ_p}` and `L_p(ℓ_p) = ℓ_p(L_p)`; for `q ≤ p` the
inequality `L_p(ℓ_q) ≤ ℓ_q(L_p)`. -/
theorem eLpNorm_lqNorm_le_lqNorm_min (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hq : 1 ≤ q)
    {g : ι → α → ℝ≥0∞} (hg : ∀ i, AEMeasurable (g i) μ) :
    eLpNorm (fun x => lqNorm q (fun i => g i x)) p μ ≤
      lqNorm (min p q) (fun i => eLpNorm (g i) p μ) := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, ← eLpNorm_lqNorm_eq_lqNorm_eLpNorm (zero_lt_one.trans_le hp1).ne' hp hg]
    refine eLpNorm_mono_eNorm_ae (aemeasurable_lqNorm_comp hg q).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [eNorm_eq_self]
    exact ENNReal.lqNorm_le_lqNorm_of_le (zero_lt_one.trans_le hp1).ne' hpq _
  · rw [min_eq_right hqp]
    exact eLpNorm_lqNorm_le_lqNorm_eLpNorm (zero_lt_one.trans_le hq).ne' hqp hp

/-- **The lower half of the sandwich**:
`‖(‖g_i‖_p)_i‖_{ℓ_{max(p,q)}} ≤ ‖ x ↦ ‖(g_i(x))_i‖_{ℓ_q} ‖_p` for `1 ≤ p < ∞` and `1 ≤ q ≤ ∞`.
For `p ≤ q` the inequality `ℓ_q(L_p) ≤ L_p(ℓ_q)`; for `q ≤ p` the identity
`ℓ_p(L_p) = L_p(ℓ_p)` and the pointwise bound `‖·‖_{ℓ_p} ≤ ‖·‖_{ℓ_q}`. -/
theorem lqNorm_max_le_eLpNorm_lqNorm (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hq : 1 ≤ q)
    {g : ι → α → ℝ≥0∞} (hg : ∀ i, AEMeasurable (g i) μ) :
    lqNorm (max p q) (fun i => eLpNorm (g i) p μ) ≤
      eLpNorm (fun x => lqNorm q (fun i => g i x)) p μ := by
  rcases le_total p q with hpq | hqp
  · rw [max_eq_right hpq]
    exact lqNorm_eLpNorm_le_eLpNorm_lqNorm (zero_lt_one.trans_le hp1).ne' hpq hg
  · rw [max_eq_left hqp, ← eLpNorm_lqNorm_eq_lqNorm_eLpNorm (zero_lt_one.trans_le hp1).ne' hp hg]
    refine eLpNorm_mono_eNorm_ae (aemeasurable_lqNorm_comp hg p).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [eNorm_eq_self]
    exact ENNReal.lqNorm_le_lqNorm_of_le (zero_lt_one.trans_le hq).ne' hqp _

end Countable

/-! ### Weighted families of functions -/

section Weighted

variable {E : Type*} [NormedAddCommGroup E]

/-- **Homogeneity of the pointwise norm**: `‖c ‖v(·)‖‖_p = c ‖v‖_p` for every constant
`c ∈ [0, ∞]`, every measurable `v : α → E` with values in a normed group and every `p`. -/
theorem eLpNorm_const_mul_enorm (c : ℝ≥0∞) {v : α → E} (hv : AEStronglyMeasurable v μ)
    (p : ℝ≥0∞) : eLpNorm (fun x => c * ‖v x‖ₑ) p μ = c * eLpNorm v p μ := by
  rw [eLpNorm_const_mul_ennreal hv.eNorm.aestronglyMeasurable, eLpNorm_eNorm _ hv]

section Countable

variable {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {u : ι → α → E}

/-- **`L_p(ℓ_p) = ℓ_p(L_p)` for weighted families**: for `0 < p < ∞`, weights `w_j ∈ [0, ∞]` and
measurable `u_j : α → E` with values in a normed group, indexed by a countable set,
`‖ x ↦ ‖(w_j ‖u_j(x)‖)_j‖_{ℓ_p} ‖_p = ‖(w_j ‖u_j‖_p)_j‖_{ℓ_p}`. -/
theorem eLpNorm_lqNorm_weighted_eq (w : ι → ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) :
    eLpNorm (fun x => lqNorm p (fun j => w j * ‖u j x‖ₑ)) p μ =
      lqNorm p (fun j => w j * eLpNorm (u j) p μ) := by
  rw [eLpNorm_lqNorm_eq_lqNorm_eLpNorm hp0 hp fun j => (hu j).eNorm.const_mul _]
  congr 1
  funext j
  exact eLpNorm_const_mul_enorm (w j) (hu j) p

/-- **The upper half of the sandwich for weighted families**: for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
weights `w_j ∈ [0, ∞]` and measurable `u_j : α → E` with values in a normed group, indexed by a
countable set, `‖ x ↦ ‖(w_j ‖u_j(x)‖)_j‖_{ℓ_q} ‖_p ≤ ‖(w_j ‖u_j‖_p)_j‖_{ℓ_{min(p,q)}}`. -/
theorem eLpNorm_lqNorm_weighted_le_min (w : ι → ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hq : 1 ≤ q)
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) :
    eLpNorm (fun x => lqNorm q (fun j => w j * ‖u j x‖ₑ)) p μ ≤
      lqNorm (min p q) (fun j => w j * eLpNorm (u j) p μ) := by
  refine (eLpNorm_lqNorm_le_lqNorm_min hp1 hp hq fun j => (hu j).eNorm.const_mul _).trans_eq ?_
  congr 1
  funext j
  exact eLpNorm_const_mul_enorm (w j) (hu j) p

/-- **The lower half of the sandwich for weighted families**: for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
weights `w_j ∈ [0, ∞]` and measurable `u_j : α → E` with values in a normed group, indexed by a
countable set, `‖(w_j ‖u_j‖_p)_j‖_{ℓ_{max(p,q)}} ≤ ‖ x ↦ ‖(w_j ‖u_j(x)‖)_j‖_{ℓ_q} ‖_p`. -/
theorem lqNorm_max_weighted_le (w : ι → ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hq : 1 ≤ q)
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) :
    lqNorm (max p q) (fun j => w j * eLpNorm (u j) p μ) ≤
      eLpNorm (fun x => lqNorm q (fun j => w j * ‖u j x‖ₑ)) p μ := by
  refine le_of_eq_of_le ?_ (lqNorm_max_le_eLpNorm_lqNorm hp1 hp hq
    fun j => (hu j).eNorm.const_mul _)
  congr 1
  funext j
  exact (eLpNorm_const_mul_enorm (w j) (hu j) p).symm

end Countable

variable {s : ℝ} {u : ℕ → α → E}

/-- **`L_p(ℓ_p) = ℓ_p(L_p)` for dyadic weights**: for `0 < p < ∞`, `s ∈ ℝ` and measurable
`u_j : α → E`, `‖ x ↦ ‖(2^(js) ‖u_j(x)‖)_j‖_{ℓ_p} ‖_p = ‖(2^(js) ‖u_j‖_p)_j‖_{ℓ_p}`. With `u_j` the
Littlewood–Paley blocks of `f`, this says that the Triebel–Lizorkin and the Besov quasi-norm agree
for `q = p`. -/
theorem eLpNorm_lqNorm_dyadicWeight_eq (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) :
    eLpNorm (fun x => lqNorm p (fun j => dyadicWeight s j * ‖u j x‖ₑ)) p μ =
      lqNorm p (fun j => dyadicWeight s j * eLpNorm (u j) p μ) :=
  eLpNorm_lqNorm_weighted_eq (dyadicWeight s) hp0 hp hu

/-- **The upper half of the sandwich for dyadic weights**: for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`s ∈ ℝ` and measurable `u_j : α → E`,
`‖ x ↦ ‖(2^(js) ‖u_j(x)‖)_j‖_{ℓ_q} ‖_p ≤ ‖(2^(js) ‖u_j‖_p)_j‖_{ℓ_{min(p,q)}}`. -/
theorem eLpNorm_lqNorm_dyadicWeight_le_min (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hq : 1 ≤ q)
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) :
    eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j * ‖u j x‖ₑ)) p μ ≤
      lqNorm (min p q) (fun j => dyadicWeight s j * eLpNorm (u j) p μ) :=
  eLpNorm_lqNorm_weighted_le_min (dyadicWeight s) hp1 hp hq hu

/-- **The lower half of the sandwich for dyadic weights**: for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`s ∈ ℝ` and measurable `u_j : α → E`,
`‖(2^(js) ‖u_j‖_p)_j‖_{ℓ_{max(p,q)}} ≤ ‖ x ↦ ‖(2^(js) ‖u_j(x)‖)_j‖_{ℓ_q} ‖_p`. -/
theorem lqNorm_max_dyadicWeight_le (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hq : 1 ≤ q)
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) :
    lqNorm (max p q) (fun j => dyadicWeight s j * eLpNorm (u j) p μ) ≤
      eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j * ‖u j x‖ₑ)) p μ :=
  lqNorm_max_weighted_le (dyadicWeight s) hp1 hp hq hu

end Weighted

/-! ### Limits of pointwise bounds -/

/-- **Limits of pointwise bounds**: if `u` and `v` are measurable, `u ≤ v + w_J` almost everywhere
for every `J` and `‖w_J‖_p → 0` for some `p > 0`, then `u ≤ v` almost everywhere. The truncated
difference `(u - v)_+` has `‖(u - v)_+‖_p ≤ ‖w_J‖_p` for every `J`, hence norm `0`. This passes
pointwise bounds to limits in `L_p` for functions with values in `[0, ∞]` directly; Mathlib
derives convergence in measure from `L_p` convergence for functions with values in a normed group
(`tendstoInMeasure_of_tendsto_eLpNorm`). -/
theorem ae_le_of_le_add_of_tendsto_eLpNorm {u v : α → ℝ≥0∞} {w : ℕ → α → ℝ≥0∞}
    (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) (hp0 : p ≠ 0)
    (h : ∀ J, ∀ᵐ x ∂μ, u x ≤ v x + w J x)
    (hw : Tendsto (fun J => eLpNorm (w J) p μ) atTop (𝓝 0)) : ∀ᵐ x ∂μ, u x ≤ v x := by
  have hd : AEStronglyMeasurable (fun x => u x - v x) μ := (hu.sub hv).aestronglyMeasurable
  have hle : ∀ J, eLpNorm (fun x => u x - v x) p μ ≤ eLpNorm (w J) p μ := fun J =>
    eLpNorm_mono_eNorm_ae hd ((h J).mono fun x hx => by
      simp only [eNorm_eq_self]
      exact tsub_le_iff_left.2 hx)
  have h0 : eLpNorm (fun x => u x - v x) p μ = 0 := le_antisymm (ge_of_tendsto' hw hle) zero_le
  filter_upwards [(eLpNorm_eq_zero_iff hp0).1 h0] with x hx
  exact tsub_eq_zero_iff_le.1 hx

/-- **Pointwise bounds pass to limits in `L_p`**: for `1 ≤ p ≤ ∞`, if `G_J → F` in `L_p` and
`|G_J| ≤ v` almost everywhere for every `J`, then `|F| ≤ v` almost everywhere, for every
`v : α → [0, ∞]`. A subsequence of `G_J` converges to `F` almost everywhere (Mathlib's
`tendstoInMeasure_of_tendsto_Lp` and `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`). -/
theorem ae_enorm_le_of_tendsto_Lp {E : Type*} [NormedAddCommGroup E] [Fact (1 ≤ p)]
    {F : Lp E p μ} {G : ℕ → Lp E p μ} (hG : Tendsto G atTop (𝓝 F)) {v : α → ℝ≥0∞}
    (h : ∀ J, ∀ᵐ x ∂μ, ‖G J x‖ₑ ≤ v x) : ∀ᵐ x ∂μ, ‖F x‖ₑ ≤ v x := by
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  filter_upwards [hns, ae_all_iff.2 fun k => h (ns k)] with x hx hk
  exact le_of_tendsto' hx.eNorm hk

/-! ### Families with terms set to zero -/

/-- **Measurability with terms set to zero**: if every `g_j : α → [0, ∞]` is measurable, then for
every predicate `P` on `ℕ` the function `x ↦ ‖(1_P(j) g_j(x))_j‖_{ℓ_q}` is measurable, where
`1_P(j) g_j(x)` is `g_j(x)` if `P j` holds and `0` otherwise. -/
theorem aemeasurable_lqNorm_ite {P : ℕ → Prop} [DecidablePred P] {g : ℕ → α → ℝ≥0∞}
    (hg : ∀ j, AEMeasurable (g j) μ) (q : ℝ≥0∞) :
    AEMeasurable (fun x => lqNorm q fun j => if P j then g j x else 0) μ :=
  aemeasurable_lqNorm_comp (fun j => by
    split_ifs
    · exact hg j
    · exact aemeasurable_const) q

/-- **Setting terms to zero decreases the mixed norm**: for measurable `g_j : α → [0, ∞]` and every
predicate `P` on `ℕ`,
`‖x ↦ ‖(1_P(j) g_j(x))_j‖_{ℓ_q}‖_p ≤ ‖x ↦ ‖(g_j(x))_j‖_{ℓ_q}‖_p`, by the monotonicity of the
`ℓ_q` norm and of the `L_p` norm. -/
theorem eLpNorm_lqNorm_ite_le {P : ℕ → Prop} [DecidablePred P] {g : ℕ → α → ℝ≥0∞}
    (hg : ∀ j, AEMeasurable (g j) μ) :
    eLpNorm (fun x => lqNorm q fun j => if P j then g j x else 0) p μ ≤
      eLpNorm (fun x => lqNorm q fun j => g j x) p μ :=
  eLpNorm_mono_eNorm (aemeasurable_lqNorm_ite hg q).aestronglyMeasurable fun x => by
    simp only [eNorm_eq_self]
    exact ENNReal.lqNorm_mono fun j => by split_ifs <;> simp

/-- **Setting more terms to zero decreases the mixed norm**: for measurable `g_j : α → [0, ∞]` and
predicates `P`, `Q` on `ℕ` with `P j → Q j` for every `j`,
`‖x ↦ ‖(1_P(j) g_j(x))_j‖_{ℓ_q}‖_p ≤ ‖x ↦ ‖(1_Q(j) g_j(x))_j‖_{ℓ_q}‖_p`;
`MeasureTheory.eLpNorm_lqNorm_ite_le` is the case where `Q` always holds. -/
theorem eLpNorm_lqNorm_ite_mono {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    {g : ℕ → α → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) μ) (hPQ : ∀ j, P j → Q j) :
    eLpNorm (fun x => lqNorm q fun j => if P j then g j x else 0) p μ ≤
      eLpNorm (fun x => lqNorm q fun j => if Q j then g j x else 0) p μ :=
  eLpNorm_mono_eNorm (aemeasurable_lqNorm_ite hg q).aestronglyMeasurable fun x => by
    simp only [eNorm_eq_self]
    refine ENNReal.lqNorm_mono fun j => ?_
    by_cases hP : P j
    · simp only [hP, hPQ j hP, ↓reduceIte, le_refl]
    · simp only [hP, ↓reduceIte]
      exact zero_le

/-! ### Tails in `L_p(ℓ_q)` -/

/-- **Dominated convergence for tails in `L_p(ℓ_q)`**: for `0 < p, q < ∞` and measurable
`g_j : α → [0, ∞]` with `‖x ↦ ‖(g_j(x))_j‖_{ℓ_q}‖_p < ∞`,
`∫ ‖(0, …, 0, g_N(x), g_{N+1}(x), …)‖_{ℓ_q}^p dμ(x) → 0` as `N → ∞`: the integrands are at most
`‖(g_j(x))_j‖_{ℓ_q}^p`, which is integrable and hence finite almost everywhere, and tend to zero
wherever it is finite (`ENNReal.tendsto_lqNorm_ite_le`; Mathlib's
`tendsto_lintegral_of_dominated_convergence'`). -/
theorem tendsto_lintegral_lqNorm_ite_le_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0)
    (hq : q ≠ ∞) {g : ℕ → α → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) μ)
    (hG : eLpNorm (fun x => lqNorm q fun j => g j x) p μ ≠ ∞) :
    Tendsto (fun N => ∫⁻ x, (lqNorm q fun j => if N ≤ j then g j x else 0) ^ p.toReal ∂μ)
      atTop (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hGm : AEMeasurable (fun x => lqNorm q fun j => g j x) μ := aemeasurable_lqNorm_comp hg q
  have hint : ∫⁻ x, (lqNorm q fun j => g j x) ^ p.toReal ∂μ ≠ ∞ := by
    rw [← eLpNorm_rpow_eq_lintegral hp0 hp hGm]
    exact ENNReal.rpow_ne_top_of_nonneg hr.le hG
  have hFm : ∀ N, AEMeasurable (fun x => lqNorm q fun j => if N ≤ j then g j x else 0) μ :=
    fun N => aemeasurable_lqNorm_ite hg q
  have hae : ∀ᵐ x ∂μ, Tendsto (fun N => (lqNorm q fun j => if N ≤ j then g j x else 0) ^ p.toReal)
      atTop (𝓝 0) := by
    filter_upwards [ae_lt_top' (hGm.pow_const p.toReal) hint] with x hx
    have hx' := ((ENNReal.rpow_lt_top_iff_of_pos hr).1 hx).ne
    have h := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp
      (ENNReal.tendsto_lqNorm_ite_le hq0 hq hx')
    rwa [ENNReal.zero_rpow_of_pos hr] at h
  have hlim : Tendsto (fun N => ∫⁻ x, (lqNorm q fun j => if N ≤ j then g j x else 0) ^ p.toReal ∂μ)
      atTop (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' _ (fun N => (hFm N).pow_const _)
      (fun N => ae_of_all _ fun x => ?_) hint hae
    refine ENNReal.rpow_le_rpow (ENNReal.lqNorm_mono fun j => ?_) hr.le
    split_ifs
    · exact le_rfl
    · exact zero_le
  rwa [lintegral_zero] at hlim

/-- **Tails in `L_p(ℓ_q)` tend to zero**: for `0 < p, q < ∞` and measurable `g_j : α → [0, ∞]`
with `‖x ↦ ‖(g_j(x))_j‖_{ℓ_q}‖_p < ∞`,
`‖x ↦ ‖(0, …, 0, g_N(x), g_{N+1}(x), …)‖_{ℓ_q}‖_p → 0` as `N → ∞`
(`MeasureTheory.tendsto_lintegral_lqNorm_ite_le_rpow`). -/
theorem tendsto_eLpNorm_lqNorm_ite_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) (hq : q ≠ ∞)
    {g : ℕ → α → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) μ)
    (hG : eLpNorm (fun x => lqNorm q fun j => g j x) p μ ≠ ∞) :
    Tendsto (fun N => eLpNorm (fun x => lqNorm q fun j => if N ≤ j then g j x else 0) p μ)
      atTop (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp
    (tendsto_lintegral_lqNorm_ite_le_rpow hp0 hp hq0 hq hg hG)
  rw [ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)] at h
  refine h.congr fun N => ?_
  rw [Function.comp_apply, ← eLpNorm_rpow_eq_lintegral hp0 hp (aemeasurable_lqNorm_ite hg q),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

/-- **Cauchy sequences from tails in `L_p(ℓ_q)`**: let `0 < p, q < ∞`, let `g_j : α → [0, ∞]` be
measurable with `‖x ↦ ‖(g_j(x))_j‖_{ℓ_q}‖_p < ∞`, and let `C < ∞`. A sequence `S` in a
pseudo-extended metric space with `edist(S_{N'}, S_N) ≤ C ‖x ↦ ‖(g_j(x))_{j ≥ N}‖_{ℓ_q}‖_p` for
all `N ≤ N'` (the terms `j < N` set to `0`) is a Cauchy sequence: two members beyond `N` are
within `2 C` times the `N`-th tail, and the tails tend to zero
(`MeasureTheory.tendsto_eLpNorm_lqNorm_ite_le`; Mathlib's `EMetric.cauchySeq_iff_le_tendsto_0`). -/
theorem cauchySeq_of_edist_le_lqNorm_ite {E : Type*} [PseudoEMetricSpace E] {S : ℕ → E}
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) (hq : q ≠ ∞)
    {g : ℕ → α → ℝ≥0∞} (hg : ∀ j, AEMeasurable (g j) μ)
    (hG : eLpNorm (fun x => lqNorm q fun j => g j x) p μ ≠ ∞)
    (hS : ∀ N N', N ≤ N' → edist (S N') (S N) ≤
      C * eLpNorm (fun x => lqNorm q fun j => if N ≤ j then g j x else 0) p μ) :
    CauchySeq S := by
  have h := ENNReal.Tendsto.const_mul (tendsto_eLpNorm_lqNorm_ite_le hp0 hp hq0 hq hg hG)
    (Or.inr hC)
  rw [mul_zero] at h
  refine EMetric.cauchySeq_iff_le_tendsto_0.2 ⟨fun N => C * eLpNorm (fun x => lqNorm q fun j =>
    if N ≤ j then g j x else 0) p μ + C * eLpNorm (fun x => lqNorm q fun j =>
    if N ≤ j then g j x else 0) p μ, fun n m N hn hm => ?_, by simpa using h.add h⟩
  exact (edist_triangle_right _ _ (S N)).trans (add_le_add (hS N n hn) (hS N m hm))

/-! ### Splitting off the first term -/

/-- **Minkowski's inequality for a pointwise bound**: for `1 ≤ p`, a measurable `B : α → [0, ∞]`
and measurable `F_i : α → [0, ∞]`, `i ∈ s` finite, the bound `B ≤ c ∑_i F_i` almost everywhere
gives `‖B‖_p ≤ c ∑_i ‖F_i‖_p` (Mathlib's `MeasureTheory.eLpNorm_const_mul_ennreal` and
`eLpNorm_sum_le`). -/
theorem eLpNorm_le_const_mul_sum_of_ae_le (hp1 : 1 ≤ p) {ι : Type*} (s : Finset ι)
    {B : α → ℝ≥0∞} {F : ι → α → ℝ≥0∞} (hB : AEMeasurable B μ)
    (hF : ∀ i ∈ s, AEMeasurable (F i) μ) (c : ℝ≥0∞) (h : ∀ᵐ x ∂μ, B x ≤ c * ∑ i ∈ s, F i x) :
    eLpNorm B p μ ≤ c * ∑ i ∈ s, eLpNorm (F i) p μ := by
  calc eLpNorm B p μ ≤ eLpNorm (fun x => c * ∑ i ∈ s, F i x) p μ := by
        refine eLpNorm_mono_eNorm_ae hB.aestronglyMeasurable ?_
        filter_upwards [h] with x hx
        simpa only [eNorm_eq_self] using hx
    _ = c * eLpNorm (∑ i ∈ s, F i) p μ := by
        rw [eLpNorm_const_mul_ennreal (Finset.aemeasurable_fun_sum _ hF).aestronglyMeasurable,
          Finset.sum_fn]
    _ ≤ c * ∑ i ∈ s, eLpNorm (F i) p μ := by
        gcongr
        exact eLpNorm_sum_le hp1

/-- **The first term of a weighted family splits off**: for `1 ≤ p`, `1 ≤ q ≤ ∞`, `s ∈ ℝ` and
measurable `b_j : α → [0, ∞]`,
`‖x ↦ ‖(2^(js) b_j(x))_j‖_{ℓ_q}‖_p ≤ ‖b_0‖_p + ‖x ↦ ‖(2^((n+1)s) b_{n+1}(x))_n‖_{ℓ_q}‖_p`,
by the bound of the `ℓ_q` norm by its first term and its shifted tail
(`ENNReal.lqNorm_le_sum_range_add_shift`) and the triangle inequality in `L_p`. -/
theorem eLpNorm_lqNorm_dyadicWeight_le_zero_add_succ (hp1 : 1 ≤ p) (hq : 1 ≤ q) (s : ℝ)
    {b : ℕ → α → ℝ≥0∞} (hb : ∀ j, AEMeasurable (b j) μ) :
    eLpNorm (fun x => lqNorm q fun j => dyadicWeight s j * b j x) p μ ≤
      eLpNorm (b 0) p μ +
        eLpNorm (fun x => lqNorm q fun n => dyadicWeight s (n + 1) * b (n + 1) x) p μ := by
  refine (eLpNorm_mono_eNorm (f := fun x => lqNorm q fun j => dyadicWeight s j * b j x)
    (g := b 0 + fun x => lqNorm q fun n => dyadicWeight s (n + 1) * b (n + 1) x)
    (aemeasurable_lqNorm_comp (fun j => (hb j).const_mul _) q).aestronglyMeasurable
    fun x => ?_).trans (eLpNorm_add_le hp1)
  simp only [eNorm_eq_self, Pi.add_apply]
  refine (ENNReal.lqNorm_le_sum_range_add_shift hq _ 1).trans_eq ?_
  simp [ENNReal.dyadicWeight_zero_right]

/-! ### Mixed norms of families and of dyadically weighted families -/

section DyadicFamily

variable {s : ℝ} {u v w : ℕ → α → ℝ≥0∞}

/-- **The triangle inequality for mixed norms**: for `1 ≤ p`, `1 ≤ q ≤ ∞` and families
`u_j, v_j, w_j : α → [0, ∞]` with `w` measurable and, almost everywhere, `w_j ≤ u_j + v_j` for
every `j`, `‖x ↦ ‖(w_j(x))_j‖_{ℓ_q}‖_p` is at most the sum of the same norms of `u` and `v`, by
the triangle inequalities in `ℓ_q` at every point and in `L_p`. -/
theorem eLpNorm_lqNorm_le_add (hp1 : 1 ≤ p) (hq : 1 ≤ q) (hw : ∀ j, AEMeasurable (w j) μ)
    (h : ∀ᵐ x ∂μ, ∀ j, w j x ≤ u j x + v j x) :
    eLpNorm (fun x => lqNorm q fun j => w j x) p μ ≤
      eLpNorm (fun x => lqNorm q fun j => u j x) p μ +
        eLpNorm (fun x => lqNorm q fun j => v j x) p μ := by
  refine (eLpNorm_mono_eNorm_ae (g := (fun x => lqNorm q fun j => u j x) +
    fun x => lqNorm q fun j => v j x)
    (aemeasurable_lqNorm_comp hw q).aestronglyMeasurable ?_).trans (eLpNorm_add_le hp1)
  filter_upwards [h] with x hx
  simp only [eNorm_eq_self, Pi.add_apply]
  exact (ENNReal.lqNorm_mono hx).trans (ENNReal.lqNorm_add_le hq _ _)

/-- **Homogeneity of mixed norms**: for `c ∈ [0, ∞]` and families `u_j, w_j : α → [0, ∞]` with
`u` measurable and, almost everywhere, `w_j = c u_j` for every `j`,
`‖x ↦ ‖(w_j(x))_j‖_{ℓ_q}‖_p = c ‖x ↦ ‖(u_j(x))_j‖_{ℓ_q}‖_p`. -/
theorem eLpNorm_lqNorm_eq_const_mul (c : ℝ≥0∞) (hu : ∀ j, AEMeasurable (u j) μ)
    (h : ∀ᵐ x ∂μ, ∀ j, w j x = c * u j x) :
    eLpNorm (fun x => lqNorm q fun j => w j x) p μ =
      c * eLpNorm (fun x => lqNorm q fun j => u j x) p μ := by
  rw [← eLpNorm_const_mul_ennreal (c := c) (aemeasurable_lqNorm_comp hu q).aestronglyMeasurable]
  refine eLpNorm_congr_ae ?_
  filter_upwards [h] with x hx
  rw [← ENNReal.lqNorm_const_mul]
  exact congrArg (lqNorm q) (funext hx)

/-- **Smoothness `0` for dyadic families**: for every family `u_j : α → [0, ∞]`,
`‖x ↦ ‖(2^(j·0) u_j(x))_j‖_{ℓ_q}‖_p = ‖x ↦ ‖(u_j(x))_j‖_{ℓ_q}‖_p`, since the weights are `1`. -/
theorem eLpNorm_lqNorm_dyadicWeight_zero_left (u : ℕ → α → ℝ≥0∞) :
    eLpNorm (fun x => lqNorm q fun j => dyadicWeight 0 j * u j x) p μ =
      eLpNorm (fun x => lqNorm q fun j => u j x) p μ := by
  simp only [ENNReal.dyadicWeight_zero_left, one_mul]

/-- **Mixed norms decrease in `q`**: for `0 < q ≤ r ≤ ∞` and measurable `u_j : α → [0, ∞]`,
`‖x ↦ ‖(u_j(x))_j‖_{ℓ_r}‖_p ≤ ‖x ↦ ‖(u_j(x))_j‖_{ℓ_q}‖_p`, since `‖·‖_{ℓ_r} ≤ ‖·‖_{ℓ_q}` at
every point. -/
theorem eLpNorm_lqNorm_mono_exponent {r : ℝ≥0∞} (hq0 : q ≠ 0) (hqr : q ≤ r)
    (hu : ∀ j, AEMeasurable (u j) μ) :
    eLpNorm (fun x => lqNorm r fun j => u j x) p μ ≤
      eLpNorm (fun x => lqNorm q fun j => u j x) p μ :=
  eLpNorm_mono_eNorm (aemeasurable_lqNorm_comp hu r).aestronglyMeasurable fun x => by
    simp only [eNorm_eq_self]
    exact ENNReal.lqNorm_le_lqNorm_of_le hq0 hqr _

/-- **Monotonicity in `s` for dyadic families**: for `s ≤ t` and measurable `u_j : α → [0, ∞]`,
`‖x ↦ ‖(2^(js) u_j(x))_j‖_{ℓ_q}‖_p ≤ ‖x ↦ ‖(2^(jt) u_j(x))_j‖_{ℓ_q}‖_p`, since
`2^(js) ≤ 2^(jt)`. -/
theorem eLpNorm_lqNorm_dyadicWeight_mono_smoothness {t : ℝ} (hst : s ≤ t)
    (hu : ∀ j, AEMeasurable (u j) μ) :
    eLpNorm (fun x => lqNorm q fun j => dyadicWeight s j * u j x) p μ ≤
      eLpNorm (fun x => lqNorm q fun j => dyadicWeight t j * u j x) p μ :=
  eLpNorm_mono_eNorm
    (aemeasurable_lqNorm_comp (fun j => (hu j).const_mul _) q).aestronglyMeasurable
    fun x => by
      simp only [eNorm_eq_self]
      exact ENNReal.lqNorm_mono fun j => by gcongr; exact ENNReal.dyadicWeight_le_of_le hst j

end DyadicFamily

end MeasureTheory
