/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecificLimits.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# `ℓ_q` norms of sequences in `ℝ≥0∞`

For a sequence `a : ℕ → ℝ≥0∞` and `q ∈ (0, ∞]`,

`lqNorm q a = (∑ₙ a n ^ q) ^ (1/q)`   for `q < ∞`,   `lqNorm ∞ a = supₙ a n`.

**Why `ℝ≥0∞` and why `eLpNorm`.** All quasi-norms of approximation spaces are `ℓ_q` norms of
nonnegative sequences.  In `ℝ≥0∞` every series has a value, possibly `∞`, so no summability
side conditions appear, and membership in a space becomes the statement `lqNorm q a < ∞`.
This is Mathlib's own design for `L_p` (`MeasureTheory.eLpNorm`, `MeasureTheory.MemLp`).  The
definition is literally `eLpNorm a q Measure.count`, the `L_q` norm for the counting measure
on `ℕ`, so Minkowski's inequality (`MeasureTheory.eLpNorm_add_le`) and monotonicity come for
free from Mathlib.  The alternative, Mathlib's normed space `lp`, would require summability
proofs for every sequence that enters.

**Sums of powers.** The file opens with the comparison of a sum of powers with the power of the
sum in `[0, ∞]`: `∑_{i ∈ s} f_i^p ≤ (∑_{i ∈ s} f_i)^p` for `p ≥ 1`, the decrease of
`(∑_{i ∈ s} f_i^p)^(1/p)` in `p`, and `(∑_{i ∈ s} f_i)^p ≤ ∑_{i ∈ s} f_i^p` for `0 < p ≤ 1`
(`ENNReal.sum_rpow_le_rpow_sum`, `ENNReal.rpow_sum_rpow_le`, `ENNReal.rpow_sum_le_sum_rpow`).
These three are a copy of Mathlib PR #44783; delete them when the project's Mathlib has it. The
series form `(∑_i f_i)^p ≤ ∑_i f_i^p` for `0 < p ≤ 1` (`ENNReal.rpow_tsum_le_tsum_rpow`) bounds
the `q`-th power of an inner series by the series of the `q`-th powers for `q ≤ 1`, so that
estimates for `ℓ_1` transfer to `ℓ_q` (`ENNReal.lqNorm_le_rpow_mul_of_tsum_rpow_le`); it also
gives the decrease of `(∑_i f_i^p)^(1/p)` in `p` for series over any index set
(`ENNReal.rpow_tsum_rpow_le`).

**Exponents below `1`.** For `0 < q < 1` the `ℓ_q` norm satisfies only the quasi-triangle
inequality `‖a + b‖_q ≤ C_q (‖a‖_q + ‖b‖_q)` with Mathlib's constant `C_q = LpAddConst q`
(`ENNReal.lqNorm_add_le'`, `ENNReal.lqNorm_le_head_add_shift'`); `C_q = 2^(1/q - 1)` for
`0 < q < 1` and `C_q = 1` otherwise, with `1 ≤ C_q`, `2^(1/q) ≤ 2 C_q` and
`(x^q + y^q)^(1/q) ≤ C_q (x + y)` (`ENNReal.one_le_LpAddConst`,
`ENNReal.two_rpow_one_div_le_two_mul_LpAddConst`, `ENNReal.rpow_add_rpow_le_LpAddConst_mul`).
On any measure space the `p`-th power of the `L_p` quasi-norm, `0 < p ≤ 1`, is subadditive,
`‖f + g‖_p^p ≤ ‖f‖_p^p + ‖g‖_p^p` (`MeasureTheory.eLpNorm_add_rpow_le_of_le_one`), so sums of
many terms are estimated in the `p`-th power with constant `1`.

The file adds what Mathlib lacks: the explicit formulas, homogeneity for `ℝ≥0∞` scalars,
**monotonicity in `q`** (`lqNorm r a ≤ lqNorm q a` for `0 < q ≤ r`; Mathlib has only the
inclusion `lp.monotone`, without the norm bound), the Cauchy–Schwarz inequality
`∑_k a_k b_k ≤ ‖a‖_{ℓ_2} ‖b‖_{ℓ_2}` for series and for finite sums
(`ENNReal.lqNorm_one_mul_le`, `ENNReal.sum_mul_le_lqNorm_two_mul`), the splitting off of the
first term, also with dyadic weights (`ENNReal.lqNorm_dyadicWeight_le_of_head_of_succ_le`), tails
of sequences (`ENNReal.lqNorm_ite_le_eq`), sequences with one nonzero term
(`ENNReal.lqNorm_ite_eq`), reindexing along bijections and injections
(`ENNReal.lqNorm_comp_equiv`, `ENNReal.lqNorm_extend_zero`), the `ℓ_q` norm of the geometric
sequence for every `q` (`ENNReal.dyadicGeomConst`, which is `1` for `q = ∞`,
`ENNReal.dyadicGeomConst_top`), and the **dyadic weights**
`dyadicWeight s k = 2 ^ (k s)` that every approximation space uses, with the identity
`2^(ks) 2^(-(k-j)σ) = 2^(-k(σ-s)) 2^(jσ)` of almost diagonal estimates
(`ENNReal.dyadicWeight_mul_dyadicWeight_neg_sub`), the bound `2^(-(n-2)θ) ≤ 2^(2θ) 2^(-nθ)` for
truncated subtraction and `θ ≥ 0` (`ENNReal.dyadicWeight_neg_sub_two_le`), the bound
`2^{js} ≤ 2^{c|s|} 2^{ks}` for `|j - k| ≤ c` (`ENNReal.dyadicWeight_le_of_mem_Icc`), the weights
of integer order (`ENNReal.dyadicWeight_natCast`), and the powers of two `2^s ≠ ∞`, `1 ≤ 2^s`
for `s ≥ 0` (`ENNReal.two_rpow_ne_top`, `ENNReal.one_le_two_rpow`), `2^((k : ℤ) : ℝ) = 2^k`
(`ENNReal.two_rpow_intCast_natCast`) and `(ρ 2^(-j))^b = ρ^b 2^(-jb)`
(`ENNReal.ofReal_div_two_pow_rpow`).  Three inequalities in `[0, ∞]`,
`a x + b y ≤ (a + b)(x + y)`, `∑_i a_i b_i ≤ (∑_i a_i)(∑_i b_i)` and
`x_0 + ∑_{j<k} x_j ≤ 2 ∑_{j≤k} x_j` (`ENNReal.mul_add_mul_le_add_mul_add`,
`ENNReal.sum_mul_le_sum_mul_sum`, `ENNReal.add_sum_range_le_two_mul_sum`), bound sums of
products by products of sums and a sum with a repeated term by twice the sum; further identities
and inequalities for products, quotients and powers in `[0, ∞]` serve the constants of the
K-method and of the trace theorems
(`ENNReal.mul_div_rpow_eq`, `ENNReal.div_rpow_le_rpow_mul_div_rpow`).

For Mathlib's normed space `ℓ²` the file proves Parseval's identity in `ℝ≥0∞`,
`‖x‖² = ∑_i ‖x_i‖²` (`lp.enorm_sq_eq_tsum`), which computes norms through the coefficients of a
Hilbert basis.

For `L_p` norms of functions with values in `[0, ∞]` the file proves the rule for powers inside the
norm (`MeasureTheory.eLpNorm_fun_rpow`), monotone convergence
(`MeasureTheory.eLpNorm_iSup_of_directed`) and Minkowski's inequality for series
(`MeasureTheory.eLpNorm_tsum_le`); the `ℓ_q` versions are their cases for the counting measure.
For a function bounded between step values `a_n` on disjoint pieces of equal measure `c`, the
`L_q` norm compares with `c^(1/q) ‖a‖_{ℓ_q}` (`MeasureTheory.eLpNorm_le_of_le_on_pieces`,
`MeasureTheory.le_eLpNorm_of_le_on_pieces`), and `∫ u^r ≤ c^(r-1) ∫ u` for `u ≤ c`
(`MeasureTheory.lintegral_rpow_le_mul_lintegral_of_ae_le`), in particular `∫ u² ≤ c ∫ u`
(`MeasureTheory.lintegral_sq_le_mul_lintegral_of_ae_le`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ENNReal

/-! ### Sums of powers -/

section PowerSums

variable {ι : Type*}

/-- **Superadditivity of `x ↦ x^p` for `p ≥ 1`**: `∑_{i ∈ s} f_i^p ≤ (∑_{i ∈ s} f_i)^p` for every
finite set `s` and every family `f` in `[0, ∞]`, by induction over `s` from the case of two terms
(Mathlib's `ENNReal.add_rpow_le_rpow_add`). -/
theorem sum_rpow_le_rpow_sum (s : Finset ι) (f : ι → ℝ≥0∞) {p : ℝ} (hp1 : 1 ≤ p) :
    ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_rpow_of_pos (zero_lt_one.trans_le hp1)]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (add_rpow_le_rpow_add _ _ hp1)

/-- **The finite `ℓ_p` sums decrease in `p`**:
`(∑_{i ∈ s} f_i^q)^(1/q) ≤ (∑_{i ∈ s} f_i^p)^(1/p)` for `0 < p ≤ q`, every finite set `s` and every
family `f` in `[0, ∞]`. Write `f_i^q = (f_i^p)^(q/p)` with `q/p ≥ 1` and apply
`ENNReal.sum_rpow_le_rpow_sum`; this is the finite form of Mathlib's `ENNReal.rpow_add_rpow_le`. -/
theorem rpow_sum_rpow_le (s : Finset ι) (f : ι → ℝ≥0∞) {p q : ℝ} (hp_pos : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, f i ^ q) ^ (1 / q) ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) := by
  have hq_pos : 0 < q := hp_pos.trans_le hpq
  have h_rpow : ∀ i ∈ s, f i ^ q = (f i ^ p) ^ (q / p) := fun i _ => by
    rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hp_pos.ne']
  have h_sum : ∑ i ∈ s, (f i ^ p) ^ (q / p) ≤ (∑ i ∈ s, f i ^ p) ^ (q / p) :=
    sum_rpow_le_rpow_sum s (fun i => f i ^ p) ((one_le_div hp_pos).2 hpq)
  rw [Finset.sum_congr rfl h_rpow]
  calc (∑ i ∈ s, (f i ^ p) ^ (q / p)) ^ (1 / q)
      ≤ ((∑ i ∈ s, f i ^ p) ^ (q / p)) ^ (1 / q) := rpow_le_rpow h_sum (by positivity)
    _ = (∑ i ∈ s, f i ^ p) ^ (1 / p) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        field_simp

/-- **Subadditivity of `x ↦ x^p` for `0 < p ≤ 1`**: `(∑_{i ∈ s} f_i)^p ≤ ∑_{i ∈ s} f_i^p` for every
finite set `s` and every family `f` in `[0, ∞]` (Mathlib's `Finset.le_sum_of_subadditive` for the
case of two terms, `ENNReal.rpow_add_le_add_rpow`). -/
theorem rpow_sum_le_sum_rpow (s : Finset ι) (f : ι → ℝ≥0∞) {p : ℝ} (hp_pos : 0 < p)
    (hp1 : p ≤ 1) : (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p :=
  Finset.le_sum_of_subadditive (fun x : ℝ≥0∞ => x ^ p) (zero_rpow_of_pos hp_pos).le
    (fun x y => rpow_add_le_add_rpow x y hp_pos.le hp1) s f

/-- **Subadditivity of `x ↦ x^p` for series**, `0 < p ≤ 1`: `(∑_i f_i)^p ≤ ∑_i f_i^p` for every
family `f` in `[0, ∞]`. A series is the supremum of its finite partial sums
(`tsum_eq_iSup_sum`), the power `x ↦ x^p` commutes with suprema
(`ENNReal.orderIsoRpow`), and `ENNReal.rpow_sum_le_sum_rpow` bounds each partial sum. -/
theorem rpow_tsum_le_tsum_rpow (f : ι → ℝ≥0∞) {p : ℝ} (hp_pos : 0 < p) (hp1 : p ≤ 1) :
    (∑' i, f i) ^ p ≤ ∑' i, f i ^ p := by
  rw [tsum_eq_iSup_sum]
  calc (⨆ s : Finset ι, ∑ i ∈ s, f i) ^ p = ⨆ s : Finset ι, (∑ i ∈ s, f i) ^ p :=
        (orderIsoRpow p hp_pos).map_iSup _
    _ ≤ ⨆ s : Finset ι, ∑ i ∈ s, f i ^ p :=
        iSup_mono fun s => rpow_sum_le_sum_rpow s f hp_pos hp1
    _ = ∑' i, f i ^ p := tsum_eq_iSup_sum.symm

/-- **The `ℓ_p` sums of a series decrease in `p`**: `(∑_i f_i^q)^(1/q) ≤ (∑_i f_i^p)^(1/p)` for
`0 < p ≤ q` and every family `f` in `[0, ∞]` on any index set, so `‖f‖_{ℓ_q} ≤ ‖f‖_{ℓ_p}`; for a
countable index set this is `ENNReal.lqNorm_le_lqNorm_of_le`, the same bound for `ENNReal.lqNorm`.
The subadditivity `ENNReal.rpow_tsum_le_tsum_rpow` with the exponent `p/q ≤ 1`, applied to the
family `f_i^q`, gives `(∑_i f_i^q)^(p/q) ≤ ∑_i f_i^p`; this is the series form of
`ENNReal.rpow_sum_rpow_le`. -/
theorem rpow_tsum_rpow_le (f : ι → ℝ≥0∞) {p q : ℝ} (hp_pos : 0 < p) (hpq : p ≤ q) :
    (∑' i, f i ^ q) ^ (1 / q) ≤ (∑' i, f i ^ p) ^ (1 / p) := by
  have hq_pos : 0 < q := hp_pos.trans_le hpq
  have h := rpow_tsum_le_tsum_rpow (fun i => f i ^ q) (div_pos hp_pos hq_pos)
    ((div_le_one hq_pos).2 hpq)
  have hfi : ∀ i, (f i ^ q) ^ (p / q) = f i ^ p := fun i => by
    rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hq_pos.ne']
  simp_rw [hfi] at h
  calc (∑' i, f i ^ q) ^ (1 / q) = ((∑' i, f i ^ q) ^ (p / q)) ^ (1 / p) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        field_simp
    _ ≤ (∑' i, f i ^ p) ^ (1 / p) := rpow_le_rpow h (by positivity)

end PowerSums

/-- The **`ℓ_q` norm** of a family `a : ι → [0, ∞]`: `(∑_i a_i ^ q) ^ (1/q)` for `q < ∞` and
`sup_i a_i` for `q = ∞`, defined as the `L_q` norm for the counting measure.  The index set is `ℕ`
for sequences, `ℕ^d` for the spaces of dominating mixed smoothness and a finite set for the
coefficients of one level of atoms or wavelets; the general lemmas hold for every countable `ι`
with measurable singletons. -/
noncomputable def lqNorm {ι : Type*} [MeasurableSpace ι] (q : ℝ≥0∞) (a : ι → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm a q Measure.count

section Generic

variable {ι : Type*} [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
  {q r : ℝ≥0∞} {a b : ι → ℝ≥0∞}

/-- Every sequence is measurable for the counting measure; this is the side condition of the
Mathlib lemmas on `eLpNorm`. -/
theorem aestronglyMeasurable_count (a : ι → ℝ≥0∞) : AEStronglyMeasurable a Measure.count :=
  (measurable_of_countable a).aestronglyMeasurable

/-- `‖a‖_{ℓ_∞} = sup_n a_n`. -/
theorem lqNorm_top (a : ι → ℝ≥0∞) : lqNorm ∞ a = ⨆ n, a n := by
  simp [lqNorm, eLpNorm_exponent_top (aestronglyMeasurable_count a)]

/-- `‖a‖_{ℓ_q} = (∑_n a_n^q)^(1/q)` for `0 < q < ∞`. -/
theorem lqNorm_eq_tsum (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ι → ℝ≥0∞) :
    lqNorm q a = (∑' n, a n ^ q.toReal) ^ (1 / q.toReal) := by
  rw [lqNorm, eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq (aestronglyMeasurable_count a),
    lintegral_count]
  rfl

/-- `‖a‖_{ℓ_1} = ∑_n a_n`. -/
theorem lqNorm_one (a : ι → ℝ≥0∞) : lqNorm 1 a = ∑' n, a n := by
  simp [lqNorm_eq_tsum one_ne_zero one_ne_top]

/-- For `1 ≤ q < ∞` the exponent `q.toReal` is at least `1`. -/
theorem one_le_toReal_of_one_le (hq : 1 ≤ q) (hq' : q ≠ ∞) : 1 ≤ q.toReal := by
  simpa using ENNReal.toReal_mono hq' hq

/-- `a^r = a · a^(r-1)` in `[0, ∞]` for `r ≥ 1`. -/
theorem rpow_eq_mul_rpow_sub_one (a : ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) :
    a ^ r = a * a ^ (r - 1) := by
  calc a ^ r = a ^ ((1 : ℝ) + (r - 1)) := by ring_nf
    _ = a ^ (1 : ℝ) * a ^ (r - 1) := ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith)
    _ = a * a ^ (r - 1) := by rw [ENNReal.rpow_one]

/-- An exponent `1 < p < ∞` in `[0, ∞]` has real value `p.toReal > 1`. -/
theorem one_lt_toReal {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) : 1 < p.toReal := by
  simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1

/-- An exponent `0 < q ≤ 1` in `[0, ∞]` has real value `q.toReal ∈ (0, 1]`. -/
theorem toReal_mem_Ioc_of_le_one (hq0 : q ≠ 0) (hq1 : q ≤ 1) : q.toReal ∈ Set.Ioc 0 1 :=
  ⟨ENNReal.toReal_pos hq0 (ne_top_of_le_ne_top one_ne_top hq1),
    by simpa using ENNReal.toReal_mono one_ne_top hq1⟩

/-- The `q`-th power of the norm is the sum of the `q`-th powers. -/
theorem lqNorm_rpow (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ι → ℝ≥0∞) :
    lqNorm q a ^ q.toReal = ∑' n, a n ^ q.toReal := by
  have hp : q.toReal ≠ 0 := (ENNReal.toReal_pos hq0 hq).ne'
  rw [lqNorm_eq_tsum hq0 hq, one_div, ENNReal.rpow_inv_rpow hp]

/-- **The square of the `ℓ_2` norm** is the sum of the squares:
`‖a‖_{ℓ_2}² = ∑_i a_i²` (`ENNReal.lqNorm_rpow` with `q = 2`, natural exponent). -/
theorem lqNorm_two_sq (a : ι → ℝ≥0∞) : lqNorm 2 a ^ 2 = ∑' i, a i ^ 2 := by
  have h := lqNorm_rpow two_ne_zero ofNat_ne_top a
  simpa only [toReal_ofNat, rpow_two] using h

/-- **The Cauchy–Schwarz inequality for nonnegative sequences**:
`∑_k a_k b_k ≤ ‖a‖_{ℓ_2} ‖b‖_{ℓ_2}` for families `a, b` in `[0, ∞]` indexed by a countable set
(Mathlib's `ENNReal.lintegral_mul_le_Lp_mul_Lq` for the counting measure). -/
theorem lqNorm_one_mul_le (a b : ι → ℝ≥0∞) :
    lqNorm 1 (fun k => a k * b k) ≤ lqNorm 2 a * lqNorm 2 b := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ι)
    Real.HolderConjugate.two_two (measurable_of_countable a).aemeasurable
    (measurable_of_countable b).aemeasurable
  rw [lqNorm_one, lqNorm_eq_tsum two_ne_zero ofNat_ne_top, lqNorm_eq_tsum two_ne_zero ofNat_ne_top]
  simpa [lintegral_count] using h

/-- **The Cauchy–Schwarz inequality for finite sums against `ℓ_2` norms**:
`∑_{j ∈ s} a_j b_j ≤ ‖a‖_{ℓ_2} ‖b‖_{ℓ_2}` for every finite set `s` and all families `a, b` in
`[0, ∞]` indexed by a countable set: a finite sum is at most the series
(`sum_le_tsum`), which is the `ℓ_1` norm of the products (`ENNReal.lqNorm_one`), and
`ENNReal.lqNorm_one_mul_le` bounds that. -/
theorem sum_mul_le_lqNorm_two_mul (s : Finset ι) (a b : ι → ℝ≥0∞) :
    ∑ j ∈ s, a j * b j ≤ lqNorm 2 a * lqNorm 2 b :=
  (sum_le_tsum s).trans ((lqNorm_one _).symm.trans_le (lqNorm_one_mul_le a b))

omit [Countable ι] [MeasurableSingletonClass ι] in
/-- The zero family has norm `0`. -/
@[simp]
theorem lqNorm_zero_right (q : ℝ≥0∞) : lqNorm q (fun _ : ι => (0 : ℝ≥0∞)) = 0 := eLpNorm_fun_zero

/-- The exponent `0` is degenerate: `eLpNorm` assigns it the value `0`.  The statements below
that hold only for genuine exponents carry a hypothesis `q ≠ 0` or `1 ≤ q`; the others hold for
every `q`. -/
@[simp]
theorem lqNorm_zero_left (a : ι → ℝ≥0∞) : lqNorm 0 a = 0 :=
  eLpNorm_exponent_zero (aestronglyMeasurable_count a)

omit [Countable ι] in
/-- Every term is bounded by the norm. -/
theorem le_lqNorm (hq : q ≠ 0) (a : ι → ℝ≥0∞) (n : ι) : a n ≤ lqNorm q a :=
  eNorm_le_eLpNorm_count a n hq

/-- The `ℓ_q` norm is monotone in the sequence. -/
theorem lqNorm_mono (h : ∀ n, a n ≤ b n) : lqNorm q a ≤ lqNorm q b :=
  eLpNorm_mono_eNorm (aestronglyMeasurable_count a) h

omit [Countable ι] [MeasurableSingletonClass ι] in
/-- **Minkowski's inequality** for `ℓ_q`, `1 ≤ q ≤ ∞`. -/
theorem lqNorm_add_le (hq : 1 ≤ q) (a b : ι → ℝ≥0∞) :
    lqNorm q (fun n => a n + b n) ≤ lqNorm q a + lqNorm q b :=
  eLpNorm_add_le (f := a) (g := b) hq

omit [Countable ι] [MeasurableSingletonClass ι] in
/-- **The quasi-triangle inequality** for `ℓ_q`, every `q ∈ [0, ∞]`:
`‖a + b‖_q ≤ C_q (‖a‖_q + ‖b‖_q)` with Mathlib's constant `C_q = LpAddConst q`, which is
`2^(1/q - 1)` for `0 < q < 1` and `1` otherwise (`MeasureTheory.eLpNorm_add_le'` for the counting
measure). -/
theorem lqNorm_add_le' (q : ℝ≥0∞) (a b : ι → ℝ≥0∞) :
    lqNorm q (fun n => a n + b n) ≤ LpAddConst q * (lqNorm q a + lqNorm q b) :=
  eLpNorm_add_le' (f := a) (g := b) q

/-- **Homogeneity**: `‖c a‖_q = c ‖a‖_q` for every `c ∈ ℝ≥0∞`. -/
theorem lqNorm_const_mul (c : ℝ≥0∞) (a : ι → ℝ≥0∞) :
    lqNorm q (fun n => c * a n) = c * lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, lqNorm_top, ENNReal.mul_iSup]
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- **Comparable sequences have finite `ℓ_q` norms together**: if `a ≤ M b` and `b ≤ K a` with
finite `K, M`, then `‖a‖_q < ∞ ↔ ‖b‖_q < ∞`. -/
theorem lqNorm_lt_top_iff_of_le_mul {a b : ι → ℝ≥0∞} {K M : ℝ≥0∞} (hK : K ≠ ∞) (hM : M ≠ ∞)
    (hab : ∀ n, a n ≤ M * b n) (hba : ∀ n, b n ≤ K * a n) :
    lqNorm q a < ∞ ↔ lqNorm q b < ∞ := by
  constructor
  · intro h
    calc lqNorm q b ≤ lqNorm q (fun n => K * a n) := lqNorm_mono hba
      _ = K * lqNorm q a := lqNorm_const_mul K a
      _ < ∞ := ENNReal.mul_lt_top hK.lt_top h
  · intro h
    calc lqNorm q a ≤ lqNorm q (fun n => M * b n) := lqNorm_mono hab
      _ = M * lqNorm q b := lqNorm_const_mul M b
      _ < ∞ := ENNReal.mul_lt_top hM.lt_top h

/-- **Monotonicity in the exponent**: for `0 < q ≤ r`, `‖a‖_r ≤ ‖a‖_q`, also for exponents below
`1`.  For `r = ∞` every term is at most `‖a‖_q`; for `r < ∞` this is the decrease of the `ℓ_p`
sums of a series in `p` (`ENNReal.rpow_tsum_rpow_le`). -/
theorem lqNorm_le_lqNorm_of_le (hq0 : q ≠ 0) (hqr : q ≤ r) (a : ι → ℝ≥0∞) :
    lqNorm r a ≤ lqNorm q a := by
  rcases eq_or_ne r ∞ with rfl | hr
  · rw [lqNorm_top]; exact iSup_le (le_lqNorm hq0 a)
  have hq' : q ≠ ∞ := ne_top_of_le_ne_top hr hqr
  have hr0 : r ≠ 0 := ((pos_iff_ne_zero.2 hq0).trans_le hqr).ne'
  rw [lqNorm_eq_tsum hr0 hr, lqNorm_eq_tsum hq0 hq']
  exact rpow_tsum_rpow_le a (ENNReal.toReal_pos hq0 hq') (ENNReal.toReal_mono hr hqr)

/-- `‖a‖_{ℓ_q} ≤ ‖a‖_{ℓ_1} = ∑_i a_i` for `q ≥ 1`. -/
theorem lqNorm_le_lqNorm_one (hq : 1 ≤ q) (a : ι → ℝ≥0∞) : lqNorm q a ≤ ∑' n, a n := by
  simpa [lqNorm_one] using lqNorm_le_lqNorm_of_le one_ne_zero hq a

/-- A family that vanishes outside a finite set `s` has `‖a‖_{ℓ_q} ≤ ∑_{i ∈ s} a_i` for
`q ≥ 1` (`ENNReal.lqNorm_le_lqNorm_one`). -/
theorem lqNorm_le_sum_of_eq_zero (hq : 1 ≤ q) (s : Finset ι) (ha : ∀ i ∉ s, a i = 0) :
    lqNorm q a ≤ ∑ i ∈ s, a i :=
  (lqNorm_le_lqNorm_one hq a).trans_eq (tsum_eq_sum ha)

/-- For a finite index set, `‖a‖_{ℓ_q} = (∑_i a_i^q)^(1/q)` for `0 < q < ∞`. -/
theorem lqNorm_eq_sum [Fintype ι] (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ι → ℝ≥0∞) :
    lqNorm q a = (∑ i, a i ^ q.toReal) ^ (1 / q.toReal) := by
  rw [lqNorm_eq_tsum hq0 hq, tsum_fintype]

/-- For a finite index set, a family bounded by `B` has `‖a‖_{ℓ_q} ≤ (#ι)^(1/q) B` (Mathlib's
`eLpNorm_le_of_ae_eNorm_bound`, with `#ι` the counting measure of `ι`). -/
theorem lqNorm_le_card_rpow_mul [Fintype ι] {B : ℝ≥0∞} (h : ∀ i, a i ≤ B) :
    lqNorm q a ≤ (Fintype.card ι : ℝ≥0∞) ^ (1 / q.toReal) * B := by
  refine (eLpNorm_le_of_ae_eNorm_bound (aestronglyMeasurable_count a)
    (Eventually.of_forall h)).trans_eq ?_
  rw [Measure.count_univ, ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe, smul_eq_mul,
    mul_comm, one_div]

/-- **The `ℓ_q` norm on a finite product**: `‖a‖_{ℓ_q(M × N)}^q = ∑_m ‖a_{m,·}‖_{ℓ_q(N)}^q` for
`0 < q < ∞`. -/
theorem lqNorm_prod_rpow {M N : Type*} [Fintype M] [Finite N] [MeasurableSpace M]
    [MeasurableSpace N] [MeasurableSingletonClass M] [MeasurableSingletonClass N] (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (a : M × N → ℝ≥0∞) :
    lqNorm q a ^ q.toReal = ∑ m, lqNorm q (fun n => a (m, n)) ^ q.toReal := by
  let := Fintype.ofFinite N
  rw [lqNorm_rpow hq0 hq, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [lqNorm_rpow hq0 hq, tsum_fintype]

/-- **Iterated `ℓ_q` norms**: for `0 < q < ∞` and families `a_k` on countable index sets `N_k`,
`‖(‖a_k‖_{ℓ_q(N_k)})_k‖_{ℓ_q}^q = ∑_k ∑_{n ∈ N_k} a_{k,n}^q`, the `q`-th power of the `ℓ_q` norm
of the whole family. -/
theorem lqNorm_lqNorm_rpow {N : ι → Type*} [∀ k, MeasurableSpace (N k)] [∀ k, Countable (N k)]
    [∀ k, MeasurableSingletonClass (N k)] (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ∀ k, N k → ℝ≥0∞) :
    lqNorm q (fun k => lqNorm q (a k)) ^ q.toReal = ∑' k, ∑' n, a k n ^ q.toReal := by
  rw [lqNorm_rpow hq0 hq]
  exact tsum_congr fun k => lqNorm_rpow hq0 hq (a k)

/-! ### Reindexing -/

variable {ι' : Type*} [MeasurableSpace ι'] [Countable ι'] [MeasurableSingletonClass ι']

/-- **Reindexing by a bijection** does not change the `ℓ_q` norm: `‖a ∘ e‖_q = ‖a‖_q`. -/
theorem lqNorm_comp_equiv (e : ι ≃ ι') (a : ι' → ℝ≥0∞) : lqNorm q (a ∘ e) = lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [lqNorm_zero_left]
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, lqNorm_top]
    exact e.iSup_comp
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq]
  congr 1
  exact e.tsum_eq fun n => a n ^ q.toReal

/-- **Extension by zero along an injective map** does not change the `ℓ_q` norm: if
`g : ι → ι'` is injective, the family on `ι'` equal to `a i` at `g i` and to `0` off the range
of `g` has the norm of `a`. -/
theorem lqNorm_extend_zero {g : ι → ι'} (hg : Function.Injective g) (a : ι → ℝ≥0∞) :
    lqNorm q (Function.extend g a 0) = lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [lqNorm_zero_left]
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, lqNorm_top]
    exact iSup_extend_bot hg a
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq]
  congr 1
  have hext : ∀ n, Function.extend g a 0 n ^ q.toReal =
      Function.extend g (fun i => a i ^ q.toReal) 0 n :=
    fun n => by
      rw [Function.apply_extend (· ^ q.toReal) g 0 n]
      congr 1
      funext m
      simp [ENNReal.zero_rpow_of_pos hp]
  simp_rw [hext]
  exact tsum_extend_zero hg _

/-- **Restriction to the range of an injective map** does not increase the `ℓ_q` norm:
`‖a ∘ g‖_q ≤ ‖a‖_q`. -/
theorem lqNorm_comp_le_of_injective {g : ι → ι'} (hg : Function.Injective g) (a : ι' → ℝ≥0∞) :
    lqNorm q (a ∘ g) ≤ lqNorm q a := by
  rw [← lqNorm_extend_zero hg]
  refine lqNorm_mono fun n => ?_
  by_cases hn : ∃ i, g i = n
  · obtain ⟨i, rfl⟩ := hn
    rw [hg.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ hn]
    exact zero_le

/-- **Comparing `ℓ_q` norms through the sums of `q`-th powers**: for `q < ∞` and families
`a`, `b` in `[0, ∞]` on two countable sets, if `∑_i a_i^q ≤ C ∑_j b_j^q`, then
`‖a‖_{ℓ_q} ≤ C^(1/q) ‖b‖_{ℓ_q}` (for `q = 0` the left side is the degenerate value `0`). For
`q ≤ 1` the `q`-th power of an inner series is at most the series of the `q`-th powers, so an
inequality for `ℓ_1` norms transfers to `ℓ_q` this way. -/
theorem lqNorm_le_rpow_mul_of_tsum_rpow_le (hq : q ≠ ∞) {a : ι → ℝ≥0∞}
    {b : ι' → ℝ≥0∞} {C : ℝ≥0∞} (h : ∑' i, a i ^ q.toReal ≤ C * ∑' j, b j ^ q.toReal) :
    lqNorm q a ≤ C ^ (1 / q.toReal) * lqNorm q b := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq, ← mul_rpow_of_nonneg _ _ (by positivity)]
  exact rpow_le_rpow h (by positivity)

end Generic

/-- Restricting every member of a family to a set `S` restricts its pointwise `ℓ_q` norm:
`‖(1_S g_i(x))_i‖_{ℓ_q} = 1_S(x) ‖(g_i(x))_i‖_{ℓ_q}`. -/
theorem lqNorm_indicator {α ι : Type*} [MeasurableSpace ι] (q : ℝ≥0∞)
    (S : Set α) (g : ι → α → ℝ≥0∞) (x : α) :
    lqNorm q (fun i => S.indicator (g i) x) =
      S.indicator (fun y => lqNorm q (fun i => g i y)) x := by
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, ENNReal.lqNorm_zero_right]

variable {q r : ℝ≥0∞} {a b : ℕ → ℝ≥0∞}

/-- Dropping the first term does not increase the norm. -/
theorem lqNorm_shift_le (a : ℕ → ℝ≥0∞) : lqNorm q (fun n => a (n + 1)) ≤ lqNorm q a :=
  lqNorm_comp_le_of_injective (add_left_injective 1) a

/-- `‖(…, 0, x, 0, …)‖_{ℓ_q} = x` for a sequence with one nonzero term and every `q ≠ 0`. -/
theorem lqNorm_ite_eq {q : ℝ≥0∞} (hq0 : q ≠ 0) (j : ℕ) (x : ℝ≥0∞) :
    lqNorm q (fun i => if i = j then x else 0) = x := by
  have h : (fun i => if i = j then x else 0) = ({j} : Set ℕ).indicator fun _ => x := by
    funext i
    by_cases hi : i = j
    · rw [Set.indicator_of_mem (Set.mem_singleton_iff.2 hi)]; simp [hi]
    · rw [Set.indicator_of_notMem (mt Set.mem_singleton_iff.1 hi)]; simp [hi]
  rw [lqNorm, h, eLpNorm_indicator_const' (measurableSet_singleton j).nullMeasurableSet
    (by simp) hq0, Measure.count_singleton, ENNReal.one_rpow, mul_one]
  rfl

/-- **Splitting off the first term, for every exponent**:
`‖a‖_q ≤ C_q (a 0 + ‖(a (n + 1))ₙ‖_q)` with Mathlib's constant `C_q = LpAddConst q` of the
quasi-triangle inequality (`ENNReal.lqNorm_add_le'`) for
`a = (a 0, 0, 0, …) + (0, a 1, a 2, …)`; the second summand is the extension by zero of
`(a (n + 1))ₙ` along `n ↦ n + 1` (`ENNReal.lqNorm_extend_zero`). -/
theorem lqNorm_le_head_add_shift' (q : ℝ≥0∞) (a : ℕ → ℝ≥0∞) :
    lqNorm q a ≤ LpAddConst q * (a 0 + lqNorm q (fun n => a (n + 1))) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hab : a = fun n => (if n = 0 then a 0 else 0) +
      Function.extend (· + 1) (fun n => a (n + 1)) 0 n := by
    funext n
    rcases n with _ | n
    · simp
    · simp [(add_left_injective 1).extend_apply (fun n => a (n + 1)) 0 n]
  calc lqNorm q a ≤ LpAddConst q * (lqNorm q (fun n => if n = 0 then a 0 else 0) +
        lqNorm q (Function.extend (· + 1) (fun n => a (n + 1)) 0)) := by
        conv_lhs => rw [hab]
        exact lqNorm_add_le' q _ _
    _ = LpAddConst q * (a 0 + lqNorm q (fun n => a (n + 1))) := by
        rw [lqNorm_extend_zero (add_left_injective 1), lqNorm_ite_eq hq0]

/-- **Splitting off the first term**: `‖a‖_q ≤ a 0 + ‖(a (n + 1))ₙ‖_q` for `1 ≤ q ≤ ∞`, the case
`LpAddConst q = 1` of `ENNReal.lqNorm_le_head_add_shift'`. -/
theorem lqNorm_le_head_add_shift (hq : 1 ≤ q) (a : ℕ → ℝ≥0∞) :
    lqNorm q a ≤ a 0 + lqNorm q (fun n => a (n + 1)) := by
  simpa [LpAddConst_of_one_le hq] using lqNorm_le_head_add_shift' q a

/-- **Splitting off the first `m` terms**: `‖a‖_q ≤ a 0 + ⋯ + a (m - 1) + ‖(a (n + m))ₙ‖_q`. -/
theorem lqNorm_le_sum_range_add_shift (hq : 1 ≤ q) (a : ℕ → ℝ≥0∞) (m : ℕ) :
    lqNorm q a ≤ ∑ j ∈ Finset.range m, a j + lqNorm q (fun n => a (n + m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hshift : (fun n => a (n + 1 + m)) = fun n => a (n + (m + 1)) := by
      funext n
      congr 1
      omega
    calc lqNorm q a ≤ ∑ j ∈ Finset.range m, a j + lqNorm q (fun n => a (n + m)) := ih
      _ ≤ ∑ j ∈ Finset.range m, a j + (a (0 + m) + lqNorm q (fun n => a (n + 1 + m))) := by
          gcongr
          exact lqNorm_le_head_add_shift hq (fun n => a (n + m))
      _ = ∑ j ∈ Finset.range (m + 1), a j + lqNorm q (fun n => a (n + (m + 1))) := by
          rw [hshift, Finset.sum_range_succ, zero_add, add_assoc]

/-- The norm of a geometric sequence: `‖(r ^ k)ₖ‖_q ≤ (1 - r)⁻¹`, the value of the series
for `q = 1`. -/
theorem lqNorm_geometric_le (hq : 1 ≤ q) (r : ℝ≥0∞) :
    lqNorm q (fun k => r ^ k) ≤ (1 - r)⁻¹ := by
  calc lqNorm q (fun k => r ^ k) ≤ lqNorm 1 (fun k => r ^ k) :=
        lqNorm_le_lqNorm_of_le one_ne_zero hq _
    _ = (1 - r)⁻¹ := by rw [lqNorm_one, ENNReal.tsum_geometric]

/-! ### Dyadic weights -/

/-- The **dyadic weight** `2 ^ (k s)`: the factor by which the error `E_{2^k}` is multiplied
in the dyadic form of an approximation space of smoothness `s`. -/
noncomputable def dyadicWeight (s : ℝ) (k : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((k : ℝ) * s)

variable {s t : ℝ}

/-- `2^s` is finite in `ℝ≥0∞`. -/
theorem two_rpow_ne_top (s : ℝ) : (2 : ℝ≥0∞) ^ s ≠ ∞ :=
  rpow_ne_top_of_ne_zero two_ne_zero ofNat_ne_top

/-- `1 ≤ 2^s` for `s ≥ 0`. -/
theorem one_le_two_rpow (hs : 0 ≤ s) : 1 ≤ (2 : ℝ≥0∞) ^ s := by
  simpa using ENNReal.rpow_le_rpow_of_exponent_le one_le_two hs

/-- `1 ≤ 2 · 2^s` for `s ≥ 0`: the quasi-triangle constants `2 · 2^s` of the dyadic quasi-norms
dominate the constant `1` of the norm. -/
theorem one_le_two_mul_two_rpow (hs : 0 ≤ s) : 1 ≤ (2 : ℝ≥0∞) * 2 ^ s :=
  one_le_two.trans (le_mul_of_one_le_right' (ENNReal.one_le_two_rpow hs))

/-- `2^(0·s) = 1`. -/
@[simp]
theorem dyadicWeight_zero_right (s : ℝ) : dyadicWeight s 0 = 1 := by simp [dyadicWeight]

/-- `2^(k·0) = 1`. -/
@[simp]
theorem dyadicWeight_zero_left (k : ℕ) : dyadicWeight 0 k = 1 := by simp [dyadicWeight]

/-- The dyadic weights are finite. -/
theorem dyadicWeight_ne_top (s : ℝ) (k : ℕ) : dyadicWeight s k ≠ ∞ :=
  ENNReal.two_rpow_ne_top _

/-- The dyadic weights are finite. -/
theorem dyadicWeight_lt_top (s : ℝ) (k : ℕ) : dyadicWeight s k < ∞ :=
  (dyadicWeight_ne_top s k).lt_top

/-- The dyadic weights are positive. -/
theorem dyadicWeight_pos (s : ℝ) (k : ℕ) : 0 < dyadicWeight s k :=
  ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top

/-- The dyadic weights are nonzero. -/
theorem dyadicWeight_ne_zero (s : ℝ) (k : ℕ) : dyadicWeight s k ≠ 0 := (dyadicWeight_pos s k).ne'

/-- `2^(k(s+t)) = 2^(ks) 2^(kt)`. -/
theorem dyadicWeight_add (s t : ℝ) (k : ℕ) :
    dyadicWeight (s + t) k = dyadicWeight s k * dyadicWeight t k := by
  rw [dyadicWeight, mul_add, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]; rfl

/-- `2^((k+j)s) = 2^(ks) 2^(js)`. -/
theorem dyadicWeight_add_nat (s : ℝ) (k j : ℕ) :
    dyadicWeight s (k + j) = dyadicWeight s k * dyadicWeight s j := by
  rw [dyadicWeight, Nat.cast_add, add_mul, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
  rfl

/-- `2^((k+1)s) = 2^s 2^(ks)`. -/
theorem dyadicWeight_succ (s : ℝ) (k : ℕ) :
    dyadicWeight s (k + 1) = 2 ^ s * dyadicWeight s k := by
  rw [dyadicWeight_add_nat, mul_comm]; simp [dyadicWeight]

/-- `2^(-ks) = (2^(ks))⁻¹`. -/
theorem dyadicWeight_neg (s : ℝ) (k : ℕ) : dyadicWeight (-s) k = (dyadicWeight s k)⁻¹ := by
  rw [dyadicWeight, mul_neg, ENNReal.rpow_neg]; rfl

/-- `2^(-ks) 2^(ks) = 1`. -/
theorem dyadicWeight_neg_mul_self (s : ℝ) (k : ℕ) : dyadicWeight (-s) k * dyadicWeight s k = 1 := by
  rw [dyadicWeight_neg, ENNReal.inv_mul_cancel (dyadicWeight_ne_zero s k) (dyadicWeight_ne_top s k)]

/-- `2^(ks) 2^(-ks) = 1`. -/
theorem dyadicWeight_mul_neg_self (s : ℝ) (k : ℕ) : dyadicWeight s k * dyadicWeight (-s) k = 1 := by
  rw [mul_comm, dyadicWeight_neg_mul_self]

/-- **Trading growth for decay**: `2^(ks) 2^(-(k-j)σ) = 2^(-k(σ-s)) 2^(jσ)` for `j ≤ k`, the
identity behind every almost diagonal estimate. -/
theorem dyadicWeight_mul_dyadicWeight_neg_sub (s σ : ℝ) {j k : ℕ} (hjk : j ≤ k) :
    dyadicWeight s k * dyadicWeight (-σ) (k - j) =
      dyadicWeight (-(σ - s)) k * dyadicWeight σ j := by
  simp only [dyadicWeight]
  rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, Nat.cast_sub hjk]
  congr 1
  ring

/-- **Weights inside a window**: for `|j - k| ≤ c`, `2^{js} ≤ 2^{c|s|} 2^{ks}`, since
`s(j - k) ≤ |s| c`. -/
theorem dyadicWeight_le_of_mem_Icc (s : ℝ) {c j k : ℕ} (hk : k ∈ Finset.Icc (j - c) (j + c)) :
    dyadicWeight s j ≤ dyadicWeight |s| c * dyadicWeight s k := by
  rw [Finset.mem_Icc] at hk
  rw [dyadicWeight, dyadicWeight, dyadicWeight,
    ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
  have h1 : (j : ℝ) ≤ k + c := by exact_mod_cast (by omega : j ≤ k + c)
  have h2 : (k : ℝ) ≤ j + c := by exact_mod_cast hk.2
  have hjk : |(j : ℝ) - k| ≤ c := abs_le.2 ⟨by linarith, by linarith⟩
  have h3 : ((j : ℝ) - k) * s ≤ |s| * c := by
    calc ((j : ℝ) - k) * s ≤ |((j : ℝ) - k) * s| := le_abs_self _
      _ = |(j : ℝ) - k| * |s| := abs_mul _ _
      _ ≤ c * |s| := mul_le_mul_of_nonneg_right hjk (abs_nonneg s)
      _ = |s| * c := mul_comm _ _
  linarith [h3]

/-- `(2^(ks))^p = 2^(k s p)`. -/
theorem dyadicWeight_rpow (s p : ℝ) (k : ℕ) : dyadicWeight s k ^ p = dyadicWeight (s * p) k := by
  rw [dyadicWeight, dyadicWeight, ← ENNReal.rpow_mul, mul_assoc]

/-- The dyadic weights are a geometric sequence with ratio `2 ^ s`. -/
theorem dyadicWeight_eq_pow (s : ℝ) (k : ℕ) : dyadicWeight s k = ((2 : ℝ≥0∞) ^ s) ^ k := by
  rw [dyadicWeight, mul_comm, ENNReal.rpow_mul_natCast]

/-- The squared dyadic weight: `(2^(ks))² = (4^k)^s`. -/
theorem dyadicWeight_sq (s : ℝ) (k : ℕ) : dyadicWeight s k ^ 2 = ((4 : ℝ≥0∞) ^ k) ^ s := by
  rw [dyadicWeight, ← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_natCast (4 : ℝ≥0∞) k,
    ← ENNReal.rpow_mul, show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by norm_num, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- For `s ≥ 0` the dyadic weights increase in `k`. -/
theorem dyadicWeight_mono (hs : 0 ≤ s) : Monotone (dyadicWeight s) := fun _ _ hkj =>
  ENNReal.rpow_le_rpow_of_exponent_le one_le_two
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hkj) hs)

/-- For a fixed `k`, the weight `2 ^ (k s)` increases with `s`. -/
theorem dyadicWeight_le_of_le {s t : ℝ} (h : s ≤ t) (k : ℕ) : dyadicWeight s k ≤ dyadicWeight t k :=
  ENNReal.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k))

/-- For `s ≤ 0` the weights decrease. -/
theorem dyadicWeight_anti (hs : s ≤ 0) : Antitone (dyadicWeight s) := fun _ _ hkj =>
  ENNReal.rpow_le_rpow_of_exponent_le one_le_two
    (mul_le_mul_of_nonpos_right (Nat.cast_le.2 hkj) hs)

/-- For `s ≥ 0`, `1 ≤ 2^(ks)`. -/
theorem one_le_dyadicWeight (hs : 0 ≤ s) (k : ℕ) : 1 ≤ dyadicWeight s k := by
  simpa using dyadicWeight_mono hs (Nat.zero_le k)

/-- `2^(-(n-2)θ) ≤ 2^(2θ) 2^(-nθ)` for truncated subtraction and `θ ≥ 0`. -/
theorem dyadicWeight_neg_sub_two_le {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) :
    dyadicWeight (-θ) (n - 2) ≤ dyadicWeight θ 2 * dyadicWeight (-θ) n := by
  rcases le_or_gt 2 n with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left, dyadicWeight_add_nat, ← mul_assoc, dyadicWeight_mul_neg_self,
      one_mul]
  · calc dyadicWeight (-θ) (n - 2) = 1 := by rw [show n - 2 = 0 by omega]; simp
      _ ≤ dyadicWeight θ 2 * dyadicWeight (-θ) n := by
          rw [← dyadicWeight_mul_neg_self θ n]
          gcongr
          · exact dyadicWeight_mono hθ (by omega)

/-- `(2 ^ k) ^ s = 2 ^ (k s)`: the dyadic weight is the power weight at the dyadic point. -/
theorem natCast_two_pow_rpow (s : ℝ) (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ≥0∞) ^ s = dyadicWeight s k := by
  rw [dyadicWeight, ENNReal.rpow_natCast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- `2^((k : ℤ) : ℝ) = 2^k` in `[0, ∞]` for `k ∈ ℕ`: the real power of `2` with an integer
exponent `k ≥ 0` is the natural power. -/
theorem two_rpow_intCast_natCast (k : ℕ) :
    (2 : ℝ≥0∞) ^ (((k : ℤ) : ℝ)) = ((2 ^ k : ℕ) : ℝ≥0∞) := by
  rw [Int.cast_natCast, rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]

/-- `(2^(jn))^t = 2^(j n t)`: a power of the volume factor `2^(jn)` is a dyadic weight. -/
theorem two_pow_rpow_eq_dyadicWeight (j n : ℕ) (t : ℝ) :
    ((2 : ℝ≥0∞) ^ (j * n)) ^ t = dyadicWeight (n * t) j := by
  rw [dyadicWeight, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- **A weighted `ℓ_q` norm from its first term and a bound of the others**: if `x_0 ≤ M a` and
`x_{j+1} ≤ A w_{j+1}` for every `j`, then for `1 ≤ q ≤ ∞`
`‖(2^(js) x_j)_j‖_{ℓ_q} ≤ (M + A) (a + ‖(2^(js) w_j)_j‖_{ℓ_q})`. The first term splits off
(`ENNReal.lqNorm_le_head_add_shift`), and the shifted rest is at most `A ‖(2^(js) w_j)_j‖_{ℓ_q}`. -/
theorem lqNorm_dyadicWeight_le_of_head_of_succ_le {q : ℝ≥0∞} (hq : 1 ≤ q) (s : ℝ)
    (x w : ℕ → ℝ≥0∞) {a M A : ℝ≥0∞} (h0 : x 0 ≤ M * a) (hsucc : ∀ j, x (j + 1) ≤ A * w (j + 1)) :
    lqNorm q (fun j => dyadicWeight s j * x j) ≤
      (M + A) * (a + lqNorm q (fun j => dyadicWeight s j * w j)) := by
  set Λ := lqNorm q (fun j => dyadicWeight s j * w j)
  have htail : lqNorm q (fun j => dyadicWeight s (j + 1) * x (j + 1)) ≤ A * Λ :=
    calc lqNorm q (fun j => dyadicWeight s (j + 1) * x (j + 1))
        ≤ lqNorm q (fun j => A * (dyadicWeight s (j + 1) * w (j + 1))) :=
          lqNorm_mono fun j => (mul_le_mul' le_rfl (hsucc j)).trans_eq (by ring)
      _ = A * lqNorm q (fun j => dyadicWeight s (j + 1) * w (j + 1)) :=
          lqNorm_const_mul _ _
      _ ≤ A * Λ := mul_le_mul' le_rfl (lqNorm_shift_le fun j => dyadicWeight s j * w j)
  calc lqNorm q (fun j => dyadicWeight s j * x j)
      ≤ dyadicWeight s 0 * x 0 + lqNorm q (fun j => dyadicWeight s (j + 1) * x (j + 1)) :=
        lqNorm_le_head_add_shift hq _
    _ ≤ M * a + A * Λ := by
        rw [dyadicWeight_zero_right, one_mul]
        exact add_le_add h0 htail
    _ ≤ (M + A) * a + (M + A) * Λ := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = (M + A) * (a + Λ) := by ring

/-! ### Dyadic weights of integer order -/

/-- For a natural order `L`, the dyadic weight `dyadicWeight L k`, a real power `2^(k·L)` in
`[0, ∞]`, equals the natural power `2^(kL)`. -/
theorem dyadicWeight_natCast (L k : ℕ) : dyadicWeight (L : ℝ) k = 2 ^ (k * L) := by
  rw [dyadicWeight_eq_pow, ENNReal.rpow_natCast, ← pow_mul, mul_comm]

/-- `2^(-kL) = (2^k)^(-L)`. -/
theorem dyadicWeight_neg_natCast (L k : ℕ) :
    dyadicWeight (-(L : ℝ)) k = ((2 : ℝ≥0∞) ^ k)⁻¹ ^ L := by
  rw [ENNReal.dyadicWeight_neg, dyadicWeight_natCast, pow_mul, ENNReal.inv_pow]

/-- For `i ≤ j' ≤ k`, `2^(-(k-i)L) ≤ 2^L 2^(-(j'+1-i)L)`. -/
theorem dyadicWeight_neg_sub_le (L : ℕ) {i j' k : ℕ} (hij : i ≤ j') (hk : j' ≤ k) :
    dyadicWeight (-(L : ℝ)) (k - i) ≤ 2 ^ L * dyadicWeight (-(L : ℝ)) (j' + 1 - i) := by
  have h1 : dyadicWeight (-(L : ℝ)) (k - i) ≤ dyadicWeight (-(L : ℝ)) (j' - i) :=
    ENNReal.dyadicWeight_anti (neg_nonpos.2 (Nat.cast_nonneg L)) (Nat.sub_le_sub_right hk i)
  have h2 : j' + 1 - i = (j' - i) + 1 := by omega
  rw [h2, ENNReal.dyadicWeight_add_nat, dyadicWeight_neg_natCast L 1, pow_one]
  calc dyadicWeight (-(L : ℝ)) (k - i) ≤ dyadicWeight (-(L : ℝ)) (j' - i) := h1
    _ = dyadicWeight (-(L : ℝ)) (j' - i) * (2 ^ L * (2 : ℝ≥0∞)⁻¹ ^ L) := by
        rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]
    _ = _ := by ring

/-- `1 ≤ 2^L 2^(-mL)` for `m ≤ 1`. -/
theorem one_le_two_pow_mul_dyadicWeight_neg (L : ℕ) {m : ℕ} (hm : m ≤ 1) :
    1 ≤ 2 ^ L * dyadicWeight (-(L : ℝ)) m := by
  have h : dyadicWeight (-(L : ℝ)) 1 ≤ dyadicWeight (-(L : ℝ)) m :=
    ENNReal.dyadicWeight_anti (neg_nonpos.2 (Nat.cast_nonneg L)) hm
  calc (1 : ℝ≥0∞) = 2 ^ L * dyadicWeight (-(L : ℝ)) 1 := by
        rw [dyadicWeight_neg_natCast, pow_one, ← mul_pow,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    _ ≤ 2 ^ L * dyadicWeight (-(L : ℝ)) m := by gcongr

/-- `2^(iL) 2^(-j'L) = 4^L 2^(-(j'+2-i)L)` for `i ≤ j' + 2`. -/
theorem dyadicWeight_mul_dyadicWeight_neg_eq (L : ℕ) {i j' : ℕ} (hij : i ≤ j' + 2) :
    dyadicWeight (L : ℝ) i * dyadicWeight (-(L : ℝ)) j' =
      4 ^ L * dyadicWeight (-(L : ℝ)) (j' + 2 - i) := by
  have h1 : dyadicWeight (-(L : ℝ)) (j' + 2 - i) * dyadicWeight (-(L : ℝ)) i =
      dyadicWeight (-(L : ℝ)) j' * dyadicWeight (-(L : ℝ)) 2 := by
    rw [← ENNReal.dyadicWeight_add_nat, ← ENNReal.dyadicWeight_add_nat, Nat.sub_add_cancel hij]
  have h4 : (4 : ℝ≥0∞) ^ L * dyadicWeight (-(L : ℝ)) 2 = 1 := by
    rw [dyadicWeight_neg_natCast, ← mul_pow, show (2 : ℝ≥0∞) ^ 2 = 4 by norm_num,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  calc dyadicWeight (L : ℝ) i * dyadicWeight (-(L : ℝ)) j'
      = dyadicWeight (L : ℝ) i * dyadicWeight (-(L : ℝ)) j' *
          (4 ^ L * dyadicWeight (-(L : ℝ)) 2) := by rw [h4, mul_one]
    _ = 4 ^ L * (dyadicWeight (-(L : ℝ)) j' * dyadicWeight (-(L : ℝ)) 2) *
          dyadicWeight (L : ℝ) i := by ring
    _ = 4 ^ L * (dyadicWeight (-(L : ℝ)) (j' + 2 - i) * dyadicWeight (-(L : ℝ)) i) *
          dyadicWeight (L : ℝ) i := by rw [h1]
    _ = 4 ^ L * dyadicWeight (-(L : ℝ)) (j' + 2 - i) *
          (dyadicWeight (-(L : ℝ)) i * dyadicWeight (L : ℝ) i) := by ring
    _ = _ := by rw [ENNReal.dyadicWeight_neg_mul_self, mul_one]

/-- `(X 2^(-jn))^(1/p) = X^(1/p) 2^(-jn/p)`. -/
theorem rpow_mul_dyadicWeight_neg (X : ℝ≥0∞) (n : ℕ) (p : ℝ≥0∞) (j : ℕ) :
    (X * dyadicWeight (-(n : ℝ)) j) ^ (1 / p.toReal) =
      X ^ (1 / p.toReal) * dyadicWeight (-(n / p.toReal)) j := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one ENNReal.toReal_nonneg),
    ENNReal.dyadicWeight_rpow]
  congr 2
  ring

/-- The product rule for powers of `2` in `[0, ∞]`: `2^x 2^y = 2^(x+y)` for all real `x, y`
(Mathlib's `ENNReal.rpow_add` with the side conditions `2 ≠ 0` and `2 ≠ ∞` discharged). -/
theorem two_rpow_mul_two_rpow (x y : ℝ) : (2 : ℝ≥0∞) ^ x * 2 ^ y = 2 ^ (x + y) :=
  (ENNReal.rpow_add x y two_ne_zero ENNReal.ofNat_ne_top).symm

/-- For `α > 0` the ratio `2 ^ (-α)` of the decaying weights is `< 1`. -/
theorem two_rpow_neg_lt_one {α : ℝ} (hα : 0 < α) : (2 : ℝ≥0∞) ^ (-α) < 1 :=
  ENNReal.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_iff_pos.2 hα)

/-- The constant `(1 - 2 ^ (-α))⁻¹` of geometric sums is finite for `α > 0`. -/
theorem one_sub_two_rpow_neg_inv_ne_top {α : ℝ} (hα : 0 < α) : (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ ≠ ∞ := by
  rw [ENNReal.inv_ne_top]
  exact (tsub_pos_of_lt (two_rpow_neg_lt_one hα)).ne'

/-- The constant `2 (1 - 2^(-s))⁻¹` is finite for `s > 0`
(`ENNReal.one_sub_two_rpow_neg_inv_ne_top`). -/
theorem two_mul_one_sub_two_rpow_neg_inv_ne_top {s : ℝ} (hs : 0 < s) :
    2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofNat_ne_top (one_sub_two_rpow_neg_inv_ne_top hs)

/-- The constant `(1 - 2 ^ (-α))⁻¹` is at least `1`. -/
theorem one_le_one_sub_two_rpow_neg_inv (α : ℝ) : 1 ≤ (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ :=
  ENNReal.one_le_inv.2 tsub_le_self

/-- `‖(2 ^ (-k α))ₖ‖_q ≤ (1 - 2 ^ (-α))⁻¹`. -/
theorem lqNorm_dyadicWeight_neg_le (hq : 1 ≤ q) (α : ℝ) :
    lqNorm q (dyadicWeight (-α)) ≤ (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ := by
  have : dyadicWeight (-α) = fun k => ((2 : ℝ≥0∞) ^ (-α)) ^ k := funext (dyadicWeight_eq_pow _)
  rw [this]
  exact lqNorm_geometric_le hq _

/-- `∑ₖ 2^(-kα) = (1 - 2^(-α))⁻¹`. -/
theorem tsum_dyadicWeight_neg (α : ℝ) :
    ∑' k, dyadicWeight (-α) k = (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ := by
  simp_rw [dyadicWeight_eq_pow]
  exact ENNReal.tsum_geometric _

/-- The constant `(1 - 2^(-α q))^(-1/q)` of the dyadic geometric sequence `(2^(-kα))_k`, with
the value `1` for `q = ∞` (where `q.toReal = 0`).  For `α ≥ 0` and `q ≠ 0` it is the `ℓ_q` norm
of that sequence (`ENNReal.lqNorm_dyadicWeight_neg_eq_dyadicGeomConst`). -/
noncomputable def dyadicGeomConst (α : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  ((1 - (2 : ℝ≥0∞) ^ (-(α * q.toReal)))⁻¹) ^ (1 / q.toReal)

/-- **The geometric sequence in `ℓ_q`** for every `q ≠ 0`:
`‖(2^(-kα))_k‖_{ℓ_q} = dyadicGeomConst α q` for `α ≥ 0`. -/
theorem lqNorm_dyadicWeight_neg_eq_dyadicGeomConst {α : ℝ} (hα : 0 ≤ α) (hq0 : q ≠ 0) :
    lqNorm q (dyadicWeight (-α)) = dyadicGeomConst α q := by
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, dyadicGeomConst, toReal_top, _root_.div_zero, rpow_zero]
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0 (dyadicWeight_zero_right _).ge)
    exact (dyadicWeight_anti (neg_nonpos.2 hα) (Nat.zero_le k)).trans_eq
      (dyadicWeight_zero_right _)
  rw [lqNorm_eq_tsum hq0 hq, dyadicGeomConst]
  simp_rw [dyadicWeight_rpow, neg_mul]
  rw [tsum_dyadicWeight_neg]

/-- The geometric sequence for every `q`: `‖(2^(-kα))_k‖_{ℓ_q} ≤ dyadicGeomConst α q` for
`α ≥ 0`; for `q = 0` the left side is `0`. -/
theorem lqNorm_dyadicWeight_neg_le_dyadicGeomConst {α : ℝ} (hα : 0 ≤ α) :
    lqNorm q (dyadicWeight (-α)) ≤ dyadicGeomConst α q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [lqNorm_zero_left]
  exact (lqNorm_dyadicWeight_neg_eq_dyadicGeomConst hα hq0).le

/-- The constant `dyadicGeomConst α q` is at least `1`, for every `α` and `q`. -/
theorem one_le_dyadicGeomConst (α : ℝ) (q : ℝ≥0∞) : 1 ≤ dyadicGeomConst α q :=
  (one_rpow _).symm.trans_le
    (rpow_le_rpow (one_le_one_sub_two_rpow_neg_inv _) (by positivity))

/-- The constant `dyadicGeomConst α q` is finite for `α > 0`. -/
theorem dyadicGeomConst_ne_top {α : ℝ} (hα : 0 < α) (q : ℝ≥0∞) : dyadicGeomConst α q ≠ ∞ := by
  rcases (ENNReal.toReal_nonneg (a := q)).eq_or_lt with h | h
  · rw [dyadicGeomConst, ← h, _root_.div_zero, rpow_zero]
    exact one_ne_top
  exact rpow_ne_top_of_nonneg (by positivity)
    (one_sub_two_rpow_neg_inv_ne_top (_root_.mul_pos hα h))

/-- For `q = ∞` the constant `dyadicGeomConst α ∞` is `1`, for every `α`. -/
theorem dyadicGeomConst_top (α : ℝ) : dyadicGeomConst α ∞ = 1 := by
  rw [dyadicGeomConst, toReal_top, _root_.div_zero, rpow_zero]

/-- `∑ₖ 2^(-k) = 2`. -/
theorem tsum_dyadicWeight_neg_one : ∑' k, dyadicWeight (-1) k = 2 := by
  simp_rw [dyadicWeight_eq_pow, ENNReal.rpow_neg_one]
  exact ENNReal.tsum_geometric_two

/-- `‖(2^(-k))ₖ‖_q ≤ 2`. -/
theorem lqNorm_dyadicWeight_neg_one_le (hq : 1 ≤ q) : lqNorm q (dyadicWeight (-1)) ≤ 2 := by
  calc lqNorm q (dyadicWeight (-1)) ≤ ∑' k, dyadicWeight (-1) k := lqNorm_le_lqNorm_one hq _
    _ = 2 := tsum_dyadicWeight_neg_one

/-! ### Powers of two as dyadic weights -/

/-- `ofReal (2^x) = 2^x`: the real power of two as an element of `[0, ∞]`. -/
theorem ofReal_two_rpow (x : ℝ) : ENNReal.ofReal ((2 : ℝ) ^ x) = (2 : ℝ≥0∞) ^ x := by
  rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- `2^k` as a dyadic weight. -/
theorem ofReal_two_pow_eq (k : ℕ) : ENNReal.ofReal (2 ^ k) = dyadicWeight 1 k := by
  rw [← ENNReal.natCast_two_pow_rpow, ENNReal.rpow_one, ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]
  push_cast
  rfl

/-- `(2^i)^n = 2^(in)` as a dyadic weight. -/
theorem ofReal_two_pow_pow (i n : ℕ) :
    ENNReal.ofReal (((2 : ℝ) ^ i) ^ n) = dyadicWeight n i := by
  rw [ENNReal.dyadicWeight_eq_pow, ENNReal.rpow_natCast, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← pow_mul, ← pow_mul, mul_comm]

/-- `(2^(-k))^l = 2^(-kl)` as a dyadic weight. -/
theorem ofReal_one_div_two_pow_pow (k l : ℕ) :
    ENNReal.ofReal ((1 / 2 ^ k) ^ l) = dyadicWeight (-(l : ℝ)) k := by
  have h : (1 / 2 ^ k : ℝ) ^ l = ((2 : ℝ) ^ (-(l : ℝ))) ^ k := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow, inv_pow, ← pow_mul,
      ← pow_mul, mul_comm]
  rw [ENNReal.dyadicWeight_eq_pow, h, ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_rpow_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- `(2^j h)^θ ≤ 2^(-(k-j)θ)` for `0 ≤ h ≤ 2^(-k)`, `j ≤ k` and `θ ≥ 0`. -/
theorem ofReal_two_pow_mul_rpow_le {j k : ℕ} (hjk : j ≤ k) {h : ℝ} (hh : h ≤ 1 / 2 ^ k) {θ : ℝ}
    (hθ : 0 ≤ θ) : ENNReal.ofReal (2 ^ j * h) ^ θ ≤ dyadicWeight (-θ) (k - j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left]
  have h1 : (2 : ℝ) ^ j * h ≤ ((2 : ℝ) ^ m)⁻¹ := by
    rw [pow_add] at hh
    calc (2 : ℝ) ^ j * h ≤ 2 ^ j * (1 / (2 ^ j * 2 ^ m)) := by gcongr
      _ = ((2 : ℝ) ^ m)⁻¹ := by field_simp
  calc ENNReal.ofReal (2 ^ j * h) ^ θ ≤ ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) ^ θ :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) hθ
    _ = dyadicWeight (-θ) m := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, ENNReal.inv_rpow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          dyadicWeight, mul_neg, ENNReal.rpow_neg]

/-- `(ρ 2^(-j))^b = ρ^b 2^(-jb)` in `[0, ∞]` for `ρ > 0` and every real `b`. -/
theorem ofReal_div_two_pow_rpow {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) (j : ℕ) :
    ENNReal.ofReal (ρ / 2 ^ j) ^ b = ENNReal.ofReal ρ ^ b * dyadicWeight (-b) j := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul hρ.le,
    ENNReal.mul_rpow_of_ne_zero (ENNReal.ofReal_pos.2 hρ).ne' (by positivity),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat, ENNReal.inv_rpow, ENNReal.dyadicWeight_neg,
    ← ENNReal.natCast_two_pow_rpow]
  norm_cast

/-- `(2^j ρ)^b = ρ^b 2^(jb)` in `[0, ∞]` for `ρ > 0` and every real `b`. -/
theorem ofReal_two_pow_mul_rpow {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) (j : ℕ) :
    ENNReal.ofReal (2 ^ j * ρ) ^ b = ENNReal.ofReal ρ ^ b * dyadicWeight b j := by
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.mul_rpow_of_ne_zero (by positivity) (ENNReal.ofReal_pos.2 hρ).ne', mul_comm,
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← ENNReal.natCast_two_pow_rpow]
  norm_cast

/-- **Dyadic scales as dyadic weights**: `(2^(-n))^θ = 2^(-nθ)` for every `n ∈ ℕ` and every real
exponent `θ`, as an identity in `[0, ∞]` (`ENNReal.dyadicWeight`); the case `ρ = 1` of
`ENNReal.ofReal_div_two_pow_rpow`. -/
theorem ofReal_one_div_two_pow_rpow (n : ℕ) (θ : ℝ) :
    ENNReal.ofReal ((1 / 2 ^ n) ^ θ) = dyadicWeight (-θ) n := by
  rw [← ENNReal.ofReal_rpow_of_pos (by positivity), ofReal_div_two_pow_rpow one_pos,
    ENNReal.ofReal_one, ENNReal.one_rpow, one_mul]

/-! ### Subadditive functionals and series -/

/-- **Subadditive functionals and multiple series**: if `Q` is subadditive, `Q a ≤ C ‖a‖` with
`C < ∞`, and the partial sums of `∑ u_k` over finite sets `S_J` converge to `F`, then
`Q F ≤ ∑_k Q(u_k)`. -/
theorem le_tsum_of_tendsto_finsetSum {E ι : Type*} [NormedAddCommGroup E] {Q : E → ℝ≥0∞}
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hadd : ∀ a b, Q (a + b) ≤ Q a + Q b) (hle : ∀ a, Q a ≤ C * ‖a‖ₑ)
    {S : ℕ → Finset ι} {u : ι → E} {F : E}
    (hu : Tendsto (fun J => ∑ k ∈ S J, u k) atTop (nhds F)) :
    Q F ≤ ∑' k, Q (u k) := by
  have hsum : ∀ s : Finset ι, Q (∑ k ∈ s, u k) ≤ ∑ k ∈ s, Q (u k) := fun s =>
    Finset.le_sum_of_subadditive Q (by simpa using hle 0) hadd s u
  have hJ : ∀ J, Q F ≤ ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ := fun J => by
    calc Q F = Q (∑ k ∈ S J, u k + (F - ∑ k ∈ S J, u k)) := by rw [add_sub_cancel]
      _ ≤ Q (∑ k ∈ S J, u k) + Q (F - ∑ k ∈ S J, u k) := hadd _ _
      _ ≤ ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ :=
          add_le_add ((hsum _).trans (sum_le_tsum _)) (hle _)
  have h1 : Tendsto (fun J => F - ∑ k ∈ S J, u k) atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := F)).sub hu
    rwa [sub_self] at this
  have h2 : Tendsto (fun J => ‖F - ∑ k ∈ S J, u k‖ₑ) atTop (nhds 0) := by
    have h3 := (continuous_eNorm.tendsto (0 : E)).comp h1
    rw [eNorm_zero] at h3
    exact h3
  have hlim : Tendsto (fun J => ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ) atTop
      (nhds (∑' k, Q (u k) + C * 0)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul h2 (Or.inr hC))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hJ)

/-- **Subadditive functionals and series**: if `Q` is subadditive, `Q a ≤ C ‖a‖` with `C < ∞`, and
the partial sums of `∑ u_j` converge to `f`, then `Q f ≤ ∑_j Q(u_j)`. -/
theorem le_tsum_of_tendsto_sum {E : Type*} [NormedAddCommGroup E] {Q : E → ℝ≥0∞} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hadd : ∀ a b, Q (a + b) ≤ Q a + Q b) (hle : ∀ a, Q a ≤ C * ‖a‖ₑ)
    {u : ℕ → E} {f : E}
    (hu : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), u j) atTop (nhds f)) :
    Q f ≤ ∑' j, Q (u j) :=
  le_tsum_of_tendsto_finsetSum (S := fun J => Finset.range (J + 1)) hC hadd hle hu

/-- **Weighted sequences are summable**: `∑_j a_j ≤ (1 - 2^(-s))⁻¹ ‖(2^(js) a_j)_j‖_{ℓ_q}`,
since `a_j ≤ 2^(-js) ‖(2^(js) a_j)_j‖_{ℓ_q}`. -/
theorem tsum_le_lqNorm_dyadicWeight {q : ℝ≥0∞} (hq : 1 ≤ q) (s : ℝ) (a : ℕ → ℝ≥0∞) :
    ∑' j, a j ≤ (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun j => dyadicWeight s j * a j) := by
  set X := lqNorm q (fun j => dyadicWeight s j * a j)
  calc ∑' j, a j ≤ ∑' j, dyadicWeight (-s) j * X := tsum_le_tsum fun j => by
        calc a j = dyadicWeight (-s) j * (dyadicWeight s j * a j) := by
              rw [← mul_assoc, dyadicWeight_neg_mul_self, one_mul]
          _ ≤ dyadicWeight (-s) j * X := mul_le_mul' le_rfl
              (le_lqNorm (zero_lt_one.trans_le hq).ne' (fun j => dyadicWeight s j * a j) j)
    _ = (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
        rw [ENNReal.tsum_mul_right, tsum_dyadicWeight_neg]

/-- **A series with weighted bounds**: if the partial sums of `∑ u_j` converge to `F` and
`‖u_j‖ ≤ K b_j`, then `‖F‖ ≤ K (1 - 2^(-s))⁻¹ ‖(2^(js) b_j)_j‖_{ℓ_q}`
(`ENNReal.tsum_le_lqNorm_dyadicWeight`). -/
theorem enorm_le_of_tendsto_sum {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {F : E}
    (hu : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), u j) atTop (nhds F)) {K : ℝ≥0∞}
    {b : ℕ → ℝ≥0∞} (hb : ∀ j, ‖u j‖ₑ ≤ K * b j) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ‖F‖ₑ ≤ K * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun j => dyadicWeight s j * b j) := by
  have h1 : ‖F‖ₑ ≤ ∑' j, ‖u j‖ₑ :=
    le_tsum_of_tendsto_sum (C := 1) ENNReal.one_ne_top (fun x y => eNorm_add_le x y)
      (fun x => by rw [one_mul]) hu
  calc ‖F‖ₑ ≤ ∑' j, K * b j := h1.trans (tsum_le_tsum hb)
    _ = K * ∑' j, b j := ENNReal.tsum_mul_left
    _ ≤ K * ((1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun j => dyadicWeight s j * b j)) :=
        mul_le_mul' le_rfl (tsum_le_lqNorm_dyadicWeight hq s b)
    _ = _ := (mul_assoc _ _ _).symm

/-! ### Tails and partial sums -/

/-- `∑_K [j ≤ K] g K = ∑_i g (j + i)`. -/
theorem tsum_ite_le_eq (j : ℕ) (g : ℕ → ℝ≥0∞) :
    ∑' K, (if j ≤ K then g K else 0) = ∑' i, g (j + i) := by
  rw [← CompleteLattice.summable.sum_add_tsum_nat_add' (k := j)]
  have h0 : ∑ K ∈ Finset.range j, (if j ≤ K then g K else 0) = 0 :=
    Finset.sum_eq_zero fun K hK => by simp [not_le.2 (Finset.mem_range.1 hK)]
  rw [h0, zero_add]
  congr 1; funext i
  simp only [Nat.le_add_left j i, ↓reduceIte]
  rw [add_comm]

/-- `∑_K [K ≤ j] g K = ∑_{K ≤ j} g K`. -/
theorem tsum_ite_ge_eq (j : ℕ) (g : ℕ → ℝ≥0∞) :
    ∑' K, (if K ≤ j then g K else 0) = ∑ K ∈ Finset.range (j + 1), g K := by
  rw [tsum_eq_sum (s := Finset.range (j + 1)) fun K hK => by
    simp [not_le.2 (by simpa using hK : j < K)]]
  exact Finset.sum_congr rfl fun K hK => by
    simp [Nat.lt_succ_iff.1 (Finset.mem_range.1 hK)]

/-- **The `ℓ_q` norm of a tail is the norm of the shifted sequence**: for `0 < q < ∞`,
`‖(0, …, 0, a_N, a_{N+1}, …)‖_{ℓ_q} = ‖(a_{N+k})_k‖_{ℓ_q}` (`ENNReal.tsum_ite_le_eq`). -/
theorem lqNorm_ite_le_eq {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ℕ → ℝ≥0∞) (N : ℕ) :
    lqNorm q (fun j => if N ≤ j then a j else 0) = lqNorm q (fun k => a (N + k)) := by
  have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq, ← tsum_ite_le_eq N (fun n => a n ^ q.toReal)]
  congr 1
  refine tsum_congr fun j => ?_
  split_ifs <;> simp [ENNReal.zero_rpow_of_pos hpos]

/-! ### Products of sums -/

/-- `a x + b y ≤ (a + b)(x + y)` in `[0, ∞]`. -/
theorem mul_add_mul_le_add_mul_add (a b x y : ℝ≥0∞) :
    a * x + b * y ≤ (a + b) * (x + y) := by
  rw [add_mul, mul_add, mul_add]
  exact add_le_add le_self_add le_add_self

/-- `∑_{i ∈ s} a_i b_i ≤ (∑_{i ∈ s} a_i)(∑_{i ∈ s} b_i)` for every finite set `s` and all families
`a, b` in `[0, ∞]`: each `b_i` is at most `∑_{j ∈ s} b_j` (Mathlib's `Finset.single_le_sum`,
`Finset.sum_mul`). -/
theorem sum_mul_le_sum_mul_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ≥0∞) :
    ∑ i ∈ s, a i * b i ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, b i := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_right (Finset.single_le_sum
    (fun j _ => zero_le) hi) _

/-- `x_0 + ∑_{j<k} x_j ≤ 2 ∑_{j≤k} x_j` for every sequence `x` in `[0, ∞]`: both summands are at
most `∑_{j≤k} x_j` (Mathlib's `Finset.single_le_sum`, `Finset.sum_le_sum_of_subset`). -/
theorem add_sum_range_le_two_mul_sum (x : ℕ → ℝ≥0∞) (k : ℕ) :
    x 0 + ∑ j ∈ Finset.range k, x j ≤ 2 * ∑ j ∈ Finset.range (k + 1), x j := by
  rw [two_mul]
  exact add_le_add (Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_range.2 k.succ_pos))
    (Finset.sum_le_sum_of_subset (Finset.range_mono k.le_succ))

/-- **Dividing by a smaller power**: if `w ≤ c v` with `0 < c < ∞` and `a ≥ 0`, then
`u / v^a ≤ c^a (u / w^a)` in `[0, ∞]`. -/
theorem div_rpow_le_rpow_mul_div_rpow {u v w c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hw : w ≤ c * v) {a : ℝ} (ha : 0 ≤ a) : u / v ^ a ≤ c ^ a * (u / w ^ a) := by
  have hca0 : c ^ a ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) hct).ne'
  have hcat : c ^ a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha hct
  calc u / v ^ a = c ^ a * u / (c ^ a * v ^ a) := (ENNReal.mul_div_mul_left _ _ hca0 hcat).symm
    _ ≤ c ^ a * u / w ^ a := ENNReal.div_le_div_left (by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ ha]
        exact ENNReal.rpow_le_rpow hw ha) _
    _ = c ^ a * (u / w ^ a) := mul_div_assoc _ _ _

/-- `a Y + b X + c X ≤ (a + b + c) (X + Y)` in `[0, ∞]`. -/
theorem mul_add_mul_add_mul_le (a b c X Y : ℝ≥0∞) :
    a * Y + b * X + c * X ≤ (a + b + c) * (X + Y) :=
  calc a * Y + b * X + c * X ≤ a * (X + Y) + b * (X + Y) + c * (X + Y) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl le_add_self) (mul_le_mul' le_rfl le_self_add))
          (mul_le_mul' le_rfl le_self_add)
    _ = (a + b + c) * (X + Y) := by ring

/-! ### Quotients and powers -/

/-- `a (x + (b/a) t y) = a x + t (b y)` for `0 < a < ∞`: the rescaled decomposition term of the
K-functional under a map. -/
theorem mul_add_div_mul_mul {a b : ℝ≥0∞} (ha0 : a ≠ 0) (ha : a ≠ ∞) (t x y : ℝ≥0∞) :
    a * (x + b / a * t * y) = a * x + t * (b * y) := by
  have h : a * (b / a) = b := ENNReal.mul_div_cancel ha0 ha
  calc a * (x + b / a * t * y) = a * x + a * (b / a) * t * y := by ring
    _ = a * x + t * (b * y) := by rw [h]; ring

/-- `a (b/a)^θ = a^(1-θ) b^θ` for `0 < a < ∞` and every `b ∈ [0, ∞]`.  For `b = ∞` the power
rule for products holds since both factors `∞` and `a⁻¹` are nonzero
(`ENNReal.mul_rpow_of_ne_zero`). -/
theorem mul_div_rpow_eq {a b : ℝ≥0∞} (ha0 : a ≠ 0) (ha : a ≠ ∞) (θ : ℝ) :
    a * (b / a) ^ θ = a ^ (1 - θ) * b ^ θ := by
  have h : (b * a⁻¹) ^ θ = b ^ θ * a⁻¹ ^ θ := by
    rcases eq_or_ne b ∞ with rfl | hb
    · exact ENNReal.mul_rpow_of_ne_zero ENNReal.top_ne_zero (ENNReal.inv_ne_zero.2 ha) θ
    · exact ENNReal.mul_rpow_of_ne_top hb (ENNReal.inv_ne_top.2 ha0) θ
  rw [div_eq_mul_inv, h, ENNReal.inv_rpow, ← ENNReal.rpow_neg, sub_eq_add_neg,
    ENNReal.rpow_add _ _ ha0 ha, ENNReal.rpow_one]
  ring

/-- The constant `a^(1-θ) b^θ` is finite for `0 < a, b < ∞`. -/
theorem rpow_mul_rpow_ne_top {a b : ℝ≥0∞} (ha0 : a ≠ 0) (ha : a ≠ ∞) (hb0 : b ≠ 0) (hb : b ≠ ∞)
    (θ : ℝ) : a ^ (1 - θ) * b ^ θ ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero ha0 ha) (ENNReal.rpow_ne_top_of_ne_zero hb0 hb)

/-! ### The constant of the quasi-triangle inequality -/

/-- Mathlib's constant `LpAddConst q` of the quasi-triangle inequality is at least `1`: it is `1`
outside `(0, 1)` and `2^(1/q - 1)` with `1/q - 1 > 0` inside. -/
theorem one_le_LpAddConst (q : ℝ≥0∞) : 1 ≤ LpAddConst q := by
  rw [LpAddConst]
  split_ifs with h
  · refine one_le_two_rpow ?_
    rw [one_div, sub_nonneg, ← ENNReal.toReal_inv, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simpa using h.1.ne') (ENNReal.one_le_inv.2 h.2.le)
  · exact le_rfl

/-- **`2^(1/q)` and the constant of the quasi-triangle inequality**: `2^(1/q) ≤ 2 C_q` for every
`q`, with Mathlib's constant `C_q = LpAddConst q` (and `1/0 = 1/∞ = 0` for the real value of
`q`). For `0 < q < 1` both sides are equal, since `C_q = 2^(1/q - 1)`; otherwise `C_q = 1` and
the left side is at most `2`. -/
theorem two_rpow_one_div_le_two_mul_LpAddConst (q : ℝ≥0∞) :
    (2 : ℝ≥0∞) ^ (1 / q.toReal) ≤ 2 * LpAddConst q := by
  by_cases h : q ∈ Set.Ioo 0 1
  · rw [LpAddConst, ite_eq_left h]
    refine le_of_eq ?_
    calc (2 : ℝ≥0∞) ^ (1 / q.toReal) = 2 ^ (1 : ℝ) * 2 ^ (1 / q.toReal - 1) := by
          rw [two_rpow_mul_two_rpow, add_sub_cancel]
      _ = 2 * 2 ^ (1 / q.toReal - 1) := by rw [rpow_one]
  rw [LpAddConst, ite_eq_right h, mul_one]
  calc (2 : ℝ≥0∞) ^ (1 / q.toReal) ≤ 2 ^ (1 : ℝ) := by
        refine rpow_le_rpow_of_exponent_le one_le_two ?_
        rcases eq_or_ne q 0 with rfl | hq0
        · simp
        rcases eq_or_ne q ∞ with rfl | hq
        · simp
        have hq1 : 1 ≤ q := not_lt.1 fun h1 => h ⟨pos_iff_ne_zero.2 hq0, h1⟩
        exact div_le_one_of_le₀ (one_le_toReal_of_one_le hq1 hq) toReal_nonneg
    _ = 2 := rpow_one 2

/-- **The `ℓ_q` sum of two numbers**: `(x^q + y^q)^(1/q) ≤ C_q (x + y)` for `0 < q < ∞` and all
`x, y ∈ [0, ∞]`, with Mathlib's constant `C_q = LpAddConst q` (Mathlib's
`ENNReal.rpow_add_le_mul_rpow_add_rpow''` for `x^q` and `y^q`). -/
theorem rpow_add_rpow_le_LpAddConst_mul {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) (x y : ℝ≥0∞) :
    (x ^ q.toReal + y ^ q.toReal) ^ (1 / q.toReal) ≤ LpAddConst q * (x + y) := by
  have hp : q.toReal ≠ 0 := (ENNReal.toReal_pos hq0 hq).ne'
  have h := rpow_add_le_mul_rpow_add_rpow'' (x ^ q.toReal) (y ^ q.toReal) (p := q)
  rwa [rpow_rpow_inv hp, rpow_rpow_inv hp, ← one_div] at h

end ENNReal

/-- **Parseval's identity in `ℝ≥0∞`**: `‖x‖² = ∑_i ‖x_i‖²` for every `x ∈ ℓ²`, the series of
squares in `[0, ∞]`, from Mathlib's `lp.norm_rpow_eq_tsum` at `p = 2`. Through the coefficient
map of a Hilbert basis it computes `‖f‖²` as the sum of the squared coefficients. -/
theorem lp.enorm_sq_eq_tsum {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (x : lp E 2) : ‖x‖ₑ ^ 2 = ∑' i, ‖x i‖ₑ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      ((lp.memℓp x).summable (by norm_num) |>.congr fun i => by simp)]
  congr 1; funext i
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- `(1 + t)^N ≤ 2^N (1 + t^N)` for `t ≥ 0`, from Mathlib's `add_pow_le`. -/
theorem one_add_pow_le_two_pow_mul {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  calc (1 + t) ^ N ≤ 2 ^ (N - 1) * (1 ^ N + t ^ N) := add_pow_le zero_le_one ht N
    _ ≤ 2 ^ N * (1 + t ^ N) := by
      rw [one_pow]
      gcongr
      · exact one_le_two
      · exact Nat.sub_le N 1

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### `L_p` norms of functions with values in `[0, ∞]` -/

/-- **Powers inside an `L_p` norm**: `‖g^r‖_p = ‖g‖_{p r}^r` for `r > 0` and `g : α → [0, ∞]`
measurable (Mathlib's `eLpNorm_eNorm_rpow`). -/
theorem eLpNorm_fun_rpow {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) {r : ℝ} (hr : 0 < r)
    (p : ℝ≥0∞) : eLpNorm (fun x => g x ^ r) p μ = eLpNorm g (p * ENNReal.ofReal r) μ ^ r := by
  simpa only [eNorm_eq_self] using eLpNorm_eNorm_rpow (p := p) (μ := μ) g hg.aestronglyMeasurable hr

/-- **The `p`-th power of the `L_p` quasi-norm is subadditive for `0 < p ≤ 1`**:
`‖f + g‖_p^p ≤ ‖f‖_p^p + ‖g‖_p^p` on any measure space, for all functions `f`, `g` with values in
an additive monoid with an extended seminorm and continuous addition, such as a normed group or
`[0, ∞]`. This is Mathlib's triangle inequality `inhmgELpNorm_add_le` for
`∫ ‖f‖^p = ‖f‖_p^p` (`inhmgELpNorm_eq_eLpNorm_pow`); the `L_p` quasi-norm itself satisfies only
`‖f + g‖_p ≤ 2^(1/p - 1) (‖f‖_p + ‖g‖_p)` (`eLpNorm_add_le'`). -/
theorem eLpNorm_add_rpow_le_of_le_one {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    [ContinuousAdd ε] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp1 : p ≤ 1) (f g : α → ε) :
    eLpNorm (f + g) p μ ^ p.toReal ≤ eLpNorm f p μ ^ p.toReal + eLpNorm g p μ ^ p.toReal := by
  rw [← inhmgELpNorm_eq_eLpNorm_pow hp1 hp0, ← inhmgELpNorm_eq_eLpNorm_pow hp1 hp0,
    ← inhmgELpNorm_eq_eLpNorm_pow hp1 hp0]
  exact inhmgELpNorm_add_le

/-- **Monotone convergence for `L_p` norms**: for a directed countable family of measurable
functions `F_b : α → [0, ∞]`, `‖sup_b F_b‖_p = sup_b ‖F_b‖_p`. For `p < ∞` this is the monotone
convergence theorem for `∫ F_b^p`; for `p = ∞` it holds for every countable family. -/
theorem eLpNorm_iSup_of_directed {β : Type*} [Countable β] {F : β → α → ℝ≥0∞}
    (hF : ∀ b, AEMeasurable (F b) μ) (hd : Directed (· ≤ ·) F) (p : ℝ≥0∞) :
    eLpNorm (fun x => ⨆ b, F b x) p μ = ⨆ b, eLpNorm (F b) p μ := by
  have hm : AEMeasurable (fun x => ⨆ b, F b x) μ := AEMeasurable.iSup hF
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm_exponent_zero hm.aestronglyMeasurable,
      eLpNorm_exponent_zero (hF _).aestronglyMeasurable]
  rcases eq_or_ne p ∞ with rfl | hp
  · simp only [eLpNorm_exponent_top hm.aestronglyMeasurable,
      eLpNorm_exponent_top (hF _).aestronglyMeasurable, eLpNormEssSup, eNorm_eq_self]
    refine le_antisymm (essSup_le_of_ae_le _ ?_) (iSup_le fun b => essSup_mono_ae ?_)
    · have h : ∀ᵐ x ∂μ, ∀ b, F b x ≤ essSup (F b) μ :=
        ae_all_iff.2 fun b => ENNReal.ae_le_essSup (F b)
      filter_upwards [h] with x hx
      exact iSup_le fun b => (hx b).trans (le_iSup (fun b => essSup (F b) μ) b)
    · exact Eventually.of_forall fun x => le_iSup (fun b => F b x) b
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hm.aestronglyMeasurable]
  simp_rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (hF _).aestronglyMeasurable]
  simp only [eNorm_eq_self]
  have h1 : ∀ x, (⨆ b, F b x) ^ p.toReal = ⨆ b, F b x ^ p.toReal := fun x =>
    (ENNReal.orderIsoRpow p.toReal hr).map_iSup (fun b => F b x)
  simp_rw [h1]
  rw [lintegral_iSup_directed (fun b => (hF b).pow_const _) ?_]
  · exact (ENNReal.orderIsoRpow (1 / p.toReal) (by positivity)).map_iSup _
  · intro b₁ b₂
    obtain ⟨c, h₁, h₂⟩ := hd b₁ b₂
    exact ⟨c, fun x => ENNReal.rpow_le_rpow (h₁ x) hr.le,
      fun x => ENNReal.rpow_le_rpow (h₂ x) hr.le⟩

/-- **Minkowski's inequality for series** in `L_p`, `1 ≤ p ≤ ∞`, on any measure space: for
`g_i : α → [0, ∞]` indexed by a countable set, `‖∑_i g_i‖_p ≤ ∑_i ‖g_i‖_p`. If some `g_i` is not
measurable, then `‖g_i‖_p = ∞` and so is the right side. Otherwise the series is the supremum of
its finite partial sums, and this follows from Mathlib's finite version `eLpNorm_sum_le` by
monotone convergence (`MeasureTheory.eLpNorm_iSup_of_directed`). -/
theorem eLpNorm_tsum_le {ι : Type*} [Countable ι] {g : ι → α → ℝ≥0∞} {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    eLpNorm (fun x => ∑' i, g i x) p μ ≤ ∑' i, eLpNorm (g i) p μ := by
  by_cases hg : ∀ i, AEMeasurable (g i) μ
  swap
  · obtain ⟨i, hi⟩ := not_forall.1 hg
    have h : eLpNorm (g i) p μ = ∞ :=
      eLpNorm_of_not_aestronglyMeasurable fun h => hi h.aemeasurable
    rw [tsum_eq_top_of_eq_top ⟨i, h⟩]
    exact le_top
  have h : (fun x => ∑' i, g i x) = fun x => ⨆ s : Finset ι, ∑ i ∈ s, g i x := by
    funext x
    exact tsum_eq_iSup_sum
  have hmono : Monotone fun (s : Finset ι) (x : α) => ∑ i ∈ s, g i x := fun s t hst x =>
    Finset.sum_le_sum_of_subset hst
  rw [h, eLpNorm_iSup_of_directed (fun s => Finset.aemeasurable_fun_sum s fun i _ => hg i)
    hmono.directed_le p]
  refine iSup_le fun s => ?_
  calc eLpNorm (fun x => ∑ i ∈ s, g i x) p μ = eLpNorm (∑ i ∈ s, g i) p μ := by
        congr 1
        funext x
        simp [Finset.sum_apply]
    _ ≤ ∑ i ∈ s, eLpNorm (g i) p μ := eLpNorm_sum_le hp1
    _ ≤ ∑' i, eLpNorm (g i) p μ := sum_le_tsum s

/-! ### Powers of bounded functions -/

/-- **Powers of a bounded function**: if `u ≤ c` almost everywhere, then
`∫ u^r ≤ c^(r-1) ∫ u` for every `r ≥ 1` and every almost everywhere measurable `u : α → [0, ∞]`,
since `u^r = u · u^(r-1) ≤ u · c^(r-1)`. -/
theorem lintegral_rpow_le_mul_lintegral_of_ae_le {u : α → ℝ≥0∞} {c : ℝ≥0∞} {r : ℝ} (hr : 1 ≤ r)
    (hu : AEMeasurable u μ) (h : ∀ᵐ x ∂μ, u x ≤ c) :
    ∫⁻ x, u x ^ r ∂μ ≤ c ^ (r - 1) * ∫⁻ x, u x ∂μ :=
  calc ∫⁻ x, u x ^ r ∂μ ≤ ∫⁻ x, u x * c ^ (r - 1) ∂μ :=
        lintegral_mono_ae (h.mono fun x hx => by
          rw [ENNReal.rpow_eq_mul_rpow_sub_one _ hr]
          exact mul_le_mul_right (ENNReal.rpow_le_rpow hx (by linarith)) _)
    _ = (∫⁻ x, u x ∂μ) * c ^ (r - 1) := lintegral_mul_const'' _ hu
    _ = c ^ (r - 1) * ∫⁻ x, u x ∂μ := mul_comm _ _

/-- If `u ≤ c` almost everywhere, then `∫ u² ≤ c ∫ u`, for every almost everywhere measurable
`u : α → [0, ∞]`: the case `r = 2` of
`MeasureTheory.lintegral_rpow_le_mul_lintegral_of_ae_le`. -/
theorem lintegral_sq_le_mul_lintegral_of_ae_le {u : α → ℝ≥0∞} {c : ℝ≥0∞} (hu : AEMeasurable u μ)
    (h : ∀ᵐ x ∂μ, u x ≤ c) : ∫⁻ x, u x ^ 2 ∂μ ≤ c * ∫⁻ x, u x ∂μ := by
  have h2 := lintegral_rpow_le_mul_lintegral_of_ae_le one_le_two hu h
  norm_num [ENNReal.rpow_two] at h2
  exact h2

/-! ### `L_q` norms of functions that are bounded on pieces -/

section Pieces

open Function Set

variable {ι : Type*} [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
  {S : ι → Set α} {c : ℝ≥0∞} {G : α → ℝ≥0∞} {a : ι → ℝ≥0∞} {q : ℝ≥0∞}

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- **Integral of a function bounded on pieces**: if almost every point lies in one of the
disjoint measurable sets `S n`, each of measure `c`, and `G ≤ a n` on `S n`, then
`∫ G dμ ≤ c ∑_n a n`. -/
theorem lintegral_le_of_le_on_pieces (hS : ∀ n, MeasurableSet (S n))
    (hd : Pairwise (Disjoint on S)) (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ n, S n) (hμ : ∀ n, μ (S n) = c)
    (h : ∀ n, ∀ x ∈ S n, G x ≤ a n) : ∫⁻ x, G x ∂μ ≤ c * ∑' n, a n := by
  calc ∫⁻ x, G x ∂μ = ∫⁻ x in ⋃ n, S n, G x ∂μ := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ = ∑' n, ∫⁻ x in S n, G x ∂μ := lintegral_iUnion hS hd G
    _ ≤ ∑' n, ∫⁻ _ in S n, a n ∂μ := tsum_le_tsum fun n =>
        lintegral_mono_ae ((ae_restrict_iff' (hS n)).2 (Filter.Eventually.of_forall (h n)))
    _ = c * ∑' n, a n := by
        simp_rw [setLIntegral_const, hμ]
        rw [ENNReal.tsum_mul_right, mul_comm]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- **Integral of a function bounded below on pieces**: if the measurable sets `S n` are
disjoint, each of measure `c`, and `a n ≤ G` on `S n`, then `c ∑_n a n ≤ ∫ G dμ`. -/
theorem le_lintegral_of_le_on_pieces (hS : ∀ n, MeasurableSet (S n))
    (hd : Pairwise (Disjoint on S)) (hμ : ∀ n, μ (S n) = c)
    (h : ∀ n, ∀ x ∈ S n, a n ≤ G x) : c * ∑' n, a n ≤ ∫⁻ x, G x ∂μ := by
  calc c * ∑' n, a n = ∑' n, ∫⁻ _ in S n, a n ∂μ := by
        simp_rw [setLIntegral_const, hμ]
        rw [ENNReal.tsum_mul_right, mul_comm]
    _ ≤ ∑' n, ∫⁻ x in S n, G x ∂μ := tsum_le_tsum fun n =>
        lintegral_mono_ae ((ae_restrict_iff' (hS n)).2 (Filter.Eventually.of_forall (h n)))
    _ = ∫⁻ x in ⋃ n, S n, G x ∂μ := (lintegral_iUnion hS hd G).symm
    _ ≤ ∫⁻ x, G x ∂μ := setLIntegral_le_lintegral _ _

/-- **`L_q` norm of a function bounded on pieces**: if almost every point lies in one of the
disjoint measurable sets `S n`, each of measure `c`, and `G ≤ a n` on `S n`, then
`‖G‖_{L_q(μ)} ≤ c^(1/q) ‖a‖_{ℓ_q}` for every `q` (with `c^(1/q) = 1` for `q = ∞`).  `G` is
measurable, since `eLpNorm` is `∞` otherwise. -/
theorem eLpNorm_le_of_le_on_pieces (hG : AEStronglyMeasurable G μ)
    (hS : ∀ n, MeasurableSet (S n)) (hd : Pairwise (Disjoint on S))
    (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ n, S n) (hμ : ∀ n, μ (S n) = c) (h : ∀ n, ∀ x ∈ S n, G x ≤ a n) :
    eLpNorm G q μ ≤ c ^ (1 / q.toReal) * ENNReal.lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [eLpNorm_exponent_zero hG]
    exact zero_le
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [eLpNorm_exponent_top hG, ENNReal.lqNorm_top, ENNReal.toReal_top, div_zero,
      ENNReal.rpow_zero, one_mul]
    refine essSup_le_of_ae_le _ (hcov.mono fun x hx => ?_)
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    simpa only [eNorm_eq_self] using (h n x hn).trans (le_iSup a n)
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq hG, ENNReal.lqNorm_eq_tsum hq0 hq,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  gcongr
  refine lintegral_le_of_le_on_pieces hS hd hcov hμ fun n x hx => ?_
  simp only [eNorm_eq_self]
  exact ENNReal.rpow_le_rpow (h n x hx) hp.le

/-- **`L_q` norm of a function bounded below on pieces**: if the measurable sets `S n` are
disjoint, each of measure `c ≠ 0`, and `a n ≤ G` on `S n`, then
`c^(1/q) ‖a‖_{ℓ_q} ≤ ‖G‖_{L_q(μ)}` for every `q` (with `c^(1/q) = 1` for `q = ∞`). -/
theorem le_eLpNorm_of_le_on_pieces (hS : ∀ n, MeasurableSet (S n))
    (hd : Pairwise (Disjoint on S)) (hμ : ∀ n, μ (S n) = c) (hc : c ≠ 0)
    (h : ∀ n, ∀ x ∈ S n, a n ≤ G x) :
    c ^ (1 / q.toReal) * ENNReal.lqNorm q a ≤ eLpNorm G q μ := by
  by_cases hG : AEStronglyMeasurable G μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hG]
    exact le_top
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [ENNReal.lqNorm_zero_left]
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [eLpNorm_exponent_top hG, ENNReal.lqNorm_top, ENNReal.toReal_top, div_zero,
      ENNReal.rpow_zero, one_mul]
    refine iSup_le fun n => ?_
    by_contra hlt
    push Not at hlt
    have hae : ∀ᵐ x ∂μ, ‖G x‖ₑ < a n := ae_lt_of_essSup_lt hlt
    have hsub : S n ⊆ {x | ¬ ‖G x‖ₑ < a n} := fun x hx => by
      simp only [mem_ofPred_eq, eNorm_eq_self, not_lt]
      exact h n x hx
    exact hc ((hμ n).symm.trans (measure_mono_null hsub (ae_iff.1 hae)))
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq hG, ENNReal.lqNorm_eq_tsum hq0 hq,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  gcongr
  refine le_lintegral_of_le_on_pieces hS hd hμ fun n x hx => ?_
  simp only [eNorm_eq_self]
  exact ENNReal.rpow_le_rpow (h n x hx) hp.le

end Pieces

end MeasureTheory
