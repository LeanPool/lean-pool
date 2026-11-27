/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.ContinuousSpectralBasis
public import LeanPool.FunctionSpaces.Analysis.Lp.Interpolation

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The local Weyl bound, the Nikolskii inequality and continuity

A continuous spectral basis `(e_i)` on `M` (`ContinuousSpectralBasis`), with continuous basis
functions `eTilde_i`, satisfies the **local Weyl bound** of dimension `D` with constant `C`
(`ContinuousSpectralBasis.LocalWeylBound`) if

`∑_{λ(i) < n} |eTilde_i(x)|² ≤ C n^D`   for every `x ∈ M` and `n ≥ 1`.

For the Laplace–Beltrami operator of a compact Riemannian manifold of dimension `d` this is
Hörmander's local Weyl law with `D = d`; on the torus `𝕋^d` it is the count of at most `(2n)^d`
frequencies of degree `< n` (`Torus.localWeylBound_fourierEigenbasis`).

* **The Nikolskii inequality from `L_2` to `L_∞`**
  (`ContinuousSpectralBasis.norm_sq_le_of_localWeyl`): for `a` in the span of the basis
  functions of level `< n`, `‖a‖_∞² ≤ C n^D ‖a‖_2²`, by the Cauchy–Schwarz inequality in
  `a(x) = ∑_i c_i eTilde_i(x)` and Parseval's identity `‖a‖_2² = ∑_i |c_i|²`.
* **The Nikolskii inequality for `1 ≤ p ≤ 2`**
  (`ContinuousSpectralBasis.norm_rpow_le_of_localWeyl`): `‖a‖_∞^p ≤ C n^D ‖a‖_p^p`, since
  `‖a‖_2² ≤ ‖a‖_∞^(2-p) ‖a‖_p^p`. For `p > 2` the inequality with `n^(D/p)` does not follow this
  way: the proof on the torus raises trigonometric polynomials of degree `< n` to the power `m`,
  which have degree `< mn`; for a general basis, products of functions of `basisSpan n` need not lie
  in any `basisSpan m`. The embedding theorems of `FunctionSpaces.MeasureSpaces.Besov.Embeddings`
  apply to the scheme of the basis functions under the hypothesis `FunctionScheme.HasNikolskii`.
* **Continuity of `H^s` for `s > D/2`**
  (`ContinuousSpectralBasis.exists_continuous_of_localWeyl`): every `f ∈ L_2(μ)` with
  `∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞` has a bounded continuous representative. The partial
  sums `S_n f = ∑_{λ(i) < n} ⟨e_i, f⟩ eTilde_i` are continuous
  (`ContinuousSpectralBasis.partialSum`), and on the dyadic levels the Nikolskii inequality and
  the truncation error `‖f - P_n f‖_2 ≤ n^(-s) ‖c‖` give
  `‖S_{2^(k+1)} f - S_{2^k} f‖_∞ ≤ C^(1/2) 2^(D/2) ‖c‖ (2^(D/2 - s))^k`, a geometric series; the
  uniform limit represents `f`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction InnerProductSpace lp

/-- `(2^k)^t = (2^t)^k` for real `t` (Mathlib's `Real.rpow_pow_comm`). -/
theorem Real.natCast_two_pow_rpow (t : ℝ) (k : ℕ) : ((2 ^ k : ℕ) : ℝ) ^ t = ((2 : ℝ) ^ t) ^ k := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  exact (Real.rpow_pow_comm zero_le_two t k).symm

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

namespace ContinuousSpectralBasis

variable {ι : Type*} {μ : Measure M} [IsFiniteMeasure μ] (B : ContinuousSpectralBasis ι μ)

/-- The finite set of the indices of level `< n`. -/
noncomputable def levelSet (n : ℕ) : Finset ι := (B.finite_level n).toFinset

/-- `i` lies in the level set `< n` iff `λ(i) < n`. -/
@[simp]
theorem mem_levelSet {n : ℕ} {i : ι} : i ∈ B.levelSet n ↔ B.level i < n := by
  simp [levelSet]

/-- The **local Weyl bound** of dimension `D` with constant `C ≥ 0`:
`∑_{λ(i) < n} |eTilde_i(x)|² ≤ C n^D` for every point `x` and every `n ≥ 1`. A hypothesis on the
basis; the torus satisfies it (`Torus.localWeylBound_fourierEigenbasis`). -/
structure LocalWeylBound (D C : ℝ) : Prop where
  /-- The constant is nonnegative. -/
  nonneg : 0 ≤ C
  /-- `∑_{λ(i) < n} |eTilde_i(x)|² ≤ C n^D` for every `n ≥ 1` and every `x`. -/
  le : ∀ n : ℕ, 1 ≤ n → ∀ x : M, ∑ i ∈ B.levelSet n, ‖B.basisFun i x‖ ^ 2 ≤ C * (n : ℝ) ^ D

/-- An element of the span of level `< n` is a combination `∑_{λ(i) < n} c_i eTilde_i`. -/
theorem exists_sum_of_mem_basisSpan {n : ℕ} {a : M →ᵇ ℂ} (ha : a ∈ B.basisSpan n) :
    ∃ c : ι → ℂ, a = ∑ i ∈ B.levelSet n, c i • B.basisFun i := by
  classical
  obtain ⟨t, ht, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun ℂ).1 ha
  have hsub : t ⊆ B.levelSet n := fun i hi => B.mem_levelSet.2 (ht hi)
  refine ⟨fun i => if hi : i ∈ t then c ⟨i, hi⟩ else 0, ?_⟩
  calc a = ∑ i ∈ t, (if hi : i ∈ t then c ⟨i, hi⟩ else 0) • B.basisFun i := by
        rw [← hc, ← Finset.sum_coe_sort t]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp
    _ = _ := Finset.sum_subset hsub fun i _ hi => by simp [hi]

/-- **Parseval's identity for combinations of the basis functions**:
`‖∑ c_i eTilde_i‖_2² = ∑ |c_i|²` (Mathlib's `OrthogonalFamily.norm_sum` for the orthonormal
basis). -/
theorem norm_toLp_sum_sq (t : Finset ι) (c : ι → ℂ) :
    ‖BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (∑ i ∈ t, c i • B.basisFun i)‖ ^ 2 =
      ∑ i ∈ t, ‖c i‖ ^ 2 := by
  have hsum : BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (∑ i ∈ t, c i • B.basisFun i) =
      ∑ i ∈ t, c i • B.basis i := by
    rw [map_sum]; simp_rw [map_smul, B.toLp_basisFun]
  rw [hsum]
  exact B.basis.orthonormal.orthogonalFamily.norm_sum c t

variable {B}

/-- **The Nikolskii inequality from `L_2` to `L_∞`** under the local Weyl bound: for `a` in the
span of level `< n`, `n ≥ 1`, `‖a‖_∞² ≤ C n^D ‖a‖_2²`. -/
theorem norm_sq_le_of_localWeyl {D C : ℝ} (hW : B.LocalWeylBound D C) {n : ℕ} (hn : 1 ≤ n)
    {a : M →ᵇ ℂ} (ha : a ∈ B.basisSpan n) :
    ‖a‖ ^ 2 ≤ C * (n : ℝ) ^ D * ‖BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ a‖ ^ 2 := by
  obtain ⟨c, rfl⟩ := B.exists_sum_of_mem_basisSpan ha
  rw [B.norm_toLp_sum_sq]
  set t := B.levelSet n
  set N := ∑ i ∈ t, ‖c i‖ ^ 2
  have hK : 0 ≤ C * (n : ℝ) ^ D := mul_nonneg hW.nonneg (by positivity)
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => by positivity
  have hpt : ∀ x, ‖(∑ i ∈ t, c i • B.basisFun i) x‖ ≤ Real.sqrt (C * (n : ℝ) ^ D * N) :=
    fun x => by
      rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
      calc ‖(∑ i ∈ t, c i • B.basisFun i) x‖ ^ 2 = ‖∑ i ∈ t, c i * B.basisFun i x‖ ^ 2 := by
            simp
        _ ≤ (∑ i ∈ t, ‖c i‖ * ‖B.basisFun i x‖) ^ 2 := by
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_mul _ _).le)
        _ ≤ N * ∑ i ∈ t, ‖B.basisFun i x‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq t _ _
        _ ≤ N * (C * (n : ℝ) ^ D) := by gcongr; exact hW.le n hn x
        _ = C * (n : ℝ) ^ D * N := by ring
  have hsup := (BoundedContinuousFunction.norm_le (Real.sqrt_nonneg _)).2 hpt
  calc ‖∑ i ∈ t, c i • B.basisFun i‖ ^ 2 ≤ Real.sqrt (C * (n : ℝ) ^ D * N) ^ 2 := by gcongr
    _ = C * (n : ℝ) ^ D * N := Real.sq_sqrt (by positivity)

/-- The Nikolskii inequality from `L_2` to `L_∞`, unsquared:
`‖a‖_∞ ≤ (C n^D)^(1/2) ‖a‖_2`. -/
theorem norm_le_sqrt_mul_of_localWeyl {D C : ℝ} (hW : B.LocalWeylBound D C) {n : ℕ}
    (hn : 1 ≤ n) {a : M →ᵇ ℂ} (ha : a ∈ B.basisSpan n) :
    ‖a‖ ≤ Real.sqrt (C * (n : ℝ) ^ D) * ‖BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ a‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ a)),
    ← Real.sqrt_mul (mul_nonneg hW.nonneg (by positivity))]
  exact Real.le_sqrt_of_sq_le (norm_sq_le_of_localWeyl hW hn ha)

/-- **The Nikolskii inequality for `1 ≤ p ≤ 2`** under the local Weyl bound: for `a` in the span
of level `< n`, `n ≥ 1`, `‖a‖_∞^p ≤ C n^D ‖a‖_p^p`. The case `p = 2` gives
`‖a‖_∞² ≤ C n^D ‖a‖_2²`, and `‖a‖_2² ≤ ‖a‖_∞^(2-p) ‖a‖_p^p`
(`MeasureTheory.toReal_eLpNorm_le_rpow_mul`). -/
theorem norm_rpow_le_of_localWeyl {D C : ℝ} (hW : B.LocalWeylBound D C) {n : ℕ} (hn : 1 ≤ n)
    {a : M →ᵇ ℂ} (ha : a ∈ B.basisSpan n) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖a‖ ^ p.toReal ≤ C * (n : ℝ) ^ D * (eLpNorm a p μ).toReal ^ p.toReal := by
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top (by norm_num) hp2
  set P := p.toReal
  have hP1 : 1 ≤ P := ENNReal.one_le_toReal_of_one_le hp hp'
  have hP2 : P ≤ 2 := by
    have h := ENNReal.toReal_mono (by norm_num) hp2
    simpa using h
  set K := C * (n : ℝ) ^ D
  have hK : 0 ≤ K := mul_nonneg hW.nonneg (by positivity)
  set N := (eLpNorm a p μ).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  set X := (eLpNorm a 2 μ).toReal
  -- interpolation between `L_p` and `L_∞` at the exponent `2`
  have hint := toReal_eLpNorm_le_rpow_mul (μ := μ) a.continuous.aestronglyMeasurable
    (norm_nonneg a) (Eventually.of_forall a.norm_coe_le_norm)
    (zero_lt_one.trans_le hp).ne' hp2 (by norm_num)
  simp only [ENNReal.toReal_ofNat] at hint
  have hX : X ^ (2 : ℝ) ≤ ‖a‖ ^ (2 - P) * N ^ P := by
    calc X ^ (2 : ℝ) ≤ (‖a‖ ^ (1 - P / 2) * N ^ (P / 2)) ^ (2 : ℝ) :=
          Real.rpow_le_rpow ENNReal.toReal_nonneg hint (by norm_num)
      _ = ‖a‖ ^ (2 - P) * N ^ P := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (norm_nonneg _),
            ← Real.rpow_mul hN]
          congr 2 <;> ring
  have hchain : ‖a‖ ^ (2 : ℝ) ≤ K * (‖a‖ ^ (2 - P) * N ^ P) := by
    have h2 := norm_sq_le_of_localWeyl hW hn ha
    rw [BoundedContinuousFunction.norm_toLp_eq_toReal_eLpNorm] at h2
    calc ‖a‖ ^ (2 : ℝ) = ‖a‖ ^ 2 := Real.rpow_two _
      _ ≤ K * X ^ 2 := h2
      _ = K * X ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ ≤ K * (‖a‖ ^ (2 - P) * N ^ P) := by gcongr
  rcases (norm_nonneg a).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith)]
    exact mul_nonneg hK (Real.rpow_nonneg hN _)
  have hsplit : ‖a‖ ^ (2 : ℝ) = ‖a‖ ^ (2 - P) * ‖a‖ ^ P := by
    rw [← Real.rpow_add hpos, sub_add_cancel]
  rw [hsplit, mul_left_comm] at hchain
  exact le_of_mul_le_mul_left hchain (Real.rpow_pos_of_pos hpos _)

/-- **The Nikolskii inequality for `1 ≤ p ≤ 2`**, unpowered:
`‖a‖_∞ ≤ C^(1/p) n^(D/p) ‖a‖_p`. -/
theorem norm_le_of_localWeyl {D C : ℝ} (hW : B.LocalWeylBound D C) {n : ℕ} (hn : 1 ≤ n)
    {a : M →ᵇ ℂ} (ha : a ∈ B.basisSpan n) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖a‖ ≤ C ^ p.toReal⁻¹ * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal := by
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top (by norm_num) hp2
  set P := p.toReal
  have hP0 : 0 < P := zero_lt_one.trans_le (ENNReal.one_le_toReal_of_one_le hp hp')
  set N := (eLpNorm a p μ).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hC := hW.nonneg
  have h := norm_rpow_le_of_localWeyl hW hn ha hp hp2
  calc ‖a‖ = (‖a‖ ^ P) ^ P⁻¹ := (Real.rpow_rpow_inv (norm_nonneg a) hP0.ne').symm
    _ ≤ (C * (n : ℝ) ^ D * N ^ P) ^ P⁻¹ := Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = C ^ P⁻¹ * (n : ℝ) ^ (D * P⁻¹) * N := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_rpow_inv hN hP0.ne',
          Real.mul_rpow hC (by positivity), ← Real.rpow_mul (by positivity)]

/-! ### Continuity of `H^s` for `s > D/2` -/

variable (B)

/-- The **partial sum** `S_n f = ∑_{λ(i) < n} ⟨e_i, f⟩ eTilde_i`, a bounded continuous function. -/
noncomputable def partialSum (n : ℕ) (f : Lp ℂ 2 μ) : M →ᵇ ℂ :=
  ∑ i ∈ B.levelSet n, B.basis.repr f i • B.basisFun i

/-- The partial sum lies in the span of level `< n`. -/
theorem partialSum_mem_basisSpan (n : ℕ) (f : Lp ℂ 2 μ) : B.partialSum n f ∈ B.basisSpan n :=
  Submodule.sum_mem _ fun _ hi =>
    Submodule.smul_mem _ _ (B.basisFun_mem_basisSpan (B.mem_levelSet.1 hi))

/-- The `L_2` class of the partial sum is the truncation `P_n f`. -/
theorem toLp_partialSum (n : ℕ) (f : Lp ℂ 2 μ) :
    BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (B.partialSum n f) = B.truncate n f := by
  rw [partialSum, map_sum]
  simp_rw [map_smul, B.toLp_basisFun]
  rfl

/-- For `m ≤ n`, `‖P_n f - P_m f‖_2 ≤ ‖f - P_m f‖_2`: the difference keeps the coefficients of
the levels in `[m, n)`. -/
theorem norm_truncate_sub_truncate_le {m n : ℕ} (hmn : m ≤ n) (f : Lp ℂ 2 μ) :
    ‖B.truncate n f - B.truncate m f‖ ≤ ‖f - B.truncate m f‖ := by
  have hsub : B.truncate n f - B.truncate m f = B.truncate n (f - B.truncate m f) := by
    rw [sub_eq_add_neg f, B.truncate_add, ← neg_one_smul ℂ (B.truncate m f), B.truncate_smul,
      B.truncate_of_mem (B.span_mono hmn (B.truncate_mem_span m f)), neg_one_smul,
      ← sub_eq_add_neg]
  rw [hsub]
  exact B.norm_truncate_le n _

variable {B}

/-- **The dyadic steps of the partial sums** of a Sobolev element `f = J_s c` under the local
Weyl bound: `‖S_{2^(k+1)} f - S_{2^k} f‖_∞ ≤ C^(1/2) 2^(D/2) ‖c‖ (2^(D/2 - s))^k`. -/
theorem norm_partialSum_succ_sub_le {D C : ℝ} (hW : B.LocalWeylBound D C) {s : ℝ} (hs : 0 ≤ s)
    (c : ℓ²(ι, ℂ)) (k : ℕ) :
    ‖B.partialSum (2 ^ (k + 1)) (B.sobolevEmbed s hs c) -
        B.partialSum (2 ^ k) (B.sobolevEmbed s hs c)‖ ≤
      Real.sqrt C * (2 : ℝ) ^ (D / 2) * ‖c‖ * ((2 : ℝ) ^ (D / 2 - s)) ^ k := by
  set f := B.sobolevEmbed s hs c
  have hC := hW.nonneg
  have hmem : B.partialSum (2 ^ (k + 1)) f - B.partialSum (2 ^ k) f ∈ B.basisSpan (2 ^ (k + 1)) :=
    Submodule.sub_mem _ (B.partialSum_mem_basisSpan _ f)
      (B.basisSpan_mono (Nat.pow_le_pow_right two_pos (Nat.le_succ k))
        (B.partialSum_mem_basisSpan _ f))
  have hL2 : ‖BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ
      (B.partialSum (2 ^ (k + 1)) f - B.partialSum (2 ^ k) f)‖ ≤
        ((2 ^ k : ℕ) : ℝ) ^ (-s) * ‖c‖ := by
    rw [map_sub, B.toLp_partialSum, B.toLp_partialSum]
    exact (B.norm_truncate_sub_truncate_le
      (Nat.pow_le_pow_right two_pos (Nat.le_succ k)) f).trans
      (B.norm_sub_truncate_le s hs (Nat.one_le_two_pow) c)
  have h2 : (0 : ℝ) < 2 := two_pos
  calc _ ≤ Real.sqrt (C * ((2 ^ (k + 1) : ℕ) : ℝ) ^ D) * (((2 ^ k : ℕ) : ℝ) ^ (-s) * ‖c‖) :=
        (norm_le_sqrt_mul_of_localWeyl hW Nat.one_le_two_pow hmem).trans
          (mul_le_mul_of_nonneg_left hL2 (Real.sqrt_nonneg _))
    _ = Real.sqrt C * (2 : ℝ) ^ (D / 2) * ‖c‖ * ((2 : ℝ) ^ (D / 2 - s)) ^ k := by
        have hsq : ((2 : ℝ) ^ (D / 2)) ^ 2 = (2 : ℝ) ^ D := by
          rw [sq, ← Real.rpow_add two_pos]; congr 1; ring
        have ha : Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) ^ D) = ((2 : ℝ) ^ (D / 2)) ^ (k + 1) := by
          rw [show ((2 ^ (k + 1) : ℕ) : ℝ) ^ D = (((2 : ℝ) ^ (D / 2)) ^ (k + 1)) ^ 2 by
              rw [Real.natCast_two_pow_rpow, ← pow_mul, mul_comm, pow_mul, hsq],
            Real.sqrt_sq (by positivity)]
        have hd : (2 : ℝ) ^ (D / 2 - s) = (2 : ℝ) ^ (D / 2) * (2 : ℝ) ^ (-s) := by
          rw [← Real.rpow_add two_pos, ← sub_eq_add_neg]
        rw [Real.sqrt_mul hC, ha, Real.natCast_two_pow_rpow, hd, mul_pow]
        ring

/-- **Sobolev elements of order `s > D/2` are continuous** under the local Weyl bound of
dimension `D`: every `f ∈ L_2(μ)` with `∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞` is the `L_2` class
of a bounded continuous function, the uniform limit of the partial sums `S_{2^k} f`. -/
theorem exists_continuous_of_localWeyl {D C : ℝ} (hW : B.LocalWeylBound D C) {s : ℝ}
    (hs : 0 < s) (hsD : D < 2 * s) {f : Lp ℂ 2 μ}
    (hf : Memℓp (fun i => ((((1 + B.level i : ℕ) : ℝ) ^ s : ℝ) : ℂ) * B.basis.repr f i) 2) :
    ∃ g : M →ᵇ ℂ, BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ g = f := by
  obtain ⟨c, rfl⟩ := (B.mem_range_sobolevEmbed_iff s hs.le f).2 hf
  set f := B.sobolevEmbed s hs.le c
  set u : ℕ → M →ᵇ ℂ := fun k => B.partialSum (2 ^ k) f
  have hr : (2 : ℝ) ^ (D / 2 - s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric _ (Real.sqrt C * (2 : ℝ) ^ (D / 2) * ‖c‖) hr fun k => ?_
    rw [dist_comm, dist_eq_norm]
    exact norm_partialSum_succ_sub_le hW hs.le c k
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨g, tendsto_nhds_unique
    ((BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ).continuous.tendsto g |>.comp hg) ?_⟩
  -- the truncations `P_{2^k} f` converge to `f`
  have hlim : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ) ^ (-s) * ‖c‖) atTop (𝓝 0) := by
    simp_rw [Real.natCast_two_pow_rpow]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hs))).mul_const ‖c‖
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
  change ‖BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (B.partialSum (2 ^ k) f) - f‖ ≤ _
  rw [B.toLp_partialSum, norm_sub_rev]
  exact B.norm_sub_truncate_le s hs.le Nat.one_le_two_pow c

end ContinuousSpectralBasis
