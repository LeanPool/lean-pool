/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Atomic decompositions of Triebel–Lizorkin spaces

Coefficients `λ_{j,m}` of the dyadic cells `P_{j,m}` define the step functions
`x ↦ |λ_{j,m}|` for `x ∈ P_{j,m}` (`Rd.cellCoefFun`), and the sequence space `f^s_{p,q}` takes
the `ℓ_q` norm of their weighted values at each point, then the `L_p` norm:
`‖λ‖_{f^s_{p,q}} = ‖ x ↦ ‖(2^(js) |λ_{j,m_j(x)}|)_j‖_{ℓ_q} ‖_p` (`Rd.tlCoeffNorm`), where
`P_{j,m_j(x)}` is the cell of level `j` containing `x`. The atoms are the smooth atoms
`Rd.IsSmoothAtom` of order `L`, normalised in `L_∞`.

**Atomic characterisation** (`Rd.memTriebelLizorkin_iff_atomic`): for `1 < p < ∞`,
`1 < q ≤ ∞` and `0 < s < L`, `F ∈ F^s_{p,q}` iff `F = ∑_j ∑_m λ_{j,m} a_{j,m}` with smooth atoms
of order `L` centred at the cells and `‖λ‖_{f^s_{p,q}} < ∞`. No moment conditions are needed.

* **Synthesis** (`Rd.LocalMeansBump.tlLocalMeansNorm_le_tlCoeffNorm`). A local mean `k_i` of the
  atoms of level `j ≥ i` is bounded by the coefficients of the nearby cells; for `j < i` the
  moments of `k_i` and the smoothness of the atoms give the factor `2^(-(i-j)L)`. Both bounds
  are maximal functions of the step functions of the coefficients
  (`Rd.LocalMeansBump.ae_enorm_conv_kernel_level_le`), and the almost diagonal estimate and the
  Fefferman–Stein inequality finish. The **coarse local means** are those of levels `i ≤ j`, at
  most the level `j` of the atoms, and the **fine local means** those of levels `i > j`.
* **Analysis** (`Rd.LocalMeansBump.tl_atomic_decomposition`,
  `Rd.LocalMeansBump.tlCoeffNorm_cellCoef_le`). The atoms of `F` are the cell atoms of
  `η_j ⋆ (k_j ⋆ F)` with the coefficients `2^(jn) ∫_{P_{j,m}} |k_j ⋆ F|`, and each coefficient is
  at most a multiple of `M(k_j ⋆ F)` at every point of its cell
  (`Rd.cellCoefFun_le_maximal`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Set
open scoped ENNReal Topology

open ENNReal (lqNorm dyadicWeight)

namespace ENNReal

/-- **A series against bounds supported on some indices**: if `u_m ≤ B 1_{P(m)}` for every index
`m`, then `∑_m c_m u_m ≤ B ∑_{m : P(m)} c_m`, for every family `c_m ∈ [0, ∞]`. -/
theorem tsum_mul_le_of_le {ι : Type*} {c u : ι → ℝ≥0∞} {B : ℝ≥0∞} {P : ι → Prop}
    [DecidablePred P] (h : ∀ m, u m ≤ B * if P m then 1 else 0) :
    ∑' m, c m * u m ≤ B * ∑' m, if P m then c m else 0 := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun m => (mul_le_mul_right (h m) _).trans_eq ?_
  split_ifs <;> ring

end ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The sequence space `f^s_{p,q}` -/

/-- The **step function of the coefficients** of level `j`: at `x` the modulus `|λ_{j,m}|` of
the coefficient of the cell `P_{j,m}` of level `j` that contains `x`. -/
noncomputable def cellCoefFun (j : ℕ) (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ) (x : V) :
    ℝ≥0∞ :=
  ‖coef j (cellIndex j x)‖ₑ

omit [MeasurableSpace V] [BorelSpace V] in
/-- On the cell `P_{j,m}` the step function of the coefficients is `|λ_{j,m}|`. -/
theorem cellCoefFun_of_mem {j : ℕ} {m : Fin (finrank ℝ V) → ℤ} {x : V} (hx : x ∈ cell j m)
    (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ) : cellCoefFun j coef x = ‖coef j m‖ₑ := by
  rw [cellCoefFun, show cellIndex j x = m from hx]

/-- The step function of the coefficients is measurable: it factors through the measurable cell
index, which takes values in a countable set. -/
theorem measurable_cellCoefFun (j : ℕ) (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ) :
    Measurable (cellCoefFun (V := V) j coef) :=
  (measurable_of_countable fun m => ‖coef j m‖ₑ).comp (measurable_cellIndex j)

/-- The **quasi-norm of the sequence space `f^s_{p,q}`**:
`‖λ‖_{f^s_{p,q}} = ‖ x ↦ ‖(2^(js) |λ_{j,m_j(x)}|)_j‖_{ℓ_q} ‖_p`, where `P_{j,m_j(x)}` is the cell
of level `j` containing `x`: the `ℓ_q` norm at each point, then the `L_p` norm. -/
noncomputable def tlCoeffNorm (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞)
    (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun x : V => lqNorm q (fun j => dyadicWeight s j * cellCoefFun j coef x)) p volume

/-- The pointwise `ℓ_q` norm of the weighted step functions of the coefficients is
measurable. -/
theorem aemeasurable_lqNorm_cellCoefFun (s : ℝ) (q : ℝ≥0∞)
    (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ) :
    AEMeasurable (fun x : V => lqNorm q (fun j => dyadicWeight s j * cellCoefFun j coef x))
      volume :=
  aemeasurable_lqNorm_comp
    (fun j => ((measurable_cellCoefFun j coef).const_mul _).aemeasurable) q

/-! ### Coefficients and the maximal function -/

/-- **Integrals over dyadic balls by the maximal function**:
`2^(jn) ∫_{B(x, ρ 2^(-j))} g ≤ ρ^n |B_1| M g(x)` for `ρ > 0` and every `g : V → [0, ∞]`. -/
theorem dyadicWeight_mul_setLIntegral_ball_le {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) (g : V → ℝ≥0∞)
    (x : V) :
    dyadicWeight (finrank ℝ V : ℝ) j * ∫⁻ y in ball x (ρ / 2 ^ j), g y ≤
      ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1) * maximal g x := by
  calc dyadicWeight (finrank ℝ V : ℝ) j * ∫⁻ y in ball x (ρ / 2 ^ j), g y
      ≤ dyadicWeight (finrank ℝ V : ℝ) j *
          (volume (ball (0 : V) (ρ / 2 ^ j)) * maximal g x) := by
        gcongr
        exact setLIntegral_ball_le_mul_maximal (by positivity) g x
    _ = ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1) * maximal g x *
          (dyadicWeight (-(finrank ℝ V : ℝ)) j * dyadicWeight (finrank ℝ V : ℝ) j) := by
        rw [volume_ball_div_two_pow hρ j 0]
        ring
    _ = _ := by rw [ENNReal.dyadicWeight_neg_mul_self, mul_one]

/-- **Coefficients below the maximal function**: if `|λ_{j,m}| ≤ 2^(jn) ∫_{P_{j,m}} g` for every
cell of level `j`, then at every point `x` the coefficient of the cell containing `x` is at most
`(2n + 1)^n |B_1| M g(x)`, since that cell lies in `B(x, (2n + 1) 2^(-j))`. -/
theorem cellCoefFun_le_maximal {j : ℕ} {coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ}
    {g : V → ℝ≥0∞}
    (hcoef : ∀ m, ‖coef j m‖ₑ ≤ dyadicWeight (finrank ℝ V : ℝ) j * ∫⁻ y in cell j m, g y)
    (x : V) :
    cellCoefFun j coef x ≤ ENNReal.ofReal ((2 * finrank ℝ V + 1) ^ finrank ℝ V) *
      volume (ball (0 : V) 1) * maximal g x := by
  have hsub : cell j (cellIndex j x) ⊆ ball x ((2 * finrank ℝ V + 1) / 2 ^ j) := fun y hy => by
    have h1 := norm_sub_cellCenter_le hy
    have h2 := norm_sub_cellCenter_le (mem_cell_cellIndex j x)
    rw [mem_ball, dist_eq_norm]
    calc ‖y - x‖ ≤ ‖y - cellCenter j (cellIndex j x)‖ + ‖x - cellCenter j (cellIndex j x)‖ := by
          simpa only [dist_eq_norm] using dist_triangle_right y x (cellCenter j (cellIndex j x))
      _ ≤ finrank ℝ V / 2 ^ j + finrank ℝ V / 2 ^ j := add_le_add h1 h2
      _ < (2 * finrank ℝ V + 1) / 2 ^ j := by
          rw [← add_div, div_lt_div_iff_of_pos_right (by positivity)]
          linarith
  calc cellCoefFun j coef x = ‖coef j (cellIndex j x)‖ₑ := rfl
    _ ≤ dyadicWeight (finrank ℝ V : ℝ) j * ∫⁻ y in cell j (cellIndex j x), g y := hcoef _
    _ ≤ dyadicWeight (finrank ℝ V : ℝ) j *
          ∫⁻ y in ball x ((2 * finrank ℝ V + 1) / 2 ^ j), g y := by
        gcongr
    _ ≤ _ := dyadicWeight_mul_setLIntegral_ball_le (by positivity) j g x

/-- **A coefficient below the maximal function of the step function**: if `x` lies within
`ρ 2^(-j)` of the centre of `P_{j,m}`, then `|λ_{j,m}| ≤ (2(ρ + 1))^n M(x)`, with `M` the maximal
function of the step function of the coefficients of level `j`: the ball
`B(c_{j,m}, 2^(-j)/2)` lies in `P_{j,m}` and in `B(x, (ρ + 1) 2^(-j))`. -/
theorem enorm_coef_le_maximal_cellCoefFun {j : ℕ} (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ)
    {m : Fin (finrank ℝ V) → ℤ} {ρ : ℝ} {x : V} (hx : ‖x - cellCenter j m‖ ≤ ρ / 2 ^ j) :
    ‖coef j m‖ₑ ≤ ENNReal.ofReal ((2 * (ρ + 1)) ^ finrank ℝ V) *
      maximal (cellCoefFun j coef) x := by
  have hρ : 0 ≤ ρ := by
    have h := (norm_nonneg _).trans hx
    rwa [le_div_iff₀ (by positivity), zero_mul] at h
  have hr : (0 : ℝ) < 1 / 2 / 2 ^ j := by positivity
  have hsub : ball (cellCenter j m) (1 / 2 / 2 ^ j) ⊆ cell j m := by
    have h := ball_subset_zcell (V := V) (j : ℤ) m
    rwa [zcell_natCast, zcellCenter_natCast, zpow_natCast] at h
  have hball : ball (cellCenter j m) (1 / 2 / 2 ^ j) ⊆
      ball x (2 * (ρ + 1) * (1 / 2 / 2 ^ j)) := fun y hy => by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have h1 : 2 * (ρ + 1) * (1 / 2 / 2 ^ j) = ρ / 2 ^ j + 1 / 2 ^ j := by ring
    have h2 : (1 : ℝ) / 2 / 2 ^ j = (1 / 2 ^ j) / 2 := by ring
    have h3 : (0 : ℝ) < 1 / 2 ^ j := by positivity
    calc ‖y - x‖ ≤ ‖y - cellCenter j m‖ + ‖x - cellCenter j m‖ := by
          simpa only [dist_eq_norm] using dist_triangle_right y x (cellCenter j m)
      _ < 2 * (ρ + 1) * (1 / 2 / 2 ^ j) := by rw [h1]; linarith
  have hc : 0 < 2 * (ρ + 1) := by positivity
  refine (ENNReal.mul_le_mul_iff_left (volume_ball_ne_zero (V := V) hr)
    (volume_ball_ne_top _)).1 ?_
  calc ‖coef j m‖ₑ * volume (ball (0 : V) (1 / 2 / 2 ^ j))
      = ∫⁻ y in ball (cellCenter j m) (1 / 2 / 2 ^ j), cellCoefFun j coef y := by
        rw [setLIntegral_congr_fun measurableSet_ball fun y hy => cellCoefFun_of_mem (hsub hy) coef,
          setLIntegral_const, Measure.addHaar_ball_center volume (cellCenter j m)]
    _ ≤ ∫⁻ y in ball x (2 * (ρ + 1) * (1 / 2 / 2 ^ j)), cellCoefFun j coef y :=
        lintegral_mono_set hball
    _ ≤ volume (ball (0 : V) (2 * (ρ + 1) * (1 / 2 / 2 ^ j))) * maximal (cellCoefFun j coef) x :=
        setLIntegral_ball_le_mul_maximal (by positivity) _ x
    _ = _ := by
        rw [Measure.addHaar_ball_mul_of_pos volume (0 : V) hc]
        ring

/-- **The coefficients of the cells near a point**: for levels `i ≤ j` and `ρ ≥ 0`,
`2^(-jn) ∑_{m : |x - c_{j,m}| ≤ ρ 2^(-i)} |λ_{j,m}| ≤ (ρ + n + 1)^n |B_1| 2^(-in) M(x)`, with `M`
the maximal function of the step function of the coefficients of level `j`: these cells lie in
`B(x, (ρ + n + 1) 2^(-i))`, and `2^(-jn) |λ_{j,m}|` is the integral of the step function over
`P_{j,m}`. -/
theorem dyadicWeight_mul_tsum_ite_le_maximal {i j : ℕ} (hij : i ≤ j)
    (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (x : V) :
    dyadicWeight (-(finrank ℝ V : ℝ)) j *
        ∑' m, (if ‖x - cellCenter j m‖ ≤ ρ / 2 ^ i then ‖coef j m‖ₑ else 0) ≤
      ENNReal.ofReal ((ρ + finrank ℝ V + 1) ^ finrank ℝ V) * volume (ball (0 : V) 1) *
        dyadicWeight (-(finrank ℝ V : ℝ)) i * maximal (cellCoefFun j coef) x := by
  set r : ℝ := (ρ + finrank ℝ V + 1) / 2 ^ i
  have hsub : ∀ m, ‖x - cellCenter j m‖ ≤ ρ / 2 ^ i → cell j m ⊆ ball x r := fun m hm y hy => by
    have h1 := norm_sub_cellCenter_le hy
    have h2 : (finrank ℝ V : ℝ) / 2 ^ j ≤ finrank ℝ V / 2 ^ i :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (pow_le_pow_right₀ one_le_two hij)
    have h3 : r = ρ / 2 ^ i + finrank ℝ V / 2 ^ i + 1 / 2 ^ i := by simp only [r]; ring
    have h4 : (0 : ℝ) < 1 / 2 ^ i := by positivity
    rw [mem_ball, dist_eq_norm]
    calc ‖y - x‖ ≤ ‖y - cellCenter j m‖ + ‖x - cellCenter j m‖ := by
          simpa only [dist_eq_norm] using dist_triangle_right y x (cellCenter j m)
      _ < r := by linarith
  have hterm : ∀ m, dyadicWeight (-(finrank ℝ V : ℝ)) j *
      (if ‖x - cellCenter j m‖ ≤ ρ / 2 ^ i then ‖coef j m‖ₑ else 0) ≤
        ∫⁻ y in cell j m, (ball x r).indicator (cellCoefFun j coef) y := fun m => by
    split_ifs with hm
    · rw [setLIntegral_congr_fun (measurableSet_cell j m) fun y hy => by
        rw [indicator_of_mem (hsub m hm hy), cellCoefFun_of_mem hy coef],
        setLIntegral_const, volume_cell, mul_comm]
    · rw [mul_zero]
      exact zero_le
  calc dyadicWeight (-(finrank ℝ V : ℝ)) j *
        ∑' m, (if ‖x - cellCenter j m‖ ≤ ρ / 2 ^ i then ‖coef j m‖ₑ else 0)
      ≤ ∑' m, ∫⁻ y in cell j m, (ball x r).indicator (cellCoefFun j coef) y := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_le_tsum hterm
    _ = ∫⁻ y in ball x r, cellCoefFun j coef y := by
        rw [← lintegral_eq_tsum_cell j, lintegral_indicator measurableSet_ball]
    _ ≤ volume (ball (0 : V) r) * maximal (cellCoefFun j coef) x :=
        setLIntegral_ball_le_mul_maximal (by positivity) _ x
    _ = _ := by rw [volume_ball_div_two_pow (by positivity) i 0]

/-! ### Smooth atoms -/

/-- A smooth atom on `Ω` is bounded by its constant on `Ω`: `|a(y)| ≤ A`. -/
theorem IsSmoothAtom.norm_le {Ω : Set V} {K : ℕ} {d A : ℝ} {j : ℕ} {c : V} {a : V → ℂ}
    (ha : IsSmoothAtom Ω K d A j c a) {y : V} (hy : y ∈ Ω) : ‖a y‖ ≤ A := by
  simpa [norm_iteratedFDerivWithin_zero] using
    ha.norm_iteratedFDerivWithin_le 0 (Nat.zero_le K) y hy

/-- The constant of a smooth atom on `V` is nonnegative: `0 ≤ |a(0)| ≤ A`. -/
theorem IsSmoothAtom.const_nonneg {K : ℕ} {d A : ℝ} {j : ℕ} {c : V} {a : V → ℂ}
    (ha : IsSmoothAtom univ K d A j c a) : 0 ≤ A :=
  (norm_nonneg _).trans (ha.norm_le (mem_univ 0))

/-- A smooth atom on `V` is continuous. -/
theorem IsSmoothAtom.continuous {K : ℕ} {d A : ℝ} {j : ℕ} {c : V} {a : V → ℂ}
    (ha : IsSmoothAtom univ K d A j c a) : Continuous a :=
  continuousOn_univ.1 ha.contDiffOn.continuousOn

/-- A smooth atom has compact support, in `closedBall(c, d 2^(-j))`. -/
theorem IsSmoothAtom.hasCompactSupport {Ω : Set V} {K : ℕ} {d A : ℝ} {j : ℕ} {c : V}
    {a : V → ℂ} (ha : IsSmoothAtom Ω K d A j c a) : HasCompactSupport a :=
  HasCompactSupport.intro (isCompact_closedBall c (d / 2 ^ j)) fun x hx =>
    ha.eq_zero x (by rwa [mem_closedBall, dist_eq_norm, not_le] at hx)

/-- A smooth atom on `V` is integrable. -/
theorem IsSmoothAtom.integrable {K : ℕ} {d A : ℝ} {j : ℕ} {c : V} {a : V → ℂ}
    (ha : IsSmoothAtom univ K d A j c a) : Integrable a :=
  ha.continuous.integrable_of_hasCompactSupport ha.hasCompactSupport

/-- `∫ |a| ≤ A |closedBall(c, d 2^(-j))| = A d^n |B_1| 2^(-jn)` for a smooth atom `a` on `V`
with radius
factor `d ≥ 0`. -/
theorem IsSmoothAtom.lintegral_enorm_le {K : ℕ} {d A : ℝ} (hd : 0 ≤ d) {j : ℕ} {c : V}
    {a : V → ℂ} (ha : IsSmoothAtom univ K d A j c a) :
    ∫⁻ y, ‖a y‖ₑ ≤ ENNReal.ofReal A * (ENNReal.ofReal (d ^ finrank ℝ V) *
      volume (ball (0 : V) 1) * dyadicWeight (-(finrank ℝ V : ℝ)) j) := by
  rw [← eLpNorm_one_eq_lintegral_eNorm ha.integrable.aestronglyMeasurable,
    ← volume_closedBall_div_two_pow hd j c]
  refine (eLpNorm_le_of_bound_of_support ha.integrable.aestronglyMeasurable
    (S := closedBall c (d / 2 ^ j)) (B := ENNReal.ofReal A)
    (fun y hy => ha.eq_zero y (by rwa [mem_closedBall, dist_eq_norm, not_le] at hy))
    fun y => ?_).trans_eq ?_
  · rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ha.norm_le (mem_univ y))
  · rw [ENNReal.toReal_one, div_one, ENNReal.rpow_one]

/-- **Convolution with a series of atoms, term by term**: for a continuous kernel `K` that
vanishes outside `closedBall(0, ρ)`, `ρ ≥ 0`, and smooth atoms `a_m` of level `j` centred at the
cells
with radius factor `d ≥ 0`, `K ⋆ (∑_m λ_m a_m) = ∑_m λ_m K ⋆ a_m` at every point. Near each
point only finitely many atoms meet the support of `y ↦ K(x - y)`. -/
theorem conv_tsum_atom {K : V → ℂ} (hKc : Continuous K) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hKρ : ∀ y, ρ < ‖y‖ → K y = 0) {k : ℕ} {d A : ℝ} (hd : 0 ≤ d) {j : ℕ}
    (coef : (Fin (finrank ℝ V) → ℤ) → ℂ) {a : (Fin (finrank ℝ V) → ℤ) → V → ℂ}
    (ha : ∀ m, IsSmoothAtom univ k d A j (cellCenter j m) (a m)) (x : V) :
    conv K (fun y => ∑' m, coef m * a m y) volume x = ∑' m, coef m * conv K (a m) volume x := by
  have hKs : HasCompactSupport K := HasCompactSupport.intro (isCompact_closedBall 0 ρ)
    fun y hy => hKρ y (by simpa [mem_closedBall, dist_zero_right, not_le] using hy)
  set R := ρ * 2 ^ j + d
  have hR : 0 ≤ R := by positivity
  have hnear : ∀ m y, K y ≠ 0 → a m (x - y) ≠ 0 → ‖x - cellCenter j m‖ ≤ R / 2 ^ j :=
    fun m y hy hay => by
      have h1 : ‖y‖ ≤ ρ := not_lt.1 fun h => hy (hKρ y h)
      have h2 : ‖x - y - cellCenter j m‖ ≤ d / 2 ^ j := not_lt.1 fun h => hay ((ha m).eq_zero _ h)
      calc ‖x - cellCenter j m‖ ≤ ‖x - (x - y)‖ + ‖x - y - cellCenter j m‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ρ + d / 2 ^ j := by rw [sub_sub_cancel]; exact add_le_add h1 h2
        _ = R / 2 ^ j := by simp only [R]; field_simp
  obtain ⟨T, hT, -⟩ := exists_finset_of_card_le
    (P := fun m => ‖x - cellCenter j m‖ ≤ R / 2 ^ j)
    fun S hS => card_le_of_norm_sub_cellCenter_le j hR x S hS
  rw [conv_tsum_of_finset hKc hKs (u := fun m y => coef m * a m y)
    (fun m => ((ha m).integrable.const_mul (coef m)).locallyIntegrable) x T
    fun m hm y hy => by_contra fun hay => hm (hT m (hnear m y hy (right_ne_zero_of_mul hay)))]
  refine tsum_congr fun m => ?_
  rw [conv_apply, conv_apply, ← integral_const_mul]
  congr 1
  funext y
  ring

/-- **Convolution with a series of atoms, bounded term by term**: if `f = ∑_m λ_m a_m` almost
everywhere, for smooth atoms `a_m` of level `j` centred at the cells with radius factor `d ≥ 0`,
then `|K ⋆ f(x)| ≤ ∑_m |λ_m| |K ⋆ a_m(x)|` at every point, for a continuous kernel `K` that
vanishes outside `closedBall(0, ρ)`, `ρ ≥ 0`. -/
theorem enorm_conv_le_tsum_atom {K : V → ℂ} (hKc : Continuous K) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hKρ : ∀ y, ρ < ‖y‖ → K y = 0) {k : ℕ} {d A : ℝ} (hd : 0 ≤ d) {j : ℕ}
    {coef : (Fin (finrank ℝ V) → ℤ) → ℂ} {a : (Fin (finrank ℝ V) → ℤ) → V → ℂ}
    (ha : ∀ m, IsSmoothAtom univ k d A j (cellCenter j m) (a m)) {f : V → ℂ}
    (hf : ∀ᵐ x ∂volume, f x = ∑' m, coef m * a m x) (x : V) :
    ‖conv K f volume x‖ₑ ≤ ∑' m, ‖coef m‖ₑ * ‖conv K (a m) volume x‖ₑ := by
  rw [conv_congr_ae hf, conv_tsum_atom hKc hρ hKρ hd coef ha x]
  refine eNorm_tsum_le_tsum_eNorm.trans_eq ?_
  simp only [eNorm_mul]

/-! ### Coefficients with exponent one -/

/-- **The coefficients with exponent one in `f^s_{p,q}` by maximal functions**: for almost
everywhere strongly measurable functions `g_j`, the step functions of the coefficients
`λ_{j,m} = Rd.cellCoef 1 j g_j m` satisfy, at every point,
`‖(2^(js) |λ_{j,m_j(x)}|)_j‖_{ℓ_q} ≤ (2n + 1)^n |B_1| ‖(M(2^(js) |g_j|)(x))_j‖_{ℓ_q}`. -/
theorem lqNorm_cellCoefFun_le_lqNorm_maximal (q : ℝ≥0∞) (s : ℝ) {g : ℕ → V → ℂ}
    (hg : ∀ j, AEStronglyMeasurable (g j) volume) (x : V) :
    lqNorm q (fun j => dyadicWeight s j * cellCoefFun j (fun j => cellCoef 1 j (g j)) x) ≤
      ENNReal.ofReal ((2 * finrank ℝ V + 1) ^ finrank ℝ V) * volume (ball (0 : V) 1) *
        lqNorm q (fun j => maximal (fun y => dyadicWeight s j * ‖g j y‖ₑ) x) := by
  rw [← ENNReal.lqNorm_const_mul]
  refine ENNReal.lqNorm_mono fun j => ?_
  rw [← dyadicWeight_mul_maximal, mul_left_comm]
  gcongr
  exact cellCoefFun_le_maximal (fun m => enorm_cellCoef_one_le j (hg j) m) x

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-! ### Synthesis: coarse local means -/

/-- **A coarse local mean of an atom**: for levels `i ≤ j` and a smooth atom `a` on `V` of level
`j` with centre `c`, radius factor `d ≥ 0` and constant `A`,
`∫ |k_i(y)| |a(x - y)| dy ≤ C A d^n |B_1| 2^(in) 2^(-jn)` with
`C = Rd.LocalMeansBump.kernelSupConst L`, and the integral vanishes unless
`|x - c| ≤ (2LR + d) 2^(-i)`. -/
theorem lintegral_enorm_kernel_mul_atom_le (L : ℕ) {i j : ℕ} (hij : i ≤ j) {K : ℕ} {d A : ℝ}
    (hd : 0 ≤ d) {c : V} {a : V → ℂ} (ha : IsSmoothAtom univ K d A j c a) (x : V) :
    ∫⁻ y, ‖b.kernel L i y‖ₑ * ‖a (x - y)‖ₑ ≤
      ENNReal.ofReal (b.kernelSupConst L) * (ENNReal.ofReal A *
        (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1))) *
          dyadicWeight (finrank ℝ V : ℝ) i * dyadicWeight (-(finrank ℝ V : ℝ)) j *
            (if ‖x - c‖ ≤ (2 * L * b.radius + d) / 2 ^ i then 1 else 0) := by
  split_ifs with hx
  · rw [mul_one]
    calc ∫⁻ y, ‖b.kernel L i y‖ₑ * ‖a (x - y)‖ₑ
        ≤ ∫⁻ y, ENNReal.ofReal (b.kernelSupConst L) * dyadicWeight (finrank ℝ V : ℝ) i *
            ‖a (x - y)‖ₑ :=
          lintegral_mono fun y => by
            gcongr
            rw [ENNReal.dyadicWeight_natCast]
            exact b.enorm_kernel_le L i y
      _ = ENNReal.ofReal (b.kernelSupConst L) * dyadicWeight (finrank ℝ V : ℝ) i *
            ∫⁻ y, ‖a y‖ₑ := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.dyadicWeight_ne_top _ _)), lintegral_sub_left_eq_self (fun y => ‖a y‖ₑ) x]
      _ ≤ ENNReal.ofReal (b.kernelSupConst L) * dyadicWeight (finrank ℝ V : ℝ) i *
            (ENNReal.ofReal A * (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1) *
              dyadicWeight (-(finrank ℝ V : ℝ)) j)) := by
          gcongr
          exact ha.lintegral_enorm_le hd
      _ = _ := by ring
  · have h0 : ∀ y, ‖b.kernel L i y‖ₑ * ‖a (x - y)‖ₑ = 0 := fun y => by
      by_cases hy : 2 * L * b.radius / 2 ^ i < ‖y‖
      · rw [b.kernel_eq_zero_of_lt L i hy, eNorm_zero, zero_mul]
      · push Not at hy hx
        have h1 : d / 2 ^ j ≤ d / 2 ^ i :=
          div_le_div_of_nonneg_left hd (by positivity) (pow_le_pow_right₀ one_le_two hij)
        have h2 : ‖x - c‖ ≤ ‖x - y - c‖ + ‖y‖ := by
          calc ‖x - c‖ = ‖(x - y - c) + y‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        have h3 : (2 * L * b.radius + d) / 2 ^ i = 2 * L * b.radius / 2 ^ i + d / 2 ^ i :=
          add_div _ _ _
        rw [ha.eq_zero (x - y) (by linarith), eNorm_zero, mul_zero]
    simp only [h0, lintegral_zero, mul_zero, le_refl]

/-- The constant `C A_+ d^n |B_1| (2LR + d + n + 1)^n |B_1|` of the coarse local means of atoms
with radius factor `d` and constant `A`, where `A_+ = max(A, 0)`,
`C = Rd.LocalMeansBump.kernelSupConst L` and `R` is the radius of the bump. -/
noncomputable def tlAtomCoarseConst (L : ℕ) (d A : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (b.kernelSupConst L) * (ENNReal.ofReal A *
    (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1))) *
      (ENNReal.ofReal ((2 * L * b.radius + d + finrank ℝ V + 1) ^ finrank ℝ V) *
        volume (ball (0 : V) 1))

/-- The constant of the coarse local means of atoms is finite. -/
theorem tlAtomCoarseConst_ne_top (L : ℕ) (d A : ℝ) : b.tlAtomCoarseConst L d A ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_ball_ne_top 1))))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_ball_ne_top 1))

/-- **A coarse local mean of the atoms of one level**: for levels `i ≤ j`, smooth atoms
`a_{j,m}` on `V` of level `j` centred at the cells, with radius factor `d ≥ 0` and constant `A`,
and `f = ∑_m λ_{j,m} a_{j,m}` almost everywhere, `|k_i ⋆ f(x)| ≤ C M(x)` at every point, with
`M` the maximal function of the step function of the coefficients of level `j` and
`C = Rd.LocalMeansBump.tlAtomCoarseConst L d A`. -/
theorem enorm_conv_kernel_level_le_of_le (L : ℕ) {i j : ℕ} (hij : i ≤ j) {K : ℕ} {d A : ℝ}
    (hd : 0 ≤ d) {coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ}
    {a : ℕ → (Fin (finrank ℝ V) → ℤ) → V → ℂ}
    (hatom : ∀ m, IsSmoothAtom univ K d A j (cellCenter j m) (a j m)) {f : V → ℂ}
    (hf : ∀ᵐ x ∂volume, f x = ∑' m, coef j m * a j m x) (x : V) :
    ‖conv (b.kernel L i) f volume x‖ₑ ≤
      b.tlAtomCoarseConst L d A * maximal (cellCoefFun j coef) x := by
  have hR := b.radius_nonneg
  have hρ : 0 ≤ 2 * L * b.radius + d := by positivity
  refine (enorm_conv_le_tsum_atom (b.continuous_kernel L i) (by positivity)
    (fun y hy => b.kernel_eq_zero_of_lt L i hy) hd hatom hf x).trans
    ((ENNReal.tsum_mul_le_of_le fun m => (enorm_conv_le_lintegral _ _ x).trans
      (b.lintegral_enorm_kernel_mul_atom_le L hij hd (hatom m) x)).trans ?_)
  calc ENNReal.ofReal (b.kernelSupConst L) * (ENNReal.ofReal A *
        (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1))) *
          dyadicWeight (finrank ℝ V : ℝ) i * dyadicWeight (-(finrank ℝ V : ℝ)) j *
        ∑' m, (if ‖x - cellCenter j m‖ ≤ (2 * L * b.radius + d) / 2 ^ i then ‖coef j m‖ₑ
          else 0)
      = ENNReal.ofReal (b.kernelSupConst L) * (ENNReal.ofReal A *
        (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1))) *
          dyadicWeight (finrank ℝ V : ℝ) i * (dyadicWeight (-(finrank ℝ V : ℝ)) j *
        ∑' m, (if ‖x - cellCenter j m‖ ≤ (2 * L * b.radius + d) / 2 ^ i then ‖coef j m‖ₑ
          else 0)) := by ring
    _ ≤ ENNReal.ofReal (b.kernelSupConst L) * (ENNReal.ofReal A *
        (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1))) *
          dyadicWeight (finrank ℝ V : ℝ) i *
        (ENNReal.ofReal ((2 * L * b.radius + d + finrank ℝ V + 1) ^ finrank ℝ V) *
          volume (ball (0 : V) 1) * dyadicWeight (-(finrank ℝ V : ℝ)) i *
            maximal (cellCoefFun j coef) x) :=
        mul_le_mul_right (dyadicWeight_mul_tsum_ite_le_maximal hij coef hρ x) _
    _ = b.tlAtomCoarseConst L d A * maximal (cellCoefFun j coef) x *
          (dyadicWeight (-(finrank ℝ V : ℝ)) i * dyadicWeight (finrank ℝ V : ℝ) i) := by
        rw [tlAtomCoarseConst]
        ring
    _ = _ := by rw [ENNReal.dyadicWeight_neg_mul_self, mul_one]

/-! ### Synthesis: fine local means -/

/-- One step of the moment identity for an atom, pointwise in `z`: for a smooth atom `a` on `V`
of level `j` and order `L ≥ 1` with centre `c`, radius factor `d` and constant `A`, and `k ≥ j`,
`|g(z)| |Δ^L_{-2^(-k) z} a(x)| ≤ |g(z)| 2^L L^(L+1) A R^L 2^(-(k-j)L) 1_{|x - c| ≤ (d + LR) 2^(-j)}`
for the bump `g` of radius `R`: on the support of `g` the step has length at most `2^(-k) R`, and
far from `c` the differences vanish (`Rd.IsSmoothAtom.higherDiff_eq_zero_of_lt`). -/
theorem enorm_mul_higherDiff_atom_le {L : ℕ} (hL : 1 ≤ L) {d A : ℝ} {j : ℕ}
    {c : V} {a : V → ℂ} (ha : IsSmoothAtom univ L d A j c a) {k : ℕ} (hjk : j ≤ k) (z x : V) :
    ‖b.toFun z‖ₑ * ‖(fwdDiff (-((2 : ℝ) ^ k)⁻¹ • z))^[L] a x‖ₑ ≤
      ‖b.toFun z‖ₑ * (ENNReal.ofReal (2 ^ L * (L : ℝ) ^ (L + 1) * A) *
        ENNReal.ofReal (b.radius ^ L) * dyadicWeight (-(L : ℝ)) (k - j) *
          (if ‖x - c‖ ≤ (d + L * b.radius) / 2 ^ j then 1 else 0)) := by
  by_cases hz : b.radius < ‖z‖
  · rw [b.eq_zero z hz, eNorm_zero, zero_mul, zero_mul]
  push Not at hz
  refine mul_le_mul_right ?_ _
  have hR := b.radius_nonneg
  have hA := ha.const_nonneg
  have hh : ‖-((2 : ℝ) ^ k)⁻¹ • z‖ ≤ b.radius / 2 ^ k := by
    rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hz (by positivity)
  have hkj : b.radius / 2 ^ k ≤ b.radius / 2 ^ j :=
    div_le_div_of_nonneg_left hR (by positivity) (pow_le_pow_right₀ one_le_two hjk)
  split_ifs with hx
  · rw [mul_one, mul_assoc]
    refine (ha.enorm_higherDiff_le convex_univ (by rw [interior_univ]; exact univ_nonempty) hA hL
      le_rfl (by rw [stepSet_univ]; trivial)).trans
      (mul_le_mul_right ((min_le_right _ _).trans ?_) _)
    have h1 : 2 ^ j * ‖-((2 : ℝ) ^ k)⁻¹ • z‖ ≤ b.radius * (1 / 2 ^ (k - j)) := by
      have hk : (2 : ℝ) ^ k = 2 ^ (k - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hjk]
      calc 2 ^ j * ‖-((2 : ℝ) ^ k)⁻¹ • z‖ ≤ 2 ^ j * (b.radius / 2 ^ k) := by gcongr
        _ = b.radius * (1 / 2 ^ (k - j)) := by rw [hk]; field_simp
    calc ENNReal.ofReal (2 ^ j * ‖-((2 : ℝ) ^ k)⁻¹ • z‖) ^ (L : ℝ)
        = ENNReal.ofReal ((2 ^ j * ‖-((2 : ℝ) ^ k)⁻¹ • z‖) ^ L) := by
          rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (by positivity)]
      _ ≤ ENNReal.ofReal ((b.radius * (1 / 2 ^ (k - j))) ^ L) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) h1 L)
      _ = ENNReal.ofReal (b.radius ^ L) * dyadicWeight (-(L : ℝ)) (k - j) := by
          rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_one_div_two_pow_pow]
  · push Not at hx
    rw [ha.higherDiff_eq_zero_of_lt L (hh.trans hkj) (lt_of_eq_of_lt (by ring) hx), eNorm_zero]
    exact zero_le

/-- **One scale of the moment identity for an atom**: for a smooth atom `a` on `V` of level `j`
and order `L ≥ 1` with centre `c`, radius factor `d` and constant `A`, and `k ≥ j`, almost
everywhere
`|a(x) - (m_{2^k} ⋆ a)(x)| ≤ ‖g‖_1 2^L L^(L+1) A R^L 2^(-(k-j)L) 1_{|x - c| ≤ (d + LR) 2^(-j)}`,
by the averaged differences of the moment kernel `m` of the bump `g`. -/
theorem ae_enorm_atom_sub_conv_scaled_le {L : ℕ} (hL : 1 ≤ L) {d A : ℝ} {j : ℕ}
    {c : V} {a : V → ℂ} (ha : IsSmoothAtom univ L d A j c a) {k : ℕ} (hjk : j ≤ k) :
    ∀ᵐ x ∂volume, ‖a x - conv (b.scaled L k) a volume x‖ₑ ≤
      (∫⁻ z, ‖b.toFun z‖ₑ) * (ENNReal.ofReal (2 ^ L * (L : ℝ) ^ (L + 1) * A) *
        ENNReal.ofReal (b.radius ^ L) * dyadicWeight (-(L : ℝ)) (k - j) *
          (if ‖x - c‖ ≤ (d + L * b.radius) / 2 ^ j then 1 else 0)) := by
  filter_upwards [ae_enorm_sub_conv_dilate_momentKernel_le le_rfl ENNReal.one_ne_top b.integrable
    b.integral_eq_one (memLp_one_iff_integrable.2 ha.integrable) L (c := (2 : ℝ) ^ k)
    (by positivity)] with x hx
  refine hx.trans ((lintegral_mono fun z =>
    b.enorm_mul_higherDiff_atom_le hL ha hjk z x).trans ?_)
  rw [lintegral_mul_const'' _ b.contDiff.continuous.aestronglyMeasurable.eNorm]

/-- The constant `2 ‖g‖_1 2^L L^(L+1) A (2R)^L` of the fine local means of a smooth atom of order
`L` and constant `A`, for the bump `g` of radius `R`. -/
noncomputable def momentAtomConst (L : ℕ) (A : ℝ) : ℝ≥0∞ :=
  2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (2 ^ L * (L : ℝ) ^ (L + 1) * A) *
    ENNReal.ofReal ((2 * b.radius) ^ L)

/-- The constant of the fine local means of a smooth atom is finite. -/
theorem momentAtomConst_ne_top (L : ℕ) (A : ℝ) : b.momentAtomConst L A ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    b.integrable.hasFiniteIntegral.ne) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

/-- **A fine local mean of an atom**: for a smooth atom `a` on `V` of level `j < i` and order
`L ≥ 1` with centre `c`, radius factor `d` and constant `A`, almost everywhere
`|k_i ⋆ a(x)| ≤ C 2^(-(i-j)L) 1_{|x - c| ≤ (d + LR) 2^(-j)}` with
`C = Rd.LocalMeansBump.momentAtomConst L A`. The kernel `k_i = m_{2^i} - m_{2^(i-1)}` is a
difference of two moment kernels (`Rd.LocalMeansBump.ae_enorm_conv_kernel_le_of_scaled`), each of
which reproduces `a` up to averaged differences of order `L` with steps of length at most
`2^(1-i) R`. -/
theorem ae_enorm_conv_kernel_atom_le_of_lt {L : ℕ} (hL : 1 ≤ L) {d A : ℝ} {j : ℕ}
    {c : V} {a : V → ℂ} (ha : IsSmoothAtom univ L d A j c a) {i : ℕ} (hji : j < i) :
    ∀ᵐ x ∂volume, ‖conv (b.kernel L i) a volume x‖ₑ ≤
      b.momentAtomConst L A * dyadicWeight (-(L : ℝ)) (i - j) *
        (if ‖x - c‖ ≤ (d + L * b.radius) / 2 ^ j then 1 else 0) := by
  have hR := b.radius_nonneg
  have h2R : ENNReal.ofReal ((2 * b.radius) ^ L) = 2 ^ L * ENNReal.ofReal (b.radius ^ L) := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat]
  filter_upwards [b.ae_enorm_conv_kernel_le_of_scaled L (memLp_one_iff_integrable.2 ha.integrable)
    (C := (∫⁻ z, ‖b.toFun z‖ₑ) * (ENNReal.ofReal (2 ^ L * (L : ℝ) ^ (L + 1) * A) *
      ENNReal.ofReal (b.radius ^ L)))
    (u := fun x => if ‖x - c‖ ≤ (d + L * b.radius) / 2 ^ j then 1 else 0)
    (fun k hjk => (b.ae_enorm_atom_sub_conv_scaled_le hL ha hjk).mono fun x hx =>
      hx.trans_eq (by ring)) hji] with x hx
  refine hx.trans_eq ?_
  rw [momentAtomConst, h2R]
  ring

/-- The constant `C (d + LR + n + 1)^n |B_1|` of the fine local means of atoms with radius factor
`d` and constant `A`, with `C = Rd.LocalMeansBump.momentAtomConst L A` and the radius `R` of the
bump. -/
noncomputable def tlAtomFineConst (L : ℕ) (d A : ℝ) : ℝ≥0∞ :=
  b.momentAtomConst L A * (ENNReal.ofReal ((d + L * b.radius + finrank ℝ V + 1) ^ finrank ℝ V) *
    volume (ball (0 : V) 1))

/-- The constant of the fine local means of atoms is finite. -/
theorem tlAtomFineConst_ne_top (L : ℕ) (d A : ℝ) : b.tlAtomFineConst L d A ≠ ∞ :=
  ENNReal.mul_ne_top (b.momentAtomConst_ne_top L A)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_ball_ne_top 1))

/-- **A fine local mean of the atoms of one level**: for levels `j < i`, smooth atoms `a_{j,m}`
on `V` of level `j` and order `L ≥ 1` centred at the cells, with radius factor `d ≥ 0` and
constant `A`, and `f = ∑_m λ_{j,m} a_{j,m}` almost everywhere, almost everywhere
`|k_i ⋆ f(x)| ≤ C 2^(-(i-j)L) M(x)`, with `M` the maximal function of the step function of the
coefficients of level `j` and `C = Rd.LocalMeansBump.tlAtomFineConst L d A`. -/
theorem ae_enorm_conv_kernel_level_le_of_lt {L : ℕ} (hL : 1 ≤ L) {d A : ℝ} (hd : 0 ≤ d)
    {j : ℕ} {coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ}
    {a : ℕ → (Fin (finrank ℝ V) → ℤ) → V → ℂ}
    (hatom : ∀ m, IsSmoothAtom univ L d A j (cellCenter j m) (a j m)) {f : V → ℂ}
    (hf : ∀ᵐ x ∂volume, f x = ∑' m, coef j m * a j m x) {i : ℕ} (hji : j < i) :
    ∀ᵐ x ∂volume, ‖conv (b.kernel L i) f volume x‖ₑ ≤
      b.tlAtomFineConst L d A * dyadicWeight (-(L : ℝ)) (i - j) *
        maximal (cellCoefFun j coef) x := by
  have hR := b.radius_nonneg
  have hρ : 0 ≤ d + L * b.radius := by positivity
  filter_upwards [ae_all_iff.2 fun m => b.ae_enorm_conv_kernel_atom_le_of_lt hL (hatom m) hji]
    with x hx
  refine (enorm_conv_le_tsum_atom (b.continuous_kernel L i) (by positivity)
    (fun y hy => b.kernel_eq_zero_of_lt L i hy) hd hatom hf x).trans
    ((ENNReal.tsum_mul_le_of_le hx).trans ?_)
  have hS : ∑' m, (if ‖x - cellCenter j m‖ ≤ (d + L * b.radius) / 2 ^ j then ‖coef j m‖ₑ
      else 0) ≤ ENNReal.ofReal ((d + L * b.radius + finrank ℝ V + 1) ^ finrank ℝ V) *
        volume (ball (0 : V) 1) * maximal (cellCoefFun j coef) x := by
    refine (ENNReal.mul_le_mul_iff_right (ENNReal.dyadicWeight_ne_zero (-(finrank ℝ V : ℝ)) j)
      (ENNReal.dyadicWeight_ne_top _ _)).1
      ((dyadicWeight_mul_tsum_ite_le_maximal (le_refl j) coef hρ x).trans_eq ?_)
    ring
  calc b.momentAtomConst L A * dyadicWeight (-(L : ℝ)) (i - j) *
        ∑' m, (if ‖x - cellCenter j m‖ ≤ (d + L * b.radius) / 2 ^ j then ‖coef j m‖ₑ else 0)
      ≤ b.momentAtomConst L A * dyadicWeight (-(L : ℝ)) (i - j) *
        (ENNReal.ofReal ((d + L * b.radius + finrank ℝ V + 1) ^ finrank ℝ V) *
          volume (ball (0 : V) 1) * maximal (cellCoefFun j coef) x) := by gcongr
    _ = _ := by rw [tlAtomFineConst]; ring

/-! ### Synthesis: the theorem -/

/-- The constant of the synthesis of Triebel–Lizorkin spaces from atoms with radius factor `d`
and constant `A`: the larger of the constants of the coarse and of the fine local means,
`max (Rd.LocalMeansBump.tlAtomCoarseConst L d A) (Rd.LocalMeansBump.tlAtomFineConst L d A)`. -/
noncomputable def tlAtomSynthesisConst (L : ℕ) (d A : ℝ) : ℝ≥0∞ :=
  max (b.tlAtomCoarseConst L d A) (b.tlAtomFineConst L d A)

/-- The constant of the synthesis from atoms is finite. -/
theorem tlAtomSynthesisConst_ne_top (L : ℕ) (d A : ℝ) : b.tlAtomSynthesisConst L d A ≠ ∞ :=
  (max_lt (b.tlAtomCoarseConst_ne_top L d A).lt_top (b.tlAtomFineConst_ne_top L d A).lt_top).ne

/-- **A local mean of the atoms of one level**: for smooth atoms `a_{j,m}` on `V` of level `j`
and order `L ≥ 1` centred at the cells, with radius factor `d ≥ 0` and constant `A`, and
`f = ∑_m λ_{j,m} a_{j,m}` almost everywhere, for every `i` almost everywhere
`|k_i ⋆ f(x)| ≤ C c_{ij} M(x)` with `c_{ij} = 2^(-(i-j)L)` for `j ≤ i`, `c_{ij} = 1` for `j > i`,
`M` the maximal function of the step function of the coefficients of level `j` and
`C = Rd.LocalMeansBump.tlAtomSynthesisConst L d A`. -/
theorem ae_enorm_conv_kernel_level_le {L : ℕ} (hL : 1 ≤ L) {d A : ℝ} (hd : 0 ≤ d)
    {j : ℕ} {coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ}
    {a : ℕ → (Fin (finrank ℝ V) → ℤ) → V → ℂ}
    (hatom : ∀ m, IsSmoothAtom univ L d A j (cellCenter j m) (a j m)) {f : V → ℂ}
    (hf : ∀ᵐ x ∂volume, f x = ∑' m, coef j m * a j m x) (i : ℕ) :
    ∀ᵐ x ∂volume, ‖conv (b.kernel L i) f volume x‖ₑ ≤ b.tlAtomSynthesisConst L d A *
      ((if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) *
        maximal (cellCoefFun j coef) x) := by
  rcases lt_or_ge j i with hji | hij
  · filter_upwards [b.ae_enorm_conv_kernel_level_le_of_lt hL hd hatom hf hji] with x hx
    simp only [hji.le, ↓reduceIte]
    refine hx.trans ?_
    rw [← mul_assoc, tlAtomSynthesisConst]
    gcongr
    exact le_max_right _ _
  · refine ae_of_all _ fun x => (b.enorm_conv_kernel_level_le_of_le L hij hd hatom hf x).trans ?_
    have h1 : 1 ≤ (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) := by
      split_ifs with hji
      · rw [le_antisymm hji hij, Nat.sub_self, ENNReal.dyadicWeight_zero_right]
      · exact le_rfl
    calc b.tlAtomCoarseConst L d A * maximal (cellCoefFun j coef) x
        ≤ b.tlAtomSynthesisConst L d A * (1 * maximal (cellCoefFun j coef) x) := by
          rw [one_mul, tlAtomSynthesisConst]
          gcongr
          exact le_max_left _ _
      _ ≤ _ := by gcongr

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Local means of a sum of levels**: if `∑_{j ≤ J} f_j → F` in `L_p`, `1 ≤ p < ∞`, then
almost everywhere `|k_i ⋆ F(x)| ≤ ∑_j |k_i ⋆ f_j(x)|`: the local mean `k_i ⋆` is continuous on
`L_p`, and the bound holds for the partial sums
(`MeasureTheory.ae_enorm_le_of_tendsto_Lp`). -/
theorem enorm_conv_kernel_le_tsum_level (hp : p ≠ ∞) (L : ℕ)
    (f : ℕ → Lp ℂ p (volume : Measure V)) {F : Lp ℂ p (volume : Measure V)}
    (hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F)) (i : ℕ) :
    ∀ᵐ x ∂volume, ‖conv (b.kernel L i) F volume x‖ₑ ≤
      ∑' j, ‖conv (b.kernel L i) (f j) volume x‖ₑ := by
  have h := ae_enorm_le_of_tendsto_Lp (((b.localMean hp L i).continuous.tendsto F).comp hF)
    (v := fun x => ∑' j, ‖conv (b.kernel L i) (f j) volume x‖ₑ) fun J => by
      have hall := ae_all_iff.2 fun j => b.localMean_ae_eq hp L i (f j)
      filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
        (fun j => b.localMean hp L i (f j)), hall] with x hx hj
      simp only [Function.comp_apply, map_sum]
      rw [hx]
      refine (eNorm_sum_le _ _).trans ?_
      simp only [hj]
      exact sum_le_tsum _
  filter_upwards [h, b.localMean_ae_eq hp L i F] with x hx hb
  rwa [← hb]

/-- **Local means of an atomic sum, pointwise**: for smooth atoms `a_{j,m}` on `V` of level `j`
and order `L ≥ 1` centred at the cells, with radius factor `d ≥ 0` and constant `A`, level
sums `f_j = ∑_m λ_{j,m} a_{j,m}` almost everywhere and `∑_{j ≤ J} f_j → F` in `L_p`,
`1 ≤ p < ∞`, almost everywhere and for all `i`,
`|k_i ⋆ F(x)| ≤ C ∑_j c_{ij} M_j(x)` with `c_{ij} = 2^(-(i-j)L)` for `j ≤ i`, `c_{ij} = 1` for
`j > i`, `M_j` the maximal function of the step function of the coefficients of level `j` and
`C = Rd.LocalMeansBump.tlAtomSynthesisConst L d A`. -/
theorem enorm_localMean_le_tsum_maximal_cellCoefFun {L : ℕ} (hL : 1 ≤ L) (hp : p ≠ ∞)
    {d A : ℝ} (hd : 0 ≤ d) {coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ}
    {a : ℕ → (Fin (finrank ℝ V) → ℤ) → V → ℂ}
    (hatom : ∀ j m, IsSmoothAtom univ L d A j (cellCenter j m) (a j m))
    {f : ℕ → Lp ℂ p (volume : Measure V)}
    (hf : ∀ j, ∀ᵐ x ∂volume, f j x = ∑' m, coef j m * a j m x) {F : Lp ℂ p (volume : Measure V)}
    (hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F)) :
    ∀ᵐ x ∂volume, ∀ i, ‖conv (b.kernel L i) F volume x‖ₑ ≤ b.tlAtomSynthesisConst L d A *
      ∑' j, (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) *
        maximal (cellCoefFun j coef) x := by
  have h1 := ae_all_iff.2 fun i => b.enorm_conv_kernel_le_tsum_level hp L f hF i
  have h2 := ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
    b.ae_enorm_conv_kernel_level_le hL hd (hatom j) (hf j) i
  filter_upwards [h1, h2] with x hx1 hx2 i
  refine (hx1 i).trans ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_le_tsum fun j => hx2 i j

/-- **Synthesis from atoms**: for smooth atoms `a_{j,m}` on `V` of level `j` and order `L ≥ 1`
centred at the cells, with radius factor `d ≥ 0` and constant `A`, level sums
`f_j = ∑_m λ_{j,m} a_{j,m}` almost everywhere with `∑_{j ≤ J} f_j → F` in `L_p`, `1 < p < ∞`,
`1 < q ≤ ∞` and `s ∈ ℝ`,
`‖F‖_{F^s_{p,q}}^{b,L} ≤ C A_{s,L} C_{FS} ‖λ‖_{f^s_{p,q}}` with
`C = Rd.LocalMeansBump.tlAtomSynthesisConst L d A`, `A_{s,L} = ENNReal.almostDiagonalConst s L`
(finite for `0 < s < L`) and the Fefferman–Stein constant `C_{FS} = Rd.feffermanSteinConst V p q`.
-/
theorem tlLocalMeansNorm_le_tlCoeffNorm {L : ℕ} (hL : 1 ≤ L) (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) (s : ℝ) {d A : ℝ} (hd : 0 ≤ d)
    {coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ} {a : ℕ → (Fin (finrank ℝ V) → ℤ) → V → ℂ}
    (hatom : ∀ j m, IsSmoothAtom univ L d A j (cellCenter j m) (a j m))
    {f : ℕ → Lp ℂ p (volume : Measure V)}
    (hf : ∀ j, ∀ᵐ x ∂volume, f j x = ∑' m, coef j m * a j m x) {F : Lp ℂ p (volume : Measure V)}
    (hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F)) :
    b.tlLocalMeansNorm L s q F ≤ b.tlAtomSynthesisConst L d A * ENNReal.almostDiagonalConst s L *
      feffermanSteinConst V p q * tlCoeffNorm p s q coef :=
  eLpNorm_le_of_le_lqNorm_maximal hp1 hp hq1 (b.aemeasurable_lqNorm_conv_kernel L s q F)
    (fun j => ((measurable_cellCoefFun j coef).const_mul _).aemeasurable)
    ((b.enorm_localMean_le_tsum_maximal_cellCoefFun hL hp hd hatom hf hF).mono fun x hx =>
      (ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq1.le s L hx).trans_eq
        (by simp only [dyadicWeight_mul_maximal]))

/-! ### Analysis -/

/-- **Atomic decomposition with `L_1`-normalised coefficients**: for `L ≥ 1`, every order `K`,
`1 ≤ p < ∞` and `F ∈ L_p`, with `g_j = k_j ⋆ F`, the coefficients
`λ_{j,m} = Rd.cellCoef 1 j g_j m = 2^(jn) ∫_{P_{j,m}} |g_j|` and the cell atoms
`a_{j,m} = Rd.cellAtom 1 η_j j g_j m = λ_{j,m}⁻¹ η_j ⋆ (1_{P_{j,m}} g_j)` with exponent one
satisfy: every `a_{j,m}` is a smooth atom on `V` of level `j` and order `K` with radius factor
`2LR + n` and constant `Rd.LocalMeansBump.dualDerivConst L K`; `η_j ⋆ g_j = ∑_m λ_{j,m} a_{j,m}`
at every point; and `∑_{j ≤ J} η_j ⋆ g_j → F` in `L_p`. -/
theorem tl_atomic_decomposition {L : ℕ} (hL : 1 ≤ L) (K : ℕ) (hp : p ≠ ∞)
    (F : Lp ℂ p (volume : Measure V)) :
    (∀ j m, IsSmoothAtom univ K (2 * L * b.radius + finrank ℝ V) (b.dualDerivConst L K) j
      (cellCenter j m) (cellAtom 1 (b.dual L j) j (conv (b.kernel L j) F volume) m)) ∧
    (∀ j x, conv (b.dual L j) (conv (b.kernel L j) F volume) volume x =
      ∑' m, cellCoef 1 j (conv (b.kernel L j) F volume) m *
        cellAtom 1 (b.dual L j) j (conv (b.kernel L j) F volume) m x) ∧
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L j) (b.localMean hp L j F)) atTop (𝓝 F) := by
  have hcell : ∀ j m, MemLp ((cell j m).indicator (conv (b.kernel L j) F volume)) 1 volume :=
    fun j m => memLp_one_indicator_cell Fact.out
      (memLp_conv Fact.out (b.integrable_kernel L j) (Lp.memLp F)) j m
  refine ⟨fun j m => ?_, fun j x => ?_, b.tendsto_sum_dual_localMean hp hL F⟩
  · have h := b.isSmoothAtom_cellAtom le_rfl L K j (hcell j m) m
    rw [cellAtom_indicator] at h
    convert h using 1
    simp
  · have hR := b.radius_nonneg
    exact conv_eq_tsum_cellAtom_of_indicator le_rfl (b.continuous_dual L j) (by positivity)
      (fun y hy => b.dual_eq_zero_of_lt L j hy) (hcell j) x

/-- **The coefficients of the atomic decomposition in `f^s_{p,q}`**: for every order `L`,
`1 < p < ∞`, `1 < q ≤ ∞`, `s ∈ ℝ` and `F ∈ L_p`, the coefficients with exponent one
`λ_{j,m} = Rd.cellCoef 1 j (k_j ⋆ F) m` satisfy
`‖λ‖_{f^s_{p,q}} ≤ (2n + 1)^n |B_1| C_{FS} ‖F‖_{F^s_{p,q}}^{b,L}` with the Fefferman–Stein
constant `C_{FS} = Rd.feffermanSteinConst V p q`. -/
theorem tlCoeffNorm_cellCoef_le (L : ℕ) (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q)
    (s : ℝ) (F : Lp ℂ p (volume : Measure V)) :
    tlCoeffNorm p s q (fun j => cellCoef 1 j (conv (b.kernel L j) F volume)) ≤
      ENNReal.ofReal ((2 * finrank ℝ V + 1) ^ finrank ℝ V) * volume (ball (0 : V) 1) *
        feffermanSteinConst V p q * b.tlLocalMeansNorm L s q F :=
  eLpNorm_le_of_le_lqNorm_maximal hp1 hp hq1 (aemeasurable_lqNorm_cellCoefFun s q _)
    (fun j => (b.measurable_dyadicWeight_mul_conv_kernel L s j F).aemeasurable)
    (ae_of_all _ (lqNorm_cellCoefFun_le_lqNorm_maximal q s fun j =>
      (b.continuous_conv_kernel L j F).aestronglyMeasurable))

end LocalMeansBump

/-! ### The atomic characterisation -/

/-- **The atomic characterisation of Triebel–Lizorkin spaces** for `1 < p < ∞`, `1 < q ≤ ∞`
and `s > 0`, with atoms normalised in `L_∞` and the weights `2^(js)` in `f^s_{p,q}`; for `s > 0`
the atoms carry no moment conditions. Triebel, *Theory of Function Spaces II*, states it with
`(s,p)`-atoms normalised in `L_p`; the coefficients `λ_{j,m}` here correspond to his
coefficients `2^(j(s - n/p)) λ_{j,m}`, `n = dim V`. For an order `L` with `0 < s < L`,
`F ∈ F^s_{p,q}` iff `F = ∑_j f_j` in `L_p` with `f_j = ∑_m λ_{j,m} a_{j,m}` almost everywhere for
smooth atoms `a_{j,m}` on `V` of level `j` and order `L` centred at the cells, with a common
radius factor `d ≥ 0` and constant `A`, and `‖λ‖_{f^s_{p,q}} < ∞`. The atoms of `F` are the cell
atoms of `η_j ⋆ (k_j ⋆ F)` (`Rd.LocalMeansBump.tl_atomic_decomposition`); the converse is the
synthesis `Rd.LocalMeansBump.tlLocalMeansNorm_le_tlCoeffNorm`. The Besov analogue is
`Rd.LocalMeansBump.besov_iff_atomic`. -/
theorem memTriebelLizorkin_iff_atomic {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) {s : ℝ} (hs : 0 < s) {L : ℕ} (hsL : s < L)
    (F : Lp ℂ p (volume : Measure V)) :
    MemTriebelLizorkin s q F ↔ ∃ (d A : ℝ) (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ)
      (a : ℕ → (Fin (finrank ℝ V) → ℤ) → V → ℂ) (f : ℕ → Lp ℂ p (volume : Measure V)),
      0 ≤ d ∧ (∀ j m, IsSmoothAtom univ L d A j (cellCenter j m) (a j m)) ∧
      (∀ j, ∀ᵐ x ∂volume, f j x = ∑' m, coef j m * a j m x) ∧
      Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F) ∧
      tlCoeffNorm p s q coef < ∞ := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 fun h => by
    rw [h, Nat.cast_zero] at hsL
    linarith
  obtain ⟨b⟩ : Nonempty (LocalMeansBump V) := ⟨LocalMeansBump.std⟩
  rw [b.memTriebelLizorkin_iff_tlLocalMeans hp1 hp hq1 hs hsL]
  constructor
  · intro hF
    obtain ⟨hatom, hsum, hlim⟩ := b.tl_atomic_decomposition hL L hp F
    have hR := b.radius_nonneg
    refine ⟨2 * L * b.radius + finrank ℝ V, b.dualDerivConst L L,
      fun j => cellCoef 1 j (conv (b.kernel L j) F volume),
      fun j => cellAtom 1 (b.dual L j) j (conv (b.kernel L j) F volume),
      fun j => convLp hp (b.integrable_dual L j) (b.localMean hp L j F), by positivity, hatom,
      fun j => ?_, hlim, ?_⟩
    · filter_upwards [convLp_apply_ae hp (b.integrable_dual L j) (b.localMean hp L j F)]
        with x hx
      rw [hx, conv_congr_ae (b.localMean_ae_eq hp L j F)]
      exact hsum j x
    · exact (b.tlCoeffNorm_cellCoef_le L hp1 hp hq1 s F).trans_lt (ENNReal.mul_lt_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_ball_ne_top 1))
          (feffermanSteinConst_ne_top hp1 hp hq1)).lt_top hF)
  · rintro ⟨d, A, coef, a, f, hd, hatom, hf, hF, hcoef⟩
    exact (b.tlLocalMeansNorm_le_tlCoeffNorm hL hp1 hp hq1 s hd hatom hf hF).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (b.tlAtomSynthesisConst_ne_top L d A) (ENNReal.almostDiagonalConst_ne_top hs hsL))
          (feffermanSteinConst_ne_top hp1 hp hq1)).lt_top hcoef)

end Rd
