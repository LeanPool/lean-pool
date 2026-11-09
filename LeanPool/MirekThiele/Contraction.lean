/-
Copyright (c) 2026 Stefanos Lappas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefanos Lappas
-/
module

public import LeanPool.MirekThiele.Estimates

/-! # Part 3 of the development: the bound on `‖Θ‖_r`, the closing of the main estimate
(2.13), (2.14) and the contraction `A ≤ A θ + C`, and the bridge from the hypotheses of
Theorem 1.4 to the stopping data (`namespace Bridge`). -/

@[expose] public section

open MeasureTheory

namespace MirekThiele

variable {d : ℕ}


/-! ## §2.6 continued: the bound on `‖Θ‖_r` (p. 53–54)

`Θ = ∑_{T ∈ 𝐓 ∪ parents(𝐏)} θ^T`, where `parents(𝐏) = parents(𝐒)₄` are the parents of the second
stopping cubes of `𝐒 ∩ 𝐒₄`
and
`𝐓` the other non-leaf cubes in no second stopping cube. The `parents(𝐏)`-portion is bounded in
`L^∞`
(bounded overlap of `parents(𝐒)₄`, p. 53); the `𝐓`-portion by the martingale estimate
(2.61)–(2.63) and
Lemma 2.71 (p. 54), with the auxiliary bounded function `v̂`, constant on the cubes of `𝐏_R` with
`[v̂]_P = [v]_P`. This part comes after the proof of Lemma 2.71. -/

section ThetaBound

variable {d : ℕ}

/-- A weighted Cauchy–Schwarz inequality: `∑ |a_i| |b_i| w_i ≤ (∑ a_i² w_i)^{1/2} (∑ b_i²
w_i)^{1/2}`.
[PROVED] -/
theorem sum_abs_mul_abs_mul_le {ι : Type*} (s : Finset ι) (a b w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i ∈ s, |a i| * |b i| * w i ≤
      Real.sqrt (∑ i ∈ s, a i ^ 2 * w i) * Real.sqrt (∑ i ∈ s, b i ^ 2 * w i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => |a i| * Real.sqrt (w i))
    (fun i => |b i| * Real.sqrt (w i))
  have e1 : ∀ i, |a i| * Real.sqrt (w i) * (|b i| * Real.sqrt (w i)) = |a i| * |b i| * w i := by
    intro i
    rw [show |a i| * Real.sqrt (w i) * (|b i| * Real.sqrt (w i)) =
      |a i| * |b i| * (Real.sqrt (w i) * Real.sqrt (w i)) by ring, Real.mul_self_sqrt (hw i)]
  have e2 : ∀ i, (|a i| * Real.sqrt (w i)) ^ 2 = a i ^ 2 * w i := fun i => by
    rw [mul_pow, sq_abs, Real.sq_sqrt (hw i)]
  have e3 : ∀ i, (|b i| * Real.sqrt (w i)) ^ 2 = b i ^ 2 * w i := fun i => by
    rw [mul_pow, sq_abs, Real.sq_sqrt (hw i)]
  simp only [e1, e2, e3] at h
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hw i))]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- `(∑_{T'} |[f]_{T'} − [f]_T|² |T'|)^{1/2} = Δ_T f |T|^{1/2}`. [PROVED] -/
theorem sqrt_dsq_eq (T : DyadicCube d) (f : (Fin d → ℝ) → ℝ) :
    Real.sqrt (dsq T f) = martDiff T f * Real.sqrt T.vol := by
  rw [← martDiff_sq_mul_vol, abs_of_nonneg (martDiff_nonneg T f), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (martDiff_nonneg T f)]

/-- The elementary estimate behind (2.61): for `|z|, |z'| > 1/8` and `|z|, |z'| ≤ M`,
`|x/z − x'/z'| ≤ (8 + 128 M)|x' − x| + 64 |x| |z' − z|`. [PROVED] -/
theorem abs_div_sub_div_le {x x' z z' M : ℝ} (hz : 1 / 8 < |z|) (hz' : 1 / 8 < |z'|)
    (hzM : |z| ≤ M) (hz'M : |z'| ≤ M) :
    |x / z - x' / z'| ≤ (8 + 128 * M) * |x' - x| + 64 * |x| * |z' - z| := by
  have hz0 : z ≠ 0 := fun h => by rw [h, abs_zero] at hz; norm_num at hz
  have hz'0 : z' ≠ 0 := fun h => by rw [h, abs_zero] at hz'; norm_num at hz'
  have e : x / z - x' / z' = (x - x') / z + x' * (z' - z) / (z * z') := by
    field_simp
    ring
  have h1 : |(x - x') / z| ≤ 8 * |x' - x| := by
    rw [abs_div, div_le_iff₀ (by linarith), abs_sub_comm]
    nlinarith [abs_nonneg (x' - x)]
  have h2 : |x' * (z' - z) / (z * z')| ≤ 64 * |x'| * |z' - z| := by
    rw [abs_div, abs_mul, abs_mul, div_le_iff₀ (by positivity)]
    have h3 : 1 ≤ 64 * (|z| * |z'|) := by nlinarith [mul_pos (sub_pos.mpr hz) (sub_pos.mpr hz')]
    calc |x'| * |z' - z| = |x'| * |z' - z| * 1 := by ring
      _ ≤ |x'| * |z' - z| * (64 * (|z| * |z'|)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 64 * |x'| * |z' - z| * (|z| * |z'|) := by ring
  have h4 : |x'| ≤ |x| + |x' - x| := by
    have := abs_add_le x (x' - x)
    rwa [add_sub_cancel] at this
  have h5 : |z' - z| ≤ 2 * M := by
    have := abs_sub z' z
    linarith
  have h6 : |x'| * |z' - z| ≤ (|x| + |x' - x|) * |z' - z| :=
    mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
  have h7 : |x' - x| * |z' - z| ≤ |x' - x| * (2 * M) :=
    mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
  calc |x / z - x' / z'| = |(x - x') / z + x' * (z' - z) / (z * z')| := by rw [e]
    _ ≤ |(x - x') / z| + |x' * (z' - z) / (z * z')| := abs_add_le _ _
    _ ≤ 8 * |x' - x| + 64 * |x'| * |z' - z| := add_le_add h1 h2
    _ ≤ (8 + 128 * M) * |x' - x| + 64 * |x| * |z' - z| := by nlinarith

/-- The companion estimate: `|y' − (y/z) z'| ≤ |y' − y| + 8 |y| |z' − z|` for `|z| > 1/8`. [PROVED]
-/
theorem abs_sub_div_mul_le {y y' z z' : ℝ} (hz : 1 / 8 < |z|) :
    |y' - y / z * z'| ≤ |y' - y| + 8 * |y| * |z' - z| := by
  have hz0 : z ≠ 0 := fun h => by rw [h, abs_zero] at hz; norm_num at hz
  have e : y' - y / z * z' = (y' - y) + y * (z - z') / z := by
    field_simp
    ring
  have h1 : |y * (z - z') / z| ≤ 8 * |y| * |z' - z| := by
    rw [abs_div, abs_mul, div_le_iff₀ (by linarith), abs_sub_comm z z']
    nlinarith [abs_nonneg y, abs_nonneg (z' - z), mul_nonneg (abs_nonneg y) (abs_nonneg (z' - z))]
  calc |y' - y / z * z'| = |(y' - y) + y * (z - z') / z| := by rw [e]
    _ ≤ |y' - y| + |y * (z - z') / z| := abs_add_le _ _
    _ ≤ |y' - y| + 8 * |y| * |z' - z| := add_le_add le_rfl h1

/-- **The martingale estimate (2.62)** for one cube `T`: with `x = [f]`, `y = [w]`, `z = [v]` on `T`
and its children, `|[v]| > 1/8` and `|[v]| ≤ M` on these cubes,
`|∑_{T'} ([f]_T/[v]_T − [f]_{T'}/[v]_{T'}) ([w]_{T'} − ([w]_T/[v]_T)[v]_{T'}) |T'||`
`≤ ((8+128M) Δ_T f Δ_T w + 8(8+128M) E_T w Δ_T f Δ_T v + 64 E_T f Δ_T v Δ_T w + 512 E_T f E_T w (Δ_T
v)²) |T|`.
[PROVED] -/
theorem abs_sum_children_mart_le (T : DyadicCube d) (f w v : (Fin d → ℝ) → ℝ) {M : ℝ}
    (hv : 1 / 8 < |avg T v|) (hv' : ∀ ε, 1 / 8 < |avg (T.child ε) v|) (hvM : |avg T v| ≤ M)
    (hv'M : ∀ ε, |avg (T.child ε) v| ≤ M) :
    |∑ ε : Fin d → Bool, (avg T f / avg T v - avg (T.child ε) f / avg (T.child ε) v) *
        (avg (T.child ε) w - avg T w / avg T v * avg (T.child ε) v) * (T.child ε).vol| ≤
      ((8 + 128 * M) * (martDiff T f * martDiff T w)
        + 8 * (8 + 128 * M) * (martAvg T w * martDiff T f * martDiff T v)
        + 64 * (martAvg T f * martDiff T v * martDiff T w)
        + 512 * (martAvg T f * martAvg T w * martDiff T v ^ 2)) * T.vol := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hvM
  set α₁ := 8 + 128 * M with hα₁
  have hα₁0 : 0 ≤ α₁ := by positivity
  set Ef := martAvg T f with hEf
  set Ew := martAvg T w with hEw
  have hEf0 : 0 ≤ Ef := abs_nonneg _
  have hEw0 : 0 ≤ Ew := abs_nonneg _
  have hvol : ∀ ε, 0 ≤ (T.child ε).vol := fun ε => (T.child ε).vol_pos.le
  -- the pointwise bound on each child
  have hpt : ∀ ε : Fin d → Bool,
      |(avg T f / avg T v - avg (T.child ε) f / avg (T.child ε) v) *
        (avg (T.child ε) w - avg T w / avg T v * avg (T.child ε) v) * (T.child ε).vol| ≤
      (α₁ * |avg (T.child ε) f - avg T f| + 64 * Ef * |avg (T.child ε) v - avg T v|) *
        (|avg (T.child ε) w - avg T w| + 8 * Ew * |avg (T.child ε) v - avg T v|) *
        (T.child ε).vol := by
    intro ε
    rw [abs_mul, abs_mul, abs_of_nonneg (hvol ε)]
    refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ ?_ (abs_nonneg _)
      (add_nonneg (mul_nonneg hα₁0 (abs_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) hEf0) (abs_nonneg _)))) (hvol ε)
    · exact abs_div_sub_div_le hv (hv' ε) hvM (hv'M ε)
    · exact abs_sub_div_mul_le hv
  -- expand the product
  have hexp : ∀ ε : Fin d → Bool,
      (α₁ * |avg (T.child ε) f - avg T f| + 64 * Ef * |avg (T.child ε) v - avg T v|) *
        (|avg (T.child ε) w - avg T w| + 8 * Ew * |avg (T.child ε) v - avg T v|) *
        (T.child ε).vol =
      α₁ * (|avg (T.child ε) f - avg T f| * |avg (T.child ε) w - avg T w| * (T.child ε).vol)
      + 8 * α₁ * Ew * (|avg (T.child ε) f - avg T f| * |avg (T.child ε) v - avg T v| *
          (T.child ε).vol)
      + 64 * Ef * (|avg (T.child ε) v - avg T v| * |avg (T.child ε) w - avg T w| *
          (T.child ε).vol)
      + 512 * Ef * Ew * (|avg (T.child ε) v - avg T v| * |avg (T.child ε) v - avg T v| *
          (T.child ε).vol) := fun ε => by ring
  -- the four Cauchy–Schwarz bounds
  have hvT := T.vol_pos
  have hsq : Real.sqrt T.vol * Real.sqrt T.vol = T.vol := Real.mul_self_sqrt hvT.le
  have cs : ∀ g₁ g₂ : (Fin d → ℝ) → ℝ,
      ∑ ε : Fin d → Bool, |avg (T.child ε) g₁ - avg T g₁| * |avg (T.child ε) g₂ - avg T g₂| *
        (T.child ε).vol ≤ martDiff T g₁ * martDiff T g₂ * T.vol := by
    intro g₁ g₂
    refine (sum_abs_mul_abs_mul_le Finset.univ (fun ε => avg (T.child ε) g₁ - avg T g₁)
      (fun ε => avg (T.child ε) g₂ - avg T g₂) (fun ε => (T.child ε).vol) hvol).trans (le_of_eq ?_)
    change Real.sqrt (dsq T g₁) * Real.sqrt (dsq T g₂) = _
    rw [sqrt_dsq_eq, sqrt_dsq_eq,
      show martDiff T g₁ * Real.sqrt T.vol * (martDiff T g₂ * Real.sqrt T.vol) =
        martDiff T g₁ * martDiff T g₂ * (Real.sqrt T.vol * Real.sqrt T.vol) by ring, hsq]
  have cvv : ∑ ε : Fin d → Bool, |avg (T.child ε) v - avg T v| * |avg (T.child ε) v - avg T v| *
      (T.child ε).vol = martDiff T v ^ 2 * T.vol := by
    rw [← sq_abs (martDiff T v), martDiff_sq_mul_vol, dsq]
    exact Finset.sum_congr rfl fun ε _ => by rw [abs_mul_abs_self, sq]
  calc |∑ ε : Fin d → Bool, (avg T f / avg T v - avg (T.child ε) f / avg (T.child ε) v) *
        (avg (T.child ε) w - avg T w / avg T v * avg (T.child ε) v) * (T.child ε).vol|
      ≤ ∑ ε : Fin d → Bool, |(avg T f / avg T v - avg (T.child ε) f / avg (T.child ε) v) *
        (avg (T.child ε) w - avg T w / avg T v * avg (T.child ε) v) * (T.child ε).vol| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ε : Fin d → Bool,
        (α₁ * |avg (T.child ε) f - avg T f| + 64 * Ef * |avg (T.child ε) v - avg T v|) *
          (|avg (T.child ε) w - avg T w| + 8 * Ew * |avg (T.child ε) v - avg T v|) *
          (T.child ε).vol := Finset.sum_le_sum fun ε _ => hpt ε
    _ = α₁ * ∑ ε : Fin d → Bool, |avg (T.child ε) f - avg T f| * |avg (T.child ε) w - avg T w| *
          (T.child ε).vol
        + 8 * α₁ * Ew * ∑ ε : Fin d → Bool, |avg (T.child ε) f - avg T f| *
            |avg (T.child ε) v - avg T v| * (T.child ε).vol
        + 64 * Ef * ∑ ε : Fin d → Bool, |avg (T.child ε) v - avg T v| *
            |avg (T.child ε) w - avg T w| * (T.child ε).vol
        + 512 * Ef * Ew * ∑ ε : Fin d → Bool, |avg (T.child ε) v - avg T v| *
            |avg (T.child ε) v - avg T v| * (T.child ε).vol := by
        simp only [hexp, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ α₁ * (martDiff T f * martDiff T w * T.vol)
        + 8 * α₁ * Ew * (martDiff T f * martDiff T v * T.vol)
        + 64 * Ef * (martDiff T v * martDiff T w * T.vol)
        + 512 * Ef * Ew * (martDiff T v ^ 2 * T.vol) := by
        rw [cvv]
        gcongr
        · exact cs f w
        · exact cs f v
        · exact cs v w
    _ = _ := by ring

/-- `‖f‖_r ≤ M |R|^{1/r}` for `f` supported on `R` with `|f| ≤ M`. [PROVED] -/
theorem TestFun.lpNorm_le_of_abs_le (f : TestFun d) {R : DyadicCube d}
    (hf : SupportedOn (f : (Fin d → ℝ) → ℝ) R) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, |(f : (Fin d → ℝ) → ℝ) x| ≤ M) {r : ℝ} (hr : 0 < r) :
    lpNorm (f : (Fin d → ℝ) → ℝ) r ≤ M * R.vol ^ (1 / r) := by
  have hV := R.vol_pos
  have h : ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ r ≤ M ^ r * R.vol := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hf x hx, abs_zero, Real.zero_rpow hr.ne'])]
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := R.toSet)
      (f := fun x => |(f : (Fin d → ℝ) → ℝ) x| ^ r) (C := M ^ r)
      (by rw [R.volume_toSet]; exact ENNReal.ofReal_lt_top) fun x _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) (hM x) hr.le
    rw [Real.norm_eq_abs, measureReal_def, R.volume_toSet, ENNReal.toReal_ofReal hV.le] at h1
    exact (le_abs_self _).trans h1
  refine (TestFun.lpNorm_le_rpow_of_integral_le f hr h).trans (le_of_eq ?_)
  rw [Real.mul_rpow (Real.rpow_nonneg hM0 _) hV.le, ← Real.rpow_mul hM0, mul_one_div_cancel hr.ne',
    Real.rpow_one]

/-- `|[f]_T| ≤ M` when `|f| ≤ M`. [PROVED] -/
theorem abs_avg_le_of_abs_le (T : DyadicCube d) {f : (Fin d → ℝ) → ℝ} {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : |avg T f| ≤ M := by
  have hV := T.vol_pos
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := T.toSet) (f := f) (C := M)
    (by rw [T.volume_toSet]; exact ENNReal.ofReal_lt_top) fun x _ => by
      rw [Real.norm_eq_abs]; exact hM x
  rw [Real.norm_eq_abs, measureReal_def, T.volume_toSet, ENNReal.toReal_ofReal hV.le] at h1
  rw [avg, abs_div, abs_of_pos hV, div_le_iff₀ hV]
  exact h1

/-- `Δ_T` depends only on the averages over `T` and its children. [PROVED] -/
theorem martDiff_congr_avg (T : DyadicCube d) {f g : (Fin d → ℝ) → ℝ} (h : avg T f = avg T g)
    (hc : ∀ ε, avg (T.child ε) f = avg (T.child ε) g) : martDiff T f = martDiff T g := by
  simp only [martDiff, h, hc]

theorem avg_const_smul (T : DyadicCube d) (c : ℝ) (f : (Fin d → ℝ) → ℝ) :
    avg T (c • f) = c * avg T f := by
  simp only [avg, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, mul_div_assoc]

/-- `∑_{P ∈ s} f 𝟙_P = f` for a partition `s` of `R` and `f` supported on `R`. [PROVED] -/
theorem TestFun.sum_truncateₗ_of_partition (s : Finset (DyadicCube d))
    (hdisj : (↑s : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet) {R : DyadicCube d}
    (hsub : ∀ P ∈ s, P.toSet ⊆ R.toSet) (hcover : ∀ x ∈ R.toSet, ∃ P ∈ s, x ∈ P.toSet)
    (f : TestFun d) (hf : SupportedOn (f : (Fin d → ℝ) → ℝ) R) :
    ∑ P ∈ s, TestFun.truncateₗ P f = f := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  funext x
  simp only [Finset.sum_apply, TestFun.coe_truncateₗ, truncate]
  by_cases hx : x ∈ R.toSet
  · obtain ⟨P₀, hP₀, hxP₀⟩ := hcover x hx
    rw [Finset.sum_eq_single P₀]
    · exact Set.indicator_of_mem hxP₀ _
    · intro P hP hne
      exact Set.indicator_of_notMem
        (fun hx' => Set.disjoint_left.mp (hdisj hP hP₀ hne) hx' hxP₀) _
    · exact fun h => absurd hP₀ h
  · rw [hf x hx]
    exact Finset.sum_eq_zero fun P hP => Set.indicator_of_notMem (fun h => hx (hsub P hP h)) _

theorem integral_indicator_toSet (P : DyadicCube d) (f : (Fin d → ℝ) → ℝ) :
    ∫ x, P.toSet.indicator f x = ∫ x in P.toSet, f x :=
  integral_indicator P.measurableSet_toSet

/-- `[f]_T |T| = ∑_ε [f]_{T_ε} |T_ε|` over the children `T_ε`. [PROVED] -/
theorem avg_mul_vol_children' (T : DyadicCube d) (f : TestFun d) :
    avg T f * T.vol = ∑ ε : Fin d → Bool, avg (T.child ε) f * (T.child ε).vol := by
  rw [StoppingData.avg_mul_vol_children T f, StoppingData.children,
    Finset.sum_image fun ε _ ε' _ h => T.child_injective h]

theorem martDiff_const_smul (T : DyadicCube d) (c : ℝ) (f : (Fin d → ℝ) → ℝ) :
    martDiff T (c • f) = |c| * martDiff T f := by
  simp only [martDiff, avg_const_smul]
  have h0 : 0 ≤ T.vol⁻¹ * ∑ ε : Fin d → Bool,
      |avg (T.child ε) f - avg T f| ^ 2 * (T.child ε).vol :=
    mul_nonneg (inv_nonneg.mpr T.vol_pos.le)
      (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (DyadicCube.vol_pos _).le)
  rw [← Real.sqrt_sq (abs_nonneg c), ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [← mul_sub, abs_mul, mul_pow]
  ring

/-- The common polynomial majorant for the two martingale coefficient estimates. -/
private theorem martingale_coefficient_bounds {M : ℝ} (hM : 0 ≤ M) :
    (8 + 128 * M ≤ (8 + 192 * M) * (1 + 8 * M)) ∧
    (8 * (8 + 128 * M) * M ≤ (8 + 192 * M) * (1 + 8 * M)) ∧
    (64 * M ≤ (8 + 192 * M) * (1 + 8 * M)) ∧
    (512 * M ^ 2 ≤ (8 + 192 * M) * (1 + 8 * M)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith only [hM, sq_nonneg M]

/-- The product majorant for the mixed martingale coefficients. -/
private theorem mixed_coefficient_bounds {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ((8 + 128 * M) * (8 + 128 * N) ≤ (8 + 192 * M) * (8 + 192 * N)) ∧
    ((8 + 128 * M) * (64 * N) ≤ (8 + 192 * M) * (8 + 192 * N)) ∧
    (64 * M * (8 + 128 * N) ≤ (8 + 192 * M) * (8 + 192 * N)) ∧
    (64 * M * (64 * N) ≤ (8 + 192 * M) * (8 + 192 * N)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith only [hM, hN, mul_nonneg hM hN]

namespace StoppingData

variable {n : ℕ} (D : StoppingData d n)


section ThetaSplit

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

open Classical in
/-- The non-leaf cubes `T ⊆ R` in no second stopping cube: the index set of `Θ`. -/
noncomputable def setF : Finset (DyadicCube d) :=
  (nonleaf (D.second R hR hRs hFR).N R).filter (fun T => (D.second R hR hRs hFR).NotInStopping T)

/-- `parents(𝐏)`: the cubes of `setF` which are parents of cubes of `𝐒 ∩ 𝐒₄` (p. 53). -/
noncomputable def setP : Finset (DyadicCube d) :=
  (D.setF hR hRs hFR).filter (fun T => T ∈ (D.second R hR hRs hFR).Pbar4)

/-- `𝐓`: the other cubes of `setF` (p. 53). -/
noncomputable def setT : Finset (DyadicCube d) :=
  (D.setF hR hRs hFR).filter (fun T => T ∉ (D.second R hR hRs hFR).Pbar4)

/-- `Θ_parents(𝐏) = ∑_{T ∈ parents(𝐏)} θ^T`. -/
noncomputable def ThetaP : TestFun d := ∑ T ∈ D.setP hR hRs hFR, D.thetaT hR hRs hFR T

/-- `Θ_𝐓 = ∑_{T ∈ 𝐓} θ^T`. -/
noncomputable def ThetaT : TestFun d := ∑ T ∈ D.setT hR hRs hFR, D.thetaT hR hRs hFR T

/-- `Θ = Θ_parents(𝐏) + Θ_𝐓`. [PROVED] -/
theorem Theta_eq_add : D.Theta hR hRs hFR = D.ThetaP hR hRs hFR + D.ThetaT hR hRs hFR := by
  rw [Theta, ThetaP, ThetaT, setP, setT, Finset.sum_filter_add_sum_filter_not]
  rfl

open Classical in
theorem mem_setF {T : DyadicCube d} :
    T ∈ D.setF hR hRs hFR ↔ T ∈ nonleaf (D.second R hR hRs hFR).N R ∧
      (D.second R hR hRs hFR).NotInStopping T := Finset.mem_filter

theorem mem_setP {T : DyadicCube d} :
    T ∈ D.setP hR hRs hFR ↔ T ∈ D.setF hR hRs hFR ∧ T ∈ (D.second R hR hRs hFR).Pbar4 :=
  Finset.mem_filter

theorem mem_setT {T : DyadicCube d} :
    T ∈ D.setT hR hRs hFR ↔ T ∈ D.setF hR hRs hFR ∧ T ∉ (D.second R hR hRs hFR).Pbar4 :=
  Finset.mem_filter

/-- A non-leaf cube belongs to the tree of the second stopping time, and so do its children.
[PROVED] -/
theorem mem_second_tree_of_mem_nonleaf {T : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) : T ∈ (D.second R hR hRs hFR).tree := by
  obtain ⟨L', hL', hT⟩ := Finset.mem_biUnion.mp hT
  rw [Finset.mem_range] at hL'
  exact D.mem_second_tree_of_mem_level hR hRs hFR hL'.le hT

theorem child_mem_second_tree_of_mem_nonleaf {T : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) (ε : Fin d → Bool) :
    T.child ε ∈ (D.second R hR hRs hFR).tree := by
  obtain ⟨L', hL', hT⟩ := Finset.mem_biUnion.mp hT
  rw [Finset.mem_range] at hL'
  exact D.mem_second_tree_of_mem_level hR hRs hFR hL'
    (mem_level_succ_of_mem_children hT (mem_children.mpr ⟨ε, rfl⟩))

/-- The unit `K = |Q|^{-1/q} ‖g‖_q` of the bounds for `φ_T`. -/
noncomputable def KQ : ℝ := D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q

theorem KQ_nonneg : 0 ≤ D.KQ := mul_nonneg (Real.rpow_nonneg D.Q.vol_pos.le _) (lpNorm_nonneg _ _)

/-- `∑_{T' child of T} ψ_{T'} 𝟙_{T'}(x) = ψ_{T'(x)}` for `x ∈ T`, where `T'(x)` is the child
containing `x`. [PROVED] -/
theorem sum_children_psiT_ind_apply {T : DyadicCube d} {x : Fin d → ℝ} (hx : x ∈ T.toSet) :
    ((∑ T' ∈ children T, D.psiT hR hRs hFR T' • TestFun.ind T' : TestFun d) :
      (Fin d → ℝ) → ℝ) x = D.psiT hR hRs hFR (T.childAt x) := by
  rw [Submodule.coe_sum, Finset.sum_apply, children,
    Finset.sum_image fun ε _ ε' _ h => T.child_injective h]
  set ε₀ : Fin d → Bool := fun i => decide ((2 : ℝ) ^ (T.m - 1) * (2 * T.l i + 1) ≤ x i) with hε₀
  have hx0 : x ∈ (T.child ε₀).toSet := T.mem_childAt hx
  rw [Finset.sum_eq_single ε₀]
  · rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hx0, Pi.one_apply,
      smul_eq_mul, mul_one]
    rfl
  · intro ε _ hne
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
      Set.indicator_of_notMem (fun h => Set.disjoint_left.mp (T.child_disjoint hne) h hx0),
      smul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem CφT_nonneg : 0 ≤ D.CφT :=
  add_nonneg D.Cφ_nonneg (mul_nonneg (by norm_num) D.locConst_nonneg)

theorem Cψ_nonneg : 0 ≤ D.Cψ hR hRs hFR :=
  add_nonneg (D.second R hR hRs hFR).Cφ_nonneg
    (mul_nonneg (by norm_num) (D.second R hR hRs hFR).locConst_nonneg)

/-- `|θ^T(x)| ≤ 2 C_{φ,T} K C_ψ 𝟙_T(x)` for a non-leaf cube `T`: `θ^T = φ_T(ψ_T − ψ_{T'(x)})` on the
child `T'(x)` of `T` containing `x`. [PROVED] -/
theorem abs_thetaT_apply_le (hG : D.GBound) {T : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) (x : Fin d → ℝ) :
    |(D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x| ≤
      2 * (D.CφT * D.KQ) * D.Cψ hR hRs hFR * T.toSet.indicator 1 x := by
  have hT' := D.mem_second_tree_of_mem_nonleaf hR hRs hFR hT
  have hTR : T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp hT).1
  have hφ : |D.phiT R T| ≤ D.CφT * D.KQ :=
    D.abs_phiT_le hR hRs hG (D.second_tree_subset hR hRs hFR hT') hTR
  have hψ : |D.psiT hR hRs hFR T| ≤ D.Cψ hR hRs hFR := D.abs_psiT_le hR hRs hFR hT'
  have hC0 : 0 ≤ D.CφT * D.KQ := mul_nonneg D.CφT_nonneg D.KQ_nonneg
  by_cases hx : x ∈ T.toSet
  · have hc : |D.psiT hR hRs hFR (T.childAt x)| ≤ D.Cψ hR hRs hFR :=
      D.abs_psiT_le hR hRs hFR (D.child_mem_second_tree_of_mem_nonleaf hR hRs hFR hT _)
    rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, thetaT, Submodule.coe_smul, Pi.smul_apply,
      Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
      Set.indicator_of_mem hx, Pi.one_apply, D.sum_children_psiT_ind_apply hR hRs hFR hx,
      smul_eq_mul, smul_eq_mul, mul_one, abs_mul]
    calc |D.phiT R T| * |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.childAt x)|
        ≤ (D.CφT * D.KQ) * (D.Cψ hR hRs hFR + D.Cψ hR hRs hFR) :=
          mul_le_mul hφ ((abs_sub _ _).trans (add_le_add hψ hc)) (abs_nonneg _) hC0
      _ = 2 * (D.CφT * D.KQ) * D.Cψ hR hRs hFR := by ring
  · rw [Set.indicator_of_notMem hx, mul_zero, D.thetaT_supportedOn hR hRs hFR T x hx, abs_zero]

/-- `|Θ_parents(𝐏)(x)| ≤ 2 C_{φ,T} K C_ψ · 2^d/ε`, by the bounded overlap of `parents(𝐒)₄` (p.
53). [PROVED] -/
theorem abs_ThetaP_apply_le (hG : D.GBound) (x : Fin d → ℝ) :
    |(D.ThetaP hR hRs hFR : (Fin d → ℝ) → ℝ) x| ≤
      2 * (D.CφT * D.KQ) * D.Cψ hR hRs hFR * (2 ^ d / D.ε) := by
  classical
  have hc0 : 0 ≤ 2 * (D.CφT * D.KQ) * D.Cψ hR hRs hFR :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg D.CφT_nonneg D.KQ_nonneg))
      (D.Cψ_nonneg hR hRs hFR)
  rw [ThetaP, Submodule.coe_sum, Finset.sum_apply]
  calc |∑ T ∈ D.setP hR hRs hFR, (D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x|
      ≤ ∑ T ∈ D.setP hR hRs hFR, |(D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ D.setP hR hRs hFR, 2 * (D.CφT * D.KQ) * D.Cψ hR hRs hFR * T.toSet.indicator 1 x :=
        Finset.sum_le_sum fun T hT => D.abs_thetaT_apply_le hR hRs hFR hG
          ((D.mem_setF hR hRs hFR).mp ((D.mem_setP hR hRs hFR).mp hT).1).1 x
    _ = 2 * (D.CφT * D.KQ) * D.Cψ hR hRs hFR *
          (((D.setP hR hRs hFR).filter fun T => x ∈ T.toSet).card : ℝ) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_boole]
        exact Finset.sum_congr rfl fun T _ => by simp [Set.indicator_apply]
    _ ≤ 2 * (D.CφT * D.KQ) * D.Cψ hR hRs hFR * (2 ^ d / D.ε) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        refine le_trans ?_ ((D.second R hR hRs hFR).card_Pbar4_filter_le x)
        exact_mod_cast Finset.card_le_card (Finset.monotone_filter_left _
          fun T hT => ((D.mem_setP hR hRs hFR).mp hT).2)

theorem ThetaP_supportedOn : SupportedOn (D.ThetaP hR hRs hFR) R := fun x hx => by
  rw [ThetaP, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  exact D.thetaT_supportedOn hR hRs hFR T x fun h => hx (((mem_nonleaf_iff D.hd).mp
    ((D.mem_setF hR hRs hFR).mp ((D.mem_setP hR hRs hFR).mp hT).1).1).1 h)

theorem ThetaT_supportedOn : SupportedOn (D.ThetaT hR hRs hFR) R := fun x hx => by
  rw [ThetaT, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  exact D.thetaT_supportedOn hR hRs hFR T x fun h => hx (((mem_nonleaf_iff D.hd).mp
    ((D.mem_setF hR hRs hFR).mp ((D.mem_setT hR hRs hFR).mp hT).1).1).1 h)

/-- **The `parents(𝐏)`-portion** (p. 53): `‖Θ_parents(𝐏)‖_r ≤ 2 C_{φ,T} C_ψ (2^d/ε) · |Q|^{-1/q}
‖g‖_q · |R|^{1/r}`.
[PROVED] -/
theorem lpNorm_ThetaP_le (hG : D.GBound) :
    lpNorm (D.ThetaP hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ≤
      2 * D.CφT * D.Cψ hR hRs hFR * (2 ^ d / D.ε) * D.KQ * R.vol ^ (1 / D.r) := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hε := D.ε_pos
  have hM0 : 0 ≤ 2 * (D.CφT * D.KQ) * D.Cψ hR hRs hFR * (2 ^ d / D.ε) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg D.CφT_nonneg D.KQ_nonneg))
      (D.Cψ_nonneg hR hRs hFR)) (by positivity)
  have h := TestFun.lpNorm_le_of_abs_le (D.ThetaP hR hRs hFR) (D.ThetaP_supportedOn hR hRs hFR)
    hM0 (D.abs_ThetaP_apply_le hR hRs hFR hG) hr0
  refine h.trans (le_of_eq ?_)
  ring

end ThetaSplit

section ThetaTPortion

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

/-- The auxiliary function `v̂ = ∑_{P ∈ 𝐏_R} [v]_P 𝟙_P` (p. 53): constant on the cubes of `𝐏_R` with
`[v̂]_P = [v]_P`. -/
noncomputable def vhat : TestFun d :=
  ∑ P ∈ D.partR hR hRs hFR, avg P (D.vP R) • TestFun.ind P

theorem vhat_apply {P : DyadicCube d} {x : Fin d → ℝ} (hP : P ∈ D.partR hR hRs hFR)
    (hx : x ∈ P.toSet) : (D.vhat hR hRs hFR : (Fin d → ℝ) → ℝ) x = avg P (D.vP R) := by
  rw [vhat, Submodule.coe_sum, Finset.sum_apply, Finset.sum_eq_single P]
  · rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hx, Pi.one_apply,
      smul_eq_mul, mul_one]
  · intro P' hP' hne
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_notMem
      (fun h => Set.disjoint_left.mp (D.partR_pairwiseDisjoint hR hRs hFR hP' hP hne) h hx),
      smul_zero]
  · exact fun h => absurd hP h

theorem vhat_apply_of_notMem {x : Fin d → ℝ} (hx : x ∉ R.toSet) :
    (D.vhat hR hRs hFR : (Fin d → ℝ) → ℝ) x = 0 := by
  rw [vhat, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
    Set.indicator_of_notMem (fun h => hx (D.subset_of_mem_partR hR hRs hFR hP h)), smul_zero]

/-- The bound `M_v = (2^d B/ε)^{1/r}` for `|[v]_P|` on good cubes of the second stopping time, hence
for `v̂`. -/
noncomputable def Mv : ℝ := (2 ^ d * D.B / D.ε) ^ (1 / D.r)

theorem Mv_pos : 0 < D.Mv := by
  have := D.ε_pos
  have : 0 < D.B := by linarith [D.hB]
  unfold Mv
  positivity

theorem Mv_nonneg : 0 ≤ D.Mv := D.Mv_pos.le

/-- `|[v]_P| ≤ M_v` on good cubes of the second stopping time, by Jensen's inequality and (2.34).
[PROVED] -/
theorem abs_avg_vP_le_Mv {P : DyadicCube d} (hP : (D.second R hR hRs hFR).Good P) :
    |avg P (D.vP R)| ≤ D.Mv := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hP0 := P.vol_pos
  have hR0 := R.vol_pos
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have h1 := abs_avg_mul_rpow_le P (D.vP R) D.hr.le
  have h2 : lpNorm (TestFun.truncateₗ P (D.vP R) : (Fin d → ℝ) → ℝ) D.r ≤
      (2 ^ d * D.B / D.ε * P.vol) ^ (1 / D.r) := by
    refine TestFun.lpNorm_le_rpow_of_integral_le _ hr0 ?_
    rw [← lpNorm_rpow_eq_integral hr0 (TestFun.memLp (TestFun.truncateₗ P (D.vP R)).2 _),
      TestFun.lpNorm_truncateₗ_rpow P _ hr0]
    refine (D.setIntegral_vP_rpow_le hR hRs hFR hP).trans (le_of_eq ?_)
    calc 2 ^ d / D.ε * (P.vol / R.vol) * (D.B * R.vol)
        = 2 ^ d / D.ε * D.B * (P.vol / R.vol * R.vol) := by ring
      _ = 2 ^ d * D.B / D.ε * P.vol := by
          rw [div_mul_cancel₀ _ hR0.ne']
          ring
  rw [Real.mul_rpow (by positivity) hP0.le] at h2
  exact le_of_mul_le_mul_right (h1.trans h2) (Real.rpow_pos_of_pos hP0 _)

theorem abs_vhat_le (x : Fin d → ℝ) : |(D.vhat hR hRs hFR : (Fin d → ℝ) → ℝ) x| ≤ D.Mv := by
  by_cases hx : x ∈ R.toSet
  · rw [← D.partR_cover hR hRs hFR, Set.mem_iUnion₂] at hx
    obtain ⟨P, hP, hxP⟩ := hx
    rw [D.vhat_apply hR hRs hFR hP hxP]
    exact D.abs_avg_vP_le_Mv hR hRs hFR (D.good_of_mem_partR hR hRs hFR hP)
  · rw [D.vhat_apply_of_notMem hR hRs hFR hx, abs_zero]
    exact D.Mv_nonneg

theorem vP_eq_sum_truncateₗ_partR :
    D.vP R = ∑ P ∈ D.partR hR hRs hFR, TestFun.truncateₗ P (D.vP R) :=
  (TestFun.sum_truncateₗ_of_partition _ (D.partR_pairwiseDisjoint hR hRs hFR)
    (fun P hP => D.subset_of_mem_partR hR hRs hFR hP) (fun x hx => by
      rw [← D.partR_cover hR hRs hFR, Set.mem_iUnion₂] at hx
      obtain ⟨P, hP, h⟩ := hx
      exact ⟨P, hP, h⟩) (D.vP R) (D.vP_supp R hR.1)).symm

/-- `[v̂]_T = [v]_T` for a cube `T ⊆ R` which is a union of cubes of `𝐏_R`. [PROVED] -/
theorem avg_vhat_eq {T : DyadicCube d}
    (h : ∀ P ∈ D.partR hR hRs hFR, P.toSet ⊆ T.toSet ∨ Disjoint P.toSet T.toSet) :
    avg T (D.vhat hR hRs hFR) = avg T (D.vP R) := by
  have key : ∀ P ∈ D.partR hR hRs hFR,
      TestFun.integralₗ (avg P (D.vP R) • TestFun.truncateₗ T (TestFun.ind P)) =
        TestFun.integralₗ (TestFun.truncateₗ T (TestFun.truncateₗ P (D.vP R))) := by
    intro P hP
    rcases h P hP with hsub | hdis
    · rw [TestFun.truncateₗ_of_supportedOn
          (fun x hx => TestFun.ind_supportedOn P x fun h => hx (hsub h)),
        TestFun.truncateₗ_of_supportedOn
          (fun x hx => TestFun.truncateₗ_supportedOn P (D.vP R) x fun h => hx (hsub h)),
        map_smul, TestFun.integralₗ_truncateₗ, TestFun.integralₗ_apply, TestFun.integral_ind,
        smul_eq_mul]
    · rw [← TestFun.truncateₗ_ind P, TestFun.truncateₗ_truncateₗ_of_disjoint hdis.symm,
        TestFun.truncateₗ_truncateₗ_of_disjoint hdis.symm, smul_zero]
  have e : TestFun.truncateₗ T (D.vhat hR hRs hFR) =
      ∑ P ∈ D.partR hR hRs hFR, avg P (D.vP R) • TestFun.truncateₗ T (TestFun.ind P) := by
    rw [vhat, map_sum]
    simp only [map_smul]
  have h1 := TestFun.integralₗ_truncateₗ T (D.vhat hR hRs hFR)
  have h2 := TestFun.integralₗ_truncateₗ T (D.vP R)
  rw [e, map_sum, Finset.sum_congr rfl key, ← map_sum TestFun.integralₗ,
    ← map_sum (TestFun.truncateₗ T), ← D.vP_eq_sum_truncateₗ_partR hR hRs hFR] at h1
  rw [h1] at h2
  exact mul_right_cancel₀ T.vol_pos.ne' h2

theorem avg_vhat_eq_of_mem_setF {T : DyadicCube d} (hT : T ∈ D.setF hR hRs hFR) :
    avg T (D.vhat hR hRs hFR) = avg T (D.vP R) := by
  obtain ⟨hTn, hTs⟩ := (D.mem_setF hR hRs hFR).mp hT
  exact D.avg_vhat_eq hR hRs hFR
    fun P hP => D.subset_or_disjoint_of_mem_partR hR hRs hFR hTn hTs hP

theorem child_avg_vhat_eq_of_mem_setF {T : DyadicCube d} (hT : T ∈ D.setF hR hRs hFR)
    (ε : Fin d → Bool) :
    avg (T.child ε) (D.vhat hR hRs hFR) = avg (T.child ε) (D.vP R) := by
  obtain ⟨hTn, hTs⟩ := (D.mem_setF hR hRs hFR).mp hT
  exact D.avg_vhat_eq hR hRs hFR
    fun P hP => D.child_subset_or_disjoint_of_mem_partR hR hRs hFR hTn hTs
      (mem_children.mpr ⟨ε, rfl⟩) hP

theorem abs_avg_vP_le_Mv_of_mem_setF {T : DyadicCube d} (hT : T ∈ D.setF hR hRs hFR) :
    |avg T (D.vP R)| ≤ D.Mv := by
  rw [← D.avg_vhat_eq_of_mem_setF hR hRs hFR hT]
  exact abs_avg_le_of_abs_le T (D.abs_vhat_le hR hRs hFR)

theorem child_abs_avg_vP_le_Mv_of_mem_setF {T : DyadicCube d} (hT : T ∈ D.setF hR hRs hFR)
    (ε : Fin d → Bool) : |avg (T.child ε) (D.vP R)| ≤ D.Mv := by
  rw [← D.child_avg_vhat_eq_of_mem_setF hR hRs hFR hT ε]
  exact abs_avg_le_of_abs_le _ (D.abs_vhat_le hR hRs hFR)

/-- `|[v]_T| > 1/8` for `T ∈ setF`, by (2.30). [PROVED] -/
theorem lt_abs_avg_vP_of_mem_setF {T : DyadicCube d} (hT : T ∈ D.setF hR hRs hFR) :
    1 / 8 < |avg T (D.vP R)| := by
  obtain ⟨hTn, hTs⟩ := (D.mem_setF hR hRs hFR).mp hT
  exact D.second_bound_2_30 hR hRs hFR (D.mem_second_tree_of_mem_nonleaf hR hRs hFR hTn)
    ((D.second R hR hRs hFR).not_in_P4_of_notInStopping hTs)

/-- A child of a cube `T ∈ 𝐓` lies in no cube of `𝐒₄`: otherwise it would be a stopping cube of
`𝐒 ∩ 𝐒₄` and `T ∈ parents(𝐒)₄`. [PROVED] -/
theorem child_not_in_P4_of_mem_setT {T : DyadicCube d} (hT : T ∈ D.setT hR hRs hFR)
    (ε : Fin d → Bool) :
    ∀ S ∈ (D.second R hR hRs hFR).P4, ¬ (T.child ε).toSet ⊆ S.toSet := by
  intro S hS hsub
  obtain ⟨hTF, hT4⟩ := (D.mem_setT hR hRs hFR).mp hT
  obtain ⟨_, hTs⟩ := (D.mem_setF hR hRs hFR).mp hTF
  obtain ⟨S', hS', hSS'⟩ := exists_maximal_superset (D.second R hR hRs hFR).hd
    (D.second R hR hRs hFR).union_subset_tree ((D.second R hR hRs hFR).P4_subset hS)
  have hcS' : (T.child ε).toSet ⊆ S'.toSet := hsub.trans hSS'
  have hTS' : ¬ T.toSet ⊆ S'.toSet := hTs S' hS'
  have hcT := T.child_subset ε
  have hS'T : S'.toSet ⊆ T.toSet := by
    rcases le_total S'.m T.m with hm | hm
    · rcases DyadicCube.subset_or_disjoint S' T hm with h | h
      · exact h
      · exact absurd (hcT (T.child ε).corner_mem)
          (Set.disjoint_left.mp h (hcS' (T.child ε).corner_mem))
    · rcases DyadicCube.subset_or_disjoint T S' hm with h | h
      · exact absurd h hTS'
      · exact absurd (hcS' (T.child ε).corner_mem)
          (Set.disjoint_left.mp h (hcT (T.child ε).corner_mem))
  have hm1 := DyadicCube.m_le_of_subset D.hd hcS'
  have hm2 := DyadicCube.m_le_of_subset D.hd hS'T
  have hne : S' ≠ T := fun e => hTS' (e ▸ subset_rfl)
  have hm3 : S'.m < T.m :=
    lt_of_le_of_ne hm2 fun e => hne (DyadicCube.eq_of_subset_of_m_eq hS'T e)
  have hm' : (T.child ε).m = T.m - 1 := rfl
  have e1 : T.child ε = S' := DyadicCube.eq_of_subset_of_m_eq hcS' (by omega)
  have hm4 := DyadicCube.m_le_of_subset D.hd hSS'
  have hm5 := DyadicCube.m_le_of_subset D.hd hsub
  rw [e1] at hm5
  have e2 : S = S' := DyadicCube.eq_of_subset_of_m_eq hSS' (le_antisymm hm4 hm5)
  rw [e2] at hS
  have hmem : T.child ε ∈ (D.second R hR hRs hFR).PstIn4 := by
    rw [(D.second R hR hRs hFR).mem_PstIn4, e1]
    exact ⟨hS', hS⟩
  exact hT4 ((D.second R hR hRs hFR).mem_Pbar4.mpr ⟨T.child ε, hmem, T.parent_child ε⟩)

theorem lt_abs_avg_vP_child_of_mem_setT {T : DyadicCube d} (hT : T ∈ D.setT hR hRs hFR)
    (ε : Fin d → Bool) : 1 / 8 < |avg (T.child ε) (D.vP R)| := by
  obtain ⟨hTn, _⟩ := (D.mem_setF hR hRs hFR).mp ((D.mem_setT hR hRs hFR).mp hT).1
  exact D.second_bound_2_30 hR hRs hFR (D.child_mem_second_tree_of_mem_nonleaf hR hRs hFR hTn ε)
    (D.child_not_in_P4_of_mem_setT hR hRs hFR hT ε)

theorem ne_zero_of_lt_abs {z : ℝ} (hz : 1 / 8 < |z|) : z ≠ 0 := fun h => by
  rw [h, abs_zero] at hz
  norm_num at hz

/-- Pair a scaled cube difference with a test function by summing over its children. -/
private theorem integral_smul_cube_difference_mul (T : DyadicCube d) (w : TestFun d)
    (a : ℝ) (c : DyadicCube d → ℝ) :
    ∫ x, ((a • (c T • TestFun.ind T -
        ∑ P ∈ children T, c P • TestFun.ind P) : TestFun d) : (Fin d → ℝ) → ℝ) x *
          (w : (Fin d → ℝ) → ℝ) x =
      a * ∑ ε : Fin d → Bool, (c T - c (T.child ε)) * avg (T.child ε) w *
        (T.child ε).vol := by
  let θ : TestFun d := a • (c T • TestFun.ind T - ∑ P ∈ children T, c P • TestFun.ind P)
  change ∫ x, (θ : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x = _
  have hint : ∀ P : DyadicCube d,
      Integrable (P.toSet.indicator (w : (Fin d → ℝ) → ℝ)) volume :=
    fun P => (TestFun.integrable w.2).indicator P.measurableSet_toSet
  have e : ∀ x, (θ : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x =
      a * (c T * T.toSet.indicator (w : (Fin d → ℝ) → ℝ) x
        - ∑ T' ∈ children T, c T' *
            T'.toSet.indicator (w : (Fin d → ℝ) → ℝ) x) := by
    intro x
    have hi : ∀ P : DyadicCube d, P.toSet.indicator (1 : (Fin d → ℝ) → ℝ) x *
        (w : (Fin d → ℝ) → ℝ) x = P.toSet.indicator (w : (Fin d → ℝ) → ℝ) x := fun P => by
      by_cases hx : x ∈ P.toSet <;> simp [hx]
    simp only [θ, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_sub, Pi.sub_apply,
      Submodule.coe_sum, Finset.sum_apply, TestFun.coe_ind, smul_eq_mul]
    rw [mul_assoc, sub_mul, Finset.sum_mul]
    simp only [mul_assoc, hi]
  simp_rw [e]
  rw [integral_const_mul, integral_sub ((hint T).const_mul _)
    (integrable_finsetSum _ fun T' _ => (hint T').const_mul _), integral_const_mul,
    integral_finsetSum _ fun T' _ => (hint T').const_mul _]
  simp only [integral_const_mul, integral_indicator_toSet, ← avg_mul_vol]
  congr 1
  rw [StoppingData.avg_mul_vol_children T w, children,
    Finset.sum_image fun ε _ ε' _ h => T.child_injective h,
    Finset.sum_image fun ε _ ε' _ h => T.child_injective h, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ε _ => by ring

/-- `∫ θ^T w = φ_T ∑_ε (ψ_T − ψ_{T_ε}) [w]_{T_ε} |T_ε|`. [PROVED] -/
theorem integral_thetaT_mul (T : DyadicCube d) (w : TestFun d) :
    ∫ x, (D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x =
      D.phiT R T * ∑ ε : Fin d → Bool,
        (D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)) * avg (T.child ε) w *
          (T.child ε).vol := by
  simpa only [thetaT] using integral_smul_cube_difference_mul T w (D.phiT R T) (D.psiT hR hRs hFR)

/-- For `T ∈ 𝐓`, with `ψ = [𝔥]/[v]` on `T` and its children, the sum `∑_ε (ψ_T − ψ_{T_ε}) [w]_{T_ε}
|T_ε|`
equals `∑_ε ([𝔥]_T/[v]_T − [𝔥]_{T_ε}/[v]_{T_ε}) ([w]_{T_ε} − ([w]_T/[v]_T) [v]_{T_ε}) |T_ε|`, since
`∑_ε (ψ_T − ψ_{T_ε}) [v]_{T_ε} |T_ε| = [𝔥]_T |T| − ∑_ε [𝔥]_{T_ε} |T_ε| = 0` (the identity behind
(2.62), p. 54). [PROVED] -/
theorem sum_psiT_diff_mul_eq {T : DyadicCube d} (hT : T ∈ D.setT hR hRs hFR) (w : TestFun d) :
    ∑ ε : Fin d → Bool, (D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)) *
        avg (T.child ε) w * (T.child ε).vol =
      ∑ ε : Fin d → Bool,
        (avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) -
          avg (T.child ε) (D.prunedH hR hRs hFR) / avg (T.child ε) (D.vP R)) *
        (avg (T.child ε) w - avg T w / avg T (D.vP R) * avg (T.child ε) (D.vP R)) *
          (T.child ε).vol := by
  have hTF := ((D.mem_setT hR hRs hFR).mp hT).1
  have hvT : avg T (D.vP R) ≠ 0 := ne_zero_of_lt_abs (D.lt_abs_avg_vP_of_mem_setF hR hRs hFR hTF)
  have hvc : ∀ ε, avg (T.child ε) (D.vP R) ≠ 0 :=
    fun ε => ne_zero_of_lt_abs (D.lt_abs_avg_vP_child_of_mem_setT hR hRs hFR hT ε)
  have hψT : D.psiT hR hRs hFR T = avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) := by
    rw [psiT, coefOn_eq_div hvT]
  have hψc : ∀ ε, D.psiT hR hRs hFR (T.child ε) =
      avg (T.child ε) (D.prunedH hR hRs hFR) / avg (T.child ε) (D.vP R) := fun ε => by
    rw [psiT, coefOn_eq_div (hvc ε)]
  simp only [hψT, hψc]
  have hsum : ∑ ε : Fin d → Bool,
      (avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) -
          avg (T.child ε) (D.prunedH hR hRs hFR) / avg (T.child ε) (D.vP R)) *
        avg (T.child ε) (D.vP R) * (T.child ε).vol = 0 := by
    have h1 := avg_mul_vol_children' T (D.prunedH hR hRs hFR)
    have h2 := avg_mul_vol_children' T (D.vP R)
    rw [Finset.sum_congr rfl fun ε _ => show
      (avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) -
          avg (T.child ε) (D.prunedH hR hRs hFR) / avg (T.child ε) (D.vP R)) *
        avg (T.child ε) (D.vP R) * (T.child ε).vol =
      avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) *
          (avg (T.child ε) (D.vP R) * (T.child ε).vol) -
        avg (T.child ε) (D.prunedH hR hRs hFR) * (T.child ε).vol by
          rw [sub_mul, div_mul_cancel₀ _ (hvc ε)]; ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← h2, ← h1, div_mul_eq_mul_div,
      mul_comm (avg T (D.vP R)) T.vol, ← mul_assoc, mul_div_assoc, div_self hvT, mul_one, sub_self]
  calc ∑ ε : Fin d → Bool,
        (avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) -
            avg (T.child ε) (D.prunedH hR hRs hFR) / avg (T.child ε) (D.vP R)) *
          avg (T.child ε) w * (T.child ε).vol
      = ∑ ε : Fin d → Bool,
          (avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) -
              avg (T.child ε) (D.prunedH hR hRs hFR) / avg (T.child ε) (D.vP R)) *
            (avg (T.child ε) w - avg T w / avg T (D.vP R) * avg (T.child ε) (D.vP R)) *
              (T.child ε).vol
        + avg T w / avg T (D.vP R) * ∑ ε : Fin d → Bool,
          (avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) -
              avg (T.child ε) (D.prunedH hR hRs hFR) / avg (T.child ε) (D.vP R)) *
            avg (T.child ε) (D.vP R) * (T.child ε).vol := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ε _ => by ring
    _ = _ := by rw [hsum, mul_zero, add_zero]

/-- **(2.62) for one cube** `T ∈ 𝐓`: `|∫ θ^T w| ≤ |φ_T| · (martingale expression in 𝔥, w, v) |T|`.
[PROVED] -/
theorem abs_integral_thetaT_mul_le (hG : D.GBound) {T : DyadicCube d}
    (hT : T ∈ D.setT hR hRs hFR) (w : TestFun d) :
    |∫ x, (D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x| ≤
      D.CφT * D.KQ *
        (((8 + 128 * D.Mv) * (martDiff T (D.prunedH hR hRs hFR) * martDiff T w)
          + 8 * (8 + 128 * D.Mv) *
              (martAvg T w * martDiff T (D.prunedH hR hRs hFR) * martDiff T (D.vP R))
          + 64 * (martAvg T (D.prunedH hR hRs hFR) * martDiff T (D.vP R) * martDiff T w)
          + 512 * (martAvg T (D.prunedH hR hRs hFR) * martAvg T w * martDiff T (D.vP R) ^ 2)) *
          T.vol) := by
  have hTF := ((D.mem_setT hR hRs hFR).mp hT).1
  obtain ⟨hTn, _⟩ := (D.mem_setF hR hRs hFR).mp hTF
  have hφ : |D.phiT R T| ≤ D.CφT * D.KQ :=
    D.abs_phiT_le hR hRs hG (D.second_tree_subset hR hRs hFR
      (D.mem_second_tree_of_mem_nonleaf hR hRs hFR hTn)) ((mem_nonleaf_iff D.hd).mp hTn).1
  rw [D.integral_thetaT_mul hR hRs hFR T w, D.sum_psiT_diff_mul_eq hR hRs hFR hT w, abs_mul]
  refine mul_le_mul hφ ?_ (abs_nonneg _) (mul_nonneg D.CφT_nonneg D.KQ_nonneg)
  exact abs_sum_children_mart_le T (D.prunedH hR hRs hFR) w (D.vP R)
    (D.lt_abs_avg_vP_of_mem_setF hR hRs hFR hTF) (D.lt_abs_avg_vP_child_of_mem_setT hR hRs hFR hT)
    (D.abs_avg_vP_le_Mv_of_mem_setF hR hRs hFR hTF)
    (D.child_abs_avg_vP_le_Mv_of_mem_setF hR hRs hFR hTF)

/-- The normalised bounded function `f₃ = M_v^{-1} v̂` of Lemma 2.71. -/
noncomputable def fthree : TestFun d := D.Mv⁻¹ • D.vhat hR hRs hFR

theorem abs_fthree_le (x : Fin d → ℝ) : |(D.fthree hR hRs hFR : (Fin d → ℝ) → ℝ) x| ≤ 1 := by
  have hM := D.Mv_pos
  rw [fthree, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hM,
    ← div_eq_inv_mul, div_le_one hM]
  exact D.abs_vhat_le hR hRs hFR x

theorem eLpNorm_fthree_le :
    eLpNorm (D.fthree hR hRs hFR : (Fin d → ℝ) → ℝ) ⊤ volume ≤ 1 := by
  rw [eLpNorm_exponent_top (TestFun.memLp (D.fthree hR hRs hFR).2 ⊤).aestronglyMeasurable]
  refine (eLpNormEssSup_le_of_ae_bound (C := 1) (Filter.Eventually.of_forall fun x => ?_)).trans
    (by rw [ENNReal.ofReal_one])
  rw [Real.norm_eq_abs]
  exact D.abs_fthree_le hR hRs hFR x

/-- `Δ_T v = M_v Δ_T f₃` on the cubes of `𝐓`. [PROVED] -/
theorem martDiff_vP_eq_of_mem_setF {T : DyadicCube d} (hT : T ∈ D.setF hR hRs hFR) :
    martDiff T (D.vP R) = D.Mv * martDiff T (D.fthree hR hRs hFR) := by
  have hM := D.Mv_pos
  rw [fthree, Submodule.coe_smul, martDiff_const_smul, abs_inv, abs_of_pos hM, ← mul_assoc,
    mul_inv_cancel₀ hM.ne', one_mul]
  exact martDiff_congr_avg T (D.avg_vhat_eq_of_mem_setF hR hRs hFR hT).symm
    fun ε => (D.child_avg_vhat_eq_of_mem_setF hR hRs hFR hT ε).symm

/-- The constant of the martingale estimate: `C_mart = (8 + 192 M_v)(1 + 8 M_v)`. -/
noncomputable def Cmart : ℝ := (8 + 192 * D.Mv) * (1 + 8 * D.Mv)

theorem Cmart_nonneg : 0 ≤ D.Cmart := by
  have := D.Mv_nonneg
  unfold Cmart
  positivity

/-- **(2.62) in the form required by Lemma 2.71**: for `T ∈ 𝐓`,
`|∫ θ^T w| ≤ C_{φ,T} K C_mart (Δ_T 𝔥 Δ_T w + E_T 𝔥 Δ_T w Δ_T f₃ + E_T w Δ_T 𝔥 Δ_T f₃ + E_T 𝔥 E_T w
(Δ_T f₃)²) |T|`.
[PROVED] -/
theorem abs_alpha_le (hG : D.GBound) {T : DyadicCube d} (hT : T ∈ D.setT hR hRs hFR)
    (w : TestFun d) :
    |∫ x, (D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x| ≤
      D.CφT * D.KQ * D.Cmart *
        (martDiff T (D.prunedH hR hRs hFR) * martDiff T w
          + martAvg T (D.prunedH hR hRs hFR) * martDiff T w * martDiff T (D.fthree hR hRs hFR)
          + martAvg T w * martDiff T (D.prunedH hR hRs hFR) * martDiff T (D.fthree hR hRs hFR)
          + martAvg T (D.prunedH hR hRs hFR) * martAvg T w *
              martDiff T (D.fthree hR hRs hFR) ^ 2) * T.vol := by
  have hTF := ((D.mem_setT hR hRs hFR).mp hT).1
  have hA := D.abs_integral_thetaT_mul_le hR hRs hFR hG hT w
  rw [D.martDiff_vP_eq_of_mem_setF hR hRs hFR hTF] at hA
  refine hA.trans ?_
  have hMv := D.Mv_nonneg
  have hC := mul_nonneg D.CφT_nonneg D.KQ_nonneg
  set Mv := D.Mv with hMvdef
  set Cm := D.Cmart with hCm
  obtain ⟨c1, c2, c3, c4⟩ :
      (8 + 128 * Mv ≤ Cm) ∧ (8 * (8 + 128 * Mv) * Mv ≤ Cm) ∧
      (64 * Mv ≤ Cm) ∧ (512 * Mv ^ 2 ≤ Cm) :=
    martingale_coefficient_bounds hMv
  set Δh := martDiff T (D.prunedH hR hRs hFR)
  set Δw := martDiff T w
  set Δ3 := martDiff T (D.fthree hR hRs hFR)
  set Eh := martAvg T (D.prunedH hR hRs hFR)
  set Ew := martAvg T w
  have h1 : 0 ≤ Δh := martDiff_nonneg _ _
  have h2 : 0 ≤ Δw := martDiff_nonneg _ _
  have h3 : 0 ≤ Δ3 := martDiff_nonneg _ _
  have h4 : 0 ≤ Eh := martAvg_nonneg _ _
  have h5 : 0 ≤ Ew := martAvg_nonneg _ _
  have hvol := T.vol_pos.le
  have p1 := mul_le_mul_of_nonneg_right c1 (mul_nonneg h1 h2)
  have p2 := mul_le_mul_of_nonneg_right c2 (mul_nonneg (mul_nonneg h5 h1) h3)
  have p3 := mul_le_mul_of_nonneg_right c3 (mul_nonneg (mul_nonneg h4 h3) h2)
  have p4 := mul_le_mul_of_nonneg_right c4 (mul_nonneg (mul_nonneg h4 h5) (sq_nonneg Δ3))
  have key : (8 + 128 * Mv) * (Δh * Δw) + 8 * (8 + 128 * Mv) * (Ew * Δh * (Mv * Δ3))
      + 64 * (Eh * (Mv * Δ3) * Δw) + 512 * (Eh * Ew * (Mv * Δ3) ^ 2) ≤
      Cm * (Δh * Δw + Eh * Δw * Δ3 + Ew * Δh * Δ3 + Eh * Ew * Δ3 ^ 2) := by
    convert add_le_add (add_le_add (add_le_add p1 p2) p3) p4 using 1 <;> ring
  calc D.CφT * D.KQ * (((8 + 128 * Mv) * (Δh * Δw) + 8 * (8 + 128 * Mv) * (Ew * Δh * (Mv * Δ3))
        + 64 * (Eh * (Mv * Δ3) * Δw) + 512 * (Eh * Ew * (Mv * Δ3) ^ 2)) * T.vol)
      ≤ D.CφT * D.KQ * (Cm * (Δh * Δw + Eh * Δw * Δ3 + Ew * Δh * Δ3 + Eh * Ew * Δ3 ^ 2) * T.vol) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right key hvol) hC
    _ = _ := by ring

/-- The conjugate exponent `r' = r/(r−1)`. -/
noncomputable def r' : ℝ := D.r / (D.r - 1)

theorem one_lt_r' : 1 < D.r' := by
  have := D.hr
  unfold r'
  rw [lt_div_iff₀ (by linarith)]
  linarith

theorem r'_pos : 0 < D.r' := by linarith [D.one_lt_r']

theorem inv_r_add_inv_r' : 1 / D.r + 1 / D.r' = 1 := by
  have hr := D.hr
  have hr0 : D.r ≠ 0 := by linarith
  unfold r'
  rw [one_div_div, ← add_div, add_sub_cancel, div_self hr0]

theorem sub_one_mul_r' : (D.r - 1) * D.r' = D.r := by
  have hr := D.hr
  have h : D.r - 1 ≠ 0 := by linarith
  unfold r'
  field_simp

/-- The constant of Lemma 2.71 for the exponents `r`, `r'`. -/
noncomputable def C271 : ℝ :=
  Classical.choose (lemma271 D.hd D.r D.r' D.hr D.one_lt_r' D.inv_r_add_inv_r')

theorem C271_nonneg : 0 ≤ D.C271 :=
  (Classical.choose_spec (lemma271 D.hd D.r D.r' D.hr D.one_lt_r' D.inv_r_add_inv_r')).1

theorem C271_spec (C₀ : ℝ) (R : DyadicCube d) (f₁ f₂ f₃ : (Fin d → ℝ) → ℝ)
    (α : DyadicCube d → ℝ) (hC₀ : 0 ≤ C₀) (h₁ : MemLp f₁ (ENNReal.ofReal D.r) volume)
    (h₂ : MemLp f₂ (ENNReal.ofReal D.r') volume) (h₃ : MemLp f₃ ⊤ volume)
    (h₃1 : eLpNorm f₃ ⊤ volume ≤ 1)
    (hα : ∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T f₁ * martDiff T f₂
      + martAvg T f₁ * martDiff T f₂ * martDiff T f₃
      + martAvg T f₂ * martDiff T f₁ * martDiff T f₃
      + martAvg T f₁ * martAvg T f₂ * martDiff T f₃ ^ 2) * T.vol) :
    ∑' T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal (D.C271 * C₀) *
      (eLpNorm (truncate R f₁) (ENNReal.ofReal D.r) volume *
        eLpNorm (truncate R f₂) (ENNReal.ofReal D.r') volume) :=
  (Classical.choose_spec (lemma271 D.hd D.r D.r' D.hr D.one_lt_r' D.inv_r_add_inv_r')).2
    C₀ R f₁ f₂ f₃ α hC₀ h₁ h₂ h₃ h₃1 hα

/-- **(2.62) summed by Lemma 2.71** (p. 54): for every test function `w`,
`|∫ Θ_𝐓 w| ≤ C_{2.71} C_{φ,T} K C_mart ‖𝔥‖_r ‖w‖_{r'}`. [PROVED] -/
theorem abs_integral_ThetaT_mul_le (hG : D.GBound) (w : TestFun d) :
    |∫ x, (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x| ≤
      D.C271 * (D.CφT * D.KQ * D.Cmart) *
        lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r *
          lpNorm (w : (Fin d → ℝ) → ℝ) D.r' := by
  classical
  have hC₀ : 0 ≤ D.CφT * D.KQ * D.Cmart :=
    mul_nonneg (mul_nonneg D.CφT_nonneg D.KQ_nonneg) D.Cmart_nonneg
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hr'0 := D.r'_pos
  set α : DyadicCube d → ℝ := fun T => if T ∈ D.setT hR hRs hFR then
    ∫ x, (D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x else 0 with hα
  -- the integral as a finite sum
  have hsum : ∫ x, (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x =
      ∑ T ∈ D.setT hR hRs hFR, α T := by
    have e : ∀ x, (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x =
        ∑ T ∈ D.setT hR hRs hFR,
          (D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x := fun x => by
      rw [ThetaT, Submodule.coe_sum, Finset.sum_apply, Finset.sum_mul]
    have hint : ∀ T : DyadicCube d, Integrable (fun x =>
        (D.thetaT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x) volume :=
      fun T => (TestFun.memLp (D.thetaT hR hRs hFR T).2 2).integrable_mul (TestFun.memLp w.2 2)
    simp_rw [e]
    rw [integral_finsetSum _ fun T _ => hint T]
    exact Finset.sum_congr rfl fun T hT => by simp only [hα, hT, ↓reduceIte]
  -- the bound on the coefficients
  have hα_le : ∀ T ∈ R.tree, |α T| ≤ D.CφT * D.KQ * D.Cmart *
      (martDiff T (D.prunedH hR hRs hFR) * martDiff T w
        + martAvg T (D.prunedH hR hRs hFR) * martDiff T w * martDiff T (D.fthree hR hRs hFR)
        + martAvg T w * martDiff T (D.prunedH hR hRs hFR) * martDiff T (D.fthree hR hRs hFR)
        + martAvg T (D.prunedH hR hRs hFR) * martAvg T w *
            martDiff T (D.fthree hR hRs hFR) ^ 2) * T.vol := by
    intro T _
    by_cases hT : T ∈ D.setT hR hRs hFR
    · simp only [hα, hT, ↓reduceIte]
      exact D.abs_alpha_le hR hRs hFR hG hT w
    · simp only [hα, hT, ↓reduceIte, abs_zero]
      have h1 := martDiff_nonneg T (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)
      have h2 := martDiff_nonneg T (w : (Fin d → ℝ) → ℝ)
      have h3 := martDiff_nonneg T (D.fthree hR hRs hFR : (Fin d → ℝ) → ℝ)
      have h4 := martAvg_nonneg T (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)
      have h5 := martAvg_nonneg T (w : (Fin d → ℝ) → ℝ)
      have h6 := T.vol_pos.le
      positivity
  have h271 := D.C271_spec (D.CφT * D.KQ * D.Cmart) R (D.prunedH hR hRs hFR) w
    (D.fthree hR hRs hFR) α hC₀ (TestFun.memLp (D.prunedH hR hRs hFR).2 _)
    (TestFun.memLp w.2 _) (TestFun.memLp (D.fthree hR hRs hFR).2 _)
    (D.eLpNorm_fthree_le hR hRs hFR) hα_le
  -- the right-hand side is finite
  have hE₁ : eLpNorm (truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.r)
      volume ≠ ⊤ := (TestFun.memLp (TestFun.truncateₗ R (D.prunedH hR hRs hFR)).2 _).eLpNorm_ne_top
  have hE₂ : eLpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.r') volume ≠ ⊤ :=
    (TestFun.memLp (TestFun.truncateₗ R w).2 _).eLpNorm_ne_top
  have hfin : ENNReal.ofReal (D.C271 * (D.CφT * D.KQ * D.Cmart)) *
      (eLpNorm (truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.r) volume *
        eLpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.r') volume) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hE₁ hE₂)
  -- the finite sum is dominated by the series
  have hsub : ∀ T ∈ D.setT hR hRs hFR, T ∈ R.tree := fun T hT =>
    ((mem_nonleaf_iff D.hd).mp ((D.mem_setF hR hRs hFR).mp ((D.mem_setT hR hRs hFR).mp hT).1).1).1
  have h2 : ∑ T ∈ D.setT hR hRs hFR, ‖α T‖ₑ ≤ ∑' T : R.tree, ‖α T‖ₑ := by
    rw [← Finset.sum_subtype_of_mem (fun T => ‖α T‖ₑ) hsub]
    exact ENNReal.sum_le_tsum _
  have h3 := ENNReal.toReal_mono hfin (h2.trans h271)
  rw [ENNReal.toReal_sum (fun T _ => enorm_ne_top), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg D.C271_nonneg hC₀)] at h3
  simp only [toReal_enorm, Real.norm_eq_abs] at h3
  -- assemble
  have e𝔥 : truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) = D.prunedH hR hRs hFR :=
    congrArg Subtype.val (TestFun.truncateₗ_of_supportedOn (D.prunedH_supported hR hRs hFR))
  have hw : lpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) D.r' ≤ lpNorm (w : (Fin d → ℝ) → ℝ) D.r' :=
    TestFun.lpNorm_truncateₗ_le R w hr'0
  have hnorm𝔥 : 0 ≤ lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r := lpNorm_nonneg _ _
  calc |∫ x, (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x|
      = |∑ T ∈ D.setT hR hRs hFR, α T| := by rw [hsum]
    _ ≤ ∑ T ∈ D.setT hR hRs hFR, |α T| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ D.C271 * (D.CφT * D.KQ * D.Cmart) *
          (lpNorm (truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)) D.r *
            lpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) D.r') := h3
    _ = D.C271 * (D.CφT * D.KQ * D.Cmart) * lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r *
          lpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) D.r' := by rw [e𝔥]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (mul_nonneg (mul_nonneg D.C271_nonneg hC₀) hnorm𝔥)

/-! The duality step (p. 54): `‖Θ_𝐓‖_r = sup_{‖w‖_{r'} ≤ 1} |∫ Θ_𝐓 w|`. Since `Θ_𝐓` is constant on
the
cubes of `𝐏_R`, the extremal `w` can be written down: `w = ∑_{P ∈ 𝐏_R} c_P |c_P|^{r−2} 𝟙_P` with
`c_P` the
value of `Θ_𝐓` on `P`, for which `∫ Θ_𝐓 w = ‖Θ_𝐓‖_r^r` and `‖w‖_{r'}^{r'} = ‖Θ_𝐓‖_r^r`. -/

/-- `Θ_𝐓` is constant on the cubes of `𝐏_R`. [PROVED] -/
theorem ThetaT_constOn {P : DyadicCube d} (hP : P ∈ D.partR hR hRs hFR) :
    ConstOn (D.ThetaT hR hRs hFR) P := by
  unfold ThetaT
  refine constOn_sum fun T hT => ?_
  obtain ⟨hTn, hTs⟩ := (D.mem_setF hR hRs hFR).mp ((D.mem_setT hR hRs hFR).mp hT).1
  exact D.thetaT_constOn hR hRs hFR hTn hTs hP

/-- The value `c_P` of `Θ_𝐓` on the cube `P ∈ 𝐏_R`. -/
noncomputable def cT (P : DyadicCube d) : ℝ :=
  (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) (fun i => (2 : ℝ) ^ P.m * P.l i)

theorem ThetaT_apply_eq_cT {P : DyadicCube d} {x : Fin d → ℝ} (hP : P ∈ D.partR hR hRs hFR)
    (hx : x ∈ P.toSet) : (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x = D.cT hR hRs hFR P :=
  D.ThetaT_constOn hR hRs hFR hP x hx _ P.corner_mem

/-- The dual test function `w = ∑_{P ∈ 𝐏_R} c_P |c_P|^{r−2} 𝟙_P`. -/
noncomputable def wdual : TestFun d :=
  ∑ P ∈ D.partR hR hRs hFR,
    (D.cT hR hRs hFR P * |D.cT hR hRs hFR P| ^ (D.r - 2)) • TestFun.ind P

theorem wdual_apply {P : DyadicCube d} {x : Fin d → ℝ} (hP : P ∈ D.partR hR hRs hFR)
    (hx : x ∈ P.toSet) : (D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      D.cT hR hRs hFR P * |D.cT hR hRs hFR P| ^ (D.r - 2) := by
  rw [wdual, Submodule.coe_sum, Finset.sum_apply, Finset.sum_eq_single P]
  · rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hx, Pi.one_apply,
      smul_eq_mul, mul_one]
  · intro P' hP' hne
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_notMem
      (fun h => Set.disjoint_left.mp (D.partR_pairwiseDisjoint hR hRs hFR hP' hP hne) h hx),
      smul_zero]
  · exact fun h => absurd hP h

theorem wdual_supportedOn : SupportedOn (D.wdual hR hRs hFR) R := fun x hx => by
  rw [wdual, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
    Set.indicator_of_notMem (fun h => hx (D.subset_of_mem_partR hR hRs hFR hP h)), smul_zero]

/-- `∫ f = ∑_{P ∈ 𝐏_R} ∫_P f` for an integrable `f` vanishing off `R`. [PROVED] -/
theorem integral_eq_sum_partR {f : (Fin d → ℝ) → ℝ} (hf : Integrable f volume)
    (hsupp : ∀ x ∉ R.toSet, f x = 0) :
    ∫ x, f x = ∑ P ∈ D.partR hR hRs hFR, ∫ x in P.toSet, f x := by
  rw [← integral_biUnion_finset _ (fun P _ => P.measurableSet_toSet)
    (D.partR_pairwiseDisjoint hR hRs hFR) (fun P _ => hf.integrableOn), D.partR_cover hR hRs hFR]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm

/-- `c · (c |c|^{r−2}) = |c|^r`. [PROVED] -/
theorem mul_mul_abs_rpow_eq {c r : ℝ} (hr : 0 < r) : c * (c * |c| ^ (r - 2)) = |c| ^ r := by
  by_cases hc : c = 0
  · simp [hc, Real.zero_rpow hr.ne']
  · have hc' : 0 < |c| := abs_pos.mpr hc
    rw [show c * (c * |c| ^ (r - 2)) = |c| ^ (2 : ℕ) * |c| ^ (r - 2) by rw [sq_abs]; ring,
      ← Real.rpow_natCast, Nat.cast_ofNat, ← Real.rpow_add hc', add_sub_cancel]

/-- `|c |c|^{r−2}|^{r'} = |c|^r` when `(r−1) r' = r`. [PROVED] -/
theorem abs_mul_abs_rpow_rpow_eq {c r r' : ℝ} (hr : 1 < r) (hr' : 0 < r')
    (h : (r - 1) * r' = r) : |c * |c| ^ (r - 2)| ^ r' = |c| ^ r := by
  by_cases hc : c = 0
  · simp [hc, Real.zero_rpow hr'.ne', Real.zero_rpow (by linarith : r ≠ 0)]
  · have hc' : 0 < |c| := abs_pos.mpr hc
    have e : |c| * |c| ^ (r - 2) = |c| ^ (r - 1) := by
      rw [show r - 1 = 1 + (r - 2) by ring, Real.rpow_add hc', Real.rpow_one]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc' _), e, ← Real.rpow_mul (abs_nonneg _), h]

/-- `∫ Θ_𝐓 w = ∑_{P ∈ 𝐏_R} |c_P|^r |P|`. [PROVED] -/
theorem integral_ThetaT_mul_wdual :
    ∫ x, (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      ∑ P ∈ D.partR hR hRs hFR, |D.cT hR hRs hFR P| ^ D.r * P.vol := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  rw [D.integral_eq_sum_partR hR hRs hFR (f := fun x =>
      (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) x)
    ((TestFun.memLp (D.ThetaT hR hRs hFR).2 2).integrable_mul
      (TestFun.memLp (D.wdual hR hRs hFR).2 2))
    (fun x hx => by
      show (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) x = 0
      rw [D.ThetaT_supportedOn hR hRs hFR x hx, zero_mul])]
  refine Finset.sum_congr rfl fun P hP => ?_
  have e : ∫ x in P.toSet, (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x *
      (D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      ∫ x in P.toSet, (D.cT hR hRs hFR P * (D.cT hR hRs hFR P * |D.cT hR hRs hFR P| ^ (D.r - 2))) :=
    setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
      show (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) x = _
      rw [D.ThetaT_apply_eq_cT hR hRs hFR hP hx, D.wdual_apply hR hRs hFR hP hx]
  rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le,
    smul_eq_mul, mul_comm, mul_mul_abs_rpow_eq hr0]

/-- `‖Θ_𝐓‖_r^r = ∑_{P ∈ 𝐏_R} |c_P|^r |P|`. [PROVED] -/
theorem lpNorm_ThetaT_rpow_eq :
    lpNorm (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ^ D.r =
      ∑ P ∈ D.partR hR hRs hFR, |D.cT hR hRs hFR P| ^ D.r * P.vol := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  rw [lpNorm_rpow_eq_integral hr0 (TestFun.memLp (D.ThetaT hR hRs hFR).2 _),
    D.integral_abs_rpow_eq_sum_partR hR hRs hFR (D.ThetaT_supportedOn hR hRs hFR) hr0]
  refine Finset.sum_congr rfl fun P hP => ?_
  have e : ∫ x in P.toSet, |(D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r =
      ∫ x in P.toSet, |D.cT hR hRs hFR P| ^ D.r :=
    setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
      show |(D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r = _
      rw [D.ThetaT_apply_eq_cT hR hRs hFR hP hx]
  rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le,
    smul_eq_mul, mul_comm]

/-- `‖w‖_{r'}^{r'} = ∑_{P ∈ 𝐏_R} |c_P|^r |P|`. [PROVED] -/
theorem lpNorm_wdual_rpow_eq :
    lpNorm (D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) D.r' ^ D.r' =
      ∑ P ∈ D.partR hR hRs hFR, |D.cT hR hRs hFR P| ^ D.r * P.vol := by
  have hr'0 := D.r'_pos
  rw [lpNorm_rpow_eq_integral hr'0 (TestFun.memLp (D.wdual hR hRs hFR).2 _),
    D.integral_abs_rpow_eq_sum_partR hR hRs hFR (D.wdual_supportedOn hR hRs hFR) hr'0]
  refine Finset.sum_congr rfl fun P hP => ?_
  have e : ∫ x in P.toSet, |(D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r' =
      ∫ x in P.toSet, |D.cT hR hRs hFR P| ^ D.r :=
    setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
      show |(D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r' = _
      rw [D.wdual_apply hR hRs hFR hP hx, abs_mul_abs_rpow_rpow_eq D.hr hr'0 D.sub_one_mul_r']
  rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le,
    smul_eq_mul, mul_comm]

theorem second_pruneConst_nonneg : 0 ≤ (D.second R hR hRs hFR).pruneConst := by
  have := (D.second R hR hRs hFR).ε_pos
  have : 0 ≤ (D.second R hR hRs hFR).B := by linarith [(D.second R hR hRs hFR).hB]
  unfold pruneConst
  positivity

/-- **The `𝐓`-portion** (p. 54): `‖Θ_𝐓‖_r ≤ C_{2.71} C_{φ,T} C_mart K · pruneConst' |R|^{1/r}`,
where `pruneConst'` is the constant of the norm bound for `𝔥` (`‖𝔥‖_r ≤ pruneConst' |R|^{1/r}`).
[PROVED] -/
theorem lpNorm_ThetaT_le (hG : D.GBound) :
    lpNorm (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ≤
      D.C271 * (D.CφT * D.KQ * D.Cmart) *
        ((D.second R hR hRs hFR).pruneConst * R.vol ^ (1 / D.r)) := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hr'0 := D.r'_pos
  have hK₁ : 0 ≤ D.C271 * (D.CφT * D.KQ * D.Cmart) :=
    mul_nonneg D.C271_nonneg (mul_nonneg (mul_nonneg D.CφT_nonneg D.KQ_nonneg) D.Cmart_nonneg)
  set A := ∑ P ∈ D.partR hR hRs hFR, |D.cT hR hRs hFR P| ^ D.r * P.vol with hAdef
  have hA0 : 0 ≤ A :=
    Finset.sum_nonneg fun P _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) P.vol_pos.le
  have hN : lpNorm (D.ThetaT hR hRs hFR : (Fin d → ℝ) → ℝ) D.r = A ^ (1 / D.r) := by
    rw [hAdef, ← D.lpNorm_ThetaT_rpow_eq hR hRs hFR, one_div,
      Real.rpow_rpow_inv (lpNorm_nonneg _ _) hr0.ne']
  have hW : lpNorm (D.wdual hR hRs hFR : (Fin d → ℝ) → ℝ) D.r' = A ^ (1 / D.r') := by
    rw [hAdef, ← D.lpNorm_wdual_rpow_eq hR hRs hFR, one_div,
      Real.rpow_rpow_inv (lpNorm_nonneg _ _) hr'0.ne']
  have hmain := D.abs_integral_ThetaT_mul_le hR hRs hFR hG (D.wdual hR hRs hFR)
  rw [D.integral_ThetaT_mul_wdual hR hRs hFR, abs_of_nonneg hA0, hW] at hmain
  have h𝔥 : lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ≤
      (D.second R hR hRs hFR).pruneConst * R.vol ^ (1 / D.r) := by
    have h := (D.second R hR hRs hFR).pruned_lpNorm_le
    rw [show (D.second R hR hRs hFR).q = D.r from rfl,
      show ((D.second R hR hRs hFR).G : (Fin d → ℝ) → ℝ) = ((TestFun.ind R : TestFun d) :
        (Fin d → ℝ) → ℝ) from rfl, TestFun.lpNorm_ind R hr0] at h
    exact h
  rw [hN]
  by_cases hA : A = 0
  · rw [hA, Real.zero_rpow (one_div_pos.mpr hr0).ne']
    exact mul_nonneg hK₁ (mul_nonneg (D.second_pruneConst_nonneg hR hRs hFR)
      (Real.rpow_nonneg R.vol_pos.le _))
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
    have hsplit : A ^ (1 / D.r) * A ^ (1 / D.r') = A := by
      rw [← Real.rpow_add hApos, D.inv_r_add_inv_r', Real.rpow_one]
    have h1 : A ^ (1 / D.r) * A ^ (1 / D.r') ≤ D.C271 * (D.CφT * D.KQ * D.Cmart) *
        lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r * A ^ (1 / D.r') := by
      rw [hsplit]
      exact hmain
    have h2 := le_of_mul_le_mul_right h1 (Real.rpow_pos_of_pos hApos _)
    calc A ^ (1 / D.r)
        ≤ D.C271 * (D.CφT * D.KQ * D.Cmart) *
            lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h𝔥 hK₁

/-- The constant of the bound on `‖Θ‖_r`:
`C_Θ = 2 C_{φ,T} C_ψ (2^d/ε) + C_{2.71} C_{φ,T} C_mart · pruneConst'`. -/
noncomputable def CΘ : ℝ :=
  2 * D.CφT * D.Cψ hR hRs hFR * (2 ^ d / D.ε) +
    D.C271 * (D.CφT * D.Cmart) * (D.second R hR hRs hFR).pruneConst

theorem CΘ_nonneg : 0 ≤ D.CΘ hR hRs hFR := by
  have := D.ε_pos
  have := D.CφT_nonneg
  have := D.Cψ_nonneg hR hRs hFR
  have := D.C271_nonneg
  have := D.Cmart_nonneg
  have := D.second_pruneConst_nonneg hR hRs hFR
  unfold CΘ
  positivity

/-- **The bound on `‖Θ‖_r`** (p. 53–54): `‖Θ‖_r ≤ C_Θ |Q|^{-1/q} ‖g‖_q |R|^{1/r}`. [PROVED] -/
theorem lpNorm_Theta_le (hG : D.GBound) :
    lpNorm (D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ≤
      D.CΘ hR hRs hFR * D.KQ * R.vol ^ (1 / D.r) := by
  rw [D.Theta_eq_add hR hRs hFR]
  refine (TestFun.lpNorm_add_le _ _ D.hr.le).trans ?_
  have h1 := D.lpNorm_ThetaP_le hR hRs hFR hG
  have h2 := D.lpNorm_ThetaT_le hR hRs hFR hG
  unfold CΘ
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- The constant of the estimate of (2.58):
`C₅₈ = 2^d B ε^{-1} (2^d B/ε)^{1/r} C_Θ B^{1/q}`. -/
noncomputable def C₅₈ : ℝ :=
  2 ^ d * D.B * D.ε⁻¹ * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * D.CΘ hR hRs hFR * D.B ^ (1 / D.q)

/-- **The estimate of the term (2.58)** (p. 52–54): `|Λ_R(θ, u)| ≤ C₅₈ E_R`, from (2.10), the
reduction `‖θ‖_r ≤ (2^d B/ε)^{1/r} ‖Θ‖_r` and the bound on `‖Θ‖_r`. [PROVED] -/
theorem abs_form2_theta_le_E (hG : D.GBound) :
    |twoSlotForm D.T D.a D.b D.g R (D.theta hR hRs hFR) D.u| ≤ D.C₅₈ hR hRs hFR * D.E R := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  have hR0 := R.vol_pos
  have hF := D.Fpos'
  have hu0 := lpNorm_nonneg (D.u : (Fin d → ℝ) → ℝ) D.q
  have hG0 := lpNorm_nonneg (D.G : (Fin d → ℝ) → ℝ) D.q
  have hCΘ0 := D.CΘ_nonneg hR hRs hFR
  have h1 := D.abs_form2_theta_le hR hRs hFR
  have h2 := D.lpNorm_theta_le hR hRs hFR
  have h3 := D.lpNorm_Theta_le hR hRs hFR hG
  have hu : lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (-(1 / D.q)) ≤ D.B ^ (1 / D.q) := by
    calc lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (-(1 / D.q))
        ≤ (D.B * D.Q.vol) ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) :=
          mul_le_mul_of_nonneg_right D.lpNorm_u_le (Real.rpow_nonneg hV.le _)
      _ = D.B ^ (1 / D.q) := by
          rw [Real.mul_rpow hB hV.le, mul_assoc, ← Real.rpow_add hV, add_neg_cancel,
            Real.rpow_zero, mul_one]
  have hMv : 0 ≤ (2 ^ d * D.B / D.ε) ^ (1 / D.r) := by positivity
  have hθ : lpNorm (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ≤
      (2 ^ d * D.B / D.ε) ^ (1 / D.r) * (D.CΘ hR hRs hFR * D.KQ * R.vol ^ (1 / D.r)) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 hMv)
  have hX : 0 ≤ 2 ^ d * D.B * D.ε⁻¹ * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * D.CΘ hR hRs hFR := by
    positivity
  have hY : 0 ≤ D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
      ((R.vol / D.Q.vol) ^ (1 - 1 / D.r) * R.vol ^ (1 / D.r)) := by positivity
  calc |twoSlotForm D.T D.a D.b D.g R (D.theta hR hRs hFR) D.u|
      ≤ 2 ^ d * (D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹) *
          (R.vol / D.Q.vol) ^ (1 - 1 / D.r) *
          lpNorm (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r := h1
    _ ≤ 2 ^ d * (D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹) *
          (R.vol / D.Q.vol) ^ (1 - 1 / D.r) *
          ((2 ^ d * D.B / D.ε) ^ (1 / D.r) * (D.CΘ hR hRs hFR * D.KQ * R.vol ^ (1 / D.r))) :=
        mul_le_mul_of_nonneg_left hθ (by positivity)
    _ = 2 ^ d * D.B * D.ε⁻¹ * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * D.CΘ hR hRs hFR *
          (lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (-(1 / D.q))) *
          (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
            ((R.vol / D.Q.vol) ^ (1 - 1 / D.r) * R.vol ^ (1 / D.r))) := by
        unfold KQ
        ring
    _ ≤ 2 ^ d * D.B * D.ε⁻¹ * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * D.CΘ hR hRs hFR *
          D.B ^ (1 / D.q) *
          (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
            ((R.vol / D.Q.vol) ^ (1 - 1 / D.r) * R.vol ^ (1 / D.r))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hX) hY
    _ = D.C₅₈ hR hRs hFR * D.E R := by
        unfold C₅₈ E
        rw [rpow_fact1 hR0 hV]
        ring

end ThetaTPortion

/-! ### §2.7 The estimate of the term (2.59) (p. 54)

The term (2.59) is the mirror image of (2.58), with the roles of `(𝔥, v, ψ)` and `(𝔤̂, u, φ)`
exchanged: `ψ_T` is moved to the second entry by bilinearity and the factor `𝟙_T` in the first
entry is dropped by smoothness, so that (2.59) `= Λ_R(v, θ')` with `θ' = u ∑_T θ'^T`,
`θ'^T = ψ_T (φ_T 𝟙_T − ∑_{T'} φ_{T'} 𝟙_{T'})`. The testing condition (1.9) for `τ`, `𝐐_R` gives
`|Λ_R(v, θ')| ≤ B F_R ‖v‖_r ‖θ'‖_q`, and `‖θ'‖_q` is estimated as `‖θ‖_r` was, now with the
partition of `R` into the **first** stopping cubes inside `R` and the remaining leaves (on the cubes
inside a first stopping cube `u θ'^T = 0`, since `𝔤̂ = φ u` there), the bound (2.9) for `u`, the
lower
bound (2.11) for `[u]`, Lemma 2.71 with the exponents `q`, `q'`, and the norm bound for
`𝔤̂ = ψ_R 𝟙_R`. -/

section Term259

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

/-- The function `θ'^T = ψ_T (φ_T 𝟙_T − ∑_{T' child of T} φ_{T'} 𝟙_{T'})`. -/
noncomputable def thetaGT (T : DyadicCube d) : TestFun d :=
  D.psiT hR hRs hFR T • (D.phiT R T • TestFun.ind T - ∑ T' ∈ children T, D.phiT R T' • TestFun.ind
    T')

/-- The function `θ' = ∑_T ψ_T (φ_T u_T − ∑_{T'} φ_{T'} u_{T'}) = u ∑_T θ'^T`, the sum over the
non-leaf
cubes `T ⊆ R` of the tree. -/
noncomputable def thetaG : TestFun d :=
  ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R,
    D.psiT hR hRs hFR T • (D.yT R T - ∑ T' ∈ children T, D.yT R T')

/-- `∑_{T ∈ s} ψ_T (φ_T u_T − ∑_{T'} φ_{T'} u_{T'}) = u ∑_{T ∈ s} θ'^T` pointwise. [PROVED] -/
theorem sum_smul_yT_apply (s : Finset (DyadicCube d)) (x : Fin d → ℝ) :
    ((∑ T ∈ s, D.psiT hR hRs hFR T • (D.yT R T - ∑ T' ∈ children T, D.yT R T') :
        TestFun d) : (Fin d → ℝ) → ℝ) x =
      (D.u : (Fin d → ℝ) → ℝ) x *
        ((∑ T ∈ s, D.thetaGT hR hRs hFR T : TestFun d) : (Fin d → ℝ) → ℝ) x := by
  simp only [thetaGT, yT, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_sub,
    Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, TestFun.coe_truncateₗ, TestFun.coe_ind,
    smul_eq_mul, truncate_apply_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  have e : ∑ T' ∈ children T, D.phiT R T' *
      ((D.u : (Fin d → ℝ) → ℝ) x * T'.toSet.indicator 1 x) =
      (D.u : (Fin d → ℝ) → ℝ) x * ∑ T' ∈ children T, D.phiT R T' * T'.toSet.indicator 1 x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T' _ => by ring
  rw [e]
  ring

theorem thetaG_supportedOn : SupportedOn (D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) R := by
  intro x hx
  rw [thetaG, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  have hTR : T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp hT).1
  rw [Submodule.coe_smul, Pi.smul_apply,
    supportedOn_sub (D.yT_supportedOn R T) (supportedOn_sum_children (D.yT_supportedOn R) T) x
      (fun h => hx (hTR h)), smul_zero]

/-- **(2.59) as `Λ_R(v, θ')`** (p. 54):
`∑_T Λ_R(ψ_T v_T, φ_T u_T − ∑_{T'} φ_{T'} u_{T'}) = Λ_R(v, θ')`. [PROVED] -/
theorem sum_2_59_eq :
    ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, twoSlotForm D.T D.a D.b D.g R
        (D.xT hR hRs hFR T) (D.yT R T - ∑ T' ∈ children T, D.yT R T') =
      twoSlotForm D.T D.a D.b D.g R (D.vP R) (D.thetaG hR hRs hFR) := by
  rw [thetaG, twoSlotForm_sum_right]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [xT, twoSlotForm_smul_left D.T D.hab, twoSlotForm_smul_right]
  congr 1
  have hTR : T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp hT).1
  have hsupp := supportedOn_sub (D.yT_supportedOn R T)
    (supportedOn_sum_children (D.yT_supportedOn R) T)
  have h0 := D.yT_sub_sum_meanZero hR hRs hFR hT
  rw [← twoSlotForm_eq_of_subset D.T D.a D.b D.g hTR (TestFun.truncateₗ T (D.vP R)) hsupp h0,
    twoSlotForm_truncateₗ_left, twoSlotForm_eq_of_subset D.T D.a D.b D.g hTR (D.vP R) hsupp h0]

/-- **The estimate of (2.59) by the testing condition (1.9) for `τ`, `𝐐_R`**:
`|Λ_R(v, θ')| ≤ B F_R ‖v‖_r ‖θ'‖_q`. [PROVED] -/
theorem abs_form2_vP_thetaG_le :
    |twoSlotForm D.T D.a D.b D.g R (D.vP R) (D.thetaG hR hRs hFR)| ≤
      D.B * D.FP R * lpNorm (D.vP R : (Fin d → ℝ) → ℝ) D.r *
        lpNorm (D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q :=
  D.testing_vP R hR.1 _ (D.thetaG_supportedOn hR hRs hFR)

/-- On a cube `T ⊆ R` inside a first stopping cube `P`, `φ_T u_T = 𝔤̂_T` (p. 51: `𝔤̂` is a multiple
of
`u` on `P`). [PROVED] -/
theorem yT_eq_truncateₗ_ghat {T P : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hTP : T.toSet ⊆ P.toSet) (hTR : T.toSet ⊆ R.toSet) :
    D.yT R T = TestFun.truncateₗ T (D.ghat R) := by
  obtain ⟨φ, hφ⟩ := D.exists_truncateₗ_pruned_eq_smul hP hTP
  have h : ∃ c : ℝ, TestFun.truncateₗ T (D.ghat R) = c • TestFun.truncateₗ T D.u :=
    ⟨φ - D.cS R, by rw [D.truncateₗ_ghat_eq_sub hTR, hφ]; module⟩
  exact (truncateₗ_eq_coefOn_smul h).symm

/-- `u θ'^T = 0` for a cube `T ⊆ R` inside a first stopping cube. [PROVED] -/
theorem yT_sub_sum_eq_zero {T P : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hTP : T.toSet ⊆ P.toSet) (hTR : T.toSet ⊆ R.toSet) :
    D.yT R T - ∑ T' ∈ children T, D.yT R T' = 0 := by
  rw [D.yT_eq_truncateₗ_ghat hP hTP hTR,
    Finset.sum_congr rfl fun c hc => D.yT_eq_truncateₗ_ghat hP
      ((subset_of_mem_children hc).trans hTP) ((subset_of_mem_children hc).trans hTR),
    sum_children_truncateₗ, sub_self]

open Classical in
/-- The non-leaf cubes `T ⊆ R` in no first stopping cube: the index set of `Θ'`. -/
noncomputable def setFG : Finset (DyadicCube d) :=
  (nonleaf (D.second R hR hRs hFR).N R).filter (fun T => D.NotInStopping T)

open Classical in
theorem mem_setFG {T : DyadicCube d} :
    T ∈ D.setFG hR hRs hFR ↔ T ∈ nonleaf (D.second R hR hRs hFR).N R ∧ D.NotInStopping T :=
  Finset.mem_filter

/-- Only the non-leaf cubes in no first stopping cube contribute to `θ'`. [PROVED] -/
theorem thetaG_eq_filter :
    D.thetaG hR hRs hFR = ∑ T ∈ D.setFG hR hRs hFR,
      D.psiT hR hRs hFR T • (D.yT R T - ∑ T' ∈ children T, D.yT R T') := by
  classical
  rw [thetaG, setFG]
  symm
  refine Finset.sum_filter_of_ne fun T hT hne => ?_
  by_contra hTs
  simp only [NotInStopping, not_forall, not_not] at hTs
  obtain ⟨P, hP, hTP⟩ := hTs
  exact hne (by rw [D.yT_sub_sum_eq_zero hP hTP ((mem_nonleaf_iff D.hd).mp hT).1, smul_zero])

/-- `Θ' = ∑_T θ'^T` over the non-leaf cubes in no first stopping cube. -/
noncomputable def ThetaG : TestFun d := ∑ T ∈ D.setFG hR hRs hFR, D.thetaGT hR hRs hFR T

/-- `θ' = u Θ'` pointwise. [PROVED] -/
theorem thetaG_apply_ThetaG (x : Fin d → ℝ) :
    (D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      (D.u : (Fin d → ℝ) → ℝ) x * (D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) x := by
  rw [D.thetaG_eq_filter hR hRs hFR, ThetaG]
  exact D.sum_smul_yT_apply hR hRs hFR _ x

theorem thetaGT_supportedOn (T : DyadicCube d) : SupportedOn (D.thetaGT hR hRs hFR T) T :=
  fun x hx => by
  have h1 : ((TestFun.ind T : TestFun d) : (Fin d → ℝ) → ℝ) x = 0 := Set.indicator_of_notMem hx _
  have h2 : ((∑ T' ∈ children T, D.phiT R T' • TestFun.ind T' : TestFun d) :
      (Fin d → ℝ) → ℝ) x = 0 := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun T' hc => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
      Set.indicator_of_notMem (fun h => hx (subset_of_mem_children hc h)), smul_zero]
  rw [thetaGT, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_sub, Pi.sub_apply,
    Submodule.coe_smul, Pi.smul_apply, h1, h2, smul_zero, sub_zero, smul_zero]

theorem ThetaG_supportedOn : SupportedOn (D.ThetaG hR hRs hFR) R := fun x hx => by
  rw [ThetaG, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  exact D.thetaGT_supportedOn hR hRs hFR T x fun h =>
    hx (((mem_nonleaf_iff D.hd).mp ((D.mem_setFG hR hRs hFR).mp hT).1).1 h)

open Classical in
/-- The partition `𝐏'_R` of `R`: the first stopping cubes inside `R` and the leaves of the tree not
contained in a first stopping cube. -/
noncomputable def partRG : Finset (DyadicCube d) :=
  D.Pst.filter (fun P => P.toSet ⊆ R.toSet) ∪
    (level (D.second R hR hRs hFR).N R).filter (fun T => D.NotInStopping T)

theorem mem_partRG {P : DyadicCube d} :
    P ∈ D.partRG hR hRs hFR ↔ (P ∈ D.stoppingCubes ∧ P.toSet ⊆ R.toSet) ∨
      (P ∈ level (D.second R hR hRs hFR).N R ∧ D.NotInStopping P) := by
  classical
  rw [partRG, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, D.mem_Pst]

theorem subset_of_mem_partRG {P : DyadicCube d} (hP : P ∈ D.partRG hR hRs hFR) :
    P.toSet ⊆ R.toSet := by
  rcases (D.mem_partRG hR hRs hFR).mp hP with hP | hP
  · exact hP.2
  · exact subset_of_mem_level hP.1

/-- The cubes of `𝐏'_R` are good cubes of the first stopping time. [PROVED] -/
theorem good_of_mem_partRG {P : DyadicCube d} (hP : P ∈ D.partRG hR hRs hFR) : D.Good P := by
  rcases (D.mem_partRG hR hRs hFR).mp hP with hP | hP
  · exact D.good_of_mem_stoppingCubes hP.1
  · exact D.good_of_notInStopping (D.second_tree_subset hR hRs hFR
      (D.mem_second_tree_of_mem_level hR hRs hFR le_rfl hP.1)) hP.2

/-- The leaves have the side length `2^{-N} ℓ(Q)` of the tree `𝒟_N(Q)`. [PROVED] -/
theorem m_of_mem_leaf {T : DyadicCube d} (hT : T ∈ level (D.second R hR hRs hFR).N R) :
    T.m = D.Q.m - D.N := by
  have h1 := m_of_mem_level hT
  have h2 := D.second_N_spec hR
  change T.m = D.Q.m - D.N
  rw [h1]
  exact h2

/-- A first stopping cube and a leaf not contained in a first stopping cube are disjoint. [PROVED]
-/
theorem disjoint_of_mem_stopping_of_mem_leafG {S T : DyadicCube d} (hS : S ∈ D.stoppingCubes)
    (hT : T ∈ level (D.second R hR hRs hFR).N R) (hTs : D.NotInStopping T) :
    Disjoint S.toSet T.toSet := by
  have h1 : ¬ T.toSet ⊆ S.toSet := hTs S hS
  refine DyadicCube.disjoint_of_not_subset h1 fun h2 => h1 ?_
  have hm1 := DyadicCube.m_le_of_subset D.hd h2
  have hm2 : D.Q.m - D.N ≤ S.m := (D.stoppingCubes_subset_tree' hS).2
  have hm3 := D.m_of_mem_leaf hR hRs hFR hT
  have e := DyadicCube.eq_of_subset_of_m_eq h2 (by omega)
  subst e
  exact subset_rfl

/-- The cubes of `𝐏'_R` are pairwise disjoint. [PROVED] -/
theorem partRG_pairwiseDisjoint :
    (↑(D.partRG hR hRs hFR) : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet := by
  intro P hP P' hP' hne
  rw [Finset.mem_coe] at hP hP'
  rw [D.mem_partRG hR hRs hFR] at hP hP'
  change Disjoint P.toSet P'.toSet
  rcases hP with hP | hP <;> rcases hP' with hP' | hP'
  · exact maximal_pairwiseDisjoint _ hP.1 hP'.1 hne
  · exact D.disjoint_of_mem_stopping_of_mem_leafG hR hRs hFR hP.1 hP'.1 hP'.2
  · exact (D.disjoint_of_mem_stopping_of_mem_leafG hR hRs hFR hP'.1 hP.1 hP.2).symm
  · exact (level_eq_or_disjoint hP.1 hP'.1).resolve_left hne

include hRs in
/-- A first stopping cube meeting `R` is contained in `R` (`R` lies in no first stopping cube).
[PROVED] -/
theorem stopping_subset_of_mem {P : DyadicCube d} (hP : P ∈ D.stoppingCubes) {x : Fin d → ℝ}
    (hxP : x ∈ P.toSet) (hxR : x ∈ R.toSet) : P.toSet ⊆ R.toSet := by
  rcases le_total P.m R.m with hm | hm
  · rcases DyadicCube.subset_or_disjoint P R hm with h | h
    · exact h
    · exact absurd hxR (Set.disjoint_left.mp h hxP)
  · rcases DyadicCube.subset_or_disjoint R P hm with h | h
    · exact absurd h (hRs P hP)
    · exact absurd hxP (Set.disjoint_left.mp h hxR)

/-- The cubes of `𝐏'_R` cover `R`. [PROVED] -/
theorem partRG_cover : ⋃ P ∈ D.partRG hR hRs hFR, P.toSet = R.toSet := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun P hP => D.subset_of_mem_partRG hR hRs hFR hP
  · intro x hx
    obtain ⟨T, hT, hxT⟩ := exists_mem_level (D.second R hR hRs hFR).N hx
    rw [Set.mem_iUnion₂]
    by_cases hTs : D.NotInStopping T
    · exact ⟨T, (D.mem_partRG hR hRs hFR).mpr (Or.inr ⟨hT, hTs⟩), hxT⟩
    · simp only [NotInStopping, not_forall, not_not] at hTs
      obtain ⟨S, hS, hTS⟩ := hTs
      exact ⟨S, (D.mem_partRG hR hRs hFR).mpr
        (Or.inl ⟨hS, D.stopping_subset_of_mem hRs hS (hTS hxT) hx⟩), hTS hxT⟩

/-- A non-leaf cube `T` in no first stopping cube and a cube `P ∈ 𝐏'_R`: `P ⊆ T` or `P ∩ T = ∅`.
[PROVED] -/
theorem subset_or_disjoint_of_mem_partRG {T P : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) (hTs : D.NotInStopping T)
    (hP : P ∈ D.partRG hR hRs hFR) : P.toSet ⊆ T.toSet ∨ Disjoint P.toSet T.toSet := by
  rcases (D.mem_partRG hR hRs hFR).mp hP with hP | hP
  · have h1 : ¬ T.toSet ⊆ P.toSet := hTs P hP.1
    rcases le_total P.m T.m with hm | hm
    · rcases DyadicCube.subset_or_disjoint P T hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases DyadicCube.subset_or_disjoint T P hm with h | h
      · exact absurd h h1
      · exact Or.inr h.symm
  · have hm1 := m_of_mem_level hP.1
    have hm2 := ((mem_nonleaf_iff D.hd).mp hT).2
    rcases DyadicCube.subset_or_disjoint P T (by omega) with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- The same for the children `T'` of `T`. [PROVED] -/
theorem child_subset_or_disjoint_of_mem_partRG {T T' P : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) (hTs : D.NotInStopping T)
    (hc : T' ∈ children T) (hP : P ∈ D.partRG hR hRs hFR) :
    P.toSet ⊆ T'.toSet ∨ Disjoint P.toSet T'.toSet := by
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  have hm' : (T.child ε).m = T.m - 1 := rfl
  rcases (D.mem_partRG hR hRs hFR).mp hP with hP | hP
  · have h1 : ¬ T.toSet ⊆ P.toSet := hTs P hP.1
    rcases le_total P.m (T.child ε).m with hm | hm
    · rcases DyadicCube.subset_or_disjoint P (T.child ε) hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases DyadicCube.subset_or_disjoint (T.child ε) P hm with h | h
      · rcases le_or_gt T.m P.m with hm2 | hm2
        · rcases DyadicCube.subset_or_disjoint T P hm2 with h3 | h3
          · exact absurd h3 h1
          · exact absurd (h (T.child ε).corner_mem)
              (Set.disjoint_left.mp h3 (T.child_subset ε (T.child ε).corner_mem))
        · have e : T.child ε = P := DyadicCube.eq_of_subset_of_m_eq h (by omega)
          rw [e]
          exact Or.inl subset_rfl
      · exact Or.inr h.symm
  · have hm1 := m_of_mem_level hP.1
    have hm2 := ((mem_nonleaf_iff D.hd).mp hT).2
    rcases DyadicCube.subset_or_disjoint P (T.child ε) (by omega) with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- `θ'^T` is constant on every cube of `𝐏'_R`, for `T` non-leaf in no first stopping cube. [PROVED]
-/
theorem thetaGT_constOn {T P : DyadicCube d} (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R)
    (hTs : D.NotInStopping T) (hP : P ∈ D.partRG hR hRs hFR) :
    ConstOn (D.thetaGT hR hRs hFR T) P := by
  unfold thetaGT
  exact constOn_smul _ (constOn_sub
    (constOn_smul _ (constOn_ind (D.subset_or_disjoint_of_mem_partRG hR hRs hFR hT hTs hP)))
    (constOn_sum fun T' hc => constOn_smul _
      (constOn_ind (D.child_subset_or_disjoint_of_mem_partRG hR hRs hFR hT hTs hc hP))))

/-- `Θ'` is constant on every cube of `𝐏'_R`. [PROVED] -/
theorem ThetaG_constOn {P : DyadicCube d} (hP : P ∈ D.partRG hR hRs hFR) :
    ConstOn (D.ThetaG hR hRs hFR) P := by
  unfold ThetaG
  refine constOn_sum fun T hT => ?_
  rw [D.mem_setFG hR hRs hFR] at hT
  exact D.thetaGT_constOn hR hRs hFR hT.1 hT.2 hP

/-- `∫ f = ∑_{P ∈ 𝐏'_R} ∫_P f` for an integrable `f` vanishing off `R`. [PROVED] -/
theorem integral_eq_sum_partRG {f : (Fin d → ℝ) → ℝ} (hf : Integrable f volume)
    (hsupp : ∀ x ∉ R.toSet, f x = 0) :
    ∫ x, f x = ∑ P ∈ D.partRG hR hRs hFR, ∫ x in P.toSet, f x := by
  rw [← integral_biUnion_finset _ (fun P _ => P.measurableSet_toSet)
    (D.partRG_pairwiseDisjoint hR hRs hFR) (fun P _ => hf.integrableOn),
    D.partRG_cover hR hRs hFR]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm

/-- `∫ |f|^p = ∑_{P ∈ 𝐏'_R} ∫_P |f|^p` for `f` supported on `R`. [PROVED] -/
theorem integral_abs_rpow_eq_sum_partRG {f : TestFun d} (hf : SupportedOn f R) {p : ℝ}
    (hp : 0 < p) :
    ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ p =
      ∑ P ∈ D.partRG hR hRs hFR, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ p :=
  D.integral_eq_sum_partRG hR hRs hFR (TestFun.integrable_abs_rpow f hp)
    fun x hx => by rw [hf x hx, abs_zero, Real.zero_rpow hp.ne']

/-- **(2.9) in real form**: `∫_P |u|^q ≤ 2^d B ε^{-1} |P|` on good cubes. [PROVED] -/
theorem setIntegral_u_rpow_le {P : DyadicCube d} (hP : D.Good P) :
    ∫ x in P.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q ≤ 2 ^ d * D.B / D.ε * P.vol := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have hP0 := P.vol_pos
  have h := Real.rpow_le_rpow (lpNorm_nonneg _ _) (D.lpNorm_truncateₗ_u_le hP) hq0.le
  rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hq0.ne', Real.rpow_one,
    TestFun.lpNorm_truncateₗ_rpow P D.u hq0] at h

/-- **The reduction of `‖θ'‖_q` to `‖Θ'‖_q`** (p. 54): `‖θ'‖_q^q ≤ 2^d B ε^{-1} ‖Θ'‖_q^q`. [PROVED]
-/
theorem lpNorm_thetaG_rpow_le :
    lpNorm (D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ^ D.q ≤
      2 ^ d * D.B / D.ε * lpNorm (D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ^ D.q := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  rw [lpNorm_rpow_eq_integral hq0 (TestFun.memLp (D.thetaG hR hRs hFR).2 _),
    lpNorm_rpow_eq_integral hq0 (TestFun.memLp (D.ThetaG hR hRs hFR).2 _),
    D.integral_abs_rpow_eq_sum_partRG hR hRs hFR (D.thetaG_supportedOn hR hRs hFR) hq0,
    D.integral_abs_rpow_eq_sum_partRG hR hRs hFR (D.ThetaG_supportedOn hR hRs hFR) hq0,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun P hP => ?_
  have hconst := D.ThetaG_constOn hR hRs hFR hP
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ x ∈ P.toSet, (D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) x = c :=
    ⟨_, fun x hx => hconst x hx _ P.corner_mem⟩
  have e1 : ∫ x in P.toSet, |(D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q =
      |c| ^ D.q * ∫ x in P.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun P.measurableSet_toSet fun x hx => ?_
    change |(D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q =
      |c| ^ D.q * |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q
    rw [D.thetaG_apply_ThetaG hR hRs hFR x, hc x hx, abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm]
  have e2 : ∫ x in P.toSet, |(D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q =
      |c| ^ D.q * P.vol := by
    have e : ∫ x in P.toSet, |(D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q =
        ∫ x in P.toSet, |c| ^ D.q :=
      setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
        show |(D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q = |c| ^ D.q
        rw [hc x hx]
    rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le,
      smul_eq_mul, mul_comm]
  rw [e1, e2]
  have h9 := D.setIntegral_u_rpow_le (D.good_of_mem_partRG hR hRs hFR hP)
  have hc0 : 0 ≤ |c| ^ D.q := Real.rpow_nonneg (abs_nonneg _) _
  calc |c| ^ D.q * ∫ x in P.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q
      ≤ |c| ^ D.q * (2 ^ d * D.B / D.ε * P.vol) := mul_le_mul_of_nonneg_left h9 hc0
    _ = 2 ^ d * D.B / D.ε * (|c| ^ D.q * P.vol) := by ring

/-- `‖θ'‖_q ≤ (2^d B/ε)^{1/q} ‖Θ'‖_q`. [PROVED] -/
theorem lpNorm_thetaG_le :
    lpNorm (D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ≤
      (2 ^ d * D.B / D.ε) ^ (1 / D.q) * lpNorm (D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have hC : 0 ≤ 2 ^ d * D.B / D.ε := by positivity
  have h := TestFun.lpNorm_le_rpow_of_integral_le (D.thetaG hR hRs hFR) hq0
    (C := 2 ^ d * D.B / D.ε * lpNorm (D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ^ D.q) (by
      rw [← lpNorm_rpow_eq_integral hq0 (TestFun.memLp (D.thetaG hR hRs hFR).2 _)]
      exact D.lpNorm_thetaG_rpow_le hR hRs hFR)
  refine h.trans (le_of_eq ?_)
  rw [Real.mul_rpow hC (Real.rpow_nonneg (lpNorm_nonneg _ _) _), one_div,
    Real.rpow_rpow_inv (lpNorm_nonneg _ _) hq0.ne']

/-! The `parents(𝐏)`-portion of `Θ'`: `parents(𝐏)' = parents(𝐏)₄`, the parents of the first
stopping cubes of `𝐏 ∩ 𝐏₄`. -/

/-- `parents(𝐏)'`: the cubes of `setFG` which are parents of cubes of `𝐏 ∩ 𝐏₄`. -/
noncomputable def setPG : Finset (DyadicCube d) :=
  (D.setFG hR hRs hFR).filter (fun T => T ∈ D.Pbar4)

/-- `𝐓'`: the other cubes of `setFG`. -/
noncomputable def setTG : Finset (DyadicCube d) :=
  (D.setFG hR hRs hFR).filter (fun T => T ∉ D.Pbar4)

/-- The contribution of parent cubes to the second auxiliary martingale sum. -/
noncomputable def ThetaGP : TestFun d := ∑ T ∈ D.setPG hR hRs hFR, D.thetaGT hR hRs hFR T

/-- The contribution of the remaining cubes to the second auxiliary martingale sum. -/
noncomputable def ThetaGT : TestFun d := ∑ T ∈ D.setTG hR hRs hFR, D.thetaGT hR hRs hFR T

theorem ThetaG_eq_add : D.ThetaG hR hRs hFR = D.ThetaGP hR hRs hFR + D.ThetaGT hR hRs hFR := by
  rw [ThetaG, ThetaGP, ThetaGT, setPG, setTG, Finset.sum_filter_add_sum_filter_not]

theorem mem_setPG {T : DyadicCube d} :
    T ∈ D.setPG hR hRs hFR ↔ T ∈ D.setFG hR hRs hFR ∧ T ∈ D.Pbar4 := Finset.mem_filter

theorem mem_setTG {T : DyadicCube d} :
    T ∈ D.setTG hR hRs hFR ↔ T ∈ D.setFG hR hRs hFR ∧ T ∉ D.Pbar4 := Finset.mem_filter

/-- `∑_{T' child of T} φ_{T'} 𝟙_{T'}(x) = φ_{T'(x)}` for `x ∈ T`. [PROVED] -/
theorem sum_children_phiT_ind_apply {T : DyadicCube d} {x : Fin d → ℝ} (hx : x ∈ T.toSet) :
    ((∑ T' ∈ children T, D.phiT R T' • TestFun.ind T' : TestFun d) :
      (Fin d → ℝ) → ℝ) x = D.phiT R (T.childAt x) := by
  rw [Submodule.coe_sum, Finset.sum_apply, children,
    Finset.sum_image fun ε _ ε' _ h => T.child_injective h]
  set ε₀ : Fin d → Bool := fun i => decide ((2 : ℝ) ^ (T.m - 1) * (2 * T.l i + 1) ≤ x i) with hε₀
  have hx0 : x ∈ (T.child ε₀).toSet := T.mem_childAt hx
  rw [Finset.sum_eq_single ε₀]
  · rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hx0, Pi.one_apply,
      smul_eq_mul, mul_one]
    rfl
  · intro ε _ hne
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
      Set.indicator_of_notMem (fun h => Set.disjoint_left.mp (T.child_disjoint hne) h hx0),
      smul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- `|θ'^T(x)| ≤ 2 C_ψ C_{φ,T} K 𝟙_T(x)` for a non-leaf cube `T`. [PROVED] -/
theorem abs_thetaGT_apply_le (hG : D.GBound) {T : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) (x : Fin d → ℝ) :
    |(D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x| ≤
      2 * D.Cψ hR hRs hFR * (D.CφT * D.KQ) * T.toSet.indicator 1 x := by
  have hT' := D.mem_second_tree_of_mem_nonleaf hR hRs hFR hT
  have hTR : T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp hT).1
  have hφ : |D.phiT R T| ≤ D.CφT * D.KQ :=
    D.abs_phiT_le hR hRs hG (D.second_tree_subset hR hRs hFR hT') hTR
  have hψ : |D.psiT hR hRs hFR T| ≤ D.Cψ hR hRs hFR := D.abs_psiT_le hR hRs hFR hT'
  have hC0 : 0 ≤ D.CφT * D.KQ := mul_nonneg D.CφT_nonneg D.KQ_nonneg
  have hCψ0 := D.Cψ_nonneg hR hRs hFR
  by_cases hx : x ∈ T.toSet
  · have hc : |D.phiT R (T.childAt x)| ≤ D.CφT * D.KQ :=
      D.abs_phiT_le hR hRs hG (D.second_tree_subset hR hRs hFR
        (D.child_mem_second_tree_of_mem_nonleaf hR hRs hFR hT _))
        ((T.child_subset _).trans hTR)
    rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, thetaGT, Submodule.coe_smul, Pi.smul_apply,
      Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
      Set.indicator_of_mem hx, Pi.one_apply, D.sum_children_phiT_ind_apply hx,
      smul_eq_mul, smul_eq_mul, mul_one, abs_mul]
    calc |D.psiT hR hRs hFR T| * |D.phiT R T - D.phiT R (T.childAt x)|
        ≤ D.Cψ hR hRs hFR * (D.CφT * D.KQ + D.CφT * D.KQ) :=
          mul_le_mul hψ ((abs_sub _ _).trans (add_le_add hφ hc)) (abs_nonneg _) hCψ0
      _ = 2 * D.Cψ hR hRs hFR * (D.CφT * D.KQ) := by ring
  · rw [Set.indicator_of_notMem hx, mul_zero, D.thetaGT_supportedOn hR hRs hFR T x hx, abs_zero]

/-- `|Θ'_parents(𝐏)(x)| ≤ 2 C_ψ C_{φ,T} K · 2^d/ε`, by the bounded overlap of `parents(𝐏)₄`.
[PROVED] -/
theorem abs_ThetaGP_apply_le (hG : D.GBound) (x : Fin d → ℝ) :
    |(D.ThetaGP hR hRs hFR : (Fin d → ℝ) → ℝ) x| ≤
      2 * D.Cψ hR hRs hFR * (D.CφT * D.KQ) * (2 ^ d / D.ε) := by
  classical
  have hc0 : 0 ≤ 2 * D.Cψ hR hRs hFR * (D.CφT * D.KQ) :=
    mul_nonneg (mul_nonneg (by norm_num) (D.Cψ_nonneg hR hRs hFR))
      (mul_nonneg D.CφT_nonneg D.KQ_nonneg)
  rw [ThetaGP, Submodule.coe_sum, Finset.sum_apply]
  calc |∑ T ∈ D.setPG hR hRs hFR, (D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x|
      ≤ ∑ T ∈ D.setPG hR hRs hFR, |(D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ D.setPG hR hRs hFR,
          2 * D.Cψ hR hRs hFR * (D.CφT * D.KQ) * T.toSet.indicator 1 x :=
        Finset.sum_le_sum fun T hT => D.abs_thetaGT_apply_le hR hRs hFR hG
          ((D.mem_setFG hR hRs hFR).mp ((D.mem_setPG hR hRs hFR).mp hT).1).1 x
    _ = 2 * D.Cψ hR hRs hFR * (D.CφT * D.KQ) *
          (((D.setPG hR hRs hFR).filter fun T => x ∈ T.toSet).card : ℝ) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_boole]
        exact Finset.sum_congr rfl fun T _ => by simp [Set.indicator_apply]
    _ ≤ 2 * D.Cψ hR hRs hFR * (D.CφT * D.KQ) * (2 ^ d / D.ε) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        refine le_trans ?_ (D.card_Pbar4_filter_le x)
        exact_mod_cast Finset.card_le_card (Finset.monotone_filter_left _
          fun T hT => ((D.mem_setPG hR hRs hFR).mp hT).2)

theorem ThetaGP_supportedOn : SupportedOn (D.ThetaGP hR hRs hFR) R := fun x hx => by
  rw [ThetaGP, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  exact D.thetaGT_supportedOn hR hRs hFR T x fun h => hx (((mem_nonleaf_iff D.hd).mp
    ((D.mem_setFG hR hRs hFR).mp ((D.mem_setPG hR hRs hFR).mp hT).1).1).1 h)

theorem ThetaGT_supportedOn : SupportedOn (D.ThetaGT hR hRs hFR) R := fun x hx => by
  rw [ThetaGT, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  exact D.thetaGT_supportedOn hR hRs hFR T x fun h => hx (((mem_nonleaf_iff D.hd).mp
    ((D.mem_setFG hR hRs hFR).mp ((D.mem_setTG hR hRs hFR).mp hT).1).1).1 h)

/-- **The `parents(𝐏)'`-portion**: `‖Θ'_parents(𝐏)‖_q ≤ 2 C_ψ C_{φ,T} (2^d/ε) · K · |R|^{1/q}`.
[PROVED] -/
theorem lpNorm_ThetaGP_le (hG : D.GBound) :
    lpNorm (D.ThetaGP hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ≤
      2 * D.Cψ hR hRs hFR * D.CφT * (2 ^ d / D.ε) * D.KQ * R.vol ^ (1 / D.q) := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hM0 : 0 ≤ 2 * D.Cψ hR hRs hFR * (D.CφT * D.KQ) * (2 ^ d / D.ε) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (D.Cψ_nonneg hR hRs hFR))
      (mul_nonneg D.CφT_nonneg D.KQ_nonneg)) (by positivity)
  have h := TestFun.lpNorm_le_of_abs_le (D.ThetaGP hR hRs hFR) (D.ThetaGP_supportedOn hR hRs hFR)
    hM0 (D.abs_ThetaGP_apply_le hR hRs hFR hG) hq0
  refine h.trans (le_of_eq ?_)
  ring

/-! The `𝐓'`-portion of `Θ'`: the martingale estimate with the bounded function `û`, Lemma 2.71 for
the exponents `q`, `q'`, and the explicit duality. -/

/-- The auxiliary function `û = ∑_{P ∈ 𝐏'_R} [u]_P 𝟙_P`. -/
noncomputable def uhat : TestFun d :=
  ∑ P ∈ D.partRG hR hRs hFR, avg P D.u • TestFun.ind P

theorem uhat_apply {P : DyadicCube d} {x : Fin d → ℝ} (hP : P ∈ D.partRG hR hRs hFR)
    (hx : x ∈ P.toSet) : (D.uhat hR hRs hFR : (Fin d → ℝ) → ℝ) x = avg P D.u := by
  rw [uhat, Submodule.coe_sum, Finset.sum_apply, Finset.sum_eq_single P]
  · rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hx, Pi.one_apply,
      smul_eq_mul, mul_one]
  · intro P' hP' hne
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_notMem
      (fun h => Set.disjoint_left.mp (D.partRG_pairwiseDisjoint hR hRs hFR hP' hP hne) h hx),
      smul_zero]
  · exact fun h => absurd hP h

theorem uhat_apply_of_notMem {x : Fin d → ℝ} (hx : x ∉ R.toSet) :
    (D.uhat hR hRs hFR : (Fin d → ℝ) → ℝ) x = 0 := by
  rw [uhat, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
    Set.indicator_of_notMem (fun h => hx (D.subset_of_mem_partRG hR hRs hFR hP h)), smul_zero]

/-- The bound `M_u = (2^d B/ε)^{1/q}` for `|[u]_P|` on good cubes, hence for `û`. -/
noncomputable def Mu : ℝ := (2 ^ d * D.B / D.ε) ^ (1 / D.q)

theorem Mu_pos : 0 < D.Mu := by
  have := D.ε_pos
  have : 0 < D.B := by linarith [D.hB]
  unfold Mu
  positivity

theorem Mu_nonneg : 0 ≤ D.Mu := D.Mu_pos.le

/-- `|[u]_P| ≤ M_u` on good cubes, by Jensen's inequality and (2.9). [PROVED] -/
theorem abs_avg_u_le_Mu {P : DyadicCube d} (hP : D.Good P) : |avg P D.u| ≤ D.Mu := by
  have hP0 := P.vol_pos
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have h1 := abs_avg_mul_rpow_le P D.u D.hq.le
  have h2 := D.lpNorm_truncateₗ_u_le hP
  rw [Real.mul_rpow (by positivity) hP0.le] at h2
  exact le_of_mul_le_mul_right (h1.trans h2) (Real.rpow_pos_of_pos hP0 _)

theorem abs_uhat_le (x : Fin d → ℝ) : |(D.uhat hR hRs hFR : (Fin d → ℝ) → ℝ) x| ≤ D.Mu := by
  by_cases hx : x ∈ R.toSet
  · rw [← D.partRG_cover hR hRs hFR, Set.mem_iUnion₂] at hx
    obtain ⟨P, hP, hxP⟩ := hx
    rw [D.uhat_apply hR hRs hFR hP hxP]
    exact D.abs_avg_u_le_Mu (D.good_of_mem_partRG hR hRs hFR hP)
  · rw [D.uhat_apply_of_notMem hR hRs hFR hx, abs_zero]
    exact D.Mu_nonneg

theorem truncateₗ_u_eq_sum_partRG :
    TestFun.truncateₗ R D.u = ∑ P ∈ D.partRG hR hRs hFR, TestFun.truncateₗ P D.u := by
  have h := TestFun.sum_truncateₗ_of_partition _ (D.partRG_pairwiseDisjoint hR hRs hFR)
    (fun P hP => D.subset_of_mem_partRG hR hRs hFR hP) (fun x hx => by
      rw [← D.partRG_cover hR hRs hFR, Set.mem_iUnion₂] at hx
      obtain ⟨P, hP, h⟩ := hx
      exact ⟨P, hP, h⟩) (TestFun.truncateₗ R D.u) (TestFun.truncateₗ_supportedOn R D.u)
  rw [← h]
  exact Finset.sum_congr rfl fun P hP =>
    TestFun.truncateₗ_truncateₗ_of_subset (D.subset_of_mem_partRG hR hRs hFR hP) D.u

/-- `[û]_T = [u]_T` for a cube `T ⊆ R` which is a union of cubes of `𝐏'_R`. [PROVED] -/
theorem avg_uhat_eq {T : DyadicCube d} (hTR : T.toSet ⊆ R.toSet)
    (h : ∀ P ∈ D.partRG hR hRs hFR, P.toSet ⊆ T.toSet ∨ Disjoint P.toSet T.toSet) :
    avg T (D.uhat hR hRs hFR) = avg T D.u := by
  have key : ∀ P ∈ D.partRG hR hRs hFR,
      TestFun.integralₗ (avg P D.u • TestFun.truncateₗ T (TestFun.ind P)) =
        TestFun.integralₗ (TestFun.truncateₗ T (TestFun.truncateₗ P D.u)) := by
    intro P hP
    rcases h P hP with hsub | hdis
    · rw [TestFun.truncateₗ_of_supportedOn
          (fun x hx => TestFun.ind_supportedOn P x fun h => hx (hsub h)),
        TestFun.truncateₗ_of_supportedOn
          (fun x hx => TestFun.truncateₗ_supportedOn P D.u x fun h => hx (hsub h)),
        map_smul, TestFun.integralₗ_truncateₗ, TestFun.integralₗ_apply, TestFun.integral_ind,
        smul_eq_mul]
    · rw [← TestFun.truncateₗ_ind P, TestFun.truncateₗ_truncateₗ_of_disjoint hdis.symm,
        TestFun.truncateₗ_truncateₗ_of_disjoint hdis.symm, smul_zero]
  have e : TestFun.truncateₗ T (D.uhat hR hRs hFR) =
      ∑ P ∈ D.partRG hR hRs hFR, avg P D.u • TestFun.truncateₗ T (TestFun.ind P) := by
    rw [uhat, map_sum]
    simp only [map_smul]
  have h1 := TestFun.integralₗ_truncateₗ T (D.uhat hR hRs hFR)
  have h2 := TestFun.integralₗ_truncateₗ T D.u
  rw [e, map_sum, Finset.sum_congr rfl key, ← map_sum TestFun.integralₗ,
    ← map_sum (TestFun.truncateₗ T), ← D.truncateₗ_u_eq_sum_partRG hR hRs hFR,
    TestFun.truncateₗ_truncateₗ_of_subset hTR] at h1
  rw [h1] at h2
  exact mul_right_cancel₀ T.vol_pos.ne' h2

theorem avg_uhat_eq_of_mem_setFG {T : DyadicCube d} (hT : T ∈ D.setFG hR hRs hFR) :
    avg T (D.uhat hR hRs hFR) = avg T D.u := by
  obtain ⟨hTn, hTs⟩ := (D.mem_setFG hR hRs hFR).mp hT
  exact D.avg_uhat_eq hR hRs hFR ((mem_nonleaf_iff D.hd).mp hTn).1
    fun P hP => D.subset_or_disjoint_of_mem_partRG hR hRs hFR hTn hTs hP

theorem child_avg_uhat_eq_of_mem_setFG {T : DyadicCube d} (hT : T ∈ D.setFG hR hRs hFR)
    (ε : Fin d → Bool) : avg (T.child ε) (D.uhat hR hRs hFR) = avg (T.child ε) D.u := by
  obtain ⟨hTn, hTs⟩ := (D.mem_setFG hR hRs hFR).mp hT
  exact D.avg_uhat_eq hR hRs hFR ((T.child_subset ε).trans ((mem_nonleaf_iff D.hd).mp hTn).1)
    fun P hP => D.child_subset_or_disjoint_of_mem_partRG hR hRs hFR hTn hTs
      (mem_children.mpr ⟨ε, rfl⟩) hP

theorem abs_avg_u_le_Mu_of_mem_setFG {T : DyadicCube d} (hT : T ∈ D.setFG hR hRs hFR) :
    |avg T D.u| ≤ D.Mu := by
  rw [← D.avg_uhat_eq_of_mem_setFG hR hRs hFR hT]
  exact abs_avg_le_of_abs_le T (D.abs_uhat_le hR hRs hFR)

theorem child_abs_avg_u_le_Mu_of_mem_setFG {T : DyadicCube d} (hT : T ∈ D.setFG hR hRs hFR)
    (ε : Fin d → Bool) : |avg (T.child ε) D.u| ≤ D.Mu := by
  rw [← D.child_avg_uhat_eq_of_mem_setFG hR hRs hFR hT ε]
  exact abs_avg_le_of_abs_le _ (D.abs_uhat_le hR hRs hFR)

/-- `|[u]_T| > 1/8` for `T ∈ setFG`, by (2.11). [PROVED] -/
theorem lt_abs_avg_u_of_mem_setFG {T : DyadicCube d} (hT : T ∈ D.setFG hR hRs hFR) :
    1 / 8 < |avg T D.u| := by
  obtain ⟨hTn, hTs⟩ := (D.mem_setFG hR hRs hFR).mp hT
  exact D.bound_2_11 D.hd (D.second_tree_subset hR hRs hFR
    (D.mem_second_tree_of_mem_nonleaf hR hRs hFR hTn)) (D.not_in_P4_of_notInStopping hTs)

/-- A child of a cube `T ∈ 𝐓'` lies in no cube of `𝐏₄`. [PROVED] -/
theorem child_not_in_P4_of_mem_setTG {T : DyadicCube d} (hT : T ∈ D.setTG hR hRs hFR)
    (ε : Fin d → Bool) : ∀ S ∈ D.P4, ¬ (T.child ε).toSet ⊆ S.toSet := by
  intro S hS hsub
  obtain ⟨hTF, hT4⟩ := (D.mem_setTG hR hRs hFR).mp hT
  obtain ⟨_, hTs⟩ := (D.mem_setFG hR hRs hFR).mp hTF
  obtain ⟨S', hS', hSS'⟩ := exists_maximal_superset D.hd D.union_subset_tree (D.P4_subset hS)
  have hcS' : (T.child ε).toSet ⊆ S'.toSet := hsub.trans hSS'
  have hTS' : ¬ T.toSet ⊆ S'.toSet := hTs S' hS'
  have hcT := T.child_subset ε
  have hS'T : S'.toSet ⊆ T.toSet := by
    rcases le_total S'.m T.m with hm | hm
    · rcases DyadicCube.subset_or_disjoint S' T hm with h | h
      · exact h
      · exact absurd (hcT (T.child ε).corner_mem)
          (Set.disjoint_left.mp h (hcS' (T.child ε).corner_mem))
    · rcases DyadicCube.subset_or_disjoint T S' hm with h | h
      · exact absurd h hTS'
      · exact absurd (hcS' (T.child ε).corner_mem)
          (Set.disjoint_left.mp h (hcT (T.child ε).corner_mem))
  have hm1 := DyadicCube.m_le_of_subset D.hd hcS'
  have hm2 := DyadicCube.m_le_of_subset D.hd hS'T
  have hne : S' ≠ T := fun e => hTS' (e ▸ subset_rfl)
  have hm3 : S'.m < T.m :=
    lt_of_le_of_ne hm2 fun e => hne (DyadicCube.eq_of_subset_of_m_eq hS'T e)
  have hm' : (T.child ε).m = T.m - 1 := rfl
  have e1 : T.child ε = S' := DyadicCube.eq_of_subset_of_m_eq hcS' (by omega)
  have hm4 := DyadicCube.m_le_of_subset D.hd hSS'
  have hm5 := DyadicCube.m_le_of_subset D.hd hsub
  rw [e1] at hm5
  have e2 : S = S' := DyadicCube.eq_of_subset_of_m_eq hSS' (le_antisymm hm4 hm5)
  rw [e2] at hS
  have hmem : T.child ε ∈ D.PstIn4 := by
    rw [D.mem_PstIn4, e1]
    exact ⟨hS', hS⟩
  exact hT4 (D.mem_Pbar4.mpr ⟨T.child ε, hmem, T.parent_child ε⟩)

theorem lt_abs_avg_u_child_of_mem_setTG {T : DyadicCube d} (hT : T ∈ D.setTG hR hRs hFR)
    (ε : Fin d → Bool) : 1 / 8 < |avg (T.child ε) D.u| := by
  obtain ⟨hTn, _⟩ := (D.mem_setFG hR hRs hFR).mp ((D.mem_setTG hR hRs hFR).mp hT).1
  exact D.bound_2_11 D.hd (D.second_tree_subset hR hRs hFR
    (D.child_mem_second_tree_of_mem_nonleaf hR hRs hFR hTn ε))
    (D.child_not_in_P4_of_mem_setTG hR hRs hFR hT ε)

/-- `∫ θ'^T w = ψ_T ∑_ε (φ_T − φ_{T_ε}) [w]_{T_ε} |T_ε|`. [PROVED] -/
theorem integral_thetaGT_mul (T : DyadicCube d) (w : TestFun d) :
    ∫ x, (D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x =
      D.psiT hR hRs hFR T * ∑ ε : Fin d → Bool,
        (D.phiT R T - D.phiT R (T.child ε)) * avg (T.child ε) w * (T.child ε).vol := by
  simpa only [thetaGT] using integral_smul_cube_difference_mul T w (D.psiT hR hRs hFR T) (D.phiT R)

/-- For `T ∈ 𝐓'`, with `φ = [𝔤̂]/[u]` on `T` and its children,
`∑_ε (φ_T − φ_{T_ε}) [w]_{T_ε} |T_ε| = ∑_ε ([𝔤̂]_T/[u]_T − [𝔤̂]_{T_ε}/[u]_{T_ε}) ([w]_{T_ε} −
([w]_T/[u]_T)[u]_{T_ε}) |T_ε|`.
[PROVED] -/
theorem sum_phiT_diff_mul_eq {T : DyadicCube d} (hT : T ∈ D.setTG hR hRs hFR) (w : TestFun d) :
    ∑ ε : Fin d → Bool, (D.phiT R T - D.phiT R (T.child ε)) * avg (T.child ε) w *
        (T.child ε).vol =
      ∑ ε : Fin d → Bool,
        (avg T (D.ghat R) / avg T D.u - avg (T.child ε) (D.ghat R) / avg (T.child ε) D.u) *
        (avg (T.child ε) w - avg T w / avg T D.u * avg (T.child ε) D.u) * (T.child ε).vol := by
  have hTF := ((D.mem_setTG hR hRs hFR).mp hT).1
  have huT : avg T D.u ≠ 0 := ne_zero_of_lt_abs (D.lt_abs_avg_u_of_mem_setFG hR hRs hFR hTF)
  have huc : ∀ ε, avg (T.child ε) D.u ≠ 0 :=
    fun ε => ne_zero_of_lt_abs (D.lt_abs_avg_u_child_of_mem_setTG hR hRs hFR hT ε)
  have hφT : D.phiT R T = avg T (D.ghat R) / avg T D.u := by
    rw [phiT, coefOn_eq_div huT]
  have hφc : ∀ ε, D.phiT R (T.child ε) = avg (T.child ε) (D.ghat R) / avg (T.child ε) D.u :=
    fun ε => by rw [phiT, coefOn_eq_div (huc ε)]
  simp only [hφT, hφc]
  have hsum : ∑ ε : Fin d → Bool,
      (avg T (D.ghat R) / avg T D.u - avg (T.child ε) (D.ghat R) / avg (T.child ε) D.u) *
        avg (T.child ε) D.u * (T.child ε).vol = 0 := by
    have h1 := avg_mul_vol_children' T (D.ghat R)
    have h2 := avg_mul_vol_children' T D.u
    rw [Finset.sum_congr rfl fun ε _ => show
      (avg T (D.ghat R) / avg T D.u - avg (T.child ε) (D.ghat R) / avg (T.child ε) D.u) *
        avg (T.child ε) D.u * (T.child ε).vol =
      avg T (D.ghat R) / avg T D.u * (avg (T.child ε) D.u * (T.child ε).vol) -
        avg (T.child ε) (D.ghat R) * (T.child ε).vol by
          rw [sub_mul, div_mul_cancel₀ _ (huc ε)]; ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← h2, ← h1, div_mul_eq_mul_div,
      mul_comm (avg T D.u) T.vol, ← mul_assoc, mul_div_assoc, div_self huT, mul_one, sub_self]
  calc ∑ ε : Fin d → Bool,
        (avg T (D.ghat R) / avg T D.u - avg (T.child ε) (D.ghat R) / avg (T.child ε) D.u) *
          avg (T.child ε) w * (T.child ε).vol
      = ∑ ε : Fin d → Bool,
          (avg T (D.ghat R) / avg T D.u - avg (T.child ε) (D.ghat R) / avg (T.child ε) D.u) *
            (avg (T.child ε) w - avg T w / avg T D.u * avg (T.child ε) D.u) * (T.child ε).vol
        + avg T w / avg T D.u * ∑ ε : Fin d → Bool,
          (avg T (D.ghat R) / avg T D.u - avg (T.child ε) (D.ghat R) / avg (T.child ε) D.u) *
            avg (T.child ε) D.u * (T.child ε).vol := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ε _ => by ring
    _ = _ := by rw [hsum, mul_zero, add_zero]

/-- **(2.62) for one cube** `T ∈ 𝐓'`. [PROVED] -/
theorem abs_integral_thetaGT_mul_le {T : DyadicCube d} (hT : T ∈ D.setTG hR hRs hFR)
    (w : TestFun d) :
    |∫ x, (D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x| ≤
      D.Cψ hR hRs hFR *
        (((8 + 128 * D.Mu) * (martDiff T (D.ghat R) * martDiff T w)
          + 8 * (8 + 128 * D.Mu) * (martAvg T w * martDiff T (D.ghat R) * martDiff T D.u)
          + 64 * (martAvg T (D.ghat R) * martDiff T D.u * martDiff T w)
          + 512 * (martAvg T (D.ghat R) * martAvg T w * martDiff T D.u ^ 2)) * T.vol) := by
  have hTF := ((D.mem_setTG hR hRs hFR).mp hT).1
  obtain ⟨hTn, _⟩ := (D.mem_setFG hR hRs hFR).mp hTF
  have hψ : |D.psiT hR hRs hFR T| ≤ D.Cψ hR hRs hFR :=
    D.abs_psiT_le hR hRs hFR (D.mem_second_tree_of_mem_nonleaf hR hRs hFR hTn)
  rw [D.integral_thetaGT_mul hR hRs hFR T w, D.sum_phiT_diff_mul_eq hR hRs hFR hT w, abs_mul]
  refine mul_le_mul hψ ?_ (abs_nonneg _) (D.Cψ_nonneg hR hRs hFR)
  exact abs_sum_children_mart_le T (D.ghat R) w D.u
    (D.lt_abs_avg_u_of_mem_setFG hR hRs hFR hTF) (D.lt_abs_avg_u_child_of_mem_setTG hR hRs hFR hT)
    (D.abs_avg_u_le_Mu_of_mem_setFG hR hRs hFR hTF)
    (D.child_abs_avg_u_le_Mu_of_mem_setFG hR hRs hFR hTF)

/-- The normalised bounded function `f₃ = M_u^{-1} û`. -/
noncomputable def fthreeG : TestFun d := D.Mu⁻¹ • D.uhat hR hRs hFR

theorem abs_fthreeG_le (x : Fin d → ℝ) : |(D.fthreeG hR hRs hFR : (Fin d → ℝ) → ℝ) x| ≤ 1 := by
  have hM := D.Mu_pos
  rw [fthreeG, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hM,
    ← div_eq_inv_mul, div_le_one hM]
  exact D.abs_uhat_le hR hRs hFR x

theorem eLpNorm_fthreeG_le :
    eLpNorm (D.fthreeG hR hRs hFR : (Fin d → ℝ) → ℝ) ⊤ volume ≤ 1 := by
  rw [eLpNorm_exponent_top (TestFun.memLp (D.fthreeG hR hRs hFR).2 ⊤).aestronglyMeasurable]
  refine (eLpNormEssSup_le_of_ae_bound (C := 1) (Filter.Eventually.of_forall fun x => ?_)).trans
    (by rw [ENNReal.ofReal_one])
  rw [Real.norm_eq_abs]
  exact D.abs_fthreeG_le hR hRs hFR x

/-- `Δ_T u = M_u Δ_T f₃` on the cubes of `setFG`. [PROVED] -/
theorem martDiff_u_eq_of_mem_setFG {T : DyadicCube d} (hT : T ∈ D.setFG hR hRs hFR) :
    martDiff T D.u = D.Mu * martDiff T (D.fthreeG hR hRs hFR) := by
  have hM := D.Mu_pos
  rw [fthreeG, Submodule.coe_smul, martDiff_const_smul, abs_inv, abs_of_pos hM, ← mul_assoc,
    mul_inv_cancel₀ hM.ne', one_mul]
  exact martDiff_congr_avg T (D.avg_uhat_eq_of_mem_setFG hR hRs hFR hT).symm
    fun ε => (D.child_avg_uhat_eq_of_mem_setFG hR hRs hFR hT ε).symm

/-- The constant of the martingale estimate for `û`: `C_mart' = (8 + 192 M_u)(1 + 8 M_u)`. -/
noncomputable def CmartG : ℝ := (8 + 192 * D.Mu) * (1 + 8 * D.Mu)

theorem CmartG_nonneg : 0 ≤ D.CmartG := by
  have := D.Mu_nonneg
  unfold CmartG
  positivity

/-- **(2.62) in the form required by Lemma 2.71**, for `T ∈ 𝐓'`. [PROVED] -/
theorem abs_alphaG_le {T : DyadicCube d} (hT : T ∈ D.setTG hR hRs hFR) (w : TestFun d) :
    |∫ x, (D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x| ≤
      D.Cψ hR hRs hFR * D.CmartG *
        (martDiff T (D.ghat R) * martDiff T w
          + martAvg T (D.ghat R) * martDiff T w * martDiff T (D.fthreeG hR hRs hFR)
          + martAvg T w * martDiff T (D.ghat R) * martDiff T (D.fthreeG hR hRs hFR)
          + martAvg T (D.ghat R) * martAvg T w * martDiff T (D.fthreeG hR hRs hFR) ^ 2) *
        T.vol := by
  have hTF := ((D.mem_setTG hR hRs hFR).mp hT).1
  have hA := D.abs_integral_thetaGT_mul_le hR hRs hFR hT w
  rw [D.martDiff_u_eq_of_mem_setFG hR hRs hFR hTF] at hA
  refine hA.trans ?_
  have hMu := D.Mu_nonneg
  have hC := D.Cψ_nonneg hR hRs hFR
  set Mu := D.Mu with hMudef
  set Cm := D.CmartG with hCm
  obtain ⟨c1, c2, c3, c4⟩ :
      (8 + 128 * Mu ≤ Cm) ∧ (8 * (8 + 128 * Mu) * Mu ≤ Cm) ∧
      (64 * Mu ≤ Cm) ∧ (512 * Mu ^ 2 ≤ Cm) :=
    martingale_coefficient_bounds hMu
  set Δg := martDiff T (D.ghat R)
  set Δw := martDiff T w
  set Δ3 := martDiff T (D.fthreeG hR hRs hFR)
  set Eg := martAvg T (D.ghat R)
  set Ew := martAvg T w
  have h1 : 0 ≤ Δg := martDiff_nonneg _ _
  have h2 : 0 ≤ Δw := martDiff_nonneg _ _
  have h3 : 0 ≤ Δ3 := martDiff_nonneg _ _
  have h4 : 0 ≤ Eg := martAvg_nonneg _ _
  have h5 : 0 ≤ Ew := martAvg_nonneg _ _
  have hvol := T.vol_pos.le
  have p1 := mul_le_mul_of_nonneg_right c1 (mul_nonneg h1 h2)
  have p2 := mul_le_mul_of_nonneg_right c2 (mul_nonneg (mul_nonneg h5 h1) h3)
  have p3 := mul_le_mul_of_nonneg_right c3 (mul_nonneg (mul_nonneg h4 h3) h2)
  have p4 := mul_le_mul_of_nonneg_right c4 (mul_nonneg (mul_nonneg h4 h5) (sq_nonneg Δ3))
  have key : (8 + 128 * Mu) * (Δg * Δw) + 8 * (8 + 128 * Mu) * (Ew * Δg * (Mu * Δ3))
      + 64 * (Eg * (Mu * Δ3) * Δw) + 512 * (Eg * Ew * (Mu * Δ3) ^ 2) ≤
      Cm * (Δg * Δw + Eg * Δw * Δ3 + Ew * Δg * Δ3 + Eg * Ew * Δ3 ^ 2) := by
    convert add_le_add (add_le_add (add_le_add p1 p2) p3) p4 using 1 <;> ring
  calc D.Cψ hR hRs hFR * (((8 + 128 * Mu) * (Δg * Δw) + 8 * (8 + 128 * Mu) * (Ew * Δg * (Mu * Δ3))
        + 64 * (Eg * (Mu * Δ3) * Δw) + 512 * (Eg * Ew * (Mu * Δ3) ^ 2)) * T.vol)
      ≤ D.Cψ hR hRs hFR * (Cm * (Δg * Δw + Eg * Δw * Δ3 + Ew * Δg * Δ3 + Eg * Ew * Δ3 ^ 2) *
          T.vol) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right key hvol) hC
    _ = _ := by ring

/-- The conjugate exponent `q' = q/(q−1)`. -/
noncomputable def q' : ℝ := D.q / (D.q - 1)

theorem one_lt_q' : 1 < D.q' := by
  have := D.hq
  unfold q'
  rw [lt_div_iff₀ (by linarith)]
  linarith

theorem q'_pos : 0 < D.q' := by linarith [D.one_lt_q']

theorem inv_q_add_inv_q' : 1 / D.q + 1 / D.q' = 1 := by
  have hq := D.hq
  have hq0 : D.q ≠ 0 := by linarith
  unfold q'
  rw [one_div_div, ← add_div, add_sub_cancel, div_self hq0]

theorem sub_one_mul_q' : (D.q - 1) * D.q' = D.q := by
  have hq := D.hq
  have h : D.q - 1 ≠ 0 := by linarith
  unfold q'
  field_simp

/-- The constant of Lemma 2.71 for the exponents `q`, `q'`. -/
noncomputable def C271q : ℝ :=
  Classical.choose (lemma271 D.hd D.q D.q' D.hq D.one_lt_q' D.inv_q_add_inv_q')

theorem C271q_nonneg : 0 ≤ D.C271q :=
  (Classical.choose_spec (lemma271 D.hd D.q D.q' D.hq D.one_lt_q' D.inv_q_add_inv_q')).1

theorem C271q_spec (C₀ : ℝ) (R : DyadicCube d) (f₁ f₂ f₃ : (Fin d → ℝ) → ℝ)
    (α : DyadicCube d → ℝ) (hC₀ : 0 ≤ C₀) (h₁ : MemLp f₁ (ENNReal.ofReal D.q) volume)
    (h₂ : MemLp f₂ (ENNReal.ofReal D.q') volume) (h₃ : MemLp f₃ ⊤ volume)
    (h₃1 : eLpNorm f₃ ⊤ volume ≤ 1)
    (hα : ∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T f₁ * martDiff T f₂
      + martAvg T f₁ * martDiff T f₂ * martDiff T f₃
      + martAvg T f₂ * martDiff T f₁ * martDiff T f₃
      + martAvg T f₁ * martAvg T f₂ * martDiff T f₃ ^ 2) * T.vol) :
    ∑' T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal (D.C271q * C₀) *
      (eLpNorm (truncate R f₁) (ENNReal.ofReal D.q) volume *
        eLpNorm (truncate R f₂) (ENNReal.ofReal D.q') volume) :=
  (Classical.choose_spec (lemma271 D.hd D.q D.q' D.hq D.one_lt_q' D.inv_q_add_inv_q')).2
    C₀ R f₁ f₂ f₃ α hC₀ h₁ h₂ h₃ h₃1 hα

/-- **(2.62) summed by Lemma 2.71** for `Θ'_𝐓`: `|∫ Θ'_𝐓 w| ≤ C_{2.71} C_ψ C_mart' ‖𝔤̂‖_q ‖w‖_{q'}`.
[PROVED] -/
theorem abs_integral_ThetaGT_mul_le (w : TestFun d) :
    |∫ x, (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x| ≤
      D.C271q * (D.Cψ hR hRs hFR * D.CmartG) *
        lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q * lpNorm (w : (Fin d → ℝ) → ℝ) D.q' := by
  classical
  have hC₀ : 0 ≤ D.Cψ hR hRs hFR * D.CmartG := mul_nonneg (D.Cψ_nonneg hR hRs hFR) D.CmartG_nonneg
  have hq'0 := D.q'_pos
  set α : DyadicCube d → ℝ := fun T => if T ∈ D.setTG hR hRs hFR then
    ∫ x, (D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x else 0 with hα
  have hsum : ∫ x, (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x =
      ∑ T ∈ D.setTG hR hRs hFR, α T := by
    have e : ∀ x, (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x =
        ∑ T ∈ D.setTG hR hRs hFR,
          (D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x := fun x => by
      rw [ThetaGT, Submodule.coe_sum, Finset.sum_apply, Finset.sum_mul]
    have hint : ∀ T : DyadicCube d, Integrable (fun x =>
        (D.thetaGT hR hRs hFR T : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x) volume :=
      fun T => (TestFun.memLp (D.thetaGT hR hRs hFR T).2 2).integrable_mul (TestFun.memLp w.2 2)
    simp_rw [e]
    rw [integral_finsetSum _ fun T _ => hint T]
    exact Finset.sum_congr rfl fun T hT => by simp only [hα, hT, ↓reduceIte]
  have hα_le : ∀ T ∈ R.tree, |α T| ≤ D.Cψ hR hRs hFR * D.CmartG *
      (martDiff T (D.ghat R) * martDiff T w
        + martAvg T (D.ghat R) * martDiff T w * martDiff T (D.fthreeG hR hRs hFR)
        + martAvg T w * martDiff T (D.ghat R) * martDiff T (D.fthreeG hR hRs hFR)
        + martAvg T (D.ghat R) * martAvg T w * martDiff T (D.fthreeG hR hRs hFR) ^ 2) * T.vol := by
    intro T _
    by_cases hT : T ∈ D.setTG hR hRs hFR
    · simp only [hα, hT, ↓reduceIte]
      exact D.abs_alphaG_le hR hRs hFR hT w
    · simp only [hα, hT, ↓reduceIte, abs_zero]
      have h1 := martDiff_nonneg T (D.ghat R : (Fin d → ℝ) → ℝ)
      have h2 := martDiff_nonneg T (w : (Fin d → ℝ) → ℝ)
      have h3 := martDiff_nonneg T (D.fthreeG hR hRs hFR : (Fin d → ℝ) → ℝ)
      have h4 := martAvg_nonneg T (D.ghat R : (Fin d → ℝ) → ℝ)
      have h5 := martAvg_nonneg T (w : (Fin d → ℝ) → ℝ)
      have h6 := T.vol_pos.le
      positivity
  have h271 := D.C271q_spec (D.Cψ hR hRs hFR * D.CmartG) R (D.ghat R) w
    (D.fthreeG hR hRs hFR) α hC₀ (TestFun.memLp (D.ghat R).2 _)
    (TestFun.memLp w.2 _) (TestFun.memLp (D.fthreeG hR hRs hFR).2 _)
    (D.eLpNorm_fthreeG_le hR hRs hFR) hα_le
  have hE₁ : eLpNorm (truncate R (D.ghat R : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.q)
      volume ≠ ⊤ := (TestFun.memLp (TestFun.truncateₗ R (D.ghat R)).2 _).eLpNorm_ne_top
  have hE₂ : eLpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.q') volume ≠ ⊤ :=
    (TestFun.memLp (TestFun.truncateₗ R w).2 _).eLpNorm_ne_top
  have hfin : ENNReal.ofReal (D.C271q * (D.Cψ hR hRs hFR * D.CmartG)) *
      (eLpNorm (truncate R (D.ghat R : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.q) volume *
        eLpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.q') volume) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hE₁ hE₂)
  have hsub : ∀ T ∈ D.setTG hR hRs hFR, T ∈ R.tree := fun T hT =>
    ((mem_nonleaf_iff D.hd).mp ((D.mem_setFG hR hRs hFR).mp ((D.mem_setTG hR hRs hFR).mp hT).1).1).1
  have h2 : ∑ T ∈ D.setTG hR hRs hFR, ‖α T‖ₑ ≤ ∑' T : R.tree, ‖α T‖ₑ := by
    rw [← Finset.sum_subtype_of_mem (fun T => ‖α T‖ₑ) hsub]
    exact ENNReal.sum_le_tsum _
  have h3 := ENNReal.toReal_mono hfin (h2.trans h271)
  rw [ENNReal.toReal_sum (fun T _ => enorm_ne_top), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg D.C271q_nonneg hC₀)] at h3
  simp only [toReal_enorm, Real.norm_eq_abs] at h3
  have e𝔤 : truncate R (D.ghat R : (Fin d → ℝ) → ℝ) = D.ghat R :=
    congrArg Subtype.val (TestFun.truncateₗ_of_supportedOn (D.ghat_supported R))
  have hw : lpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) D.q' ≤ lpNorm (w : (Fin d → ℝ) → ℝ) D.q' :=
    TestFun.lpNorm_truncateₗ_le R w hq'0
  have hnorm𝔤 : 0 ≤ lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  calc |∫ x, (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (w : (Fin d → ℝ) → ℝ) x|
      = |∑ T ∈ D.setTG hR hRs hFR, α T| := by rw [hsum]
    _ ≤ ∑ T ∈ D.setTG hR hRs hFR, |α T| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ D.C271q * (D.Cψ hR hRs hFR * D.CmartG) *
          (lpNorm (truncate R (D.ghat R : (Fin d → ℝ) → ℝ)) D.q *
            lpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) D.q') := h3
    _ = D.C271q * (D.Cψ hR hRs hFR * D.CmartG) * lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q *
          lpNorm (truncate R (w : (Fin d → ℝ) → ℝ)) D.q' := by rw [e𝔤]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (mul_nonneg (mul_nonneg D.C271q_nonneg hC₀) hnorm𝔤)

/-- `Θ'_𝐓` is constant on the cubes of `𝐏'_R`. [PROVED] -/
theorem ThetaGT_constOn {P : DyadicCube d} (hP : P ∈ D.partRG hR hRs hFR) :
    ConstOn (D.ThetaGT hR hRs hFR) P := by
  unfold ThetaGT
  refine constOn_sum fun T hT => ?_
  obtain ⟨hTn, hTs⟩ := (D.mem_setFG hR hRs hFR).mp ((D.mem_setTG hR hRs hFR).mp hT).1
  exact D.thetaGT_constOn hR hRs hFR hTn hTs hP

/-- The value `c_P` of `Θ'_𝐓` on the cube `P ∈ 𝐏'_R`. -/
noncomputable def cTG (P : DyadicCube d) : ℝ :=
  (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) (fun i => (2 : ℝ) ^ P.m * P.l i)

theorem ThetaGT_apply_eq_cTG {P : DyadicCube d} {x : Fin d → ℝ} (hP : P ∈ D.partRG hR hRs hFR)
    (hx : x ∈ P.toSet) : (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x = D.cTG hR hRs hFR P :=
  D.ThetaGT_constOn hR hRs hFR hP x hx _ P.corner_mem

/-- The dual test function `w = ∑_{P ∈ 𝐏'_R} c_P |c_P|^{q−2} 𝟙_P`. -/
noncomputable def wdualG : TestFun d :=
  ∑ P ∈ D.partRG hR hRs hFR,
    (D.cTG hR hRs hFR P * |D.cTG hR hRs hFR P| ^ (D.q - 2)) • TestFun.ind P

theorem wdualG_apply {P : DyadicCube d} {x : Fin d → ℝ} (hP : P ∈ D.partRG hR hRs hFR)
    (hx : x ∈ P.toSet) : (D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      D.cTG hR hRs hFR P * |D.cTG hR hRs hFR P| ^ (D.q - 2) := by
  rw [wdualG, Submodule.coe_sum, Finset.sum_apply, Finset.sum_eq_single P]
  · rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hx, Pi.one_apply,
      smul_eq_mul, mul_one]
  · intro P' hP' hne
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_notMem
      (fun h => Set.disjoint_left.mp (D.partRG_pairwiseDisjoint hR hRs hFR hP' hP hne) h hx),
      smul_zero]
  · exact fun h => absurd hP h

theorem wdualG_supportedOn : SupportedOn (D.wdualG hR hRs hFR) R := fun x hx => by
  rw [wdualG, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
    Set.indicator_of_notMem (fun h => hx (D.subset_of_mem_partRG hR hRs hFR hP h)), smul_zero]

/-- `∫ Θ'_𝐓 w = ∑_{P ∈ 𝐏'_R} |c_P|^q |P|`. [PROVED] -/
theorem integral_ThetaGT_mul_wdualG :
    ∫ x, (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      ∑ P ∈ D.partRG hR hRs hFR, |D.cTG hR hRs hFR P| ^ D.q * P.vol := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  rw [D.integral_eq_sum_partRG hR hRs hFR (f := fun x =>
      (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) x)
    ((TestFun.memLp (D.ThetaGT hR hRs hFR).2 2).integrable_mul
      (TestFun.memLp (D.wdualG hR hRs hFR).2 2))
    (fun x hx => by
      show (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) x =
        0
      rw [D.ThetaGT_supportedOn hR hRs hFR x hx, zero_mul])]
  refine Finset.sum_congr rfl fun P hP => ?_
  have e : ∫ x in P.toSet, (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x *
      (D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      ∫ x in P.toSet, (D.cTG hR hRs hFR P * (D.cTG hR hRs hFR P * |D.cTG hR hRs hFR P| ^ (D.q - 2)))
        :=
    setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
      show (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x * (D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) x =
        _
      rw [D.ThetaGT_apply_eq_cTG hR hRs hFR hP hx, D.wdualG_apply hR hRs hFR hP hx]
  rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le,
    smul_eq_mul, mul_comm, mul_mul_abs_rpow_eq hq0]

theorem lpNorm_ThetaGT_rpow_eq :
    lpNorm (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ^ D.q =
      ∑ P ∈ D.partRG hR hRs hFR, |D.cTG hR hRs hFR P| ^ D.q * P.vol := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  rw [lpNorm_rpow_eq_integral hq0 (TestFun.memLp (D.ThetaGT hR hRs hFR).2 _),
    D.integral_abs_rpow_eq_sum_partRG hR hRs hFR (D.ThetaGT_supportedOn hR hRs hFR) hq0]
  refine Finset.sum_congr rfl fun P hP => ?_
  have e : ∫ x in P.toSet, |(D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q =
      ∫ x in P.toSet, |D.cTG hR hRs hFR P| ^ D.q :=
    setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
      show |(D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q = _
      rw [D.ThetaGT_apply_eq_cTG hR hRs hFR hP hx]
  rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le,
    smul_eq_mul, mul_comm]

theorem lpNorm_wdualG_rpow_eq :
    lpNorm (D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q' ^ D.q' =
      ∑ P ∈ D.partRG hR hRs hFR, |D.cTG hR hRs hFR P| ^ D.q * P.vol := by
  have hq'0 := D.q'_pos
  rw [lpNorm_rpow_eq_integral hq'0 (TestFun.memLp (D.wdualG hR hRs hFR).2 _),
    D.integral_abs_rpow_eq_sum_partRG hR hRs hFR (D.wdualG_supportedOn hR hRs hFR) hq'0]
  refine Finset.sum_congr rfl fun P hP => ?_
  have e : ∫ x in P.toSet, |(D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q' =
      ∫ x in P.toSet, |D.cTG hR hRs hFR P| ^ D.q :=
    setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
      show |(D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.q' = _
      rw [D.wdualG_apply hR hRs hFR hP hx, abs_mul_abs_rpow_rpow_eq D.hq hq'0 D.sub_one_mul_q']
  rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le,
    smul_eq_mul, mul_comm]

include hR hRs in
/-- The norm bound for `𝔤̂ = ψ_R 𝟙_R`: `‖𝔤̂‖_q ≤ C_ψ' K |R|^{1/q}` (`C_ψ'` the constant of
`lpNorm_truncateₗ_psi_le`). [PROVED] -/
theorem lpNorm_ghat_le (hG : D.GBound) :
    lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q ≤ D.psiConst * D.KQ * R.vol ^ (1 / D.q) := by
  have h := D.lpNorm_truncateₗ_psi_le hG hR hRs
  rw [← ghat_eq, ← rpow_div_eq R.vol_pos D.Q.vol_pos] at h
  refine h.trans (le_of_eq ?_)
  unfold KQ
  ring

/-- **The `𝐓'`-portion** (p. 54): `‖Θ'_𝐓‖_q ≤ C_{2.71} C_ψ C_mart' · C_ψ' K |R|^{1/q}`. [PROVED] -/
theorem lpNorm_ThetaGT_le (hG : D.GBound) :
    lpNorm (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ≤
      D.C271q * (D.Cψ hR hRs hFR * D.CmartG) * (D.psiConst * D.KQ * R.vol ^ (1 / D.q)) := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hq'0 := D.q'_pos
  have hK₁ : 0 ≤ D.C271q * (D.Cψ hR hRs hFR * D.CmartG) :=
    mul_nonneg D.C271q_nonneg (mul_nonneg (D.Cψ_nonneg hR hRs hFR) D.CmartG_nonneg)
  set A := ∑ P ∈ D.partRG hR hRs hFR, |D.cTG hR hRs hFR P| ^ D.q * P.vol with hAdef
  have hA0 : 0 ≤ A :=
    Finset.sum_nonneg fun P _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) P.vol_pos.le
  have hN : lpNorm (D.ThetaGT hR hRs hFR : (Fin d → ℝ) → ℝ) D.q = A ^ (1 / D.q) := by
    rw [hAdef, ← D.lpNorm_ThetaGT_rpow_eq hR hRs hFR, one_div,
      Real.rpow_rpow_inv (lpNorm_nonneg _ _) hq0.ne']
  have hW : lpNorm (D.wdualG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q' = A ^ (1 / D.q') := by
    rw [hAdef, ← D.lpNorm_wdualG_rpow_eq hR hRs hFR, one_div,
      Real.rpow_rpow_inv (lpNorm_nonneg _ _) hq'0.ne']
  have hmain := D.abs_integral_ThetaGT_mul_le hR hRs hFR (D.wdualG hR hRs hFR)
  rw [D.integral_ThetaGT_mul_wdualG hR hRs hFR, abs_of_nonneg hA0, hW] at hmain
  have h𝔤 := D.lpNorm_ghat_le hR hRs hG
  rw [hN]
  by_cases hA : A = 0
  · rw [hA, Real.zero_rpow (one_div_pos.mpr hq0).ne']
    exact mul_nonneg hK₁ (mul_nonneg (mul_nonneg D.psiConst_nonneg D.KQ_nonneg)
      (Real.rpow_nonneg R.vol_pos.le _))
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
    have hsplit : A ^ (1 / D.q) * A ^ (1 / D.q') = A := by
      rw [← Real.rpow_add hApos, D.inv_q_add_inv_q', Real.rpow_one]
    have h1 : A ^ (1 / D.q) * A ^ (1 / D.q') ≤ D.C271q * (D.Cψ hR hRs hFR * D.CmartG) *
        lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q * A ^ (1 / D.q') := by
      rw [hsplit]
      exact hmain
    have h2 := le_of_mul_le_mul_right h1 (Real.rpow_pos_of_pos hApos _)
    calc A ^ (1 / D.q)
        ≤ D.C271q * (D.Cψ hR hRs hFR * D.CmartG) * lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h𝔤 hK₁

/-- The constant of the bound on `‖Θ'‖_q`:
`C_Θ' = 2 C_ψ C_{φ,T} (2^d/ε) + C_{2.71} C_ψ C_mart' C_ψ'`. -/
noncomputable def CΘG : ℝ :=
  2 * D.Cψ hR hRs hFR * D.CφT * (2 ^ d / D.ε) +
    D.C271q * (D.Cψ hR hRs hFR * D.CmartG) * D.psiConst

theorem CΘG_nonneg : 0 ≤ D.CΘG hR hRs hFR := by
  have := D.ε_pos
  have := D.CφT_nonneg
  have := D.Cψ_nonneg hR hRs hFR
  have := D.C271q_nonneg
  have := D.CmartG_nonneg
  have := D.psiConst_nonneg
  unfold CΘG
  positivity

/-- **The bound on `‖Θ'‖_q`** (p. 54): `‖Θ'‖_q ≤ C_Θ' |Q|^{-1/q} ‖g‖_q |R|^{1/q}`. [PROVED] -/
theorem lpNorm_ThetaG_le (hG : D.GBound) :
    lpNorm (D.ThetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ≤
      D.CΘG hR hRs hFR * D.KQ * R.vol ^ (1 / D.q) := by
  rw [D.ThetaG_eq_add hR hRs hFR]
  refine (TestFun.lpNorm_add_le _ _ D.hq.le).trans ?_
  have h1 := D.lpNorm_ThetaGP_le hR hRs hFR hG
  have h2 := D.lpNorm_ThetaGT_le hR hRs hFR hG
  unfold CΘG
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- Exponent bookkeeping for (2.59):
`(|R|/|Q|)^{1−1/r−1/q} |R|^{1/r} |R|^{1/q} |Q|^{-1/q} = |R| |Q|^{1/r−1}`. [PROVED] -/
theorem rpow_fact3 {s V r q : ℝ} (hs : 0 < s) (hV : 0 < V) :
    (s / V) ^ (1 - 1 / r - 1 / q) * s ^ (1 / r) * s ^ (1 / q) * V ^ (-(1 / q)) =
      s * V ^ (1 / r - 1) := by
  rw [Real.div_rpow hs.le hV.le, div_eq_mul_inv, ← Real.rpow_neg hV.le,
    show s ^ (1 - 1 / r - 1 / q) * V ^ (-(1 - 1 / r - 1 / q)) * s ^ (1 / r) * s ^ (1 / q) *
      V ^ (-(1 / q)) = (s ^ (1 - 1 / r - 1 / q) * s ^ (1 / r) * s ^ (1 / q)) *
      (V ^ (-(1 - 1 / r - 1 / q)) * V ^ (-(1 / q))) by ring,
    ← Real.rpow_add hs, ← Real.rpow_add hs, ← Real.rpow_add hV]
  congr 1
  · rw [show 1 - 1 / r - 1 / q + 1 / r + 1 / q = (1 : ℝ) by ring, Real.rpow_one]
  · congr 1
    ring

/-- The constant of the estimate of (2.59):
`C₅₉ = B C_G^{1−1/r−1/q} B^{1/r} (2^d B/ε)^{1/q} C_Θ'`. -/
noncomputable def C₅₉ : ℝ :=
  D.B * D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.B ^ (1 / D.r) * (2 ^ d * D.B / D.ε) ^ (1 / D.q) *
    D.CΘG hR hRs hFR

/-- **The estimate of the term (2.59)** (p. 54): `|Λ_R(v, θ')| ≤ C₅₉ E_R`, from the testing
condition
(1.9) for `τ`, `𝐐_R`, the local bounds `F_R ≤ (C_G |R|/|Q|)^{1−1/r−1/q} F`, `‖v‖_r ≤ (B|R|)^{1/r}`,
the
reduction `‖θ'‖_q ≤ (2^d B/ε)^{1/q} ‖Θ'‖_q` and the bound on `‖Θ'‖_q`. [PROVED] -/
theorem abs_form2_vP_thetaG_le_E (hG : D.GBound) :
    |twoSlotForm D.T D.a D.b D.g R (D.vP R) (D.thetaG hR hRs hFR)| ≤
      D.C₅₉ hR hRs hFR * D.E R := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  have hR0 := R.vol_pos
  have hF := D.Fpos'
  have hCG := D.CG_pos
  have hG0 := lpNorm_nonneg (D.G : (Fin d → ℝ) → ℝ) D.q
  have hv0 := lpNorm_nonneg (D.vP R : (Fin d → ℝ) → ℝ) D.r
  have hθ0 := lpNorm_nonneg (D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q
  have hFP0 := D.FP_nonneg R
  have hCΘ0 := D.CΘG_nonneg hR hRs hFR
  have hdiv : 0 ≤ R.vol / D.Q.vol := by positivity
  have h1 := D.abs_form2_vP_thetaG_le hR hRs hFR
  have hFP := D.FP_le (D.good_of_notInStopping hR hRs)
  have hv := D.lpNorm_vP_le hR.1
  have hMu : 0 ≤ (2 ^ d * D.B / D.ε) ^ (1 / D.q) := by positivity
  have hθ : lpNorm (D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q ≤
      (2 ^ d * D.B / D.ε) ^ (1 / D.q) * (D.CΘG hR hRs hFR * D.KQ * R.vol ^ (1 / D.q)) :=
    (D.lpNorm_thetaG_le hR hRs hFR).trans
      (mul_le_mul_of_nonneg_left (D.lpNorm_ThetaG_le hR hRs hFR hG) hMu)
  have hexp := rpow_fact3 (r := D.r) (q := D.q) hR0 hV
  calc |twoSlotForm D.T D.a D.b D.g R (D.vP R) (D.thetaG hR hRs hFR)|
      ≤ D.B * D.FP R * lpNorm (D.vP R : (Fin d → ℝ) → ℝ) D.r *
          lpNorm (D.thetaG hR hRs hFR : (Fin d → ℝ) → ℝ) D.q := h1
    _ ≤ D.B * ((D.CG * (R.vol / D.Q.vol)) ^ (1 - 1 / D.r - 1 / D.q) * D.F) *
          (D.B * R.vol) ^ (1 / D.r) *
          ((2 ^ d * D.B / D.ε) ^ (1 / D.q) * (D.CΘG hR hRs hFR * D.KQ * R.vol ^ (1 / D.q))) := by
        gcongr
    _ = D.B * D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.B ^ (1 / D.r) * (2 ^ d * D.B / D.ε) ^ (1 / D.q) *
          D.CΘG hR hRs hFR * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) *
          ((R.vol / D.Q.vol) ^ (1 - 1 / D.r - 1 / D.q) * R.vol ^ (1 / D.r) * R.vol ^ (1 / D.q) *
            D.Q.vol ^ (-(1 / D.q))) := by
        rw [Real.mul_rpow hCG.le hdiv, Real.mul_rpow hB hR0.le]
        unfold KQ
        ring
    _ = D.C₅₉ hR hRs hFR * D.E R := by
        rw [hexp]
        unfold C₅₉ E
        ring

end Term259

/-! ### §2.8 The estimate of the term (2.60) (p. 54–56)

(2.60) `= ∑_T Λ_R(X_T, Y_T)` with `X_T = ψ_T v_T − ∑_{T'} ψ_{T'} v_{T'}`,
`Y_T = φ_T u_T − ∑_{T'} φ_{T'} u_{T'}`, both of mean zero and supported on `T`, so that `Λ_R` may be
replaced by `Λ_T`; the sum runs over the non-leaf cubes `T ⊆ R` in no stopping cube of either
stopping
time (otherwise one of `X_T`, `Y_T` vanishes). Writing `X_T = ∑_ε (ψ_T − ψ_{T_ε}) v 𝟙_{T_ε}` and
`Y_T = ∑_{ε'} (φ_T − φ_{T_{ε'}}) u 𝟙_{T_{ε'}}` over the children, (2.64),
`Λ_T(X_T, Y_T) = ∑_{ε, ε'} (ψ_T − ψ_{T_ε})(φ_T − φ_{T_{ε'}}) Λ_T(v 𝟙_{T_ε}, u 𝟙_{T_{ε'}})`, and each
`|Λ_T(v 𝟙_{T_ε}, u 𝟙_{T_{ε'}})| ≤ C F |Q|^{-a} |T|`, `a = 1 − 1/r − 1/q`: for `ε ≠ ε'` by the decay
condition (1.1), for `ε = ε'` by moving `Λ_T` to `Λ_{T_ε}` (decay) and (2.66): the testing condition
for `b_{τ,𝐐_{T_ε},k}` and the stopping condition (2.10) for `v − [v]_{T_ε} b_{τ,𝐐_{T_ε},k}`. The
remaining sums `∑_T (∑_ε |ψ_T − ψ_{T_ε}|)(∑_{ε'} |φ_T − φ_{T_{ε'}}|) |T|` are handled as in §2.6:
the
parents of `𝐏 ∩ 𝐏₄` and of `𝐒 ∩ 𝐒₄` by bounded overlap, the other cubes by (2.61), Cauchy–Schwarz
and Lemma 2.72 with `f₁ = 𝔥`, `f₂ = 𝔤̂`, `f₃ = 𝟙_R`, `f₄ = û/M_u`, `f₅ = v̂/M_v`. -/

section Term260

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

/-- `c_T f 𝟙_T − ∑_{T' child of T} c_{T'} f 𝟙_{T'} = ∑_ε (c_T − c_{T_ε}) f 𝟙_{T_ε}`. [PROVED] -/
theorem smul_truncateₗ_sub_sum_children (c : DyadicCube d → ℝ) (f : TestFun d)
    (T : DyadicCube d) :
    c T • TestFun.truncateₗ T f - ∑ T' ∈ children T, c T' • TestFun.truncateₗ T' f =
      ∑ ε : Fin d → Bool, (c T - c (T.child ε)) • TestFun.truncateₗ (T.child ε) f := by
  have e : TestFun.truncateₗ T f = ∑ ε : Fin d → Bool, TestFun.truncateₗ (T.child ε) f := by
    rw [← TestFun.sum_truncateₗ_children T (TestFun.truncateₗ T f)
      (TestFun.truncateₗ_supportedOn T f)]
    exact Finset.sum_congr rfl fun ε _ =>
      TestFun.truncateₗ_truncateₗ_of_subset (T.child_subset ε) f
  rw [e, Finset.smul_sum, children, Finset.sum_image fun ε _ ε' _ h => T.child_injective h,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ε _ => by module

/-- **Two-slot decay (1.1)**: `|Λ_R(ρ, ρ')| ≤ F_R ‖ρ‖_{p_a} ‖ρ'‖_{p_b}` when `ρ`, `ρ'` are supported
on
different children of `R`. [PROVED] -/
theorem abs_twoSlotForm_le_of_children (T : PerfectCZForm d n) (p : HolderTuple n) {a b : Fin n}
    (hab : a ≠ b) (g : Fin n → TestFun d) (R : DyadicCube d) {ε ε' : Fin d → Bool} (hne : ε ≠ ε')
    {ρ ρ' : TestFun d} (hρ : SupportedOn ρ (R.child ε)) (hρ' : SupportedOn ρ' (R.child ε')) :
    |twoSlotForm T a b g R ρ ρ'| ≤
      (∏ j ∈ (Finset.univ.erase a).erase b,
          lpNorm (TestFun.truncateₗ R (g j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p a) * lpNorm (ρ' : (Fin d → ℝ) → ℝ) (p.p b) := by
  have hρR : TestFun.truncateₗ R ρ = ρ :=
    TestFun.truncateₗ_of_supportedOn fun x hx => hρ x fun h => hx (R.child_subset ε h)
  have hρ'R : TestFun.truncateₗ R ρ' = ρ' :=
    TestFun.truncateₗ_of_supportedOn fun x hx => hρ' x fun h => hx (R.child_subset ε' h)
  unfold twoSlotForm
  rw [hρR, hρ'R]
  set e : Fin n → TestFun d :=
    Function.update (Function.update (fun j => TestFun.truncateₗ R (g j)) a ρ) b ρ' with he
  have hea : e a = ρ := by rw [he, Function.update_of_ne hab, Function.update_self]
  have heb : e b = ρ' := by rw [he, Function.update_self]
  have hsupp : ∀ j, SupportedOn (e j) R := by
    intro j
    by_cases hjb : j = b
    · rw [hjb, heb]
      exact fun x hx => hρ' x fun h => hx (R.child_subset ε' h)
    · by_cases hja : j = a
      · rw [hja, hea]
        exact fun x hx => hρ x fun h => hx (R.child_subset ε h)
      · rw [he, Function.update_of_ne hjb, Function.update_of_ne hja]
        exact TestFun.truncateₗ_supportedOn R _
  have h := T.decay p R e hsupp ⟨a, b, hab, ε, ε', hne, by rw [hea]; exact hρ, by rw [heb]; exact
    hρ'⟩
  refine h.trans (le_of_eq ?_)
  rw [he, prodNorm_update_update p hab]

/-- The children of a cube in no stopping cube are good cubes. [PROVED] -/
theorem child_good_of_notInStopping {T : DyadicCube d} (hTs : D.NotInStopping T)
    (ε : Fin d → Bool) (hmem : T.child ε ∈ D.tree) : D.Good (T.child ε) := by
  refine ⟨hmem, fun S hS ε' hsub => ?_⟩
  have hcS : (T.child ε).toSet ⊆ S.toSet := hsub.trans (S.child_subset ε')
  have hTS : ¬ T.toSet ⊆ S.toSet := hTs S hS
  have hcT := T.child_subset ε
  have hST : S.toSet ⊆ T.toSet := by
    rcases le_total S.m T.m with hm | hm
    · rcases DyadicCube.subset_or_disjoint S T hm with h | h
      · exact h
      · exact absurd (hcT (T.child ε).corner_mem)
          (Set.disjoint_left.mp h (hcS (T.child ε).corner_mem))
    · rcases DyadicCube.subset_or_disjoint T S hm with h | h
      · exact absurd h hTS
      · exact absurd (hcS (T.child ε).corner_mem)
          (Set.disjoint_left.mp h (hcT (T.child ε).corner_mem))
  have hne : S ≠ T := fun e => hTS (e ▸ subset_rfl)
  obtain ⟨ε'', hSc⟩ := DyadicCube.exists_child_of_ssubset D.hd hST hne
  have hcc : (T.child ε).toSet ⊆ (T.child ε'').toSet := hcS.trans hSc
  have hεε : ε = ε'' := by
    by_contra h
    exact Set.disjoint_left.mp (T.child_disjoint h) (T.child ε).corner_mem
      (hcc (T.child ε).corner_mem)
  subst hεε
  have hm1 := DyadicCube.m_le_of_subset D.hd hcS
  have hm2 := DyadicCube.m_le_of_subset D.hd hSc
  have e : T.child ε = S := DyadicCube.eq_of_subset_of_m_eq hcS (le_antisymm hm1 hm2)
  rw [← e] at hsub
  have h3 := DyadicCube.m_le_of_subset D.hd hsub
  have h' : ((T.child ε).child ε').m = (T.child ε).m - 1 := rfl
  omega

/-- `∑_ε |[f]_{T_ε} − [f]_T| ≤ 2^d Δ_T f`, by Cauchy–Schwarz. [PROVED] -/
theorem sum_abs_sub_avg_le (T : DyadicCube d) (f : (Fin d → ℝ) → ℝ) :
    ∑ ε : Fin d → Bool, |avg (T.child ε) f - avg T f| ≤ 2 ^ d * martDiff T f := by
  have hvol : ∀ ε : Fin d → Bool, 0 < (T.child ε).vol := fun ε => (T.child ε).vol_pos
  have hT := T.vol_pos
  have h := sum_abs_mul_abs_mul_le Finset.univ (fun ε => avg (T.child ε) f - avg T f)
    (fun ε => ((T.child ε).vol)⁻¹) (fun ε => (T.child ε).vol) (fun ε => (hvol ε).le)
  have e1 : ∀ ε : Fin d → Bool, |avg (T.child ε) f - avg T f| * |((T.child ε).vol)⁻¹| *
      (T.child ε).vol = |avg (T.child ε) f - avg T f| := fun ε => by
    rw [abs_inv, abs_of_pos (hvol ε), mul_assoc, inv_mul_cancel₀ (hvol ε).ne', mul_one]
  have e2 : ∑ ε : Fin d → Bool, (((T.child ε).vol)⁻¹) ^ 2 * (T.child ε).vol =
      2 ^ d * (2 ^ d / T.vol) := by
    have h1 : ∀ ε : Fin d → Bool, (((T.child ε).vol)⁻¹) ^ 2 * (T.child ε).vol = 2 ^ d / T.vol := by
      intro ε
      have := (hvol ε).ne'
      rw [← T.vol_child ε]
      field_simp
    rw [Finset.sum_congr rfl fun ε _ => h1 ε, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  simp only [e1] at h
  rw [e2] at h
  refine h.trans (le_of_eq ?_)
  change Real.sqrt (dsq T f) * Real.sqrt (2 ^ d * (2 ^ d / T.vol)) = 2 ^ d * martDiff T f
  have hs := (Real.sqrt_pos.mpr hT).ne'
  rw [sqrt_dsq_eq, show (2 : ℝ) ^ d * (2 ^ d / T.vol) = (2 ^ d / Real.sqrt T.vol) ^ 2 by
    rw [div_pow, Real.sq_sqrt hT.le]; ring, Real.sqrt_sq (by positivity)]
  field_simp

open Classical in
/-- `∑_{T ∈ s} |T| ≤ M |R|` for a collection `s` of subcubes of `R` with overlap at most `M`.
[PROVED] -/
theorem sum_vol_le_of_card_le (s : Finset (DyadicCube d)) {R : DyadicCube d}
    (hs : ∀ T ∈ s, T.toSet ⊆ R.toSet) {M : ℝ}
    (hM : ∀ x, ((s.filter fun T => x ∈ T.toSet).card : ℝ) ≤ M) :
    ∑ T ∈ s, T.vol ≤ M * R.vol := by
  have h := sum_setIntegral_le_of_overlap_real s hM (TestFun.ind R) one_pos
  simp only [Real.rpow_one] at h
  have h2 : ∫ x, |((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) x| = R.vol := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [TestFun.coe_ind, Set.indicator_of_notMem hx, abs_zero])]
    exact TestFun.setIntegral_abs_ind (subset_refl _)
  rwa [Finset.sum_congr rfl fun T hT => TestFun.setIntegral_abs_ind (hs T hT), h2] at h

open Classical in
/-- The index set of (2.60): the non-leaf cubes `T ⊆ R` in no stopping cube of either stopping
time. -/
noncomputable def setF2 : Finset (DyadicCube d) :=
  (nonleaf (D.second R hR hRs hFR).N R).filter
    (fun T => D.NotInStopping T ∧ (D.second R hR hRs hFR).NotInStopping T)

open Classical in
theorem mem_setF2 {T : DyadicCube d} :
    T ∈ D.setF2 hR hRs hFR ↔ T ∈ nonleaf (D.second R hR hRs hFR).N R ∧
      (D.NotInStopping T ∧ (D.second R hR hRs hFR).NotInStopping T) := Finset.mem_filter

theorem setF2_subset_setF : D.setF2 hR hRs hFR ⊆ D.setF hR hRs hFR := fun _ hT =>
  (D.mem_setF hR hRs hFR).mpr ⟨((D.mem_setF2 hR hRs hFR).mp hT).1,
    ((D.mem_setF2 hR hRs hFR).mp hT).2.2⟩

theorem setF2_subset_setFG : D.setF2 hR hRs hFR ⊆ D.setFG hR hRs hFR := fun _ hT =>
  (D.mem_setFG hR hRs hFR).mpr ⟨((D.mem_setF2 hR hRs hFR).mp hT).1,
    ((D.mem_setF2 hR hRs hFR).mp hT).2.1⟩

/-- **(2.60) as a sum over `setF2` of the forms `Λ_T`**: the terms with `T` inside a stopping cube
vanish, and `Λ_R` may be replaced by `Λ_T` by smoothness. [PROVED] -/
theorem sum_2_60_eq :
    ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, twoSlotForm D.T D.a D.b D.g R
        (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T') =
      ∑ T ∈ D.setF2 hR hRs hFR, twoSlotForm D.T D.a D.b D.g T
        (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T') := by
  rw [setF2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTR : T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp hT).1
  by_cases h : D.NotInStopping T ∧ (D.second R hR hRs hFR).NotInStopping T
  · simp only [h, and_self, ↓reduceIte]
    exact (twoSlotForm_eq_of_subset D.T D.a D.b D.g hTR _
      (supportedOn_sub (D.yT_supportedOn R T) (supportedOn_sum_children (D.yT_supportedOn R) T))
      (D.yT_sub_sum_meanZero hR hRs hFR hT)).symm
  · simp only [h, ↓reduceIte]
    rw [not_and_or] at h
    rcases h with h | h
    · simp only [NotInStopping, not_forall, not_not] at h
      obtain ⟨P, hP, hTP⟩ := h
      rw [D.yT_sub_sum_eq_zero hP hTP hTR, twoSlotForm_zero_right]
    · simp only [NotInStopping, not_forall, not_not] at h
      obtain ⟨S, hS, hTS⟩ := h
      rw [D.xT_sub_sum_eq_zero hR hRs hFR hS hTS, twoSlotForm_zero_left D.T D.hab]

/-- `X_T = ∑_ε (ψ_T − ψ_{T_ε}) v 𝟙_{T_ε}`. [PROVED] -/
theorem xT_sub_sum_eq (T : DyadicCube d) :
    D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T' =
      ∑ ε : Fin d → Bool,
        (D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)) •
          TestFun.truncateₗ (T.child ε) (D.vP R) :=
  smul_truncateₗ_sub_sum_children (D.psiT hR hRs hFR) (D.vP R) T

/-- `Y_T = ∑_ε (φ_T − φ_{T_ε}) u 𝟙_{T_ε}`. [PROVED] -/
theorem yT_sub_sum_eq (T : DyadicCube d) :
    D.yT R T - ∑ T' ∈ children T, D.yT R T' =
      ∑ ε : Fin d → Bool, (D.phiT R T - D.phiT R (T.child ε)) • TestFun.truncateₗ (T.child ε) D.u :=
  smul_truncateₗ_sub_sum_children (D.phiT R) D.u T

/-- **(2.64)**: `Λ_T(X_T, Y_T) = ∑_{ε,ε'} (ψ_T − ψ_{T_ε})(φ_T − φ_{T_{ε'}}) Λ_T(v 𝟙_{T_ε}, u
𝟙_{T_{ε'}})`.
[PROVED] -/
theorem form2_XY_eq (T : DyadicCube d) :
    twoSlotForm D.T D.a D.b D.g T (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T') =
      ∑ ε : Fin d → Bool, ∑ ε' : Fin d → Bool,
        (D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)) *
          (D.phiT R T - D.phiT R (T.child ε')) *
          twoSlotForm D.T D.a D.b D.g T (TestFun.truncateₗ (T.child ε) (D.vP R))
            (TestFun.truncateₗ (T.child ε') D.u) := by
  rw [D.xT_sub_sum_eq hR hRs hFR T, D.yT_sub_sum_eq T, twoSlotForm_sum_left D.T D.hab]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [twoSlotForm_sum_right]
  refine Finset.sum_congr rfl fun ε' _ => ?_
  rw [twoSlotForm_smul_left D.T D.hab, twoSlotForm_smul_right]
  ring

/-- `|Λ_T(X_T, Y_T)| ≤ K (∑_ε |ψ_T − ψ_{T_ε}|)(∑_{ε'} |φ_T − φ_{T_{ε'}}|)` when every
`|Λ_T(v 𝟙_{T_ε}, u 𝟙_{T_{ε'}})| ≤ K`. [PROVED] -/
theorem abs_form2_XY_le_of (T : DyadicCube d) {K : ℝ}
    (hK : ∀ ε ε' : Fin d → Bool, |twoSlotForm D.T D.a D.b D.g T
      (TestFun.truncateₗ (T.child ε) (D.vP R)) (TestFun.truncateₗ (T.child ε') D.u)| ≤ K) :
    |twoSlotForm D.T D.a D.b D.g T (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T')| ≤
      K * ((∑ ε : Fin d → Bool, |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)|) *
        ∑ ε' : Fin d → Bool, |D.phiT R T - D.phiT R (T.child ε')|) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK default default)
  rw [D.form2_XY_eq hR hRs hFR T, Finset.sum_mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ε _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ε' _ => ?_)
  rw [abs_mul, abs_mul]
  calc |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)| *
        |D.phiT R T - D.phiT R (T.child ε')| * |twoSlotForm D.T D.a D.b D.g T
          (TestFun.truncateₗ (T.child ε) (D.vP R)) (TestFun.truncateₗ (T.child ε') D.u)|
      ≤ |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)| *
        |D.phiT R T - D.phiT R (T.child ε')| * K :=
        mul_le_mul_of_nonneg_left (hK ε ε') (by positivity)
    _ = _ := by ring

/-! The per-cube bound `|Λ_T(v 𝟙_{T_ε}, u 𝟙_{T_{ε'}})| ≤ C_diag F |Q|^{-a} |T|` for `T ∈ setF2`. -/

/-- The exponent `a = 1 − 1/r − 1/q = ∑_{j ≠ k,k+1} 1/p_j` is nonnegative. [PROVED] -/
theorem exp_a_nonneg : 0 ≤ 1 - 1 / D.r - 1 / D.q := by
  rw [← D.sum_J_inv]
  exact Finset.sum_nonneg fun j _ => by have := D.p.one_lt j; positivity

/-- `F_P ≤ C_G^a F |P|^a |Q|^{-a}` on good cubes. [PROVED] -/
theorem FP_le' {P : DyadicCube d} (hP : D.Good P) :
    D.FP P ≤ D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.F * P.vol ^ (1 - 1 / D.r - 1 / D.q) *
      D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) := by
  have hV := D.Q.vol_pos
  have hP0 := P.vol_pos
  refine (D.FP_le hP).trans (le_of_eq ?_)
  rw [Real.mul_rpow D.CG_pos.le (by positivity), Real.div_rpow hP0.le hV.le, Real.rpow_neg hV.le,
    div_eq_mul_inv]
  ring

/-- `‖v 𝟙_P‖_r ≤ (2^d B/ε |P|)^{1/r}` on good cubes of the second stopping time. [PROVED] -/
theorem lpNorm_truncateₗ_vP_le {P : DyadicCube d} (hP : (D.second R hR hRs hFR).Good P) :
    lpNorm (TestFun.truncateₗ P (D.vP R) : (Fin d → ℝ) → ℝ) D.r ≤
      (2 ^ d * D.B / D.ε * P.vol) ^ (1 / D.r) := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hR0 := R.vol_pos
  refine TestFun.lpNorm_le_rpow_of_integral_le _ hr0 ?_
  rw [← lpNorm_rpow_eq_integral hr0 (TestFun.memLp (TestFun.truncateₗ P (D.vP R)).2 _),
    TestFun.lpNorm_truncateₗ_rpow P _ hr0]
  refine (D.setIntegral_vP_rpow_le hR hRs hFR hP).trans (le_of_eq ?_)
  calc 2 ^ d / D.ε * (P.vol / R.vol) * (D.B * R.vol)
      = 2 ^ d / D.ε * D.B * (P.vol / R.vol * R.vol) := by ring
    _ = 2 ^ d * D.B / D.ε * P.vol := by
        rw [div_mul_cancel₀ _ hR0.ne']
        ring

theorem mem_tree_of_mem_setF2 {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR) : T ∈ D.tree :=
  D.second_tree_subset hR hRs hFR
    (D.mem_second_tree_of_mem_nonleaf hR hRs hFR ((D.mem_setF2 hR hRs hFR).mp hT).1)

theorem good_of_mem_setF2 {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR) : D.Good T :=
  D.good_of_notInStopping (D.mem_tree_of_mem_setF2 hR hRs hFR hT)
    ((D.mem_setF2 hR hRs hFR).mp hT).2.1

theorem child_good_of_mem_setF2 {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR)
    (ε : Fin d → Bool) : D.Good (T.child ε) :=
  D.child_good_of_notInStopping ((D.mem_setF2 hR hRs hFR).mp hT).2.1 ε
    (D.second_tree_subset hR hRs hFR (D.child_mem_second_tree_of_mem_nonleaf hR hRs hFR
      ((D.mem_setF2 hR hRs hFR).mp hT).1 ε))

theorem child_second_good_of_mem_setF2 {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR)
    (ε : Fin d → Bool) : (D.second R hR hRs hFR).Good (T.child ε) :=
  (D.second R hR hRs hFR).child_good_of_notInStopping ((D.mem_setF2 hR hRs hFR).mp hT).2.2 ε
    (D.child_mem_second_tree_of_mem_nonleaf hR hRs hFR ((D.mem_setF2 hR hRs hFR).mp hT).1 ε)

theorem subset_R_of_mem_setF2 {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR) :
    T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp ((D.mem_setF2 hR hRs hFR).mp hT).1).1

/-- `C_dec = C_G^a (2^d B/ε)^{1/r} (2^d B/ε)^{1/q}`, the constant of the decay terms. -/
noncomputable def Cdec : ℝ :=
  D.CG ^ (1 - 1 / D.r - 1 / D.q) * (2 ^ d * D.B / D.ε) ^ (1 / D.r) *
    (2 ^ d * D.B / D.ε) ^ (1 / D.q)

/-- `C_test = M_v B C_G^a B^{1/r} (2^d B/ε)^{1/q}`, the constant of the testing term in (2.66). -/
noncomputable def Ctest : ℝ :=
  D.Mv * D.B * D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.B ^ (1 / D.r) * (2 ^ d * D.B / D.ε) ^ (1 / D.q)

/-- `C_{2.10} = 2^d B ε^{-1} B^{1/q} ((2^d B/ε)^{1/r} + M_v B^{1/r})`, the constant of the (2.10)
term
in (2.66). -/
noncomputable def C210 : ℝ :=
  2 ^ d * D.B * D.ε⁻¹ * D.B ^ (1 / D.q) * ((2 ^ d * D.B / D.ε) ^ (1 / D.r) + D.Mv * D.B ^ (1 / D.r))

/-- The per-cube constant of (2.64)–(2.66): `C_diag = (1 + n 2^d) C_dec + C_test + C_{2.10}`. -/
noncomputable def Cdiag : ℝ := (1 + n * 2 ^ d) * D.Cdec + D.Ctest + D.C210

/-- The unit `U_T = F |Q|^{-a} |T|` of the per-cube bounds. -/
noncomputable def UT (T : DyadicCube d) : ℝ :=
  D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) * T.vol

theorem Cdec_nonneg : 0 ≤ D.Cdec := by
  have := D.CG_pos
  have := D.ε_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold Cdec
  positivity

theorem Ctest_nonneg : 0 ≤ D.Ctest := by
  have := D.CG_pos
  have := D.ε_pos
  have := D.Mv_nonneg
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold Ctest
  positivity

theorem C210_nonneg : 0 ≤ D.C210 := by
  have := D.ε_pos
  have := D.Mv_nonneg
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold C210
  positivity

theorem Cdiag_nonneg : 0 ≤ D.Cdiag := by
  have := D.Cdec_nonneg
  have := D.Ctest_nonneg
  have := D.C210_nonneg
  unfold Cdiag
  positivity

theorem UT_nonneg (T : DyadicCube d) : 0 ≤ D.UT T := by
  have := D.Fpos'
  have := D.Q.vol_pos
  have := T.vol_pos
  unfold UT
  positivity

/-- `|T|^a |T|^{1/r} |T|^{1/q} = |T|`. [PROVED] -/
theorem vol_rpow_split (T : DyadicCube d) :
    T.vol ^ (1 - 1 / D.r - 1 / D.q) * T.vol ^ (1 / D.r) * T.vol ^ (1 / D.q) = T.vol := by
  rw [← Real.rpow_add T.vol_pos, ← Real.rpow_add T.vol_pos,
    show 1 - 1 / D.r - 1 / D.q + 1 / D.r + 1 / D.q = (1 : ℝ) by ring, Real.rpow_one]

/-- The local bounds on `T ∈ setF2` and its children, in terms of `|T|`: `F_T`, `F_{T_ε}`,
`‖v 𝟙_{T_ε}‖_r`, `‖u 𝟙_{T_ε}‖_q`, `‖b_{τ,𝐐_{T_ε},k}‖_r`. [PROVED] -/
theorem local_bounds_setF2 {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR) (ε : Fin d → Bool) :
    D.FP (T.child ε) ≤ D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.F * T.vol ^ (1 - 1 / D.r - 1 / D.q) *
        D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) ∧
      lpNorm (TestFun.truncateₗ (T.child ε) (D.vP R) : (Fin d → ℝ) → ℝ) D.r ≤
        (2 ^ d * D.B / D.ε) ^ (1 / D.r) * T.vol ^ (1 / D.r) ∧
      lpNorm (TestFun.truncateₗ (T.child ε) D.u : (Fin d → ℝ) → ℝ) D.q ≤
        (2 ^ d * D.B / D.ε) ^ (1 / D.q) * T.vol ^ (1 / D.q) ∧
      lpNorm (D.vP (T.child ε) : (Fin d → ℝ) → ℝ) D.r ≤ D.B ^ (1 / D.r) * T.vol ^ (1 / D.r) := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have hCG := D.CG_pos
  have hF := D.Fpos'
  have hV := D.Q.vol_pos
  have hT0 := T.vol_pos
  have hc0 := (T.child ε).vol_pos
  have hcT : (T.child ε).vol ≤ T.vol := DyadicCube.vol_le_of_subset (T.child_subset ε)
  have ha := D.exp_a_nonneg
  have hcg := D.child_good_of_mem_setF2 hR hRs hFR hT ε
  have hcg' := D.child_second_good_of_mem_setF2 hR hRs hFR hT ε
  have hcQ : (T.child ε).toSet ⊆ D.Q.toSet :=
    (T.child_subset ε).trans ((D.subset_R_of_mem_setF2 hR hRs hFR hT).trans hR.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (D.FP_le' hcg).trans ?_
    gcongr
  · refine (D.lpNorm_truncateₗ_vP_le hR hRs hFR hcg').trans ?_
    rw [Real.mul_rpow (by positivity) hc0.le]
    gcongr
  · refine (D.lpNorm_truncateₗ_u_le hcg).trans ?_
    rw [Real.mul_rpow (by positivity) hc0.le]
    gcongr
  · refine (D.lpNorm_vP_le hcQ).trans ?_
    rw [Real.mul_rpow hB hc0.le]
    gcongr

/-- The off-diagonal terms of (2.64): `|Λ_T(v 𝟙_{T_ε}, u 𝟙_{T_{ε'}})| ≤ C_dec U_T` for `ε ≠ ε'`, by
the decay condition (1.1). [PROVED] -/
theorem abs_form2_offdiag_le {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR)
    {ε ε' : Fin d → Bool} (hne : ε ≠ ε') :
    |twoSlotForm D.T D.a D.b D.g T (TestFun.truncateₗ (T.child ε) (D.vP R))
      (TestFun.truncateₗ (T.child ε') D.u)| ≤ D.Cdec * D.UT T := by
  have h := abs_twoSlotForm_le_of_children D.T D.p D.hab D.g T hne
    (TestFun.truncateₗ_supportedOn (T.child ε) (D.vP R))
    (TestFun.truncateₗ_supportedOn (T.child ε') D.u)
  have h' : |twoSlotForm D.T D.a D.b D.g T (TestFun.truncateₗ (T.child ε) (D.vP R))
      (TestFun.truncateₗ (T.child ε') D.u)| ≤ D.FP T *
      lpNorm (TestFun.truncateₗ (T.child ε) (D.vP R) : (Fin d → ℝ) → ℝ) D.r *
      lpNorm (TestFun.truncateₗ (T.child ε') D.u : (Fin d → ℝ) → ℝ) D.q := h
  have hFP := D.FP_le' (D.good_of_mem_setF2 hR hRs hFR hT)
  obtain ⟨-, hv, -, -⟩ := D.local_bounds_setF2 hR hRs hFR hT ε
  obtain ⟨-, -, hu, -⟩ := D.local_bounds_setF2 hR hRs hFR hT ε'
  have hFP0 := D.FP_nonneg T
  have hv0 := lpNorm_nonneg (TestFun.truncateₗ (T.child ε) (D.vP R) : (Fin d → ℝ) → ℝ) D.r
  have hu0 := lpNorm_nonneg (TestFun.truncateₗ (T.child ε') D.u : (Fin d → ℝ) → ℝ) D.q
  have hA0 : 0 ≤ D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.F * T.vol ^ (1 - 1 / D.r - 1 / D.q) *
      D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) := by
    have := D.CG_pos; have := D.Fpos'; have := T.vol_pos; have := D.Q.vol_pos
    positivity
  have hB0 : 0 ≤ (2 ^ d * D.B / D.ε) ^ (1 / D.r) * T.vol ^ (1 / D.r) := by
    have := D.ε_pos; have : 0 ≤ D.B := by linarith [D.hB]
    have := T.vol_pos
    positivity
  calc |twoSlotForm D.T D.a D.b D.g T (TestFun.truncateₗ (T.child ε) (D.vP R))
        (TestFun.truncateₗ (T.child ε') D.u)|
      ≤ D.FP T * lpNorm (TestFun.truncateₗ (T.child ε) (D.vP R) : (Fin d → ℝ) → ℝ) D.r *
          lpNorm (TestFun.truncateₗ (T.child ε') D.u : (Fin d → ℝ) → ℝ) D.q := h'
    _ ≤ (D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.F * T.vol ^ (1 - 1 / D.r - 1 / D.q) *
          D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) *
          ((2 ^ d * D.B / D.ε) ^ (1 / D.r) * T.vol ^ (1 / D.r)) *
          ((2 ^ d * D.B / D.ε) ^ (1 / D.q) * T.vol ^ (1 / D.q)) :=
        mul_le_mul (mul_le_mul hFP hv hv0 hA0) hu hu0 (mul_nonneg hA0 hB0)
    _ = D.Cdec * (D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) *
          (T.vol ^ (1 - 1 / D.r - 1 / D.q) * T.vol ^ (1 / D.r) * T.vol ^ (1 / D.q)) := by
        unfold Cdec
        ring
    _ = D.Cdec * D.UT T := by
        rw [D.vol_rpow_split T]
        unfold UT
        ring

/-- Moving `Λ_T` to `Λ_{T_ε}` in the diagonal terms of (2.64): the residual is bounded by
`n 2^d C_dec U_T`, by decay. [PROVED] -/
theorem abs_form2_resid_le {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR) (ε : Fin d → Bool) :
    |twoSlotForm D.T D.a D.b D.g T (TestFun.truncateₗ (T.child ε) (D.vP R))
        (TestFun.truncateₗ (T.child ε) D.u) -
      twoSlotForm D.T D.a D.b D.g (T.child ε) (TestFun.truncateₗ (T.child ε) (D.vP R))
        (TestFun.truncateₗ (T.child ε) D.u)| ≤ n * 2 ^ d * D.Cdec * D.UT T := by
  have h := abs_twoSlotForm_sub_child_le D.T D.p D.hab D.g T ε
    (TestFun.truncateₗ_supportedOn (T.child ε) (D.vP R))
    (fun x hx => TestFun.truncateₗ_supportedOn (T.child ε) D.u x fun h => hx (T.child_subset ε h))
  have h' : |twoSlotForm D.T D.a D.b D.g T (TestFun.truncateₗ (T.child ε) (D.vP R))
        (TestFun.truncateₗ (T.child ε) D.u) -
      twoSlotForm D.T D.a D.b D.g (T.child ε) (TestFun.truncateₗ (T.child ε) (D.vP R))
        (TestFun.truncateₗ (T.child ε) D.u)| ≤ n * 2 ^ d * (D.FP T *
      lpNorm (TestFun.truncateₗ (T.child ε) (D.vP R) : (Fin d → ℝ) → ℝ) D.r *
      lpNorm (TestFun.truncateₗ (T.child ε) D.u : (Fin d → ℝ) → ℝ) D.q) := h
  have hFP := D.FP_le' (D.good_of_mem_setF2 hR hRs hFR hT)
  obtain ⟨-, hv, hu, -⟩ := D.local_bounds_setF2 hR hRs hFR hT ε
  have hFP0 := D.FP_nonneg T
  have hv0 := lpNorm_nonneg (TestFun.truncateₗ (T.child ε) (D.vP R) : (Fin d → ℝ) → ℝ) D.r
  have hu0 := lpNorm_nonneg (TestFun.truncateₗ (T.child ε) D.u : (Fin d → ℝ) → ℝ) D.q
  have hA0 : 0 ≤ D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.F * T.vol ^ (1 - 1 / D.r - 1 / D.q) *
      D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) := by
    have := D.CG_pos; have := D.Fpos'; have := T.vol_pos; have := D.Q.vol_pos
    positivity
  have hB0 : 0 ≤ (2 ^ d * D.B / D.ε) ^ (1 / D.r) * T.vol ^ (1 / D.r) := by
    have := D.ε_pos; have : 0 ≤ D.B := by linarith [D.hB]
    have := T.vol_pos
    positivity
  have hn : (0 : ℝ) ≤ n * 2 ^ d := by positivity
  calc _ ≤ n * 2 ^ d * (D.FP T *
          lpNorm (TestFun.truncateₗ (T.child ε) (D.vP R) : (Fin d → ℝ) → ℝ) D.r *
          lpNorm (TestFun.truncateₗ (T.child ε) D.u : (Fin d → ℝ) → ℝ) D.q) := h'
    _ ≤ n * 2 ^ d * ((D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.F * T.vol ^ (1 - 1 / D.r - 1 / D.q) *
          D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) *
          ((2 ^ d * D.B / D.ε) ^ (1 / D.r) * T.vol ^ (1 / D.r)) *
          ((2 ^ d * D.B / D.ε) ^ (1 / D.q) * T.vol ^ (1 / D.q))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul hFP hv hv0 hA0) hu hu0 (mul_nonneg hA0 hB0)) hn
    _ = n * 2 ^ d * D.Cdec * (D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) *
          (T.vol ^ (1 - 1 / D.r - 1 / D.q) * T.vol ^ (1 / D.r) * T.vol ^ (1 / D.q)) := by
        unfold Cdec
        ring
    _ = n * 2 ^ d * D.Cdec * D.UT T := by
        rw [D.vol_rpow_split T]
        unfold UT
        ring

/-- **(2.66)**: the diagonal terms at the child, `|Λ_{T_ε}(v 𝟙_{T_ε}, u 𝟙_{T_ε})| ≤ (C_test +
C_{2.10}) U_T`:
`v 𝟙_{T_ε} = [v]_{T_ε} b_{τ,𝐐_{T_ε},k} + (v 𝟙_{T_ε} − [v]_{T_ε} b_{τ,𝐐_{T_ε},k})`, the first part by
the testing condition (1.9) for `τ`, the mean-zero second part by (2.10). [PROVED] -/
theorem abs_form2_child_le {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR) (ε : Fin d → Bool) :
    |twoSlotForm D.T D.a D.b D.g (T.child ε) (TestFun.truncateₗ (T.child ε) (D.vP R))
      (TestFun.truncateₗ (T.child ε) D.u)| ≤ (D.Ctest + D.C210) * D.UT T := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have hCG := D.CG_pos
  have hF := D.Fpos'
  have hV := D.Q.vol_pos
  have hT0 := T.vol_pos
  have hMv := D.Mv_nonneg
  have ha := D.exp_a_nonneg
  set c := T.child ε with hc
  have hcT : c.toSet ⊆ T.toSet := T.child_subset ε
  have hcQ : c.toSet ⊆ D.Q.toSet :=
    hcT.trans ((D.subset_R_of_mem_setF2 hR hRs hFR hT).trans hR.1)
  have hcg := D.child_good_of_mem_setF2 hR hRs hFR hT ε
  obtain ⟨hFPc, hv, hu, hb⟩ := D.local_bounds_setF2 hR hRs hFR hT ε
  have havg : |avg c (D.vP R)| ≤ D.Mv :=
    D.child_abs_avg_vP_le_Mv_of_mem_setF hR hRs hFR (D.setF2_subset_setF hR hRs hFR hT) ε
  -- the decomposition `v 𝟙_c = [v]_c b_c + ρ₀`
  set ρ₀ : TestFun d := TestFun.truncateₗ c (D.vP R) - avg c (D.vP R) • D.vP c with hρ₀
  have hdec : TestFun.truncateₗ c (D.vP R) = avg c (D.vP R) • D.vP c + ρ₀ := by
    rw [hρ₀, add_sub_cancel]
  have hsupp : SupportedOn ρ₀ c :=
    supportedOn_sub (TestFun.truncateₗ_supportedOn c _) fun x hx => by
      rw [Submodule.coe_smul, Pi.smul_apply, D.vP_supp c hcQ x hx, smul_zero]
  have hmean : MeanZero (ρ₀ : (Fin d → ℝ) → ℝ) := by
    change TestFun.integralₗ ρ₀ = 0
    rw [hρ₀, map_sub, map_smul, TestFun.integralₗ_truncateₗ, TestFun.integralₗ_apply,
      D.vP_mean c hcQ, smul_eq_mul, sub_self]
  have hρ₀ : lpNorm (ρ₀ : (Fin d → ℝ) → ℝ) D.r ≤
      ((2 ^ d * D.B / D.ε) ^ (1 / D.r) + D.Mv * D.B ^ (1 / D.r)) * T.vol ^ (1 / D.r) := by
    calc lpNorm (ρ₀ : (Fin d → ℝ) → ℝ) D.r
        ≤ lpNorm (TestFun.truncateₗ c (D.vP R) : (Fin d → ℝ) → ℝ) D.r +
          lpNorm ((avg c (D.vP R) • D.vP c : TestFun d) : (Fin d → ℝ) → ℝ) D.r :=
          TestFun.lpNorm_sub_le _ _ D.hr.le
      _ = lpNorm (TestFun.truncateₗ c (D.vP R) : (Fin d → ℝ) → ℝ) D.r +
          |avg c (D.vP R)| * lpNorm (D.vP c : (Fin d → ℝ) → ℝ) D.r := by
          rw [TestFun.lpNorm_smul]
      _ ≤ (2 ^ d * D.B / D.ε) ^ (1 / D.r) * T.vol ^ (1 / D.r) +
          D.Mv * (D.B ^ (1 / D.r) * T.vol ^ (1 / D.r)) :=
          add_le_add hv (mul_le_mul havg hb (lpNorm_nonneg _ _) hMv)
      _ = _ := by ring
  -- the testing term
  have h1 := D.testing_vP c hcQ _ (TestFun.truncateₗ_supportedOn c D.u)
  have h1' : |twoSlotForm D.T D.a D.b D.g c (D.vP c) (TestFun.truncateₗ c D.u)| ≤
      D.B * D.FP c * lpNorm (D.vP c : (Fin d → ℝ) → ℝ) D.r *
        lpNorm (TestFun.truncateₗ c D.u : (Fin d → ℝ) → ℝ) D.q := h1
  -- the (2.10) term
  have h2 : twoSlotForm D.T D.a D.b D.g c ρ₀ (TestFun.truncateₗ c D.u) =
      slotForm D.T D.a D.g c ρ₀ := by
    rw [twoSlotForm_truncateₗ_right, twoSlotForm_self D.T D.hab]
  have h3 := D.bound_2_10 D.hd hcg ρ₀ hsupp hmean
  have hc0 := c.vol_pos
  have h1r : 0 ≤ 1 - 1 / D.r := by
    rw [sub_nonneg, div_le_one hr0]
    exact D.hr.le
  have hcvol : (c.vol / D.Q.vol) ^ (1 - 1 / D.r) ≤
      T.vol ^ (1 - 1 / D.r) * D.Q.vol ^ (-(1 - 1 / D.r)) := by
    rw [Real.div_rpow hc0.le hV.le, Real.rpow_neg hV.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hc0.le (DyadicCube.vol_le_of_subset hcT) h1r)
      (inv_nonneg.mpr (Real.rpow_nonneg hV.le _))
  have hu_full : lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q ≤ D.B ^ (1 / D.q) * D.Q.vol ^ (1 / D.q) := by
    refine D.lpNorm_u_le.trans (le_of_eq ?_)
    rw [Real.mul_rpow hB hV.le]
  -- assemble
  have hvP0 := lpNorm_nonneg (D.vP c : (Fin d → ℝ) → ℝ) D.r
  have hu0 := lpNorm_nonneg (TestFun.truncateₗ c D.u : (Fin d → ℝ) → ℝ) D.q
  have hFP0 := D.FP_nonneg c
  have hρ0 := lpNorm_nonneg (ρ₀ : (Fin d → ℝ) → ℝ) D.r
  have huu0 := lpNorm_nonneg (D.u : (Fin d → ℝ) → ℝ) D.q
  have hA0 : 0 ≤ D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.F * T.vol ^ (1 - 1 / D.r - 1 / D.q) *
      D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) := by positivity
  have hB0 : 0 ≤ D.B ^ (1 / D.r) * T.vol ^ (1 / D.r) := by positivity
  have hterm1 : |avg c (D.vP R) * twoSlotForm D.T D.a D.b D.g c (D.vP c)
      (TestFun.truncateₗ c D.u)| ≤ D.Ctest * D.UT T := by
    rw [abs_mul]
    calc |avg c (D.vP R)| * |twoSlotForm D.T D.a D.b D.g c (D.vP c) (TestFun.truncateₗ c D.u)|
        ≤ D.Mv * (D.B * (D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.F * T.vol ^ (1 - 1 / D.r - 1 / D.q) *
            D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) * (D.B ^ (1 / D.r) * T.vol ^ (1 / D.r)) *
            ((2 ^ d * D.B / D.ε) ^ (1 / D.q) * T.vol ^ (1 / D.q))) := by
          refine mul_le_mul havg (h1'.trans ?_) (abs_nonneg _) hMv
          exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hFPc hB) hb hvP0
            (mul_nonneg hB hA0)) hu hu0 (mul_nonneg (mul_nonneg hB hA0) hB0)
      _ = D.Ctest * (D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) *
            (T.vol ^ (1 - 1 / D.r - 1 / D.q) * T.vol ^ (1 / D.r) * T.vol ^ (1 / D.q)) := by
          unfold Ctest
          ring
      _ = D.Ctest * D.UT T := by
          rw [D.vol_rpow_split T]
          unfold UT
          ring
  have hQsplit : D.Q.vol ^ (1 / D.q) * D.Q.vol ^ (-(1 - 1 / D.r)) =
      D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) := by
    rw [← Real.rpow_add hV]
    congr 1
    ring
  have hTsplit : T.vol ^ (1 - 1 / D.r) * T.vol ^ (1 / D.r) = T.vol := by
    rw [← Real.rpow_add hT0, sub_add_cancel, Real.rpow_one]
  have hterm2 : |twoSlotForm D.T D.a D.b D.g c ρ₀ (TestFun.truncateₗ c D.u)| ≤ D.C210 * D.UT T := by
    rw [h2]
    calc |slotForm D.T D.a D.g c ρ₀|
        ≤ 2 ^ d * (D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹) *
            (c.vol / D.Q.vol) ^ (1 - 1 / D.r) * lpNorm (ρ₀ : (Fin d → ℝ) → ℝ) D.r := h3
      _ ≤ 2 ^ d * (D.B * D.F * (D.B ^ (1 / D.q) * D.Q.vol ^ (1 / D.q)) * D.ε⁻¹) *
            (T.vol ^ (1 - 1 / D.r) * D.Q.vol ^ (-(1 - 1 / D.r))) *
            (((2 ^ d * D.B / D.ε) ^ (1 / D.r) + D.Mv * D.B ^ (1 / D.r)) * T.vol ^ (1 / D.r)) := by
          gcongr
      _ = D.C210 * (D.F * (D.Q.vol ^ (1 / D.q) * D.Q.vol ^ (-(1 - 1 / D.r)))) *
            (T.vol ^ (1 - 1 / D.r) * T.vol ^ (1 / D.r)) := by
          unfold C210
          ring
      _ = D.C210 * D.UT T := by
          rw [hQsplit, hTsplit]
          unfold UT
          ring
  rw [hdec, twoSlotForm_add_left D.T D.hab, twoSlotForm_smul_left D.T D.hab]
  calc |avg c (D.vP R) * twoSlotForm D.T D.a D.b D.g c (D.vP c) (TestFun.truncateₗ c D.u) +
        twoSlotForm D.T D.a D.b D.g c ρ₀ (TestFun.truncateₗ c D.u)|
      ≤ |avg c (D.vP R) * twoSlotForm D.T D.a D.b D.g c (D.vP c) (TestFun.truncateₗ c D.u)| +
        |twoSlotForm D.T D.a D.b D.g c ρ₀ (TestFun.truncateₗ c D.u)| := abs_add_le _ _
    _ ≤ D.Ctest * D.UT T + D.C210 * D.UT T := add_le_add hterm1 hterm2
    _ = _ := by ring

/-- **The per-cube bound of (2.64)–(2.66)**: `|Λ_T(v 𝟙_{T_ε}, u 𝟙_{T_{ε'}})| ≤ C_diag U_T` for every
pair of children of `T ∈ setF2`. [PROVED] -/
theorem abs_form2_child_child_le {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR)
    (ε ε' : Fin d → Bool) :
    |twoSlotForm D.T D.a D.b D.g T (TestFun.truncateₗ (T.child ε) (D.vP R))
      (TestFun.truncateₗ (T.child ε') D.u)| ≤ D.Cdiag * D.UT T := by
  have hU := D.UT_nonneg T
  have hCdec := D.Cdec_nonneg
  have hCtest := D.Ctest_nonneg
  have hC210 := D.C210_nonneg
  have hn : (0 : ℝ) ≤ n * 2 ^ d := by positivity
  by_cases hne : ε = ε'
  · subst hne
    have h1 := D.abs_form2_resid_le hR hRs hFR hT ε
    have h2 := D.abs_form2_child_le hR hRs hFR hT ε
    set A := twoSlotForm D.T D.a D.b D.g T (TestFun.truncateₗ (T.child ε) (D.vP R))
      (TestFun.truncateₗ (T.child ε) D.u)
    set Bv := twoSlotForm D.T D.a D.b D.g (T.child ε) (TestFun.truncateₗ (T.child ε) (D.vP R))
      (TestFun.truncateₗ (T.child ε) D.u)
    have h3 : |A| ≤ |A - Bv| + |Bv| := by
      have := abs_add_le (A - Bv) Bv
      rwa [sub_add_cancel] at this
    calc |A| ≤ |A - Bv| + |Bv| := h3
      _ ≤ n * 2 ^ d * D.Cdec * D.UT T + (D.Ctest + D.C210) * D.UT T := add_le_add h1 h2
      _ ≤ D.Cdiag * D.UT T := by
          unfold Cdiag
          nlinarith [mul_nonneg hCdec hU]
  · refine (D.abs_form2_offdiag_le hR hRs hFR hT hne).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hU
    unfold Cdiag
    nlinarith [mul_nonneg hn hCdec]

/-- **The per-cube bound for (2.60)**: `|Λ_T(X_T, Y_T)| ≤ C_diag U_T (∑_ε |ψ_T − ψ_{T_ε}|)(∑_{ε'}
|φ_T − φ_{T_{ε'}}|)`
for `T ∈ setF2`. [PROVED] -/
theorem abs_form2_XY_le {T : DyadicCube d} (hT : T ∈ D.setF2 hR hRs hFR) :
    |twoSlotForm D.T D.a D.b D.g T (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T')| ≤
      D.Cdiag * D.UT T * ((∑ ε : Fin d → Bool, |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child
        ε)|) *
        ∑ ε' : Fin d → Bool, |D.phiT R T - D.phiT R (T.child ε')|) :=
  D.abs_form2_XY_le_of hR hRs hFR T fun ε ε' => D.abs_form2_child_child_le hR hRs hFR hT ε ε'

/-! The sums over `setF2`: the parents of `𝐏 ∩ 𝐏₄` and of `𝐒 ∩ 𝐒₄` by bounded overlap, the other
cubes
by (2.61), Cauchy–Schwarz and Lemma 2.72. -/

/-- `∑_ε f_ε ≤ 2^d c` when `f_ε ≤ c` for all `ε`. [PROVED] -/
theorem sum_le_two_pow_mul {f : (Fin d → Bool) → ℝ} {c : ℝ} (h : ∀ ε, f ε ≤ c) :
    ∑ ε : Fin d → Bool, f ε ≤ 2 ^ d * c := by
  calc ∑ ε : Fin d → Bool, f ε ≤ ∑ _ε : Fin d → Bool, c := Finset.sum_le_sum fun ε _ => h ε
    _ = 2 ^ d * c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The cubes of `setF2` which are parents of cubes of `𝐏 ∩ 𝐏₄` or of `𝐒 ∩ 𝐒₄`. -/
noncomputable def setP2 : Finset (DyadicCube d) :=
  (D.setF2 hR hRs hFR).filter (fun T => T ∈ D.Pbar4 ∨ T ∈ (D.second R hR hRs hFR).Pbar4)

/-- The other cubes of `setF2`. -/
noncomputable def setT2 : Finset (DyadicCube d) :=
  (D.setF2 hR hRs hFR).filter (fun T => ¬ (T ∈ D.Pbar4 ∨ T ∈ (D.second R hR hRs hFR).Pbar4))

theorem mem_setP2 {T : DyadicCube d} :
    T ∈ D.setP2 hR hRs hFR ↔ T ∈ D.setF2 hR hRs hFR ∧
      (T ∈ D.Pbar4 ∨ T ∈ (D.second R hR hRs hFR).Pbar4) := Finset.mem_filter

theorem mem_setT2 {T : DyadicCube d} :
    T ∈ D.setT2 hR hRs hFR ↔ T ∈ D.setF2 hR hRs hFR ∧
      ¬ (T ∈ D.Pbar4 ∨ T ∈ (D.second R hR hRs hFR).Pbar4) := Finset.mem_filter

theorem sum_setF2_eq (f : DyadicCube d → ℝ) :
    ∑ T ∈ D.setF2 hR hRs hFR, f T = ∑ T ∈ D.setP2 hR hRs hFR, f T + ∑ T ∈ D.setT2 hR hRs hFR, f T :=
      by
  rw [setP2, setT2, Finset.sum_filter_add_sum_filter_not]

theorem setT2_subset_setT : D.setT2 hR hRs hFR ⊆ D.setT hR hRs hFR := fun _ hT => by
  rw [D.mem_setT2 hR hRs hFR] at hT
  exact (D.mem_setT hR hRs hFR).mpr ⟨D.setF2_subset_setF hR hRs hFR hT.1, fun h => hT.2 (Or.inr h)⟩

theorem setT2_subset_setTG : D.setT2 hR hRs hFR ⊆ D.setTG hR hRs hFR := fun _ hT => by
  rw [D.mem_setT2 hR hRs hFR] at hT
  exact (D.mem_setTG hR hRs hFR).mpr ⟨D.setF2_subset_setFG hR hRs hFR hT.1, fun h => hT.2 (Or.inl
    h)⟩

/-- The crude bound `(∑_ε |ψ_T − ψ_{T_ε}|)(∑_{ε'} |φ_T − φ_{T_{ε'}}|) ≤ (2^d · 2 C_ψ)(2^d · 2
C_{φ,T} K)` for
every non-leaf `T`. [PROVED] -/
theorem A_le_crude (hG : D.GBound) {T : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) :
    (∑ ε : Fin d → Bool, |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)|) *
      ∑ ε' : Fin d → Bool, |D.phiT R T - D.phiT R (T.child ε')| ≤
      (2 ^ d * (2 * D.Cψ hR hRs hFR)) * (2 ^ d * (2 * (D.CφT * D.KQ))) := by
  have hT' := D.mem_second_tree_of_mem_nonleaf hR hRs hFR hT
  have hTR : T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp hT).1
  have hψ : ∀ ε, |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)| ≤
      2 * D.Cψ hR hRs hFR := fun ε => by
    have h1 := D.abs_psiT_le hR hRs hFR hT'
    have h2 := D.abs_psiT_le hR hRs hFR (D.child_mem_second_tree_of_mem_nonleaf hR hRs hFR hT ε)
    linarith [abs_sub (D.psiT hR hRs hFR T) (D.psiT hR hRs hFR (T.child ε))]
  have hφ : ∀ ε, |D.phiT R T - D.phiT R (T.child ε)| ≤ 2 * (D.CφT * D.KQ) := fun ε => by
    have h1 : |D.phiT R T| ≤ D.CφT * D.KQ :=
      D.abs_phiT_le hR hRs hG (D.second_tree_subset hR hRs hFR hT') hTR
    have h2 : |D.phiT R (T.child ε)| ≤ D.CφT * D.KQ :=
      D.abs_phiT_le hR hRs hG (D.second_tree_subset hR hRs hFR
        (D.child_mem_second_tree_of_mem_nonleaf hR hRs hFR hT ε)) ((T.child_subset ε).trans hTR)
    linarith [abs_sub (D.phiT R T) (D.phiT R (T.child ε))]
  exact mul_le_mul (sum_le_two_pow_mul hψ) (sum_le_two_pow_mul hφ)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (mul_nonneg (by positivity) (mul_nonneg (by norm_num) (D.Cψ_nonneg hR hRs hFR)))

/-- `∑_{T ∈ setP2} |T| ≤ 2 (2^d/ε) |R|`, by the bounded overlap of `parents(𝐏)₄` and
`parents(𝐒)₄`. [PROVED] -/
theorem sum_vol_setP2_le : ∑ T ∈ D.setP2 hR hRs hFR, T.vol ≤ 2 * (2 ^ d / D.ε) * R.vol := by
  classical
  have hsub : D.setP2 hR hRs hFR ⊆
      D.Pbar4.filter (fun T => T.toSet ⊆ R.toSet) ∪ (D.second R hR hRs hFR).Pbar4 := by
    intro T hT
    rw [D.mem_setP2 hR hRs hFR] at hT
    rw [Finset.mem_union, Finset.mem_filter]
    rcases hT.2 with h | h
    · exact Or.inl ⟨h, D.subset_R_of_mem_setF2 hR hRs hFR hT.1⟩
    · exact Or.inr h
  have h1 : ∑ T ∈ D.Pbar4.filter (fun T => T.toSet ⊆ R.toSet), T.vol ≤ 2 ^ d / D.ε * R.vol := by
    refine sum_vol_le_of_card_le _ (fun T hT => (Finset.mem_filter.mp hT).2) fun x => ?_
    refine le_trans ?_ (D.card_Pbar4_filter_le x)
    exact_mod_cast Finset.card_le_card
      (Finset.monotone_filter_left _ (Finset.filter_subset _ _))
  have h2 : ∑ T ∈ (D.second R hR hRs hFR).Pbar4, T.vol ≤ 2 ^ d / D.ε * R.vol :=
    sum_vol_le_of_card_le _ (fun T hT => (D.second R hR hRs hFR).Pbar4_subset_Q hT)
      fun x => (D.second R hR hRs hFR).card_Pbar4_filter_le x
  have h0 : 0 ≤ ∑ T ∈ D.Pbar4.filter (fun T => T.toSet ⊆ R.toSet) ∩
      (D.second R hR hRs hFR).Pbar4, T.vol := Finset.sum_nonneg fun T _ => T.vol_pos.le
  have hui := Finset.sum_union_inter (s₁ := D.Pbar4.filter (fun T => T.toSet ⊆ R.toSet))
    (s₂ := (D.second R hR hRs hFR).Pbar4) (f := fun T : DyadicCube d => T.vol)
  calc ∑ T ∈ D.setP2 hR hRs hFR, T.vol
      ≤ ∑ T ∈ D.Pbar4.filter (fun T => T.toSet ⊆ R.toSet) ∪ (D.second R hR hRs hFR).Pbar4,
          T.vol := Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ => T.vol_pos.le
    _ ≤ ∑ T ∈ D.Pbar4.filter (fun T => T.toSet ⊆ R.toSet), T.vol +
          ∑ T ∈ (D.second R hR hRs hFR).Pbar4, T.vol := by linarith
    _ ≤ 2 ^ d / D.ε * R.vol + 2 ^ d / D.ε * R.vol := add_le_add h1 h2
    _ = 2 * (2 ^ d / D.ε) * R.vol := by ring

/-- `|Q|^{-a} |Q|^{-1/q} = |Q|^{1/r − 1}`. [PROVED] -/
theorem Q_rpow_split : D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) * D.Q.vol ^ (-(1 / D.q)) =
    D.Q.vol ^ (1 / D.r - 1) := by
  rw [← Real.rpow_add D.Q.vol_pos]
  congr 1
  ring

/-- The constant of the `parents(𝐏)`-portion of (2.60): `C₆₀P = 8 · 2^d 2^d (2^d/ε) C_diag C_ψ
C_{φ,T}`. -/
noncomputable def C₆₀P : ℝ :=
  8 * (2 ^ d * 2 ^ d) * (2 ^ d / D.ε) * D.Cdiag * D.Cψ hR hRs hFR * D.CφT

/-- **The `parents(𝐏)`-portion of (2.60)**: `∑_{T ∈ setP2} |Λ_T(X_T, Y_T)| ≤ C₆₀P E_R`. [PROVED] -/
theorem sum_setP2_le (hG : D.GBound) :
    ∑ T ∈ D.setP2 hR hRs hFR, |twoSlotForm D.T D.a D.b D.g T
        (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T')| ≤ D.C₆₀P hR hRs hFR * D.E R := by
  have hF := D.Fpos'
  have hV := D.Q.vol_pos
  have hε := D.ε_pos
  have hCd := D.Cdiag_nonneg
  have hCψ := D.Cψ_nonneg hR hRs hFR
  have hCφ := D.CφT_nonneg
  have hK := D.KQ_nonneg
  have hVq : 0 ≤ D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) := Real.rpow_nonneg hV.le _
  set M : ℝ := (2 ^ d * (2 * D.Cψ hR hRs hFR)) * (2 ^ d * (2 * (D.CφT * D.KQ))) with hM
  have hM0 : 0 ≤ M := by positivity
  calc ∑ T ∈ D.setP2 hR hRs hFR, |twoSlotForm D.T D.a D.b D.g T
          (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
          (D.yT R T - ∑ T' ∈ children T, D.yT R T')|
      ≤ ∑ T ∈ D.setP2 hR hRs hFR, D.Cdiag * D.UT T * M :=
        Finset.sum_le_sum fun T hT =>
          (D.abs_form2_XY_le hR hRs hFR ((D.mem_setP2 hR hRs hFR).mp hT).1).trans
            (mul_le_mul_of_nonneg_left (D.A_le_crude hR hRs hFR hG
              ((D.mem_setF2 hR hRs hFR).mp ((D.mem_setP2 hR hRs hFR).mp hT).1).1)
              (mul_nonneg hCd (D.UT_nonneg T)))
    _ = D.Cdiag * M * (D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) *
          ∑ T ∈ D.setP2 hR hRs hFR, T.vol := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun T _ => by unfold UT; ring
    _ ≤ D.Cdiag * M * (D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) *
          (2 * (2 ^ d / D.ε) * R.vol) :=
        mul_le_mul_of_nonneg_left (D.sum_vol_setP2_le hR hRs hFR) (by positivity)
    _ = D.C₆₀P hR hRs hFR * D.E R := by
        unfold C₆₀P E
        rw [hM]
        unfold KQ
        rw [show D.Cdiag * (2 ^ d * (2 * D.Cψ hR hRs hFR) *
            (2 ^ d * (2 * (D.CφT * (D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q)))))
              *
            (D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q))) * (2 * (2 ^ d / D.ε) * R.vol) =
          8 * (2 ^ d * 2 ^ d) * (2 ^ d / D.ε) * D.Cdiag * D.Cψ hR hRs hFR * D.CφT *
            (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * R.vol) *
            (D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) * D.Q.vol ^ (-(1 / D.q))) by ring,
          D.Q_rpow_split]
        ring

/-- **(2.61) for `ψ` on `T ∈ setT2`**: `∑_ε |ψ_T − ψ_{T_ε}| ≤ 2^d ((8 + 128 M_v) Δ_T 𝔥 + 64 M_v E_T
𝔥 Δ_T f₅)`.
[PROVED] -/
theorem sum_abs_psiT_sub_le {T : DyadicCube d} (hT : T ∈ D.setT2 hR hRs hFR) :
    ∑ ε : Fin d → Bool, |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)| ≤
      2 ^ d * ((8 + 128 * D.Mv) * martDiff T (D.prunedH hR hRs hFR) +
        64 * D.Mv * martAvg T (D.prunedH hR hRs hFR) * martDiff T (D.fthree hR hRs hFR)) := by
  have hTT := D.setT2_subset_setT hR hRs hFR hT
  have hTF := ((D.mem_setT hR hRs hFR).mp hTT).1
  have hvT := D.lt_abs_avg_vP_of_mem_setF hR hRs hFR hTF
  have hvc := D.lt_abs_avg_vP_child_of_mem_setT hR hRs hFR hTT
  have hMT := D.abs_avg_vP_le_Mv_of_mem_setF hR hRs hFR hTF
  have hMc := D.child_abs_avg_vP_le_Mv_of_mem_setF hR hRs hFR hTF
  have hψT : D.psiT hR hRs hFR T = avg T (D.prunedH hR hRs hFR) / avg T (D.vP R) := by
    rw [psiT, coefOn_eq_div (ne_zero_of_lt_abs hvT)]
  have hψc : ∀ ε, D.psiT hR hRs hFR (T.child ε) =
      avg (T.child ε) (D.prunedH hR hRs hFR) / avg (T.child ε) (D.vP R) := fun ε => by
    rw [psiT, coefOn_eq_div (ne_zero_of_lt_abs (hvc ε))]
  have hpt : ∀ ε, |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)| ≤
      (8 + 128 * D.Mv) * |avg (T.child ε) (D.prunedH hR hRs hFR) - avg T (D.prunedH hR hRs hFR)| +
        64 * |avg T (D.prunedH hR hRs hFR)| * |avg (T.child ε) (D.vP R) - avg T (D.vP R)| :=
    fun ε => by
      rw [hψT, hψc]
      exact abs_div_sub_div_le hvT (hvc ε) hMT (hMc ε)
  have h1 := sum_abs_sub_avg_le T (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)
  have h2 := sum_abs_sub_avg_le T (D.vP R : (Fin d → ℝ) → ℝ)
  have hΔv := D.martDiff_vP_eq_of_mem_setF hR hRs hFR hTF
  have hMv := D.Mv_nonneg
  calc ∑ ε : Fin d → Bool, |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)|
      ≤ ∑ ε : Fin d → Bool, ((8 + 128 * D.Mv) *
          |avg (T.child ε) (D.prunedH hR hRs hFR) - avg T (D.prunedH hR hRs hFR)| +
          64 * |avg T (D.prunedH hR hRs hFR)| * |avg (T.child ε) (D.vP R) - avg T (D.vP R)|) :=
        Finset.sum_le_sum fun ε _ => hpt ε
    _ = (8 + 128 * D.Mv) * ∑ ε : Fin d → Bool,
          |avg (T.child ε) (D.prunedH hR hRs hFR) - avg T (D.prunedH hR hRs hFR)| +
          64 * |avg T (D.prunedH hR hRs hFR)| *
            ∑ ε : Fin d → Bool, |avg (T.child ε) (D.vP R) - avg T (D.vP R)| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (8 + 128 * D.Mv) * (2 ^ d * martDiff T (D.prunedH hR hRs hFR)) +
          64 * |avg T (D.prunedH hR hRs hFR)| * (2 ^ d * martDiff T (D.vP R)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by
        rw [hΔv]
        unfold martAvg
        ring

/-- **(2.61) for `φ` on `T ∈ setT2`**: `∑_ε |φ_T − φ_{T_ε}| ≤ 2^d ((8 + 128 M_u) Δ_T 𝔤̂ + 64 M_u E_T
𝔤̂ Δ_T f₄)`.
[PROVED] -/
theorem sum_abs_phiT_sub_le {T : DyadicCube d} (hT : T ∈ D.setT2 hR hRs hFR) :
    ∑ ε : Fin d → Bool, |D.phiT R T - D.phiT R (T.child ε)| ≤
      2 ^ d * ((8 + 128 * D.Mu) * martDiff T (D.ghat R) +
        64 * D.Mu * martAvg T (D.ghat R) * martDiff T (D.fthreeG hR hRs hFR)) := by
  have hTT := D.setT2_subset_setTG hR hRs hFR hT
  have hTF := ((D.mem_setTG hR hRs hFR).mp hTT).1
  have huT := D.lt_abs_avg_u_of_mem_setFG hR hRs hFR hTF
  have huc := D.lt_abs_avg_u_child_of_mem_setTG hR hRs hFR hTT
  have hMT := D.abs_avg_u_le_Mu_of_mem_setFG hR hRs hFR hTF
  have hMc := D.child_abs_avg_u_le_Mu_of_mem_setFG hR hRs hFR hTF
  have hφT : D.phiT R T = avg T (D.ghat R) / avg T D.u := by
    rw [phiT, coefOn_eq_div (ne_zero_of_lt_abs huT)]
  have hφc : ∀ ε, D.phiT R (T.child ε) = avg (T.child ε) (D.ghat R) / avg (T.child ε) D.u :=
    fun ε => by rw [phiT, coefOn_eq_div (ne_zero_of_lt_abs (huc ε))]
  have hpt : ∀ ε, |D.phiT R T - D.phiT R (T.child ε)| ≤
      (8 + 128 * D.Mu) * |avg (T.child ε) (D.ghat R) - avg T (D.ghat R)| +
        64 * |avg T (D.ghat R)| * |avg (T.child ε) D.u - avg T D.u| := fun ε => by
    rw [hφT, hφc]
    exact abs_div_sub_div_le huT (huc ε) hMT (hMc ε)
  have h1 := sum_abs_sub_avg_le T (D.ghat R : (Fin d → ℝ) → ℝ)
  have h2 := sum_abs_sub_avg_le T (D.u : (Fin d → ℝ) → ℝ)
  have hΔu := D.martDiff_u_eq_of_mem_setFG hR hRs hFR hTF
  have hMu := D.Mu_nonneg
  calc ∑ ε : Fin d → Bool, |D.phiT R T - D.phiT R (T.child ε)|
      ≤ ∑ ε : Fin d → Bool, ((8 + 128 * D.Mu) * |avg (T.child ε) (D.ghat R) - avg T (D.ghat R)| +
          64 * |avg T (D.ghat R)| * |avg (T.child ε) D.u - avg T D.u|) :=
        Finset.sum_le_sum fun ε _ => hpt ε
    _ = (8 + 128 * D.Mu) * ∑ ε : Fin d → Bool, |avg (T.child ε) (D.ghat R) - avg T (D.ghat R)| +
          64 * |avg T (D.ghat R)| * ∑ ε : Fin d → Bool, |avg (T.child ε) D.u - avg T D.u| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (8 + 128 * D.Mu) * (2 ^ d * martDiff T (D.ghat R)) +
          64 * |avg T (D.ghat R)| * (2 ^ d * martDiff T D.u) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by
        rw [hΔu]
        unfold martAvg
        ring

/-- The coefficient constant of the Lemma 2.72 bound: `C_co = (8 + 192 M_v)(8 + 192 M_u)`. -/
noncomputable def Cco : ℝ := (8 + 192 * D.Mv) * (8 + 192 * D.Mu)

theorem Cco_nonneg : 0 ≤ D.Cco := by
  have := D.Mv_nonneg
  have := D.Mu_nonneg
  unfold Cco
  positivity

/-- **The per-cube bound for (2.60) in the form required by Lemma 2.72**, for `T ∈ setT2`:
`|Λ_T(X_T, Y_T)| ≤ C₀ (Δ_T 𝔤̂ Δ_T 𝔥 + E_T 𝔥 Δ_T 𝔤̂ Δ_T f₅ + E_T 𝔤̂ Δ_T f₄ Δ_T 𝔥 + E_T 𝔤̂ E_T 𝔥 Δ_T
f₄ Δ_T f₅) E_T 𝟙_R |T|`
with `C₀ = C_diag F |Q|^{-a} 2^d 2^d C_co`, `f₄ = û/M_u`, `f₅ = v̂/M_v`. [PROVED] -/
theorem abs_alpha60_le {T : DyadicCube d} (hT : T ∈ D.setT2 hR hRs hFR) :
    |twoSlotForm D.T D.a D.b D.g T (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T')| ≤
      (D.Cdiag * D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) * (2 ^ d * 2 ^ d) * D.Cco) *
        (martDiff T (D.ghat R) * martDiff T (D.prunedH hR hRs hFR)
          + martAvg T (D.prunedH hR hRs hFR) * martDiff T (D.ghat R) * martDiff T (D.fthree hR hRs
            hFR)
          + martAvg T (D.ghat R) * martDiff T (D.fthreeG hR hRs hFR) * martDiff T (D.prunedH hR hRs
            hFR)
          + martAvg T (D.ghat R) * martAvg T (D.prunedH hR hRs hFR) *
              martDiff T (D.fthreeG hR hRs hFR) * martDiff T (D.fthree hR hRs hFR)) *
        martAvg T ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) * T.vol := by
  have hTF2 := ((D.mem_setT2 hR hRs hFR).mp hT).1
  have hA := D.abs_form2_XY_le hR hRs hFR hTF2
  have hψ := D.sum_abs_psiT_sub_le hR hRs hFR hT
  have hφ := D.sum_abs_phiT_sub_le hR hRs hFR hT
  have hE3 : martAvg T ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) = 1 := by
    rw [martAvg, avg_ind_of_subset (D.subset_R_of_mem_setF2 hR hRs hFR hTF2), abs_one]
  have hMv := D.Mv_nonneg
  have hMu := D.Mu_nonneg
  set Δh := martDiff T (D.prunedH hR hRs hFR) with hΔh
  set Δg := martDiff T (D.ghat R) with hΔg
  set Δ5 := martDiff T (D.fthree hR hRs hFR) with hΔ5
  set Δ4 := martDiff T (D.fthreeG hR hRs hFR) with hΔ4
  set Eh := martAvg T (D.prunedH hR hRs hFR) with hEh
  set Eg := martAvg T (D.ghat R) with hEg
  have h1 : 0 ≤ Δh := martDiff_nonneg _ _
  have h2 : 0 ≤ Δg := martDiff_nonneg _ _
  have h3 : 0 ≤ Δ5 := martDiff_nonneg _ _
  have h4 : 0 ≤ Δ4 := martDiff_nonneg _ _
  have h5 : 0 ≤ Eh := martAvg_nonneg _ _
  have h6 : 0 ≤ Eg := martAvg_nonneg _ _
  set Mv := D.Mv with hMvd
  set Mu := D.Mu with hMud
  set Cc := D.Cco with hCc
  obtain ⟨c1, c2, c3, c4⟩ :
      ((8 + 128 * Mv) * (8 + 128 * Mu) ≤ Cc) ∧
      ((8 + 128 * Mv) * (64 * Mu) ≤ Cc) ∧
      (64 * Mv * (8 + 128 * Mu) ≤ Cc) ∧ (64 * Mv * (64 * Mu) ≤ Cc) :=
    mixed_coefficient_bounds hMv hMu
  have p1 := mul_le_mul_of_nonneg_right c1 (mul_nonneg h2 h1)
  have p2 := mul_le_mul_of_nonneg_right c2 (mul_nonneg (mul_nonneg h6 h4) h1)
  have p3 := mul_le_mul_of_nonneg_right c3 (mul_nonneg (mul_nonneg h5 h2) h3)
  have p4 := mul_le_mul_of_nonneg_right c4 (mul_nonneg (mul_nonneg (mul_nonneg h6 h5) h4) h3)
  have hprod : (∑ ε : Fin d → Bool, |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)|) *
      ∑ ε' : Fin d → Bool, |D.phiT R T - D.phiT R (T.child ε')| ≤
      2 ^ d * 2 ^ d * Cc * (Δg * Δh + Eh * Δg * Δ5 + Eg * Δ4 * Δh + Eg * Eh * Δ4 * Δ5) := by
    calc _ ≤ (2 ^ d * ((8 + 128 * Mv) * Δh + 64 * Mv * Eh * Δ5)) *
          (2 ^ d * ((8 + 128 * Mu) * Δg + 64 * Mu * Eg * Δ4)) :=
          mul_le_mul hψ hφ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
      _ = 2 ^ d * 2 ^ d * (((8 + 128 * Mv) * (8 + 128 * Mu)) * (Δg * Δh) +
          ((8 + 128 * Mv) * (64 * Mu)) * (Eg * Δ4 * Δh) + (64 * Mv * (8 + 128 * Mu)) * (Eh * Δg *
            Δ5) +
          (64 * Mv * (64 * Mu)) * (Eg * Eh * Δ4 * Δ5)) := by ring
      _ ≤ 2 ^ d * 2 ^ d * (Cc * (Δg * Δh) + Cc * (Eg * Δ4 * Δh) + Cc * (Eh * Δg * Δ5) +
          Cc * (Eg * Eh * Δ4 * Δ5)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact add_le_add (add_le_add (add_le_add p1 p2) p3) p4
      _ = _ := by ring
  rw [hE3, mul_one]
  have hCU : 0 ≤ D.Cdiag * D.UT T := mul_nonneg D.Cdiag_nonneg (D.UT_nonneg T)
  calc _ ≤ D.Cdiag * D.UT T * ((∑ ε : Fin d → Bool,
          |D.psiT hR hRs hFR T - D.psiT hR hRs hFR (T.child ε)|) *
          ∑ ε' : Fin d → Bool, |D.phiT R T - D.phiT R (T.child ε')|) := hA
    _ ≤ D.Cdiag * D.UT T * (2 ^ d * 2 ^ d * Cc * (Δg * Δh + Eh * Δg * Δ5 + Eg * Δ4 * Δh +
          Eg * Eh * Δ4 * Δ5)) := mul_le_mul_of_nonneg_left hprod hCU
    _ = _ := by
        unfold UT
        ring

/-- The constant of Lemma 2.72 for the exponents `r`, `q`, under the hypothesis `1/r + 1/q ≤ 1`
(always true for a Hölder tuple): the constant of `lemma272` when `1/r + 1/q < 1` (`n ≥ 3`: there
is an entry besides `h` and `g`), and the constant of the endpoint case `lemma272one` when
`1/r + 1/q = 1` (`n = 2`). -/
noncomputable def C272 (hrq : 1 / D.r + 1 / D.q ≤ 1) : ℝ :=
  if h : 1 / D.r + 1 / D.q < 1 then Classical.choose (lemma272 D.hd D.r D.q D.hr D.hq h)
  else Classical.choose (lemma272one D.hd D.r D.q D.hr D.hq (le_antisymm hrq (not_lt.mp h)))

theorem C272_nonneg (hrq : 1 / D.r + 1 / D.q ≤ 1) : 0 ≤ D.C272 hrq := by
  unfold C272
  split_ifs with h
  · exact (Classical.choose_spec (lemma272 D.hd D.r D.q D.hr D.hq h)).1
  · exact (Classical.choose_spec (lemma272one D.hd D.r D.q D.hr D.hq
      (le_antisymm hrq (not_lt.mp h)))).1

/-- Lemma 2.72 for the data, in the case `1/r + 1/q < 1`. [PROVED] -/
theorem C272_spec (hrq : 1 / D.r + 1 / D.q ≤ 1) (hlt : 1 / D.r + 1 / D.q < 1) (C₀ : ℝ)
    (R : DyadicCube d) (f₁ f₂ f₃ f₄ f₅ : (Fin d → ℝ) → ℝ) (α : DyadicCube d → ℝ) (hC₀ : 0 ≤ C₀)
    (h₁ : MemLp f₁ (ENNReal.ofReal D.r) volume) (h₂ : MemLp f₂ (ENNReal.ofReal D.q) volume)
    (h₃ : MemLp f₃ (ENNReal.ofReal ((D.r * D.q / (D.r + D.q)) / (D.r * D.q / (D.r + D.q) - 1)))
      volume)
    (h₄ : MemLp f₄ ⊤ volume) (h₄1 : eLpNorm f₄ ⊤ volume ≤ 1)
    (h₅ : MemLp f₅ ⊤ volume) (h₅1 : eLpNorm f₅ ⊤ volume ≤ 1)
    (hα : ∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T f₂ * martDiff T f₁
      + martAvg T f₁ * martDiff T f₂ * martDiff T f₅
      + martAvg T f₂ * martDiff T f₄ * martDiff T f₁
      + martAvg T f₂ * martAvg T f₁ * martDiff T f₄ * martDiff T f₅) * martAvg T f₃ * T.vol) :
    ∑' T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal (D.C272 hrq * C₀) *
      (eLpNorm (truncate R f₁) (ENNReal.ofReal D.r) volume *
        eLpNorm (truncate R f₂) (ENNReal.ofReal D.q) volume *
        eLpNorm (truncate R f₃)
          (ENNReal.ofReal ((D.r * D.q / (D.r + D.q)) / (D.r * D.q / (D.r + D.q) - 1))) volume) := by
  have e : D.C272 hrq = Classical.choose (lemma272 D.hd D.r D.q D.hr D.hq hlt) := by
    simp only [C272, hlt, ↓reduceDIte]
  rw [e]
  exact (Classical.choose_spec (lemma272 D.hd D.r D.q D.hr D.hq hlt)).2
    C₀ R f₁ f₂ f₃ f₄ f₅ α hC₀ h₁ h₂ h₃ h₄ h₄1 h₅ h₅1 hα

/-- Lemma 2.72 for the data in the endpoint case `1/r + 1/q = 1` (`n = 2`). [PROVED] -/
theorem C272_spec_one (hrq : 1 / D.r + 1 / D.q ≤ 1) (hlt : ¬ 1 / D.r + 1 / D.q < 1) (C₀ : ℝ)
    (R : DyadicCube d) (f₁ f₂ f₄ f₅ : (Fin d → ℝ) → ℝ) (α : DyadicCube d → ℝ) (hC₀ : 0 ≤ C₀)
    (h₁ : MemLp f₁ (ENNReal.ofReal D.r) volume) (h₂ : MemLp f₂ (ENNReal.ofReal D.q) volume)
    (h₄ : MemLp f₄ ⊤ volume) (h₄1 : eLpNorm f₄ ⊤ volume ≤ 1)
    (h₅ : MemLp f₅ ⊤ volume) (h₅1 : eLpNorm f₅ ⊤ volume ≤ 1)
    (hα : ∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T f₂ * martDiff T f₁
      + martAvg T f₁ * martDiff T f₂ * martDiff T f₅
      + martAvg T f₂ * martDiff T f₄ * martDiff T f₁
      + martAvg T f₂ * martAvg T f₁ * martDiff T f₄ * martDiff T f₅) * T.vol) :
    ∑' T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal (D.C272 hrq * C₀) *
      (eLpNorm (truncate R f₁) (ENNReal.ofReal D.r) volume *
        eLpNorm (truncate R f₂) (ENNReal.ofReal D.q) volume) := by
  have e : D.C272 hrq = Classical.choose (lemma272one D.hd D.r D.q D.hr D.hq
      (le_antisymm hrq (not_lt.mp hlt))) := by
    simp only [C272, hlt, ↓reduceDIte]
  rw [e]
  exact (Classical.choose_spec (lemma272one D.hd D.r D.q D.hr D.hq
    (le_antisymm hrq (not_lt.mp hlt)))).2 C₀ R f₁ f₂ f₄ f₅ α hC₀ h₁ h₂ h₄ h₄1 h₅ h₅1 hα

/-- The dual exponent `s' = (rq/(r+q))/(rq/(r+q) − 1)` of Lemma 2.72 satisfies
`1/s' = 1 − 1/r − 1/q` and `s' > 1`. [PROVED] -/
theorem inv_s'_eq (hlt : 1 / D.r + 1 / D.q < 1) :
    1 / ((D.r * D.q / (D.r + D.q)) / (D.r * D.q / (D.r + D.q) - 1)) = 1 - 1 / D.r - 1 / D.q ∧
      1 < (D.r * D.q / (D.r + D.q)) / (D.r * D.q / (D.r + D.q) - 1) := by
  obtain ⟨_, _, h1, h2, h3⟩ := holder_exponents D.hr D.hq hlt rfl
  exact ⟨by linarith, h2⟩

/-- The constant of the `𝐓`-portion of (2.60):
`C₆₀T = C_{2.72} C_diag 2^d 2^d C_co · pruneConst' · C_ψ'`. -/
noncomputable def C₆₀T (hrq : 1 / D.r + 1 / D.q ≤ 1) : ℝ :=
  D.C272 hrq * (D.Cdiag * (2 ^ d * 2 ^ d) * D.Cco) * (D.second R hR hRs hFR).pruneConst *
    D.psiConst

/-- **The `𝐓`-portion of (2.60)** (p. 55–56): `∑_{T ∈ setT2} |Λ_T(X_T, Y_T)| ≤ C₆₀T E_R`, by Lemma
2.72
with `f₁ = 𝔥`, `f₂ = 𝔤̂`, `f₃ = 𝟙_R`, `f₄ = û/M_u`, `f₅ = v̂/M_v`. [PROVED] -/
theorem sum_setT2_le (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) :
    ∑ T ∈ D.setT2 hR hRs hFR, |twoSlotForm D.T D.a D.b D.g T
        (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T')| ≤ D.C₆₀T hR hRs hFR hrq * D.E R := by
  classical
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hF := D.Fpos'
  have hV := D.Q.vol_pos
  have hR0 := R.vol_pos
  have hVq : 0 ≤ D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) := Real.rpow_nonneg hV.le _
  have hCd := D.Cdiag_nonneg
  have hCco := D.Cco_nonneg
  set C₀ : ℝ := D.Cdiag * D.F * D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) * (2 ^ d * 2 ^ d) * D.Cco
    with hC₀def
  have hC₀ : 0 ≤ C₀ := by positivity
  set α : DyadicCube d → ℝ := fun T => if T ∈ D.setT2 hR hRs hFR then
    twoSlotForm D.T D.a D.b D.g T (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
      (D.yT R T - ∑ T' ∈ children T, D.yT R T') else 0 with hα
  have hα_le : ∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T (D.ghat R) * martDiff T (D.prunedH hR hRs hFR)
      + martAvg T (D.prunedH hR hRs hFR) * martDiff T (D.ghat R) * martDiff T (D.fthree hR hRs hFR)
      + martAvg T (D.ghat R) * martDiff T (D.fthreeG hR hRs hFR) * martDiff T (D.prunedH hR hRs hFR)
      + martAvg T (D.ghat R) * martAvg T (D.prunedH hR hRs hFR) *
          martDiff T (D.fthreeG hR hRs hFR) * martDiff T (D.fthree hR hRs hFR)) *
      martAvg T ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) * T.vol := by
    intro T _
    by_cases hT : T ∈ D.setT2 hR hRs hFR
    · simp only [hα, hT, ↓reduceIte]
      exact D.abs_alpha60_le hR hRs hFR hT
    · simp only [hα, hT, ↓reduceIte, abs_zero]
      have h1 := martDiff_nonneg T (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)
      have h2 := martDiff_nonneg T (D.ghat R : (Fin d → ℝ) → ℝ)
      have h3 := martDiff_nonneg T (D.fthree hR hRs hFR : (Fin d → ℝ) → ℝ)
      have h4 := martDiff_nonneg T (D.fthreeG hR hRs hFR : (Fin d → ℝ) → ℝ)
      have h5 := martAvg_nonneg T (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)
      have h6 := martAvg_nonneg T (D.ghat R : (Fin d → ℝ) → ℝ)
      have h7 := martAvg_nonneg T ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ)
      have h8 := T.vol_pos.le
      positivity
  -- finiteness and the conversion to real numbers
  have hE₁ : eLpNorm (truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.r)
      volume ≠ ⊤ := (TestFun.memLp (TestFun.truncateₗ R (D.prunedH hR hRs hFR)).2 _).eLpNorm_ne_top
  have hE₂ : eLpNorm (truncate R (D.ghat R : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.q) volume ≠ ⊤ :=
    (TestFun.memLp (TestFun.truncateₗ R (D.ghat R)).2 _).eLpNorm_ne_top
  have hsub : ∀ T ∈ D.setT2 hR hRs hFR, T ∈ R.tree := fun T hT =>
    D.subset_R_of_mem_setF2 hR hRs hFR ((D.mem_setT2 hR hRs hFR).mp hT).1
  have h2 : ∑ T ∈ D.setT2 hR hRs hFR, ‖α T‖ₑ ≤ ∑' T : R.tree, ‖α T‖ₑ := by
    rw [← Finset.sum_subtype_of_mem (fun T => ‖α T‖ₑ) hsub]
    exact ENNReal.sum_le_tsum _
  -- the truncations
  have e𝔥 : truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) = D.prunedH hR hRs hFR :=
    congrArg Subtype.val (TestFun.truncateₗ_of_supportedOn (D.prunedH_supported hR hRs hFR))
  have e𝔤 : truncate R (D.ghat R : (Fin d → ℝ) → ℝ) = D.ghat R :=
    congrArg Subtype.val (TestFun.truncateₗ_of_supportedOn (D.ghat_supported R))
  -- Lemma 2.72 (or its endpoint case): the bound in terms of the norms of `𝔥`, `𝔤̂`
  have hmain : ∑ T ∈ D.setT2 hR hRs hFR, |α T| ≤ D.C272 hrq * C₀ *
      (lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r *
        lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q * R.vol ^ (1 - 1 / D.r - 1 / D.q)) := by
    by_cases hlt : 1 / D.r + 1 / D.q < 1
    · obtain ⟨hs'inv, hs'1⟩ := D.inv_s'_eq hlt
      set s' : ℝ := (D.r * D.q / (D.r + D.q)) / (D.r * D.q / (D.r + D.q) - 1) with hs'
      have hs'0 : 0 < s' := by linarith
      have h272 := D.C272_spec hrq hlt C₀ R (D.prunedH hR hRs hFR) (D.ghat R) (TestFun.ind R)
        (D.fthreeG hR hRs hFR) (D.fthree hR hRs hFR) α hC₀
        (TestFun.memLp (D.prunedH hR hRs hFR).2 _)
        (TestFun.memLp (D.ghat R).2 _) (TestFun.memLp (TestFun.ind R).2 _)
        (TestFun.memLp (D.fthreeG hR hRs hFR).2 _) (D.eLpNorm_fthreeG_le hR hRs hFR)
        (TestFun.memLp (D.fthree hR hRs hFR).2 _) (D.eLpNorm_fthree_le hR hRs hFR) hα_le
      have hE₃ : eLpNorm (truncate R ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ))
          (ENNReal.ofReal s') volume ≠ ⊤ :=
        (TestFun.memLp (TestFun.truncateₗ R (TestFun.ind R)).2 _).eLpNorm_ne_top
      have hfin : ENNReal.ofReal (D.C272 hrq * C₀) *
          (eLpNorm (truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.r)
              volume *
            eLpNorm (truncate R (D.ghat R : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.q) volume *
            eLpNorm (truncate R ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ))
              (ENNReal.ofReal s') volume) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top hE₁ hE₂) hE₃)
      have h3 := ENNReal.toReal_mono hfin (h2.trans h272)
      rw [ENNReal.toReal_sum (fun T _ => enorm_ne_top), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (D.C272_nonneg hrq) hC₀)] at h3
      simp only [toReal_enorm, Real.norm_eq_abs] at h3
      have eind : truncate R ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) = TestFun.ind R :=
        congrArg Subtype.val (TestFun.truncateₗ_ind R)
      have hind : lpNorm ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) s' =
          R.vol ^ (1 - 1 / D.r - 1 / D.q) := by
        rw [TestFun.lpNorm_ind R hs'0, hs'inv]
      calc ∑ T ∈ D.setT2 hR hRs hFR, |α T|
          ≤ D.C272 hrq * C₀ * (lpNorm (truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)) D.r *
              lpNorm (truncate R (D.ghat R : (Fin d → ℝ) → ℝ)) D.q *
              lpNorm (truncate R ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ)) s') := h3
        _ = _ := by rw [e𝔥, e𝔤, eind, hind]
    · have heq : 1 / D.r + 1 / D.q = 1 := le_antisymm hrq (not_lt.mp hlt)
      have hone : ∀ T ∈ R.tree, martAvg T ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) = 1 :=
        fun T hT => by
          rw [martAvg, avg_ind_of_subset (DyadicCube.mem_tree.mp hT), abs_one]
      have hα_le' : ∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T (D.ghat R) *
          martDiff T (D.prunedH hR hRs hFR)
          + martAvg T (D.prunedH hR hRs hFR) * martDiff T (D.ghat R) *
              martDiff T (D.fthree hR hRs hFR)
          + martAvg T (D.ghat R) * martDiff T (D.fthreeG hR hRs hFR) *
              martDiff T (D.prunedH hR hRs hFR)
          + martAvg T (D.ghat R) * martAvg T (D.prunedH hR hRs hFR) *
              martDiff T (D.fthreeG hR hRs hFR) * martDiff T (D.fthree hR hRs hFR)) * T.vol := by
        intro T hT
        have h := hα_le T hT
        rwa [hone T hT, mul_one] at h
      have h272 := D.C272_spec_one hrq hlt C₀ R (D.prunedH hR hRs hFR) (D.ghat R)
        (D.fthreeG hR hRs hFR) (D.fthree hR hRs hFR) α hC₀
        (TestFun.memLp (D.prunedH hR hRs hFR).2 _) (TestFun.memLp (D.ghat R).2 _)
        (TestFun.memLp (D.fthreeG hR hRs hFR).2 _) (D.eLpNorm_fthreeG_le hR hRs hFR)
        (TestFun.memLp (D.fthree hR hRs hFR).2 _) (D.eLpNorm_fthree_le hR hRs hFR) hα_le'
      have hfin : ENNReal.ofReal (D.C272 hrq * C₀) *
          (eLpNorm (truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.r)
              volume *
            eLpNorm (truncate R (D.ghat R : (Fin d → ℝ) → ℝ)) (ENNReal.ofReal D.q) volume) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hE₁ hE₂)
      have h3 := ENNReal.toReal_mono hfin (h2.trans h272)
      rw [ENNReal.toReal_sum (fun T _ => enorm_ne_top), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (mul_nonneg (D.C272_nonneg hrq) hC₀)] at h3
      simp only [toReal_enorm, Real.norm_eq_abs] at h3
      have hexp : (1 : ℝ) - 1 / D.r - 1 / D.q = 0 := by linarith
      rw [hexp, Real.rpow_zero, mul_one]
      calc ∑ T ∈ D.setT2 hR hRs hFR, |α T|
          ≤ D.C272 hrq * C₀ * (lpNorm (truncate R (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ)) D.r *
              lpNorm (truncate R (D.ghat R : (Fin d → ℝ) → ℝ)) D.q) := h3
        _ = _ := by rw [e𝔥, e𝔤]
  have h𝔥 : lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ≤
      (D.second R hR hRs hFR).pruneConst * R.vol ^ (1 / D.r) := by
    have h := (D.second R hR hRs hFR).pruned_lpNorm_le
    rw [show (D.second R hR hRs hFR).q = D.r from rfl,
      show ((D.second R hR hRs hFR).G : (Fin d → ℝ) → ℝ) = ((TestFun.ind R : TestFun d) :
        (Fin d → ℝ) → ℝ) from rfl, TestFun.lpNorm_ind R hr0] at h
    exact h
  have h𝔤 := D.lpNorm_ghat_le hR hRs hG
  have hα_eq : ∀ T ∈ D.setT2 hR hRs hFR, |α T| = |twoSlotForm D.T D.a D.b D.g T
      (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
      (D.yT R T - ∑ T' ∈ children T, D.yT R T')| := fun T hT => by
    simp only [hα, hT, ↓reduceIte]
  have hK := D.KQ_nonneg
  have hpc := D.second_pruneConst_nonneg hR hRs hFR
  have hψc := D.psiConst_nonneg
  have hsplit := D.vol_rpow_split R
  have hCC : 0 ≤ D.C272 hrq * C₀ := mul_nonneg (D.C272_nonneg hrq) hC₀
  have hg0 := lpNorm_nonneg (D.ghat R : (Fin d → ℝ) → ℝ) D.q
  have hh0 := lpNorm_nonneg (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r
  have hRa : 0 ≤ R.vol ^ (1 - 1 / D.r - 1 / D.q) := Real.rpow_nonneg hR0.le _
  calc ∑ T ∈ D.setT2 hR hRs hFR, |twoSlotForm D.T D.a D.b D.g T
          (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
          (D.yT R T - ∑ T' ∈ children T, D.yT R T')|
      = ∑ T ∈ D.setT2 hR hRs hFR, |α T| := (Finset.sum_congr rfl hα_eq).symm
    _ ≤ D.C272 hrq * C₀ * (lpNorm (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) D.r *
          lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q * R.vol ^ (1 - 1 / D.r - 1 / D.q)) := hmain
    _ ≤ D.C272 hrq * C₀ * (((D.second R hR hRs hFR).pruneConst * R.vol ^ (1 / D.r)) *
          (D.psiConst * D.KQ * R.vol ^ (1 / D.q)) * R.vol ^ (1 - 1 / D.r - 1 / D.q)) := by
        gcongr
    _ = D.C₆₀T hR hRs hFR hrq * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) *
          (D.Q.vol ^ (-(1 - 1 / D.r - 1 / D.q)) * D.Q.vol ^ (-(1 / D.q))) *
          (R.vol ^ (1 - 1 / D.r - 1 / D.q) * R.vol ^ (1 / D.r) * R.vol ^ (1 / D.q)) := by
        rw [hC₀def]
        unfold C₆₀T KQ
        ring
    _ = D.C₆₀T hR hRs hFR hrq * D.E R := by
        rw [hsplit, D.Q_rpow_split]
        unfold E
        ring

/-- The constant of the estimate of (2.60): `C₆₀ = C₆₀P + C₆₀T`. -/
noncomputable def C₆₀ (hrq : 1 / D.r + 1 / D.q ≤ 1) : ℝ :=
  D.C₆₀P hR hRs hFR + D.C₆₀T hR hRs hFR hrq

/-- **The estimate of the term (2.60)** (p. 54–56): `|∑_T Λ_R(X_T, Y_T)| ≤ C₆₀ E_R`. [PROVED] -/
theorem abs_sum_2_60_le (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) :
    |∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, twoSlotForm D.T D.a D.b D.g R
        (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
        (D.yT R T - ∑ T' ∈ children T, D.yT R T')| ≤ D.C₆₀ hR hRs hFR hrq * D.E R := by
  rw [D.sum_2_60_eq hR hRs hFR, D.sum_setF2_eq hR hRs hFR]
  have hP := D.sum_setP2_le hR hRs hFR hG
  have hT := D.sum_setT2_le hR hRs hFR hG hrq
  calc |∑ T ∈ D.setP2 hR hRs hFR, twoSlotForm D.T D.a D.b D.g T
          (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
          (D.yT R T - ∑ T' ∈ children T, D.yT R T') +
        ∑ T ∈ D.setT2 hR hRs hFR, twoSlotForm D.T D.a D.b D.g T
          (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
          (D.yT R T - ∑ T' ∈ children T, D.yT R T')|
      ≤ ∑ T ∈ D.setP2 hR hRs hFR, |twoSlotForm D.T D.a D.b D.g T
          (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
          (D.yT R T - ∑ T' ∈ children T, D.yT R T')| +
        ∑ T ∈ D.setT2 hR hRs hFR, |twoSlotForm D.T D.a D.b D.g T
          (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
          (D.yT R T - ∑ T' ∈ children T, D.yT R T')| :=
        (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
          (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ D.C₆₀P hR hRs hFR * D.E R + D.C₆₀T hR hRs hFR hrq * D.E R := add_le_add hP hT
    _ = D.C₆₀ hR hRs hFR hrq * D.E R := by
        unfold C₆₀
        ring

/-- **The estimate (2.40)** (p. 51–56): for a cube `R` of the tree in no first stopping cube with
`F_R > 0`, under the standing assumptions (the bound (2.8) for `g`, `1/r + 1/q ≤ 1`, and the
constancy of `𝔥`, `v`, `𝔤̂`, `u` on the leaves), `|Λ_R(𝔥, 𝔤̂)| ≤ (C₅₈ + C₅₉ + C₆₀) E_R`: the
telescoping (2.56)–(2.60), the vanishing of (2.57) (`ψ_R = 0`), and the estimates of the three
terms (2.58), (2.59), (2.60). [PROVED] -/
theorem estimate_2_40 (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1)
    (hconst : ∀ T ∈ level (D.second R hR hRs hFR).N R,
      (ConstOn (D.prunedH hR hRs hFR) T ∧ ConstOn (D.vP R) T) ∧
        (ConstOn (D.ghat R) T ∧ ConstOn D.u T)) :
    |twoSlotForm D.T D.a D.b D.g R (D.prunedH hR hRs hFR) (D.ghat R)| ≤
      (D.C₅₈ hR hRs hFR + D.C₅₉ hR hRs hFR + D.C₆₀ hR hRs hFR hrq) * D.E R := by
  rw [D.form2_prunedH_ghat_eq hR hRs hFR hconst]
  have h57 : twoSlotForm D.T D.a D.b D.g R (D.xT hR hRs hFR R) (D.yT R R) = 0 := by
    rw [xT, D.psiT_self hR hRs hFR, zero_smul, twoSlotForm_zero_left D.T D.hab]
  rw [h57, D.sum_2_58_eq hR hRs hFR, D.sum_2_59_eq hR hRs hFR, zero_sub]
  have h58 := D.abs_form2_theta_le_E hR hRs hFR hG
  have h59 := D.abs_form2_vP_thetaG_le_E hR hRs hFR hG
  have h60 := D.abs_sum_2_60_le hR hRs hFR hG hrq
  set A := twoSlotForm D.T D.a D.b D.g R (D.theta hR hRs hFR) D.u
  set Bv := twoSlotForm D.T D.a D.b D.g R (D.vP R) (D.thetaG hR hRs hFR)
  set Cs := ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, twoSlotForm D.T D.a D.b D.g R
    (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
    (D.yT R T - ∑ T' ∈ children T, D.yT R T')
  have h1 := abs_add_le (-A - Bv) Cs
  have h2 := abs_sub (-A) Bv
  rw [abs_neg] at h2
  linarith

end Term260

/-! ### Closing the contraction: `A' ≤ C/ε` and the estimate (2.14) at `R = Q` (p. 44, p. 47)

The constants of (2.40) were defined through the second stopping data `D.second R hR hRs hFR`
and hence formally depend on `R`; since the second stopping time has `q = r`, `B`, `ε`, `m = 2`
independent of `R`, each of them equals an `R`-free constant. Combining (2.39) and (2.40) at every
admissible cube `R` gives `A' ≤ (1−ε) A' + C₃₉ + C₄₀`, hence `A' ≤ (C₃₉ + C₄₀)/ε`, and (2.23) at the
admissible cube `R = Q` (where `ψ_Q = 𝔤`) is the estimate (2.14). -/

section Closing

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

theorem second_q : (D.second R hR hRs hFR).q = D.r := rfl

theorem second_B : (D.second R hR hRs hFR).B = D.B := rfl

/-- `C_G` of the second stopping time is `2^d (n+2)/ε`. [PROVED] -/
theorem second_CG : (D.second R hR hRs hFR).CG = D.CGs := by
  unfold CG
  rw [second_ε]
  change 2 ^ d * (n + ((2 : ℕ) : ℝ)) / D.ε = 2 ^ d * (n + 2) / D.ε
  norm_num

/-- The `R`-free version of `C_φ` of the second stopping time. -/
noncomputable def CφS : ℝ := 1 + 8 * D.CGs ^ (1 / D.r) * (4 + 2 * ⌊(2 : ℝ) ^ d / D.ε⌋₊)

theorem second_Cφ : (D.second R hR hRs hFR).Cφ = D.CφS := by
  unfold Cφ CφS
  rw [second_CG, second_q, second_ε]

/-- The `R`-free version of `C_loc` of the second stopping time. -/
noncomputable def locConstS : ℝ :=
  D.CGs ^ (1 / D.r) * (3 + 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * (2 + 4 * ⌊(2 : ℝ) ^ d / D.ε⌋₊)) +
    (2 ^ d * D.B / D.ε) ^ (1 / D.r)

theorem second_locConst : (D.second R hR hRs hFR).locConst = D.locConstS := by
  unfold locConst locConstS
  rw [second_CG, second_q, second_B, second_ε]

/-- The `R`-free version of the pruning constant of the second stopping time. -/
noncomputable def pruneConstS : ℝ :=
  3 + D.B ^ (1 / D.r) + 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * (1 + 2 * ⌊(2 : ℝ) ^ d / D.ε⌋₊)

theorem second_pruneConst : (D.second R hR hRs hFR).pruneConst = D.pruneConstS := by
  unfold pruneConst pruneConstS
  rw [second_q, second_B, second_ε]

/-- The `R`-free version of `C_ψ`. -/
noncomputable def CψS : ℝ := D.CφS + 8 * D.locConstS

theorem Cψ_eq : D.Cψ hR hRs hFR = D.CψS := by
  unfold Cψ CψS
  rw [D.second_Cφ hR hRs hFR, D.second_locConst hR hRs hFR]

/-- The `R`-free version of `C_Θ`. -/
noncomputable def CΘS : ℝ :=
  2 * D.CφT * D.CψS * (2 ^ d / D.ε) + D.C271 * (D.CφT * D.Cmart) * D.pruneConstS

theorem CΘ_eq : D.CΘ hR hRs hFR = D.CΘS := by
  unfold CΘ CΘS
  rw [D.Cψ_eq hR hRs hFR, D.second_pruneConst hR hRs hFR]

/-- The `R`-free constant of (2.58). -/
noncomputable def C₅₈S : ℝ :=
  2 ^ d * D.B * D.ε⁻¹ * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * D.CΘS * D.B ^ (1 / D.q)

theorem C₅₈_eq : D.C₅₈ hR hRs hFR = D.C₅₈S := by
  unfold C₅₈ C₅₈S
  rw [D.CΘ_eq hR hRs hFR]

/-- The `R`-free version of `C_Θ'`. -/
noncomputable def CΘGS : ℝ :=
  2 * D.CψS * D.CφT * (2 ^ d / D.ε) + D.C271q * (D.CψS * D.CmartG) * D.psiConst

theorem CΘG_eq : D.CΘG hR hRs hFR = D.CΘGS := by
  unfold CΘG CΘGS
  rw [D.Cψ_eq hR hRs hFR]

/-- The `R`-free constant of (2.59). -/
noncomputable def C₅₉S : ℝ :=
  D.B * D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.B ^ (1 / D.r) * (2 ^ d * D.B / D.ε) ^ (1 / D.q) * D.CΘGS

theorem C₅₉_eq : D.C₅₉ hR hRs hFR = D.C₅₉S := by
  unfold C₅₉ C₅₉S
  rw [D.CΘG_eq hR hRs hFR]

/-- The `R`-free constant of the `parents(𝐏)`-portion of (2.60). -/
noncomputable def C₆₀PS : ℝ := 8 * (2 ^ d * 2 ^ d) * (2 ^ d / D.ε) * D.Cdiag * D.CψS * D.CφT

theorem C₆₀P_eq : D.C₆₀P hR hRs hFR = D.C₆₀PS := by
  unfold C₆₀P C₆₀PS
  rw [D.Cψ_eq hR hRs hFR]

/-- The `R`-free constant of the `𝐓`-portion of (2.60). -/
noncomputable def C₆₀TS (hrq : 1 / D.r + 1 / D.q ≤ 1) : ℝ :=
  D.C272 hrq * (D.Cdiag * (2 ^ d * 2 ^ d) * D.Cco) * D.pruneConstS * D.psiConst

theorem C₆₀T_eq (hrq : 1 / D.r + 1 / D.q ≤ 1) : D.C₆₀T hR hRs hFR hrq = D.C₆₀TS hrq := by
  unfold C₆₀T C₆₀TS
  rw [D.second_pruneConst hR hRs hFR]

/-- **The constant of (2.40)**, independent of `R`: `C₄₀ = C₅₈ + C₅₉ + C₆₀`. -/
noncomputable def C₄₀ (hrq : 1 / D.r + 1 / D.q ≤ 1) : ℝ :=
  D.C₅₈S + D.C₅₉S + (D.C₆₀PS + D.C₆₀TS hrq)

theorem C₄₀_eq (hrq : 1 / D.r + 1 / D.q ≤ 1) :
    D.C₅₈ hR hRs hFR + D.C₅₉ hR hRs hFR + D.C₆₀ hR hRs hFR hrq = D.C₄₀ hrq := by
  unfold C₆₀ C₄₀
  rw [D.C₅₈_eq hR hRs hFR, D.C₅₉_eq hR hRs hFR, D.C₆₀P_eq hR hRs hFR, D.C₆₀T_eq hR hRs hFR hrq]

/-- `Λ_R(ρ, ρ') = 0` when `F_R = 0`: some frozen entry `f_j 𝟙_R`, `j ≠ k, k+1`, vanishes almost
everywhere. [PROVED] -/
theorem twoSlotForm_eq_zero_of_FP_eq_zero (h : D.FP R = 0) (ρ ρ' : TestFun d) :
    twoSlotForm D.T D.a D.b D.g R ρ ρ' = 0 := by
  obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp h
  simp only [J, Finset.mem_erase, Finset.mem_univ, and_true] at hj
  unfold twoSlotForm
  apply D.T.form_eq_zero_of_ae_zero _ j
  rw [Function.update_of_ne hj.1, Function.update_of_ne hj.2]
  have hp : 0 < D.p.p j := by linarith [D.p.one_lt j]
  have hmem := TestFun.memLp (TestFun.truncateₗ R (D.g j)).2 (ENNReal.ofReal (D.p.p j))
  have h0 : eLpNorm (TestFun.truncateₗ R (D.g j) : (Fin d → ℝ) → ℝ) (ENNReal.ofReal (D.p.p j))
      volume = 0 := by
    unfold lpNorm at hj0
    exact ((ENNReal.toReal_eq_zero_iff _).mp hj0).resolve_right hmem.eLpNorm_ne_top
  exact (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hp).ne').mp h0

/-- The form of (2.23) at `R` splits as `Λ_R(h_R − 𝔥, 𝔤̂) + Λ_R(𝔥, 𝔤̂)`, the terms of (2.39) and
(2.40). [PROVED] -/
theorem form2_ind_psi_eq :
    D.form2 R (TestFun.ind R) (D.psi R) =
      twoSlotForm D.T D.a D.b D.g R (TestFun.ind R - D.prunedH hR hRs hFR) (D.ghat R) +
        twoSlotForm D.T D.a D.b D.g R (D.prunedH hR hRs hFR) (D.ghat R) := by
  rw [form2, ← twoSlotForm_add_left D.T D.hab, sub_add_cancel, ghat_eq,
    twoSlotForm_truncateₗ_right]

/-- **The leaf-constancy hypothesis of the telescoping (2.56)** (p. 51): at every admissible cube
`R` with `F_R > 0`, the functions `𝔥, v_R, 𝔤̂, u` are constant on the leaves of the second stopping
time (the cubes of the finest scale `2^{-N} ℓ(Q)`). -/
def LeafConst : Prop :=
  ∀ (S : DyadicCube d) (hS : S ∈ D.tree) (hSs : D.NotInStopping S) (hFS : 0 < D.FP S),
    ∀ T ∈ level (D.second S hS hSs hFS).N S,
      (ConstOn (D.prunedH hS hSs hFS) T ∧ ConstOn (D.vP S) T) ∧
        (ConstOn (D.ghat S) T ∧ ConstOn D.u T)

include hR hRs hFR in
/-- **(2.39) and (2.40) combined** at an admissible cube `R` with `F_R > 0`:
`|Λ_R(h_R, ψ_R)| ≤ ((1−ε) A' + C₃₉ + C₄₀) E_R`. [PROVED] -/
theorem abs_form2_le_of_FP_pos (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) (hLC : D.LeafConst) :
    |D.form2 R (TestFun.ind R) (D.psi R)| ≤
      ((1 - D.ε) * D.A' + D.C₃₉ + D.C₄₀ hrq) * D.E R := by
  rw [D.form2_ind_psi_eq hR hRs hFR]
  have h39 := D.estimate_2_39 hR hRs hFR hG
  have h40 := D.estimate_2_40 hR hRs hFR hG hrq (hLC R hR hRs hFR)
  rw [D.C₄₀_eq hR hRs hFR hrq] at h40
  have e : ((1 - D.ε) * D.A' + D.C₃₉) * D.E R + D.C₄₀ hrq * D.E R =
      ((1 - D.ε) * D.A' + D.C₃₉ + D.C₄₀ hrq) * D.E R := by ring
  rw [← e]
  exact (abs_add_le _ _).trans (add_le_add h39 h40)

/-- `F_Q = F`. [PROVED] -/
theorem FP_Q : D.FP D.Q = D.F := by
  unfold FP F
  exact Finset.prod_congr rfl fun j _ => by rw [TestFun.truncateₗ_of_supportedOn (D.supp j)]

include D in
/-- Two dyadic cubes containing each other are equal. [PROVED] -/
theorem cube_eq_of_subset_of_subset {P P' : DyadicCube d} (h1 : P.toSet ⊆ P'.toSet)
    (h2 : P'.toSet ⊆ P.toSet) : P = P' :=
  DyadicCube.eq_of_subset_of_m_eq h1
    (le_antisymm (DyadicCube.m_le_of_subset D.hd h1) (DyadicCube.m_le_of_subset D.hd h2))

/-- If `|Q|⁻¹ < c` then `c I ≤ |Q|⁻¹ I` fails for `0 < I < ∞`: the Chebyshev-type stopping
conditions cannot hold at `Q` itself. [PROVED] -/
theorem not_le_of_inv_vol_lt {c I : ENNReal} (hlt : (volume D.Q.toSet)⁻¹ < c) (hI0 : I ≠ 0)
    (hItop : I ≠ ⊤) : ¬ c * I ≤ (volume D.Q.toSet)⁻¹ * I := by
  have h1 := ENNReal.mul_lt_mul_right hI0 hItop hlt
  rw [mul_comm I, mul_comm I] at h1
  exact not_le.mpr h1

/-- `Q ∉ 𝐏₁`: the conditions (2.3) fail at `Q` since `(n+m)/ε > 1`. [PROVED] -/
theorem Q_notMem_P1 : D.Q ∉ D.P1 := by
  intro h
  have hε := D.ε_pos
  have hεle := D.ε_le
  have hV := D.Q.vol_pos
  have hnm := D.one_le_n_add_m
  have hnm0 : (0 : ℝ) < n + D.m := by linarith
  have hlt : (volume D.Q.toSet)⁻¹ < ENNReal.ofReal ((n + D.m) / (D.ε * D.Q.vol)) := by
    rw [D.Q.volume_toSet, ← ENNReal.ofReal_inv_of_pos hV,
      ENNReal.ofReal_lt_ofReal_iff (div_pos hnm0 (mul_pos hε hV)), inv_eq_one_div,
      div_lt_div_iff₀ hV (mul_pos hε hV), one_mul]
    exact mul_lt_mul_of_pos_right (by linarith) hV
  rcases prop_of_mem_maximal_sep h with ⟨j, hj, hle⟩ | ⟨i, hi0, hle⟩
  · have hjpos : 0 < lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j) :=
      lt_of_le_of_ne (lpNorm_nonneg _ _) (Ne.symm (Finset.prod_ne_zero_iff.mp D.Fpos.ne' j hj))
    exact D.not_le_of_inv_vol_lt hlt (D.lintegral_ne_zero_of_pos hjpos) (D.lintegral_ne_top j) hle
  · exact D.not_le_of_inv_vol_lt hlt hi0
      (TestFun.setLIntegral_enorm_rpow_ne_top _ (D.aux_pos i) _) hle

/-- `Q ∉ 𝐏₂`: the condition (2.4) fails at `Q` since `ε < 1`. [PROVED] -/
theorem Q_notMem_P2 : D.Q ∉ D.P2 := by
  intro h
  have hle := prop_of_mem_maximal_sep h
  have hε := D.ε_pos
  have hεle := D.ε_le
  have hV := D.Q.vol_pos
  have hlt : (volume D.Q.toSet)⁻¹ < ENNReal.ofReal (1 / (D.ε * D.Q.vol)) := by
    rw [D.Q.volume_toSet, ← ENNReal.ofReal_inv_of_pos hV,
      ENNReal.ofReal_lt_ofReal_iff (div_pos one_pos (mul_pos hε hV)), inv_eq_one_div,
      div_lt_div_iff₀ hV (mul_pos hε hV), one_mul, one_mul]
    have := mul_lt_mul_of_pos_right (show D.ε < 1 by linarith) hV
    linarith
  exact D.not_le_of_inv_vol_lt hlt (D.lintegral_ne_zero_of_pos (j := D.b) D.lpNorm_u_pos)
    (D.lintegral_ne_top D.b) hle

/-- `Q ∉ 𝐏₃`: the conditions (2.5) at `Q` contradict the testing conditions for `u` and `w`, since
`ε⁻¹ > 1`. [PROVED] -/
theorem Q_notMem_P3 : D.Q ∉ D.P3 := by
  intro h
  have hε := D.ε_pos
  have hεinv : 1 < D.ε⁻¹ := (one_lt_inv₀ hε).mpr (by linarith [D.ε_le])
  have hQQ : ∀ s : ℝ, (D.Q.vol / D.Q.vol) ^ s = 1 := fun s => by
    rw [div_self D.Q.vol_pos.ne', Real.one_rpow]
  rcases prop_of_mem_maximal_sep h with ⟨ρ, hρ, -, hρr, hle⟩ | ⟨ρ, hρ, hρ0, hρq, hle⟩
  · have ht := D.testing ρ hρ
    change |slotForm D.T D.a D.g D.Q ρ| ≤ D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q *
      lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r at ht
    rw [hQQ, mul_one] at hle
    have hB : 0 < D.B := by linarith [D.hB]
    have hpos : 0 < D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r :=
      mul_pos (mul_pos (mul_pos hB D.Fpos') D.lpNorm_u_pos) hρr
    have := lt_mul_right hpos hεinv
    have e : D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹ *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r =
        D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r *
          D.ε⁻¹ := by ring
    linarith
  · have ht := D.w_test ρ hρ hρ0
    rw [hQQ, mul_one] at hle
    have hpos : 0 < D.K * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q := mul_pos D.hK hρq
    have := lt_mul_right hpos hεinv
    have e : D.K * D.ε⁻¹ * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q =
        D.K * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹ := by ring
    linarith

/-- `Q ∉ 𝐏₅`: the only dyadic cubes containing `Q` which are parents of cubes `P' ⊆ Q` are `Q` and
its parent, and `2 < 2^d/ε`. [PROVED] -/
theorem Q_notMem_P5 : D.Q ∉ D.P5 := by
  intro h
  obtain ⟨S, hcard, hS⟩ := prop_of_mem_maximal_sep h
  have hsub : S ⊆ {D.Q, D.Q.parent} := by
    intro R' hR'
    obtain ⟨⟨P', hP', rfl⟩, hQR⟩ := hS R' hR'
    have hP'Q : P'.toSet ⊆ D.Q.toSet := (mem_of_mem_maximal_sep hP').1
    by_cases hne : P' = D.Q
    · rw [hne]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · have heq : P'.parent = D.Q :=
        D.cube_eq_of_subset_of_subset (DyadicCube.parent_subset_of_ssubset D.hd hP'Q hne) hQR
      rw [heq]
      exact Finset.mem_insert_self _ _
  have h2 : (S.card : ℝ) ≤ 2 := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_le_two
  have hε := D.ε_pos
  have h8 : (8 : ℝ) ≤ 2 ^ d / D.ε := by
    rw [le_div_iff₀ hε]
    have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    linarith [D.ε_le]
  linarith

/-- **`Q` is admissible**: `Q` lies in no first stopping cube, since a stopping cube containing
`Q` would be `Q` itself, and `Q ∉ 𝐏₁ ∪ ⋯ ∪ 𝐏₅`. [PROVED] -/
theorem Q_notInStopping : D.NotInStopping D.Q := by
  intro S hS hQS
  have hSQ : S.toSet ⊆ D.Q.toSet := (D.stoppingCubes_subset_tree' hS).1
  have heq : S = D.Q := D.cube_eq_of_subset_of_subset hSQ hQS
  rw [heq] at hS
  rcases maximal_subset _ hS with (((h1 | h2) | h3) | h4) | h5
  · exact D.Q_notMem_P1 h1
  · exact D.Q_notMem_P2 h2
  · exact D.Q_notMem_P3 h3
  · exact D.Q_notMem_P4 h4
  · exact D.Q_notMem_P5 h5

/-- **`A' ≤ (C₃₉ + C₄₀)/ε`** (p. 47, p. 56): combining (2.39) and (2.40) at every admissible cube
gives `A' ≤ (1−ε) A' + C₃₉ + C₄₀` (at cubes with `F_R = 0` the form vanishes), and `A' < ∞` by
definition. [PROVED] -/
theorem A'_le_C (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) (hLC : D.LeafConst) :
    D.A' ≤ (D.C₃₉ + D.C₄₀ hrq) / D.ε := by
  have hε := D.ε_pos
  have hQ := D.abs_form2_le_of_FP_pos D.Q_mem_tree D.Q_notInStopping
    (by rw [D.FP_Q]; exact D.Fpos') hG hrq hLC
  have hc0 : 0 ≤ (1 - D.ε) * D.A' + D.C₃₉ + D.C₄₀ hrq :=
    le_of_mul_le_mul_right (by rw [zero_mul]; exact (abs_nonneg _).trans hQ) (D.E_pos D.Q)
  have hA : D.A' ≤ (1 - D.ε) * D.A' + D.C₃₉ + D.C₄₀ hrq := by
    refine D.A'_le hc0 fun R hR hRs => ?_
    by_cases hFR : 0 < D.FP R
    · exact D.abs_form2_le_of_FP_pos hR hRs hFR hG hrq hLC
    · have h0 : D.FP R = 0 := le_antisymm (not_lt.mp hFR) (D.FP_nonneg R)
      rw [form2, D.twoSlotForm_eq_zero_of_FP_eq_zero h0, abs_zero]
      exact mul_nonneg hc0 (D.E_pos R).le
  rw [le_div_iff₀ hε]
  linarith

/-- `ψ_Q = 𝔤`: the mean `[𝔤]_Q` vanishes, so the correction term of (2.23) at `R = Q` is zero.
[PROVED] -/
theorem psi_Q : D.psi D.Q = D.pruned := by
  have h0 : ∫ x, (D.pruned : (Fin d → ℝ) → ℝ) x = 0 := D.pruned_meanZero
  have h : avg D.Q D.pruned = 0 := by
    rw [avg, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => D.pruned_supported x hx),
      h0, zero_div]
  rw [psi_eq, cS, h, zero_div, zero_smul, sub_zero]

/-- `E_Q = F ‖g‖_q |Q|^{1/r}`. [PROVED] -/
theorem E_Q : D.E D.Q = D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) := by
  unfold E
  rw [mul_assoc, mul_comm D.Q.vol, ← Real.rpow_add_one D.Q.vol_pos.ne', sub_add_cancel]

/-- **The estimate (2.14) at `R = Q`** (p. 44): `|Λ_Q(h, 𝔤)| ≤ C ε⁻¹ F ‖g‖_q ‖h‖_r` for
`h = 𝟙_Q`, `‖h‖_r = |Q|^{1/r}`, with the explicit constant `C = C₃₉ + C₄₀`. This is (2.23) at the
admissible cube `Q` together with `A' ≤ C/ε`. [PROVED] -/
theorem estimate_2_14 (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) (hLC : D.LeafConst) :
    |D.form2 D.Q (TestFun.ind D.Q) D.pruned| ≤
      (D.C₃₉ + D.C₄₀ hrq) / D.ε *
        (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) := by
  have h23 := D.estimate_2_23 D.Q_mem_tree D.Q_notInStopping
  rw [D.psi_Q, D.E_Q] at h23
  refine h23.trans (mul_le_mul_of_nonneg_right (D.A'_le_C hG hrq hLC) ?_)
  have := lpNorm_nonneg (D.G : (Fin d → ℝ) → ℝ) D.q
  have := D.Fpos'
  have := D.Q.vol_pos
  positivity

end Closing

/-! ### The main estimate in the form `A ≤ A θ + C` (p. 43), at the level of the stopping data

Writing `g = (g − 𝔤) + 𝔤`, the estimates (2.13) and (2.14) give
`|Λ_Q(𝟙_Q, g)| ≤ (A (1−ε)^{1/r} + C₁₃ + (C₃₉ + C₄₀)/ε) F ‖g‖_q |Q|^{1/r}`: at the extremal pair
`(h, g) = (𝟙_Q, g)` the constant `A` of the estimate (2.1) for the data `σ'`, `𝐐_P` is replaced by
`A θ + C`, with `θ = (1−ε)^{1/r} < 1` and `C` depending only on `n`, `d`, `B`, `m` and the
exponents. This is the content of the main estimate of §2.2–2.8 as used in the best-constant
argument (`ContractionStep`); the passage from the hypotheses (1.5)–(1.9) for a testing family
to stopping data `D` (the choice of the extremal pair, of the chains `𝐐_P` and of the auxiliary
functions) is not formalised. -/

section Contraction

/-- The contraction factor `θ = (1−ε)^{1/r}` of p. 43. -/
noncomputable def θc : ℝ := (1 - D.ε) ^ (1 / D.r)

theorem θc_nonneg : 0 ≤ D.θc := Real.rpow_nonneg (by linarith [D.ε_le]) _

/-- `θ < 1`. [PROVED] -/
theorem θc_lt_one : D.θc < 1 :=
  Real.rpow_lt_one (by linarith [D.ε_le]) (by linarith [D.ε_pos]) (one_div_pos.mpr (by linarith
    [D.hr]))

theorem C₁₃_nonneg : 0 ≤ D.C₁₃ := by
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have := D.K₁_nonneg
  have := D.K₂_nonneg
  have := D.K₃_nonneg
  unfold C₁₃
  positivity

/-- **The constant `C` of the contraction `A ≤ A θ + C`**: `C = C₁₃ + (C₃₉ + C₄₀)/ε`. -/
noncomputable def Cstep (hrq : 1 / D.r + 1 / D.q ≤ 1) : ℝ := D.C₁₃ + (D.C₃₉ + D.C₄₀ hrq) / D.ε

theorem Cstep_nonneg (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) (hLC : D.LeafConst) :
    0 ≤ D.Cstep hrq :=
  add_nonneg D.C₁₃_nonneg (D.A'_nonneg.trans (D.A'_le_C hG hrq hLC))

/-- **The main estimate in the form `A ≤ A θ + C`** (p. 43) at the extremal pair `(𝟙_Q, g)`:
`|Λ_Q(𝟙_Q, g)| ≤ (A θ + C) F ‖g‖_q |Q|^{1/r}`, from `g = (g − 𝔤) + 𝔤`, (2.13) and (2.14), under
the hypotheses `GBound`, `1/r + 1/q ≤ 1` and `LeafConst`. [PROVED] -/
theorem contraction_estimate (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) (hLC : D.LeafConst) :
    |D.form2 D.Q (TestFun.ind D.Q) D.G| ≤
      (D.A * D.θc + D.Cstep hrq) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
        D.Q.vol ^ (1 / D.r) := by
  have h13 := D.estimate_2_13
  have h14 := D.estimate_2_14 hG hrq hLC
  have hsplit : D.form2 D.Q (TestFun.ind D.Q) D.G =
      D.form2 D.Q (TestFun.ind D.Q) (D.G - D.pruned) + D.form2 D.Q (TestFun.ind D.Q) D.pruned := by
    rw [← D.form2_add_right, sub_add_cancel]
  have e : (D.A * D.θc + D.Cstep hrq) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
      D.Q.vol ^ (1 / D.r) =
      (D.A * (1 - D.ε) ^ (1 / D.r) + D.C₁₃) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          D.Q.vol ^ (1 / D.r) +
        (D.C₃₉ + D.C₄₀ hrq) / D.ε *
          (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) := by
    unfold θc Cstep
    ring
  rw [hsplit, e]
  exact (abs_add_le _ _).trans (add_le_add h13 h14)

/-- The same bound in the shape of the estimate (2.1) for the data `σ'`, `𝐐_Q` (the field
`estimateA` at `P = Q`, `ρ = g`): the constant `A` is replaced by `A θ + C`. [PROVED] -/
theorem contraction_estimateA (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) (hLC : D.LeafConst) :
    |twoSlotForm D.T D.a D.b D.g D.Q (TestFun.ind D.Q) D.G| ≤
      (D.A * D.θc + D.Cstep hrq) * (∏ j ∈ (Finset.univ.erase D.a).erase D.b,
          lpNorm (TestFun.truncateₗ D.Q (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j)) *
        D.Q.vol ^ (1 / D.p.p D.a) * lpNorm (D.G : (Fin d → ℝ) → ℝ) (D.p.p D.b) := by
  have h := D.contraction_estimate hG hrq hLC
  have hFQ : (∏ j ∈ (Finset.univ.erase D.a).erase D.b,
      lpNorm (TestFun.truncateₗ D.Q (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j)) = D.F := D.FP_Q
  rw [hFQ]
  exact h.trans (le_of_eq (by ring))

end Contraction

/-! ### The leaf constancy (p. 51, p. 56) from the data

The paper assumes "without loss of generality" that all functions involved are constant on the
dyadic cubes of the finest scale `2^{-N} ℓ(Q)`. Here this is part of the data: the fields
`g_const`, `G_const`, `bP_const`, `vP_const` of `StoppingData` say that the frozen entries, the
extremal function `g` and the testing functions `b_{σ,𝐐_P,k+1}`, `b_{τ,𝐐_P,k}` are constant on the
leaves of `𝒟_N(Q)`. Since every cube of the tree is a union of leaves (a leaf is contained in or
disjoint from every cube of the tree), the pruned function `𝔤` is constant on the leaves, and so
are its mirror image `𝔥` for the second stopping time at an admissible cube `S` (whose leaves are
leaves of `𝒟_N(Q)`), `v_S`, `𝔤̂_S` and `u`. This derives the hypothesis `LeafConst` of the
telescoping (2.56) and removes it from (2.40), (2.14) and the contraction estimate. -/

section LeafConstancy

/-- A leaf of the tree is contained in or disjoint from every cube of the tree. [PROVED] -/
theorem leaf_subset_or_disjoint {T P : DyadicCube d} (hP : P ∈ D.tree)
    (hTm : T.m = D.Q.m - D.N) : T.toSet ⊆ P.toSet ∨ Disjoint T.toSet P.toSet :=
  DyadicCube.subset_or_disjoint T P (by rw [hTm]; exact hP.2)

/-- **`𝔤` is constant on the leaves of `𝒟_N(Q)`**: `𝔤` is a combination of `g`, `u` and the
`b_{σ,𝐐_P,k+1}`, truncated to cubes of the tree. [PROVED] -/
theorem pruned_constOn {T : DyadicCube d} (hTQ : T.toSet ⊆ D.Q.toSet)
    (hTm : T.m = D.Q.m - D.N) : ConstOn D.pruned T := by
  have hG := D.G_const T hTQ hTm
  have hu : ConstOn D.u T := D.g_const D.b T hTQ hTm
  have htr : ∀ P ∈ D.tree, ∀ f : TestFun d, ConstOn f T →
      ConstOn (TestFun.truncateₗ P f) T :=
    fun P hP f hf => constOn_truncateₗ (D.leaf_subset_or_disjoint hP hTm) hf
  have h1 : ConstOn ((∑ P ∈ D.PstOut4, TestFun.truncateₗ P D.G : TestFun d) :
      (Fin d → ℝ) → ℝ) T :=
    constOn_sum fun P hP => htr P (D.stoppingCubes_subset_tree' (D.mem_PstOut4.mp hP).1) _ hG
  have h2 : ConstOn ((∑ P ∈ D.PstOut4, D.coef P • TestFun.truncateₗ P D.u : TestFun d) :
      (Fin d → ℝ) → ℝ) T :=
    constOn_sum fun P hP =>
      constOn_smul _ (htr P (D.stoppingCubes_subset_tree' (D.mem_PstOut4.mp hP).1) _ hu)
  have h3 : ConstOn ((∑ P ∈ D.PstIn4, TestFun.truncateₗ P D.G : TestFun d) :
      (Fin d → ℝ) → ℝ) T :=
    constOn_sum fun P hP => htr P (D.stoppingCubes_subset_tree' (D.mem_PstIn4.mp hP).1) _ hG
  have h4 : ConstOn ((∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u : TestFun d) :
      (Fin d → ℝ) → ℝ) T :=
    constOn_sum fun P hP => constOn_smul _ (htr P (D.Pbar4_mem_tree hP) _ hu)
  have h5 : ConstOn ((∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u : TestFun d) :
      (Fin d → ℝ) → ℝ) T :=
    constOn_sum fun P hP => constOn_smul _ (htr P (D.Psib4_mem_tree hP) _ hu)
  unfold pruned
  exact constOn_sub (constOn_add (constOn_sub (constOn_add (constOn_sub
    (constOn_sub hG (constOn_smul _ hu)) h1) h2) h3) h4) h5

/-- **The leaf constancy `LeafConst` holds**: at an admissible cube `S` with `F_S > 0`, the leaves
of the second stopping time are leaves of `𝒟_N(Q)`, on which `𝔥` (the pruned function of the
mirrored data), `v_S`, `𝔤̂_S = (𝔤 − c u) 𝟙_S` and `u` are constant. [PROVED] -/
theorem leafConst : D.LeafConst := by
  intro S hS hSs hFS T hT
  have hTS : T.toSet ⊆ S.toSet := subset_of_mem_level hT
  have hTQ : T.toSet ⊆ D.Q.toSet := hTS.trans hS.1
  have hTm : T.m = D.Q.m - D.N := D.m_of_mem_leaf hS hSs hFS hT
  have hTm' : T.m = S.m - (D.second S hS hSs hFS).N := m_of_mem_level hT
  have hu : ConstOn D.u T := D.g_const D.b T hTQ hTm
  refine ⟨⟨?_, D.vP_const S hS.1 hS.2 T hTQ hTm⟩, ?_, hu⟩
  · change ConstOn ((D.second S hS hSs hFS).pruned : (Fin d → ℝ) → ℝ) T
    exact (D.second S hS hSs hFS).pruned_constOn hTS hTm'
  · unfold ghat
    exact constOn_truncateₗ (Or.inl hTS) (constOn_sub (D.pruned_constOn hTQ hTm) (constOn_smul _
      hu))

/-- **(2.40) without the constancy hypothesis**. [PROVED] -/
theorem estimate_2_40' {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) :
    |twoSlotForm D.T D.a D.b D.g R (D.prunedH hR hRs hFR) (D.ghat R)| ≤ D.C₄₀ hrq * D.E R := by
  rw [← D.C₄₀_eq hR hRs hFR hrq]
  exact D.estimate_2_40 hR hRs hFR hG hrq (D.leafConst R hR hRs hFR)

/-- **`A' ≤ (C₃₉ + C₄₀)/ε` without the constancy hypothesis**. [PROVED] -/
theorem A'_le_C' (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) :
    D.A' ≤ (D.C₃₉ + D.C₄₀ hrq) / D.ε :=
  D.A'_le_C hG hrq D.leafConst

/-- **The estimate (2.14) without the constancy hypothesis**. [PROVED] -/
theorem estimate_2_14' (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) :
    |D.form2 D.Q (TestFun.ind D.Q) D.pruned| ≤
      (D.C₃₉ + D.C₄₀ hrq) / D.ε *
        (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) :=
  D.estimate_2_14 hG hrq D.leafConst

/-- **The contraction `A ≤ A θ + C` without the constancy hypothesis**: under `GBound` and
`1/r + 1/q ≤ 1` alone, `|Λ_Q(𝟙_Q, g)| ≤ (A θ + C) F ‖g‖_q |Q|^{1/r}`. [PROVED] -/
theorem contraction_estimate' (hG : D.GBound) (hrq : 1 / D.r + 1 / D.q ≤ 1) :
    |D.form2 D.Q (TestFun.ind D.Q) D.G| ≤
      (D.A * D.θc + D.Cstep hrq) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
        D.Q.vol ^ (1 / D.r) :=
  D.contraction_estimate hG hrq D.leafConst

end LeafConstancy

end StoppingData

end ThetaBound

/-! ## The bridge from the hypotheses of Theorem 1.4 to the stopping data (p. 40–41, 43–44)

An instance of the testing condition (2.1) for the restricted family consists of an admissible
path `σ₀` of length `k+1` (the paper's `σ'`), a `σ₀`-nested tuple `𝐐`, a dyadic test function `g`
supported on `Q := Q_{σ₀(k)}` (the paper's extremal function) and the constant `A`. Choosing an
admissible extension `σ` of `σ₀` (the paper's `σ`, with `σ(k) = k+1`, `σ(k+1) = k` after
relabelling)
and its swap `τ = σ.swapLast`, the stopping data of §2.2 are: the slot `b = σ₀(k)` of `g`, the slot
`a = σ(k+1)` of `h = 𝟙_Q`, the frozen entries `g_j = f_j 𝟙_Q` (the truncated restricted testing
functions at the head positions `σ₀(l)`, `l < k`, the testing function `u = b_{σ,𝐐,σ(k)}` in the
slot `b`, and `𝟙_Q` elsewhere), and for every `P ⊆ Q` the chain `𝐐_P` (p. 43: `𝐐` at the head
positions, `P` elsewhere) with the testing functions `b_{σ,𝐐_P,k+1}` and `b_{τ,𝐐_P,k}`. The
hypotheses (1.5)–(1.8), the testing conditions (1.9) for `σ, 𝐐_P` and `τ, 𝐐_P` and the estimate
(2.1) for `σ₀, 𝐐_P` give the fields of `StoppingData`; the interdependence condition (1.8) shows
that the testing functions on `𝐐_P` at the head positions agree with those on `𝐐`. The paper's
standing assumption that all functions are constant on the finest scale is the hypothesis
`Resolution` (the family has resolution `2^{-N} ℓ(Q)` on the chains ending inside `Q`), together
with the same for `g`. The extremal function `g` is put among the auxiliary functions of `𝐏₁`, so
that (2.8) holds for it (`GBound`). -/

section Bridge


variable {n k : ℕ}

namespace Bridge

/-- The head positions of a path `σ₀` of length `k+1`: the values `σ₀(l)`, `l < k`. -/
def IsHead (σ₀ : IPath n (k + 1)) (s : Fin n) : Prop := ∃ l : Fin k, σ₀ l.castSucc = s

theorem isHead_castSucc (σ₀ : IPath n (k + 1)) (l : Fin k) : IsHead σ₀ (σ₀ l.castSucc) := ⟨l, rfl⟩

theorem not_isHead_last (σ₀ : IPath n (k + 1)) : ¬ IsHead σ₀ (σ₀ (Fin.last k)) := by
  rintro ⟨l, hl⟩
  exact (Fin.castSucc_lt_last l).ne (σ₀.injective hl)

theorem mem_range_of_isHead {σ₀ : IPath n (k + 1)} {s : Fin n} (h : IsHead σ₀ s) :
    s ∈ Set.range σ₀ := by
  obtain ⟨l, rfl⟩ := h
  exact ⟨_, rfl⟩

theorem not_mem_range_of {σ₀ : IPath n (k + 1)} {s : Fin n} (hh : ¬ IsHead σ₀ s)
    (hs : s ≠ σ₀ (Fin.last k)) : s ∉ Set.range σ₀ := by
  rintro ⟨i, rfl⟩
  induction i using Fin.lastCases with
  | last => exact hs rfl
  | cast l => exact hh ⟨l, rfl⟩

open Classical in
/-- The chain `𝐐_P` (p. 43): `𝐐` at the head positions of `σ₀`, `P` elsewhere. -/
noncomputable def chain (σ₀ : IPath n (k + 1)) (Q : Fin n → DyadicCube d) (P : DyadicCube d) :
    Fin n → DyadicCube d :=
  fun s => if IsHead σ₀ s then Q s else P

theorem chain_of_isHead {σ₀ : IPath n (k + 1)} {Q : Fin n → DyadicCube d} {P : DyadicCube d}
    {s : Fin n} (h : IsHead σ₀ s) : chain σ₀ Q P s = Q s := by
  simp only [chain, h, ↓reduceIte]

theorem chain_of_not_isHead {σ₀ : IPath n (k + 1)} {Q : Fin n → DyadicCube d} {P : DyadicCube d}
    {s : Fin n} (h : ¬ IsHead σ₀ s) : chain σ₀ Q P s = P := by
  simp only [chain, h, ↓reduceIte]

theorem chain_castSucc (σ₀ : IPath n (k + 1)) (Q : Fin n → DyadicCube d) (P : DyadicCube d)
    (l : Fin k) : chain σ₀ Q P (σ₀ l.castSucc) = Q (σ₀ l.castSucc) :=
  chain_of_isHead (isHead_castSucc σ₀ l)

theorem chain_last (σ₀ : IPath n (k + 1)) (Q : Fin n → DyadicCube d) (P : DyadicCube d) :
    chain σ₀ Q P (σ₀ (Fin.last k)) = P :=
  chain_of_not_isHead (not_isHead_last σ₀)

/-- A path `τ` of length `k+2` agrees with `σ₀` at the head positions. -/
def HeadsAgree (σ₀ : IPath n (k + 1)) (τ : IPath n (k + 2)) : Prop :=
  ∀ l : Fin k, τ l.castSucc.castSucc = σ₀ l.castSucc

theorem headsAgree_of_restrict {σ₀ : IPath n (k + 1)} {τ : IPath n (k + 2)}
    (h : τ.restrict = σ₀) : HeadsAgree σ₀ τ := fun l => by
  rw [← h]
  rfl

theorem swapLast_castSucc_castSucc (τ : IPath n (k + 2)) (l : Fin k) :
    τ.swapLast l.castSucc.castSucc = τ l.castSucc.castSucc := by
  change τ (Equiv.swap (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) l.castSucc.castSucc) = _
  rw [Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last _).ne
    (fun h => (Fin.castSucc_lt_last l).ne (Fin.castSucc_injective _ h))]

theorem HeadsAgree.swapLast {σ₀ : IPath n (k + 1)} {τ : IPath n (k + 2)} (h : HeadsAgree σ₀ τ) :
    HeadsAgree σ₀ τ.swapLast := fun l => by
  rw [swapLast_castSucc_castSucc]
  exact h l

theorem HeadsAgree.not_isHead_castSucc_last {σ₀ : IPath n (k + 1)} {τ : IPath n (k + 2)}
    (h : HeadsAgree σ₀ τ) : ¬ IsHead σ₀ (τ (Fin.castSucc (Fin.last k))) := by
  rintro ⟨l, hl⟩
  rw [← h l] at hl
  exact (Fin.castSucc_lt_last l).ne (Fin.castSucc_injective _ (τ.injective hl))

theorem HeadsAgree.not_isHead_last {σ₀ : IPath n (k + 1)} {τ : IPath n (k + 2)}
    (h : HeadsAgree σ₀ τ) : ¬ IsHead σ₀ (τ (Fin.last (k + 1))) := by
  rintro ⟨l, hl⟩
  rw [← h l] at hl
  exact (Fin.castSucc_lt_last _).ne (τ.injective hl)

theorem HeadsAgree.chain_castSucc_last {σ₀ : IPath n (k + 1)} {τ : IPath n (k + 2)}
    (h : HeadsAgree σ₀ τ) (Q : Fin n → DyadicCube d) (P : DyadicCube d) :
    chain σ₀ Q P (τ (Fin.castSucc (Fin.last k))) = P :=
  chain_of_not_isHead h.not_isHead_castSucc_last

theorem HeadsAgree.chain_last {σ₀ : IPath n (k + 1)} {τ : IPath n (k + 2)}
    (h : HeadsAgree σ₀ τ) (Q : Fin n → DyadicCube d) (P : DyadicCube d) :
    chain σ₀ Q P (τ (Fin.last (k + 1))) = P :=
  chain_of_not_isHead h.not_isHead_last

/-- **The chain `𝐐_P` is `σ₀`-nested** when `𝐐` is and `P ⊆ Q_{σ₀(k)}` (`σ₀` has an extension, so
`k + 1 < n` and the top condition is vacuous). [PROVED] -/
theorem nested_chain (hk : k + 1 < n) {σ₀ : IPath n (k + 1)} {Q : Fin n → DyadicCube d}
    (hQ : IPath.Nested σ₀ Q) {P : DyadicCube d} (hP : P.toSet ⊆ (Q (σ₀ (Fin.last k))).toSet) :
    IPath.Nested σ₀ (chain σ₀ Q P) := by
  refine ⟨?_, ?_, fun h => absurd h hk.ne⟩
  · intro i j hij
    induction j using Fin.lastCases with
    | last =>
      rw [chain_last]
      induction i using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast i =>
        rw [chain_castSucc]
        exact hP.trans (hQ.mono _ _ (Fin.castSucc_lt_last i))
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
      | cast i =>
        rw [chain_castSucc, chain_castSucc]
        exact hQ.mono _ _ hij
  · intro s hs
    rw [chain_last, chain_of_not_isHead]
    exact fun h => hs (mem_range_of_isHead h)

/-- **The chain `𝐐_P` is `τ`-nested** for every path `τ` of length `k+2` agreeing with `σ₀` at the
head positions (the extension `σ` and its swap `τ`). [PROVED] -/
theorem nested_chain_of_headsAgree {σ₀ : IPath n (k + 1)} {τ : IPath n (k + 2)}
    (hτ : HeadsAgree σ₀ τ) {Q : Fin n → DyadicCube d} (hQ : IPath.Nested σ₀ Q) {P : DyadicCube d}
    (hP : P.toSet ⊆ (Q (σ₀ (Fin.last k))).toSet) : IPath.Nested τ (chain σ₀ Q P) := by
  have hhead : ∀ l : Fin k, P.toSet ⊆ (chain σ₀ Q P (τ l.castSucc.castSucc)).toSet := fun l => by
    rw [hτ l, chain_castSucc]
    exact hP.trans (hQ.mono _ _ (Fin.castSucc_lt_last l))
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    induction j using Fin.lastCases with
    | last =>
      rw [hτ.chain_last]
      induction i using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast i =>
        induction i using Fin.lastCases with
        | last => exact (congrArg DyadicCube.toSet (hτ.chain_castSucc_last Q P)).symm.le
        | cast i => exact hhead i
    | cast j =>
      induction j using Fin.lastCases with
      | last =>
        rw [hτ.chain_castSucc_last]
        induction i using Fin.lastCases with
        | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
        | cast i =>
          induction i using Fin.lastCases with
          | last => exact absurd hij (lt_irrefl _)
          | cast i => exact hhead i
      | cast j =>
        induction i using Fin.lastCases with
        | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
        | cast i =>
          induction i using Fin.lastCases with
          | last =>
            exact absurd hij (not_lt.mpr (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _)))
          | cast i =>
            rw [hτ i, hτ j, chain_castSucc, chain_castSucc]
            exact hQ.mono _ _
              (Fin.castSucc_lt_castSucc_iff.mp (Fin.castSucc_lt_castSucc_iff.mp hij))
  · intro s hs
    rw [hτ.chain_last, chain_of_not_isHead]
    rintro ⟨l, hl⟩
    exact hs ⟨l.castSucc.castSucc, (hτ l).trans hl⟩
  · intro _ _
    have e : (⟨k + 1 - 1, by omega⟩ : Fin (k + 2)) = Fin.castSucc (Fin.last k) := by
      ext
      simp
    rw [e, hτ.chain_castSucc_last, hτ.chain_last]

variable {T : PerfectCZForm d n} {p : HolderTuple n} {C : IPath.Collection n}
  {b : TestingFamily d n (k + 1)} {B : ℝ}

/-- **Interdependence on the chains** (1.8): for two paths `τ, τ'` of length `k+2` agreeing with
`σ₀` at the heads, the testing functions of `τ, 𝐐_P` at the head positions are those of `τ', 𝐐`.
[PROVED] -/
theorem b_chain_eq (hb : LocalTbHypotheses T p C b B) {σ₀ : IPath n (k + 1)}
    {τ τ' : IPath n (k + 2)} (hτ : τ ∈ C (k + 2)) (hτ' : τ' ∈ C (k + 2)) (hh : HeadsAgree σ₀ τ)
    (hh' : HeadsAgree σ₀ τ') {Q : Fin n → DyadicCube d} (hQ : IPath.Nested σ₀ Q)
    (hQτ' : IPath.Nested τ' Q) {P : DyadicCube d} (hP : P.toSet ⊆ (Q (σ₀ (Fin.last k))).toSet)
    (l : Fin k) : b τ (chain σ₀ Q P) l.castSucc = b τ' Q l.castSucc := by
  apply hb.interdep τ hτ τ' hτ' _ Q (nested_chain_of_headsAgree hh hQ hP) hQτ' l.castSucc
  intro l' hl'
  obtain ⟨l'', rfl⟩ := Fin.exists_castSucc_eq.mpr
    (ne_of_lt (lt_of_le_of_lt hl' (Fin.castSucc_lt_last l)))
  rw [hh l'', hh' l'', chain_castSucc]
  exact ⟨rfl, rfl⟩

/-- The restricted family at `σ₀` is given by any admissible extension `σ` (interdependence).
[PROVED] -/
theorem restrictFamily_eq_of_ext (hC : IPath.Admissible C) (hk : k + 1 < n)
    (hb : LocalTbHypotheses T p C b B) {σ₀ : IPath n (k + 1)} (hσ₀ : σ₀ ∈ C (k + 1))
    {σ : IPath n (k + 2)} (hσ : σ ∈ C (k + 2)) (hσσ₀ : σ.restrict = σ₀) {Q : Fin n → DyadicCube d}
    (hQ : IPath.Nested σ₀ Q) (l : Fin k) : restrictFamily C b σ₀ Q l = b σ Q l.castSucc := by
  obtain ⟨τ, hτ, hτσ₀, e⟩ := restrictFamily_eq hC hk b hσ₀ Q l
  rw [e]
  apply hb.interdep τ hτ σ hσ Q Q (hQ.of_restrict hτσ₀) (hQ.of_restrict hσσ₀) l.castSucc
  intro l' hl'
  obtain ⟨l'', rfl⟩ := Fin.exists_castSucc_eq.mpr
    (ne_of_lt (lt_of_le_of_lt hl' (Fin.castSucc_lt_last l)))
  rw [headsAgree_of_restrict hτσ₀ l'', headsAgree_of_restrict hσσ₀ l'']
  exact ⟨rfl, rfl⟩

/-- `∏_j ‖f_j‖_{p_j}` for a tuple with the entry `a` replaced. [PROVED] -/
theorem prodNorm_update (p : HolderTuple n) (g : Fin n → TestFun d) (a : Fin n) (x : TestFun d) :
    prodNorm p (Function.update g a x) =
      lpNorm (x : (Fin d → ℝ) → ℝ) (p.p a) *
        ∏ j ∈ Finset.univ.erase a, lpNorm (g j : (Fin d → ℝ) → ℝ) (p.p j) := by
  have e : ∏ j ∈ Finset.univ.erase a,
      lpNorm ((Function.update g a x j : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j) =
      ∏ j ∈ Finset.univ.erase a, lpNorm (g j : (Fin d → ℝ) → ℝ) (p.p j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  unfold prodNorm
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => lpNorm ((Function.update g a x j : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j))
    (Finset.mem_univ a), Function.update_self, e]

/-- `∏_j ‖f_j‖_{p_j}` for a tuple with the entries `a ≠ b` replaced. [PROVED] -/
theorem prodNorm_update_update (p : HolderTuple n) (g : Fin n → TestFun d) {a b : Fin n}
    (hab : a ≠ b) (x y : TestFun d) :
    prodNorm p (Function.update (Function.update g a x) b y) =
      lpNorm (x : (Fin d → ℝ) → ℝ) (p.p a) * lpNorm (y : (Fin d → ℝ) → ℝ) (p.p b) *
        ∏ j ∈ (Finset.univ.erase a).erase b, lpNorm (g j : (Fin d → ℝ) → ℝ) (p.p j) := by
  have e : ∏ j ∈ (Finset.univ.erase a).erase b,
      lpNorm ((Function.update g b y j : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j) =
      ∏ j ∈ (Finset.univ.erase a).erase b, lpNorm (g j : (Fin d → ℝ) → ℝ) (p.p j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Function.update_comm hab, prodNorm_update,
    ← Finset.mul_prod_erase (Finset.univ.erase a)
      (fun j => lpNorm ((Function.update g b y j : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j))
      (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
    Function.update_self, e]
  ring

/-! ### The resolution of the form and the coarsening of the testing functions

The kernel of `Λ` is a dyadic test function on `ℝ^{dn}` (condition (iii)), a finite combination
of indicators of products `P_1 × ⋯ × P_n` of cubes of a common scale. Below the smallest of these
scales `s` the form sees an entry only through its means: for `φ` supported on a cube `L` of scale
`≤ s`, `Λ(…, φ, …) = [φ]_L Λ(…, 𝟙_L, …)` (`KernelScale`, `exists_kernelScale`). Consequently the
testing functions `b_{σ,𝐐_P,k+1}`, `b_{τ,𝐐_P,k}` of the chains may be replaced by their
coarsenings `E_N b = ∑_{L ∈ 𝒟_N(P)} [b]_L 𝟙_L` at the leaf scale of the tree `𝒟_N(Q)`, provided
this scale is at most `s`: the form values are unchanged (`form_update_coarsen`), the support
and mean conditions are preserved (`coarsen_supportedOn`, `coarsen_integral`), the norm
condition improves (`coarsen_norm_le`, Jensen), and the testing conditions hold with the constant
`B²`, since `‖b‖_q ≤ (B|P|)^{1/q} ≤ B |P|^{1/q} ≤ B ‖E_N b‖_q` by the mean condition and Hölder's
inequality. This is the paper's "appropriate limiting process as `N → ∞`" (p. 51), and removes
the finite-resolution hypothesis from the contraction step. -/

/-- `∫ 𝟙_{∏ P_j}(x) ∏_j f_j(x_j) dx = ∏_j ∫ 𝟙_{P_j} f_j`. [PROVED] -/
theorem prodSet_integral_eq (P : Fin n → DyadicCube d) (f : Fin n → TestFun d) :
    ∫ x, (DyadicCube.prodSet P).indicator 1 x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j) =
      ∏ j, ∫ x, (P j).toSet.indicator (f j : (Fin d → ℝ) → ℝ) x := by
  have hfun : (fun x : Fin n → Fin d → ℝ =>
      (DyadicCube.prodSet P).indicator 1 x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) =
      fun x => ∏ j, (P j).toSet.indicator (f j : (Fin d → ℝ) → ℝ) (x j) := by
    funext x
    by_cases hx : x ∈ DyadicCube.prodSet P
    · rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
      exact Finset.prod_congr rfl fun j _ =>
        (Set.indicator_of_mem ((show ∀ j, x j ∈ (P j).toSet from hx) j) _).symm
    · rw [Set.indicator_of_notMem hx, zero_mul]
      have hx' : ¬ ∀ j, x j ∈ (P j).toSet := fun h => hx h
      obtain ⟨j, hj⟩ := not_forall.mp hx'
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm
  rw [hfun, volume_pi,
    integral_fintype_prod_eq_prod (fun j => (P j).toSet.indicator (f j : (Fin d → ℝ) → ℝ))]

/-- `∫ 𝟙_P φ = [φ]_L ∫ 𝟙_P 𝟙_L` for `φ` supported on a cube `L` of scale at most that of `P`.
[PROVED] -/
theorem integral_indicator_eq_avg_mul {L P : DyadicCube d} (hLP : L.m ≤ P.m) {φ : TestFun d}
    (hφ : SupportedOn (φ : (Fin d → ℝ) → ℝ) L) :
    ∫ x, P.toSet.indicator (φ : (Fin d → ℝ) → ℝ) x =
      avg L φ * ∫ x, P.toSet.indicator ((TestFun.ind L : TestFun d) : (Fin d → ℝ) → ℝ) x := by
  rcases DyadicCube.subset_or_disjoint L P hLP with h | h
  · have e1 : P.toSet.indicator (φ : (Fin d → ℝ) → ℝ) = φ := by
      funext x
      by_cases hx : x ∈ P.toSet
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hφ x (fun hxL => hx (h hxL))]
    have e2 : P.toSet.indicator ((TestFun.ind L : TestFun d) : (Fin d → ℝ) → ℝ) =
        (TestFun.ind L : TestFun d) := by
      funext x
      by_cases hx : x ∈ P.toSet
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, TestFun.coe_ind,
          Set.indicator_of_notMem (fun hxL => hx (h hxL))]
    rw [e1, e2, TestFun.integral_ind, avg_mul_vol,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hφ x hx]
  · have e1 : P.toSet.indicator (φ : (Fin d → ℝ) → ℝ) = 0 := by
      funext x
      by_cases hx : x ∈ P.toSet
      · rw [Set.indicator_of_mem hx, hφ x (Set.disjoint_right.mp h hx), Pi.zero_apply]
      · rw [Set.indicator_of_notMem hx, Pi.zero_apply]
    have e2 : P.toSet.indicator ((TestFun.ind L : TestFun d) : (Fin d → ℝ) → ℝ) = 0 := by
      funext x
      by_cases hx : x ∈ P.toSet
      · rw [Set.indicator_of_mem hx, TestFun.coe_ind,
          Set.indicator_of_notMem (Set.disjoint_right.mp h hx), Pi.zero_apply]
      · rw [Set.indicator_of_notMem hx, Pi.zero_apply]
    rw [e1, e2]
    simp

/-- The form has resolution `s`: in every slot, an entry supported on a cube `L` of scale `≤ s`
enters only through its mean, `Λ(…, φ, …) = [φ]_L Λ(…, 𝟙_L, …)`. -/
def KernelScale (T : PerfectCZForm d n) (s : ℤ) : Prop :=
  ∀ (f : Fin n → TestFun d) (j : Fin n) (L : DyadicCube d), L.m ≤ s →
    ∀ φ : TestFun d, SupportedOn (φ : (Fin d → ℝ) → ℝ) L →
      T.form (Function.update f j φ) = avg L φ * T.form (Function.update f j (TestFun.ind L))

/-- The generators of the kernel space of scale at least `s`. -/
def kernelGens (d n : ℕ) (s : ℤ) : Set ((Fin n → Fin d → ℝ) → ℝ) :=
  {K | ∃ P : Fin n → DyadicCube d, (∀ i j, (P i).m = (P j).m) ∧ (∀ j, s ≤ (P j).m) ∧
    K = (DyadicCube.prodSet P).indicator 1}

theorem kernelGens_subset (s : ℤ) : kernelGens d n s ⊆ {K | ∃ P : Fin n → DyadicCube d,
    (∀ i j, (P i).m = (P j).m) ∧ K = (DyadicCube.prodSet P).indicator 1} :=
  fun _ ⟨P, h1, _, h3⟩ => ⟨P, h1, h3⟩

/-- **Every perfect Calderón–Zygmund form has a resolution**: the kernel is a finite combination
of product-cube indicators, and below their smallest scale the form only sees means. [PROVED] -/
theorem exists_kernelScale (T : PerfectCZForm d n) (p : HolderTuple n) :
    ∃ s : ℤ, KernelScale T s := by
  obtain ⟨K, hK, hform⟩ := T.truncation
  obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hK
  choose P hP using fun t => (show ∃ P : Fin n → DyadicCube d, (∀ i j, (P i).m = (P j).m) ∧
    ((g t : (Fin n → Fin d → ℝ) → ℝ) = (DyadicCube.prodSet P).indicator 1) from (g t).2)
  set s : ℤ := -(∑ t, ∑ j, |(P t j).m|) with hs_def
  have hs : ∀ t j, s ≤ (P t j).m := by
    intro t j
    have h1 : |(P t j).m| ≤ ∑ j, |(P t j).m| :=
      Finset.single_le_sum (f := fun j => |(P t j).m|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, |(P t j).m| ≤ ∑ t, ∑ j, |(P t j).m| :=
      Finset.single_le_sum (f := fun t => ∑ j, |(P t j).m|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ t)
    linarith [neg_abs_le (P t j).m]
  -- `K` lies in the span of the generators of scale `≥ s`
  have hKs : K ∈ Submodule.span ℝ (kernelGens d n s) := by
    rw [← hsum]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨P t, (hP t).1, hs t, (hP t).2⟩
  have hint : ∀ K' ∈ Submodule.span ℝ (kernelGens d n s), ∀ f : Fin n → TestFun d,
      Integrable (fun x => K' x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) volume := by
    intro K' hK' f
    have : K' ∈ TestFunProd d n := Submodule.span_mono (kernelGens_subset s) hK'
    exact ((TestFunProd.exists_bound p this).choose_spec.2 f).1
  refine ⟨s, fun f j L hL φ hφ => ?_⟩
  rw [hform, hform]
  clear hK hsum hform
  -- induction over the span
  induction hKs using Submodule.span_induction with
  | mem K' hK' =>
    obtain ⟨P', -, hP's, rfl⟩ := hK'
    rw [prodSet_integral_eq, prodSet_integral_eq]
    have e : ∀ ψ : TestFun d,
        ∏ i, ∫ x, (P' i).toSet.indicator ((Function.update f j ψ i : TestFun d) : (Fin d → ℝ) → ℝ) x
          =
          (∫ x, (P' j).toSet.indicator (ψ : (Fin d → ℝ) → ℝ) x) *
            ∏ i ∈ Finset.univ \ {j}, ∫ x, (P' i).toSet.indicator (f i : (Fin d → ℝ) → ℝ) x := by
      intro ψ
      calc ∏ i, ∫ x, (P' i).toSet.indicator ((Function.update f j ψ i : TestFun d) :
              (Fin d → ℝ) → ℝ) x
          = ∏ i, Function.update
              (fun i => ∫ x, (P' i).toSet.indicator ((f i : TestFun d) : (Fin d → ℝ) → ℝ) x) j
              (∫ x, (P' j).toSet.indicator (ψ : (Fin d → ℝ) → ℝ) x) i :=
            Finset.prod_congr rfl fun i _ => Function.apply_update
              (fun i (F : TestFun d) => ∫ x, (P' i).toSet.indicator (F : (Fin d → ℝ) → ℝ) x) f j ψ i
        _ = _ := Finset.prod_update_of_mem (Finset.mem_univ j) _ _
    rw [e, e, integral_indicator_eq_avg_mul (hL.trans (hP's j)) hφ]
    ring
  | zero => simp
  | add K₁ K₂ hK₁ hK₂ h₁ h₂ =>
    have e : ∀ F : Fin n → TestFun d, (fun x => (K₁ + K₂) x * ∏ i, (F i : (Fin d → ℝ) → ℝ) (x i)) =
        fun x => K₁ x * ∏ i, (F i : (Fin d → ℝ) → ℝ) (x i) +
          K₂ x * ∏ i, (F i : (Fin d → ℝ) → ℝ) (x i) := by
      intro F
      funext x
      rw [Pi.add_apply, add_mul]
    rw [e, e, integral_add (hint K₁ hK₁ _) (hint K₂ hK₂ _),
      integral_add (hint K₁ hK₁ _) (hint K₂ hK₂ _), h₁, h₂]
    ring
  | smul a K' hK' h =>
    have e : ∀ F : Fin n → TestFun d, (fun x => (a • K') x * ∏ i, (F i : (Fin d → ℝ) → ℝ) (x i)) =
        fun x => a * (K' x * ∏ i, (F i : (Fin d → ℝ) → ℝ) (x i)) := by
      intro F
      funext x
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [e, e, integral_const_mul, integral_const_mul, h]
    ring

/-- The coarsening `E_N f = ∑_{L ∈ 𝒟_N(P)} [f]_L 𝟙_L` of `f` at depth `N` below `P`. -/
noncomputable def coarsen (P : DyadicCube d) (N : ℕ) (f : TestFun d) : TestFun d :=
  ∑ L ∈ StoppingData.level N P, avg L (f : (Fin d → ℝ) → ℝ) • TestFun.ind L

theorem coarsen_apply (P : DyadicCube d) (N : ℕ) (f : TestFun d) (x : Fin d → ℝ) :
    (coarsen P N f : (Fin d → ℝ) → ℝ) x = ∑ L ∈ StoppingData.level N P,
      avg L (f : (Fin d → ℝ) → ℝ) * L.toSet.indicator (1 : (Fin d → ℝ) → ℝ) x := by
  simp only [coarsen, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, TestFun.coe_ind]

theorem coarsen_supportedOn (P : DyadicCube d) (N : ℕ) (f : TestFun d) :
    SupportedOn (coarsen P N f : (Fin d → ℝ) → ℝ) P := by
  intro x hx
  rw [coarsen_apply]
  exact Finset.sum_eq_zero fun L hL => by
    rw [Set.indicator_of_notMem (fun h => hx (StoppingData.subset_of_mem_level hL h)), mul_zero]

/-- The coarsening is constant on every cube of scale at most the leaf scale. [PROVED] -/
theorem coarsen_constOn (P : DyadicCube d) (N : ℕ) (f : TestFun d) {T : DyadicCube d}
    (hT : T.m ≤ P.m - N) : ConstOn (coarsen P N f : (Fin d → ℝ) → ℝ) T := by
  unfold coarsen
  refine StoppingData.constOn_sum fun L hL => StoppingData.constOn_smul _ (constOn_ind ?_)
  exact DyadicCube.subset_or_disjoint T L (by rw [StoppingData.m_of_mem_level hL]; exact hT)

/-- `∫ E_N f = ∫_P f`. [PROVED] -/
theorem coarsen_integral' (P : DyadicCube d) (N : ℕ) (f : TestFun d) :
    ∫ x, (coarsen P N f : (Fin d → ℝ) → ℝ) x = ∫ x in P.toSet, (f : (Fin d → ℝ) → ℝ) x := by
  have h1 : ∫ x, (coarsen P N f : (Fin d → ℝ) → ℝ) x =
      ∑ L ∈ StoppingData.level N P, ∫ x, (TestFun.truncateₗ L f : (Fin d → ℝ) → ℝ) x := by
    rw [← TestFun.integralₗ_apply, coarsen, map_sum]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [map_smul, smul_eq_mul, TestFun.integralₗ_apply, TestFun.integral_ind,
      TestFun.coe_truncateₗ, truncate, integral_indicator L.measurableSet_toSet, avg_mul_vol]
  have h2 : ∑ L ∈ StoppingData.level N P, ∫ x, (TestFun.truncateₗ L f : (Fin d → ℝ) → ℝ) x =
      ∑ L ∈ StoppingData.level N P, TestFun.integralₗ (TestFun.truncateₗ L f) :=
    Finset.sum_congr rfl fun L _ => by rw [TestFun.integralₗ_apply]
  rw [h1, h2, ← map_sum, StoppingData.sum_level_truncateₗ, TestFun.integralₗ_apply,
    TestFun.coe_truncateₗ, truncate, integral_indicator P.measurableSet_toSet]

/-- `∫ E_N f = ∫ f` for `f` supported on `P`. [PROVED] -/
theorem coarsen_integral {P : DyadicCube d} {N : ℕ} {f : TestFun d}
    (hf : SupportedOn (f : (Fin d → ℝ) → ℝ) P) :
    ∫ x, (coarsen P N f : (Fin d → ℝ) → ℝ) x = ∫ x, (f : (Fin d → ℝ) → ℝ) x := by
  rw [coarsen_integral', setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hf x hx]

/-- Jensen on a cube via Hölder: `|[f]_L|^q |L| ≤ ∫_L |f|^q` for `q ≥ 1`. [PROVED] -/
theorem abs_avg_rpow_mul_vol_le (L : DyadicCube d) (f : TestFun d) {q : ℝ} (hq : 1 ≤ q) :
    |avg L (f : (Fin d → ℝ) → ℝ)| ^ q * L.vol ≤ ∫ x in L.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  have hq0 : 0 < q := by linarith
  have hV := L.vol_pos
  have hM0 : 0 ≤ lpNorm (TestFun.truncateₗ L f : (Fin d → ℝ) → ℝ) q := lpNorm_nonneg _ _
  have hMq := TestFun.lpNorm_truncateₗ_rpow L f hq0
  have hI : |∫ x in L.toSet, (f : (Fin d → ℝ) → ℝ) x| ≤
      L.vol ^ (1 - 1 / q) * lpNorm (TestFun.truncateₗ L f : (Fin d → ℝ) → ℝ) q := by
    have := abs_integral_indicator_le hq (TestFun.memLp (TestFun.truncateₗ L f).2 _) L
    rwa [TestFun.coe_truncateₗ, truncate, Set.indicator_indicator, Set.inter_self,
      integral_indicator L.measurableSet_toSet] at this
  have h1 : |avg L (f : (Fin d → ℝ) → ℝ)| ≤
      L.vol ^ (-(1 / q)) * lpNorm (TestFun.truncateₗ L f : (Fin d → ℝ) → ℝ) q := by
    rw [avg, abs_div, abs_of_pos hV, div_le_iff₀ hV]
    refine hI.trans (le_of_eq ?_)
    rw [mul_right_comm, ← Real.rpow_add_one hV.ne']
    congr 2
    ring
  calc |avg L (f : (Fin d → ℝ) → ℝ)| ^ q * L.vol
      ≤ (L.vol ^ (-(1 / q)) * lpNorm (TestFun.truncateₗ L f : (Fin d → ℝ) → ℝ) q) ^ q * L.vol :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) h1 hq0.le) hV.le
    _ = lpNorm (TestFun.truncateₗ L f : (Fin d → ℝ) → ℝ) q ^ q := by
        rw [Real.mul_rpow (Real.rpow_nonneg hV.le _) hM0, ← Real.rpow_mul hV.le,
          show -(1 / q) * q = -1 by rw [neg_mul, one_div, inv_mul_cancel₀ hq0.ne'],
          Real.rpow_neg_one, mul_comm, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]
    _ = _ := hMq

/-- `∑_{L ∈ 𝒟_N(P)} 𝟙_L g = 𝟙_P g` pointwise: the leaves partition `P`. [PROVED] -/
theorem sum_indicator_level (N : ℕ) (P : DyadicCube d) (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ∑ L ∈ StoppingData.level N P, L.toSet.indicator g x = P.toSet.indicator g x := by
  by_cases hx : x ∈ P.toSet
  · obtain ⟨L₀, hL₀, hxL₀⟩ := StoppingData.exists_mem_level N hx
    rw [Set.indicator_of_mem hx, Finset.sum_eq_single L₀]
    · rw [Set.indicator_of_mem hxL₀]
    · intro L hL hne
      rcases StoppingData.level_eq_or_disjoint hL hL₀ with h | h
      · exact absurd h hne
      · exact Set.indicator_of_notMem (Set.disjoint_right.mp h hxL₀) _
    · intro h
      exact absurd hL₀ h
  · rw [Set.indicator_of_notMem hx]
    exact Finset.sum_eq_zero fun L hL =>
      Set.indicator_of_notMem (fun h => hx (StoppingData.subset_of_mem_level hL h)) _

/-- `∫_P g = ∑_{L ∈ 𝒟_N(P)} ∫_L g` for integrable `g`. [PROVED] -/
theorem setIntegral_eq_sum_level {g : (Fin d → ℝ) → ℝ} (hg : Integrable g volume) (N : ℕ)
    (P : DyadicCube d) :
    ∫ x in P.toSet, g x = ∑ L ∈ StoppingData.level N P, ∫ x in L.toSet, g x := by
  calc ∫ x in P.toSet, g x = ∫ x, P.toSet.indicator g x :=
        (integral_indicator P.measurableSet_toSet).symm
    _ = ∫ x, ∑ L ∈ StoppingData.level N P, L.toSet.indicator g x :=
        integral_congr_ae (ae_of_all _ fun x => (sum_indicator_level N P g x).symm)
    _ = ∑ L ∈ StoppingData.level N P, ∫ x, L.toSet.indicator g x :=
        integral_finsetSum _ fun L _ => hg.indicator L.measurableSet_toSet
    _ = _ := Finset.sum_congr rfl fun L _ => integral_indicator L.measurableSet_toSet

/-- **Jensen's inequality for the coarsening**: `∫ |E_N f|^q ≤ ∫ |f|^q` for `q ≥ 1`. [PROVED] -/
theorem coarsen_norm_le (P : DyadicCube d) (N : ℕ) (f : TestFun d) {q : ℝ} (hq : 1 ≤ q) :
    ∫ x, |(coarsen P N f : (Fin d → ℝ) → ℝ) x| ^ q ≤ ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  have hq0 : 0 < q := by linarith
  have hint : Integrable (fun x => |(f : (Fin d → ℝ) → ℝ) x| ^ q) volume :=
    TestFun.integrable_abs_rpow f hq0
  -- `|E_N f|^q = ∑_L |[f]_L|^q 𝟙_L`
  have hpt : ∀ x, |(coarsen P N f : (Fin d → ℝ) → ℝ) x| ^ q =
      ((∑ L ∈ StoppingData.level N P, |avg L (f : (Fin d → ℝ) → ℝ)| ^ q • TestFun.ind L :
        TestFun d) : (Fin d → ℝ) → ℝ) x := by
    intro x
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      TestFun.coe_ind]
    rw [coarsen_apply]
    by_cases hx : x ∈ P.toSet
    · obtain ⟨L₀, hL₀, hxL₀⟩ := StoppingData.exists_mem_level N hx
      have hother : ∀ L ∈ StoppingData.level N P, L ≠ L₀ →
          L.toSet.indicator (1 : (Fin d → ℝ) → ℝ) x = 0 := by
        intro L hL hne
        rcases StoppingData.level_eq_or_disjoint hL hL₀ with h | h
        · exact absurd h hne
        · exact Set.indicator_of_notMem (Set.disjoint_right.mp h hxL₀) _
      rw [Finset.sum_eq_single L₀ (fun L hL hne => by rw [hother L hL hne, mul_zero])
          (fun h => absurd hL₀ h),
        Finset.sum_eq_single L₀ (fun L hL hne => by rw [hother L hL hne, mul_zero])
          (fun h => absurd hL₀ h),
        Set.indicator_of_mem hxL₀, Pi.one_apply, mul_one, mul_one]
    · have hall : ∀ L ∈ StoppingData.level N P, L.toSet.indicator (1 : (Fin d → ℝ) → ℝ) x = 0 :=
        fun L hL => Set.indicator_of_notMem (fun h => hx (StoppingData.subset_of_mem_level hL h)) _
      rw [Finset.sum_eq_zero (fun L hL => by rw [hall L hL, mul_zero]),
        Finset.sum_eq_zero (fun L hL => by rw [hall L hL, mul_zero]), abs_zero,
        Real.zero_rpow hq0.ne']
  calc ∫ x, |(coarsen P N f : (Fin d → ℝ) → ℝ) x| ^ q
      = ∑ L ∈ StoppingData.level N P, |avg L (f : (Fin d → ℝ) → ℝ)| ^ q * L.vol := by
        rw [integral_congr_ae (ae_of_all _ hpt), ← TestFun.integralₗ_apply, map_sum]
        exact Finset.sum_congr rfl fun L _ => by
          rw [map_smul, smul_eq_mul, TestFun.integralₗ_apply, TestFun.integral_ind]
    _ ≤ ∑ L ∈ StoppingData.level N P, ∫ x in L.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q :=
        Finset.sum_le_sum fun L _ => abs_avg_rpow_mul_vol_le L f hq
    _ = ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q := (setIntegral_eq_sum_level hint N P).symm
    _ ≤ ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q :=
        setIntegral_le_integral hint (ae_of_all _ fun x => by positivity)

/-- **The form is unchanged by coarsening an entry below its resolution**: for `f_j` supported on
`P` and `P.m − N ≤ s`, `Λ(…, E_N f_j, …) = Λ(…, f_j, …)`. [PROVED] -/
theorem form_update_coarsen {T : PerfectCZForm d n} {s : ℤ} (hs : KernelScale T s)
    (f : Fin n → TestFun d) (j : Fin n) {P : DyadicCube d} {N : ℕ} (hPN : P.m - N ≤ s)
    (hf : SupportedOn (f j : (Fin d → ℝ) → ℝ) P) :
    T.form (Function.update f j (coarsen P N (f j))) = T.form f := by
  have hdec : f j = ∑ L ∈ StoppingData.level N P, TestFun.truncateₗ L (f j) := by
    rw [StoppingData.sum_level_truncateₗ, TestFun.truncateₗ_of_supportedOn hf]
  conv_rhs => rw [← Function.update_eq_self j f, hdec]
  rw [coarsen, MultilinearMap.map_update_sum, MultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun L hL => ?_
  rw [MultilinearMap.map_update_smul, smul_eq_mul]
  have hLm : L.m ≤ s := by
    rw [StoppingData.m_of_mem_level hL]
    exact hPN
  rw [hs f j L hLm (TestFun.truncateₗ L (f j)) (TestFun.truncateₗ_supportedOn _ _)]
  congr 1
  rw [avg, avg, TestFun.coe_truncateₗ, truncate, setIntegral_indicator L.measurableSet_toSet,
    Set.inter_self]

/-- **An instance of the testing condition (2.1)** (p. 40–41): an admissible path `σ₀` of length
`k+1` with an admissible extension `σ`, a `σ₀`-nested tuple `𝐐`, the extremal function `g`
supported on `Q = Q_{σ₀(k)}` with `‖g‖ > 0`, the constant `A ≥ 0` of (2.1) for the restricted
family, the resolution `N` of the frozen entries and of `g` relative to `Q`, and the resolution
`s` of the form, with the leaf scale `m_Q − N` of the tree at most `s`. -/
structure Instance (T : PerfectCZForm d n) (p : HolderTuple n) (C : IPath.Collection n)
    (b : TestingFamily d n (k + 1)) (B : ℝ) where
  hd : d ≠ 0
  hC : IPath.Admissible C
  hk : k + 1 < n
  hb : LocalTbHypotheses T p C b B
  hB : 1 ≤ B
  /-- the path `σ'` of length `k+1` -/
  σ₀ : IPath n (k + 1)
  hσ₀ : σ₀ ∈ C (k + 1)
  /-- the admissible extension `σ` of `σ'` -/
  σ : IPath n (k + 2)
  hσ : σ ∈ C (k + 2)
  hσσ₀ : σ.restrict = σ₀
  /-- the `σ'`-nested tuple `𝐐` -/
  Q : Fin n → DyadicCube d
  hQ : IPath.Nested σ₀ Q
  /-- the extremal function `g` -/
  G : TestFun d
  hG : SupportedOn G (Q (σ₀ (Fin.last k)))
  /-- the constant `A` of (2.1) -/
  A : ℝ
  hA : 0 ≤ A
  htest : TestingCondition T p C (restrictFamily C b) A
  /-- the resolution -/
  N : ℕ
  /-- the testing functions `b_{σ,𝐐,l}` of the chain `𝐐` (the frozen heads and `u`) are constant
  on the leaves of `𝒟_N(Q)` -/
  hgres : ∀ l : Fin (k + 1), ∀ T' : DyadicCube d, T'.toSet ⊆ (Q (σ₀ (Fin.last k))).toSet →
    T'.m = (Q (σ₀ (Fin.last k))).m - N → ConstOn (b σ Q l) T'
  hGres : ∀ T' : DyadicCube d, T'.toSet ⊆ (Q (σ₀ (Fin.last k))).toSet →
    T'.m = (Q (σ₀ (Fin.last k))).m - N → ConstOn G T'
  /-- the resolution of the form -/
  s : ℤ
  hs : KernelScale T s
  /-- the leaf scale of the tree is at most the resolution of the form -/
  hNs : (Q (σ₀ (Fin.last k))).m - N ≤ s

namespace Instance

variable (I : Instance T p C b B)

/-- The cube `Q = Q_{σ'(k)}`. -/
abbrev Q₀ : DyadicCube d := I.Q (I.σ₀ (Fin.last k))

/-- The slot `a = σ(k+1)` of `h`. -/
abbrev a : Fin n := I.σ (Fin.last (k + 1))

/-- The slot `b = σ'(k) = σ(k)` of `g` and `u`. -/
abbrev b₀ : Fin n := I.σ₀ (Fin.last k)

/-- The swapped path `τ`. -/
abbrev τ : IPath n (k + 2) := I.σ.swapLast

theorem hτ : I.τ ∈ C (k + 2) := I.hC.swap _ _ I.hσ

theorem hQσ : IPath.Nested I.σ I.Q := I.hQ.of_restrict I.hσσ₀

theorem hh : HeadsAgree I.σ₀ I.σ := headsAgree_of_restrict I.hσσ₀

theorem hhτ : HeadsAgree I.σ₀ I.τ := I.hh.swapLast

theorem cs (l : Fin (k + 1)) : I.σ l.castSucc = I.σ₀ l := by
  rw [← I.hσσ₀]
  rfl

theorem σ_castSucc_last : I.σ (Fin.castSucc (Fin.last k)) = I.b₀ := I.cs _

theorem τ_castSucc_last : I.τ (Fin.castSucc (Fin.last k)) = I.a := IPath.swapLast_castSucc_last _

theorem τ_last : I.τ (Fin.last (k + 1)) = I.b₀ := by
  rw [τ, IPath.swapLast_last, I.cs]

theorem a_not_mem_range : I.a ∉ Set.range I.σ₀ := by
  rintro ⟨i, hi⟩
  rw [← I.cs i] at hi
  exact (Fin.castSucc_lt_last i).ne (I.σ.injective hi)

theorem hab : I.a ≠ I.b₀ := fun h => I.a_not_mem_range ⟨_, h.symm⟩

theorem Q_a : I.Q I.a = I.Q₀ := I.hQ.outside _ I.a_not_mem_range

/-- The chains `𝐐_P` are nested for `σ'`, `σ` and `τ`. [PROVED] -/
theorem nested_σ₀ {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    IPath.Nested I.σ₀ (chain I.σ₀ I.Q P) := nested_chain I.hk I.hQ hP

theorem nested_σ {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    IPath.Nested I.σ (chain I.σ₀ I.Q P) := nested_chain_of_headsAgree I.hh I.hQ hP

theorem nested_τ {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    IPath.Nested I.τ (chain I.σ₀ I.Q P) := nested_chain_of_headsAgree I.hhτ I.hQ hP

theorem chain_a (P : DyadicCube d) : chain I.σ₀ I.Q P I.a = P := I.hh.chain_last I.Q P

theorem chain_b₀ (P : DyadicCube d) : chain I.σ₀ I.Q P I.b₀ = P := chain_last I.σ₀ I.Q P

/-- The testing function `u = b_{σ,𝐐,k+1}`. -/
noncomputable def u : TestFun d := ⟨b I.σ I.Q (Fin.last k), I.hb.testFun _ I.hσ _ I.hQσ _⟩

theorem u_supp : SupportedOn (I.u : (Fin d → ℝ) → ℝ) I.Q₀ := by
  have h := I.hb.support _ I.hσ _ I.hQσ (Fin.last k)
  rwa [I.σ_castSucc_last] at h

theorem u_mean : ∫ x, (I.u : (Fin d → ℝ) → ℝ) x = I.Q₀.vol := by
  have h := I.hb.mean _ I.hσ _ I.hQσ (Fin.last k)
  rwa [I.σ_castSucc_last] at h

theorem u_norm : ∫ x, |(I.u : (Fin d → ℝ) → ℝ) x| ^ p.p I.b₀ ≤ B * I.Q₀.vol := by
  have h := I.hb.norm _ I.hσ _ I.hQσ (Fin.last k)
  rwa [I.σ_castSucc_last] at h

/-- The frozen entries `g_j = f_j 𝟙_Q`: the truncated testing functions at the head positions, `u`
in the slot `b`, and `𝟙_Q` elsewhere. -/
noncomputable def frozen : Fin n → TestFun d :=
  Function.extend (fun l : Fin k => I.σ₀ l.castSucc)
    (fun l => TestFun.truncateₗ I.Q₀ ⟨b I.σ I.Q l.castSucc, I.hb.testFun _ I.hσ _ I.hQσ _⟩)
    (fun s => if s = I.b₀ then I.u else TestFun.ind I.Q₀)

theorem head_injective : Function.Injective (fun l : Fin k => I.σ₀ l.castSucc) :=
  fun _ _ h => Fin.castSucc_injective _ (I.σ₀.injective h)

theorem frozen_castSucc (l : Fin k) :
    I.frozen (I.σ₀ l.castSucc) =
      TestFun.truncateₗ I.Q₀ ⟨b I.σ I.Q l.castSucc, I.hb.testFun _ I.hσ _ I.hQσ _⟩ :=
  I.head_injective.extend_apply _ _ l

theorem frozen_b₀ : I.frozen I.b₀ = I.u := by
  rw [frozen, Function.extend_apply' _ _ _ (not_isHead_last I.σ₀)]
  simp

theorem frozen_of_not_mem {s : Fin n} (hs : s ∉ Set.range I.σ₀) : I.frozen s = TestFun.ind I.Q₀ :=
  by
  have h2 : s ≠ I.b₀ := fun h => hs ⟨_, h.symm⟩
  rw [frozen, Function.extend_apply' _ _ _ (fun h => hs (mem_range_of_isHead h))]
  simp only [h2, ↓reduceIte]

theorem frozen_supportedOn (s : Fin n) : SupportedOn (I.frozen s : (Fin d → ℝ) → ℝ) I.Q₀ := by
  by_cases h : IsHead I.σ₀ s
  · obtain ⟨l, rfl⟩ := h
    rw [I.frozen_castSucc]
    exact TestFun.truncateₗ_supportedOn _ _
  · by_cases hs : s = I.b₀
    · subst hs
      rw [I.frozen_b₀]
      exact I.u_supp
    · rw [I.frozen_of_not_mem (not_mem_range_of h hs)]
      exact TestFun.ind_supportedOn _

theorem truncateₗ_frozen (s : Fin n) : TestFun.truncateₗ I.Q₀ (I.frozen s) = I.frozen s :=
  TestFun.truncateₗ_of_supportedOn (I.frozen_supportedOn s)

open Classical in
/-- The testing functions `b_{σ,𝐐_P,k+1}` of the chains (`0` for `P ⊄ Q`). -/
noncomputable def bP (P : DyadicCube d) : TestFun d :=
  if hP : P.toSet ⊆ I.Q₀.toSet then
    ⟨b I.σ (chain I.σ₀ I.Q P) (Fin.last k), I.hb.testFun _ I.hσ _ (I.nested_σ hP) _⟩
  else 0

open Classical in
/-- The testing functions `b_{τ,𝐐_P,k}` of the chains (`0` for `P ⊄ Q`). -/
noncomputable def vP (P : DyadicCube d) : TestFun d :=
  if hP : P.toSet ⊆ I.Q₀.toSet then
    ⟨b I.τ (chain I.σ₀ I.Q P) (Fin.last k), I.hb.testFun _ I.hτ _ (I.nested_τ hP) _⟩
  else 0

theorem bP_eq {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    I.bP P = ⟨b I.σ (chain I.σ₀ I.Q P) (Fin.last k), I.hb.testFun _ I.hσ _ (I.nested_σ hP) _⟩ := by
  unfold bP
  simp only [hP, ↓reduceDIte]

theorem vP_eq {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    I.vP P = ⟨b I.τ (chain I.σ₀ I.Q P) (Fin.last k), I.hb.testFun _ I.hτ _ (I.nested_τ hP) _⟩ := by
  unfold vP
  simp only [hP, ↓reduceDIte]

theorem bP_supp {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    SupportedOn (I.bP P : (Fin d → ℝ) → ℝ) P := by
  rw [I.bP_eq hP]
  have h := I.hb.support _ I.hσ _ (I.nested_σ hP) (Fin.last k)
  rwa [I.σ_castSucc_last, I.chain_b₀] at h

theorem bP_mean {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    ∫ x, (I.bP P : (Fin d → ℝ) → ℝ) x = P.vol := by
  rw [I.bP_eq hP]
  have h := I.hb.mean _ I.hσ _ (I.nested_σ hP) (Fin.last k)
  rwa [I.σ_castSucc_last, I.chain_b₀] at h

theorem bP_norm {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    ∫ x, |(I.bP P : (Fin d → ℝ) → ℝ) x| ^ p.p I.b₀ ≤ B * P.vol := by
  rw [I.bP_eq hP]
  have h := I.hb.norm _ I.hσ _ (I.nested_σ hP) (Fin.last k)
  rwa [I.σ_castSucc_last, I.chain_b₀] at h

theorem vP_supp {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    SupportedOn (I.vP P : (Fin d → ℝ) → ℝ) P := by
  rw [I.vP_eq hP]
  have h := I.hb.support _ I.hτ _ (I.nested_τ hP) (Fin.last k)
  rwa [I.τ_castSucc_last, I.chain_a] at h

theorem vP_mean {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    ∫ x, (I.vP P : (Fin d → ℝ) → ℝ) x = P.vol := by
  rw [I.vP_eq hP]
  have h := I.hb.mean _ I.hτ _ (I.nested_τ hP) (Fin.last k)
  rwa [I.τ_castSucc_last, I.chain_a] at h

theorem vP_norm {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    ∫ x, |(I.vP P : (Fin d → ℝ) → ℝ) x| ^ p.p I.a ≤ B * P.vol := by
  rw [I.vP_eq hP]
  have h := I.hb.norm _ I.hτ _ (I.nested_τ hP) (Fin.last k)
  rwa [I.τ_castSucc_last, I.chain_a] at h

/-- The tuple of the two-slot form `Λ_P(x, y)` with the frozen entries. -/
noncomputable def tup (P : DyadicCube d) (x y : TestFun d) : Fin n → TestFun d :=
  Function.update (Function.update (fun j => TestFun.truncateₗ P (I.frozen j)) I.a
    (TestFun.truncateₗ P x)) I.b₀ (TestFun.truncateₗ P y)

theorem twoSlotForm_eq_form_tup (P : DyadicCube d) (x y : TestFun d) :
    twoSlotForm T I.a I.b₀ I.frozen P x y = T.form (I.tup P x y) := rfl

theorem tup_a (P : DyadicCube d) (x y : TestFun d) : I.tup P x y I.a = TestFun.truncateₗ P x := by
  rw [tup, Function.update_of_ne I.hab, Function.update_self]

theorem tup_b₀ (P : DyadicCube d) (x y : TestFun d) : I.tup P x y I.b₀ = TestFun.truncateₗ P y := by
  rw [tup, Function.update_self]

theorem tup_of_ne (P : DyadicCube d) (x y : TestFun d) {j : Fin n} (hja : j ≠ I.a)
    (hjb : j ≠ I.b₀) : I.tup P x y j = TestFun.truncateₗ P (I.frozen j) := by
  rw [tup, Function.update_of_ne hjb, Function.update_of_ne hja]

theorem tup_head {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (x y : TestFun d) (l : Fin k) :
    I.tup P x y (I.σ₀ l.castSucc) =
      TestFun.truncateₗ P ⟨b I.σ I.Q l.castSucc, I.hb.testFun _ I.hσ _ I.hQσ _⟩ := by
  have h1 : I.σ₀ l.castSucc ≠ I.b₀ := fun h => (Fin.castSucc_lt_last l).ne (I.σ₀.injective h)
  have h2 : I.σ₀ l.castSucc ≠ I.a := fun h => I.a_not_mem_range ⟨_, h⟩
  rw [tup, Function.update_of_ne h1, Function.update_of_ne h2, I.frozen_castSucc,
    TestFun.truncateₗ_truncateₗ_of_subset hP]

theorem tup_out {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (x y : TestFun d) {s : Fin n}
    (hs : s ∉ Set.range I.σ₀) (hsa : s ≠ I.a) : I.tup P x y s = TestFun.ind P := by
  have h1 : s ≠ I.b₀ := fun h => hs ⟨_, h.symm⟩
  rw [tup, Function.update_of_ne h1, Function.update_of_ne hsa, I.frozen_of_not_mem hs,
    TestFun.truncateₗ_ind_of_subset hP]

theorem prodNorm_tup (P : DyadicCube d) (x y : TestFun d) :
    prodNorm p (I.tup P x y) =
      lpNorm (TestFun.truncateₗ P x : (Fin d → ℝ) → ℝ) (p.p I.a) *
        lpNorm (TestFun.truncateₗ P y : (Fin d → ℝ) → ℝ) (p.p I.b₀) *
        ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j) :=
  prodNorm_update_update p _ I.hab _ _

theorem not_mem_range_σ {s : Fin n} (hs : s ∉ Set.range I.σ) : s ∉ Set.range I.σ₀ :=
  fun ⟨i, hi⟩ => hs ⟨i.castSucc, by rw [I.cs, hi]⟩

theorem ne_a_of_not_mem_range_σ {s : Fin n} (hs : s ∉ Set.range I.σ) : s ≠ I.a :=
  fun h => hs ⟨_, h.symm⟩

theorem not_mem_range_τ {s : Fin n} (hs : s ∉ Set.range I.τ) : s ∉ Set.range I.σ₀ := by
  rintro ⟨i, rfl⟩
  induction i using Fin.lastCases with
  | last => exact hs ⟨_, I.τ_last⟩
  | cast l => exact hs ⟨_, I.hhτ l⟩

theorem ne_a_of_not_mem_range_τ {s : Fin n} (hs : s ∉ Set.range I.τ) : s ≠ I.a :=
  fun h => hs ⟨_, I.τ_castSucc_last.trans h.symm⟩

/-- **The testing condition (1.9) for `σ`, `𝐐_P`** in the form of the field `testing_bP`. [PROVED]
-/
theorem testing_bP {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (ρ : TestFun d)
    (hρ : SupportedOn ρ P) :
    |twoSlotForm T I.a I.b₀ I.frozen P ρ (I.bP P)| ≤
      B * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (I.bP P : (Fin d → ℝ) → ℝ) (p.p I.b₀) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.a) := by
  rw [I.twoSlotForm_eq_form_tup]
  have hbot : chain I.σ₀ I.Q P (I.σ (Fin.last (k + 1))) = P := I.chain_a P
  have h2 : ∀ l : Fin (k + 1), (I.tup P ρ (I.bP P) (I.σ l.castSucc) : (Fin d → ℝ) → ℝ) =
      truncate (chain I.σ₀ I.Q P (I.σ (Fin.last (k + 1)))) (b I.σ (chain I.σ₀ I.Q P) l) := by
    intro l
    rw [hbot]
    induction l using Fin.lastCases with
    | last =>
      rw [I.σ_castSucc_last, I.tup_b₀, I.bP_eq hP]
      rfl
    | cast l =>
      rw [I.hh l, I.tup_head hP, b_chain_eq I.hb I.hσ I.hσ I.hh I.hh I.hQ I.hQσ hP l]
      rfl
  have h3 : ∀ s, s ∉ Set.range I.σ → (I.tup P ρ (I.bP P) s : (Fin d → ℝ) → ℝ) =
      (chain I.σ₀ I.Q P (I.σ (Fin.last (k + 1)))).indicator := by
    intro s hs
    rw [hbot, I.tup_out hP _ _ (I.not_mem_range_σ hs) (I.ne_a_of_not_mem_range_σ hs)]
    rfl
  have h := I.hb.testing I.σ I.hσ _ (I.nested_σ hP) (TestFun.truncateₗ P ρ)
    (by rw [hbot]; exact TestFun.truncateₗ_supportedOn _ _) (I.tup P ρ (I.bP P)) (I.tup_a _ _ _)
    h2 h3
  rw [I.prodNorm_tup, TestFun.truncateₗ_of_supportedOn hρ,
    TestFun.truncateₗ_of_supportedOn (I.bP_supp hP)] at h
  exact h.trans (le_of_eq (by ring))

/-- **The testing condition (1.9) for `τ`, `𝐐_P`** in the form of the field `testing_vP`. [PROVED]
-/
theorem testing_vP {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (ρ : TestFun d)
    (hρ : SupportedOn ρ P) :
    |twoSlotForm T I.a I.b₀ I.frozen P (I.vP P) ρ| ≤
      B * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (I.vP P : (Fin d → ℝ) → ℝ) (p.p I.a) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.b₀) := by
  rw [I.twoSlotForm_eq_form_tup]
  have hbot : chain I.σ₀ I.Q P (I.τ (Fin.last (k + 1))) = P := by rw [I.τ_last, I.chain_b₀]
  have h2 : ∀ l : Fin (k + 1), (I.tup P (I.vP P) ρ (I.τ l.castSucc) : (Fin d → ℝ) → ℝ) =
      truncate (chain I.σ₀ I.Q P (I.τ (Fin.last (k + 1)))) (b I.τ (chain I.σ₀ I.Q P) l) := by
    intro l
    rw [hbot]
    induction l using Fin.lastCases with
    | last =>
      rw [I.τ_castSucc_last, I.tup_a, I.vP_eq hP]
      rfl
    | cast l =>
      rw [I.hhτ l, I.tup_head hP, b_chain_eq I.hb I.hτ I.hσ I.hhτ I.hh I.hQ I.hQσ hP l]
      rfl
  have h3 : ∀ s, s ∉ Set.range I.τ → (I.tup P (I.vP P) ρ s : (Fin d → ℝ) → ℝ) =
      (chain I.σ₀ I.Q P (I.τ (Fin.last (k + 1)))).indicator := by
    intro s hs
    rw [hbot, I.tup_out hP _ _ (I.not_mem_range_τ hs) (I.ne_a_of_not_mem_range_τ hs)]
    rfl
  have h := I.hb.testing I.τ I.hτ _ (I.nested_τ hP) (TestFun.truncateₗ P ρ)
    (by rw [hbot]; exact TestFun.truncateₗ_supportedOn _ _) (I.tup P (I.vP P) ρ)
    (by rw [I.τ_last, I.tup_b₀]) h2 h3
  rw [I.prodNorm_tup, TestFun.truncateₗ_of_supportedOn hρ,
    TestFun.truncateₗ_of_supportedOn (I.vP_supp hP)] at h
  exact h.trans (le_of_eq (by ring))

/-- **The estimate (2.1) for `σ'`, `𝐐_P`** in the form of the field `estimateA`. [PROVED] -/
theorem estimateA {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (ρ : TestFun d)
    (hρ : SupportedOn ρ P) :
    |twoSlotForm T I.a I.b₀ I.frozen P (TestFun.ind P) ρ| ≤
      I.A * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        P.vol ^ (1 / p.p I.a) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.b₀) := by
  rw [I.twoSlotForm_eq_form_tup]
  have hbot : chain I.σ₀ I.Q P (I.σ₀ (Fin.last k)) = P := I.chain_b₀ P
  have h2 : ∀ l : Fin k, (I.tup P (TestFun.ind P) ρ (I.σ₀ l.castSucc) : (Fin d → ℝ) → ℝ) =
      truncate (chain I.σ₀ I.Q P (I.σ₀ (Fin.last k)))
        (restrictFamily C b I.σ₀ (chain I.σ₀ I.Q P) l) := by
    intro l
    rw [hbot, I.tup_head hP,
      restrictFamily_eq_of_ext I.hC I.hk I.hb I.hσ₀ I.hσ I.hσσ₀ (I.nested_σ₀ hP) l,
      b_chain_eq I.hb I.hσ I.hσ I.hh I.hh I.hQ I.hQσ hP l]
    rfl
  have h3 : ∀ s, s ∉ Set.range I.σ₀ → (I.tup P (TestFun.ind P) ρ s : (Fin d → ℝ) → ℝ) =
      (chain I.σ₀ I.Q P (I.σ₀ (Fin.last k))).indicator := by
    intro s hs
    rw [hbot]
    by_cases hsa : s = I.a
    · subst hsa
      rw [I.tup_a, TestFun.truncateₗ_ind]
      rfl
    · rw [I.tup_out hP _ _ hs hsa]
      rfl
  have h := I.htest I.σ₀ I.hσ₀ _ (I.nested_σ₀ hP) (TestFun.truncateₗ P ρ)
    (by rw [hbot]; exact TestFun.truncateₗ_supportedOn _ _) (I.tup P (TestFun.ind P) ρ)
    (I.tup_b₀ _ _ _) h2 h3
  rw [I.prodNorm_tup, TestFun.truncateₗ_of_supportedOn hρ, TestFun.truncateₗ_ind,
    TestFun.lpNorm_ind P (by linarith [p.one_lt I.a])] at h
  exact h.trans (le_of_eq (by ring))

/-- **The testing condition (1.9) for `σ`, `𝐐`** in the form of the field `testing`. [PROVED] -/
theorem testing (ρ : TestFun d) (hρ : SupportedOn ρ I.Q₀) :
    |slotForm T I.a I.frozen I.Q₀ ρ| ≤
      B * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (I.u : (Fin d → ℝ) → ℝ) (p.p I.b₀) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.a) := by
  rw [← twoSlotForm_self T I.hab, I.frozen_b₀, I.twoSlotForm_eq_form_tup]
  have hprod : ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
      lpNorm (TestFun.truncateₗ I.Q₀ (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j) =
      ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀, lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j) :=
    Finset.prod_congr rfl fun j _ => by rw [I.truncateₗ_frozen j]
  have h2 : ∀ l : Fin (k + 1), (I.tup I.Q₀ ρ I.u (I.σ l.castSucc) : (Fin d → ℝ) → ℝ) =
      truncate (I.Q (I.σ (Fin.last (k + 1)))) (b I.σ I.Q l) := by
    intro l
    rw [I.Q_a]
    induction l using Fin.lastCases with
    | last =>
      rw [I.σ_castSucc_last, I.tup_b₀]
      rfl
    | cast l =>
      rw [I.hh l, I.tup_head (subset_refl _)]
      rfl
  have h3 : ∀ s, s ∉ Set.range I.σ → (I.tup I.Q₀ ρ I.u s : (Fin d → ℝ) → ℝ) =
      (I.Q (I.σ (Fin.last (k + 1)))).indicator := by
    intro s hs
    rw [I.Q_a, I.tup_out (subset_refl _) _ _ (I.not_mem_range_σ hs) (I.ne_a_of_not_mem_range_σ hs)]
    rfl
  have h := I.hb.testing I.σ I.hσ I.Q I.hQσ (TestFun.truncateₗ I.Q₀ ρ)
    (by rw [I.Q_a]; exact TestFun.truncateₗ_supportedOn _ _) (I.tup I.Q₀ ρ I.u) (I.tup_a _ _ _)
    h2 h3
  rw [I.prodNorm_tup, TestFun.truncateₗ_of_supportedOn hρ,
    TestFun.truncateₗ_of_supportedOn I.u_supp, hprod] at h
  exact h.trans (le_of_eq (by ring))

/-! #### The coarsened testing functions of the chains

The testing functions `b_{σ,𝐐_P,k+1}`, `b_{τ,𝐐_P,k}` are replaced by their coarsenings at the leaf
scale `m_Q − N` of the tree (and at their own scale for cubes below it); since this scale is at most
the resolution `s` of the form, the two-slot forms are unchanged, and the testing conditions hold
with the constant `B²`. -/

/-- The leaf depth of a cube `P`: the number of levels from `P` down to the leaf scale `m_Q − N`
(zero for cubes below the leaf scale). -/
noncomputable def leafDepth (P : DyadicCube d) : ℕ := (P.m - (I.Q₀.m - I.N)).toNat

theorem leafDepth_le (P : DyadicCube d) : P.m - I.leafDepth P ≤ I.s := by
  have h : I.Q₀.m - I.N ≤ I.s := I.hNs
  unfold leafDepth
  omega

theorem leafDepth_scale {P : DyadicCube d} (hPm : I.Q₀.m - I.N ≤ P.m) :
    P.m - I.leafDepth P = I.Q₀.m - I.N := by
  unfold leafDepth
  omega

/-- The coarsened testing functions `E_N b_{σ,𝐐_P,k+1}`. -/
noncomputable def bPc (P : DyadicCube d) : TestFun d := coarsen P (I.leafDepth P) (I.bP P)

/-- The coarsened testing functions `E_N b_{τ,𝐐_P,k}`. -/
noncomputable def vPc (P : DyadicCube d) : TestFun d := coarsen P (I.leafDepth P) (I.vP P)

theorem bPc_supp (P : DyadicCube d) : SupportedOn (I.bPc P : (Fin d → ℝ) → ℝ) P :=
  coarsen_supportedOn _ _ _

theorem vPc_supp (P : DyadicCube d) : SupportedOn (I.vPc P : (Fin d → ℝ) → ℝ) P :=
  coarsen_supportedOn _ _ _

theorem bPc_mean {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    ∫ x, (I.bPc P : (Fin d → ℝ) → ℝ) x = P.vol := by
  rw [bPc, coarsen_integral (I.bP_supp hP), I.bP_mean hP]

theorem vPc_mean {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    ∫ x, (I.vPc P : (Fin d → ℝ) → ℝ) x = P.vol := by
  rw [vPc, coarsen_integral (I.vP_supp hP), I.vP_mean hP]

theorem bPc_norm {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    ∫ x, |(I.bPc P : (Fin d → ℝ) → ℝ) x| ^ p.p I.b₀ ≤ B * P.vol :=
  (coarsen_norm_le _ _ _ (p.one_lt I.b₀).le).trans (I.bP_norm hP)

theorem vPc_norm {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) :
    ∫ x, |(I.vPc P : (Fin d → ℝ) → ℝ) x| ^ p.p I.a ≤ B * P.vol :=
  (coarsen_norm_le _ _ _ (p.one_lt I.a).le).trans (I.vP_norm hP)

theorem bPc_const {P : DyadicCube d} (hPm : I.Q₀.m - I.N ≤ P.m) {T' : DyadicCube d}
    (hTm : T'.m = I.Q₀.m - I.N) : ConstOn (I.bPc P : (Fin d → ℝ) → ℝ) T' :=
  coarsen_constOn _ _ _ (by rw [hTm, I.leafDepth_scale hPm])

theorem vPc_const {P : DyadicCube d} (hPm : I.Q₀.m - I.N ≤ P.m) {T' : DyadicCube d}
    (hTm : T'.m = I.Q₀.m - I.N) : ConstOn (I.vPc P : (Fin d → ℝ) → ℝ) T' :=
  coarsen_constOn _ _ _ (by rw [hTm, I.leafDepth_scale hPm])

/-- `|P|^{1/q} ≤ ‖φ‖_q` for `φ` supported on `P` with mean `|P|` (Hölder). [PROVED] -/
theorem vol_rpow_le_lpNorm {P : DyadicCube d} {φ : TestFun d}
    (hφ : SupportedOn (φ : (Fin d → ℝ) → ℝ) P) (hmean : ∫ x, (φ : (Fin d → ℝ) → ℝ) x = P.vol)
    {q : ℝ} (hq : 1 ≤ q) : P.vol ^ (1 / q) ≤ lpNorm (φ : (Fin d → ℝ) → ℝ) q := by
  have hV := P.vol_pos
  have hH := abs_integral_indicator_le hq (TestFun.memLp φ.2 _) P
  have e : P.toSet.indicator (φ : (Fin d → ℝ) → ℝ) = φ := by
    funext x
    by_cases hx : x ∈ P.toSet
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hφ x hx]
  rw [e, hmean, abs_of_pos hV] at hH
  have hpos : 0 < P.vol ^ (1 - 1 / q) := Real.rpow_pos_of_pos hV _
  have hsplit : P.vol ^ (1 / q) * P.vol ^ (1 - 1 / q) = P.vol := by
    rw [← Real.rpow_add hV, show 1 / q + (1 - 1 / q) = (1 : ℝ) by ring, Real.rpow_one]
  rw [show P.vol ^ (1 / q) = P.vol / P.vol ^ (1 - 1 / q) by rw [eq_div_iff hpos.ne', hsplit],
    div_le_iff₀ hpos, mul_comm]
  exact hH

/-- The coarsened `b_{σ,𝐐_P,k+1}` enters the two-slot form like the original one. [PROVED] -/
theorem twoSlotForm_bPc {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (ρ : TestFun d) :
    twoSlotForm T I.a I.b₀ I.frozen P ρ (I.bPc P) =
      twoSlotForm T I.a I.b₀ I.frozen P ρ (I.bP P) := by
  have e : I.tup P ρ (I.bPc P) = Function.update (I.tup P ρ (I.bP P)) I.b₀
      (coarsen P (I.leafDepth P) (I.tup P ρ (I.bP P) I.b₀)) := by
    rw [I.tup_b₀, TestFun.truncateₗ_of_supportedOn (I.bP_supp hP)]
    change I.tup P ρ (I.bPc P) = Function.update (I.tup P ρ (I.bP P)) I.b₀ (I.bPc P)
    rw [tup, tup, Function.update_idem, TestFun.truncateₗ_of_supportedOn (I.bPc_supp P)]
  rw [I.twoSlotForm_eq_form_tup, I.twoSlotForm_eq_form_tup, e]
  refine form_update_coarsen I.hs _ _ (I.leafDepth_le P) ?_
  rw [I.tup_b₀]
  exact TestFun.truncateₗ_supportedOn _ _

/-- The coarsened `b_{τ,𝐐_P,k}` enters the two-slot form like the original one. [PROVED] -/
theorem twoSlotForm_vPc {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (ρ : TestFun d) :
    twoSlotForm T I.a I.b₀ I.frozen P (I.vPc P) ρ =
      twoSlotForm T I.a I.b₀ I.frozen P (I.vP P) ρ := by
  have e : I.tup P (I.vPc P) ρ = Function.update (I.tup P (I.vP P) ρ) I.a
      (coarsen P (I.leafDepth P) (I.tup P (I.vP P) ρ I.a)) := by
    rw [I.tup_a, TestFun.truncateₗ_of_supportedOn (I.vP_supp hP)]
    change I.tup P (I.vPc P) ρ = Function.update (I.tup P (I.vP P) ρ) I.a (I.vPc P)
    rw [tup, tup, Function.update_comm I.hab.symm, Function.update_idem,
      TestFun.truncateₗ_of_supportedOn (I.vPc_supp P)]
  rw [I.twoSlotForm_eq_form_tup, I.twoSlotForm_eq_form_tup, e]
  refine form_update_coarsen I.hs _ _ (I.leafDepth_le P) ?_
  rw [I.tup_a]
  exact TestFun.truncateₗ_supportedOn _ _

/-- **The testing condition for the coarsened `b_{σ,𝐐_P,k+1}`**, with the constant `B²`:
`‖b‖_q ≤ (B|P|)^{1/q} ≤ B |P|^{1/q} ≤ B ‖E_N b‖_q`. [PROVED] -/
theorem testing_bPc {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (ρ : TestFun d)
    (hρ : SupportedOn ρ P) :
    |twoSlotForm T I.a I.b₀ I.frozen P ρ (I.bPc P)| ≤
      (B * B) * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (I.bPc P : (Fin d → ℝ) → ℝ) (p.p I.b₀) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.a) := by
  rw [I.twoSlotForm_bPc hP]
  have hB0 : (0 : ℝ) ≤ B := by linarith [I.hB]
  have hq1 : 1 ≤ p.p I.b₀ := (p.one_lt I.b₀).le
  have hF0 : 0 ≤ ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
      lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j) :=
    Finset.prod_nonneg fun _ _ => lpNorm_nonneg _ _
  have h1 : lpNorm (I.bP P : (Fin d → ℝ) → ℝ) (p.p I.b₀) ≤ (B * P.vol) ^ (1 / p.p I.b₀) :=
    TestFun.lpNorm_le_rpow_of_integral_le _ (by linarith) (I.bP_norm hP)
  have h2 : (B * P.vol) ^ (1 / p.p I.b₀) ≤ B * lpNorm (I.bPc P : (Fin d → ℝ) → ℝ) (p.p I.b₀) := by
    rw [Real.mul_rpow hB0 P.vol_pos.le]
    refine mul_le_mul ?_ (vol_rpow_le_lpNorm (I.bPc_supp P) (I.bPc_mean hP) hq1)
      (Real.rpow_nonneg P.vol_pos.le _) hB0
    calc B ^ (1 / p.p I.b₀) ≤ B ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le I.hB ((div_le_one (by linarith)).mpr hq1)
      _ = B := Real.rpow_one B
  calc |twoSlotForm T I.a I.b₀ I.frozen P ρ (I.bP P)|
      ≤ B * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (I.bP P : (Fin d → ℝ) → ℝ) (p.p I.b₀) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.a) :=
        I.testing_bP hP ρ hρ
    _ ≤ B * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        (B * lpNorm (I.bPc P : (Fin d → ℝ) → ℝ) (p.p I.b₀)) *
          lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.a) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hB0 hF0)) (lpNorm_nonneg _ _)
    _ = _ := by ring

/-- **The testing condition for the coarsened `b_{τ,𝐐_P,k}`**, with the constant `B²`. [PROVED] -/
theorem testing_vPc {P : DyadicCube d} (hP : P.toSet ⊆ I.Q₀.toSet) (ρ : TestFun d)
    (hρ : SupportedOn ρ P) :
    |twoSlotForm T I.a I.b₀ I.frozen P (I.vPc P) ρ| ≤
      (B * B) * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (I.vPc P : (Fin d → ℝ) → ℝ) (p.p I.a) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.b₀) := by
  rw [I.twoSlotForm_vPc hP]
  have hB0 : (0 : ℝ) ≤ B := by linarith [I.hB]
  have hq1 : 1 ≤ p.p I.a := (p.one_lt I.a).le
  have hF0 : 0 ≤ ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
      lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j) :=
    Finset.prod_nonneg fun _ _ => lpNorm_nonneg _ _
  have h1 : lpNorm (I.vP P : (Fin d → ℝ) → ℝ) (p.p I.a) ≤ (B * P.vol) ^ (1 / p.p I.a) :=
    TestFun.lpNorm_le_rpow_of_integral_le _ (by linarith) (I.vP_norm hP)
  have h2 : (B * P.vol) ^ (1 / p.p I.a) ≤ B * lpNorm (I.vPc P : (Fin d → ℝ) → ℝ) (p.p I.a) := by
    rw [Real.mul_rpow hB0 P.vol_pos.le]
    refine mul_le_mul ?_ (vol_rpow_le_lpNorm (I.vPc_supp P) (I.vPc_mean hP) hq1)
      (Real.rpow_nonneg P.vol_pos.le _) hB0
    calc B ^ (1 / p.p I.a) ≤ B ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le I.hB ((div_le_one (by linarith)).mpr hq1)
      _ = B := Real.rpow_one B
  calc |twoSlotForm T I.a I.b₀ I.frozen P (I.vP P) ρ|
      ≤ B * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (I.vP P : (Fin d → ℝ) → ℝ) (p.p I.a) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.b₀) :=
        I.testing_vP hP ρ hρ
    _ ≤ B * (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (TestFun.truncateₗ P (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        (B * lpNorm (I.vPc P : (Fin d → ℝ) → ℝ) (p.p I.a)) *
          lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p I.b₀) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hB0 hF0)) (lpNorm_nonneg _ _)
    _ = _ := by ring

/-- **The stopping data of §2.2 for the instance** (given `F > 0` and `‖g‖_q > 0`), with the
constant `B²` and the coarsened testing functions `E_N b_{σ,𝐐_P,k+1}`, `E_N b_{τ,𝐐_P,k}` of the
chains. -/
noncomputable def data
    (hF : 0 < ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
      lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j))
    (hG0 : 0 < lpNorm (I.G : (Fin d → ℝ) → ℝ) (p.p I.b₀)) : StoppingData d n where
  T := T
  p := p
  B := B * B
  Q := I.Q₀
  hd := I.hd
  N := I.N
  a := I.a
  b := I.b₀
  hab := I.hab
  g := I.frozen
  G := I.G
  hB := one_le_mul_of_one_le_of_one_le I.hB I.hB
  supp := I.frozen_supportedOn
  Gsupp := I.hG
  Gpos := hG0
  mean := by
    rw [I.frozen_b₀]
    exact I.u_mean
  norm := by
    rw [I.frozen_b₀]
    exact I.u_norm.trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left (by linarith [I.hB]) I.hB) I.Q₀.vol_pos.le)
  Fpos := hF
  testing := by
    intro ρ hρ
    rw [I.frozen_b₀]
    refine (I.testing ρ hρ).trans ?_
    have hF0 : 0 ≤ ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
        lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j) :=
      Finset.prod_nonneg fun _ _ => lpNorm_nonneg _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left (by linarith [I.hB]) I.hB) hF0) (lpNorm_nonneg _ _))
      (lpNorm_nonneg _ _)
  bP := I.bPc
  vP := I.vPc
  A := I.A
  hA0 := I.hA
  bP_supp := fun P _ => I.bPc_supp P
  bP_mean := fun _ hP => I.bPc_mean hP
  bP_norm := fun P hP => (I.bPc_norm hP).trans (mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_left (by linarith [I.hB]) I.hB) P.vol_pos.le)
  vP_supp := fun P _ => I.vPc_supp P
  vP_mean := fun _ hP => I.vPc_mean hP
  vP_norm := fun P hP => (I.vPc_norm hP).trans (mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_left (by linarith [I.hB]) I.hB) P.vol_pos.le)
  testing_bP := fun _ hP ρ hρ => I.testing_bPc hP ρ hρ
  testing_vP := fun _ hP ρ hρ => I.testing_vPc hP ρ hρ
  estimateA := fun _ hP ρ hρ => I.estimateA hP ρ hρ
  m := 1
  aux := fun _ => I.G
  auxExp := fun _ => p.p I.b₀
  aux_pos := fun _ => by linarith [p.one_lt I.b₀]
  aux_supp := fun _ => I.hG
  w := 0
  K := 1
  hK := one_pos
  w_test := by
    intro ρ _ _
    rw [StoppingData.twoSlotForm_zero_left T I.hab, abs_zero, one_mul]
    exact lpNorm_nonneg _ _
  g_const := by
    intro j T' hT' hTm
    by_cases h : IsHead I.σ₀ j
    · obtain ⟨l, rfl⟩ := h
      rw [I.frozen_castSucc]
      exact constOn_truncateₗ (Or.inl hT') (I.hgres l.castSucc T' hT' hTm)
    · by_cases hs : j = I.b₀
      · subst hs
        rw [I.frozen_b₀]
        exact I.hgres (Fin.last k) T' hT' hTm
      · rw [I.frozen_of_not_mem (not_mem_range_of h hs)]
        exact constOn_ind (Or.inl hT')
  G_const := I.hGres
  bP_const := fun _ _ hPm _ _ hTm => I.bPc_const hPm hTm
  vP_const := fun _ _ hPm _ _ hTm => I.vPc_const hPm hTm

/-- `g` satisfies (2.8) for the data: it is among the auxiliary functions. [PROVED] -/
theorem data_GBound
    (hF : 0 < ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
      lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j))
    (hG0 : 0 < lpNorm (I.G : (Fin d → ℝ) → ℝ) (p.p I.b₀)) : (I.data hF hG0).GBound :=
  (I.data hF hG0).GBound_of_GAux ⟨(⟨0, Nat.zero_lt_one⟩ : Fin 1), rfl, rfl⟩

/-- **The tuple of (2.1) at `(σ', 𝐐, g)` is the tuple of `Λ_Q(𝟙_Q, g)`** with the frozen entries.
[PROVED] -/
theorem eq_tup (f : Fin n → TestFun d) (hf : f I.b₀ = I.G)
    (hl : ∀ l : Fin k, (f (I.σ₀ l.castSucc) : (Fin d → ℝ) → ℝ) =
      truncate I.Q₀ (restrictFamily C b I.σ₀ I.Q l))
    (hs : ∀ s, s ∉ Set.range I.σ₀ → (f s : (Fin d → ℝ) → ℝ) = I.Q₀.indicator) :
    f = I.tup I.Q₀ (TestFun.ind I.Q₀) I.G := by
  funext s
  by_cases h : IsHead I.σ₀ s
  · obtain ⟨l, rfl⟩ := h
    apply Subtype.ext
    rw [hl l, I.tup_head (subset_refl _),
      restrictFamily_eq_of_ext I.hC I.hk I.hb I.hσ₀ I.hσ I.hσσ₀ I.hQ l]
    rfl
  · by_cases hb : s = I.b₀
    · subst hb
      rw [hf, I.tup_b₀, TestFun.truncateₗ_of_supportedOn I.hG]
    · by_cases hsa : s = I.a
      · subst hsa
        apply Subtype.ext
        rw [hs _ I.a_not_mem_range, I.tup_a, TestFun.truncateₗ_ind]
        rfl
      · apply Subtype.ext
        rw [hs _ (not_mem_range_of h hb), I.tup_out (subset_refl _) _ _ (not_mem_range_of h hb) hsa]
        rfl

/-- **The main estimate for the instance**: for the tuple `f` of (2.1) at `(σ', 𝐐, g)`,
`|Λ(f)| ≤ (A θ + C) ∏_j ‖f_j‖_{p_j}` with `θ = (1−ε)^{1/p_k} < 1` and the constant `C` of the
stopping data, i.e. the contraction `A ≤ A θ + C` at the extremal pair (p. 43), under the
hypothesis `1/p_k + 1/p_{k+1} ≤ 1` (always true for a Hölder tuple). [PROVED] -/
theorem abs_form_le
    (hF : 0 < ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
      lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j))
    (hG0 : 0 < lpNorm (I.G : (Fin d → ℝ) → ℝ) (p.p I.b₀))
    (hrq : 1 / p.p I.a + 1 / p.p I.b₀ ≤ 1) (f : Fin n → TestFun d) (hf : f I.b₀ = I.G)
    (hl : ∀ l : Fin k, (f (I.σ₀ l.castSucc) : (Fin d → ℝ) → ℝ) =
      truncate I.Q₀ (restrictFamily C b I.σ₀ I.Q l))
    (hs : ∀ s, s ∉ Set.range I.σ₀ → (f s : (Fin d → ℝ) → ℝ) = I.Q₀.indicator) :
    |T.form f| ≤ (I.A * (I.data hF hG0).θc + (I.data hF hG0).Cstep hrq) * prodNorm p f := by
  have h : |twoSlotForm T I.a I.b₀ I.frozen I.Q₀ (TestFun.ind I.Q₀) I.G| ≤
      (I.A * (I.data hF hG0).θc + (I.data hF hG0).Cstep hrq) *
        (∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
          lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (I.G : (Fin d → ℝ) → ℝ) (p.p I.b₀) * I.Q₀.vol ^ (1 / p.p I.a) :=
    (I.data hF hG0).contraction_estimate' (I.data_GBound hF hG0) hrq
  have hprod : ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
      lpNorm (TestFun.truncateₗ I.Q₀ (I.frozen j) : (Fin d → ℝ) → ℝ) (p.p j) =
      ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀, lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j) :=
    Finset.prod_congr rfl fun j _ => by rw [I.truncateₗ_frozen j]
  rw [I.eq_tup f hf hl hs, ← I.twoSlotForm_eq_form_tup, I.prodNorm_tup, TestFun.truncateₗ_ind,
    TestFun.lpNorm_ind _ (by linarith [p.one_lt I.a]), TestFun.truncateₗ_of_supportedOn I.hG,
    hprod]
  exact h.trans (le_of_eq (by ring))

end Instance

/-! ### Degenerate instances: a vanishing entry kills the form -/

/-- `Λ(f) = 0` if some entry has `‖f_j‖_r = 0`. [PROVED] -/
theorem _root_.MirekThiele.PerfectCZForm.form_eq_zero_of_lpNorm_eq_zero (T : PerfectCZForm d n)
    (f : Fin n → TestFun d) (j : Fin n) {r : ℝ} (hr : 0 < r)
    (h : lpNorm (f j : (Fin d → ℝ) → ℝ) r = 0) : T.form f = 0 := by
  apply T.form_eq_zero_of_ae_zero f j
  have hmem := TestFun.memLp (f j).2 (ENNReal.ofReal r)
  have h0 : eLpNorm (f j : (Fin d → ℝ) → ℝ) (ENNReal.ofReal r) volume = 0 := by
    unfold lpNorm at h
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right hmem.eLpNorm_ne_top
  exact (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hr).ne').mp h0

theorem lpNorm_zero' (r : ℝ) : lpNorm (0 : (Fin d → ℝ) → ℝ) r = 0 := by
  unfold lpNorm
  rw [eLpNorm_zero, ENNReal.toReal_zero]

theorem truncate_zero (P : DyadicCube d) : truncate P (0 : (Fin d → ℝ) → ℝ) = 0 := by
  unfold truncate
  simp

/-! ### Resolution: ancestors, monotonicity in `N`, and the resolution of a test function -/

/-- A cube has a supercube of any larger scale (iterated parents). [PROVED] -/
theorem exists_superset_of_m_eq_add (T : DyadicCube d) (j : ℕ) :
    ∃ T' : DyadicCube d, T.toSet ⊆ T'.toSet ∧ T'.m = T.m + j := by
  induction j with
  | zero => exact ⟨T, subset_refl _, by simp⟩
  | succ j ih =>
    obtain ⟨T', hT, hm⟩ := ih
    refine ⟨T'.parent, hT.trans T'.subset_parent, ?_⟩
    rw [DyadicCube.parent_m, hm]
    push_cast
    ring

/-- **The ancestor at a given scale**: a cube `T ⊆ Q₀` lies in a cube `T' ⊆ Q₀` of any scale
between `ℓ(T)` and `ℓ(Q₀)`. [PROVED] -/
theorem exists_superset_of_le {T Q₀ : DyadicCube d} (hTQ : T.toSet ⊆ Q₀.toSet) {s : ℤ}
    (hTs : T.m ≤ s) (hsQ : s ≤ Q₀.m) :
    ∃ T' : DyadicCube d, T.toSet ⊆ T'.toSet ∧ T'.m = s ∧ T'.toSet ⊆ Q₀.toSet := by
  obtain ⟨T', hT, hm⟩ := exists_superset_of_m_eq_add T (s - T.m).toNat
  have hm' : T'.m = s := by
    rw [hm, Int.toNat_of_nonneg (by omega)]
    ring
  refine ⟨T', hT, hm', ?_⟩
  rcases DyadicCube.subset_or_disjoint T' Q₀ (by rw [hm']; exact hsQ) with h | h
  · exact h
  · exact absurd (hTQ T.corner_mem) (Set.disjoint_left.mp h (hT T.corner_mem))

theorem constOn_of_subset {f : (Fin d → ℝ) → ℝ} {T T' : DyadicCube d} (h : T.toSet ⊆ T'.toSet)
    (hf : ConstOn f T') : ConstOn f T :=
  fun x hx y hy => hf x (h hx) y (h hy)

/-- Constancy on the leaves at scale `N` implies constancy on the leaves at any finer scale
`N' ≥ N`. [PROVED] -/
theorem constOn_leaves_mono {f : (Fin d → ℝ) → ℝ} {Q₀ : DyadicCube d} {N N' : ℕ} (hN : N ≤ N')
    (h : ∀ T : DyadicCube d, T.toSet ⊆ Q₀.toSet → T.m = Q₀.m - N → ConstOn f T) :
    ∀ T : DyadicCube d, T.toSet ⊆ Q₀.toSet → T.m = Q₀.m - N' → ConstOn f T := by
  intro T hTQ hTm
  obtain ⟨T', hTT', hm', hT'Q⟩ :=
    exists_superset_of_le hTQ (s := Q₀.m - N) (by rw [hTm]; omega) (by omega)
  exact constOn_of_subset hTT' (h T' hT'Q hm')

/-- **Every dyadic test function has finite resolution relative to `Q₀`**: it is a finite
combination of cube indicators, and a cube of scale at most the scale of all these cubes is
contained in or disjoint from each of them. [PROVED] -/
theorem exists_resolution (f : TestFun d) (Q₀ : DyadicCube d) :
    ∃ N : ℕ, ∀ T : DyadicCube d, T.toSet ⊆ Q₀.toSet → T.m = Q₀.m - N →
      ConstOn (f : (Fin d → ℝ) → ℝ) T := by
  have hf : (f : (Fin d → ℝ) → ℝ) ∈
      Submodule.span ℝ (Set.range (DyadicCube.indicator (d := d))) := f.2
  obtain ⟨M, c, g, hsum⟩ := Submodule.mem_span_set'.mp hf
  choose P hP using fun i => Set.mem_range.mp (g i).2
  refine ⟨∑ i, (Q₀.m - (P i).m).toNat, fun T _ hTm x hx y hy => ?_⟩
  rw [← hsum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hP i]
  have h1 : (Q₀.m - (P i).m).toNat ≤ ∑ j, (Q₀.m - (P j).m).toNat :=
    Finset.single_le_sum (f := fun j => (Q₀.m - (P j).m).toNat) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 := Int.self_le_toNat (Q₀.m - (P i).m)
  have hm : T.m ≤ (P i).m := by omega
  rcases DyadicCube.subset_or_disjoint T (P i) hm with h | h
  · rw [DyadicCube.indicator, Set.indicator_of_mem (h hx), Set.indicator_of_mem (h hy),
      Pi.one_apply, Pi.one_apply]
  · rw [DyadicCube.indicator, Set.indicator_of_notMem (Set.disjoint_left.mp h hx),
      Set.indicator_of_notMem (Set.disjoint_left.mp h hy)]

/-! ### Uniformity of `θ` and `C` over the slots

The constants `θ = (1−ε)^{1/r}` and `C` of the stopping data depend only on `B`, `p`, the slots
`a, b` and the number `m` of auxiliary functions; over the finitely many slot pairs they are
bounded by their maximum. -/

/-- `θ` depends only on `B`, `p` and the slot `a`. [PROVED] -/
theorem θc_congr {D D' : StoppingData d n} (hB : D.B = D'.B) (hp : D.p = D'.p) (ha : D.a = D'.a) :
    D.θc = D'.θc := by
  cases D
  cases D'
  dsimp only at hB hp ha
  subst hB hp ha
  rfl

/-- `C` depends only on `B`, `p`, the slots `a, b` and `m`. [PROVED] -/
theorem Cstep_congr {D D' : StoppingData d n} (hB : D.B = D'.B) (hp : D.p = D'.p) (ha : D.a = D'.a)
    (hb : D.b = D'.b) (hm : D.m = D'.m) (hrq : 1 / D.r + 1 / D.q ≤ 1)
    (hrq' : 1 / D'.r + 1 / D'.q ≤ 1) : D.Cstep hrq = D'.Cstep hrq' := by
  cases D
  cases D'
  dsimp only at hB hp ha hb hm
  subst hB hp ha hb hm
  rfl

/-- The contraction factors of all stopping data with the parameters `B`, `p` and `m = 1`. -/
def thetaSet (p : HolderTuple n) (B : ℝ) : Set ℝ :=
  {x | ∃ D : StoppingData d n, D.B = B ∧ D.p = p ∧ D.m = 1 ∧ x = D.θc}

/-- The constants `C` of all stopping data with the parameters `B`, `p` and `m = 1`. -/
def CSet (p : HolderTuple n) (B : ℝ) : Set ℝ :=
  {x | ∃ (D : StoppingData d n) (hrq : 1 / D.r + 1 / D.q ≤ 1),
    D.B = B ∧ D.p = p ∧ D.m = 1 ∧ x = D.Cstep hrq}

theorem thetaSet_finite (p : HolderTuple n) (B : ℝ) : (thetaSet (d := d) p B).Finite := by
  refine Set.Finite.subset (Set.finite_iUnion fun ab : Fin n × Fin n =>
    Set.Subsingleton.finite (s := {x | ∃ D : StoppingData d n,
      D.B = B ∧ D.p = p ∧ D.a = ab.1 ∧ x = D.θc}) ?_) ?_
  · rintro x ⟨D, hB, hp, ha, rfl⟩ y ⟨D', hB', hp', ha', rfl⟩
    exact θc_congr (hB.trans hB'.symm) (hp.trans hp'.symm) (ha.trans ha'.symm)
  · rintro x ⟨D, hB, hp, -, rfl⟩
    exact Set.mem_iUnion.mpr ⟨(D.a, D.b), D, hB, hp, rfl, rfl⟩

theorem CSet_finite (p : HolderTuple n) (B : ℝ) : (CSet (d := d) p B).Finite := by
  refine Set.Finite.subset (Set.finite_iUnion fun ab : Fin n × Fin n =>
    Set.Subsingleton.finite (s := {x | ∃ (D : StoppingData d n) (hrq : 1 / D.r + 1 / D.q ≤ 1),
      D.B = B ∧ D.p = p ∧ D.m = 1 ∧ D.a = ab.1 ∧ D.b = ab.2 ∧ x = D.Cstep hrq}) ?_) ?_
  · rintro x ⟨D, hrq, hB, hp, hm, ha, hb, rfl⟩ y ⟨D', hrq', hB', hp', hm', ha', hb', rfl⟩
    exact Cstep_congr (hB.trans hB'.symm) (hp.trans hp'.symm) (ha.trans ha'.symm)
      (hb.trans hb'.symm) (hm.trans hm'.symm) hrq hrq'
  · rintro x ⟨D, hrq, hB, hp, hm, rfl⟩
    exact Set.mem_iUnion.mpr ⟨(D.a, D.b), D, hrq, hB, hp, hm, rfl, rfl, rfl⟩

/-- **The uniform contraction factor** `θ`: the maximum of the factors over the slots. -/
noncomputable def θu (p : HolderTuple n) (B : ℝ) : ℝ := sSup (thetaSet (d := d) p B)

/-- **The uniform constant** `C₁`: the maximum of the constants `C` over the slots. -/
noncomputable def C₁u (p : HolderTuple n) (B : ℝ) : ℝ := max 0 (sSup (CSet (d := d) p B))

theorem θu_nonneg (p : HolderTuple n) (B : ℝ) : 0 ≤ θu (d := d) p B := by
  by_cases hne : (thetaSet (d := d) p B).Nonempty
  · obtain ⟨D, -, -, -, hx⟩ := hne.csSup_mem (thetaSet_finite p B)
    rw [θu, hx]
    exact D.θc_nonneg
  · rw [θu, Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]

theorem θu_lt_one (p : HolderTuple n) (B : ℝ) : θu (d := d) p B < 1 := by
  by_cases hne : (thetaSet (d := d) p B).Nonempty
  · obtain ⟨D, -, -, -, hx⟩ := hne.csSup_mem (thetaSet_finite p B)
    rw [θu, hx]
    exact D.θc_lt_one
  · rw [θu, Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact one_pos

theorem θc_le_θu (D : StoppingData d n) (hB : D.B = B) (hp : D.p = p) (hm : D.m = 1) :
    D.θc ≤ θu (d := d) p B :=
  le_csSup (thetaSet_finite p B).bddAbove ⟨D, hB, hp, hm, rfl⟩

theorem C₁u_nonneg (p : HolderTuple n) (B : ℝ) : 0 ≤ C₁u (d := d) p B := le_max_left _ _

theorem Cstep_le_C₁u (D : StoppingData d n) (hrq : 1 / D.r + 1 / D.q ≤ 1) (hB : D.B = B)
    (hp : D.p = p) (hm : D.m = 1) : D.Cstep hrq ≤ C₁u (d := d) p B :=
  (le_csSup (CSet_finite p B).bddAbove ⟨D, hrq, hB, hp, hm, rfl⟩).trans (le_max_right _ _)

/-- For two different slots, `1/p_a + 1/p_b ≤ 1` (the other exponents contribute nonnegatively to
`∑ 1/p_j = 1`). [PROVED] -/
theorem holder_pair_le_one (p : HolderTuple n) {a b : Fin n} (hab : a ≠ b) :
    1 / p.p a + 1 / p.p b ≤ 1 := by
  have hsum := p.sum_inv
  have hb' : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ hb']
    at hsum
  have hnn : 0 ≤ ∑ j ∈ (Finset.univ.erase a).erase b, (p.p j)⁻¹ :=
    Finset.sum_nonneg fun j _ => inv_nonneg.mpr (by linarith [p.one_lt j])
  rw [one_div, one_div]
  linarith

end Bridge

end Bridge

end MirekThiele
