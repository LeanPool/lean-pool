/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.IsoInverse
public import LeanPool.FunctionSpaces.Domains.Cube.PiecewiseInverse
public import LeanPool.FunctionSpaces.Domains.Cube.SplineInverse

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Approximation spaces on the cube and the isotropic modulus

The approximation spaces of the piecewise polynomials and of the tensor splines on the cube
`Q = [0, 1]^d` are the Besov spaces defined by the **isotropic** modulus as well
(`Cube.memApprox_cubePPScheme_iff_iso`, `Cube.memApprox_cubeSplineScheme_iff_iso`). Jackson's
inequality carries over from the coordinate moduli (`Cube.lpCubeModulus_le_lpIsoModulus`); the
inverse inequality comes from the bound of the isotropic difference by the gains in the single
coordinates (`Cube.eLpNorm_higherDiff_le_of_exponents`), applied to the one-dimensional classes of
the slices (`Cube.ppSubmodule`, `Cube.splineSubmodule`):

* piecewise polynomials: the gain `(2^j |t|)^(1/p)` for every difference of order `m ≥ 1`
  (`Interval.exists_eLpNorm_higherDiff_ppFun_le`), so every word of total order `r ≥ 1` gains
  `(2^j ‖h‖)^(1/p)` (`Cube.le_sum_ppExponent`);
* splines of order `r`: the gain `(2^j |t|)^m` for `m < r`
  (`Interval.exists_eLpNorm_higherDiff_spline_le_of_lt`) and `(2^j |t|)^(r - 1 + 1/p)` for
  `m = r` (`Interval.eLpNorm_higherDiff_ppFun_spline_le`), so
  every word gains `(2^j ‖h‖)^(r - 1 + 1/p)` (`Cube.le_sum_splineExponent`): either one
  coordinate carries all `r` differences, or all coordinates carry fewer and their orders add up
  to `r ≥ r - 1 + 1/p`.

As a consequence, the Besov conditions with the coordinate moduli and with the isotropic modulus
agree for `0 ≤ s < r - 1 + 1/p` (`Cube.lqNorm_cubeModulus_lt_top_iff_iso`): both describe the
approximation space of the tensor splines of order `r`.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff)
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Cube

open Interval

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The classes of the slices -/

/-- The **piecewise polynomials** of level `j` and degree `< r` on `[0, 1)`, as a subspace of the
functions on `ℝ`. -/
noncomputable def ppSubmodule (r j : ℕ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {u | ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧ u = ppFun j Q}
  add_mem' := by
    rintro _ _ ⟨Q, hQ, rfl⟩ ⟨Q', hQ', rfl⟩
    exact ⟨Q + Q', fun n => Submodule.add_mem _ (hQ n) (hQ' n), (ppFun_add j Q Q').symm⟩
  zero_mem' := ⟨0, fun _ => Submodule.zero_mem _, (ppFun_zero j).symm⟩
  smul_mem' := by
    rintro c _ ⟨Q, hQ, rfl⟩
    refine ⟨fun n => C c * Q n, fun n => ?_, ?_⟩
    · change C c * Q n ∈ degreeLT ℂ r
      rw [← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (hQ n)
    · rw [ppFun_const_mul]
      rfl

/-- The **splines** of order `r` and level `j` on `[0, 1)`, as a subspace of the functions on
`ℝ`. -/
noncomputable def splineSubmodule (r j : ℕ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {u | ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧ SplineJoins r j Q ∧
    u = ppFun j Q}
  add_mem' := by
    rintro _ _ ⟨Q, hQ, hJ, rfl⟩ ⟨Q', hQ', hJ', rfl⟩
    exact ⟨Q + Q', fun n => Submodule.add_mem _ (hQ n) (hQ' n), hJ.add hJ',
      (ppFun_add j Q Q').symm⟩
  zero_mem' := ⟨0, fun _ => Submodule.zero_mem _, splineJoins_zero r j, (ppFun_zero j).symm⟩
  smul_mem' := by
    rintro c _ ⟨Q, hQ, hJ, rfl⟩
    refine ⟨fun n => C c * Q n, fun n => ?_, hJ.const_mul c, ?_⟩
    · change C c * Q n ∈ degreeLT ℂ r
      rw [← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (hQ n)
    · rw [ppFun_const_mul]
      rfl

omit [Fact (1 ≤ p)] in
/-- The slices of a piecewise polynomial on the cube are piecewise polynomials. -/
theorem IsCubePP.slice_mem_ppSubmodule {r j : ℕ} {g : (Fin d → ℝ) → ℂ} (hg : IsCubePP r j g)
    (i : Fin d) (x : Fin d → ℝ) : slice g x i ∈ ppSubmodule r j := by
  obtain ⟨Q, hQ, hs⟩ := hg.exists_slice_eq_ppFun i x
  exact ⟨Q, hQ, hs⟩

omit [Fact (1 ≤ p)] in
/-- The slices of a spline on the cube are splines. -/
theorem IsCubeSpline.slice_mem_splineSubmodule {r j : ℕ} {g : (Fin d → ℝ) → ℂ}
    (hg : IsCubeSpline r j g) (i : Fin d) (x : Fin d → ℝ) : slice g x i ∈ splineSubmodule r j :=
  hg.2 i x

/-! ### The exponents of the gains -/

variable (p) in
/-- The gain exponent of a difference of order `m` of piecewise polynomials: `0` for `m = 0`,
`1/p` otherwise. -/
noncomputable def ppExponent (m : ℕ) : ℝ := if m = 0 then 0 else 1 / p.toReal

variable (p) in
/-- The gain exponent of a difference of order `m` of splines of order `r`: `m` for `m < r`,
`r - 1 + 1/p` for `m = r`. -/
noncomputable def splineExponent (r m : ℕ) : ℝ :=
  if m < r then m else ((r - 1 : ℕ) : ℝ) + 1 / p.toReal

omit [Fact (1 ≤ p)] in
/-- The gain exponents of piecewise polynomials are nonnegative. -/
theorem ppExponent_nonneg (m : ℕ) : 0 ≤ ppExponent p m := by
  unfold ppExponent
  split_ifs <;> positivity

omit [Fact (1 ≤ p)] in
/-- The gain exponents of splines are nonnegative. -/
theorem splineExponent_nonneg (r m : ℕ) : 0 ≤ splineExponent p r m := by
  unfold splineExponent
  split_ifs <;> positivity

omit [Fact (1 ≤ p)] in
/-- **Every word of positive order gains `1/p` for piecewise polynomials**: if `∑_i m_i = r ≥ 1`,
some `m_i ≥ 1`. -/
theorem le_sum_ppExponent {r : ℕ} (hr : 1 ≤ r) (m : Fin d → ℕ) (hm : ∑ i, m i = r) :
    1 / p.toReal ≤ ∑ i, ppExponent p (m i) := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hm
    omega
  calc 1 / p.toReal = ppExponent p (m i) := by simp [ppExponent, hi]
    _ ≤ ∑ i, ppExponent p (m i) :=
        Finset.single_le_sum (f := fun i => ppExponent p (m i))
          (fun i _ => ppExponent_nonneg _) (Finset.mem_univ i)

/-- **Every word of order `r` gains `r - 1 + 1/p` for splines of order `r`**: either one
coordinate carries all `r` differences, or all orders are `< r` and add up to `r`. -/
theorem le_sum_splineExponent {r : ℕ} (hr : 1 ≤ r) (m : Fin d → ℕ) (hm : ∑ i, m i = r) :
    ((r - 1 : ℕ) : ℝ) + 1 / p.toReal ≤ ∑ i, splineExponent p r (m i) := by
  have hle : ∀ i, m i ≤ r := fun i => hm ▸ Finset.single_le_sum (f := m)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  by_cases h : ∃ i, m i = r
  · obtain ⟨i, hi⟩ := h
    calc ((r - 1 : ℕ) : ℝ) + 1 / p.toReal = splineExponent p r (m i) := by
          simp [splineExponent, hi]
      _ ≤ ∑ i, splineExponent p r (m i) :=
          Finset.single_le_sum (f := fun i => splineExponent p r (m i))
            (fun i _ => splineExponent_nonneg _ _) (Finset.mem_univ i)
  · push Not at h
    have hlt : ∀ i, m i < r := fun i => lt_of_le_of_ne (hle i) (h i)
    have hsum : ∑ i, splineExponent p r (m i) = r := by
      simp only [splineExponent, hlt, ↓reduceIte]
      exact_mod_cast hm
    have h1p : 1 / p.toReal ≤ 1 := by
      rcases eq_or_ne p ∞ with hpinf | hpinf
      · simp [hpinf]
      · have h := ENNReal.one_le_toReal_of_one_le Fact.out hpinf
        exact (div_le_one (by linarith)).2 h
    rw [hsum, Nat.cast_sub hr, Nat.cast_one]
    linarith

/-! ### Differences of every order in one variable, for steps of either sign -/

/-- **Piecewise polynomials, steps of either sign**: there is `C` such that for every level `j`,
every piecewise polynomial `u` of level `j` and degree `< r`, every order `m ≤ r` and
`|t| ≤ 2^(-j)`, `‖Δ_t^m u‖_{L_p(J(m,t))} ≤ C (2^j |t|)^{θ_m} ‖u‖_p` with the exponent
`θ_m = Cube.ppExponent p m`. -/
theorem exists_eLpNorm_higherDiff_stepRegion_pp_le (r : ℕ) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ j : ℕ, ∀ u ∈ ppSubmodule r j, ∀ m ≤ r, ∀ t : ℝ, |t| ≤ 1 / 2 ^ j →
      eLpNorm (higherDiff m t u) p (volume.restrict (stepRegion m t)) ≤
        C * ENNReal.ofReal (2 ^ j * |t|) ^ ppExponent p m * eLpNorm u p unitVol := by
  classical
  have hex : ∀ m : ℕ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ (1 ≤ m → m ≤ r → ∀ (j : ℕ) (Q : ℕ → ℂ[X]),
      (∀ n, Q n ∈ degreeLT ℂ r) → ∀ {h : ℝ}, 0 ≤ h → h ≤ 1 / 2 ^ j →
        eLpNorm (higherDiff m h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - m * h))) ≤
          C * ENNReal.ofReal (2 ^ j * h) ^ (1 / p.toReal) * eLpNorm (ppFun j Q) p unitVol) :=
    fun m => by
      by_cases hm : 1 ≤ m ∧ m ≤ r
      · obtain ⟨C, hC, hb⟩ := exists_eLpNorm_higherDiff_ppFun_le (p := p) hm.1 hm.2 hp
        exact ⟨C, hC, fun _ _ => hb⟩
      · exact ⟨0, ENNReal.zero_ne_top, fun h1 h2 => absurd ⟨h1, h2⟩ hm⟩
  choose Cm hCm hCmb using hex
  refine ⟨1 + ∑ m ∈ Finset.range (r + 1), Cm m, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.sum_ne_top.2 fun m _ => hCm m⟩, fun j u hu m hmr t ht => ?_⟩
  obtain ⟨Q, hQ, rfl⟩ := hu
  rw [eLpNorm_higherDiff_stepRegion_eq (ppFun j Q) p m t]
  have hCle : Cm m ≤ 1 + ∑ m ∈ Finset.range (r + 1), Cm m :=
    le_add_left (Finset.single_le_sum (f := Cm) (fun _ _ => zero_le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hmr)))
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [ppExponent, ↓reduceIte, ENNReal.rpow_zero, mul_one, higherDiff_zero,
      Nat.cast_zero, zero_mul, sub_zero]
    exact le_mul_of_one_le_left zero_le le_self_add
  · have hb := hCmb m hm hmr j Q hQ (abs_nonneg t) ht
    simp only [ppExponent, show m ≠ 0 by omega, ↓reduceIte]
    exact hb.trans (by gcongr)

/-- **Splines, steps of either sign**: there is `C` such that for every level `j`, every spline
`u` of order `r` and level `j`, every order `m ≤ r` and `|t| ≤ 2^(-j)`,
`‖Δ_t^m u‖_{L_p(J(m,t))} ≤ C (2^j |t|)^{θ_m} ‖u‖_p` with the exponent
`θ_m = Cube.splineExponent p r m`. -/
theorem exists_eLpNorm_higherDiff_stepRegion_spline_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ j : ℕ, ∀ u ∈ splineSubmodule r j, ∀ m ≤ r, ∀ t : ℝ,
      |t| ≤ 1 / 2 ^ j →
        eLpNorm (higherDiff m t u) p (volume.restrict (stepRegion m t)) ≤
          C * ENNReal.ofReal (2 ^ j * |t|) ^ splineExponent p r m * eLpNorm u p unitVol := by
  classical
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  have hex : ∀ m : ℕ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ (1 ≤ m → m < r → ∀ (j : ℕ) (Q : ℕ → ℂ[X]),
      (∀ n, Q n ∈ degreeLT ℂ r) → SplineJoins r j Q → ∀ {h : ℝ}, 0 ≤ h → h ≤ 1 / 2 ^ j →
        eLpNorm (higherDiff m h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - m * h))) ≤
          C * ENNReal.ofReal (2 ^ j * h) ^ m * eLpNorm (ppFun j Q) p unitVol) :=
    fun m => by
      by_cases hm : 1 ≤ m ∧ m < r
      · obtain ⟨C, hC, hb⟩ := exists_eLpNorm_higherDiff_spline_le_of_lt (p := p) hm.1 hm.2 hp
        exact ⟨C, hC, fun _ _ => hb⟩
      · exact ⟨0, ENNReal.zero_ne_top, fun h1 h2 => absurd ⟨h1, h2⟩ hm⟩
  choose Cm hCm hCmb using hex
  set C := 1 + ∑ m ∈ Finset.range (r + 1), Cm m + splineInverseConst r K p
  refine ⟨C, ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.sum_ne_top.2 fun m _ => hCm m⟩, splineInverseConst_ne_top r hK⟩,
    fun j u hu m hmr t ht => ?_⟩
  obtain ⟨Q, hQ, hJ, rfl⟩ := hu
  rw [eLpNorm_higherDiff_stepRegion_eq (ppFun j Q) p m t]
  have hCle : Cm m ≤ C := le_add_right (le_add_left (Finset.single_le_sum (f := Cm)
    (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hmr))))
  rcases lt_or_eq_of_le hmr with hmr' | rfl
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [splineExponent, hmr', ↓reduceIte, Nat.cast_zero, ENNReal.rpow_zero, mul_one,
        higherDiff_zero, zero_mul, sub_zero]
      exact le_mul_of_one_le_left zero_le (le_add_right le_self_add)
    · have hb := hCmb m hm hmr' j Q hQ hJ (abs_nonneg t) ht
      simp only [splineExponent, hmr', ↓reduceIte, ENNReal.rpow_natCast]
      exact hb.trans (by gcongr)
  · have hb := eLpNorm_higherDiff_ppFun_spline_le hQ hJ hKb hp (abs_nonneg t) ht
    rw [splineStripConst_mul_eq m j K |t|] at hb
    simp only [splineExponent, lt_irrefl, ↓reduceIte]
    exact hb.trans (by gcongr; exact le_add_self)

/-! ### The inverse inequalities with the isotropic modulus -/

/-- **The inverse inequality for piecewise polynomials on the cube with the isotropic
modulus**, of order `θ = 1/p`. -/
theorem exists_inverse_cubePPScheme_iso {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ cubePPScheme p d r (2 ^ j),
      lpIsoModulus p r a k ≤ CB * dyadicWeight (-(1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨C, hC, hCb⟩ := exists_eLpNorm_higherDiff_stepRegion_pp_le (p := p) r hp
  refine ⟨(d : ℝ≥0∞) ^ r * C ^ d + 2 ^ r, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top d)) (ENNReal.pow_ne_top hC), by simp⟩,
    fun j k a ha => ?_⟩
  obtain ⟨g, hg, hae⟩ := mem_cubePPScheme_two_pow.1 ha
  exact lpIsoModulus_le_of_exponents (ppSubmodule r j) hp r (ppExponent p) ppExponent_nonneg
    (by positivity) (fun m hm => le_sum_ppExponent hr m hm) (hCb j) hg.1.1
    (fun i x => hg.slice_mem_ppSubmodule i x) hae

/-- **The inverse inequality for tensor splines on the cube with the isotropic modulus**, of
order `θ = r - 1 + 1/p`. -/
theorem exists_inverse_cubeSplineScheme_iso {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ cubeSplineScheme p d r (2 ^ j),
      lpIsoModulus p r a k ≤
        CB * dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨C, hC, hCb⟩ := exists_eLpNorm_higherDiff_stepRegion_spline_le (p := p) hr hp
  refine ⟨(d : ℝ≥0∞) ^ r * C ^ d + 2 ^ r, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top d)) (ENNReal.pow_ne_top hC), by simp⟩,
    fun j k a ha => ?_⟩
  obtain ⟨g, hg, hae⟩ := mem_cubeSplineScheme_two_pow.1 ha
  exact lpIsoModulus_le_of_exponents (splineSubmodule r j) hp r (splineExponent p r)
    (splineExponent_nonneg r) (by positivity) (fun m hm => le_sum_splineExponent hr m hm) (hCb j)
    hg.1.1 (fun i x => hg.slice_mem_splineSubmodule i x) hae

/-! ### The coincidence theorems -/

/-- The **isotropic modulus** `ω_r(f, 2^(-k))_p` on the cube is compatible with the scheme of
piecewise polynomials, with inverse order `θ = 1/p` and Jackson's inequality at every level. -/
noncomputable def cubePPIsoModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (cubePPScheme p d r) (1 / p.toReal) :=
  .ofExists (lpIsoModulus p r) (lpIsoModulus_add_le r) (2 ^ r) (by simp) (lpIsoModulus_le r) 0
    (by
      obtain ⟨CJ, hCJ, h⟩ := exists_approxError_cubePPScheme_le (d := d) (p := p) hr hp
      exact ⟨CJ * d, ENNReal.mul_ne_top hCJ (ENNReal.natCast_ne_top d), fun f k _ =>
        (h f k).trans (by
          rw [mul_assoc]
          exact mul_le_mul' le_rfl (lpCubeModulus_le_lpIsoModulus r f k))⟩)
    (exists_inverse_cubePPScheme_iso hr hp)

/-- **Piecewise polynomials on the cube and the isotropic modulus.** For `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < 1/p`, an `f ∈ L_p([0, 1]^d)` lies in the approximation space
`A^s_q` of the piecewise polynomials of degree `< r` in each variable iff
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` with the isotropic modulus `ω_r`. -/
theorem memApprox_cubePPScheme_iff_iso {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p (cubeVol d)) :
    (cubePPScheme p d r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpIsoModulus p r f k) < ∞ :=
  (cubePPIsoModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs hsp f

/-- The **isotropic modulus** `ω_r(f, 2^(-k))_p` on the cube is compatible with the scheme of
tensor splines of order `r`, with inverse order `θ = r - 1 + 1/p`. -/
noncomputable def cubeSplineIsoModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (cubeSplineScheme p d r) (((r - 1 : ℕ) : ℝ) + 1 / p.toReal) :=
  .ofExists (lpIsoModulus p r) (lpIsoModulus_add_le r) (2 ^ r) (by simp) (lpIsoModulus_le r) 0
    (by
      obtain ⟨CJ, hCJ, h⟩ := exists_approxError_cubeSplineScheme_le (d := d) (p := p) hr hp
      exact ⟨CJ * d, ENNReal.mul_ne_top hCJ (ENNReal.natCast_ne_top d), fun f k _ =>
        (h f k).trans (by
          rw [mul_assoc]
          exact mul_le_mul' le_rfl (lpCubeModulus_le_lpIsoModulus r f k))⟩)
    (exists_inverse_cubeSplineScheme_iso hr hp)

/-- **Tensor splines on the cube and the isotropic modulus.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`r ≥ 1` and `0 ≤ s < r - 1 + 1/p`, an `f ∈ L_p([0, 1]^d)` lies in the approximation space
`A^s_q` of the tensor splines of order `r` iff
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` with the isotropic modulus `ω_r`. -/
theorem memApprox_cubeSplineScheme_iff_iso {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 ≤ s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    (f : Lp ℂ p (cubeVol d)) :
    (cubeSplineScheme p d r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpIsoModulus p r f k) < ∞ := by
  have hθ : (r : ℝ) - 1 + 1 / p.toReal = ((r - 1 : ℕ) : ℝ) + 1 / p.toReal := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  exact (cubeSplineIsoModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs (hθ ▸ hsr) f

/-- **The coordinate and the isotropic Besov conditions agree on the cube**: for `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < r - 1 + 1/p`,
`‖f‖_p + ‖(2^(ks) ω_r^cube(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff the same holds with the isotropic
modulus; both say that `f` lies in the approximation space of the tensor splines of order `r`. -/
theorem lqNorm_cubeModulus_lt_top_iff_iso {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 ≤ s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    (f : Lp ℂ p (cubeVol d)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpCubeModulus p r f k) < ∞ ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpIsoModulus p r f k) < ∞ :=
  (memApprox_cubeSplineScheme_iff hr hp hq hs hsr f).symm.trans
    (memApprox_cubeSplineScheme_iff_iso hr hp hq hs hsr f)

end Cube
