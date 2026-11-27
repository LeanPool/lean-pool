/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.SplinePeriodic
public import LeanPool.FunctionSpaces.Domains.Interval.SplineJackson

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson's inequality for splines on the circle and the coincidence theorem

For `1 ≤ p < ∞` and `r ≥ 1`, the error of best approximation in `L_p(𝕋) = L_p[0, 1]` by periodic
splines of order `r` and level `k ≥ r` is bounded by the periodic modulus of smoothness,
`E_{2^k}(f)_p ≤ C ω_r^per(f, 2^(-k))_p` (`Interval.exists_approxError_perSplineScheme_le`).

* **The periodic quasi-interpolant.** For a `1`-periodic `G`, the quasi-interpolant of
  `FunctionSpaces.Domains.Interval.QuasiInterp` on `[0, 2)` repeats itself away from `0`: its
  coefficients repeat (`Interval.qiCoeff_add_two_pow`), since the local projections of `G` on
  `I_{k,m}` and on `I_{k,m+2^k} = I_{k,m} + 1` are translates, and so do its pieces
  (`Interval.qiPieces_add_two_pow_comp`). Its pieces on `[1, 2)`, moved to `[0, 1)`
  (`Interval.perQiPieces`), form a periodic spline once `r ≤ 2^k`
  (`Interval.perJoin_perQiPieces`).
* **Jackson's inequality for continuous periodic functions.** On `[1, 2)` the quasi-interpolant
  has the local error estimates of the interval case (`Interval.eLpNorm_sub_perQiPieces_eq`), on
  windows inside `[0, 2]` (`Interval.qiWindow_subset_Icc_zero_two`). One Steklov
  smoothing of `G` on `[0, 2]`, with the modulus on `[0, 3]`, gives polynomials on all windows,
  and `ω_r(G, t, [0, 3])_p ≤ 3^(1/p) ω_r^per(G, t)_p` (`Interval.modulus_perExt_le`). Hence
  `‖G - Q_k^per G‖_p ≤ C ω_r^per(G, 2^(-k))_p` (`Interval.exists_eLpNorm_sub_perQi_le`).
* **Density.** The continuous periodic functions are dense in `L_p[0, 1]`, `p < ∞`
  (`Interval.dense_periodic`): a bounded continuous function, cut off near `0` and `1`, extends
  periodically.

With the inverse inequality of order `r - 1 + 1/p` (`Interval.exists_inverse_perSplineScheme`)
the periodic modulus is compatible with the periodic spline scheme
(`Interval.perSplineModulusData`), and for `1 ≤ q ≤ ∞` and `0 ≤ s < r - 1 + 1/p`,
`f ∈ A^s_q ↔ ‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
(`Interval.memApprox_perSplineScheme_iff`): the approximation space of the periodic splines of
order `r` is `B^s_{p,q}(𝕋)` for `0 < s < r - 1 + 1/p`.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction
open ENNReal (dyadicWeight)

namespace Interval

/-! ### Shifts by one period -/

/-- **The local coefficients of a periodic function repeat**: for `1`-periodic `g`, the
coefficients of the local projections on `I_{j,m+2^j} = I_{j,m} + 1` and on `I_{j,m}` agree. -/
theorem locCoeff_add_two_pow {g : ℝ → ℂ} (hg : Function.Periodic g 1) (r j m : ℕ) (i : Fin r) :
    locCoeff r j g (m + 2 ^ j) i = locCoeff r j g m i := by
  rw [locCoeff, locCoeff, integral_dyadicIco_eq, integral_dyadicIco_eq]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  have h2 : (2 : ℝ) ^ j ≠ 0 := by positivity
  have e1 : t / 2 ^ j + ((m + 2 ^ j : ℕ) : ℝ) / 2 ^ j = t / 2 ^ j + (m : ℝ) / 2 ^ j + 1 := by
    push_cast
    field_simp
    ring
  have e2 : -((m + 2 ^ j : ℕ) : ℝ) + 2 ^ j * (t / 2 ^ j + (m : ℝ) / 2 ^ j + 1) =
      -(m : ℝ) + 2 ^ j * (t / 2 ^ j + (m : ℝ) / 2 ^ j) := by
    push_cast
    ring
  simp only [e1, hg (t / 2 ^ j + (m : ℝ) / 2 ^ j), e2]

/-- **The local projections of a periodic function are translates**: for `1`-periodic `g`,
`Π_{I_{j,m+2^j}} g = (Π_{I_{j,m}} g)(· - 1)`. -/
theorem locProj_add_two_pow {g : ℝ → ℂ} (hg : Function.Periodic g 1) (r j m : ℕ) :
    locProj r j g (m + 2 ^ j) = (locProj r j g m).comp (X - C 1) := by
  rw [locProj, locProj, sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [locCoeff_add_two_pow hg, smul_comp, comp_assoc]
  congr 2
  refine Polynomial.funext fun z => ?_
  simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_C, eval_X]
  push_cast
  ring

/-- The rescaled local projections of a periodic function are translates by `2^k`. -/
theorem locProjScaled_add_two_pow {g : ℝ → ℂ} (hg : Function.Periodic g 1) (r k m : ℕ) :
    locProjScaled r k g (m + 2 ^ k) =
      (locProjScaled r k g m).comp (X - C (((2 ^ k : ℤ) : ℤ) : ℂ)) := by
  rw [locProjScaled, locProjScaled, locProj_add_two_pow hg, comp_assoc, comp_assoc]
  congr 1
  refine Polynomial.funext fun z => ?_
  have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_C, eval_X]
  push_cast
  field_simp
  ring

/-- **B-spline coefficients of translates**: `c_{n+a}(P(· - a)) = c_n(P)` for `a ∈ ℤ`. -/
theorem bsplineCoef_comp_sub {r : ℕ} (hr : 1 ≤ r) (P : ℂ[X]) (n a : ℤ) :
    bsplineCoef hr (P.comp (X - C (a : ℂ))) (n + a) = bsplineCoef hr P n := by
  rw [bsplineCoef, bsplineCoef, comp_assoc]
  congr 2
  refine Polynomial.funext fun z => ?_
  simp only [eval_comp, eval_add, eval_sub, eval_C, eval_X]
  push_cast
  ring

/-- **The quasi-interpolant coefficients of a periodic function repeat**: for `1`-periodic `g`
and `n ≥ 0`, `λ_{n+2^k}(g) = λ_n(g)`. -/
theorem qiCoeff_add_two_pow {r : ℕ} (hr : 1 ≤ r) {g : ℝ → ℂ} (hg : Function.Periodic g 1)
    (k : ℕ) {n : ℤ} (hn : 0 ≤ n) : qiCoeff hr k g (n + 2 ^ k) = qiCoeff hr k g n := by
  have htoNat : (n + 2 ^ k).toNat = n.toNat + 2 ^ k := by
    rw [show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; ring]
    generalize 2 ^ k = M
    omega
  rw [qiCoeff, qiCoeff, htoNat, locProjScaled_add_two_pow hg, bsplineCoef_comp_sub]

/-- **Translates of the B-spline pieces**: the pieces of `N_r(2^k x - (n + 2^k))` on
`I_{k,m+2^k}`, moved by `1`, are those of `N_r(2^k x - n)` on `I_{k,m}`. -/
theorem bsplinePieces_add_two_pow_comp (r k : ℕ) (n : ℤ) (m : ℕ) :
    (bsplinePieces r k (n + 2 ^ k) (m + 2 ^ k)).comp (X + C 1) = bsplinePieces r k n m := by
  have h : ((m + 2 ^ k : ℕ) : ℤ) - (n + 2 ^ k) = (m : ℤ) - n := by push_cast; ring
  unfold bsplinePieces
  rw [h]
  split_ifs
  · rw [comp_assoc]
    congr 1
    refine Polynomial.funext fun z => ?_
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    push_cast
    ring
  · rw [zero_comp]

/-- **The pieces of the quasi-interpolant of a periodic function repeat**: for `1`-periodic `g`,
`r ≤ i + 1` and `i + 2^k < N`, `Q_{i+2^k}(· + 1) = Q_i`, since only the coefficients `λ_n`,
`n > i - r ≥ -1`, enter. -/
theorem qiPieces_add_two_pow_comp {r : ℕ} (hr : 1 ≤ r) {g : ℝ → ℂ} (hg : Function.Periodic g 1)
    {k N i : ℕ} (hri : r ≤ i + 1) (hiN : i + 2 ^ k < N) :
    (qiPieces hr k N g (i + 2 ^ k)).comp (X + C 1) = qiPieces hr k N g i := by
  rw [qiPieces_eq_sum_Ioc hr k hiN, qiPieces_eq_sum_Ioc hr k (lt_of_le_of_lt (Nat.le_add_right i
    _) hiN),
    sum_comp]
  have hIoc : Finset.Ioc (((i + 2 ^ k : ℕ) : ℤ) - r) ((i + 2 ^ k : ℕ) : ℤ) =
      (Finset.Ioc ((i : ℤ) - r) i).map (addRightEmbedding (2 ^ k)) := by
    rw [Finset.map_add_right_Ioc]
    congr 1
    push_cast
    ring
  rw [hIoc, Finset.sum_map]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  rw [addRightEmbedding_apply, mul_comp, C_comp, qiCoeff_add_two_pow hr hg k (by omega),
    bsplinePieces_add_two_pow_comp]

/-! ### The periodic quasi-interpolant -/

/-- The pieces of the **periodic quasi-interpolant** of level `k`: the pieces on `[1, 2)` of the
quasi-interpolant on `[0, 2)` (`N = 2^(k+1)`), moved to `[0, 1)`. -/
noncomputable def perQiPieces {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (g : ℝ → ℂ) (m : ℕ) : ℂ[X] :=
  (qiPieces hr k (2 ^ (k + 1)) g (m + 2 ^ k)).comp (X + C 1)

/-- The periodic quasi-interpolant has pieces of degree `< r`. -/
theorem perQiPieces_mem {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (g : ℝ → ℂ) (m : ℕ) :
    perQiPieces hr k g m ∈ degreeLT ℂ r :=
  comp_X_add_C_mem (qiPieces_mem hr k _ g _) 1

/-- The values of the periodic quasi-interpolant: `Q_k^per g(x) = Q_k g(x + 1)`. -/
theorem polyFun_perQiPieces {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (g : ℝ → ℂ) (m : ℕ) (x : ℝ) :
    polyFun (perQiPieces hr k g m) x =
      polyFun (qiPieces hr k (2 ^ (k + 1)) g (m + 2 ^ k)) (x + 1) := by
  simp only [perQiPieces, polyFun, eval_comp, eval_add, eval_X, eval_C]
  push_cast
  rfl

/-- **The periodic quasi-interpolant is a spline on `[0, 1]`**: its joins are those of the
quasi-interpolant at the knots of `[1, 2)`. -/
theorem splineJoins_perQiPieces {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (g : ℝ → ℂ) :
    SplineJoins r k (perQiPieces hr k g) := fun m hm _ => by
  obtain ⟨c, hc⟩ := qiPieces_join hr k (2 ^ (k + 1)) g (m := m + 2 ^ k) (by omega)
  refine ⟨c, ?_⟩
  rw [perQiPieces, perQiPieces, show m - 1 + 2 ^ k = m + 2 ^ k - 1 by omega, ← sub_comp, hc,
    mul_comp, C_comp]
  congr 1
  refine Polynomial.funext fun z => ?_
  simp only [eval_comp, eval_pow, eval_sub, eval_add, eval_X, eval_C]
  congr 1
  push_cast
  field_simp
  ring

/-- **The periodic quasi-interpolant joins across `0 = 1`** for `1`-periodic `g` and `r ≤ 2^k`:
its last piece is the piece of the quasi-interpolant on `[1 - 2^(-k), 1)`, by the periodicity of
the pieces, and its first piece, moved back to `[1, 1 + 2^(-k))`, the piece there. -/
theorem perJoin_perQiPieces {r : ℕ} (hr : 1 ≤ r) {g : ℝ → ℂ} (hg : Function.Periodic g 1)
    {k : ℕ} (hrk : r ≤ 2 ^ k) : PerJoin r k (perQiPieces hr k g) := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  obtain ⟨c, hc⟩ := qiPieces_join hr k (2 ^ (k + 1)) g (m := 2 ^ k) (by positivity)
  refine ⟨c, ?_⟩
  have hlast : perQiPieces hr k g (2 ^ k - 1) = qiPieces hr k (2 ^ (k + 1)) g (2 ^ k - 1) :=
    qiPieces_add_two_pow_comp hr hg (by omega) (by rw [pow_succ]; omega)
  have hfirst : (perQiPieces hr k g 0).comp (X - C 1) = qiPieces hr k (2 ^ (k + 1)) g (2 ^ k) := by
    rw [perQiPieces, zero_add, comp_assoc,
      show (X + C 1 : ℂ[X]).comp (X - C 1) = X by simp, comp_X]
  rw [hlast, hfirst, hc]
  congr 3
  push_cast
  field_simp

/-! ### Jackson's inequality for continuous periodic functions -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Translation of a local norm by one period**: `‖f(· + 1)‖_{L_p(I_{k,m})} =
‖f‖_{L_p(I_{k,m+2^k})}`. -/
theorem eLpNorm_comp_add_one_dyadicIco {f : ℝ → ℂ} (hf : Measurable f) (p : ℝ≥0∞) (k m : ℕ) :
    eLpNorm (fun x => f (x + 1)) p (volume.restrict (dyadicIco k m)) =
      eLpNorm f p (volume.restrict (dyadicIco k (m + 2 ^ k))) := by
  rw [dyadicIco, dyadicIco, Measure.restrict_congr_set Ico_ae_eq_Icc,
    Measure.restrict_congr_set Ico_ae_eq_Icc, eLpNorm_comp_add_Icc hf]
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  congr 3
  · push_cast
    field_simp
  · push_cast
    field_simp
    ring

/-- **The windows of the cells of `[0, 2)` lie in `[0, 2]`**: `W_{k,i} ⊆ [0, 2]` for
`i < 2^(k+1)`. -/
theorem qiWindow_subset_Icc_zero_two {r k i : ℕ} (hi : i < 2 ^ (k + 1)) :
    qiWindow r k i ⊆ Icc 0 2 := fun x hx => by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  refine ⟨(by positivity : (0 : ℝ) ≤ ((i + 1 - r : ℕ) : ℝ) / 2 ^ k).trans hx.1, hx.2.trans ?_⟩
  rw [div_le_iff₀ hpos]
  have : ((i + 1 : ℕ) : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast hi
  push_cast at this
  rw [pow_succ] at this
  linarith

/-- **The periodic quasi-interpolant is the quasi-interpolant one period to the right**: for
continuous `1`-periodic `G`, the error of `Q_k^per G` on `I_{k,m}` equals the error of the
quasi-interpolant on `[0, 2)` on `I_{k,m+2^k} = I_{k,m} + 1`. -/
theorem eLpNorm_sub_perQiPieces_eq {r : ℕ} (hr : 1 ≤ r) {G : ℝ → ℂ} (hG : Continuous G)
    (hGp : Function.Periodic G 1) (p : ℝ≥0∞) (k m : ℕ) :
    eLpNorm (fun x => G x - polyFun (perQiPieces hr k G m) x) p
        (volume.restrict (dyadicIco k m)) =
      eLpNorm (fun x => G x - polyFun (qiPieces hr k (2 ^ (k + 1)) G (m + 2 ^ k)) x) p
        (volume.restrict (dyadicIco k (m + 2 ^ k))) := by
  rw [← eLpNorm_comp_add_one_dyadicIco (f := fun x => G x -
    polyFun (qiPieces hr k (2 ^ (k + 1)) G (m + 2 ^ k)) x)
    (hG.measurable.sub (measurable_polyFun _)) p k m]
  congr 1
  funext x
  simp only [polyFun_perQiPieces]
  rw [hGp x]

/-- **Jackson's inequality for periodic splines, continuous functions**: there is `C` with
`‖G - Q_k^per G‖_{L_p[0,1]} ≤ C ω_r^per(G, 2^(-k))_p` for every continuous `1`-periodic `G` and
every `k`. -/
theorem exists_eLpNorm_sub_perQi_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ G : ℝ → ℂ, Continuous G → Function.Periodic G 1 → ∀ k : ℕ,
      eLpNorm (fun x => G x - ppFun k (perQiPieces hr k G) x) p unitVol ≤
        C * perModulus r p G (1 / 2 ^ k) := by
  obtain ⟨A, hA, hAb⟩ := exists_sum_eLpNorm_sub_qiPieces_le_of_taylor (p := p) hr hp
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  set J := 1 + (r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))
  have hJ : J ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))
    (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))⟩
  refine ⟨A * J * 3 ^ (1 / p.toReal), ENNReal.mul_ne_top (ENNReal.mul_ne_top hA hJ)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)), fun G hG hGp k => ?_⟩
  set ω := modulus r p 0 3 G (1 / 2 ^ k)
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hL : (0 : ℝ) < 1 / 2 ^ k := by positivity
  have hwL : (2 : ℝ) + 1 / 2 ^ k ≤ 3 := by
    have : (1 : ℝ) / 2 ^ k ≤ 1 := by
      rw [div_le_one hpos]
      exact one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨g, D, hgm, hDm, h1, h2, h3⟩ := exists_left_smoothing hG hr hp1 hp hL hwL
  set s := (Finset.range (2 ^ k)).map (addRightEmbedding (2 ^ k))
  have hs : s ⊆ Finset.range (2 ^ (k + 1)) := by
    intro i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.1 hi
    rw [Finset.mem_range] at hm ⊢
    rw [addRightEmbedding_apply, pow_succ]
    omega
  have hmain : eLpNorm (fun x => G x - ppFun k (perQiPieces hr k G) x) p unitVol ≤
      A * (J * ω) := by
    refine eLpNorm_le_of_lintegral_le ((hG.measurable.sub
      (measurable_ppFun _ _)).aestronglyMeasurable) hp0 hp ?_
    calc ∫⁻ x, ‖G x - ppFun k (perQiPieces hr k G) x‖ₑ ^ p.toReal ∂unitVol
        ≤ ∑ m ∈ Finset.range (2 ^ k), eLpNorm (fun x => G x -
            polyFun (perQiPieces hr k G m) x) p (volume.restrict (dyadicIco k m)) ^ p.toReal :=
          lintegral_sub_ppFun_le_sum hp hG.measurable k _
      _ = ∑ i ∈ s, eLpNorm (fun x => G x - polyFun (qiPieces hr k (2 ^ (k + 1)) G i) x) p
            (volume.restrict (dyadicIco k i)) ^ p.toReal := by
          rw [Finset.sum_map]
          exact Finset.sum_congr rfl fun m _ =>
            congrArg (· ^ p.toReal) (eLpNorm_sub_perQiPieces_eq hr hG hGp p k m)
      _ ≤ (A * (eLpNorm (fun x => G x - g x) p (volume.restrict (Icc 0 2)) +
            ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r * eLpNorm D p (volume.restrict (Icc 0 2)))) ^
              p.toReal :=
          hAb hs (fun i hi => qiWindow_subset_Icc_zero_two (Finset.mem_range.1 (hs hi)))
            hG.measurable (fun m _ => integrableOn_dyadicIco_of_continuous hG k m) hgm hDm h3
      _ ≤ (A * (J * ω)) ^ p.toReal := by
          gcongr
          exact add_ofReal_div_pow_mul_le r k h1 h2
  have hω : ω ≤ 3 ^ (1 / p.toReal) * perModulus r p G (1 / 2 ^ k) := by
    have h := modulus_perExt_le hG.measurable hp0 hp r 3 (1 / 2 ^ k)
    rw [perExt_eq_of_periodic hGp] at h
    simp only [Nat.cast_ofNat] at h
    exact h
  calc eLpNorm (fun x => G x - ppFun k (perQiPieces hr k G) x) p unitVol
      ≤ A * (J * ω) := hmain
    _ ≤ A * (J * (3 ^ (1 / p.toReal) * perModulus r p G (1 / 2 ^ k))) := by gcongr
    _ = _ := by ring

/-! ### Density of the continuous periodic functions -/

/-- A continuous **cut-off** vanishing at `0` and `1`, `φ_δ(x) = min(1, max(0, min(x, 1 - x)/δ))`,
with values in `[0, 1]` and equal to `1` on `[δ, 1 - δ]`. -/
noncomputable def cutoff (δ x : ℝ) : ℝ := min 1 (max 0 (min x (1 - x) / δ))

/-- The cut-off is continuous. -/
theorem continuous_cutoff (δ : ℝ) : Continuous (cutoff δ) :=
  continuous_const.min (continuous_const.max
    ((continuous_id.min (continuous_const.sub continuous_id)).div_const δ))

/-- The cut-off vanishes at `0`. -/
theorem cutoff_zero (δ : ℝ) : cutoff δ 0 = 0 := by simp [cutoff]

/-- The cut-off vanishes at `1`. -/
theorem cutoff_one (δ : ℝ) : cutoff δ 1 = 0 := by simp [cutoff]

/-- The cut-off is nonnegative. -/
theorem cutoff_nonneg (δ x : ℝ) : 0 ≤ cutoff δ x := le_min zero_le_one (le_max_left _ _)

/-- The cut-off is at most `1`. -/
theorem cutoff_le_one (δ x : ℝ) : cutoff δ x ≤ 1 := min_le_left _ _

/-- The cut-off is `1` on `[δ, 1 - δ]`. -/
theorem cutoff_eq_one {δ x : ℝ} (hδ : 0 < δ) (h1 : δ ≤ x) (h2 : x ≤ 1 - δ) : cutoff δ x = 1 := by
  have h : 1 ≤ min x (1 - x) / δ := by
    rw [le_div_iff₀ hδ, one_mul]
    exact le_min h1 (by linarith)
  exact min_eq_left (h.trans (le_max_right _ _))

/-- **Continuous periodic functions are dense in `L_p[0, 1]`**, `p < ∞`: for a bounded continuous
`G` (dense by Mathlib's `BoundedContinuousFunction.toLp_denseRange`), the cut-off `φ_δ G` vanishes
at `0` and `1` and so extends to a continuous periodic function (`ContinuousOn.comp_fract''`), and
`‖G - φ_δ G‖_p ≤ ‖‖G‖_∞ 1_{[0, δ] ∪ [1 - δ, 1]}‖_p`, which is small for small `δ`
(`MeasureTheory.exists_eLpNorm_indicator_le`). -/
theorem dense_periodic (hp : p ≠ ∞) :
    Dense {f : Lp ℂ p unitVol | ∃ G : ℝ → ℂ, Continuous G ∧ Function.Periodic G 1 ∧
      (f : ℝ → ℂ) =ᵐ[unitVol] G} := by
  refine Metric.dense_iff.2 fun f ε hε => ?_
  obtain ⟨G, hG⟩ := Metric.denseRange_iff.1
    (BoundedContinuousFunction.toLp_denseRange ℂ unitVol ℝ hp) f (ε / 2) (by positivity)
  obtain ⟨η, hη0, hη⟩ := exists_eLpNorm_indicator_le (μ := unitVol) hp (‖G‖ : ℝ)
    (ε := ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.2 (by positivity)).ne'
  set δ : ℝ := min ((η : ℝ) / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  set F : ℝ → ℂ := fun x => (cutoff δ x : ℂ) * G x
  have hFc : Continuous F :=
    (Complex.continuous_ofReal.comp (continuous_cutoff δ)).mul G.continuous
  set Gp : ℝ → ℂ := F ∘ Int.fract
  have hGpc : Continuous Gp :=
    ContinuousOn.comp_fract'' hFc.continuousOn (by simp [F, cutoff_zero, cutoff_one])
  have hGpp : Function.Periodic Gp 1 := fun x => by simp [Gp, Int.fract_add_one]
  have hbound : ∀ x, ‖Gp x‖ ≤ ‖G‖ := fun x => by
    simp only [Gp, F, Function.comp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutoff_nonneg _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans
      (G.norm_coe_le_norm _)
  have hmem : MemLp Gp p unitVol :=
    MemLp.of_bound hGpc.aestronglyMeasurable ‖G‖ (Filter.Eventually.of_forall hbound)
  refine ⟨hmem.toLp Gp, ?_, ⟨Gp, hGpc, hGpp, hmem.coeFn_toLp⟩⟩
  -- the cut-off changes `G` only near `0` and `1`
  set S : Set ℝ := Icc (0 : ℝ) δ ∪ Icc (1 - δ) 1
  have hS : MeasurableSet S := measurableSet_Icc.union measurableSet_Icc
  have hSμ : unitVol S ≤ η := by
    calc unitVol S ≤ volume S := Measure.restrict_apply_le _ _
      _ ≤ volume (Icc (0 : ℝ) δ) + volume (Icc (1 - δ) 1) := measure_union_le _ _
      _ = ENNReal.ofReal (2 * δ) := by
          rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith)
            (by linarith)]
          congr 1
          ring
      _ ≤ η := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (by linarith [min_le_left ((η : ℝ) / 2) (1 / 2)])
  have hpt : ∀ᵐ x ∂unitVol, ‖(G : ℝ → ℂ) x - Gp x‖ ≤ ‖S.indicator (fun _ => ‖G‖) x‖ := by
    filter_upwards [ae_mem_Ico_unitVol] with x hx
    have hsub : (G : ℝ → ℂ) x - Gp x = ((1 - cutoff δ x : ℝ) : ℂ) * G x := by
      simp only [Gp, F, Function.comp, Int.fract_eq_self.2 hx]
      push_cast
      ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [cutoff_le_one δ x])]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS, norm_norm]
      calc (1 - cutoff δ x) * ‖G x‖ ≤ 1 * ‖G‖ :=
            mul_le_mul (by linarith [cutoff_nonneg δ x]) (G.norm_coe_le_norm x) (norm_nonneg _)
              zero_le_one
        _ = ‖G‖ := one_mul _
    · have h1 : δ < x := by
        by_contra h
        exact hxS (Or.inl ⟨hx.1, not_lt.1 h⟩)
      have h2 : x < 1 - δ := by
        by_contra h
        exact hxS (Or.inr ⟨not_lt.1 h, hx.2.le⟩)
      rw [cutoff_eq_one hδ h1.le h2.le, sub_self, zero_mul]
      exact norm_nonneg _
  have hdist : dist (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ G) (hmem.toLp Gp) ≤
      ε / 4 := by
    rw [Lp.dist_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    rw [eLpNorm_congr_ae ((BoundedContinuousFunction.coeFn_toLp (E := ℂ) p unitVol ℝ G).sub
      hmem.coeFn_toLp)]
    exact (eLpNorm_mono_ae (G.continuous.sub hGpc).aestronglyMeasurable hpt).trans
      (hη S hSμ hS.nullMeasurableSet)
  rw [Metric.mem_ball]
  calc dist (hmem.toLp Gp) f
      ≤ dist (hmem.toLp Gp) (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ G) +
          dist (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ G) f := dist_triangle _ _ _
    _ < ε / 4 + ε / 2 := by
        rw [dist_comm (hmem.toLp Gp), dist_comm _ f]
        exact add_lt_add_of_le_of_lt hdist hG
    _ ≤ ε := by linarith

/-! ### Jackson's inequality in `L_p` and the coincidence theorem -/

/-- **Jackson's inequality for periodic splines**: for `1 ≤ p < ∞` and `r ≥ 1` there is `C_J`
with `E_{2^k}(f)_p ≤ C_J ω_r^per(f, 2^(-k))_p` for all `f ∈ L_p(𝕋)` and all `k ≥ r`; the levels
`k ≥ r` have `r ≤ 2^k`, so that the periodic quasi-interpolant is a periodic spline. General `f`
follow by density of the continuous periodic functions
(`ApproximationScheme.approxError_le_of_dense`). -/
theorem exists_approxError_perSplineScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p unitVol) (k : ℕ), r ≤ k →
      (perSplineScheme p r).approxError f (2 ^ k) ≤ CJ * lpPerModulus p r f k := by
  obtain ⟨C, hC, hCb⟩ := exists_eLpNorm_sub_perQi_le hr hp
  refine ⟨C, hC, fun f k hk => ?_⟩
  have hrk : r ≤ 2 ^ k := hk.trans Nat.lt_two_pow_self.le
  refine ApproximationScheme.approxError_le_of_dense (dense_periodic hp)
    (fun f g => lpPerModulus_add_le r f g k) (C0 := 2 ^ r) (by simp)
    (fun f => lpPerModulus_le hp r f k) hC ?_ f
  rintro g ⟨G, hGc, hGp, hgG⟩
  have ha : (memLp_ppFun k (perQiPieces hr k G) p).toLp _ ∈ perSplineScheme p r (2 ^ k) :=
    mem_perSplineScheme_two_pow.2 ⟨perQiPieces hr k G, perQiPieces_mem hr k G,
      splineJoins_perQiPieces hr k G, perJoin_perQiPieces hr hGp hrk, MemLp.coeFn_toLp _⟩
  refine (ApproximationScheme.approxError_le_of_mem ha g).trans ?_
  rw [Lp.eNorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (hgG.sub (MemLp.coeFn_toLp _))),
    lpPerModulus, perModulus_congr_ae hgG]
  exact hCb G hGc hGp k

/-- The periodic modulus `ω_r^per(f, 2^(-k))_p` is compatible with the scheme of periodic dyadic
splines of order `r`, with inverse order `θ = r - 1 + 1/p` and Jackson's inequality from level `r`
on. -/
noncomputable def perSplineModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (perSplineScheme p r) (((r - 1 : ℕ) : ℝ) + 1 / p.toReal) :=
  .ofExists (lpPerModulus p r) (lpPerModulus_add_le r) (2 ^ r) (by simp) (lpPerModulus_le hp r) r
    (exists_approxError_perSplineScheme_le hr hp) (exists_inverse_perSplineScheme hp)

/-- **Approximation by periodic dyadic splines.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and
`0 ≤ s < r - 1 + 1/p`, an `f ∈ L_p(𝕋) = L_p[0, 1]` lies in the approximation space `A^s_q` of the
periodic splines of order `r` on dyadic partitions iff its periodic Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q}` is finite. -/
theorem memApprox_perSplineScheme_iff {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) (f : Lp ℂ p unitVol) :
    (perSplineScheme p r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p r f k) < ∞ := by
  have hθ : (r : ℝ) - 1 + 1 / p.toReal = ((r - 1 : ℕ) : ℝ) + 1 / p.toReal := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  exact (perSplineModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs (hθ ▸ hsr) f

end Interval
