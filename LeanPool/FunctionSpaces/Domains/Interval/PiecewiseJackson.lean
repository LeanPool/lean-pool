/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.PiecewisePoly
public import LeanPool.FunctionSpaces.Domains.Interval.Whitney
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson's inequality for dyadic piecewise polynomials

For `1 ≤ p < ∞`, `r ≥ 1` and `k ≥ 1`, the error of best approximation in `L_p[0, 1]` by
piecewise polynomials of level `k` and degree `< r` is bounded by the modulus of smoothness,
`E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k), [0, 1])_p`
(`Interval.approxError_ppScheme_le`). At level `0` the approximants are the polynomials of degree
`< r`, and Whitney's inequality of `FunctionSpaces.Domains.Interval.Whitney` gives the bound there
(`Interval.exists_approxError_ppScheme_one_le`), so Jackson's inequality holds at every level
(`Interval.exists_approxError_ppScheme_le`).

For `k ≥ 1` the proof needs no Whitney theorem. For continuous `f`, the Steklov smoothing of
`Interval.exists_left_smoothing` is close to `f`, its `r`-th derivative is bounded by `2^(kr)`
times the modulus, and on each dyadic interval it is approximated by a Taylor polynomial
(`Interval.exists_taylor_pieces`). The smoothing looks to the right of `x`, so it serves
`[0, 1/2]`; its reflection `Interval.exists_right_smoothing` serves `[1/2, 1]`. The Taylor
polynomials of both halves form one piecewise polynomial
(`Interval.exists_ppFun_approx_of_taylor`, stated for any function and any two smoothings, so
that the slices of functions on the cube use it too). The point `1/2` is a knot of every level
`k ≥ 1`, which is why `k ≥ 1` in this part of the argument. General `f ∈ L_p` follow by density
of bounded continuous functions (`Interval.approxError_le_of_continuous`, which serves every scheme
in `L_p[0, 1]`).

The modulus of elements of `L_p[0, 1]` at the dyadic scales (`Interval.lpModulus`) is defined for
every `p`; for `0 < p ≤ 1` its `p`-th power is subadditive and it is at most `2^(r/p) ‖f‖_p`
(`Interval.lpModulus_add_rpow_le`, `Interval.lpModulus_le_of_le_one`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction
open ENNReal (dyadicWeight)

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The constant of the local Jackson estimate, `1 + 2^r r^(2r)`. -/
noncomputable def jacksonConst (r : ℕ) : ℝ≥0∞ := 1 + 2 ^ r * (r : ℝ≥0∞) ^ (2 * r)

/-- The local Jackson constant is finite. -/
theorem jacksonConst_ne_top (r : ℕ) : jacksonConst r ≠ ∞ := by
  unfold jacksonConst
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (by simp)
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))⟩

/-- The bound of a smoothing and of its Taylor remainders at scale `L` combine to the local
Jackson constant: `a ≤ ω` and `b ≤ L^(-r) 2^r r^(2r) ω` give `a + L^r b ≤ (1 + 2^r r^(2r)) ω`. -/
theorem add_ofReal_pow_mul_le_jacksonConst {L : ℝ} (hL : 0 < L) (r : ℕ) {a b ω : ℝ≥0∞}
    (ha : a ≤ ω) (hb : b ≤ ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω) :
    a + ENNReal.ofReal L ^ r * b ≤ jacksonConst r * ω := by
  have hLL : ENNReal.ofReal L * ENNReal.ofReal L⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hL.le, mul_inv_cancel₀ hL.ne', ENNReal.ofReal_one]
  calc a + ENNReal.ofReal L ^ r * b
      ≤ ω + ENNReal.ofReal L ^ r * (ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω) :=
        add_le_add ha (mul_le_mul' le_rfl hb)
    _ = ω + (ENNReal.ofReal L * ENNReal.ofReal L⁻¹) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω := by
        rw [mul_pow]; ring
    _ = jacksonConst r * ω := by rw [hLL, one_pow, one_mul, jacksonConst]; ring

/-- The half `[0, 1/2]` and the scale `2^(-(k+1))` fit into `[0, 1]`: `1/2 + 2^(-(k+1)) ≤ 1`. -/
theorem one_half_add_le_one (k : ℕ) : (1 / 2 : ℝ) + 1 / 2 ^ (k + 1) ≤ 1 := by
  have : (1 : ℝ) / 2 ^ (k + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- **Taylor polynomials on consecutive intervals**: let `g` have on every interval `[u, v]` a
polynomial `T` of degree `< r` with `‖g - T‖_{L_p[u, v]} ≤ (v - u)^r ‖D‖_{L_p[u, v]}`. For the
intervals `[a + nL, a + (n + 1)L]`, `n < N`, there are such polynomials `Q_n`, and every
measurable `S` equal to `Q_n` on the open intervals satisfies
`‖g - S‖_{L_p[a, a + NL]} ≤ L^r ‖D‖_{L_p[a, a + NL]}`: the `p`-th powers of the local errors add
up. -/
theorem exists_taylor_pieces {g D : ℝ → ℂ} (hg : Measurable g) (hD : Measurable D) {r : ℕ}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp' : p ≠ ∞)
    (hT : ∀ u v : ℝ, u ≤ v → ∃ T ∈ degreeLT ℂ r,
      eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc u v)) ≤
        ENNReal.ofReal (v - u) ^ r * eLpNorm D p (volume.restrict (Icc u v)))
    (a : ℝ) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧ ∀ S : ℝ → ℂ, Measurable S →
      (∀ n < N, ∀ x ∈ Ioo (a + n * L) (a + (n + 1) * L), S x = polyFun (Q n) x) →
      eLpNorm (fun x => g x - S x) p (volume.restrict (Icc a (a + N * L))) ≤
        ENNReal.ofReal L ^ r * eLpNorm D p (volume.restrict (Icc a (a + N * L))) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  choose Q hQ hQb using fun n : ℕ => hT (a + n * L) (a + (n + 1) * L) (by nlinarith)
  refine ⟨Q, hQ, fun S hS hSQ => ?_⟩
  refine eLpNorm_le_of_lintegral_le (hg.sub hS).aestronglyMeasurable hp0 hp' ?_
  refine (lintegral_Icc_le_sum (fun x => ‖g x - S x‖ₑ ^ p.toReal) a hL N).trans ?_
  have hpiece : ∀ n ∈ Finset.range N,
      ∫⁻ x in Icc (a + n * L) (a + (n + 1) * L), ‖g x - S x‖ₑ ^ p.toReal ≤
        (ENNReal.ofReal L ^ r) ^ p.toReal *
          ∫⁻ x in Icc (a + n * L) (a + (n + 1) * L), ‖D x‖ₑ ^ p.toReal := fun n hn => by
    have hae : ∀ᵐ x ∂volume.restrict (Icc (a + n * L) (a + (n + 1) * L)),
        ‖g x - S x‖ₑ ^ p.toReal = ‖g x - polyFun (Q n) x‖ₑ ^ p.toReal := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [hSQ n (Finset.mem_range.1 hn) x hx]
    rw [lintegral_congr_ae hae, ← eLpNorm_rpow_eq (g := fun x => g x - polyFun (Q n) x)
      ((hg.sub (measurable_polyFun _)).aestronglyMeasurable) hp0 hp',
      ← eLpNorm_rpow_eq hD.aestronglyMeasurable hp0 hp', ← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    have hb := hQb n
    rw [show a + (n + 1) * L - (a + n * L) = L by ring] at hb
    exact ENNReal.rpow_le_rpow hb hq.le
  refine (Finset.sum_le_sum hpiece).trans ?_
  rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    eLpNorm_rpow_eq hD.aestronglyMeasurable hp0 hp']
  gcongr
  exact sum_le_lintegral_Icc a hL N

/-- **Piecewise Taylor approximation on the two halves of `[0, 1]`**: let `g_L` and `g_R` have
Taylor polynomials of degree `< r` on every interval, with remainders controlled by `D_L` and
`D_R` as in `Interval.exists_taylor_pieces`. For every measurable `u` and every `k` there is a
piecewise polynomial `S` of level `k + 1` and degree `< r`, made of Taylor polynomials of `g_L`
on `[0, 1/2]` and of `g_R` on `[1/2, 1]`, with
`‖u - S‖_{L_p[0, 1]} ≤ (‖u - g_L‖_{L_p[0, 1/2]} + L^r ‖D_L‖_{L_p[0, 1/2]}) + (‖u -
g_R‖_{L_p[1/2, 1]} + L^r ‖D_R‖_{L_p[1/2, 1]})`,
`L = 2^(-(k+1))`. The point `1/2` is a knot of level `k + 1`. -/
theorem exists_ppFun_approx_of_taylor {u gL DL gR DR : ℝ → ℂ} (hu : Measurable u)
    (hgL : Measurable gL) (hDL : Measurable DL) (hgR : Measurable gR) (hDR : Measurable DR)
    {r : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hTL : ∀ a b : ℝ, a ≤ b → ∃ T ∈ degreeLT ℂ r,
      eLpNorm (fun x => gL x - polyFun T x) p (volume.restrict (Icc a b)) ≤
        ENNReal.ofReal (b - a) ^ r * eLpNorm DL p (volume.restrict (Icc a b)))
    (hTR : ∀ a b : ℝ, a ≤ b → ∃ T ∈ degreeLT ℂ r,
      eLpNorm (fun x => gR x - polyFun T x) p (volume.restrict (Icc a b)) ≤
        ENNReal.ofReal (b - a) ^ r * eLpNorm DR p (volume.restrict (Icc a b)))
    (k : ℕ) :
    ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧
      eLpNorm (fun x => u x - ppFun (k + 1) Q x) p unitVol ≤
        (eLpNorm (fun x => u x - gL x) p (volume.restrict (Icc 0 (1 / 2))) +
          ENNReal.ofReal (1 / 2 ^ (k + 1)) ^ r * eLpNorm DL p (volume.restrict (Icc 0 (1 / 2)))) +
        (eLpNorm (fun x => u x - gR x) p (volume.restrict (Icc (1 / 2) 1)) +
          ENNReal.ofReal (1 / 2 ^ (k + 1)) ^ r * eLpNorm DR p (volume.restrict (Icc (1 / 2) 1)))
            := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  set L : ℝ := 1 / 2 ^ (k + 1) with hLdef
  have hL : 0 < L := by positivity
  have hL2 : ((2 ^ k : ℕ) : ℝ) * L = 1 / 2 := by
    rw [hLdef]; push_cast; rw [pow_succ]; field_simp
  obtain ⟨Ql, hQl, hl⟩ := exists_taylor_pieces hgL hDL hp0 hp' hTL 0 hL.le (2 ^ k)
  obtain ⟨Qr, hQr, hrt⟩ := exists_taylor_pieces hgR hDR hp0 hp' hTR (1 / 2) hL.le (2 ^ k)
  rw [zero_add, hL2] at hl
  rw [hL2, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at hrt
  set Q : ℕ → ℂ[X] := fun m => if m < 2 ^ k then Ql m else Qr (m - 2 ^ k)
  have hQ : ∀ m, Q m ∈ degreeLT ℂ r := fun m => by
    simp only [Q]
    split_ifs
    · exact hQl m
    · exact hQr _
  refine ⟨Q, hQ, ?_⟩
  have hSm : Measurable (ppFun (k + 1) Q) := measurable_ppFun _ _
  have hleft : ∀ n : ℕ, n < 2 ^ k → ∀ x ∈ Ioo (0 + n * L) (0 + (n + 1) * L),
      ppFun (k + 1) Q x = polyFun (Ql n) x := fun n hn x hx => by
    have hn' : n < 2 ^ (k + 1) := lt_of_lt_of_le hn (Nat.pow_le_pow_right two_pos (Nat.le_succ k))
    have hmem : x ∈ dyadicIco (k + 1) n := by
      rw [hLdef, zero_add, zero_add, mul_one_div, mul_one_div] at hx
      exact Ioo_subset_Ico_self hx
    rw [ppFun_eq_of_mem Q hn' hmem]
    simp only [Q, hn, ↓reduceIte]
  have hright : ∀ n : ℕ, n < 2 ^ k → ∀ x ∈ Ioo (1 / 2 + n * L) (1 / 2 + (n + 1) * L),
      ppFun (k + 1) Q x = polyFun (Qr n) x := fun n hn x hx => by
    have hm : 2 ^ k + n < 2 ^ (k + 1) := by rw [pow_succ]; omega
    have hmem : x ∈ dyadicIco (k + 1) (2 ^ k + n) := by
      have e1 : (1 / 2 : ℝ) + n * L = ((2 ^ k + n : ℕ) : ℝ) / 2 ^ (k + 1) := by
        rw [hLdef]; push_cast; rw [pow_succ]; field_simp
      have e2 : (1 / 2 : ℝ) + (n + 1) * L = (((2 ^ k + n : ℕ) : ℝ) + 1) / 2 ^ (k + 1) := by
        rw [hLdef]; push_cast; rw [pow_succ]; field_simp; ring
      rw [e1, e2] at hx
      exact Ioo_subset_Ico_self hx
    rw [ppFun_eq_of_mem Q hm hmem]
    simp only [Q, show ¬ (2 ^ k + n < 2 ^ k) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hL' := hl _ hSm hleft
  have hR' := hrt _ hSm hright
  have hsplit : ∀ {a b : ℝ} {g : ℝ → ℂ}, Measurable g →
      eLpNorm (fun x => u x - ppFun (k + 1) Q x) p (volume.restrict (Icc a b)) ≤
        eLpNorm (fun x => u x - g x) p (volume.restrict (Icc a b)) +
          eLpNorm (fun x => g x - ppFun (k + 1) Q x) p (volume.restrict (Icc a b)) :=
    fun {a b g} _ => by
      calc eLpNorm (fun x => u x - ppFun (k + 1) Q x) p (volume.restrict (Icc a b))
          = eLpNorm ((fun x => u x - g x) + fun x => g x - ppFun (k + 1) Q x) p
              (volume.restrict (Icc a b)) := by congr 1; funext x; simp
        _ ≤ _ := eLpNorm_add_le hp
  calc eLpNorm (fun x => u x - ppFun (k + 1) Q x) p unitVol
      ≤ eLpNorm (fun x => u x - ppFun (k + 1) Q x) p (volume.restrict (Icc 0 (1 / 2))) +
          eLpNorm (fun x => u x - ppFun (k + 1) Q x) p (volume.restrict (Icc (1 / 2) 1)) :=
        eLpNorm_Icc_split (hu.sub hSm) hp hp' (by norm_num) (by norm_num)
    _ ≤ _ := add_le_add ((hsplit hgL).trans (add_le_add le_rfl hL'))
        ((hsplit hgR).trans (add_le_add le_rfl hR'))

/-- **Jackson's estimate for continuous functions**: for continuous `F` and `k ≥ 0` there is a
piecewise polynomial `S` of level `k + 1` and degree `< r` with
`‖F - S‖_{L_p[0,1]} ≤ 2 (1 + 2^r r^(2r)) ω_r(F, 2^(-(k+1)), [0, 1])_p`. The smoothings of
`Interval.exists_left_smoothing` and `Interval.exists_right_smoothing` with `L = 2^(-(k+1))`
enter `Interval.exists_ppFun_approx_of_taylor`. -/
theorem exists_ppFun_approx {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (k : ℕ) :
    ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧
      eLpNorm (fun x => F x - ppFun (k + 1) Q x) p unitVol ≤
        2 * jacksonConst r * modulus r p 0 1 F (1 / 2 ^ (k + 1)) := by
  have hL : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
  obtain ⟨gL, DL, hgL, hDL, h1L, h2L, hTL⟩ :=
    exists_left_smoothing hF hr hp hp' hL (one_half_add_le_one k)
  obtain ⟨gR, DR, hgR, hDR, h1R, h2R, hTR⟩ :=
    exists_right_smoothing hF hr hp hp' hL (one_half_add_le_one k)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h1R h2R
  obtain ⟨Q, hQ, hbound⟩ :=
    exists_ppFun_approx_of_taylor hF.measurable hgL hDL hgR hDR hp hp' hTL hTR k
  refine ⟨Q, hQ, hbound.trans ?_⟩
  rw [two_mul, add_mul]
  exact add_le_add (add_ofReal_pow_mul_le_jacksonConst hL r h1L h2L)
    (add_ofReal_pow_mul_le_jacksonConst hL r h1R h2R)

variable (p) in
/-- The modulus of an element of `L_p[0, 1]` at the dyadic scale `2^(-k)`,
`ω_r(f, 2^(-k), [0, 1])_p`. -/
noncomputable def lpModulus (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) : ℝ≥0∞ :=
  modulus r p 0 1 (f : ℝ → ℂ) (1 / 2 ^ k)

/-- The modulus of elements of `L_p[0, 1]` is subadditive. -/
theorem lpModulus_add_le (r : ℕ) (f g : Lp ℂ p unitVol) (k : ℕ) :
    lpModulus p r (f + g) k ≤ lpModulus p r f k + lpModulus p r g k := by
  rw [lpModulus, modulus_congr_ae (Lp.coeFn_add f g)]
  exact modulus_add_le Fact.out r 0 1 _ _ _

/-- `ω_r(f, t) ≤ 2^r ‖f‖_p` in `L_p[0, 1]`. -/
theorem lpModulus_le (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) :
    lpModulus p r f k ≤ 2 ^ r * ‖f‖ₑ := by
  rw [Lp.eNorm_def]
  exact modulus_le (Lp.stronglyMeasurable f).measurable Fact.out r 0 1 _

omit [Fact (1 ≤ p)] in
/-- The modulus at the dyadic scales decreases with the level. -/
theorem lpModulus_anti (r : ℕ) (f : Lp ℂ p unitVol) : Antitone (lpModulus p r f) := fun _ _ hjk =>
  modulus_mono r p 0 1 _ (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hjk))

/-- **From continuous functions to `L_p` by density**: a bound `E_n(g) ≤ C ω_r(g, 2^(-k))_p`
for every bounded continuous `g`, given by an approximant `u ∈ A_n` of `g`, holds for every
`f ∈ L_p[0, 1]`, `p < ∞`. The bounded continuous functions are dense in `L_p` (Mathlib's
`BoundedContinuousFunction.toLp_denseRange`), so `ApproximationScheme.approxError_le_of_dense`
applies. -/
theorem approxError_le_of_continuous {A : ApproximationScheme (Lp ℂ p unitVol)} (hp : p ≠ ∞)
    {r n k : ℕ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ g : ℝ →ᵇ ℂ, ∃ u : ℝ → ℂ, (∃ a ∈ A n, (a : ℝ → ℂ) =ᵐ[unitVol] u) ∧
      eLpNorm (fun x => g x - u x) p unitVol ≤ C * modulus r p 0 1 g (1 / 2 ^ k))
    (f : Lp ℂ p unitVol) : A.approxError f n ≤ C * lpModulus p r f k := by
  refine ApproximationScheme.approxError_le_of_dense
    (BoundedContinuousFunction.toLp_denseRange ℂ unitVol ℝ hp)
    (fun f g => lpModulus_add_le r f g k) (C0 := 2 ^ r) (by simp) (fun f => lpModulus_le r f k) hC
    ?_ f
  rintro _ ⟨g, rfl⟩
  obtain ⟨u, ⟨a, ha, hau⟩, hbound⟩ := h g
  have hg := BoundedContinuousFunction.coeFn_toLp (E := ℂ) p unitVol ℝ g
  refine (A.approxError_le_of_mem ha _).trans ?_
  rw [Lp.eNorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (hg.sub hau)), lpModulus,
    modulus_congr_ae hg]
  exact hbound

/-- **Jackson's inequality for dyadic piecewise polynomials**: for `1 ≤ p < ∞`, `r ≥ 1` and
`k ≥ 1`, `E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k), [0, 1])_p`; first for continuous
functions (`Interval.exists_ppFun_approx`), then by density
(`Interval.approxError_le_of_continuous`). -/
theorem approxError_ppScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) (f : Lp ℂ p unitVol) {k : ℕ}
    (hk : 1 ≤ k) :
    (ppScheme p r).approxError f (2 ^ k) ≤ 2 * jacksonConst r * lpModulus p r f k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  refine approxError_le_of_continuous hp (ENNReal.mul_ne_top (by norm_num) (jacksonConst_ne_top r))
    (fun g => ?_) f
  obtain ⟨Q, hQ, hbound⟩ := exists_ppFun_approx g.continuous hr Fact.out hp k
  exact ⟨ppFun (k + 1) Q, ⟨(memLp_ppFun (k + 1) Q p).toLp _,
    mem_ppScheme_two_pow.2 ⟨Q, hQ, MemLp.coeFn_toLp _⟩, MemLp.coeFn_toLp _⟩, hbound⟩

/-- **Whitney's inequality in `L_p[0, 1]`**: for `1 ≤ p < ∞`, `r ≥ 1` and `m ≥ 2` there is
`W < ∞` with `E_1(f)_p ≤ W ω_r(f, 2^(-m), [0, 1])_p` for every `f ∈ L_p[0, 1]`, where `E_1` is the
error of best approximation by the polynomials of degree `< r` (the approximants of
complexity `1`). -/
theorem exists_approxError_ppScheme_one_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {m : ℕ} (hm : 2 ≤ m) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ f : Lp ℂ p unitVol,
      (ppScheme p r).approxError f 1 ≤ W * lpModulus p r f m := by
  have ht : (0 : ℝ) < 1 / 2 ^ m := by positivity
  have ht3 : (1 : ℝ) / 2 ^ m ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  obtain ⟨W, hW, hWb⟩ := exists_eLpNorm_sub_polyFun_le_modulus hr hp ht ht3
  refine ⟨W, hW, fun f => approxError_le_of_continuous hp hW (fun g => ?_) f⟩
  obtain ⟨P, hP, hbound⟩ := hWb g g.continuous
  have hae : (fun x => g x - ppFun 0 (fun _ => P) x) =ᵐ[unitVol] fun x => g x - polyFun P x := by
    filter_upwards [ae_mem_Ico_unitVol] with x hx
    obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := 0) hx
    rw [ppFun_eq_of_mem _ hlt hmem]
  refine ⟨ppFun 0 (fun _ => P), ⟨(memLp_ppFun 0 (fun _ => P) p).toLp _, ?_, MemLp.coeFn_toLp _⟩,
    (eLpNorm_congr_ae hae).trans_le hbound⟩
  rw [mem_ppScheme one_ne_zero, Nat.log_one_right]
  exact ⟨fun _ => P, fun _ => hP, MemLp.coeFn_toLp _⟩

/-- **Jackson's inequality for dyadic piecewise polynomials at every level**: for `1 ≤ p < ∞` and
`r ≥ 1` there is `C_J < ∞` with `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k), [0, 1])_p` for every
`f ∈ L_p[0, 1]` and every `k ≥ 0`; level `0` is Whitney's inequality. -/
theorem exists_approxError_ppScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p unitVol) (k : ℕ),
      (ppScheme p r).approxError f (2 ^ k) ≤ CJ * lpModulus p r f k := by
  obtain ⟨W, hW, hWb⟩ := exists_approxError_ppScheme_one_le (p := p) hr hp (le_refl 2)
  refine ⟨W + 2 * jacksonConst r, ENNReal.add_ne_top.2 ⟨hW, ENNReal.mul_ne_top (by norm_num)
    (jacksonConst_ne_top r)⟩, fun f k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]
    exact (hWb f).trans (mul_le_mul' le_self_add (lpModulus_anti r f (Nat.zero_le 2)))
  · exact (approxError_ppScheme_le hr hp f hk).trans (mul_le_mul' le_add_self le_rfl)

end Interval

/-! ### The modulus of elements of `L_p[0, 1]` for `0 < p ≤ 1` -/

namespace Interval

variable {p : ℝ≥0∞}

/-- The `p`-th power of the modulus of elements of `L_p[0, 1]`, `0 < p ≤ 1`, at the dyadic scale
`2^(-k)` is subadditive. -/
theorem lpModulus_add_rpow_le (hp1 : p ≤ 1) (r : ℕ) (f g : Lp ℂ p unitVol) (k : ℕ) :
    lpModulus p r (f + g) k ^ p.toReal ≤
      lpModulus p r f k ^ p.toReal + lpModulus p r g k ^ p.toReal := by
  rw [lpModulus, modulus_congr_ae (Lp.coeFn_add f g)]
  exact modulus_add_rpow_le hp1 r 0 1 _ _ _

/-- `ω_r(f, 2^(-k), [0, 1])_p ≤ 2^(r/p) ‖f‖_p` in `L_p[0, 1]`, `0 < p ≤ 1`. -/
theorem lpModulus_le_of_le_one (hp1 : p ≤ 1) (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) :
    lpModulus p r f k ≤ 2 ^ ((r : ℝ) / p.toReal) * ‖f‖ₑ := by
  rw [Lp.eNorm_def]
  exact modulus_le_of_le_one (Lp.stronglyMeasurable f).measurable hp1 r 0 1 _

end Interval
