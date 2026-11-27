/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.QuasiInterp
public import LeanPool.FunctionSpaces.Domains.Interval.SplineInverse
public import LeanPool.FunctionSpaces.Domains.Interval.PiecewiseJackson

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson's inequality for dyadic splines and the coincidence theorem

For `1 ≤ p < ∞`, `r ≥ 1` and every level `k`, the error of best approximation in `L_p[0, 1]` by
splines of order `r` and level `k` is bounded by the modulus of smoothness,
`E_{2^k}(f)_p ≤ C ω_r(f, 2^(-k), [0, 1])_p` (`Interval.exists_approxError_splineScheme_le`).

The approximant is the quasi-interpolant `Q_k f` of `FunctionSpaces.Domains.Interval.QuasiInterp`.
On `I_{k,i}` it reproduces every polynomial `T_i` of degree `< r` and is bounded by the `L_p` norm
on the window `W_i = [(i + 1 - r) 2^(-k), (i + 1) 2^(-k)]` of `r` intervals, so
`‖f - Q_k f‖_{L_p(I_{k,i})} ≤ C ‖f - T_i‖_{L_p(W_i)}`. For continuous `f`, `T_i` is a Taylor
polynomial of the Steklov smoothing of `f`, forward on `[0, 3/4]` and backward on `[1/4, 1]`
(`Interval.exists_left_smoothing`, `Interval.exists_right_smoothing` with `L = 2^(-k)`); every
window lies in one of the two parts, and the windows overlap at most `r` times
(`Interval.sum_lintegral_window_le`). This works for `k ≥ r + 2`; general `f ∈ L_p` follow by
density (`Interval.approxError_le_of_continuous`). The coarse levels `k ≤ r + 1` need Whitney's
inequality:
`E_{2^k}(f) ≤ E_1(f)`, and the splines of level `0` are the polynomials of degree `< r`
(`Interval.approxError_splineScheme_one`), so `E_1(f) ≤ W ω_r(f, 2^(-(r+1)))_p ≤ W ω_r(f, 2^(-k))_p`
(`Interval.exists_approxError_ppScheme_one_le`).

With the inverse inequality of order `r - 1 + 1/p` (`Interval.exists_inverse_splineScheme`) this
is a modulus compatible with the spline scheme (`Interval.splineModulusData`), and for
`1 ≤ q ≤ ∞` and `0 ≤ s < r - 1 + 1/p`,
`f ∈ A^s_q ↔ ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`
(`Interval.memApprox_splineScheme_iff`): the approximation space of splines of order `r` is
`B^s_{p,q}[0, 1]` for `0 < s < r - 1 + 1/p`, beyond smoothness `1` for `r ≥ 2`.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction
open ENNReal (dyadicWeight)

namespace Interval

/-- **Bounded overlap of the windows**: the windows `[(i + 1 - r) 2^(-k), (i + 1) 2^(-k)]`,
`i < N`, cover every point at most `r` times: `∑_i ∫_{W_i} G ≤ r ∫ G`. -/
theorem sum_lintegral_window_le (r k N : ℕ) (G : ℝ → ℝ≥0∞) :
    ∑ i ∈ Finset.range N, ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k),
      G x ≤ r * ∫⁻ x, G x := by
  have hL : (0 : ℝ) ≤ 1 / 2 ^ k := by positivity
  have hwin : ∀ i : ℕ, ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), G x ≤
      ∑ n ∈ Finset.range r, ∫⁻ x in Icc ((1 - (r : ℝ) + n) / 2 ^ k + i * (1 / 2 ^ k))
        ((1 - (r : ℝ) + n) / 2 ^ k + (i + 1) * (1 / 2 ^ k)), G x := fun i => by
    have h := lintegral_Icc_le_sum G (((i : ℝ) + 1 - r) / 2 ^ k) hL r
    rw [show ((i : ℝ) + 1 - r) / 2 ^ k + r * (1 / 2 ^ k) = ((i : ℝ) + 1) / 2 ^ k by
      field_simp; ring] at h
    refine h.trans_eq (Finset.sum_congr rfl fun n _ => ?_)
    congr 2
    field_simp
    ring_nf
  calc ∑ i ∈ Finset.range N, ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k)
        (((i : ℝ) + 1) / 2 ^ k), G x
      ≤ ∑ i ∈ Finset.range N, ∑ n ∈ Finset.range r,
          ∫⁻ x in Icc ((1 - (r : ℝ) + n) / 2 ^ k + i * (1 / 2 ^ k))
            ((1 - (r : ℝ) + n) / 2 ^ k + (i + 1) * (1 / 2 ^ k)), G x :=
        Finset.sum_le_sum fun i _ => hwin i
    _ = ∑ n ∈ Finset.range r, ∑ i ∈ Finset.range N,
          ∫⁻ x in Icc ((1 - (r : ℝ) + n) / 2 ^ k + i * (1 / 2 ^ k))
            ((1 - (r : ℝ) + n) / 2 ^ k + (i + 1) * (1 / 2 ^ k)), G x := Finset.sum_comm
    _ ≤ ∑ _n ∈ Finset.range r, ∫⁻ x, G x :=
        Finset.sum_le_sum fun n _ =>
          (sum_le_lintegral_Icc _ hL N).trans (setLIntegral_le_lintegral _ _)
    _ = r * ∫⁻ x, G x := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Linearity of the quasi-interpolant -/

/-- The rescaled local projections have degree `< r`. -/
theorem locProjScaled_mem (r k : ℕ) (g : ℝ → ℂ) (m : ℕ) : locProjScaled r k g m ∈ degreeLT ℂ r :=
  comp_affine_mem_degreeLT (locProj_mem r k g m) _ _

/-- The dual polynomial `d_i` of the interval `I_{k,m}` in the coordinate `y = 2^k x`, so that
the rescaled local projection is `∑_i c_i(g) d_i(y - m)` (`Interval.locProjScaled_eq_sum`). -/
noncomputable def qiBasisPoly (r k m : ℕ) (i : Fin r) : ℂ[X] :=
  ((dualPoly r i : ℂ[X]).comp (C ((-(m : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X)).comp
    (C (((0 : ℝ) : ℝ) : ℂ) + C (((1 / 2 ^ k : ℝ) : ℝ) : ℂ) * X)

/-- These polynomials have degree `< r`. -/
theorem qiBasisPoly_mem (r k m : ℕ) (i : Fin r) : qiBasisPoly r k m i ∈ degreeLT ℂ r :=
  comp_affine_mem_degreeLT (comp_affine_mem_degreeLT (dualPoly r i).2 _ _) _ _

/-- The rescaled local projection in terms of the local coefficients. -/
theorem locProjScaled_eq_sum (r k : ℕ) (g : ℝ → ℂ) (m : ℕ) :
    locProjScaled r k g m = ∑ i, locCoeff r k g m i • qiBasisPoly r k m i := by
  rw [locProjScaled, locProj, Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.smul_comp, qiBasisPoly]

/-- **The quasi-interpolant coefficients are combinations of the local coefficients**:
`λ_n(g) = ∑_i c_i(g) β_{n,i}` with the coefficients `c_i(g)` of the local projection on `J(n)` and
the B-spline coefficients `β_{n,i}` of the rescaled dual polynomials. -/
theorem qiCoeff_eq_sum {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (g : ℝ → ℂ) (n : ℤ) :
    qiCoeff hr k g n =
      ∑ i, locCoeff r k g n.toNat i * bsplineCoef hr (qiBasisPoly r k n.toNat i) n := by
  rw [qiCoeff, locProjScaled_eq_sum, bsplineCoef_sum hr _ _ fun i _ => qiBasisPoly_mem r k _ i]

/-- **The quasi-interpolant coefficients are linear** on functions integrable on `J(n)`. -/
theorem qiCoeff_add_const_mul {r : ℕ} (hr : 1 ≤ r) (k : ℕ) {g₁ g₂ : ℝ → ℂ} (c : ℂ) {n : ℤ}
    (h₁ : IntegrableOn g₁ (dyadicIco k n.toNat)) (h₂ : IntegrableOn g₂ (dyadicIco k n.toNat)) :
    qiCoeff hr k (fun y => g₁ y + c * g₂ y) n = qiCoeff hr k g₁ n + c * qiCoeff hr k g₂ n := by
  have h₂' : IntegrableOn (fun y => c * g₂ y) (dyadicIco k n.toNat) := h₂.const_mul c
  have hloc : locProjScaled r k (fun y => g₁ y + c * g₂ y) n.toNat =
      locProjScaled r k g₁ n.toNat + C c * locProjScaled r k g₂ n.toNat := by
    rw [locProjScaled, show (fun y => g₁ y + c * g₂ y) = g₁ + fun y => c * g₂ y from rfl,
      locProj_add h₁ h₂', locProj_const_mul, add_comp, mul_comp, C_comp]
    rfl
  rw [qiCoeff, hloc, bsplineCoef_add hr (locProjScaled_mem r k _ _)
    (by rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (locProjScaled_mem r k _ _)),
    bsplineCoef_C_mul hr c (locProjScaled_mem r k _ _)]
  rfl

/-- **The error of the quasi-interpolant through a polynomial**: on `I_{k,i}`,
`g - Q_k g = (g - T) - Q_k(g - T)` for every polynomial `T` of degree `< r`. -/
theorem polyFun_qiPieces_sub {r : ℕ} (hr : 1 ≤ r) {k N i : ℕ} (hi : i < N) {g : ℝ → ℂ}
    (hg : ∀ m < N, IntegrableOn g (dyadicIco k m)) {T : ℂ[X]} (hT : T ∈ degreeLT ℂ r) {x : ℝ}
    (hx : x ∈ dyadicIco k i) :
    polyFun (qiPieces hr k N (fun y => g y - polyFun T y) i) x =
      polyFun (qiPieces hr k N g i) x - polyFun T x := by
  have hT' := polyFun_qiPieces_of_eq hr (g := polyFun T) hT hi (fun _ _ _ _ _ => rfl) hx
  rw [← hT', polyFun_qiPieces_eq_sum_Ioc hr hi _ hx, polyFun_qiPieces_eq_sum_Ioc hr hi _ hx,
    polyFun_qiPieces_eq_sum_Ioc hr hi _ hx, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have h := qiCoeff_add_const_mul hr k (-1) (n := n) (hg n.toNat (by omega))
    (integrableOn_dyadicIco_of_continuous (continuous_polyFun T) k n.toNat)
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  rw [h, sub_mul]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The window `W_i = [(i + 1 - r) 2^(-k), (i + 1) 2^(-k)]` (truncated at `0`) of the
quasi-interpolant on `I_{k,i}`. -/
noncomputable def qiWindow (r k i : ℕ) : Set ℝ := Icc (((i + 1 - r : ℕ) : ℝ) / 2 ^ k) (((i : ℝ)
  + 1) / 2 ^ k)

/-- The intervals `J(n)`, `i - r < n ≤ i`, lie in the window of `I_{k,i}`. -/
theorem dyadicIco_subset_qiWindow {r k i : ℕ} {n : ℤ} (hn : (i : ℤ) - r < n ∧ n ≤ i) :
    dyadicIco k n.toNat ⊆ qiWindow r k i := by
  intro x hx
  rw [dyadicIco, mem_Ico] at hx
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : ((i + 1 - r : ℕ) : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast (by omega : i + 1 - r ≤
    n.toNat)
  have h2 : (n.toNat : ℝ) + 1 ≤ (i : ℝ) + 1 := by exact_mod_cast (by omega : n.toNat + 1 ≤ i + 1)
  constructor
  · exact (div_le_div_of_nonneg_right h1 hpos.le).trans hx.1
  · exact hx.2.le.trans (div_le_div_of_nonneg_right h2 hpos.le)

/-- `I_{k,i}` lies in its window. -/
theorem dyadicIco_subset_qiWindow_self {r : ℕ} (hr : 1 ≤ r) (k i : ℕ) :
    dyadicIco k i ⊆ qiWindow r k i := by
  intro x hx
  rw [dyadicIco, mem_Ico] at hx
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : ((i + 1 - r : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (by omega : i + 1 - r ≤ i)
  exact ⟨(div_le_div_of_nonneg_right h1 hpos.le).trans hx.1, hx.2.le⟩

/-- `i + 1 - r ≤ (i + 1 - r : ℕ)` in `ℝ`, the natural subtraction truncating at `0`. -/
theorem natCast_add_one_sub_le (i r : ℕ) : (i : ℝ) + 1 - r ≤ ((i + 1 - r : ℕ) : ℝ) := by
  rcases le_or_gt r (i + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast; rfl
  · have : ((i + 1 : ℕ) : ℝ) < r := by exact_mod_cast h
    push_cast at this
    linarith [(Nat.cast_nonneg (i + 1 - r) : (0 : ℝ) ≤ _)]

/-- The window lies in `[(i + 1 - r) 2^(-k), (i + 1) 2^(-k)]`, with real subtraction. -/
theorem qiWindow_subset (r k i : ℕ) :
    qiWindow r k i ⊆ Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k) :=
  Icc_subset_Icc (div_le_div_of_nonneg_right (natCast_add_one_sub_le i r) (by positivity)) le_rfl

/-- **The local error of the quasi-interpolant**: for every polynomial `T` of degree `< r`,
`‖g - Q_k g‖_{L_p(I_{k,i})} ≤ (1 + r M_N C_b r M²) ‖g - T‖_{L_p(W_i)}`. -/
theorem eLpNorm_sub_qiPieces_le {r : ℕ} (hr : 1 ≤ r) {Cb : ℝ≥0∞}
    (hCb : ∀ R ∈ degreeLT ℂ r, ∀ j : ℕ,
      ‖bcoord hr R j‖ₑ ≤ Cb * eLpNorm (polyFun R) p (volume.restrict (Icc 0 1)))
    {MN : ℝ≥0∞} (hMN : ∀ y, ‖bspline r y‖ₑ ≤ MN) (hp : p ≠ ∞) {k N i : ℕ} (hi : i < N)
    {g : ℝ → ℂ} (hgm : Measurable g) (hg : ∀ m < N, IntegrableOn g (dyadicIco k m)) {T : ℂ[X]}
    (hT : T ∈ degreeLT ℂ r) :
    eLpNorm (fun x => g x - polyFun (qiPieces hr k N g i) x) p (volume.restrict (dyadicIco k i)) ≤
      (1 + r * (MN * (Cb * ppProjConst r))) *
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (qiWindow r k i)) := by
  have hp1 : 1 ≤ p := Fact.out
  set h : ℝ → ℂ := fun y => g y - polyFun T y
  have hhm : Measurable h := hgm.sub (measurable_polyFun T)
  have hfun : (fun x => g x - polyFun (qiPieces hr k N g i) x) =ᵐ[volume.restrict (dyadicIco k i)]
      fun x => h x - polyFun (qiPieces hr k N h i) x := by
    filter_upwards [ae_restrict_mem (measurableSet_dyadicIco k i)] with x hx
    simp only [h]
    rw [polyFun_qiPieces_sub hr hi hg hT hx]
    ring
  have hloc := eLpNorm_qiPieces_le hr hCb hMN hp (k := k) hi (g := h) hhm.aestronglyMeasurable
  have hcard : (Finset.Ioc ((i : ℤ) - r) i).card = r := by
    rw [Int.card_Ioc]; omega
  rw [eLpNorm_congr_ae hfun]
  calc eLpNorm (fun x => h x - polyFun (qiPieces hr k N h i) x) p (volume.restrict (dyadicIco k i))
      ≤ eLpNorm h p (volume.restrict (dyadicIco k i)) +
          eLpNorm (polyFun (qiPieces hr k N h i)) p (volume.restrict (dyadicIco k i)) :=
        eLpNorm_sub_le hp1
    _ ≤ eLpNorm h p (volume.restrict (qiWindow r k i)) + MN * (Cb * ppProjConst r) *
          ∑ _n ∈ Finset.Ioc ((i : ℤ) - r) i, eLpNorm h p (volume.restrict (qiWindow r k i)) := by
        gcongr
        · exact dyadicIco_subset_qiWindow_self hr k i
        · exact hloc.trans (by
            gcongr with n hn
            exact dyadicIco_subset_qiWindow (Finset.mem_Ioc.1 hn))
    _ = _ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        ring

/-- **Summing the local errors of the quasi-interpolant**: let `F` be measurable and integrable on
the intervals `I_{k,m}`, `m < N`, and let `s ⊆ {0, …, N - 1}`. If on the window `W_i` of every
`i ∈ s` some polynomial `T` of degree `< r` has `‖F - T‖_{L_p(W_i)}^p ≤ ∫_{W_i} H`, then
`∑_{i ∈ s} ‖F - Q_k F‖_{L_p(I_{k,i})}^p ≤ C_q^p r ∫ H` with `C_q = 1 + r M_N C_b r M²`, since the
windows overlap at most `r` times (`Interval.sum_lintegral_window_le`). -/
theorem sum_eLpNorm_sub_qiPieces_le {r : ℕ} (hr : 1 ≤ r) {Cb : ℝ≥0∞}
    (hCb : ∀ R ∈ degreeLT ℂ r, ∀ j : ℕ,
      ‖bcoord hr R j‖ₑ ≤ Cb * eLpNorm (polyFun R) p (volume.restrict (Icc 0 1)))
    {MN : ℝ≥0∞} (hMN : ∀ y, ‖bspline r y‖ₑ ≤ MN) (hp : p ≠ ∞) {k N : ℕ} {F : ℝ → ℂ}
    (hFm : Measurable F) (hF : ∀ m < N, IntegrableOn F (dyadicIco k m)) {s : Finset ℕ}
    (hs : s ⊆ Finset.range N) (H : ℝ → ℝ≥0∞)
    (hT : ∀ i ∈ s, ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => F x - polyFun T x) p
      (volume.restrict (qiWindow r k i)) ^ p.toReal ≤ ∫⁻ x in qiWindow r k i, H x) :
    ∑ i ∈ s, eLpNorm (fun x => F x - polyFun (qiPieces hr k N F i) x) p
      (volume.restrict (dyadicIco k i)) ^ p.toReal ≤
        (1 + r * (MN * (Cb * ppProjConst r))) ^ p.toReal * (r * ∫⁻ x, H x) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set Cq := 1 + r * (MN * (Cb * ppProjConst r))
  have hloc : ∀ i ∈ s, eLpNorm (fun x => F x - polyFun (qiPieces hr k N F i) x) p
      (volume.restrict (dyadicIco k i)) ^ p.toReal ≤ Cq ^ p.toReal *
        ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), H x := by
    intro i hi
    obtain ⟨T, hTm, hTb⟩ := hT i hi
    calc eLpNorm (fun x => F x - polyFun (qiPieces hr k N F i) x) p
          (volume.restrict (dyadicIco k i)) ^ p.toReal
        ≤ (Cq * eLpNorm (fun x => F x - polyFun T x) p
            (volume.restrict (qiWindow r k i))) ^ p.toReal :=
          ENNReal.rpow_le_rpow (eLpNorm_sub_qiPieces_le hr hCb hMN hp
            (Finset.mem_range.1 (hs hi)) hFm hF hTm) hq.le
      _ = Cq ^ p.toReal * eLpNorm (fun x => F x - polyFun T x) p
            (volume.restrict (qiWindow r k i)) ^ p.toReal := ENNReal.mul_rpow_of_nonneg _ _ hq.le
      _ ≤ Cq ^ p.toReal * ∫⁻ x in qiWindow r k i, H x := mul_le_mul' le_rfl hTb
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set (qiWindow_subset r k i))
  calc ∑ i ∈ s, eLpNorm (fun x => F x - polyFun (qiPieces hr k N F i) x) p
        (volume.restrict (dyadicIco k i)) ^ p.toReal
      ≤ ∑ i ∈ s, Cq ^ p.toReal *
          ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), H x :=
        Finset.sum_le_sum hloc
    _ ≤ ∑ i ∈ Finset.range N, Cq ^ p.toReal *
          ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), H x :=
        Finset.sum_le_sum_of_subset hs
    _ = Cq ^ p.toReal * ∑ i ∈ Finset.range N,
          ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), H x := by
        rw [Finset.mul_sum]
    _ ≤ Cq ^ p.toReal * (r * ∫⁻ x, H x) := mul_le_mul' le_rfl (sum_lintegral_window_le r k N H)

/-! ### Jackson's inequality for continuous functions -/

/-- **Approximation on a window**: if `‖g - T₀‖_{L_p[a,b]} ≤ (b - a)^r ‖D‖_{L_p[a,b]}` for some
polynomial `T₀` and `(b - a)^r ≤ c`, then
`‖F - T₀‖^p ≤ 2^(p-1) ∫_{[a,b]} (|F - g|^p + c^p |D|^p)`. -/
theorem exists_window_poly {F g D : ℝ → ℂ} (hFm : Measurable F) (hgm : Measurable g)
    (hDm : Measurable D) (hp : p ≠ ∞) {r : ℕ} {a b : ℝ} {c : ℝ≥0∞}
    (hT : ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) ≤
      ENNReal.ofReal (b - a) ^ r * eLpNorm D p (volume.restrict (Icc a b)))
    (hc : ENNReal.ofReal (b - a) ^ r ≤ c) :
    ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ^
      p.toReal ≤ 2 ^ (p.toReal - 1) * ∫⁻ x in Icc a b,
        (‖F x - g x‖ₑ ^ p.toReal + c ^ p.toReal * ‖D x‖ₑ ^ p.toReal) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  obtain ⟨T, hTm, hTb⟩ := hT
  refine ⟨T, hTm, ?_⟩
  have htri : eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ≤
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
        c * eLpNorm D p (volume.restrict (Icc a b)) := by
    calc eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b))
        = eLpNorm ((fun x => F x - g x) + fun x => g x - polyFun T x) p
            (volume.restrict (Icc a b)) := by congr 1; funext x; simp
      _ ≤ eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
            eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) :=
          eLpNorm_add_le hp1
      _ ≤ _ := add_le_add le_rfl (hTb.trans (by gcongr))
  calc eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ^ p.toReal
      ≤ (eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
          c * eLpNorm D p (volume.restrict (Icc a b))) ^ p.toReal :=
        ENNReal.rpow_le_rpow htri hq.le
    _ ≤ 2 ^ (p.toReal - 1) * (eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) ^
          p.toReal + (c * eLpNorm D p (volume.restrict (Icc a b))) ^ p.toReal) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq1
    _ = _ := by
        have hm1 : Measurable fun x => ‖F x - g x‖ₑ ^ p.toReal :=
          ((hFm.sub hgm).eNorm).pow_const _
        have hm2 : Measurable fun x => ‖D x‖ₑ ^ p.toReal := hDm.eNorm.pow_const _
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le,
          eLpNorm_rpow_eq (g := fun x => F x - g x) ((hFm.sub hgm).aestronglyMeasurable) hp0 hp,
          eLpNorm_rpow_eq hDm.aestronglyMeasurable hp0 hp, lintegral_add_left hm1,
          lintegral_const_mul _ hm2]

/-- **A polynomial on a window from a smoothing**: if `g` has the Taylor polynomials
`‖g - T‖_{L_p[u,v]} ≤ (v - u)^r ‖D‖_{L_p[u,v]}` on all intervals, then on the window `W_i` some
polynomial `T` of degree `< r` satisfies
`‖F - T‖_{L_p(W_i)}^p ≤ 2^(p-1) ∫_{W_i} (|F - g|^p + c^p |D|^p)` with `c = (r 2^(-k))^r`, since
`W_i` has length at most `r 2^(-k)`. -/
theorem exists_qiWindow_poly {F g D : ℝ → ℂ} (hFm : Measurable F) (hgm : Measurable g)
    (hDm : Measurable D) (hp : p ≠ ∞) {r : ℕ}
    (hT : ∀ u v : ℝ, u ≤ v → ∃ T ∈ degreeLT ℂ r,
      eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc u v)) ≤
        ENNReal.ofReal (v - u) ^ r * eLpNorm D p (volume.restrict (Icc u v))) (k i : ℕ) :
    ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => F x - polyFun T x) p
      (volume.restrict (qiWindow r k i)) ^ p.toReal ≤ 2 ^ (p.toReal - 1) *
        ∫⁻ x in qiWindow r k i, (‖F x - g x‖ₑ ^ p.toReal +
          (ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r) ^ p.toReal * ‖D x‖ₑ ^ p.toReal) := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hab : ((i + 1 - r : ℕ) : ℝ) / 2 ^ k ≤ ((i : ℝ) + 1) / 2 ^ k := by
    have : ((i + 1 - r : ℕ) : ℝ) ≤ (i : ℝ) + 1 := by
      exact_mod_cast (by omega : i + 1 - r ≤ i + 1)
    exact div_le_div_of_nonneg_right this hpos.le
  have hlen : ((i : ℝ) + 1) / 2 ^ k - ((i + 1 - r : ℕ) : ℝ) / 2 ^ k ≤ (r : ℝ) / 2 ^ k := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [natCast_add_one_sub_le i r]) hpos.le
  exact exists_window_poly hFm hgm hDm hp (hT _ _ hab)
    (pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hlen) r)

/-- **Jackson's estimate for splines from one smoothing**: there is `A < ∞` such that for every
level `k`, every `N`, every set `s ⊆ {0, …, N - 1}` of cells whose windows lie in `[a, b]`, every
measurable `u` integrable on the dyadic intervals `I_{k,m}`, `m < N`, and all measurable `g, D`
such that `g` has the Taylor polynomials `‖g - T‖_{L_p[v,w]} ≤ (w - v)^r ‖D‖_{L_p[v,w]}`,
`∑_{i ∈ s} ‖u - Q_k u‖_{L_p(I_{k,i})}^p ≤ (A (‖u - g‖_{L_p[a,b]} + c ‖D‖_{L_p[a,b]}))^p` with
`c = (r 2^(-k))^r`. On every window a Taylor polynomial of `g` approximates `u`
(`Interval.exists_qiWindow_poly`), the windows overlap at most `r` times
(`Interval.sum_eLpNorm_sub_qiPieces_le`), and `a^p + b^p ≤ (a + b)^p`. -/
theorem exists_sum_eLpNorm_sub_qiPieces_le_of_taylor {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ {k N : ℕ} {s : Finset ℕ}, s ⊆ Finset.range N → ∀ {a b : ℝ},
      (∀ i ∈ s, qiWindow r k i ⊆ Icc a b) → ∀ {u g D : ℝ → ℂ}, Measurable u →
      (∀ m < N, IntegrableOn u (dyadicIco k m)) → Measurable g → Measurable D →
      (∀ v w : ℝ, v ≤ w → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc v w)) ≤
          ENNReal.ofReal (w - v) ^ r * eLpNorm D p (volume.restrict (Icc v w))) →
      ∑ i ∈ s, eLpNorm (fun x => u x - polyFun (qiPieces hr k N u i) x) p
        (volume.restrict (dyadicIco k i)) ^ p.toReal ≤
          (A * (eLpNorm (fun x => u x - g x) p (volume.restrict (Icc a b)) +
            ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r * eLpNorm D p (volume.restrict (Icc a b)))) ^
              p.toReal := by
  obtain ⟨Cb, hCb, hCbb⟩ := exists_enorm_bcoord_le p hr
  obtain ⟨MN, hMN, hMNb⟩ := exists_enorm_bspline_le r
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have h2top : (2 : ℝ≥0∞) ^ (p.toReal - 1) ≠ ∞ :=
    ENNReal.two_rpow_ne_top _
  set Cq := 1 + r * (MN * (Cb * ppProjConst r))
  have hCq : Cq ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
    (ENNReal.natCast_ne_top r) (ENNReal.mul_ne_top hMN (ENNReal.mul_ne_top hCb
      (ppProjConst_ne_top r)))⟩
  refine ⟨Cq * ((r : ℝ≥0∞) * 2 ^ (p.toReal - 1)) ^ (1 / p.toReal), ENNReal.mul_ne_top hCq
    (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top r) h2top)),
    fun {k N s} hs {a b} hW {u g D} hum hui hg hD hT => ?_⟩
  set H : ℝ → ℝ≥0∞ := fun x => ‖u x - g x‖ₑ ^ p.toReal +
    (ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r) ^ p.toReal * ‖D x‖ₑ ^ p.toReal
  -- a Taylor polynomial of `g` on every window
  have hwin : ∀ i ∈ s, ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => u x - polyFun T x) p
      (volume.restrict (qiWindow r k i)) ^ p.toReal ≤
        ∫⁻ x in qiWindow r k i, 2 ^ (p.toReal - 1) * (Icc a b).indicator H x := by
    intro i hi
    obtain ⟨T, hT', h⟩ := exists_qiWindow_poly hum hg hD hp hT k i
    refine ⟨T, hT', h.trans (le_of_eq ?_)⟩
    rw [lintegral_const_mul' _ _ h2top]
    congr 1
    exact setLIntegral_congr_fun measurableSet_Icc fun x hx => by
      simp only [H, indicator_of_mem (hW i hi hx)]
  -- the integral of the dominating function is a `p`-th power of norms
  have hH : ∫⁻ x, 2 ^ (p.toReal - 1) * (Icc a b).indicator H x =
      2 ^ (p.toReal - 1) * (eLpNorm (fun x => u x - g x) p (volume.restrict (Icc a b)) ^
        p.toReal + (ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r *
          eLpNorm D p (volume.restrict (Icc a b))) ^ p.toReal) := by
    rw [lintegral_const_mul' _ _ h2top, lintegral_indicator measurableSet_Icc,
      lintegral_add_left (f := fun x => ‖u x - g x‖ₑ ^ p.toReal)
        ((hum.sub hg).eNorm.pow_const _), lintegral_const_mul _ (hD.eNorm.pow_const _),
      ← eLpNorm_rpow_eq (g := fun x => u x - g x) ((hum.sub hg).aestronglyMeasurable) hp0 hp,
      ← eLpNorm_rpow_eq hD.aestronglyMeasurable hp0 hp, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  calc ∑ i ∈ s, eLpNorm (fun x => u x - polyFun (qiPieces hr k N u i) x) p
        (volume.restrict (dyadicIco k i)) ^ p.toReal
      ≤ Cq ^ p.toReal * (r * ∫⁻ x, 2 ^ (p.toReal - 1) * (Icc a b).indicator H x) :=
        sum_eLpNorm_sub_qiPieces_le hr hCbb hMNb hp hum hui hs _ hwin
    _ ≤ Cq ^ p.toReal * (r * (2 ^ (p.toReal - 1) *
          (eLpNorm (fun x => u x - g x) p (volume.restrict (Icc a b)) +
            ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r * eLpNorm D p (volume.restrict (Icc a b))) ^
              p.toReal)) := by
        rw [hH]
        gcongr
        exact ENNReal.add_rpow_le_rpow_add _ _ hq1
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg Cq _ hq.le,
          ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
        ring

/-- The `p`-th power of the error over `[0, 1]` is the sum over the dyadic intervals. -/
theorem lintegral_sub_ppFun_le_sum (hp : p ≠ ∞) {F : ℝ → ℂ} (hFm : Measurable F) (k : ℕ)
    (Q : ℕ → ℂ[X]) :
    ∫⁻ x in Icc (0 : ℝ) 1, ‖F x - ppFun k Q x‖ₑ ^ p.toReal ≤
      ∑ i ∈ Finset.range (2 ^ k), eLpNorm (fun x => F x - polyFun (Q i) x) p
        (volume.restrict (dyadicIco k i)) ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  refine (lintegral_Icc_le_sum_dyadicIco _ k).trans (Finset.sum_le_sum fun i hi => le_of_eq ?_)
  rw [eLpNorm_rpow_eq (g := fun x => F x - polyFun (Q i) x)
    ((hFm.sub (measurable_polyFun _)).aestronglyMeasurable) hp0 hp]
  exact setLIntegral_congr_fun (measurableSet_dyadicIco k i) fun x hx => by
    rw [ppFun_eq_of_mem Q (Finset.mem_range.1 hi) hx]

/-- At the scale `L = 2^(-k)` the factor `c = (r 2^(-k))^r` of the Taylor remainders on the
windows and the bound `L^(-r) 2^r r^(2r)` of the derivative combine to `r^r 2^r r^(2r)`:
`a ≤ ω` and `b ≤ L^(-r) 2^r r^(2r) ω` give `a + c b ≤ (1 + r^r 2^r r^(2r)) ω`. -/
theorem add_ofReal_div_pow_mul_le (r k : ℕ) {a b ω : ℝ≥0∞} (ha : a ≤ ω)
    (hb : b ≤ ENNReal.ofReal (1 / 2 ^ k : ℝ)⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω) :
    a + ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r * b ≤
      (1 + (r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))) * ω := by
  have hcc : ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r * ENNReal.ofReal (1 / 2 ^ k : ℝ)⁻¹ ^ r =
      (r : ℝ≥0∞) ^ r := by
    rw [← mul_pow, ← ENNReal.ofReal_mul (by positivity),
      show (r : ℝ) / 2 ^ k * (1 / 2 ^ k)⁻¹ = r by field_simp, ENNReal.ofReal_natCast]
  calc a + ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r * b
      ≤ ω + ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r *
          (ENNReal.ofReal (1 / 2 ^ k : ℝ)⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω) :=
        add_le_add ha (mul_le_mul' le_rfl hb)
    _ = ω + (ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r * ENNReal.ofReal (1 / 2 ^ k : ℝ)⁻¹ ^ r) *
          (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω := by ring
    _ = _ := by rw [hcc]; ring

/-- `r 2^(-k) ≤ 1/4` for `k ≥ r + 2`: the windows of the quasi-interpolant have length at most
`1/4`. -/
theorem natCast_div_two_pow_le {r k : ℕ} (hk : r + 2 ≤ k) : (r : ℝ) / 2 ^ k ≤ 1 / 4 := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : (r : ℝ) < 2 ^ r := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ^ (r + 2) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  rw [div_le_div_iff₀ hpos (by norm_num), pow_add] at *
  nlinarith

/-- **Jackson's estimate for splines from two smoothings**: there is `A < ∞` such that for
`k ≥ r + 2`, every measurable `u` integrable on the dyadic intervals of level `k`, and measurable
`g₁, D₁` and `g₂, D₂` such that `g_ν` has Taylor polynomials
`‖g_ν - T‖_{L_p[a,b]} ≤ (b - a)^r ‖D_ν‖_{L_p[a,b]}` on all intervals,
`‖u - Q_k u‖_{L_p[0,1]} ≤ A ((‖u - g₁‖_{L_p[0,3/4]} + c ‖D₁‖_{L_p[0,3/4]}) + (‖u -
g₂‖_{L_p[1/4,1]} + c ‖D₂‖_{L_p[1/4,1]}))`
with `c = (r 2^(-k))^r`. Every window of the quasi-interpolant has length at most `1/4`, so it
lies in `[0, 3/4]` or in `[1/4, 1]`, and `Interval.exists_sum_eLpNorm_sub_qiPieces_le_of_taylor`
applies to the two sets of cells. -/
theorem exists_eLpNorm_sub_qi_le_of_taylor {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ {k : ℕ}, r + 2 ≤ k → ∀ {u g₁ D₁ g₂ D₂ : ℝ → ℂ}, Measurable u →
      (∀ m < 2 ^ k, IntegrableOn u (dyadicIco k m)) → Measurable g₁ → Measurable D₁ →
      Measurable g₂ → Measurable D₂ →
      (∀ a b : ℝ, a ≤ b → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g₁ x - polyFun T x) p (volume.restrict (Icc a b)) ≤
          ENNReal.ofReal (b - a) ^ r * eLpNorm D₁ p (volume.restrict (Icc a b))) →
      (∀ a b : ℝ, a ≤ b → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g₂ x - polyFun T x) p (volume.restrict (Icc a b)) ≤
          ENNReal.ofReal (b - a) ^ r * eLpNorm D₂ p (volume.restrict (Icc a b))) →
      eLpNorm (fun x => u x - ppFun k (qiPieces hr k (2 ^ k) u) x) p unitVol ≤
        A * ((eLpNorm (fun x => u x - g₁ x) p (volume.restrict (Icc 0 (3 / 4))) +
            ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r *
              eLpNorm D₁ p (volume.restrict (Icc 0 (3 / 4)))) +
          (eLpNorm (fun x => u x - g₂ x) p (volume.restrict (Icc (1 / 4) 1)) +
            ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r *
              eLpNorm D₂ p (volume.restrict (Icc (1 / 4) 1)))) := by
  obtain ⟨A, hA, hAb⟩ := exists_sum_eLpNorm_sub_qiPieces_le_of_taylor (p := p) hr hp
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  refine ⟨A, hA, fun {k} hk {u g₁ D₁ g₂ D₂} hum hui hg₁ hD₁ hg₂ hD₂ hT₁ hT₂ => ?_⟩
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  -- the cells whose windows lie in `[0, 3/4]`, and the others, whose windows lie in `[1/4, 1]`
  have hW₁ : ∀ i ∈ (Finset.range (2 ^ k)).filter (fun i : ℕ => ((i : ℝ) + 1) / 2 ^ k ≤ 3 / 4),
      qiWindow r k i ⊆ Icc 0 (3 / 4) := fun i hi x hx =>
    ⟨(by positivity : (0 : ℝ) ≤ ((i + 1 - r : ℕ) : ℝ) / 2 ^ k).trans hx.1,
      hx.2.trans (Finset.mem_filter.1 hi).2⟩
  have hW₂ : ∀ i ∈ (Finset.range (2 ^ k)).filter (fun i : ℕ => ¬((i : ℝ) + 1) / 2 ^ k ≤ 3 / 4),
      qiWindow r k i ⊆ Icc (1 / 4) 1 := fun i hi x hx => by
    obtain ⟨hi', hleft⟩ := Finset.mem_filter.1 hi
    push Not at hleft
    have ha : 1 / 4 ≤ ((i + 1 - r : ℕ) : ℝ) / 2 ^ k := by
      have h1 := div_le_div_of_nonneg_right (natCast_add_one_sub_le i r) hpos.le
      have : ((i : ℝ) + 1 - r) / 2 ^ k = ((i : ℝ) + 1) / 2 ^ k - (r : ℝ) / 2 ^ k := by ring
      linarith [natCast_div_two_pow_le hk]
    have hb : ((i : ℝ) + 1) / 2 ^ k ≤ 1 := by
      rw [div_le_one hpos]
      have : ((i + 1 : ℕ) : ℝ) ≤ 2 ^ k := by exact_mod_cast Finset.mem_range.1 hi'
      push_cast at this; linarith
    exact ⟨ha.trans hx.1, hx.2.trans hb⟩
  have h₁ := hAb (Finset.filter_subset _ _) hW₁ hum hui hg₁ hD₁ hT₁
  have h₂ := hAb (Finset.filter_subset _ _) hW₂ hum hui hg₂ hD₂ hT₂
  refine eLpNorm_le_of_lintegral_le ((hum.sub (measurable_ppFun _ _)).aestronglyMeasurable)
    hp0 hp ((lintegral_sub_ppFun_le_sum hp hum k _).trans ?_)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 ^ k))
    (fun i : ℕ => ((i : ℝ) + 1) / 2 ^ k ≤ 3 / 4), mul_add]
  exact (add_le_add h₁ h₂).trans (ENNReal.add_rpow_le_rpow_add _ _ hq1)

/-- **Jackson's inequality for splines, continuous functions**: there is `C` with
`‖F - Q_k F‖_{L_p[0,1]} ≤ C ω_r(F, 2^(-k), [0, 1])_p` for every continuous `F` and `k ≥ r + 2`:
the smoothings of `F` from the left on `[0, 3/4]` and from the right on `[1/4, 1]` enter
`Interval.exists_eLpNorm_sub_qi_le_of_taylor`. -/
theorem exists_eLpNorm_sub_qi_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : ℝ → ℂ, Continuous F → ∀ k : ℕ, r + 2 ≤ k →
      eLpNorm (fun x => F x - ppFun k (qiPieces hr k (2 ^ k) F) x) p unitVol ≤
        C * modulus r p 0 1 F (1 / 2 ^ k) := by
  obtain ⟨A, hA, hAb⟩ := exists_eLpNorm_sub_qi_le_of_taylor (p := p) hr hp
  have hJ : 1 + (r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))
      (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))⟩
  refine ⟨A * (2 * (1 + (r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)))),
    ENNReal.mul_ne_top hA (ENNReal.mul_ne_top (by simp) hJ), fun F hF k hk => ?_⟩
  have hp1 : 1 ≤ p := Fact.out
  have hL : (0 : ℝ) < 1 / 2 ^ k := by positivity
  have hk2 : 2 ≤ k := by omega
  have hwL : (3 / 4 : ℝ) + 1 / 2 ^ k ≤ 1 := by
    have : (1 : ℝ) / 2 ^ k ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk2
    linarith
  obtain ⟨gl, Dl, hglm, hDlm, hl1, hl2, hl3⟩ := exists_left_smoothing hF hr hp1 hp hL hwL
  obtain ⟨gr, Dr, hgrm, hDrm, hr1, hr2, hr3⟩ := exists_right_smoothing hF hr hp1 hp hL hwL
  rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num] at hr1 hr2
  refine (hAb hk hF.measurable (fun m _ => integrableOn_dyadicIco_of_continuous hF k m) hglm
    hDlm hgrm hDrm hl3 hr3).trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [two_mul, add_mul]
  exact add_le_add (add_ofReal_div_pow_mul_le r k hl1 hl2) (add_ofReal_div_pow_mul_le r k hr1 hr2)

/-- **The quasi-interpolant is bounded on `L_p[0, 1]`**: there is `C < ∞` with
`‖Q_k u‖_{L_p[0,1]} ≤ C ‖u‖_{L_p[0,1]}` for every level `k` and every measurable `u` integrable
on the dyadic intervals, from `Interval.exists_sum_eLpNorm_sub_qiPieces_le_of_taylor` with the
smoothing `0`. -/
theorem exists_eLpNorm_qi_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (k : ℕ) {u : ℝ → ℂ}, Measurable u →
      (∀ m < 2 ^ k, IntegrableOn u (dyadicIco k m)) →
      eLpNorm (ppFun k (qiPieces hr k (2 ^ k) u)) p unitVol ≤ C * eLpNorm u p unitVol := by
  obtain ⟨A, hA, hAb⟩ := exists_sum_eLpNorm_sub_qiPieces_le_of_taylor (p := p) hr hp
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  refine ⟨1 + A, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hA⟩, fun k {u} hum hui => ?_⟩
  -- the windows lie in `[0, 1]`, and the smoothing `0` has the Taylor polynomial `0`
  have hW : ∀ i ∈ Finset.range (2 ^ k), qiWindow r k i ⊆ Icc 0 1 := fun i hi x hx => by
    refine ⟨(by positivity : (0 : ℝ) ≤ ((i + 1 - r : ℕ) : ℝ) / 2 ^ k).trans hx.1, hx.2.trans ?_⟩
    rw [div_le_one (by positivity)]
    have : ((i + 1 : ℕ) : ℝ) ≤ 2 ^ k := by exact_mod_cast Finset.mem_range.1 hi
    push_cast at this; linarith
  have hT0 : ∀ v w : ℝ, v ≤ w → ∃ T ∈ degreeLT ℂ r,
      eLpNorm (fun x => (0 : ℝ → ℂ) x - polyFun T x) p (volume.restrict (Icc v w)) ≤
        ENNReal.ofReal (w - v) ^ r * eLpNorm (0 : ℝ → ℂ) p (volume.restrict (Icc v w)) :=
    fun _ _ _ => ⟨0, Submodule.zero_mem _, by simp [polyFun_zero]⟩
  have h := hAb subset_rfl hW hum hui measurable_zero measurable_zero hT0
  simp only [Pi.zero_apply, sub_zero, eLpNorm_zero, mul_zero, add_zero] at h
  have herr : eLpNorm (fun x => u x - ppFun k (qiPieces hr k (2 ^ k) u) x) p unitVol ≤
      A * eLpNorm u p unitVol :=
    eLpNorm_le_of_lintegral_le ((hum.sub (measurable_ppFun _ _)).aestronglyMeasurable)
      hp0 hp ((lintegral_sub_ppFun_le_sum hp hum k _).trans h)
  calc eLpNorm (ppFun k (qiPieces hr k (2 ^ k) u)) p unitVol
      = eLpNorm (u - fun x => u x - ppFun k (qiPieces hr k (2 ^ k) u) x) p unitVol := by
        congr 1; funext x; simp
    _ ≤ eLpNorm u p unitVol +
          eLpNorm (fun x => u x - ppFun k (qiPieces hr k (2 ^ k) u) x) p unitVol :=
        eLpNorm_sub_le hp1
    _ ≤ eLpNorm u p unitVol + A * eLpNorm u p unitVol := add_le_add le_rfl herr
    _ = (1 + A) * eLpNorm u p unitVol := by ring

/-! ### Jackson's inequality in `L_p` and the coincidence theorem -/

/-- At complexity `1` the spline scheme and the piecewise polynomial scheme have the same error:
both approximate by the polynomials of degree `< r` (`Interval.splineSpace_zero`). -/
theorem approxError_splineScheme_one (r : ℕ) (f : Lp ℂ p unitVol) :
    (splineScheme p r).approxError f 1 = (ppScheme p r).approxError f 1 := by
  have h : (splineScheme p r) 1 = (ppScheme p r) 1 := by
    ext g
    rw [mem_splineScheme one_ne_zero, mem_ppScheme one_ne_zero, Nat.log_one_right,
      splineSpace_zero]
  rw [ApproximationScheme.approxError, ApproximationScheme.approxError, h]

/-- **Jackson's inequality for dyadic splines**: for `1 ≤ p < ∞` and `r ≥ 1` there is `C_J` with
`E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k), [0, 1])_p` for all `f ∈ L_p[0, 1]` and all `k ≥ 0`: the
quasi-interpolant for `k ≥ r + 2`, Whitney's inequality for `k ≤ r + 1`. -/
theorem exists_approxError_splineScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p unitVol) (k : ℕ),
      (splineScheme p r).approxError f (2 ^ k) ≤ CJ * lpModulus p r f k := by
  obtain ⟨C, hC, hCb⟩ := exists_eLpNorm_sub_qi_le hr hp
  obtain ⟨W, hW, hWb⟩ := exists_approxError_ppScheme_one_le (p := p) hr hp (m := r + 1) (by omega)
  refine ⟨W + C, ENNReal.add_ne_top.2 ⟨hW, hC⟩, fun f k => ?_⟩
  rcases lt_or_ge k (r + 2) with hk | hk
  · -- the coarse levels: Whitney's inequality
    calc (splineScheme p r).approxError f (2 ^ k)
        ≤ (splineScheme p r).approxError f 1 :=
          ApproximationScheme.approxError_anti f Nat.one_le_two_pow
      _ = (ppScheme p r).approxError f 1 := approxError_splineScheme_one r f
      _ ≤ W * lpModulus p r f (r + 1) := hWb f
      _ ≤ (W + C) * lpModulus p r f k :=
          mul_le_mul' le_self_add (lpModulus_anti r f (by omega))
  · -- the fine levels: the quasi-interpolant
    refine (approxError_le_of_continuous hp hC (fun g => ?_) f).trans
      (mul_le_mul' le_add_self le_rfl)
    exact ⟨ppFun k (qiPieces hr k (2 ^ k) g), ⟨(memLp_ppFun k (qiPieces hr k (2 ^ k) g) p).toLp _,
      mem_splineScheme_two_pow.2 ⟨qiPieces hr k (2 ^ k) g, qiPieces_mem hr k (2 ^ k) g,
        splineJoins_qiPieces hr k (2 ^ k) g, MemLp.coeFn_toLp _⟩, MemLp.coeFn_toLp _⟩,
      hCb g g.continuous k hk⟩

/-- The modulus `ω_r(f, 2^(-k), [0, 1])_p` is compatible with the scheme of dyadic splines of
order `r`, with inverse order `θ = r - 1 + 1/p` and Jackson's inequality at every level. -/
noncomputable def splineModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (splineScheme p r) (((r - 1 : ℕ) : ℝ) + 1 / p.toReal) :=
  .ofExists (lpModulus p r) (lpModulus_add_le r) (2 ^ r) (by simp) (lpModulus_le r) 0
    ((exists_approxError_splineScheme_le hr hp).imp fun _ h => ⟨h.1, fun f k _ => h.2 f k⟩)
    (exists_inverse_splineScheme hp)

/-- **Approximation by dyadic splines.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and
`0 ≤ s < r - 1 + 1/p`, an `f ∈ L_p[0, 1]` lies in the approximation space `A^s_q` of the splines
of order `r` (degree `< r`, `C^(r-2)`) on dyadic partitions iff its Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q}` is finite. -/
theorem memApprox_splineScheme_iff {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) (f : Lp ℂ p unitVol) :
    (splineScheme p r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ := by
  have hθ : (r : ℝ) - 1 + 1 / p.toReal = ((r - 1 : ℕ) : ℝ) + 1 / p.toReal := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  exact (splineModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs (hθ ▸ hsr) f

end Interval
