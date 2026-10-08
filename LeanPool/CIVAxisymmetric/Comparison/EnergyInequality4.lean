/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.CauchySchwarzEnergy
public import LeanPool.CIVAxisymmetric.Comparison.Barrier
public import LeanPool.CIVAxisymmetric.Comparison.EnergyInequality3
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The sign of the diffusion term: Green's identity and the vanishing Kato curvature

This file analyses the diffusion term in the truncated Kato energy identity
`truncatedKatoSq_eq_add_intervalIntegral` behind the integrated energy inequality
`eq:aniso:comparison:positive:energy`. The point is its sign: `kappaProfile kap` is convex but
takes negative values, so `kappaProfile kap (g x) * deriv (deriv (kappaProfile kap)) (g x)` is not
signed for fixed `kap`, and the gradient of the cutoff contributes a further term.

Throughout, `g : Vec m → ℝ` is a smooth excess (in the application,
`fun x => mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s)` at a fixed time `s`) and
`chi : Vec m → ℝ` is a smooth, compactly supported cutoff (in the application,
`mollifierCutoff m R`). Let `φ_kap := fun x => 2 * kappaProfile kap (g x) *`
`deriv (kappaProfile kap) (g x) * chi x ^ 2`, the truncated Kato test function whose pairing against
the Laplacian is the diffusion term.

## Main results

* `integral_mul_lapD_eq` — **Green's identity for the partial Laplacian**: for any smooth,
  compactly supported `φ` and smooth `u`, `∫ φ · lapD u = -∑_{i<d} ∫ ∂_i φ · ∂_i u`. This is `d`
  applications of Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, one per
  diffusive coordinate. That lemma needs differentiability at every point of the other function's
  support, which the Kato-smoothed `φ_kap` has and the non-smooth `comparisonPosPart` lacks. `lapD`
  is `partialLaplacian` specialized to a function of `Vec m` alone, definitionally equal to it at a
  fixed time slice (`partialLaplacian_eq_lapD`).

* `integral_kappaTestFn_mul_lapD_eq` — **the chain-rule decomposition**, combining Green's
  identity with the product and chain rule `hasFDerivAt_kappaTestFn` for `φ_kap`: with
  `kappaProfile2 kap` the second derivative of `kappaProfile kap` (`deriv_deriv_kappaProfile`),
  `dirichletD` the partial Dirichlet energy `∑_{i<d} (∂_i g)²` and `mixedD` the mixed term
  `∑_{i<d} ∂_i chi · ∂_i g`,

  `∫ φ_kap · lapD g`
  `= -∫ chi² (2 (deriv (kappaProfile kap) (g ·))² + 2 kappaProfile kap (g ·) kappaProfile2 kap
  (g ·)) dirichletD`
  `  - ∫ 4 kappaProfile kap (g ·) deriv (kappaProfile kap) (g ·) chi · mixedD`.

  The `2 (deriv …)²` piece is the dissipation, nonnegative for every `kap > 0` with no limit
  needed (`kappaTestFn_dissipation_nonneg`), so it may be dropped when an upper bound is wanted.
  The `2 kappaProfile kap kappaProfile2 kap` piece is the curvature term.

* `tendsto_integral_curvature_term_nhds_zero` — **the curvature term vanishes as `kap ↓ 0`**, as
  an integral over all of `Vec m`. It rests on two facts about the real-variable Kato profile:
  `kappaProfile kap 0 = 0` exactly, for every `kap` (`kappaProfile_zero`), so no argument about the
  gradient on the level set `{g = 0}` is needed; and consequently
  `|kappaProfile kap t * kappaProfile2 kap t| ≤ 1/2` for every `t` and every `kap > 0`
  (`abs_kappaProfile_mul_kappaProfile2_le`). This `kap`-independent bound gives dominated
  convergence against `∫ chi² dirichletD` (finite, since `chi` has compact support and
  `dirichletD` is continuous), with pointwise limit `0` at every `x`
  (`tendsto_kappaProfile_mul_kappaProfile2_nhds_zero`).

* `tendsto_integral_mixed_term_nhds_zero` — the `kap ↓ 0` limit of the mixed-cutoff term is
  `4 ∫ max (g ·) 0 · chi · mixedD`, which is `0` when `max (g ·) 0` and `mixedD` have disjoint
  supports (`tendsto_integral_mixed_term_nhds_zero_of_disjoint`).

* `partialLaplacian_sub_gradPair_mollifySlice_sub_le` — **the barrier reduction**: by
  `barrier_supersolution` and the linearity lemmas `gradPair_sub` and `partialLaplacian_sub`, the
  Laplacian-minus-drift combination of the mollified slice, less the barrier's time derivative,
  is bounded above by the same combination for the excess.

* `integral_kappaProfile_mul_deriv_mul_mollifierCutoff_sq_le` — the Cauchy–Schwarz bound on the
  pairing of the truncated Kato test function with a square-integrable forcing term.

* `tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonEnergy` — the truncated
  Kato energy converges to `comparisonEnergy` as `kap ↓ 0`.

`CIV.Comparison.EnergySpatialIntegration` integrates `integral_kappaTestFn_mul_lapD_eq` and the
energy limit in space and time, using `lapD`, `dirichletD`, `mixedD` and `kappaProfile2`. The
comparison proof uses Green's identity `integral_mul_lapD_eq` (through
`integral_partialLaplacian_mul_comm_of_hasCompactSupport`) and the linearity lemmas `gradPair_sub`
and `partialLaplacian_sub` (in `CIV.Comparison.Direct.SliceEnergy`). `Vec m` carries the sup norm
throughout; nothing here needs the Euclidean length.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV


/-- The second derivative of the Kato profile in closed form. -/
@[expose] def kappaProfile2 (kap t : ℝ) : ℝ := kap ^ 2 / (2 * Real.sqrt (t ^ 2 + kap ^ 2) ^ 3)

/-- The second derivative of the Kato profile, `kappaProfile2`, is genuinely its derivative:
`(kappaProfile kap)` is differentiable twice for `kap > 0`, with the closed form computed by the
quotient rule. -/
theorem hasDerivAt_deriv_kappaProfile (kap : ℝ) (hkap : 0 < kap) (t : ℝ) :
    HasDerivAt (deriv (kappaProfile kap)) (kappaProfile2 kap t) t := by
  have hne : t ^ 2 + kap ^ 2 ≠ 0 := radicand_ne_zero kap id t hkap
  have hsqrtpos : 0 < Real.sqrt (t ^ 2 + kap ^ 2) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne (by positivity) (Ne.symm hne))
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2 + kap ^ 2) (2 * t) t := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t ^ 1) t := hasDerivAt_pow 2 t
    simpa using h1.add_const (kap ^ 2)
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + kap ^ 2))
      ((2 * t) / (2 * Real.sqrt (t ^ 2 + kap ^ 2))) t := hsq.sqrt hne
  have hsqrt' : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + kap ^ 2))
      (t / Real.sqrt (t ^ 2 + kap ^ 2)) t := by
    have heq : (2 * t) / (2 * Real.sqrt (t ^ 2 + kap ^ 2)) = t / Real.sqrt (t ^ 2 + kap ^ 2) := by
      rw [mul_div_mul_left _ _ (two_ne_zero)]
    rwa [heq] at hsqrt
  have hdiv : HasDerivAt (fun s : ℝ => s / Real.sqrt (s ^ 2 + kap ^ 2))
      ((1 * Real.sqrt (t ^ 2 + kap ^ 2) - t * (t / Real.sqrt (t ^ 2 + kap ^ 2)))
        / Real.sqrt (t ^ 2 + kap ^ 2) ^ 2) t :=
    (hasDerivAt_id t).fun_div hsqrt' hsqrtpos.ne'
  have hval : (1 * Real.sqrt (t ^ 2 + kap ^ 2) - t * (t / Real.sqrt (t ^ 2 + kap ^ 2)))
      / Real.sqrt (t ^ 2 + kap ^ 2) ^ 2 / 2 = kappaProfile2 kap t := by
    have hs2 : Real.sqrt (t ^ 2 + kap ^ 2) ^ 2 = t ^ 2 + kap ^ 2 := Real.sq_sqrt (by positivity)
    unfold kappaProfile2
    rw [eq_div_iff (by positivity)]
    have hne' : Real.sqrt (t ^ 2 + kap ^ 2) ≠ 0 := hsqrtpos.ne'
    field_simp
    nlinarith only [hs2]
  have hderiv1 : HasDerivAt (fun s : ℝ => (1 + s / Real.sqrt (s ^ 2 + kap ^ 2)) / 2)
      ((0 + (1 * Real.sqrt (t ^ 2 + kap ^ 2) - t * (t / Real.sqrt (t ^ 2 + kap ^ 2)))
        / Real.sqrt (t ^ 2 + kap ^ 2) ^ 2) / 2) t :=
    ((hasDerivAt_const t (1 : ℝ)).add hdiv).div_const 2
  have heqfun : (fun s : ℝ => (1 + s / Real.sqrt (s ^ 2 + kap ^ 2)) / 2) = deriv (kappaProfile
    kap) := by
    funext s
    rw [deriv_kappaProfile kap hkap s]
  rw [heqfun] at hderiv1
  have hvaleq : (0 + (1 * Real.sqrt (t ^ 2 + kap ^ 2) - t * (t / Real.sqrt (t ^ 2 + kap ^ 2)))
        / Real.sqrt (t ^ 2 + kap ^ 2) ^ 2) / 2 = kappaProfile2 kap t := by
    rw [zero_add]; exact hval
  rwa [hvaleq] at hderiv1

/-- `deriv (deriv (kappaProfile kap)) = kappaProfile2 kap`, the value form of
`hasDerivAt_deriv_kappaProfile`. -/
theorem deriv_deriv_kappaProfile (kap : ℝ) (hkap : 0 < kap) (t : ℝ) :
    deriv (deriv (kappaProfile kap)) t = kappaProfile2 kap t :=
  (hasDerivAt_deriv_kappaProfile kap hkap t).deriv


/-- The Kato profile vanishes exactly at `0`, for every `kap`: this single fact is what lets the
curvature term below be dominated uniformly in `kap`, with no delicate a.e.-vanishing-gradient
argument on the level set `{g = 0}`. -/
theorem kappaProfile_zero (kap : ℝ) (hkap : 0 < kap) : kappaProfile kap 0 = 0 := by
  rw [kappaProfile_eq]
  have : Real.sqrt (0 ^ 2 + kap ^ 2) = kap := by
    rw [zero_pow (two_ne_zero), zero_add, Real.sqrt_sq hkap.le]
  rw [this]; ring

/-- The curvature coefficient `kappaProfile kap t * kappaProfile2 kap t` is bounded by an
absolute constant, uniformly in `t` and `kap > 0`. This is the quantitative core of the diffusion
sign derivation: the convex, possibly-negative Kato profile can only ever contribute a bounded
amount through its own curvature. -/
theorem abs_kappaProfile_mul_kappaProfile2_le (kap : ℝ) (hkap : 0 < kap) (t : ℝ) :
    |kappaProfile kap t * kappaProfile2 kap t| ≤ 1 / 2 := by
  set s := Real.sqrt (t ^ 2 + kap ^ 2) with hsdef
  have hs2 : s ^ 2 = t ^ 2 + kap ^ 2 := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hskap : kap ≤ s := by
    nlinarith only [hs2, sq_nonneg t, hspos, Real.sqrt_le_sqrt (show kap ^ 2 ≤ t ^ 2 + kap ^ 2 by
      nlinarith only [sq_nonneg t])]
  have htle : t ≤ s := by
    nlinarith only [hs2, hspos, Real.sqrt_le_sqrt (show t ^ 2 ≤ t ^ 2 + kap ^ 2 by
      nlinarith only [sq_nonneg kap])]
  have htge : -s ≤ t := by
    nlinarith only [hs2, hspos, Real.sqrt_le_sqrt (show t ^ 2 ≤ t ^ 2 + kap ^ 2 by
      nlinarith only [sq_nonneg kap]), sq_nonneg (t + s)]
  have hval : kappaProfile kap t * kappaProfile2 kap t
      = kap ^ 2 * (t + s - kap) / (4 * s ^ 3) := by
    rw [kappaProfile_eq]
    unfold kappaProfile2
    rw [← hsdef]
    have hne : s ≠ 0 := hspos.ne'
    field_simp
    ring
  rw [hval, abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * s ^ 3)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * s ^ 3)]
  have hub : kap ^ 2 * (t + s - kap) ≤ 2 * s ^ 3 := by
    have hstep1 : t + s - kap ≤ 2 * s := by linarith only [htle, hkap]
    have hstep2 : kap ^ 2 * (t + s - kap) ≤ kap ^ 2 * (2 * s) :=
      mul_le_mul_of_nonneg_left hstep1 (sq_nonneg kap)
    have hstep3 : kap ^ 2 ≤ s ^ 2 := by nlinarith only [hskap, hkap.le]
    have hstep4 : kap ^ 2 * (2 * s) ≤ s ^ 2 * (2 * s) :=
      mul_le_mul_of_nonneg_right hstep3 (by linarith only [hspos])
    have hstep5 : s ^ 2 * (2 * s) = 2 * s ^ 3 := by ring
    linarith only [hstep2, hstep4, hstep5.le, hstep5.ge]
  have hlb : -(2 * s ^ 3) ≤ kap ^ 2 * (t + s - kap) := by
    have hstep1 : -kap ≤ t + s - kap := by linarith only [htge]
    have hstep2 : kap ^ 2 * (-kap) ≤ kap ^ 2 * (t + s - kap) :=
      mul_le_mul_of_nonneg_left hstep1 (sq_nonneg kap)
    have hstep3 : kap ^ 3 ≤ s ^ 3 := by
      have h := pow_le_pow_left₀ hkap.le hskap 3
      simpa using h
    have hstep4 : kap ^ 2 * (-kap) = -(kap ^ 3) := by ring
    have hstep5 : (0:ℝ) < s ^ 3 := by positivity
    linarith only [hstep2, hstep3, hstep4.le, hstep4.ge, hstep5]
  rw [abs_le]
  constructor
  · linarith only [hlb]
  · linarith only [hub]


/-- The curvature coefficient in closed form, as a single fraction. -/
theorem kappaProfile_mul_kappaProfile2_eq (kap t : ℝ) (hkap : 0 < kap) :
    kappaProfile kap t * kappaProfile2 kap t
      = kap ^ 2 * (t + Real.sqrt (t ^ 2 + kap ^ 2) - kap) / (4 * Real.sqrt (t ^ 2 + kap ^ 2) ^
        3) := by
  have hspos : 0 < Real.sqrt (t ^ 2 + kap ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [kappaProfile_eq]
  unfold kappaProfile2
  have hne : Real.sqrt (t ^ 2 + kap ^ 2) ≠ 0 := hspos.ne'
  field_simp
  ring

/-- **The curvature coefficient tends to `0` pointwise as `kap ↓ 0`, for every real `t`.** Away
from `t = 0` this is continuity of the closed form; at `t = 0` it is exact (`kappaProfile_zero`),
not merely a limit. Combined with `abs_kappaProfile_mul_kappaProfile2_le`'s uniform bound, this is
what makes the curvature term of the diffusion identity vanish under dominated convergence
(`tendsto_integral_curvature_term_nhds_zero` below), which is the precise sense in which the sign
of the diffusion term is resolved here. -/
theorem tendsto_kappaProfile_mul_kappaProfile2_nhds_zero (t : ℝ) :
    Tendsto (fun kap : ℝ => kappaProfile kap t * kappaProfile2 kap t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcongr : (fun kap : ℝ => kappaProfile kap t * kappaProfile2 kap t)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun kap : ℝ => kap ^ 2 * (t + Real.sqrt (t ^ 2 + kap ^ 2) - kap)
          / (4 * Real.sqrt (t ^ 2 + kap ^ 2) ^ 3) := by
    filter_upwards [self_mem_nhdsWithin] with kap hkap
    exact kappaProfile_mul_kappaProfile2_eq kap t hkap
  rw [Filter.tendsto_congr' hcongr]
  have hscont : Continuous (fun kap : ℝ => Real.sqrt (t ^ 2 + kap ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))
  have hs0 : Real.sqrt (t ^ 2 + (0:ℝ) ^ 2) = |t| := by
    rw [show (0:ℝ)^2 = 0 by ring, add_zero, Real.sqrt_sq_eq_abs]
  have hs_tendsto : Tendsto (fun kap : ℝ => Real.sqrt (t ^ 2 + kap ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds |t|) := by
    have := hscont.tendsto 0
    rw [hs0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hkap_tendsto : Tendsto (fun kap : ℝ => kap) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hkapsq_tendsto : Tendsto (fun kap : ℝ => kap ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := hkap_tendsto.pow 2
    simpa using this
  have hnum_tendsto : Tendsto (fun kap : ℝ => t + Real.sqrt (t ^ 2 + kap ^ 2) - kap)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (t + |t| - 0)) :=
    (tendsto_const_nhds.add hs_tendsto).sub hkap_tendsto
  have hprod_tendsto : Tendsto (fun kap : ℝ => kap ^ 2 * (t + Real.sqrt (t ^ 2 + kap ^ 2) - kap))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * (t + |t| - 0))) :=
    hkapsq_tendsto.mul hnum_tendsto
  have hden_tendsto : Tendsto (fun kap : ℝ => 4 * Real.sqrt (t ^ 2 + kap ^ 2) ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (4 * |t| ^ 3)) :=
    tendsto_const_nhds.mul (hs_tendsto.pow 3)
  by_cases ht : t = 0
  · have hzero : (fun kap : ℝ => kap ^ 2 * (t + Real.sqrt (t ^ 2 + kap ^ 2) - kap)
        / (4 * Real.sqrt (t ^ 2 + kap ^ 2) ^ 3))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => (0:ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with kap hkap
      have hkap0 : 0 < kap := hkap
      have hsq : Real.sqrt (t ^ 2 + kap ^ 2) = kap := by
        rw [ht, show (0:ℝ) ^ 2 = 0 by ring, zero_add, Real.sqrt_sq hkap0.le]
      rw [hsq, ht]
      have hz : (0:ℝ) + kap - kap = 0 := by ring
      rw [hz]
      simp
    rw [Filter.tendsto_congr' hzero]
    exact tendsto_const_nhds
  · have hdne : (4 * |t| ^ 3 : ℝ) ≠ 0 := by positivity
    have hres := hprod_tendsto.div hden_tendsto hdne
    have hval0 : (0:ℝ) * (t + |t| - 0) / (4 * |t| ^ 3) = 0 := by
      rw [zero_mul, zero_div]
    rw [hval0] at hres
    exact hres


/-- The product `kappaProfile kap t * deriv (kappaProfile kap) t` is bounded below by `-kap / 16`,
uniformly in `t`: it is `O(kap)`, since `kappaProfile kap t * deriv (kappaProfile kap) t` is
homogeneous of degree `1` in `(kap, t)` jointly. Used to control the supersolution slack the
barrier contributes once the drift and diffusion of the mollified equation are reduced to the
excess alone. -/
theorem neg_le_kappaProfile_mul_deriv_kappaProfile (kap : ℝ) (hkap : 0 < kap) (t : ℝ) :
    -(kap / 16) ≤ kappaProfile kap t * deriv (kappaProfile kap) t := by
  set s := Real.sqrt (t ^ 2 + kap ^ 2) with hsdef
  have hs2 : s ^ 2 = t ^ 2 + kap ^ 2 := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hskap : kap ≤ s := by
    nlinarith only [hs2, sq_nonneg t, hspos, Real.sqrt_le_sqrt (show kap ^ 2 ≤ t ^ 2 + kap ^ 2 by
      nlinarith only [sq_nonneg t])]
  have hval : kappaProfile kap t * deriv (kappaProfile kap) t
      = ((t + s) ^ 2 - kap * (t + s)) / (4 * s) := by
    rw [kappaProfile_eq, deriv_kappaProfile kap hkap t, ← hsdef]
    have hne : s ≠ 0 := hspos.ne'
    field_simp
    ring
  have hmin : -(kap ^ 2 / 4) ≤ (t + s) ^ 2 - kap * (t + s) := by
    nlinarith only [sq_nonneg (t + s - kap / 2)]
  rw [hval, le_div_iff₀ (by positivity : (0:ℝ) < 4 * s)]
  have hstep : -(kap / 16) * (4 * s) ≤ -(kap ^ 2 / 4) := by
    have hks : kap * kap ≤ kap * s := mul_le_mul_of_nonneg_left hskap hkap.le
    nlinarith only [hks]
  linarith only [hstep, hmin]

/-- `kappaProfile kap t * deriv (kappaProfile kap) t → max t 0` as `kap ↓ 0`, for every `t`: the
Kato regularization of `t ↦ (t_+)²/2`'s derivative converges to the derivative of `t ↦ (t_+)²/2`
itself away from the (here harmless) single point `t = 0`. -/
theorem tendsto_kappaProfile_mul_deriv_kappaProfile (t : ℝ) :
    Tendsto (fun kap : ℝ => kappaProfile kap t * deriv (kappaProfile kap) t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (max t 0)) := by
  have hPhi_tendsto : Tendsto (fun kap : ℝ => kappaProfile kap t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (max t 0)) := by
    have h := tendsto_katoSmooth (id : ℝ → ℝ) t
    simpa [kappaProfile] using h
  have hbase : Tendsto (fun kap : ℝ => kap / 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (continuous_id.div_const 2).tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  by_cases ht : t ≤ 0
  · have hmax0 : max t 0 = 0 := max_eq_right ht
    have hbound1 : ∀ᶠ kap in nhdsWithin (0:ℝ) (Set.Ioi 0),
        -(kap / 2) ≤ kappaProfile kap t * deriv (kappaProfile kap) t := by
      filter_upwards [self_mem_nhdsWithin] with kap hkap
      have hkap0 : 0 < kap := hkap
      have hlow0 := posPart_sub_katoSmooth_le kap id t
      have hup0 := katoSmooth_le_posPart kap hkap0 id t
      have e1 : (id t : ℝ) = t := rfl
      have e2 : katoSmooth kap id t = kappaProfile kap t := rfl
      rw [e1, e2] at hlow0 hup0
      have hlow : max t 0 - kap / 2 ≤ kappaProfile kap t := by linarith only [hlow0]
      have hup : kappaProfile kap t ≤ max t 0 := hup0
      have hd := deriv_kappaProfile_mem_Icc kap hkap0 t
      rw [hmax0] at hlow hup
      have hprod_ge : kappaProfile kap t ≤ kappaProfile kap t * deriv (kappaProfile kap) t := by
        nlinarith only [mul_nonneg (neg_nonneg.mpr hup) (sub_nonneg.mpr hd.2)]
      linarith only [hlow, hprod_ge]
    have hbound2 : ∀ᶠ kap in nhdsWithin (0:ℝ) (Set.Ioi 0),
        kappaProfile kap t * deriv (kappaProfile kap) t ≤ kap / 2 := by
      filter_upwards [self_mem_nhdsWithin] with kap hkap
      have hkap0 : 0 < kap := hkap
      have hup0 := katoSmooth_le_posPart kap hkap0 id t
      have e1 : (id t : ℝ) = t := rfl
      have e2 : katoSmooth kap id t = kappaProfile kap t := rfl
      rw [e1, e2] at hup0
      have hup : kappaProfile kap t ≤ max t 0 := hup0
      have hd := deriv_kappaProfile_mem_Icc kap hkap0 t
      rw [hmax0] at hup
      have hprod_le0 : kappaProfile kap t * deriv (kappaProfile kap) t ≤ 0 := by
        nlinarith only [mul_nonneg (neg_nonneg.mpr hup) hd.1]
      linarith only [hprod_le0, hkap0]
    have hlow_tendsto : Tendsto (fun kap : ℝ => -(kap / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
      := by
      have h := hbase.neg
      simpa using h
    rw [hmax0]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_tendsto hbase hbound1 hbound2
  · have ht' : 0 < t := not_le.mp ht
    have hmaxt : max t 0 = t := max_eq_left ht'.le
    have hderiv_tendsto : Tendsto (fun kap : ℝ => deriv (kappaProfile kap) t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have hcongr : (fun kap : ℝ => deriv (kappaProfile kap) t)
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun kap => (1 + t / Real.sqrt (t ^ 2 + kap ^ 2)) / 2 := by
        filter_upwards [self_mem_nhdsWithin] with kap hkap
        exact deriv_kappaProfile kap hkap t
      rw [Filter.tendsto_congr' hcongr]
      have hspos : ∀ kap : ℝ, Real.sqrt (t ^ 2 + kap ^ 2) ≠ 0 :=
        fun kap => (Real.sqrt_pos.mpr (by nlinarith only [sq_nonneg kap, ht', mul_pos ht' ht'])).ne'
      have hscont : Continuous (fun kap : ℝ => Real.sqrt (t ^ 2 + kap ^ 2)) :=
        Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))
      have hcont : Continuous (fun kap : ℝ => (1 + t / Real.sqrt (t ^ 2 + kap ^ 2)) / 2) :=
        (continuous_const.add (continuous_const.div hscont hspos)).div_const 2
      have hval : (1 + t / Real.sqrt (t ^ 2 + (0:ℝ) ^ 2)) / 2 = 1 := by
        rw [show (0:ℝ) ^ 2 = 0 by ring, add_zero, Real.sqrt_sq ht'.le]
        rw [div_self ht'.ne']
        norm_num
      have h := hcont.tendsto (0 : ℝ)
      rw [hval] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hres := hPhi_tendsto.mul hderiv_tendsto
    rw [hmaxt, mul_one] at hres
    rwa [hmaxt]


/-- The partial Laplacian of a pure `Vec m → ℝ` function, in the first `d` coordinates. -/
@[expose] def lapD (m d : ℕ) (u : Vec m → ℝ) (x : Vec m) : ℝ :=
  ∑ i : Fin m, if (i : ℕ) < d then
    fderiv ℝ (fun y : Vec m => fderiv ℝ u y (basisVec i)) x (basisVec i) else 0

/-- `partialLaplacian` unfolds to `lapD` of the fixed-time spatial slice: purely definitional, so
that the Green's identity below (stated for `lapD`, a function of `Vec m` alone) applies directly
to `partialLaplacian`. -/
theorem partialLaplacian_eq_lapD {m d : ℕ} (φ : Vec m × ℝ → ℝ) (z : Vec m × ℝ) :
    partialLaplacian m d φ z = lapD m d (fun y => φ (y, z.2)) z.1 := rfl

/-- The second coordinate derivative of a difference is the difference of the second coordinate
derivatives, for globally smooth `f1`, `f2`. -/
theorem fderiv_fderiv_sub_apply {m : ℕ} {f1 f2 : Vec m → ℝ} (hf1 : ContDiff ℝ (⊤ : ℕ∞) f1)
    (hf2 : ContDiff ℝ (⊤ : ℕ∞) f2) (x : Vec m) (i : Fin m) :
    fderiv ℝ (fun y => fderiv ℝ (fun w => f1 w - f2 w) y (basisVec i)) x (basisVec i)
      = fderiv ℝ (fun y => fderiv ℝ f1 y (basisVec i)) x (basisVec i)
        - fderiv ℝ (fun y => fderiv ℝ f2 y (basisVec i)) x (basisVec i) := by
  have hd1 : ∀ y : Vec m, DifferentiableAt ℝ f1 y :=
    fun y => (hf1.differentiable (by simp)).differentiableAt
  have hd2 : ∀ y : Vec m, DifferentiableAt ℝ f2 y :=
    fun y => (hf2.differentiable (by simp)).differentiableAt
  have hfun : (fun y : Vec m => fderiv ℝ (fun w => f1 w - f2 w) y (basisVec i))
      = fun y => fderiv ℝ f1 y (basisVec i) - fderiv ℝ f2 y (basisVec i) := by
    funext y
    rw [fderiv_fun_sub (hd1 y) (hd2 y)]
    simp
  rw [hfun]
  have hg1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ f1 y (basisVec i)) :=
    (hf1.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hg2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ f2 y (basisVec i)) :=
    (hf2.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdg1 : DifferentiableAt ℝ (fun y : Vec m => fderiv ℝ f1 y (basisVec i)) x :=
    (hg1.differentiable (by simp)).differentiableAt
  have hdg2 : DifferentiableAt ℝ (fun y : Vec m => fderiv ℝ f2 y (basisVec i)) x :=
    (hg2.differentiable (by simp)).differentiableAt
  rw [fderiv_fun_sub hdg1 hdg2]
  simp

/-- `lapD` is linear in its function argument, for globally smooth summands: the tool needed to
split `partialLaplacian` of the mollified slice into the partial Laplacian of the excess plus that
of the barrier. -/
theorem lapD_sub {m d : ℕ} {f1 f2 : Vec m → ℝ} (hf1 : ContDiff ℝ (⊤ : ℕ∞) f1)
    (hf2 : ContDiff ℝ (⊤ : ℕ∞) f2) (x : Vec m) :
    lapD m d (fun y => f1 y - f2 y) x = lapD m d f1 x - lapD m d f2 x := by
  unfold lapD
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · exact fderiv_fderiv_sub_apply hf1 hf2 x i
  · simp


/-- **Green's identity for `lapD`.** For a smooth, compactly supported test function `φ` and a
smooth `u`, `∫ φ · lapD u = -∑_{i<d} ∫ ∂_i φ · ∂_i u`: `d` applications of Mathlib's integration by
parts for Fréchet derivatives, one per diffusive coordinate, each licensed because `φ` and `u` are
differentiable at *every* point (not merely a.e.) — the obstruction DiPerna–Lions-type test
functions such as `comparisonPosPart` run into is exactly what the Kato smoothing of the excess
repairs. -/
theorem integral_mul_lapD_eq {m d : ℕ} {φ u : Vec m → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∫ x, φ x * lapD m d u x
      = -∑ i : Fin m, if (i : ℕ) < d then
          ∫ x, fderiv ℝ φ x (basisVec i) * fderiv ℝ u x (basisVec i) else 0 := by
  have hφcont : Continuous φ := hφ.continuous
  have hφdiff : ∀ x : Vec m, DifferentiableAt ℝ φ x :=
    fun x => (hφ.differentiable (by simp)).differentiableAt
  have hudiff : ∀ x : Vec m, DifferentiableAt ℝ u x :=
    fun x => (hu.differentiable (by simp)).differentiableAt
  have hstep : ∀ i : Fin m,
      ∫ x, φ x * fderiv ℝ (fun y => fderiv ℝ u y (basisVec i)) x (basisVec i)
        = -∫ x, fderiv ℝ φ x (basisVec i) * fderiv ℝ u x (basisVec i) := by
    intro i
    have hu2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ u y (basisVec i)) :=
      (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hu2diff : ∀ x : Vec m, DifferentiableAt ℝ (fun y => fderiv ℝ u y (basisVec i)) x :=
      fun x => (hu2.differentiable (by simp)).differentiableAt
    have hφ' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ φ y (basisVec i)) :=
      (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hφ'c : HasCompactSupport (fun y : Vec m => fderiv ℝ φ y (basisVec i)) :=
      hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hint1 : Integrable (fun x => fderiv ℝ φ x (basisVec i) * fderiv ℝ u x (basisVec i))
        volume :=
      (hφ'.continuous.mul hu2.continuous).integrable_of_hasCompactSupport (hφ'c.mul_right)
    have hu3 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m =>
        fderiv ℝ (fun z => fderiv ℝ u z (basisVec i)) y (basisVec i)) :=
      (hu2.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hint2 : Integrable (fun x => φ x * fderiv ℝ (fun y => fderiv ℝ u y (basisVec i)) x
        (basisVec i)) volume :=
      (hφcont.mul hu3.continuous).integrable_of_hasCompactSupport hφc.mul_right
    have hint3 : Integrable (fun x => φ x * fderiv ℝ u x (basisVec i)) volume :=
      (hφcont.mul hu2.continuous).integrable_of_hasCompactSupport hφc.mul_right
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint1 hint2 hint3
      (fun x _ => hφdiff x) (fun x _ => hu2diff x)
  have hdistrib : (fun x : Vec m => φ x * lapD m d u x)
      = fun x => ∑ i : Fin m, if (i : ℕ) < d then
          φ x * fderiv ℝ (fun y => fderiv ℝ u y (basisVec i)) x (basisVec i) else 0 := by
    funext x
    unfold lapD
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rfl
    · exact mul_zero _
  have hintegrableEach : ∀ i : Fin m, Integrable (fun x : Vec m => if (i : ℕ) < d then
      φ x * fderiv ℝ (fun y => fderiv ℝ u y (basisVec i)) x (basisVec i) else 0) volume := by
    intro i
    have hu2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ u y (basisVec i)) :=
      (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hu3 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m =>
        fderiv ℝ (fun z => fderiv ℝ u z (basisVec i)) y (basisVec i)) :=
      (hu2.fderiv_right (by norm_num)).clm_apply contDiff_const
    split_ifs with hi
    · exact (hφcont.mul hu3.continuous).integrable_of_hasCompactSupport hφc.mul_right
    · exact integrable_zero (Vec m) ℝ volume
  rw [hdistrib, integral_finsetSum Finset.univ (fun i _ => hintegrableEach i)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · exact hstep i
  · simp


/-- The Fréchet derivative of the truncated Kato test function `2 Φ_κ(g) Φ_κ'(g) χ²`, by the
product and chain rules. -/
theorem hasFDerivAt_kappaTestFn {m : ℕ} {g chi : Vec m → ℝ} {kap : ℝ} (hkap : 0 < kap)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (x : Vec m) :
    HasFDerivAt (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2)
      ((chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x))) • (deriv (kappaProfile kap) (g x) •
        fderiv ℝ g x)
        + (chi x ^ 2 * (2 * kappaProfile kap (g x))) • (kappaProfile2 kap (g x) • fderiv ℝ g x)
        + (2 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x)) •
            ((2 * chi x) • fderiv ℝ chi x)) x := by
  have hgx : HasFDerivAt g (fderiv ℝ g x) x :=
    (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hchix : HasFDerivAt chi (fderiv ℝ chi x) x :=
    (hchi.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hKp0 := (hasDerivAt_kappaProfile kap hkap (g x)).comp_hasFDerivAt x hgx
  have hKp : HasFDerivAt (fun y => kappaProfile kap (g y)) (deriv (kappaProfile kap) (g x) •
    fderiv ℝ g x) x := by
    rw [deriv_kappaProfile kap hkap (g x)]
    exact hKp0
  have hDp : HasFDerivAt (fun y => deriv (kappaProfile kap) (g y))
      (kappaProfile2 kap (g x) • fderiv ℝ g x) x :=
    (hasDerivAt_deriv_kappaProfile kap hkap (g x)).comp_hasFDerivAt x hgx
  have hChiSq0 := hchix.mul hchix
  have hChiSq : HasFDerivAt (fun y => chi y ^ 2) ((2 * chi x) • fderiv ℝ chi x) x := by
    have heqfun : (fun y : Vec m => chi y ^ 2) = chi * chi := by
      funext y; rw [Pi.mul_apply]; ring
    rw [heqfun]
    have hval : chi x • fderiv ℝ chi x + chi x • fderiv ℝ chi x = (2 * chi x) • fderiv ℝ chi x := by
      rw [two_mul]
      module
    rw [← hval]
    exact hChiSq0
  have h2Kp : HasFDerivAt (fun y => 2 * kappaProfile kap (g y))
      ((2 : ℝ) • (deriv (kappaProfile kap) (g x) • fderiv ℝ g x)) x := hKp.const_mul 2
  have hAB : HasFDerivAt (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y))
      ((2 * kappaProfile kap (g x)) • (kappaProfile2 kap (g x) • fderiv ℝ g x)
        + deriv (kappaProfile kap) (g x) •
          ((2 : ℝ) • (deriv (kappaProfile kap) (g x) • fderiv ℝ g x))) x :=
    h2Kp.mul hDp
  have hfinal := hAB.mul hChiSq
  have heq2 : (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y))
        * (fun y => chi y ^ 2)
      = fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2 := by
    funext y; rw [Pi.mul_apply]
  rw [heq2] at hfinal
  have hvaleq : (2 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x)) •
        ((2 * chi x) • fderiv ℝ chi x)
      + chi x ^ 2 •
        ((2 * kappaProfile kap (g x)) • (kappaProfile2 kap (g x) • fderiv ℝ g x)
          + deriv (kappaProfile kap) (g x) •
            ((2 : ℝ) • (deriv (kappaProfile kap) (g x) • fderiv ℝ g x)))
      = (chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x))) •
          (deriv (kappaProfile kap) (g x) • fderiv ℝ g x)
        + (chi x ^ 2 * (2 * kappaProfile kap (g x))) • (kappaProfile2 kap (g x) • fderiv ℝ g x)
        + (2 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x)) •
            ((2 * chi x) • fderiv ℝ chi x) := by
    module
  rwa [hvaleq] at hfinal



/-- The value of the derivative of the truncated-Kato test function `2 Φ_κ(g) Φ_κ'(g) χ²` in a
direction `v`, by the product/chain rule. -/
theorem fderiv_kappaTestFn_apply {m : ℕ} {g chi : Vec m → ℝ} {kap : ℝ} (hkap : 0 < kap)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (x v : Vec m) :
    fderiv ℝ (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2)
        x v
      = chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x) ^ 2
            + 2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * fderiv ℝ g x v
        + 4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x * fderiv ℝ chi x v
          := by
  rw [(hasFDerivAt_kappaTestFn hkap hg hchi x).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The partial Dirichlet energy density `∑_{i<d} (∂_i g)²`. -/
@[expose] def dirichletD (m d : ℕ) (g : Vec m → ℝ) (x : Vec m) : ℝ :=
  ∑ i : Fin m, if (i : ℕ) < d then fderiv ℝ g x (basisVec i) ^ 2 else 0

/-- The mixed cutoff/gradient term `∑_{i<d} ∂_i χ · ∂_i g`. -/
@[expose] def mixedD (m d : ℕ) (g chi : Vec m → ℝ) (x : Vec m) : ℝ :=
  ∑ i : Fin m, if (i : ℕ) < d then fderiv ℝ chi x (basisVec i) * fderiv ℝ g x (basisVec i) else 0

/-- The pointwise sum `∑_{i<d} ∂_i φ · ∂_i g` for the truncated-Kato test function `φ`, in closed
form: this is exactly the sum Green's identity produces. -/
theorem sum_fderiv_kappaTestFn_mul_fderiv_eq {m d : ℕ} {g chi : Vec m → ℝ} {kap : ℝ}
    (hkap : 0 < kap) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (x : Vec m) :
    (∑ i : Fin m, if (i : ℕ) < d then
        fderiv ℝ (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2)
            x (basisVec i) * fderiv ℝ g x (basisVec i)
      else 0)
      = chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x) ^ 2
            + 2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x
        + 4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x * mixedD m d g chi
          x := by
  unfold dirichletD mixedD
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [fderiv_kappaTestFn_apply hkap hg hchi x (basisVec i)]
    ring
  · ring



/-- `deriv (kappaProfile kap)` is itself smooth, for `kap > 0`: `deriv f = fderiv ℝ f · 1`, so this
is `ContDiff.fderiv_right` applied to `kappaProfile kap` and evaluated at `1`. -/
theorem contDiff_deriv_kappaProfile (kap : ℝ) (hkap : 0 < kap) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv (kappaProfile kap)) :=
  ((contDiff_kappaProfile kap hkap).fderiv_right (by norm_num)).clm_apply contDiff_const

/-- **Green's identity for the truncated-Kato diffusion term**, combined with the product/chain
rule: the exact spatial identity behind the sign of the diffusion term. No inequality or limit
is taken: this is algebra plus one integration by parts. -/
theorem integral_kappaTestFn_mul_lapD_eq {m d : ℕ} {g chi : Vec m → ℝ} {kap : ℝ} (hkap : 0 < kap)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hchic : HasCompactSupport chi) :
    ∫ x, (2 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x ^ 2) * lapD m d g x
      = -∫ x, (chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x) ^ 2
            + 2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x
          + 4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x
              * mixedD m d g chi x) := by
  have hKp : ContDiff ℝ (⊤ : ℕ∞) (fun y => kappaProfile kap (g y)) :=
    (contDiff_kappaProfile kap hkap).comp hg
  have hDp : ContDiff ℝ (⊤ : ℕ∞) (fun y => deriv (kappaProfile kap) (g y)) :=
    (contDiff_deriv_kappaProfile kap hkap).comp hg
  have hφ : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2) :=
    ((contDiff_const.mul hKp).mul hDp).mul (hchi.pow 2)
  have hchi2c : HasCompactSupport (fun y : Vec m => chi y ^ 2) := by
    have heq0 : (fun y : Vec m => chi y ^ 2) = chi * chi := by
      funext y; rw [Pi.mul_apply]; ring
    rw [heq0]
    exact hchic.mul_right
  have hφc : HasCompactSupport
      (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2) := by
    have heq : (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2)
        = fun y => (2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y)) * chi y ^ 2 := by
      funext y; ring
    rw [heq]
    exact hchi2c.mul_left
  have hgreen := integral_mul_lapD_eq (d := d) hφ hφc hg
  rw [hgreen]
  congr 1
  have hintegrableEach : ∀ i : Fin m, Integrable (fun x : Vec m => if (i : ℕ) < d then
      fderiv ℝ (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2)
          x (basisVec i) * fderiv ℝ g x (basisVec i)
      else 0) volume := by
    intro i
    split_ifs with hi
    · have hφ' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m =>
          fderiv ℝ (fun y' => 2 * kappaProfile kap (g y') * deriv (kappaProfile kap) (g y')
              * chi y' ^ 2) y (basisVec i)) :=
        (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
      have hφ'c : HasCompactSupport (fun y : Vec m =>
          fderiv ℝ (fun y' => 2 * kappaProfile kap (g y') * deriv (kappaProfile kap) (g y')
              * chi y' ^ 2) y (basisVec i)) :=
        hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
      have hg' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ g y (basisVec i)) :=
        (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
      exact (hφ'.continuous.mul hg'.continuous).integrable_of_hasCompactSupport hφ'c.mul_right
    · exact integrable_zero (Vec m) ℝ volume
  have hifeq : ∀ i : Fin m, (if (i : ℕ) < d then
        ∫ x, fderiv ℝ (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y)
              * chi y ^ 2) x (basisVec i) * fderiv ℝ g x (basisVec i)
      else (0 : ℝ))
      = ∫ x, (if (i : ℕ) < d then
          fderiv ℝ (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y
            ^ 2)
              x (basisVec i) * fderiv ℝ g x (basisVec i)
        else 0) := by
    intro i
    split_ifs with hi
    · rfl
    · exact (integral_zero (Vec m) ℝ).symm
  rw [Finset.sum_congr rfl (fun i _ => hifeq i)]
  rw [← integral_finsetSum Finset.univ (fun i _ => hintegrableEach i)]
  have hpteq : (fun x : Vec m => ∑ i : Fin m, if (i : ℕ) < d then
        fderiv ℝ (fun y => 2 * kappaProfile kap (g y) * deriv (kappaProfile kap) (g y) * chi y ^ 2)
            x (basisVec i) * fderiv ℝ g x (basisVec i)
      else 0)
      = fun x => chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x) ^ 2
            + 2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x
          + 4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x
              * mixedD m d g chi x := by
    funext x
    exact sum_fderiv_kappaTestFn_mul_fderiv_eq hkap hg hchi x
  rw [hpteq]


/-- The partial Dirichlet energy density is continuous, when `g` is smooth. -/
theorem continuous_dirichletD {m d : ℕ} {g : Vec m → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (dirichletD m d g) := by
  unfold dirichletD
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  by_cases hi : (i : ℕ) < d
  · simp only [hi, ite_true]
    have hg' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ g y (basisVec i)) :=
      (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact hg'.continuous.pow 2
  · simp only [hi, ite_false]
    exact continuous_const

/-- The second derivative of the Kato profile is continuous in `t`, for fixed `kap > 0`. -/
theorem continuous_kappaProfile2 (kap : ℝ) (hkap : 0 < kap) : Continuous (kappaProfile2 kap) := by
  unfold kappaProfile2
  have hsne : ∀ t : ℝ, (2 : ℝ) * Real.sqrt (t ^ 2 + kap ^ 2) ^ 3 ≠ 0 :=
    fun t => by positivity
  have hscont : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 + kap ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_pow 2 |>.add continuous_const)
  exact continuous_const.div (continuous_const.mul (hscont.pow 3)) hsne

/-- The curvature-term integrand is continuous, for fixed `kap > 0`. -/
theorem continuous_integrand_curvature {m d : ℕ} {g chi : Vec m → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) {kap : ℝ} (hkap : 0 < kap) :
    Continuous (fun x : Vec m => chi x ^ 2
      * (2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x) := by
  have h1 : Continuous (fun x : Vec m => kappaProfile kap (g x)) :=
    (contDiff_kappaProfile kap hkap).continuous.comp hg.continuous
  have h2 : Continuous (fun x : Vec m => kappaProfile2 kap (g x)) :=
    (continuous_kappaProfile2 kap hkap).comp hg.continuous
  exact ((hchi.continuous.pow 2).mul ((continuous_const.mul h1).mul h2)).mul
    (continuous_dirichletD hg)

/-- **The diffusion term's curvature contribution vanishes as `kap ↓ 0`, as an integral over all of
`Vec m`.** Dominated convergence: `abs_kappaProfile_mul_kappaProfile2_le` supplies the
`kap`-independent dominating function `χ² · dirichletD` (integrable, since `χ` has compact support
and `dirichletD` is continuous), and `tendsto_kappaProfile_mul_kappaProfile2_nhds_zero` supplies the
pointwise limit `0`. This is the resolution, at the level of the full spatial integral rather than
pointwise, of the sign question this module exists to answer. -/
theorem tendsto_integral_curvature_term_nhds_zero {m d : ℕ} {g chi : Vec m → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hchic : HasCompactSupport chi) :
    Tendsto (fun kap : ℝ => ∫ x, chi x ^ 2
        * (2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hchi2c : HasCompactSupport (fun y : Vec m => chi y ^ 2) := by
    have heq0 : (fun y : Vec m => chi y ^ 2) = chi * chi := by
      funext y; rw [Pi.mul_apply]; ring
    rw [heq0]
    exact hchic.mul_right
  have hbound_integrable : Integrable (fun x : Vec m => chi x ^ 2 * dirichletD m d g x) volume := by
    have hcont : Continuous (fun x : Vec m => chi x ^ 2 * dirichletD m d g x) :=
      (hchi.continuous.pow 2).mul (continuous_dirichletD hg)
    have hcs : HasCompactSupport (fun x : Vec m => chi x ^ 2 * dirichletD m d g x) :=
      hchi2c.mul_right
    exact hcont.integrable_of_hasCompactSupport hcs
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
    (F := fun kap x => chi x ^ 2
      * (2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x)
    (f := fun _ : Vec m => (0 : ℝ))
    (fun x : Vec m => chi x ^ 2 * dirichletD m d g x) ?_ ?_ hbound_integrable ?_
  · rwa [integral_zero] at hmain
  · filter_upwards [self_mem_nhdsWithin] with kap hkap
    exact (continuous_integrand_curvature hg hchi hkap).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with kap hkap
    filter_upwards with x
    have hb := abs_kappaProfile_mul_kappaProfile2_le kap hkap (g x)
    have hnn : (0 : ℝ) ≤ chi x ^ 2 * dirichletD m d g x := by
      have h1 : (0:ℝ) ≤ chi x ^ 2 := sq_nonneg _
      have h2 : (0:ℝ) ≤ dirichletD m d g x := by
        unfold dirichletD
        exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
      exact mul_nonneg h1 h2
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |chi x ^ 2| = chi x ^ 2 := abs_of_nonneg (sq_nonneg _)
    have h2 : |dirichletD m d g x| = dirichletD m d g x := by
      unfold dirichletD
      exact abs_of_nonneg (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)
    rw [h1, h2]
    calc chi x ^ 2 * |2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)| * dirichletD m d g x
        ≤ chi x ^ 2 * 1 * dirichletD m d g x := by
          have hd : (0:ℝ) ≤ dirichletD m d g x := by
            unfold dirichletD
            exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
          have habs2 : |2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)| ≤ 1 := by
            have : (2:ℝ) * kappaProfile kap (g x) * kappaProfile2 kap (g x)
                = 2 * (kappaProfile kap (g x) * kappaProfile2 kap (g x)) := by ring
            rw [this, abs_mul]
            have h2abs : |(2:ℝ)| = 2 := by norm_num
            rw [h2abs]
            linarith only [hb]
          have := mul_le_mul_of_nonneg_left habs2 (sq_nonneg (chi x))
          exact mul_le_mul_of_nonneg_right this hd
      _ = chi x ^ 2 * dirichletD m d g x := by ring
  · filter_upwards with x
    have h := tendsto_kappaProfile_mul_kappaProfile2_nhds_zero (g x)
    have hA : Tendsto (fun _ : ℝ => (2 : ℝ)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (2 : ℝ)) :=
      tendsto_const_nhds
    have hB : Tendsto (fun kap : ℝ => (2:ℝ) * (kappaProfile kap (g x) * kappaProfile2 kap (g x)))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((2:ℝ) * 0)) := hA.mul h
    have hCconst : Tendsto (fun _ : ℝ => chi x ^ 2) (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (chi x ^ 2)) := tendsto_const_nhds
    have hC : Tendsto (fun kap : ℝ => chi x ^ 2
        * ((2:ℝ) * (kappaProfile kap (g x) * kappaProfile2 kap (g x))))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (chi x ^ 2 * ((2:ℝ) * 0))) := hCconst.mul hB
    have hDconst : Tendsto (fun _ : ℝ => dirichletD m d g x) (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (dirichletD m d g x)) := tendsto_const_nhds
    have hD : Tendsto (fun kap : ℝ => chi x ^ 2
        * ((2:ℝ) * (kappaProfile kap (g x) * kappaProfile2 kap (g x))) * dirichletD m d g x)
        (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (chi x ^ 2 * ((2:ℝ) * 0) * dirichletD m d g x)) := hC.mul hDconst
    have hval : chi x ^ 2 * ((2:ℝ) * 0) * dirichletD m d g x = 0 := by ring
    rw [hval] at hD
    have heq : (fun kap : ℝ => chi x ^ 2
        * (2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x)
        = fun kap : ℝ => chi x ^ 2 * ((2:ℝ) * (kappaProfile kap (g x) * kappaProfile2 kap (g x)))
            * dirichletD m d g x := by
      funext kap; ring
    rwa [heq]


/-! ### The barrier reduction: transferring the mollified equation's estimate to the excess

The next three declarations combine `barrier_supersolution` with the linearity of `gradPair` and
`partialLaplacian` over subtraction, given only the spatial smoothness
`contDiff_mollifySlice`/`contDiff_barrier` supply at a fixed time slice — no joint space-time
smoothness of either summand is assumed, and `hCont`/`hLoc` play no role here. The reduction
shows that the Laplacian-minus-drift combination of the mollified slice, once the barrier's own
time derivative `σ · K` is subtracted, is bounded above by the same combination for the excess
`g = q_ε − Ψ_σ` alone: whatever the mollified equation supplies for `q_ε` therefore transfers to
`g` without loss, since `barrier_supersolution` supplies exactly enough slack
(`0 ≤ σK + ∇Ψ_σ · B − Δ_XΨ_σ`) to absorb the barrier's own Laplacian and drift terms. -/

/-- `gradPair` is linear over subtraction, given the spatial-slice smoothness of each summand at
the point's own time coordinate. -/
theorem gradPair_sub {m : ℕ} {f f2 : Vec m × ℝ → ℝ} (z : Vec m × ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => f (x, z.2)))
    (hf2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => f2 (x, z.2))) (v : Vec m) :
    gradPair m (fun w => f w - f2 w) z v = gradPair m f z v - gradPair m f2 z v := by
  unfold gradPair
  have hdf : DifferentiableAt ℝ (fun x : Vec m => f (x, z.2)) z.1 :=
    (hf.differentiable (by simp)).differentiableAt
  have hdf2 : DifferentiableAt ℝ (fun x : Vec m => f2 (x, z.2)) z.1 :=
    (hf2.differentiable (by simp)).differentiableAt
  rw [show (fun x : Vec m => (fun w => f w - f2 w) (x, z.2))
      = fun x : Vec m => f (x, z.2) - f2 (x, z.2) from rfl]
  rw [fderiv_fun_sub hdf hdf2]
  simp

/-- `partialLaplacian` is linear over subtraction, given the same spatial-slice smoothness as
`gradPair_sub`: this is `lapD_sub` transported across `partialLaplacian_eq_lapD`. -/
theorem partialLaplacian_sub {m d : ℕ} {f f2 : Vec m × ℝ → ℝ} (z : Vec m × ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => f (x, z.2)))
    (hf2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => f2 (x, z.2))) :
    partialLaplacian m d (fun w => f w - f2 w) z
      = partialLaplacian m d f z - partialLaplacian m d f2 z := by
  rw [partialLaplacian_eq_lapD, partialLaplacian_eq_lapD, partialLaplacian_eq_lapD]
  rw [show (fun y : Vec m => (fun w => f w - f2 w) (y, z.2))
      = fun y : Vec m => (fun x => f (x, z.2)) y - (fun x => f2 (x, z.2)) y from rfl]
  exact lapD_sub hf hf2 z.1

/-- **The barrier reduction.** With the rate `K = barrierRate m d Λ` of `barrier_supersolution`,
the Laplacian-minus-drift combination of the mollified slice, less the barrier's own time
derivative `σK`, is bounded above by the same combination for the excess
`g = fun y => mollifySlice m ε q (y, s) - barrier m M σ K τ₀ (y, s)`. -/
theorem partialLaplacian_sub_gradPair_mollifySlice_sub_le
    {m d : ℕ} {ε M σ τ₀ Λ Minf s : ℝ} (hε : 0 < ε) (hσ : 0 ≤ σ)
    {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, s)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, s)| ≤ Minf)
    {B : Vec m × ℝ → Vec m} (x : Vec m) (hB : ‖B (x, s)‖ ≤ Λ) :
    partialLaplacian m d (mollifySlice m ε q) (x, s)
        - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
        - σ * barrierRate m d Λ
      ≤ lapD m d (fun y => mollifySlice m ε q (y, s)
            - barrier m M σ (barrierRate m d Λ) τ₀ (y, s)) x
        - fderiv ℝ (fun y => mollifySlice m ε q (y, s)
            - barrier m M σ (barrierRate m d Λ) τ₀ (y, s)) x (B (x, s)) := by
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => mollifySlice m ε q (y, s)) :=
    contDiff_mollifySlice hε s q Minf hmeas hbdd
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => barrier m M σ (barrierRate m d Λ) τ₀ (y, s)) :=
    (contDiff_barrier M σ (barrierRate m d Λ) τ₀).comp (contDiff_id.prodMk contDiff_const)
  have hsuper := barrier_supersolution (m := m) d M τ₀ Λ hσ B (x, s) hB
  have htime : timeDeriv m (barrier m M σ (barrierRate m d Λ) τ₀) (x, s) = σ * barrierRate m d Λ :=
    timeDeriv_barrier M σ (barrierRate m d Λ) τ₀ (x, s)
  have hgp := gradPair_sub (f := mollifySlice m ε q) (f2 := barrier m M σ (barrierRate m d Λ) τ₀)
    (x, s) hQ hΨ (B (x, s))
  have hlap := partialLaplacian_sub (m := m) (d := d) (f := mollifySlice m ε q)
    (f2 := barrier m M σ (barrierRate m d Λ) τ₀) (x, s) hQ hΨ
  have hlapD : partialLaplacian m d
      (fun w => mollifySlice m ε q w - barrier m M σ (barrierRate m d Λ) τ₀ w) (x, s)
      = lapD m d (fun y => mollifySlice m ε q (y, s)
          - barrier m M σ (barrierRate m d Λ) τ₀ (y, s)) x :=
    partialLaplacian_eq_lapD _ (x, s)
  have hgpEq : gradPair m
      (fun w => mollifySlice m ε q w - barrier m M σ (barrierRate m d Λ) τ₀ w) (x, s) (B (x, s))
      = fderiv ℝ (fun y => mollifySlice m ε q (y, s)
          - barrier m M σ (barrierRate m d Λ) τ₀ (y, s)) x (B (x, s)) := rfl
  rw [hgpEq] at hgp
  linarith only [hsuper, htime, hgp, hlap, hlapD]

/-! ### The Cauchy–Schwarz bound on the truncated-Kato/commutator pairing

`two_mul_mul_le_two_mul_abs_mul_abs` and `integral_abs_mul_abs_le_sqrt_mul_sqrt` are combined here
to bound the pairing of the truncated Kato test function's leading factor against an arbitrary
square-integrable right-hand term `c` (the commutator or drift-type forcing of
`eq:aniso:comparison:mollified`), truncated by `mollifierCutoff m R`. Once
`kappaProfile kap (g ·) * mollifierCutoff m R` is identified with
`comparisonPosPart * mollifierCutoff m R` as `kap ↓ 0`
(`integral_sq_mul_mollifierCutoff_eq_comparisonEnergy` makes its squared integral exactly
`comparisonEnergy`), the right side becomes the `2 √E · r` shape of the hypothesis `hineq` of
`comparisonEnergy_le_exp_mul_integral_sq`; the `kap ↓ 0` limit of the truncated Kato energy is
`tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonEnergy` below. -/

/-- **The Cauchy–Schwarz commutator bound.** `deriv (kappaProfile kap) ∈ [0, 1]`
(`deriv_kappaProfile_mem_Icc`) and `mollifierCutoff m R ∈ [0, 1]`
(`mollifierCutoff_nonneg`/`mollifierCutoff_le_one`) let the pointwise bound
`two_mul_mul_le_two_mul_abs_mul_abs` discard both factors at the cost of absolute values, and
`integral_mono` transports it to the integral, which `integral_abs_mul_abs_le_sqrt_mul_sqrt` then
bounds by twice the product of the `L²` norms of `kappaProfile kap (g ·) * mollifierCutoff m R`
and `c`. -/
theorem integral_kappaProfile_mul_deriv_mul_mollifierCutoff_sq_le
    {m : ℕ} {g c : Vec m → ℝ} {kap R : ℝ} (hkap : 0 < kap) (hR : 0 < R)
    (hMemF : MemLp (fun x => kappaProfile kap (g x) * mollifierCutoff m R x) 2 volume)
    (hMemc : MemLp c 2 volume)
    (hInt : Integrable (fun x => 2 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x)
        * c x * mollifierCutoff m R x ^ 2) volume)
    (hInt2 : Integrable
        (fun x => 2 * |kappaProfile kap (g x) * mollifierCutoff m R x| * |c x|) volume) :
    (∫ x, 2 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * c x
        * mollifierCutoff m R x ^ 2)
      ≤ 2 * Real.sqrt (∫ x, (kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2)
          * Real.sqrt (∫ x, c x ^ 2) := by
  have hpt : ∀ x : Vec m, 2 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * c x
      * mollifierCutoff m R x ^ 2
      ≤ 2 * |kappaProfile kap (g x) * mollifierCutoff m R x| * |c x| := by
    intro x
    have hd := deriv_kappaProfile_mem_Icc kap hkap (g x)
    exact two_mul_mul_le_two_mul_abs_mul_abs (fun y => kappaProfile kap (g y)) c
      (mollifierCutoff m R) (fun y => deriv (kappaProfile kap) (g y)) x
      hd.1 hd.2 (mollifierCutoff_nonneg m R hR x) (mollifierCutoff_le_one m R hR x)
  have hmono := integral_mono hInt hInt2 hpt
  have hCS := integral_abs_mul_abs_le_sqrt_mul_sqrt
      (fun x => kappaProfile kap (g x) * mollifierCutoff m R x) c hMemF hMemc
  have hscale : (∫ x, 2 * |kappaProfile kap (g x) * mollifierCutoff m R x| * |c x|)
      = 2 * ∫ x, |kappaProfile kap (g x) * mollifierCutoff m R x| * |c x| := by
    have heq : (fun x : Vec m => 2 * |kappaProfile kap (g x) * mollifierCutoff m R x| * |c x|)
        = fun x => 2 * (|kappaProfile kap (g x) * mollifierCutoff m R x| * |c x|) := by
      funext x; ring
    rw [heq, integral_const_mul]
  calc (∫ x, 2 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * c x
        * mollifierCutoff m R x ^ 2)
      ≤ ∫ x, 2 * |kappaProfile kap (g x) * mollifierCutoff m R x| * |c x| := hmono
    _ = 2 * ∫ x, |kappaProfile kap (g x) * mollifierCutoff m R x| * |c x| := hscale
    _ ≤ 2 * (Real.sqrt (∫ x, (kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2)
          * Real.sqrt (∫ x, c x ^ 2)) := mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ = 2 * Real.sqrt (∫ x, (kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2)
          * Real.sqrt (∫ x, c x ^ 2) := by ring

/-! ### The dissipation term's sign and the mixed-cutoff term's `kap ↓ 0` limit

The remaining two pieces of `integral_kappaTestFn_mul_lapD_eq`'s right-hand side: the
dissipation summand `chi² · 2 (Φ_κ'(g))² · dirichletD`, nonnegative for every `kap > 0` with no
limit needed, and the mixed-cutoff summand `4 Φ_κ(g) Φ_κ'(g) chi · mixedD`, whose `kap ↓ 0` limit is
computed here by dominated convergence, as in `tendsto_integral_curvature_term_nhds_zero`.

The mixed term does not vanish for fixed `kap`. Once a cutoff radius `R` is fixed at or above the
support radius of `comparisonPosPart`, `mixedD` is supported where the cutoff's own gradient is
nonzero, which — by `comparisonPosPart_eq_zero_of_norm_ge` — is exactly where the excess `g`
itself is `≤ 0`. That does **not** make `kappaProfile kap (g ·)` vanish there for a fixed `kap`:
`kappaProfile_neg_of_neg` shows it is strictly negative on all of `{g < 0}`, not merely in the
limit `kap ↓ 0` (only `kappaProfile_zero` gives an exact zero, at `g = 0` alone). So the mixed
term does not vanish identically for fixed `kap`; its `kap ↓ 0` limit does, under the
disjoint-support hypothesis of `tendsto_integral_mixed_term_nhds_zero_of_disjoint`. -/

/-- `dirichletD` is a sum of squares, hence nonnegative. -/
theorem dirichletD_nonneg {m d : ℕ} (g : Vec m → ℝ) (x : Vec m) :
    0 ≤ dirichletD m d g x := by
  unfold dirichletD
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

/-- **The dissipation term's sign.** The dissipation contribution `chi² · 2 (Φ_κ'(g))² ·
dirichletD` to `integral_kappaTestFn_mul_lapD_eq`'s curvature/dissipation summand is nonnegative for
every `kap`, since it needs only that a square is nonnegative and `dirichletD` is a sum of squares —
so it contributes no obstruction to an upper bound on the diffusion term and may always be
dropped. -/
theorem kappaTestFn_dissipation_nonneg {m d : ℕ} (g chi : Vec m → ℝ) (kap : ℝ) (x : Vec m) :
    0 ≤ chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x) ^ 2) * dirichletD m d g x :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) (dirichletD_nonneg g x)

/-- Adding the dissipation term back to the curvature term can only increase it: the pointwise form
of "the dissipation term may be dropped when an upper bound is wanted". -/
theorem kappaTestFn_curvature_le_dissipation_add_curvature {m d : ℕ} (g chi : Vec m → ℝ) (kap : ℝ)
    (x : Vec m) :
    chi x ^ 2 * (2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x
      ≤ chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x) ^ 2
            + 2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x := by
  have hdiss := kappaTestFn_dissipation_nonneg (d := d) g chi kap x
  have heq : chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x) ^ 2
        + 2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x
      - chi x ^ 2 * (2 * kappaProfile kap (g x) * kappaProfile2 kap (g x)) * dirichletD m d g x
      = chi x ^ 2 * (2 * deriv (kappaProfile kap) (g x) ^ 2) * dirichletD m d g x := by ring
  linarith only [hdiss, heq]

/-- **The Kato profile is strictly negative below `0`.** This is why the disjoint support of `g₊`
does not make the mixed-cutoff term vanish identically for a fixed `kap`: `kappaProfile kap`
vanishes only exactly at `t = 0` (`kappaProfile_zero`), not on the whole ray
`t ≤ 0`, so being supported where `g ≤ 0` does not make `kappaProfile kap (g ·)` vanish there. -/
theorem kappaProfile_neg_of_neg (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : t < 0) :
    kappaProfile kap t < 0 := by
  rw [kappaProfile_eq]
  have hpos : 0 < kap - t := by linarith only [hkap, ht]
  have hsq : (t ^ 2 + kap ^ 2 : ℝ) < (kap - t) ^ 2 := by nlinarith only [hkap, ht]
  have hlt : Real.sqrt (t ^ 2 + kap ^ 2) < kap - t := by
    calc Real.sqrt (t ^ 2 + kap ^ 2) < Real.sqrt ((kap - t) ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) hsq
      _ = kap - t := Real.sqrt_sq hpos.le
  linarith only [hlt]

/-- The mixed cutoff/gradient density is continuous, when `g` and `chi` are smooth. -/
theorem continuous_mixedD {m d : ℕ} {g chi : Vec m → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) : Continuous (mixedD m d g chi) := by
  unfold mixedD
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  by_cases hi : (i : ℕ) < d
  · simp only [hi, ite_true]
    have hchi' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ chi y (basisVec i)) :=
      (hchi.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hg' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ g y (basisVec i)) :=
      (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact hchi'.continuous.mul hg'.continuous
  · simp only [hi, ite_false]
    exact continuous_const

/-- **The `kap`-uniform bound on the Kato profile**, the domination ingredient for the mixed-term
limit: `|Φ_κ(t)| ≤ |t| + kap / 2`, from the two-sided sandwich `max t 0 - kap/2 ≤ Φ_κ(t) ≤ max t 0`
against `katoSmooth`. -/
theorem abs_kappaProfile_le (kap : ℝ) (hkap : 0 < kap) (t : ℝ) :
    |kappaProfile kap t| ≤ |t| + kap / 2 := by
  have hlow := posPart_sub_katoSmooth_le kap id t
  have hup := katoSmooth_le_posPart kap hkap id t
  have e1 : (id t : ℝ) = t := rfl
  have e2 : katoSmooth kap id t = kappaProfile kap t := rfl
  rw [e1, e2] at hlow hup
  have hmaxnn : (0:ℝ) ≤ max t 0 := le_max_right t 0
  have hmaxabs : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
  rw [abs_le]
  constructor
  · linarith only [hlow, hmaxnn, abs_nonneg t]
  · linarith only [hup, hmaxabs, hkap]

/-- **The mixed-cutoff term's `kap ↓ 0` limit, by dominated convergence.** Structurally identical
to `tendsto_integral_curvature_term_nhds_zero`: `tendsto_kappaProfile_mul_deriv_kappaProfile`
supplies the pointwise limit `Φ_κ(g) Φ_κ'(g) → max(g, 0)`, and `abs_kappaProfile_le` (restricted to
`kap ≤ 1`, where it gives a `kap`-independent bound) supplies the dominating function
`4 (|g| + 1/2) |chi| |mixedD|`, integrable because `chi` has compact support and every other factor
is continuous. The resulting limit integral is `4 ∫ max(g, 0) · chi · mixedD`, not `0` in general —
see the module docstring above and `tendsto_integral_mixed_term_nhds_zero_of_disjoint` below for the
extra, application-specific hypothesis under which it is `0`. -/
theorem tendsto_integral_mixed_term_nhds_zero {m d : ℕ} {g chi : Vec m → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hchic : HasCompactSupport chi) :
    Tendsto (fun kap : ℝ => ∫ x, 4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x
        * mixedD m d g chi x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, 4 * max (g x) 0 * chi x * mixedD m d g chi x)) := by
  have habsChic : HasCompactSupport (fun x : Vec m => |chi x|) := hchic.abs
  have hbound1cs : HasCompactSupport (fun x : Vec m => |chi x| * |mixedD m d g chi x|) :=
    habsChic.mul_right
  have hbound1cont : Continuous (fun x : Vec m => |chi x| * |mixedD m d g chi x|) :=
    hchi.continuous.abs.mul (continuous_mixedD hg hchi).abs
  have hboundcont : Continuous
      (fun x : Vec m => 4 * (|g x| + 1 / 2) * (|chi x| * |mixedD m d g chi x|)) :=
    (continuous_const.mul (hg.continuous.abs.add continuous_const)).mul hbound1cont
  have hboundcs : HasCompactSupport
      (fun x : Vec m => 4 * (|g x| + 1 / 2) * (|chi x| * |mixedD m d g chi x|)) :=
    hbound1cs.mul_left
  have hbound_integrable : Integrable
      (fun x : Vec m => 4 * (|g x| + 1 / 2) * (|chi x| * |mixedD m d g chi x|)) volume :=
    hboundcont.integrable_of_hasCompactSupport hboundcs
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
    (F := fun kap x => 4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x
        * mixedD m d g chi x)
    (f := fun x : Vec m => 4 * max (g x) 0 * chi x * mixedD m d g chi x)
    (fun x : Vec m => 4 * (|g x| + 1 / 2) * (|chi x| * |mixedD m d g chi x|)) ?_ ?_
    hbound_integrable ?_
  · exact hmain
  · filter_upwards [self_mem_nhdsWithin] with kap hkap
    have hkap0 : 0 < kap := hkap
    have h1 : Continuous (fun x : Vec m => kappaProfile kap (g x)) :=
      (contDiff_kappaProfile kap hkap0).continuous.comp hg.continuous
    have h2 : Continuous (fun x : Vec m => deriv (kappaProfile kap) (g x)) :=
      (contDiff_deriv_kappaProfile kap hkap0).continuous.comp hg.continuous
    have hcont : Continuous (fun x : Vec m => 4 * kappaProfile kap (g x)
        * deriv (kappaProfile kap) (g x) * chi x * mixedD m d g chi x) :=
      (((continuous_const.mul h1).mul h2).mul hchi.continuous).mul (continuous_mixedD hg hchi)
    exact hcont.aestronglyMeasurable
  · have hnbhd : Set.Iio (1:ℝ) ∈ 𝓝 (0:ℝ) := isOpen_Iio.mem_nhds (by norm_num)
    have hmem : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := mem_nhdsWithin_of_mem_nhds hnbhd
    filter_upwards [self_mem_nhdsWithin, hmem] with kap hkap hkap1
    have hkap0 : 0 < kap := hkap
    have hkapleone : kap ≤ 1 := le_of_lt hkap1
    filter_upwards with x
    rw [Real.norm_eq_abs]
    have hA : |kappaProfile kap (g x)| ≤ |g x| + 1 / 2 := by
      have h := abs_kappaProfile_le kap hkap0 (g x)
      linarith only [h, hkapleone]
    have hBicc := deriv_kappaProfile_mem_Icc kap hkap0 (g x)
    have hB : |deriv (kappaProfile kap) (g x)| ≤ 1 := by
      rw [abs_of_nonneg hBicc.1]; exact hBicc.2
    have hCDnn : (0:ℝ) ≤ |chi x| * |mixedD m d g chi x| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hAnn : (0:ℝ) ≤ |g x| + 1/2 := by positivity
    have hstep1 : |kappaProfile kap (g x)| * |deriv (kappaProfile kap) (g x)|
        ≤ (|g x| + 1/2) * 1 := by
      calc |kappaProfile kap (g x)| * |deriv (kappaProfile kap) (g x)|
          ≤ (|g x| + 1/2) * |deriv (kappaProfile kap) (g x)| :=
            mul_le_mul_of_nonneg_right hA (abs_nonneg _)
        _ ≤ (|g x| + 1/2) * 1 := mul_le_mul_of_nonneg_left hB hAnn
    have hstep2 : 4 * (|kappaProfile kap (g x)| * |deriv (kappaProfile kap) (g x)|)
        * (|chi x| * |mixedD m d g chi x|)
        ≤ 4 * ((|g x| + 1/2) * 1) * (|chi x| * |mixedD m d g chi x|) := by
      have h4 : 4 * (|kappaProfile kap (g x)| * |deriv (kappaProfile kap) (g x)|)
          ≤ 4 * ((|g x| + 1/2) * 1) := by linarith only [hstep1]
      exact mul_le_mul_of_nonneg_right h4 hCDnn
    have hlhs : |4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x
          * mixedD m d g chi x|
        = 4 * (|kappaProfile kap (g x)| * |deriv (kappaProfile kap) (g x)|)
            * (|chi x| * |mixedD m d g chi x|) := by
      rw [show (4:ℝ) * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x
            * mixedD m d g chi x
          = 4 * (kappaProfile kap (g x) * deriv (kappaProfile kap) (g x))
              * (chi x * mixedD m d g chi x) from by ring]
      simp only [abs_mul]
      norm_num
    have hrhs : 4 * ((|g x| + 1/2) * 1) * (|chi x| * |mixedD m d g chi x|)
        = 4 * (|g x| + 1 / 2) * (|chi x| * |mixedD m d g chi x|) := by ring
    rw [hlhs, ← hrhs]
    exact hstep2
  · filter_upwards with x
    have h := tendsto_kappaProfile_mul_deriv_kappaProfile (g x)
    have hconst4 : Tendsto (fun _ : ℝ => (4:ℝ)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (4:ℝ)) :=
      tendsto_const_nhds
    have hconstchi : Tendsto (fun _ : ℝ => chi x) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (chi x)) :=
      tendsto_const_nhds
    have hconstD : Tendsto (fun _ : ℝ => mixedD m d g chi x) (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (mixedD m d g chi x)) := tendsto_const_nhds
    have h1 : Tendsto (fun kap : ℝ => (4:ℝ)
        * (kappaProfile kap (g x) * deriv (kappaProfile kap) (g x)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((4:ℝ) * max (g x) 0)) := hconst4.mul h
    have h2 : Tendsto (fun kap : ℝ => (4:ℝ)
        * (kappaProfile kap (g x) * deriv (kappaProfile kap) (g x)) * chi x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((4:ℝ) * max (g x) 0 * chi x)) :=
      h1.mul hconstchi
    have h3 : Tendsto (fun kap : ℝ => (4:ℝ)
        * (kappaProfile kap (g x) * deriv (kappaProfile kap) (g x)) * chi x
          * mixedD m d g chi x) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((4:ℝ) * max (g x) 0 * chi x * mixedD m d g chi x)) := h2.mul hconstD
    have heq : (fun kap : ℝ => 4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x
        * mixedD m d g chi x)
        = fun kap : ℝ => (4:ℝ) * (kappaProfile kap (g x) * deriv (kappaProfile kap) (g x))
            * chi x * mixedD m d g chi x := by
      funext kap; ring
    rwa [heq]

/-- **The mixed-cutoff term's `kap ↓ 0` limit is `0` under a disjoint-support hypothesis.** Not
an identity holding for every fixed `kap`, but a `kap ↓ 0` limit resting on
`tendsto_integral_mixed_term_nhds_zero`, once `max (g ·) 0` and `mixedD m d g chi` have disjoint
supports pointwise. For the excess and the cutoff `mollifierCutoff m R`, this hypothesis comes from
`mollifierCutoff_eq_one` and `comparisonPosPart_eq_zero_of_norm_ge`. -/
theorem tendsto_integral_mixed_term_nhds_zero_of_disjoint {m d : ℕ} {g chi : Vec m → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hchic : HasCompactSupport chi)
    (hdisj : ∀ x : Vec m, max (g x) 0 * mixedD m d g chi x = 0) :
    Tendsto (fun kap : ℝ => ∫ x, 4 * kappaProfile kap (g x) * deriv (kappaProfile kap) (g x) * chi x
        * mixedD m d g chi x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmain := tendsto_integral_mixed_term_nhds_zero (d := d) hg hchi hchic
  have heq0 : (∫ x, 4 * max (g x) 0 * chi x * mixedD m d g chi x) = 0 := by
    have hz : (fun x : Vec m => 4 * max (g x) 0 * chi x * mixedD m d g chi x) = fun _ => (0:ℝ) := by
      funext x
      have h := hdisj x
      have hre : (4:ℝ) * max (g x) 0 * chi x * mixedD m d g chi x
          = 4 * chi x * (max (g x) 0 * mixedD m d g chi x) := by ring
      rw [hre, h, mul_zero]
    rw [hz, integral_zero]
  rwa [heq0] at hmain

/-! ### The `kap ↓ 0` identification of the truncated Kato energy with `comparisonEnergy`

`integral_sq_mul_mollifierCutoff_eq_comparisonEnergy` identifies the truncated energy
`∫ (comparisonPosPart · mollifierCutoff m R)²` with `comparisonEnergy`; it says
nothing about `∫ (kappaProfile kap (g ·) · mollifierCutoff m R)²`, since `comparisonPosPart =
max (g ·) 0` and `kappaProfile kap (g ·)` are different functions at every fixed `kap` — e.g.
`kappaProfile 1 (-1) ≠ max (-1) 0`. They agree only as `kap ↓ 0`. The three theorems below supply
that limit, by dominated convergence as in `tendsto_integral_mixed_term_nhds_zero` above:
`tendsto_katoSmooth` gives the pointwise limit `kappaProfile kap t → max t 0`, and
`abs_kappaProfile_le` (restricted to `kap ≤ 1`) gives the `kap`-independent dominating function
`(|g ·| + 1/2)² · mollifierCutoff m R ²`, integrable because `mollifierCutoff m R` has compact
support (`hasCompactSupport_mollifierCutoff`) and every other factor is continuous. -/

/-- **The squared truncated Kato profile converges to the squared truncated positive part**, for
any continuous `g : Vec m → ℝ` and cutoff radius `R > 0`, as `kap ↓ 0`. -/
theorem tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_zero {m : ℕ} {g : Vec m → ℝ}
    {R : ℝ} (hg : Continuous g) (hR : 0 < R) :
    Tendsto (fun kap : ℝ => ∫ x, (kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, (max (g x) 0 * mollifierCutoff m R x) ^ 2)) := by
  have hcs : HasCompactSupport (mollifierCutoff m R) := hasCompactSupport_mollifierCutoff m R hR
  have hcs2 : HasCompactSupport (fun x : Vec m => mollifierCutoff m R x ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hgabs : Continuous (fun x : Vec m => |g x| + 1 / 2) := hg.abs.add continuous_const
  have hboundcont : Continuous
      (fun x : Vec m => (|g x| + 1 / 2) ^ 2 * mollifierCutoff m R x ^ 2) :=
    (hgabs.pow 2).mul ((contDiff_mollifierCutoff m R hR).continuous.pow 2)
  have hboundcs : HasCompactSupport
      (fun x : Vec m => (|g x| + 1 / 2) ^ 2 * mollifierCutoff m R x ^ 2) := hcs2.mul_left
  have hbound_integrable : Integrable
      (fun x : Vec m => (|g x| + 1 / 2) ^ 2 * mollifierCutoff m R x ^ 2) volume :=
    hboundcont.integrable_of_hasCompactSupport hboundcs
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
    (F := fun kap x => (kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2)
    (f := fun x : Vec m => (max (g x) 0 * mollifierCutoff m R x) ^ 2)
    (fun x : Vec m => (|g x| + 1 / 2) ^ 2 * mollifierCutoff m R x ^ 2) ?_ ?_
    hbound_integrable ?_
  · exact hmain
  · filter_upwards [self_mem_nhdsWithin] with kap hkap
    have hkap0 : 0 < kap := hkap
    have h1 : Continuous (fun x : Vec m => kappaProfile kap (g x)) :=
      (contDiff_kappaProfile kap hkap0).continuous.comp hg
    have hcont : Continuous
        (fun x : Vec m => (kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2) :=
      (h1.mul (contDiff_mollifierCutoff m R hR).continuous).pow 2
    exact hcont.aestronglyMeasurable
  · have hnbhd : Set.Iio (1:ℝ) ∈ 𝓝 (0:ℝ) := isOpen_Iio.mem_nhds (by norm_num)
    have hmem : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := mem_nhdsWithin_of_mem_nhds hnbhd
    filter_upwards [self_mem_nhdsWithin, hmem] with kap hkap hkap1
    have hkap0 : 0 < kap := hkap
    have hkapleone : kap ≤ 1 := le_of_lt hkap1
    filter_upwards with x
    have hA : |kappaProfile kap (g x)| ≤ |g x| + 1 / 2 := by
      have h := abs_kappaProfile_le kap hkap0 (g x)
      linarith only [h, hkapleone]
    have hsq : kappaProfile kap (g x) ^ 2 ≤ (|g x| + 1 / 2) ^ 2 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg (kappaProfile kap (g x))) hA 2
      rwa [sq_abs] at hpow
    have hmollnn : (0:ℝ) ≤ mollifierCutoff m R x ^ 2 := sq_nonneg _
    have hprod : kappaProfile kap (g x) ^ 2 * mollifierCutoff m R x ^ 2
        ≤ (|g x| + 1 / 2) ^ 2 * mollifierCutoff m R x ^ 2 :=
      mul_le_mul_of_nonneg_right hsq hmollnn
    have habs0 : |(kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2|
        = (kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    rw [Real.norm_eq_abs, habs0]
    calc (kappaProfile kap (g x) * mollifierCutoff m R x) ^ 2
        = kappaProfile kap (g x) ^ 2 * mollifierCutoff m R x ^ 2 := by ring
      _ ≤ (|g x| + 1 / 2) ^ 2 * mollifierCutoff m R x ^ 2 := hprod
  · filter_upwards with x
    have hPhi := tendsto_katoSmooth (id : ℝ → ℝ) (g x)
    have hPhi' : Tendsto (fun kap : ℝ => kappaProfile kap (g x))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (max (g x) 0)) := by
      simpa [kappaProfile] using hPhi
    have hconst : Tendsto (fun _ : ℝ => mollifierCutoff m R x)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (mollifierCutoff m R x)) := tendsto_const_nhds
    have hmul : Tendsto (fun kap : ℝ => kappaProfile kap (g x) * mollifierCutoff m R x)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (max (g x) 0 * mollifierCutoff m R x)) :=
      hPhi'.mul hconst
    exact hmul.pow 2

/-- **The `kap ↓ 0` identification, at the excess `g = mollifySlice - barrier`.** Instantiates
`tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_zero` at
`g x := mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ)`, continuous by
`contDiff_mollifySlice`/`contDiff_barrier`, and rewrites the limit using
`comparisonPosPart m ε M σ K τ₀ q (x, τ) = max (g x) 0`, which holds **by definition** of
`comparisonPosPart` — not an approximation. -/
theorem tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonPosPart
    {m : ℕ} {ε M σ K τ₀ τ Minf R : ℝ} (hε : 0 < ε) (hR : 0 < R) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) :
    Tendsto (fun kap : ℝ => ∫ x, (kappaProfile kap
        (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ)) * mollifierCutoff m R x) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, (comparisonPosPart m ε M σ K τ₀ q (x, τ) * mollifierCutoff m R x) ^ 2)) := by
  have hg : Continuous
      (fun x : Vec m => mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ)) := by
    have h1 : Continuous fun x : Vec m => mollifySlice m ε q (x, τ) :=
      (contDiff_mollifySlice hε τ q Minf hmeas hbdd).continuous
    have h2 : Continuous fun x : Vec m => barrier m M σ K τ₀ (x, τ) :=
      (contDiff_barrier M σ K τ₀).continuous.comp (continuous_id.prodMk continuous_const)
    exact h1.sub h2
  have hmain := tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_zero
    (g := fun x : Vec m => mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ)) hg hR
  have heq : (fun x : Vec m => (max (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ)) 0
      * mollifierCutoff m R x) ^ 2)
      = fun x : Vec m => (comparisonPosPart m ε M σ K τ₀ q (x, τ) * mollifierCutoff m R x) ^ 2 := by
    funext x
    rfl
  rwa [heq] at hmain

/-- **The `kap ↓ 0` limit of the truncated Kato energy is `comparisonEnergy`**, the form matching
the hypothesis `hineq` of `comparisonEnergy_le_exp_mul_integral_sq`. The proof composes
`tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonPosPart` with
`integral_sq_mul_mollifierCutoff_eq_comparisonEnergy`, which is exact once `R ≥ Minf / σ`. -/
theorem tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonEnergy
    {m : ℕ} {ε M σ K τ₀ τ Minf R : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hτ : τ₀ ≤ τ) (hR : 0 < R) (hRM : Minf / σ ≤ R) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) :
    Tendsto (fun kap : ℝ => ∫ x, (kappaProfile kap
        (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ)) * mollifierCutoff m R x) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (comparisonEnergy m ε M σ K τ₀ q τ)) := by
  have hmain := tendsto_integral_sq_kappaProfile_mul_mollifierCutoff_nhds_comparisonPosPart
    (M := M) (σ := σ) (K := K) (τ₀ := τ₀) hε hR hmeas hbdd
  have heq := integral_sq_mul_mollifierCutoff_eq_comparisonEnergy hε hσ hK hM hτ hR hRM hmeas hbdd
  rwa [heq] at hmain

end CIV
