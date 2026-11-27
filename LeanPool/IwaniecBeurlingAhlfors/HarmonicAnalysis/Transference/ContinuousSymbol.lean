/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Basic
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.TrigPoly
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Cube
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Density
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Duality
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Norming
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Poisson
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Transference.RiemannSum

/-!
# Transference from the torus to the plane for symbols continuous off the origin

`HarmonicAnalysis.multiplierNorm_le_liminf_torusMultiplierNorm` is Proposition 5.7.4 of
Hytönen–van Neerven–Veraar–Weis (HNVW) for `ℝ² ≅ ℂ` and scalar symbols: if `m` is continuous at
every `ξ ≠ 0`, then for `1 < p < ∞` and every sequence `R_j → ∞` (in HNVW, `ε_j = 1 / R_j ↓ 0`),
`‖T_m‖_{L^p (ℝ²)} ≤ liminf_j ‖T_{(m (n / R_j))_n}‖_{L^p_0 (𝕋²)}`.

The other direction, from the line to the circle and for vector-valued functions, is Proposition
5.7.1, in `HarmonicAnalysis.VectorValued.Transference`.

If the `liminf` is finite, `m` is bounded
(`HarmonicAnalysis.exists_norm_le_of_liminf_torusMultiplierNorm_ne_top`), and `T_m` extends to a
bounded operator on `L^p (ℝ²)` (`HarmonicAnalysis.existsUnique_extension_of_multiplierNorm_ne_top`):
`m` is a Fourier multiplier on `L^p (ℝ²)`.

## Proof

That of HNVW, pp. 461–462.

1. Test functions: Schwartz functions `f`, `g` with Fourier transforms in `C_c^∞ (ℂ ∖ {0})`
   (`HarmonicAnalysis.HasCompactFourierSupportOffZero`).
2. Pairing: `∫ T_m f · g = ∫ m 𝓕 f 𝓕⁻¹ g`.
3. The integrand is continuous with compact support, so the integral is the limit of its lattice
   Riemann sums `Σ_n R⁻² (m 𝓕 f 𝓕⁻¹ g) (n / R)` (`HarmonicAnalysis.tendsto_riemannSum_real`; the
   Riemann integrability HNVW refers to is there dominated convergence for step functions).
4. Orthogonality on `𝕋²` (`HarmonicAnalysis.integral_torusMultiplier_mul_trigPoly`): the Riemann
   sum is `R²` times the pairing of `T_{m (· / R)} P` and `Q`, where `P = Σ_n R⁻² 𝓕 f (n / R) e_n`
   and `Q = Σ_n R⁻² 𝓕 g (n / R) e_n` are trigonometric polynomials, and `P` has mean zero because
   `𝓕 f (0) = 0`.
5. Hölder's inequality on `𝕋²` and the definition of the multiplier norm bound it by
   `‖T_{m (· / R)}‖ · R^{2/p} ‖P‖_p · R^{2/q} ‖Q‖_q`, `q = p / (p − 1)`.
6. Lemma 5.7.5, for `f` and `p` and for `g` and `q`
   (`HarmonicAnalysis.tendsto_eLpNorm_tsum_fourier_mul_mFourier`): `R^{2/p} ‖P‖_p → ‖f‖_p` and
   `R^{2/q} ‖Q‖_q → ‖g‖_q`. Hence `|∫ T_m f · g| ≤ liminf ‖T_{m (· / R)}‖ ‖f‖_p ‖g‖_q`.
7. Density (Proposition 2.4.23 (ii),
   `HarmonicAnalysis.exists_tendsto_hasCompactFourierSupportOffZero`) extends this to all Schwartz
   functions `f` and `g`, and duality (`HarmonicAnalysis.eLpNorm_le_of_forall_schwartz`) concludes.
   HNVW leaves this step to the reader. As in its §5.3 (p. 401), the density of the `f` is used in
   `L^p` and for `𝓕 f_j → 𝓕 f` in `L^1`, so that `T_m f_j → T_m f`; the limit is taken here in the
   pairing, before duality, and there in `L^p`, after it.

## Corrections to the source

* The statement of Proposition 5.7.4 is printed without its first hypotheses (`X`, `Y` Banach
  spaces, `1 < p < ∞`), says "multiplier for `L^p (ℝ^d; X)`" for "from `L^p (ℝ^d; X)` to
  `L^p (ℝ^d; Y)`", and has a superfluous `ℒ (` in its display.
* It does not say that `m` is bounded, which the definition of `T_m` (HNVW, Definition 5.3.1) asks
  for. Where the `liminf` is finite, this follows from the values `|m (n / R)|`, `n ≠ 0`, at most
  the torus norms (`HarmonicAnalysis.enorm_le_torusMultiplierNorm`), and from the density of the
  lattices `R⁻¹ ℤ²` as `R → ∞`.
* The factors `ε^{d/p}` and `ε^{d/p'}` of the last display are interchanged (compare Lemma 5.7.5;
  their product is the same), and `X*` there should be `Y*`.
* HNVW quotes the density of the `g` in `L^{p'}` only. That alone does not norm `T_m f`, which is
  not yet known to be in `L^p`: the constant function `1`, for instance, pairs to `𝓕 g (0) = 0` with
  each of these `g`. Here Proposition 2.4.23 is used as stated, with `𝓕 g_j → 𝓕 g` in `L^1` as well;
  it carries the bound to every Schwartz function `g`, and these norm the `L^p` norm of every
  continuous function.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*, Ergebnisse
  der Mathematik 63, Springer, 2016: Proposition 5.7.4, Lemma 5.7.5 (pp. 460–462), Definition 5.3.1
  and §5.3.a (pp. 400–401), Proposition 2.4.23 (p. 118).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace HarmonicAnalysis

open UnitAddTorus

/-- A symbol `m` that is continuous off `0` is Borel measurable. -/
theorem measurable_of_continuousAt_ne_zero {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ) :
    Measurable m := by
  classical
  have h := ContinuousOn.measurable_piecewise (s := {0}) (continuousOn_singleton m 0)
    (fun ξ hξ => (hmc ξ hξ).continuousWithinAt) (measurableSet_singleton 0)
  rwa [Set.piecewise_same] at h

/-! ### The pairing -/

/-- The pairing (step 2): `∫ T_m f · g = ∫ m 𝓕 f 𝓕⁻¹ g` for Schwartz functions `f` and `g`, when
`m 𝓕 f` is integrable. -/
private theorem integral_fourierMultiplier_mul {m : ℂ → ℂ} {f : 𝓢(ℂ, ℂ)}
    (hmf : Integrable fun ξ => m ξ * 𝓕 (f : ℂ → ℂ) ξ) (g : 𝓢(ℂ, ℂ)) :
    ∫ x, fourierMultiplier m f x * g x =
      ∫ ξ, m ξ * 𝓕 (f : ℂ → ℂ) ξ * 𝓕⁻ (g : ℂ → ℂ) ξ :=
  integral_fourierInv_mul hmf g.integrable

/-! ### The trigonometric polynomials `Σ_n R⁻² 𝓕 f (n / R) e_n` -/

/-- If `𝓕 f` is compactly supported, its samples on `R⁻¹ ℤ²` are finitely supported. -/
private theorem exists_finsupp_samples {f : 𝓢(ℂ, ℂ)} (hf : HasCompactSupport (𝓕 (f : ℂ → ℂ)))
    {R : ℝ} (hR : 0 < R) : ∃ c : (Fin 2 → ℤ) →₀ ℂ,
      ∀ n, c n = ((R : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint n / R) := by
  obtain ⟨ρ, hρ⟩ := hf.isCompact.isBounded.subset_closedBall 0
  have hfin : (Function.support fun n : Fin 2 → ℤ =>
      ((R : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint n / R)).Finite := by
    refine ((isCompact_closedBall (0 : Fin 2 → ℤ) (ρ * R)).finite_of_discrete).subset fun n hn => ?_
    have h1 : latticePoint n / R ∈ tsupport (𝓕 (f : ℂ → ℂ)) :=
      subset_tsupport _ (right_ne_zero_of_mul hn)
    have h2 := mem_closedBall_zero_iff.1 (hρ h1)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_le_iff₀ hR] at h2
    exact mem_closedBall_zero_iff.2 ((norm_le_norm_latticePoint n).trans h2)
  exact ⟨Finsupp.ofSupportFinite _ hfin, fun n => rfl⟩

/-- A trigonometric polynomial as the series of its coefficients. -/
private theorem trigPoly_eq_tsum {c : (Fin 2 → ℤ) →₀ ℂ} {a : (Fin 2 → ℤ) → ℂ}
    (hc : ∀ n, c n = a n) : trigPoly c = fun x => ∑' n, a n * mFourier n x := by
  funext x
  rw [trigPoly, Finsupp.sum, tsum_eq_sum (s := c.support)]
  · exact Finset.sum_congr rfl fun n _ => by rw [hc]
  · intro n hn
    rw [← hc, Finsupp.notMem_support_iff.1 hn, zero_mul]

/-- The Riemann sum on the torus (steps 4 and 5): for `f` and `g` with Fourier transforms compactly
supported in `ℂ ∖ {0}` and `R > 0`, with the trigonometric polynomials `P = Σ_n R⁻² 𝓕 f (n / R) e_n`
and `Q = Σ_n R⁻² 𝓕 g (n / R) e_n`, the first of mean `R⁻² 𝓕 f (0) = 0`,
`|Σ_n R⁻² (m 𝓕 f 𝓕⁻¹ g) (n / R)| = R² |∫_{𝕋²} T_{m (· / R)} P · Q|`, by orthogonality, which is at
most `‖T_{m (· / R)}‖ · R^{2/p} ‖P‖_p · R^{2/q} ‖Q‖_q`, by Hölder's inequality. -/
private theorem enorm_riemannSum_le {f g : 𝓢(ℂ, ℂ)} (hf : HasCompactFourierSupportOffZero f)
    (hg : HasCompactFourierSupportOffZero g) (m : ℂ → ℂ) {p : ℝ} (hp : 1 < p) {R : ℝ} (hR : 0 < R) :
    ‖∑' n : Fin 2 → ℤ, ((R : ℂ) ^ 2)⁻¹ * (m (latticePoint n / R) *
        𝓕 (f : ℂ → ℂ) (latticePoint n / R) * 𝓕⁻ (g : ℂ → ℂ) (latticePoint n / R))‖ₑ ≤
      torusMultiplierNorm (fun n => m (latticePoint n / R)) p *
        ((ENNReal.ofReal (R ^ (2 / p)) * eLpNorm (fun x => ∑' n : Fin 2 → ℤ, ((R : ℂ) ^ 2)⁻¹ *
          𝓕 (f : ℂ → ℂ) (latticePoint n / R) * mFourier n x) (ENNReal.ofReal p) volume) *
        (ENNReal.ofReal (R ^ (2 / (p / (p - 1)))) * eLpNorm (fun x => ∑' n : Fin 2 → ℤ,
          ((R : ℂ) ^ 2)⁻¹ * 𝓕 (g : ℂ → ℂ) (latticePoint n / R) * mFourier n x)
          (ENNReal.ofReal (p / (p - 1))) volume)) := by
  have hp0 : 0 < p := by linarith
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) :=
    hpq.ennrealOfReal
  set q := p / (p - 1)
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  obtain ⟨c, hc⟩ := exists_finsupp_samples hf.1 hR
  obtain ⟨d, hd⟩ := exists_finsupp_samples hg.1 hR
  set μ : (Fin 2 → ℤ) → ℂ := fun n => m (latticePoint n / R)
  -- The mean vanishes.
  have hc0 : c 0 = 0 := by
    rw [hc, latticePoint_zero, zero_div, image_eq_zero_of_notMem_tsupport hf.2, mul_zero]
  -- The Riemann sum is a pairing on the torus, by orthogonality.
  have hpair : ∑' n : Fin 2 → ℤ, ((R : ℂ) ^ 2)⁻¹ * (m (latticePoint n / R) *
      𝓕 (f : ℂ → ℂ) (latticePoint n / R) * 𝓕⁻ (g : ℂ → ℂ) (latticePoint n / R)) =
      (R : ℂ) ^ 2 * ∫ x, torusMultiplier μ c x * trigPoly d x := by
    rw [integral_torusMultiplier_mul_trigPoly, Finsupp.sum, Finset.mul_sum,
      tsum_eq_sum (s := c.support)]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [hc, hd, latticePoint_neg, neg_div, ← Real.fourierInv_eq_fourier_neg]
      simp only [μ]
      field_simp
    · intro n hn
      have h := hc n
      rw [Finsupp.notMem_support_iff.1 hn] at h
      rcases mul_eq_zero.1 h.symm with h' | h'
      · exact absurd h' (inv_ne_zero (pow_ne_zero 2 hRc))
      · rw [h', mul_zero, zero_mul, mul_zero]
  have hRpow : ENNReal.ofReal (R ^ (2 / p)) * ENNReal.ofReal (R ^ (2 / q)) = ‖(R : ℂ) ^ 2‖ₑ := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hR, ← ofReal_norm, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hR.le, div_eq_mul_inv, div_eq_mul_inv, ← mul_add,
      hpq.inv_add_inv_eq_one, mul_one, Real.rpow_ofNat]
  rw [hpair, eNorm_mul, ← hRpow, ← trigPoly_eq_tsum hc, ← trigPoly_eq_tsum hd]
  calc ENNReal.ofReal (R ^ (2 / p)) * ENNReal.ofReal (R ^ (2 / q)) *
        ‖∫ x, torusMultiplier μ c x * trigPoly d x‖ₑ
      ≤ ENNReal.ofReal (R ^ (2 / p)) * ENNReal.ofReal (R ^ (2 / q)) *
          (torusMultiplierNorm μ p * eLpNorm (trigPoly c) (ENNReal.ofReal p) volume *
            eLpNorm (trigPoly d) (ENNReal.ofReal q) volume) := by
        gcongr
        refine (enorm_integral_mul_le (continuous_torusMultiplier μ c).aestronglyMeasurable
          (continuous_trigPoly d).aestronglyMeasurable (ENNReal.ofReal p)
          (ENNReal.ofReal q)).trans ?_
        gcongr
        exact eLpNorm_torusMultiplier_le μ hp0 c hc0
    _ = _ := by ring

/-! ### The bound for Fourier transforms supported off `0` -/

/-- A continuous function `ψ` with `0 ∉ supp ψ` absorbs the discontinuity of `m` at `0`: `m ψ` is
continuous. -/
private theorem continuous_mul_of_notMem_tsupport {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    {ψ : ℂ → ℂ} (hψ : Continuous ψ) (h0 : 0 ∉ tsupport ψ) : Continuous fun ξ => m ξ * ψ ξ := by
  rw [continuous_iff_continuousAt]
  intro ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [notMem_tsupport_iff_eventuallyEq] at h0
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [h0] with ξ hξ
    simp [hξ]
  · exact (hmc ξ hξ).mul hψ.continuousAt

/-- Steps 2 to 6: `|∫ T_m f · g| ≤ liminf_j ‖T_{m (· / R_j)}‖ ‖f‖_p ‖g‖_q` for `f` and `g` with
Fourier transforms compactly supported in `ℂ ∖ {0}`. -/
private theorem enorm_integral_fourierMultiplier_mul_le {m : ℂ → ℂ}
    (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ) {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) {p : ℝ}
    (hp : 1 < p) {f g : 𝓢(ℂ, ℂ)} (hf : HasCompactFourierSupportOffZero f)
    (hg : HasCompactFourierSupportOffZero g)
    (hM : liminf (fun j => torusMultiplierNorm (fun n => m (latticePoint n / R j)) p) atTop ≠ ⊤) :
    ‖∫ x, fourierMultiplier m f x * g x‖ₑ ≤
      liminf (fun j => torusMultiplierNorm (fun n => m (latticePoint n / R j)) p) atTop *
        (eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume *
          eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal (p / (p - 1))) volume) := by
  -- `m 𝓕 f` is continuous with compact support.
  have hmfc : Continuous fun ξ => m ξ * 𝓕 (f : ℂ → ℂ) ξ :=
    continuous_mul_of_notMem_tsupport hmc (𝓕 f).continuous hf.2
  have hmfs : HasCompactSupport fun ξ => m ξ * 𝓕 (f : ℂ → ℂ) ξ := hf.1.mul_left (f := m)
  rw [integral_fourierMultiplier_mul (hmfc.integrable_of_hasCompactSupport hmfs) g]
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  set q := p / (p - 1)
  set φ : ℂ → ℂ := fun ξ => m ξ * 𝓕 (f : ℂ → ℂ) ξ * 𝓕⁻ (g : ℂ → ℂ) ξ
  -- The integrand is continuous with compact support, hence `O ((1 + |ξ|)^{−3})`.
  have hgc : Continuous (𝓕⁻ (g : ℂ → ℂ)) := by
    rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ g).continuous
  have hφc : Continuous φ := hmfc.mul hgc
  have hφs : HasCompactSupport φ := hmfs.mul_right
  obtain ⟨C, hC⟩ := (hφs.mul_left
    (f := fun ξ => ((1 + ‖ξ‖ : ℝ) : ℂ) ^ 3)).exists_bound_of_continuous (by fun_prop)
  have hφb : ∀ ξ, ‖φ ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-3 : ℝ) := fun ξ => by
    have h := hC ξ
    rw [Pi.mul_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      at h
    rw [Real.rpow_neg (by positivity), Real.rpow_ofNat, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity), mul_comm]
    exact h
  -- The Riemann sums, and Lemma 5.7.5 for `f` and for `g`.
  have hsum := ((tendsto_riemannSum_real (fun ξ _ => hφc.continuousAt) hφb).comp hR).eNorm
  have hNf := (tendsto_eLpNorm_tsum_fourier_mul_mFourier f hp.le).comp hR
  have hNg := (tendsto_eLpNorm_tsum_fourier_mul_mFourier g hpq.symm.lt.le).comp hR
  have hft := (f.memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top.ne
  have hgt := (g.memLp (ENNReal.ofReal q) volume).eLpNorm_lt_top.ne
  have hN := ENNReal.Tendsto.mul hNf (Or.inr hgt) hNg (Or.inr hft)
  have hab := ENNReal.mul_ne_top hft hgt
  set N : ℕ → ℝ≥0∞ := fun j => (ENNReal.ofReal (R j ^ (2 / p)) * eLpNorm (fun x =>
      ∑' n : Fin 2 → ℤ, ((R j : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint n / R j) * mFourier n x)
      (ENNReal.ofReal p) volume) *
    (ENNReal.ofReal (R j ^ (2 / q)) * eLpNorm (fun x => ∑' n : Fin 2 → ℤ, ((R j : ℂ) ^ 2)⁻¹ *
      𝓕 (g : ℂ → ℂ) (latticePoint n / R j) * mFourier n x) (ENNReal.ofReal q) volume)
  set T : ℕ → ℝ≥0∞ := fun j => torusMultiplierNorm (fun n => m (latticePoint n / R j)) p
  have hle : ∀ᶠ j in atTop, ‖∑' n : Fin 2 → ℤ, ((R j : ℂ) ^ 2)⁻¹ * φ (latticePoint n / R j)‖ₑ ≤
      (N * T) j := by
    filter_upwards [hR.eventually_gt_atTop 0] with j hj
    exact (enorm_riemannSum_le hf hg m hp hj).trans_eq (mul_comm _ _)
  have hNlim : limsup N atTop = _ := hN.limsup_eq
  calc ‖∫ ξ, φ ξ‖ₑ = liminf (fun j => ‖∑' n : Fin 2 → ℤ, ((R j : ℂ) ^ 2)⁻¹ *
        φ (latticePoint n / R j)‖ₑ) atTop := hsum.liminf_eq.symm
    _ ≤ liminf (N * T) atTop := liminf_le_liminf hle
    _ ≤ limsup N atTop * liminf T atTop :=
        ENNReal.liminf_mul_le (Or.inr hM) (Or.inl (hNlim ▸ hab))
    _ = _ := by rw [hNlim, mul_comm]

/-! ### Density -/

/-- The symbol is bounded off `0` by `liminf_j ‖T_{m (· / R_j)}‖`: its values are limits of values
at points of the lattices `R_j⁻¹ ℤ²`, off `0`. -/
theorem enorm_le_liminf_torusMultiplierNorm {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) {p : ℝ} (hp : 0 < p) {ξ : ℂ} (hξ : ξ ≠ 0) :
    ‖m ξ‖ₑ ≤ liminf (fun j => torusMultiplierNorm (fun n => m (latticePoint n / R j)) p) atTop := by
  obtain ⟨n, hn⟩ := exists_tendsto_latticePoint_div ξ
  have hv := hn.comp hR
  have hm := ((hmc ξ hξ).tendsto.comp hv).eNorm
  rw [← hm.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [hv.eventually_ne hξ] with j hj
  refine enorm_le_torusMultiplierNorm (fun k => m (latticePoint k / R j)) hp (n := n (R j)) ?_
  intro h0
  refine hj ?_
  simp [h0]

/-- A bound `|∫ h 𝓕 φ| ≤ A ‖φ‖_p`, with `h` bounded, passes to the limit when `φ_j → f` in `L^p`
and `𝓕 φ_j → 𝓕 f` in `L^1`. -/
private theorem enorm_integral_le_of_tendsto {h : ℂ → ℂ} (hh : Measurable h) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hhC : ∀ᵐ ξ, ‖h ξ‖ₑ ≤ C) {P : ℝ≥0∞} (hP : 1 ≤ P) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    {φ : ℕ → 𝓢(ℂ, ℂ)} {f : 𝓢(ℂ, ℂ)}
    (hφ : Tendsto (fun j => eLpNorm (fun x => φ j x - f x) P volume) atTop (𝓝 0))
    (hφ1 : Tendsto (fun j => eLpNorm (fun ξ => 𝓕 (φ j) ξ - 𝓕 f ξ) 1 volume) atTop (𝓝 0))
    (H : ∀ j, ‖∫ ξ, h ξ * 𝓕 (φ j) ξ‖ₑ ≤ A * eLpNorm (φ j) P volume) :
    ‖∫ ξ, h ξ * 𝓕 f ξ‖ₑ ≤ A * eLpNorm f P volume := by
  have hint : ∀ u : 𝓢(ℂ, ℂ), Integrable fun ξ => h ξ * u ξ := fun u => by
    refine u.integrable.bdd_mul (c := C.toReal) hh.aestronglyMeasurable ?_
    filter_upwards [hhC] with ξ hξ
    rwa [← toReal_eNorm, ENNReal.toReal_le_toReal eNorm_ne_top hC]
  have hlim : Tendsto (fun j => ∫ ξ, h ξ * 𝓕 (φ j) ξ) atTop (𝓝 (∫ ξ, h ξ * 𝓕 f ξ)) := by
    refine tendsto_integral_of_L1 _ (hint _).aestronglyMeasurable
      (Eventually.of_forall fun j => hint _) ?_
    have hle : ∀ j, ∫⁻ ξ, ‖h ξ * 𝓕 (φ j) ξ - h ξ * 𝓕 f ξ‖ₑ ≤
        C * eLpNorm (fun ξ => 𝓕 (φ j) ξ - 𝓕 f ξ) 1 volume := fun j => by
      rw [eLpNorm_one_eq_lintegral_eNorm (by fun_prop : Continuous fun ξ =>
        𝓕 (φ j) ξ - 𝓕 f ξ).aestronglyMeasurable, ← lintegral_const_mul' _ _ hC]
      refine lintegral_mono_ae ?_
      filter_upwards [hhC] with ξ hξ
      rw [← mul_sub, eNorm_mul]
      gcongr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
    simpa using ENNReal.Tendsto.const_mul hφ1 (a := C) (Or.inr hC)
  have hupp : Tendsto (fun j => A * (eLpNorm (fun x => φ j x - f x) P volume +
      eLpNorm f P volume)) atTop (𝓝 (A * eLpNorm f P volume)) := by
    simpa using ENNReal.Tendsto.const_mul (hφ.add_const (eLpNorm f P volume)) (a := A) (Or.inr hA)
  refine le_of_tendsto_of_tendsto' hlim.eNorm hupp fun j => (H j).trans ?_
  gcongr
  refine le_trans (le_of_eq ?_) (eLpNorm_add_le hP (f := fun x => φ j x - f x) (g := f))
  congr 1
  ext x
  simp

/-- Density (step 7), by HNVW, Proposition 2.4.23 (ii): if `m` is bounded off `0`, a bound
`|∫ T_m f · g| ≤ M ‖f‖_p ‖g‖_q` for the `f` and `g` with Fourier transforms compactly supported in
`ℂ ∖ {0}` holds for all Schwartz functions `f` and `g`. -/
private theorem enorm_integral_fourierMultiplier_mul_le_of_forall {m : ℂ → ℂ} (hm : Measurable m)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hmM : ∀ ξ ≠ 0, ‖m ξ‖ₑ ≤ M) {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (H : ∀ f g : 𝓢(ℂ, ℂ), HasCompactFourierSupportOffZero f → HasCompactFourierSupportOffZero g →
      ‖∫ x, fourierMultiplier m f x * g x‖ₑ ≤ M * (eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume *
        eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume)) (f g : 𝓢(ℂ, ℂ)) :
    ‖∫ x, fourierMultiplier m f x * g x‖ₑ ≤ M * (eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume *
      eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume) := by
  have hmf : ∀ f : 𝓢(ℂ, ℂ), Integrable fun ξ => m ξ * 𝓕 (f : ℂ → ℂ) ξ := fun f => by
    refine (𝓕 f).integrable.bdd_mul (c := M.toReal) hm.aestronglyMeasurable ?_
    filter_upwards [Measure.ae_ne volume 0] with ξ hξ
    rw [← toReal_eNorm, ENNReal.toReal_le_toReal eNorm_ne_top hM]
    exact hmM ξ hξ
  simp only [integral_fourierMultiplier_mul (hmf _)] at H ⊢
  have hbdd : ∀ u : 𝓢(ℂ, ℂ), ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ ξ, ‖u ξ‖ₑ ≤ K := fun u =>
    ⟨ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 u), ENNReal.ofReal_ne_top, fun ξ => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (u.norm_le_seminorm ℝ ξ)⟩
  -- The density of the `f`, for `g` with Fourier transform compactly supported in `ℂ ∖ {0}`.
  have h1 : ∀ f g : 𝓢(ℂ, ℂ), HasCompactFourierSupportOffZero g →
      ‖∫ ξ, m ξ * 𝓕 (f : ℂ → ℂ) ξ * 𝓕⁻ (g : ℂ → ℂ) ξ‖ₑ ≤
        M * (eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume *
          eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume) := by
    intro f g hg
    obtain ⟨φ, hφ, hφp, hφ1⟩ := exists_tendsto_hasCompactFourierSupportOffZero f
    obtain ⟨K, hK, hgK⟩ := hbdd (𝓕⁻ g)
    have hcomm : ∀ u : 𝓢(ℂ, ℂ), ∫ ξ, m ξ * 𝓕 (u : ℂ → ℂ) ξ * 𝓕⁻ (g : ℂ → ℂ) ξ =
        ∫ ξ, m ξ * 𝓕⁻ g ξ * 𝓕 u ξ := fun u => by
      rw [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe]
      congr 1
      ext ξ
      ring
    rw [hcomm, mul_comm (eLpNorm _ _ _), ← mul_assoc]
    refine enorm_integral_le_of_tendsto (h := fun ξ => m ξ * 𝓕⁻ g ξ) (C := M * K)
      (hm.mul (𝓕⁻ g).continuous.measurable) (ENNReal.mul_ne_top hM hK) ?_ (by simpa using hp.le)
      (ENNReal.mul_ne_top hM (g.memLp (ENNReal.ofReal q) volume).eLpNorm_lt_top.ne) (hφp p hp) hφ1
      fun j => ?_
    · filter_upwards [Measure.ae_ne volume 0] with ξ hξ
      rw [eNorm_mul]
      exact mul_le_mul' (hmM ξ hξ) (hgK ξ)
    · rw [← hcomm, mul_assoc, mul_comm (eLpNorm _ _ _)]
      exact H _ g (hφ j) hg
  -- The density of the `g`.
  obtain ⟨φ, hφ, hφp, hφ1⟩ := exists_tendsto_hasCompactFourierSupportOffZero g
  obtain ⟨K, hK, hfK⟩ := hbdd (𝓕 f)
  have hcomm : ∀ u : 𝓢(ℂ, ℂ), ∫ ξ, m ξ * 𝓕 (f : ℂ → ℂ) ξ * 𝓕⁻ (u : ℂ → ℂ) ξ =
      ∫ ξ, m (-ξ) * 𝓕 f (-ξ) * 𝓕 u ξ := fun u => by
    rw [← integral_neg_eq_self]
    simp_rw [Real.fourierInv_eq_fourier_neg, neg_neg, SchwartzMap.fourier_coe]
  rw [hcomm, ← mul_assoc]
  refine enorm_integral_le_of_tendsto (h := fun ξ => m (-ξ) * 𝓕 f (-ξ)) (C := M * K)
    ((hm.comp measurable_neg).mul ((𝓕 f).continuous.comp continuous_neg).measurable)
    (ENNReal.mul_ne_top hM hK) ?_ (by simpa using hq.le)
    (ENNReal.mul_ne_top hM (f.memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top.ne)
    (hφp q hq) hφ1 fun j => ?_
  · filter_upwards [Measure.ae_ne volume 0] with ξ hξ
    rw [eNorm_mul]
    exact mul_le_mul' (hmM _ (neg_ne_zero.2 hξ)) (hfK _)
  · rw [← hcomm, mul_assoc]
    exact h1 f (φ j) (hφ j)

/-! ### Proposition 5.7.4 -/

/-- **HNVW, Proposition 5.7.4** (transference from `𝕋²` to `ℝ²`, for scalar symbols): let `m` be
continuous at every `ξ ≠ 0`, `1 < p < ∞` and `R_j → ∞` (in HNVW, `ε_j = 1 / R_j ↓ 0`). Then
`‖T_m‖_{L^p (ℝ²)} ≤ liminf_j ‖T_{(m (n / R_j))_{n ≠ 0}}‖_{L^p_0 (𝕋²)}`.

The proof is HNVW's; the module docstring gives its steps and the corrections to the printed
text. -/
theorem multiplierNorm_le_liminf_torusMultiplierNorm {m : ℂ → ℂ}
    (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ) {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) {p : ℝ}
    (hp : 1 < p) :
    multiplierNorm m p ≤
      liminf (fun j => torusMultiplierNorm (fun n => m (latticePoint n / R j)) p) atTop := by
  set M := liminf (fun j => torusMultiplierNorm (fun n => m (latticePoint n / R j)) p) atTop
  rcases eq_or_ne M ⊤ with hM | hM
  · rw [hM]
    exact le_top
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hm : Measurable m := measurable_of_continuousAt_ne_zero hmc
  have hmM : ∀ ξ ≠ 0, ‖m ξ‖ₑ ≤ M := fun ξ hξ =>
    enorm_le_liminf_torusMultiplierNorm hmc hR (by linarith) hξ
  -- The bound for the pairing of Schwartz functions.
  have hpair := enorm_integral_fourierMultiplier_mul_le_of_forall hm hM hmM hp hpq.symm.lt
    fun f g hf hg => enorm_integral_fourierMultiplier_mul_le hmc hR hp hf hg hM
  -- Duality.
  refine iSup_le fun f => ENNReal.div_le_of_le_mul ?_
  refine eLpNorm_le_of_forall_schwartz (continuous_fourierMultiplier m f) hp fun g => ?_
  have hg : (conjSchwartz g : ℂ → ℂ) = fun x => conj (g x) := funext fun x => conjSchwartz_apply g x
  have h := hpair f (conjSchwartz g)
  rw [hg, show eLpNorm (fun x => conj (g x)) _ volume = _ from eLpNorm_conj _ _ _,
    ← mul_assoc] at h
  exact h

/-- If the `liminf` is finite, the symbol is bounded, and so the symbol of a Fourier multiplier in
the sense of HNVW, Definition 5.3.1. -/
theorem exists_norm_le_of_liminf_torusMultiplierNorm_ne_top {m : ℂ → ℂ}
    (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ) {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) {p : ℝ}
    (hp : 0 < p) (hM : liminf (fun j => torusMultiplierNorm (fun n => m (latticePoint n / R j)) p)
      atTop ≠ ⊤) : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C := by
  set M := liminf (fun j => torusMultiplierNorm (fun n => m (latticePoint n / R j)) p) atTop
  refine ⟨max ‖m 0‖ M.toReal, fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact le_max_left _ _
  refine le_max_of_le_right ?_
  rw [← toReal_eNorm]
  exact ENNReal.toReal_mono hM (enorm_le_liminf_torusMultiplierNorm hmc hR hp hξ)

/-- The dilated symbols in the notation of HNVW, `m (ε k)` with `ε = 1 / R ↓ 0`. -/
theorem torusMultiplierNorm_div_inv (m : ℂ → ℂ) (ε p : ℝ) :
    torusMultiplierNorm (fun n => m (latticePoint n / (ε⁻¹ : ℝ))) p =
      torusMultiplierNorm (fun n => m (ε * latticePoint n)) p := by
  congr 1
  funext n
  rw [Complex.ofReal_inv, div_inv_eq_mul, mul_comm]

end HarmonicAnalysis
