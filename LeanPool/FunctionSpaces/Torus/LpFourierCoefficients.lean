/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.LittlewoodPaley
public import LeanPool.FunctionSpaces.Analysis.Lp.Inclusion

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Fourier coefficients in `L_p(𝕋^d)`

For `1 ≤ p ≤ ∞` and `m ∈ ℤ^d`, the Fourier coefficient `f ↦ f̂(m) = ∫ e_{-m} f` is a bounded
linear functional on `L_p(𝕋^d)` of norm at most `1`, since `|f̂(m)| ≤ ‖f‖_1 ≤ ‖f‖_p` on the
probability space `𝕋^d` (`Torus.coeffCLM`, `Torus.norm_coeffCLM_le`). The characters have the
coefficients `ê_k(m) = 1` for `k = m` and `0` otherwise (`Torus.mFourierCoeff_mFourierLp`).

* **Coefficients of convolutions**: for an integrable kernel `Φ` on `ℝ^d`,
  `(Φ ⋆ f)^(m) = 𝓕Φ(m) f̂(m)` (`Torus.mFourierCoeff_econvLp`, `Torus.mFourierCoeff_econv`). Both
  sides are bounded functionals of `f` that agree on the characters, whose span is dense
  (`Torus.ext_mFourierLp`).
* The inclusion `L_r ⊆ L_p`, `p ≤ r`, keeps the coefficients
  (`Torus.mFourierCoeff_inclusionOfExponentLe`).
* **Uniqueness**: for `1 ≤ p ≤ ∞`, an element of `L_p(𝕋^d)` is determined by its Fourier
  coefficients (`Torus.eq_of_mFourierCoeff_eq`). A trigonometric polynomial is the sum of its
  coefficients times the characters (`Torus.eq_sum_mFourierCoeff_of_mem_trigPolyLp`). In `L_1`,
  the Littlewood–Paley blocks of `f` are trigonometric polynomials with the coefficients
  `𝓕ψ_j(m) f̂(m)`, and their partial sums converge to `f`; the inclusion `L_p ⊆ L_1` gives every
  `p`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus Filter Topology
open scoped ENNReal FourierTransform TorusHaar

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### Coefficients of functions -/

/-- The Fourier coefficients see only classes: `f = g` almost everywhere gives `f̂ = ĝ`. -/
theorem mFourierCoeff_congr_ae {f g : UnitAddTorus d → ℂ} (h : f =ᵐ[volume] g) (m : d → ℤ) :
    mFourierCoeff f m = mFourierCoeff g m :=
  integral_congr_ae (h.mono fun t ht => by simp only [ht])

/-- `|e_m(t)| ≤ 1` for every character and every point of the torus. -/
theorem norm_mFourier_apply_le (m : d → ℤ) (t : UnitAddTorus d) : ‖mFourier m t‖ ≤ 1 :=
  (norm_trigMonomial_apply m t).le

/-- **The coefficient is bounded by the `L_1` norm**: `|f̂(m)| ≤ ∫ |f| = ‖f‖_1`. -/
theorem enorm_mFourierCoeff_le_eLpNorm_one (f : UnitAddTorus d → ℂ) (m : d → ℤ) :
    ‖mFourierCoeff f m‖ₑ ≤ eLpNorm f 1 volume := by
  by_cases hf : AEStronglyMeasurable f volume
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top
  rw [eLpNorm_one_eq_lintegral_eNorm hf]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun t => ?_)
  rw [eNorm_smul]
  calc ‖mFourier (-m) t‖ₑ * ‖f t‖ₑ ≤ 1 * ‖f t‖ₑ := by
        gcongr
        rw [← ofReal_norm, ENNReal.ofReal_le_one]
        exact norm_mFourier_apply_le _ t
    _ = ‖f t‖ₑ := one_mul _

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integrand `e_m f` of a coefficient of `f ∈ L_p(𝕋^d)` is integrable, `1 ≤ p`. -/
theorem integrable_mFourier_smul (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    Integrable (fun t => mFourier m t • f t) volume :=
  ((Lp.memLp f).integrable Fact.out).bdd_smul 1 (mFourier m).continuous.aestronglyMeasurable
    (Eventually.of_forall fun t => norm_mFourier_apply_le m t)

/-- **The coefficients are additive**: `(f + g)^(m) = f̂(m) + ĝ(m)` in `L_p(𝕋^d)`. -/
theorem mFourierCoeff_add (f g : Lp ℂ p (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    mFourierCoeff ⇑(f + g) m = mFourierCoeff f m + mFourierCoeff g m := by
  rw [mFourierCoeff_congr_ae (Lp.coeFn_add f g)]
  simp only [mFourierCoeff, Pi.add_apply, smul_add]
  exact integral_add (integrable_mFourier_smul f (-m)) (integrable_mFourier_smul g (-m))

omit [Fact (1 ≤ p)] in
/-- **The coefficients are homogeneous**: `(c f)^(m) = c f̂(m)` in `L_p(𝕋^d)`. -/
theorem mFourierCoeff_smul (c : ℂ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d)))
    (m : d → ℤ) : mFourierCoeff ⇑(c • f) m = c * mFourierCoeff f m := by
  rw [mFourierCoeff_congr_ae (Lp.coeFn_smul c f)]
  simp only [mFourierCoeff, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun t => by ring)

/-- **The coefficient is bounded by the norm**: `|f̂(m)| ≤ ‖f‖_p` for `f ∈ L_p(𝕋^d)`, from
`|f̂(m)| ≤ ‖f‖_1` and `‖f‖_1 ≤ ‖f‖_p` on the probability space `𝕋^d`. -/
theorem enorm_mFourierCoeff_le (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    ‖mFourierCoeff f m‖ₑ ≤ ‖f‖ₑ := by
  rw [Lp.eNorm_def]
  exact (enorm_mFourierCoeff_le_eLpNorm_one f m).trans
    (eLpNorm_le_eLpNorm_of_exponent_le Fact.out)

/-- **The coefficient is bounded by the norm**, in real norms: `|f̂(m)| ≤ ‖f‖_p`. -/
theorem norm_mFourierCoeff_le (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    ‖mFourierCoeff f m‖ ≤ ‖f‖ :=
  eNorm_le_iff_norm_le.1 (enorm_mFourierCoeff_le f m)

/-! ### The coefficient functional -/

variable (p) in
/-- The **coefficient functional** `f ↦ f̂(m)` on `L_p(𝕋^d)`, `1 ≤ p`, a bounded linear map of
norm at most `1`. -/
noncomputable def coeffCLM (m : d → ℤ) : Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => mFourierCoeff f m
      map_add' := fun f g => mFourierCoeff_add f g m
      map_smul' := fun c f => mFourierCoeff_smul c f m }
    1 fun f => by
      rw [one_mul]
      exact norm_mFourierCoeff_le f m

/-- The coefficient functional is the Fourier coefficient. -/
@[simp]
theorem coeffCLM_apply (m : d → ℤ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    coeffCLM p m f = mFourierCoeff f m := rfl

/-- **The coefficient functional has norm at most `1`**. -/
theorem norm_coeffCLM_le (m : d → ℤ) : ‖coeffCLM (d := d) p m‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `(f - g)^(m) = f̂(m) - ĝ(m)` in `L_p(𝕋^d)`. -/
theorem mFourierCoeff_sub (f g : Lp ℂ p (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    mFourierCoeff ⇑(f - g) m = mFourierCoeff f m - mFourierCoeff g m :=
  map_sub (coeffCLM p m) f g

/-- `(-f)^(m) = -f̂(m)` in `L_p(𝕋^d)`. -/
theorem mFourierCoeff_neg (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    mFourierCoeff ⇑(-f) m = -mFourierCoeff f m :=
  map_neg (coeffCLM p m) f

/-- The coefficients of `0 ∈ L_p(𝕋^d)` vanish. -/
theorem mFourierCoeff_zero (m : d → ℤ) :
    mFourierCoeff ⇑(0 : Lp ℂ p (volume : Measure (UnitAddTorus d))) m = 0 :=
  map_zero (coeffCLM p m)

/-- The coefficients of a finite sum in `L_p(𝕋^d)` are the sums of the coefficients. -/
theorem mFourierCoeff_sum {ι : Type*} (s : Finset ι)
    (F : ι → Lp ℂ p (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    mFourierCoeff ⇑(∑ i ∈ s, F i) m = ∑ i ∈ s, mFourierCoeff (F i) m :=
  map_sum (coeffCLM p m) F s

omit [Fact (1 ≤ p)] in
/-- The coefficients of `e_k` as a continuous function: `ê_k(m) = 1` for `k = m`, `0`
otherwise, by the orthonormality of the characters (Mathlib's `mFourierBasis`). -/
theorem mFourierCoeff_mFourier (k m : d → ℤ) :
    mFourierCoeff (mFourier k) m = if k = m then 1 else 0 := by
  classical
  rw [← mFourierCoeff_toLp, ← mFourierBasis_repr]
  have h : (ContinuousMap.toLp (E := ℂ) 2 volume ℂ (mFourier k) :
      Lp ℂ 2 (volume : Measure (UnitAddTorus d))) = mFourierBasis k := by
    rw [coe_mFourierBasis]
  rw [h, HilbertBasis.repr_self, lp.single_apply, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

/-- **The coefficients of the characters**: `ê_k(m) = 1` for `k = m` and `0` otherwise, in
`L_p(𝕋^d)`. -/
theorem mFourierCoeff_mFourierLp (k m : d → ℤ) :
    mFourierCoeff (mFourierLp p k) m = if k = m then 1 else 0 := by
  rw [mFourierCoeff_congr_ae (coeFn_mFourierLp p k), mFourierCoeff_mFourier]

/-- **The inclusion `L_r ⊆ L_p` keeps the coefficients**: for `p ≤ r` and `f ∈ L_r(𝕋^d)`, the
class of `f` in `L_p` has the Fourier coefficients of `f`. -/
theorem mFourierCoeff_inclusionOfExponentLe {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 ℂ] {r : ℝ≥0∞} [Fact (1 ≤ r)] (hpr : p ≤ r)
    (f : Lp ℂ r (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    mFourierCoeff (Lp.inclusionOfExponentLe (𝕜 := 𝕜) volume hpr f) m = mFourierCoeff f m :=
  mFourierCoeff_congr_ae (Lp.coeFn_inclusionOfExponentLe hpr f) m

/-! ### Coefficients of convolutions -/

/-- **The coefficients of a convolution**: `(Φ ⋆ f)^(m) = 𝓕Φ(m) f̂(m)` for `f ∈ L_p(𝕋^d)`,
`1 ≤ p < ∞`, and an integrable kernel `Φ` on `ℝ^d`. Both sides are bounded functionals of `f`;
on `e_k` both are `𝓕Φ(m)` for `k = m` and `0` otherwise (`Torus.econvLp_mFourierLp`). -/
theorem mFourierCoeff_econvLp (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    mFourierCoeff (econvLp hp hΦ f) m = 𝓕 Φ (latticeVec m) * mFourierCoeff f m := by
  have h : (coeffCLM p m).comp (econvLp hp hΦ) = 𝓕 Φ (latticeVec m) • coeffCLM p m :=
    ext_mFourierLp hp fun k => by
      simp only [ContinuousLinearMap.comp_apply, econvLp_mFourierLp, map_smul, smul_apply,
        coeffCLM_apply, mFourierCoeff_mFourierLp, smul_eq_mul]
      by_cases hk : k = m
      · rw [hk]
      · simp only [hk, ↓reduceIte, mul_zero]
  have hf := DFunLike.congr_fun h f
  simpa only [ContinuousLinearMap.comp_apply, smul_apply, coeffCLM_apply, smul_eq_mul] using hf

/-- **The coefficients of a convolution of functions**: `(Φ ⋆ f)^(m) = 𝓕Φ(m) f̂(m)` for
measurable integrable `f` on `𝕋^d` and an integrable kernel `Φ` on `ℝ^d`, from the case `p = 1`. -/
theorem mFourierCoeff_econv {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {f : UnitAddTorus d → ℂ} (hf : Measurable f) (hfi : Integrable f volume) (m : d → ℤ) :
    mFourierCoeff (econv Φ f) m = 𝓕 Φ (latticeVec m) * mFourierCoeff f m := by
  have hF := (memLp_one_iff_integrable.2 hfi).coeFn_toLp
  have h := mFourierCoeff_econvLp ENNReal.one_ne_top hΦ
    ((memLp_one_iff_integrable.2 hfi).toLp f) m
  rwa [mFourierCoeff_congr_ae (econvLp_apply_ae ENNReal.one_ne_top hΦ _),
    mFourierCoeff_congr_ae (econv_congr_ae Φ (Lp.stronglyMeasurable _).measurable hf hF),
    mFourierCoeff_congr_ae hF] at h

/-! ### Uniqueness -/

/-- **Trigonometric polynomials are their Fourier series**: an element `a` of `L_p(𝕋^d)` of
degree `< n` is `∑_{deg m < n} â(m) e_m`. Both sides are linear in `a`, and they agree on the
characters that span the trigonometric polynomials. -/
theorem eq_sum_mFourierCoeff_of_mem_trigPolyLp {n : ℕ}
    {a : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p n) :
    a = ∑ m ∈ boxLt d n, mFourierCoeff a m • mFourierLp p m := by
  classical
  rw [trigPolyLp_eq_span] at ha
  refine (LinearMap.eqOn_span (f := LinearMap.id)
    (g := ∑ m ∈ boxLt d n, (coeffCLM p m).toLinearMap.smulRight (mFourierLp p m)) ?_ ha).trans
    (by simp)
  rintro _ ⟨k, hk, rfl⟩
  simp only [LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    ContinuousLinearMap.coe_coe, coeffCLM_apply, mFourierCoeff_mFourierLp, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_coe.1 hk, ↓reduceIte]

/-- A trigonometric polynomial with vanishing Fourier coefficients is `0`. -/
theorem eq_zero_of_mem_trigPolyLp {n : ℕ} {a : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (ha : a ∈ trigPolyLp p n) (h : ∀ m, mFourierCoeff a m = 0) : a = 0 := by
  rw [eq_sum_mFourierCoeff_of_mem_trigPolyLp ha]
  simp only [h, zero_smul, Finset.sum_const_zero]

omit [Fact (1 ≤ p)] in
/-- **An element of `L_1(𝕋^d)` with vanishing Fourier coefficients is `0`**. Every
Littlewood–Paley block `Δ_j f` is a trigonometric polynomial with the coefficients
`𝓕ψ_j(m) f̂(m) = 0`, hence `0`, and the partial sums of the blocks converge to `f`
(`Torus.tendsto_sum_lpBlock`). -/
theorem eq_zero_of_mFourierCoeff_eq_zero_one {f : Lp ℂ 1 (volume : Measure (UnitAddTorus d))}
    (h : ∀ m, mFourierCoeff f m = 0) : f = 0 := by
  have hblock : ∀ j, lpBlock ENNReal.one_ne_top j f = 0 := fun j =>
    eq_zero_of_mem_trigPolyLp (lpBlock_mem_trigPolyLp ENNReal.one_ne_top j f) fun m => by
      rw [lpBlock, mFourierCoeff_econvLp, h m, mul_zero]
  have hlim := tendsto_sum_lpBlock ENNReal.one_ne_top f
  simp only [hblock, Finset.sum_const_zero] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- **An element of `L_p(𝕋^d)` with vanishing Fourier coefficients is `0`**, `1 ≤ p ≤ ∞`. Its
class in `L_1` has the same coefficients (`Torus.mFourierCoeff_inclusionOfExponentLe`), so it is
`0` by the case `p = 1`, and the inclusion `L_p ⊆ L_1` is injective. -/
theorem eq_zero_of_mFourierCoeff_eq_zero {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h : ∀ m, mFourierCoeff f m = 0) : f = 0 := by
  refine Lp.inclusionOfExponentLe_injective (E := ℂ) (𝕜 := ℂ) (μ := volume)
    (Fact.out : (1 : ℝ≥0∞) ≤ p) ?_
  rw [map_zero]
  exact eq_zero_of_mFourierCoeff_eq_zero_one fun m => by
    rw [mFourierCoeff_inclusionOfExponentLe, h m]

/-- **Uniqueness of the Fourier coefficients**: two elements of `L_p(𝕋^d)`, `1 ≤ p ≤ ∞`, with the
same Fourier coefficients are equal. -/
theorem eq_of_mFourierCoeff_eq {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h : ∀ m, mFourierCoeff f m = mFourierCoeff g m) : f = g :=
  sub_eq_zero.1 (eq_zero_of_mFourierCoeff_eq_zero fun m => by
    rw [mFourierCoeff_sub, h m, sub_self])

end Torus
