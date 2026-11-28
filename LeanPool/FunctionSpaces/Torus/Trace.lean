/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.Embeddings
public import LeanPool.FunctionSpaces.ApproximationSpaces.Trace

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Traces on the torus

The trace of a function on `𝕋^(n+1)` is its restriction to the face `{x_0 = 0} ≅ 𝕋^n`,
`x' ↦ f(0, x')` (`Torus.face`, `Torus.restrictFace`).  It is defined on continuous functions,
not on `L_p`.  This file shows, for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `s > 0`
(`Torus.trace_besov`): the restriction extends from trigonometric polynomials to a map from
`B^{s+1/p}_{p,q}(𝕋^(n+1))` into `B^s_{p,q}(𝕋^n)`, and every element of `B^s_{p,q}(𝕋^n)` is a
trace.  Both directions are the abstract trace theorem (`ApproximationSpaces.Trace`) for two
inequalities on trigonometric polynomials.  The restrictions and extensions keep the degree,
since they send monomials to multiples of monomials (`Torus.restrictFace_mem_trigPoly`).

* **The trace inequality** (`Torus.eLpNorm_restrictFace_le`): for `a` of degree `< m`,
  `‖a(0, ·)‖_{L_p(𝕋^n)} ≤ (2⌈p/2⌉ m)^(1/p) ‖a‖_{L_p(𝕋^(n+1))}`.  On every line
  `t ↦ a(t, x')` the one-dimensional Nikolskii inequality bounds `|a(0, x')|^p` by
  `2⌈p/2⌉ m ∫ |a(t, x')|^p dt`; integration over `x'` (Fubini on `𝕋^(n+1) = 𝕋 × 𝕋^n`,
  `Torus.lintegral_eq_lintegral_cons`) gives the bound.  So the restriction is a trace bound
  of exponent `1/p` (`Torus.traceBound`).
* **The extension** (`Torus.extendFace`): `b` on `𝕋^n` of degree `< m` extends to
  `φ_m(x_0) b(x')`, of degree `< 3m`, with the normalised Fejér kernel
  `φ_m = m^(-2) |∑_{j<m} e^(2πijx_0)|²` (`Torus.fejerFace`).  Since `φ_m(0) = 1`,
  `0 ≤ φ_m ≤ 1` and, by Parseval, `∫ φ_m = 1/m`, the extension has norm
  `≤ m^(-1/p) ‖b‖_p` (`Torus.eLpNorm_extendFace_le`); no pointwise kernel estimate is needed.
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal BoundedContinuousFunction TorusHaar

namespace Torus

variable {n : ℕ}

/-- The face `{x_0 = 0}` of `𝕋^(n+1)`: `x' ↦ (0, x')`. -/
noncomputable def face (n : ℕ) : C(UnitAddTorus (Fin n), UnitAddTorus (Fin (n + 1))) :=
  ⟨fun x' => Fin.cons 0 x', continuous_const.finCons continuous_id⟩

@[simp]
theorem face_apply (x' : UnitAddTorus (Fin n)) : face n x' = Fin.cons 0 x' := rfl

/-- The line `t ↦ (t, x')` through `x'`, parametrised by `𝕋^1`. -/
noncomputable def lineThrough (x' : UnitAddTorus (Fin n)) :
    C(UnitAddTorus (Fin 1), UnitAddTorus (Fin (n + 1))) :=
  ⟨fun v => Fin.cons (v 0) x',
    Continuous.finCons (A := fun _ => UnitAddCircle) (continuous_apply 0) continuous_const⟩

@[simp]
theorem lineThrough_apply (x' : UnitAddTorus (Fin n)) (v : UnitAddTorus (Fin 1)) :
    lineThrough x' v = Fin.cons (v 0) x' := rfl

/-- Composition with a continuous map, as a linear map of bounded continuous functions
(Mathlib's `BoundedContinuousFunction.compContinuousCLM`). -/
noncomputable def compLinear {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(Y, Z)) : (Z →ᵇ ℂ) →ₗ[ℂ] (Y →ᵇ ℂ) :=
  (BoundedContinuousFunction.compContinuousCLM ℂ ℂ g).toLinearMap

@[simp]
theorem compLinear_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (g : C(Y, Z))
    (a : Z →ᵇ ℂ) (y : Y) : compLinear g a y = a (g y) := rfl

/-- The restriction to the face `{x_0 = 0}`. -/
noncomputable abbrev restrictFace (n : ℕ) :
    (UnitAddTorus (Fin (n + 1)) →ᵇ ℂ) →ₗ[ℂ] (UnitAddTorus (Fin n) →ᵇ ℂ) :=
  compLinear (face n)

/-- `deg (k_1, …, k_n) ≤ deg (k_0, …, k_n)`. -/
theorem deg_tail_le (k : Fin (n + 1) → ℤ) : deg (Fin.tail k) ≤ deg k :=
  deg_le_iff.2 fun i => natAbs_le_deg k i.succ

/-- `|k_0| ≤ deg k`, as the degree of the one-variable index `(k_0)`. -/
theorem deg_const_le (k : Fin (n + 1) → ℤ) : deg (fun _ : Fin 1 => k 0) ≤ deg k :=
  deg_le_iff.2 fun _ => natAbs_le_deg k 0

/-- The restriction of a monomial to the face is a monomial: `e_k(0, x') = e_{k'}(x')`. -/
theorem restrictFace_trigMonomial (k : Fin (n + 1) → ℤ) :
    restrictFace n (trigMonomial k) = trigMonomial (Fin.tail k) := by
  ext x'
  simp only [compLinear_apply, face_apply, trigMonomial_apply, mFourier, ContinuousMap.coe_mk,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, fourier_eval_zero, one_mul, Fin.tail]

/-- A monomial on a line is a multiple of a one-variable monomial:
`e_k(t, x') = e_{k'}(x') e_{k_0}(t)`. -/
theorem compLinear_lineThrough_trigMonomial (x' : UnitAddTorus (Fin n)) (k : Fin (n + 1) → ℤ) :
    compLinear (lineThrough x') (trigMonomial k) =
      mFourier (Fin.tail k) x' • trigMonomial (fun _ : Fin 1 => k 0) := by
  ext v
  simp only [compLinear_apply, lineThrough_apply, trigMonomial_apply, mFourier,
    ContinuousMap.coe_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Fin.tail]
  ring

/-- The restriction of a trigonometric polynomial of degree `< m` to the face is a trigonometric
polynomial of degree `< m`. -/
theorem restrictFace_mem_trigPoly {m : ℕ} {a : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ}
    (ha : a ∈ trigPoly (Fin (n + 1)) m) : restrictFace n a ∈ trigPoly (Fin n) m :=
  map_mem_trigPoly _ (fun k hk => by
    rw [restrictFace_trigMonomial]
    exact trigMonomial_mem_trigPoly ((deg_tail_le k).trans_lt hk)) ha

/-- The restriction of a trigonometric polynomial of degree `< m` to a line is a one-variable
trigonometric polynomial of degree `< m`. -/
theorem compLinear_lineThrough_mem_trigPoly (x' : UnitAddTorus (Fin n)) {m : ℕ}
    {a : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ} (ha : a ∈ trigPoly (Fin (n + 1)) m) :
    compLinear (lineThrough x') a ∈ trigPoly (Fin 1) m :=
  map_mem_trigPoly _ (fun k hk => by
    rw [compLinear_lineThrough_trigMonomial]
    exact Submodule.smul_mem _ _ (trigMonomial_mem_trigPoly ((deg_const_le k).trans_lt hk))) ha

/-- **Fubini on `𝕋^(n+1) = 𝕋 × 𝕋^n`**, with the first factor written as `𝕋^1`:
`∫ F = ∫_{x'} ∫_v F(v_0, x')`. -/
theorem lintegral_eq_lintegral_cons {F : UnitAddTorus (Fin (n + 1)) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x =
      ∫⁻ x' : UnitAddTorus (Fin n), ∫⁻ v : UnitAddTorus (Fin 1), F (Fin.cons (v 0) x') := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) 0
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ => UnitAddCircle) 0
  have he' : ∀ y : UnitAddCircle × UnitAddTorus (Fin n), e.symm y = Fin.cons y.1 y.2 := fun y => by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  have h1 : ∫⁻ x, F x = ∫⁻ y : UnitAddCircle × UnitAddTorus (Fin n), F (e.symm y) :=
    (he.symm.lintegral_comp hF).symm
  have hmeas : Measurable fun y : UnitAddCircle × UnitAddTorus (Fin n) => F (e.symm y) :=
    hF.comp e.symm.measurable
  rw [h1, Measure.volume_eq_prod, lintegral_prod_symm _ hmeas.aemeasurable]
  congr 1; funext x'
  have hu : Measurable fun u : UnitAddCircle => F (Fin.cons u x') := by
    have := hmeas.comp (measurable_id.prodMk (measurable_const (a := x')))
    simpa [Function.comp_def, he'] using this
  simp only [he']
  rw [← (volume_preserving_funUnique (Fin 1) UnitAddCircle).lintegral_comp hu]
  simp [MeasurableEquiv.funUnique_apply]
  rfl

/-- **The one-dimensional Nikolskii inequality**, pointwise in `ℝ≥0∞`: for a trigonometric
polynomial `F` of degree `< m` on `𝕋^1` and `1 ≤ p < ∞`, `|F(v)|^p ≤ 2⌈p/2⌉ m ∫ |F|^p`. -/
theorem enorm_rpow_le_lintegral {m : ℕ} {F : UnitAddTorus (Fin 1) →ᵇ ℂ}
    (hF : F ∈ trigPoly (Fin 1) m) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (v : UnitAddTorus (Fin 1)) :
    ‖F v‖ₑ ^ p.toReal ≤ ((2 * (⌈p.toReal / 2⌉₊ * m) : ℕ) : ℝ≥0∞) * ∫⁻ w, ‖F w‖ₑ ^ p.toReal := by
  set P := p.toReal
  have hP0 : 0 < P := zero_lt_one.trans_le (ENNReal.one_le_toReal_of_one_le hp hp')
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have h := norm_rpow_le_card_mul_eLpNorm_rpow hF hp hp'
  rw [Fintype.card_fin, pow_one] at h
  have hfin : eLpNorm F p volume ≠ ∞ :=
    ((F.memLp_top (μ := volume)).mono_exponent le_top).eLpNorm_ne_top
  have hI : eLpNorm F p volume ^ P = ∫⁻ w, ‖F w‖ₑ ^ P := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp' F.continuous.aestronglyMeasurable,
      one_div, ENNReal.rpow_inv_rpow hP0.ne']
  calc ‖F v‖ₑ ^ P = ENNReal.ofReal (‖F v‖ ^ P) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP0.le]
    _ ≤ ENNReal.ofReal (‖F‖ ^ P) := ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (norm_nonneg _) (F.norm_coe_le_norm v) hP0.le)
    _ ≤ ENNReal.ofReal (((2 * (⌈P / 2⌉₊ * m) : ℕ) : ℝ) * (eLpNorm F p volume).toReal ^ P) :=
        ENNReal.ofReal_le_ofReal h
    _ = ((2 * (⌈P / 2⌉₊ * m) : ℕ) : ℝ≥0∞) * eLpNorm F p volume ^ P := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.toReal_rpow,
          ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hP0.le hfin)]
    _ = _ := by rw [hI]

/-- **The trace inequality on the torus**: for a trigonometric polynomial `a` of degree `< m`
on `𝕋^(n+1)` and `1 ≤ p < ∞`, `‖a(0, ·)‖_p ≤ (2⌈p/2⌉ m)^(1/p) ‖a‖_p`. -/
theorem eLpNorm_restrictFace_le {m : ℕ} {a : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ}
    (ha : a ∈ trigPoly (Fin (n + 1)) m) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (restrictFace n a) p volume ≤
      ((2 * (⌈p.toReal / 2⌉₊ * m) : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) * eLpNorm a p volume := by
  set P := p.toReal
  set N : ℝ≥0∞ := ((2 * (⌈P / 2⌉₊ * m) : ℕ) : ℝ≥0∞)
  have hP0 : 0 < P := zero_lt_one.trans_le (ENNReal.one_le_toReal_of_one_le hp hp')
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp'
      (restrictFace n a).continuous.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp' a.continuous.aestronglyMeasurable,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hmeas : Measurable fun x => ‖a x‖ₑ ^ P := a.continuous.measurable.eNorm.pow_const P
  calc ∫⁻ x', ‖restrictFace n a x'‖ₑ ^ P
      ≤ ∫⁻ x', N * ∫⁻ v : UnitAddTorus (Fin 1), ‖a (Fin.cons (v 0) x')‖ₑ ^ P := by
        refine lintegral_mono fun x' => ?_
        exact enorm_rpow_le_lintegral (compLinear_lineThrough_mem_trigPoly x' ha) hp hp'
          (fun _ => 0)
    _ = N * ∫⁻ x', ∫⁻ v : UnitAddTorus (Fin 1), ‖a (Fin.cons (v 0) x')‖ₑ ^ P :=
        lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
    _ = N * ∫⁻ x, ‖a x‖ₑ ^ P := by rw [lintegral_eq_lintegral_cons hmeas]

/-! ### Extension from the face -/

/-- The projection `x ↦ (x_1, …, x_n)` of `𝕋^(n+1)` onto the face coordinates. -/
noncomputable def tailMap (n : ℕ) : C(UnitAddTorus (Fin (n + 1)), UnitAddTorus (Fin n)) :=
  ⟨Fin.tail, continuous_pi fun i => continuous_apply i.succ⟩

@[simp]
theorem tailMap_apply (x : UnitAddTorus (Fin (n + 1))) : tailMap n x = Fin.tail x := rfl

/-- `deg (0, k') = deg k'`, at most. -/
theorem deg_cons_zero_le (k : Fin n → ℤ) : deg (Fin.cons 0 k : Fin (n + 1) → ℤ) ≤ deg k :=
  deg_le_iff.2 fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using natAbs_le_deg k j

/-- A monomial of the face coordinates is a monomial of `𝕋^(n+1)`: `e_{k'}(x') = e_{(0,k')}(x)`. -/
theorem compLinear_tailMap_trigMonomial (k : Fin n → ℤ) :
    compLinear (tailMap n) (trigMonomial k) = trigMonomial (Fin.cons 0 k) := by
  ext x
  simp only [compLinear_apply, tailMap_apply, trigMonomial_apply, mFourier, ContinuousMap.coe_mk,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, fourier_zero, one_mul, Fin.tail]

/-- A trigonometric polynomial of the face coordinates is one of `𝕋^(n+1)`, of the same
degree. -/
theorem compLinear_tailMap_mem_trigPoly {m : ℕ} {b : UnitAddTorus (Fin n) →ᵇ ℂ}
    (hb : b ∈ trigPoly (Fin n) m) : compLinear (tailMap n) b ∈ trigPoly (Fin (n + 1)) m :=
  map_mem_trigPoly _ (fun k hk => by
    rw [compLinear_tailMap_trigMonomial]
    exact trigMonomial_mem_trigPoly ((deg_cons_zero_le k).trans_lt hk)) hb

/-- The monomial `e^{2πi j x_0}` at `(u, x')` is `e^{2πi j u}`. -/
theorem trigMonomial_single_cons (j : ℤ) (u : UnitAddCircle) (x' : UnitAddTorus (Fin n)) :
    trigMonomial (Pi.single 0 j : Fin (n + 1) → ℤ) (Fin.cons u x') = fourier j u := by
  simp only [trigMonomial_apply, mFourier, ContinuousMap.coe_mk, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Pi.single_eq_same]
  rw [Finset.prod_eq_one fun i _ => by simp [Fin.succ_ne_zero], mul_one]

/-- `deg (j, 0, …, 0) = |j|`, at most. -/
theorem deg_single_le (j : ℤ) : deg (Pi.single 0 j : Fin (n + 1) → ℤ) ≤ j.natAbs :=
  deg_le_iff.2 fun i => by
    by_cases h : i = 0
    · subst h; simp
    · simp [h]

/-- The conjugate of a monomial is the monomial of the opposite frequency. -/
theorem star_trigMonomial {d : Type*} [Fintype d] (k : d → ℤ) :
    star (trigMonomial k) = trigMonomial (-k) := by
  ext x
  simp only [BoundedContinuousFunction.star_apply, trigMonomial_apply, mFourier,
    ContinuousMap.coe_mk, Pi.neg_apply, fourier_neg]
  rw [show star (∏ i, (fourier (k i)) (x i)) = (starRingEnd ℂ) (∏ i, (fourier (k i)) (x i)) from
    rfl, map_prod]

/-- The conjugate of a trigonometric polynomial of degree `< m` has degree `< m`. -/
theorem star_mem_trigPoly {d : Type*} [Fintype d] {m : ℕ} {T : UnitAddTorus d →ᵇ ℂ}
    (hT : T ∈ trigPoly d m) : star T ∈ trigPoly d m := by
  obtain ⟨t, ht, c, rfl⟩ := exists_sum_of_mem_trigPoly hT
  rw [star_sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  rw [star_smul, star_trigMonomial]
  refine Submodule.smul_mem _ _ (trigMonomial_mem_trigPoly ?_)
  have : deg (-k) = deg k := by simp [deg]
  rw [this]; exact mem_boxLt.1 (ht hk)

/-- The **Dirichlet sum** `D_m(x) = ∑_{j<m} e^{2πi j x_0}` on `𝕋^(n+1)`. -/
noncomputable def dirichletSum (n m : ℕ) : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ :=
  ∑ j ∈ Finset.range m, trigMonomial (Pi.single 0 (j : ℤ))

theorem dirichletSum_cons (m : ℕ) (u : UnitAddCircle) (x' : UnitAddTorus (Fin n)) :
    dirichletSum n m (Fin.cons u x') = ∑ j ∈ Finset.range m, fourier (j : ℤ) u := by
  simp only [dirichletSum, FunLike.coe_sum, Finset.sum_apply,
    trigMonomial_single_cons]

/-- `D_m` has degree `< m`. -/
theorem dirichletSum_mem_trigPoly (m : ℕ) : dirichletSum n m ∈ trigPoly (Fin (n + 1)) m :=
  Submodule.sum_mem _ fun j hj => trigMonomial_mem_trigPoly
    ((deg_single_le _).trans_lt (by simpa using Finset.mem_range.1 hj))

/-- `|D_m| ≤ m`. -/
theorem norm_dirichletSum_le (m : ℕ) (x : UnitAddTorus (Fin (n + 1))) :
    ‖dirichletSum n m x‖ ≤ m := by
  simp only [dirichletSum, FunLike.coe_sum, Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_trigMonomial_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    le_refl]

/-- `‖D_m‖_2² = m`, by Parseval. -/
theorem lintegral_enorm_dirichletSum_sq (m : ℕ) :
    ∫⁻ x, ‖dirichletSum n m x‖ₑ ^ (2 : ℝ) = m := by
  have hinj : Set.InjOn (fun j : ℕ => (Pi.single 0 (j : ℤ) : Fin (n + 1) → ℤ))
      (Finset.range m : Set ℕ) := fun i _ j _ h => by
    have := congr_fun h 0
    simpa using this
  have hD : dirichletSum n m = ∑ k ∈ (Finset.range m).image
      (fun j : ℕ => (Pi.single 0 (j : ℤ) : Fin (n + 1) → ℤ)), (1 : ℂ) • trigMonomial k := by
    rw [Finset.sum_image hinj]; simp [dirichletSum]
  have h2 := norm_toLp_sum_sq ((Finset.range m).image
    (fun j : ℕ => (Pi.single 0 (j : ℤ) : Fin (n + 1) → ℤ))) (fun _ => (1 : ℂ))
  rw [← hD] at h2
  simp only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at h2
  have hfin : eLpNorm (dirichletSum n m) 2 volume ≠ ∞ :=
    (((dirichletSum n m).memLp_top (μ := volume)).mono_exponent le_top).eLpNorm_ne_top
  rw [BoundedContinuousFunction.norm_toLp_eq_toReal_eLpNorm] at h2
  have he : eLpNorm (dirichletSum n m) 2 volume ^ (2 : ℝ) =
      ∫⁻ x, ‖dirichletSum n m x‖ₑ ^ (2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
      (dirichletSum n m).continuous.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, one_div]
    rw [ENNReal.rpow_inv_rpow (by norm_num)]
  rw [← he, ← ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin),
    ← ENNReal.toReal_rpow, Real.rpow_two, h2, ENNReal.ofReal_natCast]

/-- The **normalised Fejér kernel** in `x_0`: `φ_m = m^(-2) |D_m|²`, with `φ_m(0, x') = 1`,
`0 ≤ φ_m ≤ 1` and `∫ φ_m = 1/m`. -/
noncomputable def fejerFace (n m : ℕ) : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ :=
  ((m : ℂ) ^ 2)⁻¹ • (dirichletSum n m * star (dirichletSum n m))

theorem fejerFace_apply (m : ℕ) (x : UnitAddTorus (Fin (n + 1))) :
    fejerFace n m x = (((m : ℝ) ^ 2)⁻¹ * ‖dirichletSum n m x‖ ^ 2 : ℝ) := by
  simp only [fejerFace, FunLike.coe_smul, Pi.smul_apply,
    FunLike.coe_mul, BoundedContinuousFunction.star_apply, Pi.mul_apply,
    smul_eq_mul]
  rw [show star (dirichletSum n m x) = (starRingEnd ℂ) (dirichletSum n m x) from rfl,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- `φ_m` has degree `< 2m`. -/
theorem fejerFace_mem_trigPoly (m : ℕ) : fejerFace n m ∈ trigPoly (Fin (n + 1)) (m + m) :=
  Submodule.smul_mem _ _ (mul_mem_trigPoly (dirichletSum_mem_trigPoly m)
    (star_mem_trigPoly (dirichletSum_mem_trigPoly m)))

/-- `|φ_m| ≤ 1`. -/
theorem enorm_fejerFace_le (m : ℕ) (x : UnitAddTorus (Fin (n + 1))) : ‖fejerFace n m x‖ₑ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [fejerFace]
  rw [fejerFace_apply, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, ENNReal.ofReal_le_one,
    abs_of_nonneg (by positivity)]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [inv_mul_le_iff₀ (by positivity), mul_one]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletSum_le m x) 2

/-- `φ_m(0, x') = 1` for `m ≥ 1`. -/
theorem fejerFace_cons_zero {m : ℕ} (hm : 1 ≤ m) (x' : UnitAddTorus (Fin n)) :
    fejerFace n m (Fin.cons 0 x') = 1 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hm)
  rw [fejerFace_apply, dirichletSum_cons]
  simp only [fourier_eval_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Complex.norm_natCast]
  push_cast
  field_simp
  exact div_self (by exact_mod_cast hm')

/-- `∫ φ_m = 1/m`. -/
theorem lintegral_enorm_fejerFace {m : ℕ} (hm : 1 ≤ m) :
    ∫⁻ x, ‖fejerFace n m x‖ₑ = (m : ℝ≥0∞)⁻¹ := by
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hm)
  have hpt : ∀ x, ‖fejerFace n m x‖ₑ = ((m : ℝ≥0∞) ^ 2)⁻¹ * ‖dirichletSum n m x‖ₑ ^ (2 : ℝ) :=
    fun x => by
      have hmr : (0 : ℝ) < (m : ℝ) ^ 2 := by
        have : (0 : ℝ) < m := by exact_mod_cast hm
        positivity
      rw [fejerFace_apply, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_inv_of_pos hmr, ENNReal.ofReal_pow (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (pow_ne_zero 2 hm0)),
    lintegral_enorm_dirichletSum_sq, pow_two,
    ENNReal.mul_inv (Or.inl hm0) (Or.inl (ENNReal.natCast_ne_top m)),
    mul_assoc, ENNReal.inv_mul_cancel hm0 (ENNReal.natCast_ne_top m), mul_one]

/-- The **extension** of a function `b` on the face: `(φ_m b)(x) = φ_m(x_0) b(x')`. -/
noncomputable def extendFace (n m : ℕ) (b : UnitAddTorus (Fin n) →ᵇ ℂ) :
    UnitAddTorus (Fin (n + 1)) →ᵇ ℂ :=
  fejerFace n m * compLinear (tailMap n) b

/-- The extension of a polynomial of degree `< m` has degree `< 3m`. -/
theorem extendFace_mem_trigPoly {m : ℕ} {b : UnitAddTorus (Fin n) →ᵇ ℂ}
    (hb : b ∈ trigPoly (Fin n) m) : extendFace n m b ∈ trigPoly (Fin (n + 1)) (m + m + m) :=
  mul_mem_trigPoly (fejerFace_mem_trigPoly m) (compLinear_tailMap_mem_trigPoly hb)

/-- The extension restricts to `b` on the face. -/
theorem restrictFace_extendFace {m : ℕ} (hm : 1 ≤ m) (b : UnitAddTorus (Fin n) →ᵇ ℂ) :
    restrictFace n (extendFace n m b) = b := by
  ext x'
  simp [extendFace, fejerFace_cons_zero hm, Fin.tail_cons]

/-- **The extension is small**: `‖φ_m b‖_p ≤ m^(-1/p) ‖b‖_p` for `1 ≤ p < ∞`. -/
theorem eLpNorm_extendFace_le {m : ℕ} (hm : 1 ≤ m) (b : UnitAddTorus (Fin n) →ᵇ ℂ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (extendFace n m b) p volume ≤ (m : ℝ≥0∞) ^ (-p.toReal⁻¹) * eLpNorm b p volume := by
  set P := p.toReal
  have hP1 : 1 ≤ P := ENNReal.one_le_toReal_of_one_le hp hp'
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set ψ : UnitAddCircle → ℝ≥0∞ := fun u => ‖fejerFace n m (Fin.cons u (0 : UnitAddTorus (Fin n)))‖ₑ
  have hφ : ∀ u x', fejerFace n m (Fin.cons u x') = fejerFace n m (Fin.cons u 0) := fun u x' => by
    rw [fejerFace_apply, fejerFace_apply, dirichletSum_cons, dirichletSum_cons]
  -- `∫ φ_m^p ≤ ∫ φ_m = 1/m`, integrated over the first coordinate
  have hψ : ∫⁻ v : UnitAddTorus (Fin 1), ψ (v 0) ^ P ≤ (m : ℝ≥0∞)⁻¹ := by
    have hmeasφ : Measurable fun x => ‖fejerFace n m x‖ₑ :=
      (fejerFace n m).continuous.measurable.eNorm
    have h1 := lintegral_eq_lintegral_cons hmeasφ
    simp_rw [hφ] at h1
    rw [lintegral_const, measure_univ, mul_one, lintegral_enorm_fejerFace hm] at h1
    calc ∫⁻ v : UnitAddTorus (Fin 1), ψ (v 0) ^ P ≤ ∫⁻ v : UnitAddTorus (Fin 1), ψ (v 0) :=
          lintegral_mono fun v => ENNReal.rpow_le_self_of_le_one (enorm_fejerFace_le m _) hP1
      _ = (m : ℝ≥0∞)⁻¹ := h1.symm
  have hmeas : Measurable fun x => ‖extendFace n m b x‖ₑ ^ P :=
    (extendFace n m b).continuous.measurable.eNorm.pow_const P
  have hint : ∫⁻ x, ‖extendFace n m b x‖ₑ ^ P ≤ (m : ℝ≥0∞)⁻¹ * ∫⁻ x', ‖b x'‖ₑ ^ P := by
    rw [lintegral_eq_lintegral_cons hmeas]
    calc ∫⁻ x', ∫⁻ v : UnitAddTorus (Fin 1), ‖extendFace n m b (Fin.cons (v 0) x')‖ₑ ^ P
        = ∫⁻ x', (∫⁻ v : UnitAddTorus (Fin 1), ψ (v 0) ^ P) * ‖b x'‖ₑ ^ P := by
          congr 1; funext x'
          rw [← lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hP0.le eNorm_ne_top)]
          congr 1; funext v
          simp only [extendFace, FunLike.coe_mul, Pi.mul_apply,
            compLinear_apply, tailMap_apply, Fin.tail_cons, eNorm_mul, ψ, hφ (v 0) x']
          rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le]
      _ = (∫⁻ v : UnitAddTorus (Fin 1), ψ (v 0) ^ P) * ∫⁻ x', ‖b x'‖ₑ ^ P :=
          lintegral_const_mul' _ _ (ne_top_of_le_ne_top (ENNReal.inv_ne_top.2
            (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hm))) hψ)
      _ ≤ (m : ℝ≥0∞)⁻¹ * ∫⁻ x', ‖b x'‖ₑ ^ P := by gcongr
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp'
      (extendFace n m b).continuous.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp' b.continuous.aestronglyMeasurable]
  calc (∫⁻ x, ‖extendFace n m b x‖ₑ ^ P) ^ (1 / P)
      ≤ ((m : ℝ≥0∞)⁻¹ * ∫⁻ x', ‖b x'‖ₑ ^ P) ^ (1 / P) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = (m : ℝ≥0∞) ^ (-P⁻¹) * (∫⁻ x', ‖b x'‖ₑ ^ P) ^ (1 / P) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.inv_rpow, ← ENNReal.rpow_neg,
          one_div]

/-! ### The trace as a trace bound -/

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The `L_p` classes of bounded continuous functions, as a real-linear map. -/
noncomputable abbrev toLpR (d : Type*) [Fintype d] :
    (UnitAddTorus d →ᵇ ℂ) →ₗ[ℝ] Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  (BoundedContinuousFunction.toLp (E := ℂ) p volume ℝ).toLinearMap

theorem toLpR_injective (d : Type*) [Fintype d] : Function.Injective (toLpR p d) :=
  BoundedContinuousFunction.toLp_injective (E := ℂ) (p := p) (𝕜 := ℝ) volume

theorem enorm_toLpR {d : Type*} [Fintype d] (a : UnitAddTorus d →ᵇ ℂ) :
    ‖toLpR p d a‖ₑ = eLpNorm a p volume := by
  rw [Lp.eNorm_def]
  exact eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp p volume ℝ a)

/-- Every approximant of the trigonometric scheme in `L_p` is the class of a bounded continuous
function. -/
theorem iUnionSubmodule_le_range (d : Type*) [Fintype d] :
    ((trigScheme d).toLp volume p).iUnionSubmodule ≤ LinearMap.range (toLpR p d) := by
  intro g hg
  rw [← SetLike.mem_coe, ApproximationScheme.coe_iUnionSubmodule, Set.mem_iUnion] at hg
  obtain ⟨k, a, -, rfl⟩ := hg
  exact ⟨a, rfl⟩

/-- The restriction to the face on the `L_p` classes of trigonometric polynomials. -/
noncomputable def traceOnApprox (n : ℕ) :
    ((trigScheme (Fin (n + 1))).toLp volume p).iUnionSubmodule →ₗ[ℝ]
      Lp ℂ p (volume : Measure (UnitAddTorus (Fin n))) :=
  toLpR p (Fin n) ∘ₗ (restrictFace n).restrictScalars ℝ ∘ₗ
    (LinearEquiv.ofInjective (toLpR p (Fin (n + 1))) (toLpR_injective p _)).symm.toLinearMap ∘ₗ
      Submodule.inclusion (iUnionSubmodule_le_range p (Fin (n + 1)))

theorem traceOnApprox_apply (a : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ)
    (h : toLpR p (Fin (n + 1)) a ∈ ((trigScheme (Fin (n + 1))).toLp volume p).iUnionSubmodule) :
    traceOnApprox p n ⟨toLpR p (Fin (n + 1)) a, h⟩ = toLpR p (Fin n) (restrictFace n a) := by
  have he : Submodule.inclusion (iUnionSubmodule_le_range p (Fin (n + 1)))
      ⟨toLpR p (Fin (n + 1)) a, h⟩ =
        LinearEquiv.ofInjective (toLpR p (Fin (n + 1))) (toLpR_injective p _) a :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; rfl)
  simp only [traceOnApprox, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, he,
    LinearEquiv.symm_apply_apply, LinearMap.restrictScalars_apply]

/-- The constant `(2⌈p/2⌉)^(1/p)` of the trace inequality. -/
noncomputable def traceConstTorus : ℝ≥0∞ := ((2 * ⌈p.toReal / 2⌉₊ : ℕ) : ℝ≥0∞) ^ p.toReal⁻¹

/-- **The restriction to the face is a trace bound** of exponent `1/p` from the trigonometric
scheme of `𝕋^(n+1)` to that of `𝕋^n` in `L_p`, `1 ≤ p < ∞`. -/
noncomputable def traceBound (n : ℕ) (hp : p ≠ ∞) :
    ApproximationScheme.TraceBound ((trigScheme (Fin (n + 1))).toLp volume p)
      ((trigScheme (Fin n)).toLp volume p) p.toReal⁻¹ :=
  ApproximationScheme.TraceBound.ofSubmodule (traceOnApprox p n)
    (fun m g hg => by
      obtain ⟨a, ha, hag⟩ := hg
      have hg' : g = ⟨toLpR p (Fin (n + 1)) a, hag ▸ g.2⟩ := Subtype.ext hag.symm
      rw [hg', traceOnApprox_apply]
      exact FunctionScheme.toLp_mem_toLp (restrictFace_mem_trigPoly ha))
    (traceConstTorus p) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.natCast_ne_top _))
    (fun m hm g hg => by
      obtain ⟨a, ha, hag⟩ := hg
      have hg' : g = ⟨toLpR p (Fin (n + 1)) a, hag ▸ g.2⟩ := Subtype.ext hag.symm
      rw [hg', traceOnApprox_apply, enorm_toLpR, enorm_toLpR]
      refine (eLpNorm_restrictFace_le ha (Fact.out) hp).trans_eq ?_
      rw [traceConstTorus, one_div, Nat.cast_mul, Nat.cast_mul, ← mul_assoc, Nat.cast_mul,
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)])

/-- On trigonometric polynomials the trace is the restriction to the face. -/
theorem traceBound_T_toLp (hp : p ≠ ∞) {m : ℕ} {a : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ}
    (ha : a ∈ trigPoly (Fin (n + 1)) m) :
    (traceBound p n hp).T (toLpR p (Fin (n + 1)) a) = toLpR p (Fin n) (restrictFace n a) := by
  have hmem : toLpR p (Fin (n + 1)) a ∈
      ((trigScheme (Fin (n + 1))).toLp volume p).iUnionSubmodule :=
    ApproximationScheme.mem_iUnionSubmodule (FunctionScheme.toLp_mem_toLp (n := m) ha)
  unfold traceBound
  exact (ApproximationScheme.TraceBound.ofSubmodule_T _ _ _ _ _ ⟨_, hmem⟩).trans
    (traceOnApprox_apply p a hmem)

/-- **The trace of a trigonometric polynomial** is its restriction to the face. -/
theorem traceBound_ext_toLp (hp : p ≠ ∞) {m : ℕ} {a : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ}
    (ha : a ∈ trigPoly (Fin (n + 1)) m) :
    (traceBound p n hp).ext (toLpR p (Fin (n + 1)) a) = toLpR p (Fin n) (restrictFace n a) := by
  exact ((traceBound p n hp).ext_eq_of_mem (by positivity)
    (FunctionScheme.toLp_mem_toLp (n := m) ha)).trans (traceBound_T_toLp p hp ha)

/-- **The extension is a right inverse on approximants**: every polynomial of degree `< 2^k` on
`𝕋^n` is the trace of a polynomial of degree `< 2^(k+2)` on `𝕋^(n+1)` of norm
`≤ 2^(-k/p) ‖b‖_p`. -/
theorem traceBound_rightInverse (hp : p ≠ ∞) :
    (traceBound p n hp).RightInverseBound 2 1 := by
  intro k b' hb'
  obtain ⟨b, hb, rfl⟩ := hb'
  have hm : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hmem : extendFace n (2 ^ k) b ∈ trigPoly (Fin (n + 1)) (2 ^ (k + 2)) :=
    trigPoly_mono (by rw [pow_add]; omega) (extendFace_mem_trigPoly hb)
  refine ⟨toLpR p (Fin (n + 1)) (extendFace n (2 ^ k) b), FunctionScheme.toLp_mem_toLp hmem, ?_, ?_⟩
  · rw [traceBound_T_toLp p hp hmem, restrictFace_extendFace hm]
  · rw [enorm_toLpR, one_mul, ← ENNReal.natCast_two_pow_rpow]
    exact (eLpNorm_extendFace_le hm b Fact.out hp).trans_eq (by rw [enorm_toLpR])

/-- **The trace theorem on the torus**: for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `s > 0`, the
restriction to the face `{x_0 = 0}` extends from trigonometric polynomials to a map from
`B^{s+1/p}_{p,q}(𝕋^(n+1))` into `B^s_{p,q}(𝕋^n)`, and every `g ∈ B^s_{p,q}(𝕋^n)` is the trace
of some `f ∈ B^{s+1/p}_{p,q}(𝕋^(n+1))`. -/
theorem trace_besov (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    (∀ f, (trigScheme (Fin (n + 1))).MemBesov volume p (s + p.toReal⁻¹) q f →
      (trigScheme (Fin n)).MemBesov volume p s q ((traceBound p n hp).ext f)) ∧
    (∀ g, (trigScheme (Fin n)).MemBesov volume p s q g →
      ∃ f, (trigScheme (Fin (n + 1))).MemBesov volume p (s + p.toReal⁻¹) q f ∧
        (traceBound p n hp).ext f = g) := by
  have hβ : 0 ≤ p.toReal⁻¹ := by positivity
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · have := (traceBound p n hp).memApprox_ext hβ (by linarith) hq hf
    rwa [add_sub_cancel_right] at this
  · obtain ⟨f, hf, hfg, -⟩ := (traceBound p n hp).exists_ext_eq hβ ENNReal.one_ne_top
      (traceBound_rightInverse p hp) hs hq hg
    exact ⟨f, hf, hfg⟩

end Torus
