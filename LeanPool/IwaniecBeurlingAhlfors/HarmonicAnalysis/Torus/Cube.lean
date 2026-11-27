/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Defs
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The torus `𝕋^ι`, periodic functions on `ℝ^ι` and the unit cube

* `UnitAddTorus.ofPi : ℝ^ι → 𝕋^ι = (ℝ / ℤ)^ι` and its measurable section
  `UnitAddTorus.toPi : 𝕋^ι → (0, 1]^ι`; `ℤ^ι`-periodic functions (`UnitAddTorus.IsPeriodic`).
* The open unit cube `(0, 1)^ι` (`UnitAddTorus.cube`): integrals over the torus, with the Haar
  measure of total mass one, are integrals over the cube (`UnitAddTorus.integral_cube_ofPi`); the
  monomials `e_n (x) = e^{2πi ⟨n, x⟩}` on `ℝ^ι` (`UnitAddTorus.mFourier_ofPi`) and their
  orthogonality on the cube (`UnitAddTorus.integral_cube_mFourier`).
* The torus `𝕋²` and `ℂ ≅ ℝ²` (`x + iy ↦ (x, y)`): the lattice point `n₀ + i n₁` of `n ∈ ℤ²`
  (`HarmonicAnalysis.latticePoint`), the projection `HarmonicAnalysis.ofComplex : ℂ → 𝕋²`, with
  `e_n (y) = e^{2πi ⟨n₀ + i n₁, y⟩}` (`HarmonicAnalysis.mFourier_ofComplex`), and integrals over
  `𝕋²` as integrals over the centred cell `(−½, ½]²` of `ℂ`
  (`HarmonicAnalysis.lintegral_torus_eq_centredCell`).
* The dilated cell `R · (−½, ½]² = {y : y / R ∈ (−½, ½]²}`, `R > 0`
  (`HarmonicAnalysis.div_mem_centredCell_iff`, `HarmonicAnalysis.measurableSet_dilatedCell`):
  `∫_{R · (−½, ½]²} f (y / R) dy = R² ∫_{𝕋²} f` (`HarmonicAnalysis.setLIntegral_dilatedCell`,
  `HarmonicAnalysis.lintegral_torus_eq_dilatedCell`), for every `f : 𝕋² → [0, ∞]`;
  `R^{2/p} ‖F‖_{L^p (𝕋²)} = ‖F (· / R) 1_{R · (−½, ½]²}‖_{L^p (ℂ)}` for `0 < p` and every `F`
  (`HarmonicAnalysis.ofReal_rpow_mul_eLpNorm_torus_eq_dilatedCell`); these cells exhaust `ℂ` as
  `R → ∞` (`HarmonicAnalysis.eventually_div_mem_centredCell`).

The first two items normalise the measure on `ℝ / ℤ` as `Mathlib.Analysis.Fourier.AddCircleMulti`
does, with its local instances; the last two items use Mathlib's global measure on `ℝ / ℤ`, which
is the same measure of total mass one (`HarmonicAnalysis.volume_eq_pi_haarAddCircle`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Complex
open scoped ComplexConjugate Real Finset ENNReal

section HaarNormalized

/-! As in `Mathlib.Analysis.Fourier.AddCircleMulti`, the measure on `ℝ / ℤ` is the Haar measure of
total mass one. -/
attribute [local instance] instMeasureSpaceUnitAddCircle instIsAddHaarMeasureUnitAddCircleVolume
  instIsProbabilityMeasureUnitAddCircleVolume

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-! ### Periodic functions on `ℝ^ι` and functions on the torus -/

/-- The projection `ℝ^ι → 𝕋^ι = (ℝ / ℤ)^ι`. -/
def ofPi (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

omit [Fintype ι] in
theorem continuous_ofPi : Continuous (ofPi : (ι → ℝ) → UnitAddTorus ι) :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_apply i)

omit [Fintype ι] in
theorem measurable_ofPi [Finite ι] : Measurable (ofPi : (ι → ℝ) → UnitAddTorus ι) :=
  continuous_ofPi.measurable

omit [Fintype ι] in
theorem ofPi_add (x y : ι → ℝ) : ofPi (x + y) = ofPi x + ofPi y := by
  funext i; simp [ofPi]

omit [Fintype ι] in
theorem ofPi_add_int (x : ι → ℝ) (k : ι → ℤ) : ofPi (x + fun i => (k i : ℝ)) = ofPi x := by
  funext i
  simp only [ofPi, Pi.add_apply, AddCircle.coe_add, add_eq_left]
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k i, by simp⟩

/-- The representative of a point of the torus in `(0, 1]^ι`. -/
def toPi (z : UnitAddTorus ι) : ι → ℝ := ((measurableEquivPiIoc (0 : ι → ℝ) z : _) : ι → ℝ)

omit [Fintype ι] in
theorem measurable_toPi : Measurable (toPi : UnitAddTorus ι → ι → ℝ) :=
  measurable_subtype_coe.comp (measurableEquivPiIoc (0 : ι → ℝ)).measurable

omit [Fintype ι] in
theorem ofPi_toPi (z : UnitAddTorus ι) : ofPi (toPi z) = z := by
  funext i
  simp [ofPi, toPi]

omit [Fintype ι] in
theorem exists_toPi_ofPi (x : ι → ℝ) : ∃ k : ι → ℤ, toPi (ofPi x) = x + fun i => (k i : ℝ) := by
  have h : ∀ i, ∃ k : ℤ, toPi (ofPi x) i = x i + k := by
    intro i
    have h1 : ((toPi (ofPi x) i - x i : ℝ) : UnitAddCircle) = 0 := by
      have := congrFun (ofPi_toPi (ofPi x)) i
      simp only [ofPi] at this
      rw [AddCircle.coe_sub, this, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
    exact ⟨k, by simp at hk; linarith⟩
  choose k hk using h
  exact ⟨k, funext fun i => by simp [hk i]⟩

/-- `g` is `ℤ^ι`-periodic. -/
def IsPeriodic {E : Type*} (g : (ι → ℝ) → E) : Prop :=
  ∀ (x : ι → ℝ) (k : ι → ℤ), g (x + fun i => (k i : ℝ)) = g x

omit [Fintype ι] in
theorem IsPeriodic.comp_toPi_ofPi {E : Type*} {g : (ι → ℝ) → E} (hg : IsPeriodic g)
    (x : ι → ℝ) : g (toPi (ofPi x)) = g x := by
  obtain ⟨k, hk⟩ := exists_toPi_ofPi x
  rw [hk, hg]

/-- The open unit cube `(0, 1)^ι`. -/
abbrev cube (ι : Type*) : Set (ι → ℝ) := univ.pi fun _ => Ioo (0 : ℝ) 1

omit [Fintype ι] in
theorem measurableSet_cube [Finite ι] : MeasurableSet (cube ι) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem volume_cube : volume (cube ι) = 1 := by
  rw [Real.volume_pi_Ioo]; simp

instance : IsFiniteMeasure (volume.restrict (cube ι)) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_cube]; exact ENNReal.one_lt_top⟩

/-- Integrals over the torus (with the Haar measure of total mass one, as in
`Mathlib.Analysis.Fourier.AddCircleMulti`) are integrals over the cube. -/
theorem integral_cube_ofPi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : UnitAddTorus ι → E) : ∫ x in cube ι, F (ofPi x) = ∫ z, F z := by
  rw [integral_preimage F 0]
  have h1 : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      univ.pi fun _ => Ioc (0 : ℝ) 1 := by
    ext x; simp
  rw [h1]
  exact setIntegral_congr_set
    (Measure.univ_pi_Ioo_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm)

/-- The integral over the cube of a periodic function is invariant under translations. -/
theorem integral_cube_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hg : IsPeriodic g) (a : ι → ℝ) :
    ∫ x in cube ι, g (x + a) = ∫ x in cube ι, g x := by
  have h1 : ∀ x, g (x + a) = (g ∘ toPi) (ofPi x + ofPi a) := fun x => by
    rw [Function.comp_apply, ← ofPi_add, hg.comp_toPi_ofPi]
  have h2 : ∀ x, g x = (g ∘ toPi) (ofPi x) := fun x => (hg.comp_toPi_ofPi x).symm
  simp_rw [h1, h2]
  rw [integral_cube_ofPi (fun z => (g ∘ toPi) (z + ofPi a)), integral_cube_ofPi,
    integral_add_right_eq_self]

/-! ### The monomials on `ℝ^ι` -/

theorem mFourier_ofPi (n : ι → ℤ) (x : ι → ℝ) :
    mFourier n (ofPi x) = Complex.exp (2 * π * I * ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, ofPi, fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- `|e_n| = 1` on `𝕋^ι`. -/
theorem norm_mFourier_apply_eq_one (n : ι → ℤ) (z : UnitAddTorus ι) : ‖mFourier n z‖ = 1 := by
  simp [mFourier, fourier_apply, norm_prod, Circle.norm_coe]

theorem norm_mFourier_ofPi (n : ι → ℤ) (x : ι → ℝ) : ‖mFourier n (ofPi x)‖ = 1 :=
  norm_mFourier_apply_eq_one n (ofPi x)

theorem mFourier_ofPi_add (n : ι → ℤ) (x y : ι → ℝ) :
    mFourier n (ofPi (x + y)) = mFourier n (ofPi x) * mFourier n (ofPi y) := by
  simp only [mFourier_ofPi, ← Complex.exp_add, Pi.add_apply]
  congr 1
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mFourier_ofPi_neg (n : ι → ℤ) (x : ι → ℝ) :
    mFourier (-n) (ofPi x) = mFourier n (ofPi (-x)) := by
  simp only [mFourier_ofPi, Pi.neg_apply]
  congr 1
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mFourier_ofPi_add_index (m n : ι → ℤ) (x : ι → ℝ) :
    mFourier (m + n) (ofPi x) = mFourier m (ofPi x) * mFourier n (ofPi x) :=
  mFourier_add

theorem continuous_mFourier_ofPi (n : ι → ℤ) : Continuous fun x : ι → ℝ => mFourier n (ofPi x) :=
  (mFourier n).continuous.comp continuous_ofPi

theorem mFourier_ofPi_isPeriodic (n : ι → ℤ) : IsPeriodic fun x : ι → ℝ => mFourier n (ofPi x) :=
  fun x k => by simp only [ofPi_add_int]

/-- Orthogonality: `∫_{(0,1)^ι} e_m = 1` if `m = 0`, and `0` otherwise. -/
theorem integral_cube_mFourier (m : ι → ℤ) :
    ∫ x in cube ι, mFourier m (ofPi x) = if m = 0 then 1 else 0 := by
  rw [integral_cube_ofPi (fun z => mFourier m z)]
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι))) 0 m
  rw [ContinuousMap.inner_toLp] at h
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  rw [h]
  by_cases hm : m = 0 <;> simp [hm, eq_comm]

end UnitAddTorus

end HaarNormalized

namespace HarmonicAnalysis

open UnitAddTorus

/-- Mathlib's measure on the torus, of total mass one, is the product of the Haar probability
measures. -/
theorem volume_eq_pi_haarAddCircle {ι : Type*} [Fintype ι] :
    (volume : Measure (UnitAddTorus ι)) = Measure.pi fun _ : ι => AddCircle.haarAddCircle := by
  rw [volume_pi]
  congr 1
  funext i
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- The projection `ℂ → 𝕋² = (ℝ / ℤ)²`, `y ↦ (Re y, Im y) mod ℤ²`. -/
def ofComplex (y : ℂ) : UnitAddTorus (Fin 2) := ofPi ![y.re, y.im]

/-- The centred cell `{y : Re y, Im y ∈ (−½, ½]}` of the lattice `ℤ² = ℤ + iℤ ⊂ ℂ`. -/
def centredCell : Set ℂ := {y | y.re ∈ Ioc (-2⁻¹ : ℝ) 2⁻¹ ∧ y.im ∈ Ioc (-2⁻¹ : ℝ) 2⁻¹}

/-- The projection `ℂ → 𝕋²` is continuous. -/
theorem continuous_ofComplex : Continuous ofComplex :=
  continuous_ofPi.comp (continuous_pi fun i => by fin_cases i <;> simpa using by fun_prop)

/-- The projection `ℂ → 𝕋²` is measurable. -/
theorem measurable_ofComplex : Measurable ofComplex :=
  continuous_ofComplex.measurable

/-- The centred cell `(−½, ½]²` is measurable. -/
theorem measurableSet_centredCell : MeasurableSet centredCell :=
  (measurable_re measurableSet_Ioc).inter (measurable_im measurableSet_Ioc)

/-- The monomial `e_n` on `ℂ`: `e_n (y) = e^{2πi ⟨n₀ + i n₁, y⟩}`. -/
theorem mFourier_ofComplex (n : Fin 2 → ℤ) (y : ℂ) :
    mFourier n (ofComplex y) =
      Complex.exp (2 * π * Complex.I * (inner ℝ (latticePoint n) y : ℝ)) := by
  rw [ofComplex, mFourier_ofPi]
  congr 1
  simp [Fin.sum_univ_two, latticePoint, Complex.inner]
  ring

/-- Integrals over `𝕋²` (with Mathlib's measure, of total mass one) are integrals over the centred
cell of `ℂ`. -/
theorem lintegral_torus_eq_centredCell (f : UnitAddTorus (Fin 2) → ℝ≥0∞) :
    ∫⁻ x, f x = ∫⁻ y in centredCell, f (ofComplex y) := by
  have hvol : (volume : Measure (UnitAddTorus (Fin 2))) =
      @volume _ (@MeasureSpace.pi (Fin 2) _ (fun _ => UnitAddCircle)
        (fun _ => instMeasureSpaceUnitAddCircle)) :=
    volume_eq_pi_haarAddCircle
  rw [hvol, UnitAddTorus.lintegral_preimage f (fun _ => -2⁻¹),
    ← Complex.volume_preserving_equiv_pi.setLIntegral_comp_preimage_emb
      Complex.measurableEquivPi.measurableEmbedding]
  congr 2
  ext y
  simp only [mem_preimage, mem_ofPred_eq, Fin.forall_fin_two, measurableEquivPi_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, centredCell]
  norm_num

/-! ### Dilated cells

For `R > 0`, the dilated cell `R · (−½, ½]² = {y : y / R ∈ (−½, ½]²}` of `ℂ`: integrals and `L^p`
norms over `𝕋²` as integrals and `L^p` norms over it, after the change of variables `y ↦ y / R`. -/

/-- `y ∈ R · (−½, ½]²` if and only if `Re y, Im y ∈ (−R/2, R/2]`. -/
theorem div_mem_centredCell_iff {R : ℝ} (hR : 0 < R) {y : ℂ} :
    y / R ∈ centredCell ↔ y.re ∈ Ioc (-(R / 2)) (R / 2) ∧ y.im ∈ Ioc (-(R / 2)) (R / 2) := by
  simp only [centredCell, mem_ofPred_eq, div_ofReal_re, div_ofReal_im, mem_Ioc,
    lt_div_iff₀ hR, div_le_iff₀ hR]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The dilated cell `R · (−½, ½]²` is measurable. -/
theorem measurableSet_dilatedCell (R : ℝ) : MeasurableSet {y : ℂ | y / R ∈ centredCell} :=
  measurableSet_centredCell.preimage (measurable_id.div_const _)

/-- Integrals over `𝕋²` (with Mathlib's measure, of total mass one) are, up to the factor `R²`,
integrals over the dilated cell `R · (−½, ½]²`: for `R > 0`,
`∫_{R · (−½, ½]²} f (y / R) dy = R² ∫_{𝕋²} f`. -/
theorem setLIntegral_dilatedCell (f : UnitAddTorus (Fin 2) → ℝ≥0∞) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y in {y : ℂ | y / R ∈ centredCell}, f (ofComplex (y / R)) =
      ENNReal.ofReal (R ^ 2) * ∫⁻ x, f x := by
  have hR' : R⁻¹ ≠ 0 := inv_ne_zero hR.ne'
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.smul₀ R⁻¹ hR'
  have he : ∀ y : ℂ, e y = y / R := fun y => by
    simp [e, Complex.real_smul, div_eq_inv_mul]
  have hmap : Measure.map e volume = ENNReal.ofReal (R ^ 2) • (volume : Measure ℂ) := by
    rw [MeasurableEquiv.coe_smul₀, Measure.map_addHaar_smul volume hR',
      Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin, inv_pow, inv_inv,
      abs_of_nonneg (sq_nonneg R)]
  have hset : {y : ℂ | y / R ∈ centredCell} = e ⁻¹' centredCell := by
    ext y
    simp [he]
  rw [lintegral_torus_eq_centredCell, hset]
  simp_rw [← he]
  calc ∫⁻ y in e ⁻¹' centredCell, f (ofComplex (e y))
      = ∫⁻ y in centredCell, f (ofComplex y) ∂(Measure.map e volume) := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
    _ = _ := by rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

/-- Integrals over `𝕋²` (with Mathlib's measure, of total mass one) as integrals over the dilated
cell `R · (−½, ½]²`: for `R > 0`, `∫_{𝕋²} f = R⁻² ∫_{R · (−½, ½]²} f (y / R) dy`. -/
theorem lintegral_torus_eq_dilatedCell (f : UnitAddTorus (Fin 2) → ℝ≥0∞) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x, f x =
      ENNReal.ofReal (R ^ 2)⁻¹ * ∫⁻ y in {y : ℂ | y / R ∈ centredCell}, f (ofComplex (y / R)) := by
  rw [setLIntegral_dilatedCell f hR, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- A measurable section of `ofComplex` with values in the centred cell, inverse to `ofComplex` on
the cell. -/
private theorem exists_section_ofComplex : ∃ g : UnitAddTorus (Fin 2) → ℂ, Measurable g ∧
    (∀ z, ofComplex (g z) = z) ∧ (∀ z, g z ∈ centredCell) ∧
    ∀ y ∈ centredCell, g (ofComplex y) = y := by
  let e := measurableEquivPiIoc (fun _ : Fin 2 => (-2⁻¹ : ℝ))
  refine ⟨fun z => measurableEquivPi.symm (e z).1, ?_, fun z => ?_, fun z => ?_, fun y hy => ?_⟩
  · exact measurableEquivPi.symm.measurable.comp (measurable_subtype_coe.comp e.measurable)
  · funext i
    fin_cases i <;> simp [ofComplex, ofPi, e]
  · have h := (e z).2
    simp only [Fin.forall_fin_two] at h
    norm_num at h
    simpa [centredCell] using h
  · have h1 : y.re ∈ Ioc (-2⁻¹ : ℝ) (-2⁻¹ + 1) := by convert hy.1 using 2; norm_num
    have h2 : y.im ∈ Ioc (-2⁻¹ : ℝ) (-2⁻¹ + 1) := by convert hy.2 using 2; norm_num
    apply Complex.ext <;> simp [e, ofComplex, ofPi, AddCircle.equivIoc_coe_of_mem h1,
      AddCircle.equivIoc_coe_of_mem h2]

/-- `L^p` norms over `𝕋²` (with Mathlib's measure, of total mass one) as `L^p` norms over the
dilated cell `R · (−½, ½]²`: for `0 < p` and `R > 0`,
`R^{2/p} ‖F‖_{L^p (𝕋²)} = ‖F (· / R) 1_{R · (−½, ½]²}‖_{L^p (ℂ)}`. No measurability of `F` is
assumed. -/
theorem ofReal_rpow_mul_eLpNorm_torus_eq_dilatedCell (F : UnitAddTorus (Fin 2) → ℂ) {p : ℝ}
    (hp : 0 < p) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (R ^ (2 / p)) * eLpNorm F (ENNReal.ofReal p) volume =
      eLpNorm ({y : ℂ | y / R ∈ centredCell}.indicator fun y => F (ofComplex (y / R)))
        (ENNReal.ofReal p) volume := by
  obtain ⟨g, hgm, hg1, hg2, hg3⟩ := exists_section_ofComplex
  set S := {y : ℂ | y / R ∈ centredCell}
  have hS : MeasurableSet S := measurableSet_dilatedCell R
  have hR0 : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR.ne'
  -- `ψ z = R g (z)` is a measurable embedding of `𝕋²` onto the dilated cell, inverse to
  -- `y ↦ ofComplex (y / R)` there.
  let ψ : UnitAddTorus (Fin 2) → ℂ := fun z => R * g z
  have hψφ : ∀ y ∈ S, ψ (ofComplex (y / R)) = y := fun y hy => by
    simp only [ψ, hg3 _ hy]
    field_simp
  have hφψ : ∀ z, ofComplex (ψ z / R) = z := fun z => by
    simp only [ψ]
    rw [mul_div_cancel_left₀ _ hR0]
    exact hg1 z
  have hψS : ∀ z, ψ z ∈ S := fun z => by
    change ψ z / R ∈ centredCell
    simp only [ψ]
    rw [mul_div_cancel_left₀ _ hR0]
    exact hg2 z
  have hψm : Measurable ψ := measurable_const.mul hgm
  have hφm : Measurable fun y : ℂ => ofComplex (y / R) :=
    measurable_ofComplex.comp (measurable_id.div_const _)
  have hemb : MeasurableEmbedding ψ := by
    refine ⟨fun z w h => by rw [← hφψ z, ← hφψ w, h], hψm, fun s hs => ?_⟩
    have : ψ '' s = S ∩ (fun y : ℂ => ofComplex (y / R)) ⁻¹' s := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hψS z, by simp only [mem_preimage, hφψ z, hz]⟩
      · rintro ⟨hy, hys⟩
        exact ⟨_, hys, hψφ y hy⟩
    rw [this]
    exact hS.inter (hφm hs)
  have hmap : Measure.map ψ (ENNReal.ofReal (R ^ 2) • volume) = volume.restrict S := by
    ext s hs
    rw [Measure.map_apply hψm hs, smul_apply, smul_eq_mul,
      ← lintegral_indicator_one (hψm hs), ← setLIntegral_dilatedCell _ hR,
      ← lintegral_indicator_one hs]
    refine setLIntegral_congr_fun hS fun y hy => ?_
    have h : ofComplex (y / R) ∈ ψ ⁻¹' s ↔ y ∈ s := by rw [mem_preimage, hψφ y hy]
    by_cases hys : y ∈ s
    · rw [indicator_of_mem hys, indicator_of_mem (h.2 hys)]
      rfl
    · rw [indicator_of_notMem hys, indicator_of_notMem (mt h.1 hys)]
  have h1 : eLpNorm F (ENNReal.ofReal p) (ENNReal.ofReal (R ^ 2) • volume) =
      eLpNorm (S.indicator fun y => F (ofComplex (y / R))) (ENNReal.ofReal p) volume := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet, ← hmap,
      hemb.eLpNorm_map_measure]
    congr 1
    funext z
    simp only [Function.comp_apply, hφψ z]
  rw [← h1, eLpNorm_smul_measure_of_ne_zero_of_ne_top (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top, smul_eq_mul]
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hp.le, ← Real.rpow_natCast, ← Real.rpow_mul hR.le, Nat.cast_ofNat,
    div_eq_mul_inv]

/-- The dilated cells `R · (−½, ½]²` exhaust `ℂ` as `R → ∞`. -/
theorem eventually_div_mem_centredCell (y : ℂ) : ∀ᶠ R : ℝ in atTop, y / R ∈ centredCell := by
  filter_upwards [eventually_gt_atTop (2 * ‖y‖)] with R hR
  rw [div_mem_centredCell_iff (lt_of_le_of_lt (by positivity) hR)]
  have h1 := abs_re_le_norm y
  have h2 := abs_im_le_norm y
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    linarith [neg_abs_le y.re, le_abs_self y.re, neg_abs_le y.im, le_abs_self y.im]

end HarmonicAnalysis
