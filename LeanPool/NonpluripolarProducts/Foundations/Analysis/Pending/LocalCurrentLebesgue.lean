/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentRestriction

/-!
# The pointwise density form and the Lebesgue decomposition of a positive current

Let `T` be a positive current of bidimension `(q,q)` on an open set `U ⊆ ℂⁿ`
(`LocalProductCurrents.IsPositive`), with trace measure `σ_T` and coefficient densities `f_γ`.

* `densityForm hT x` — **the pointwise density form** `L_x : Λ_q → ℝ`, a linear functional,
  measurable and bounded in `x`, with `L_x(γ) = f_γ(x)` for `σ_T`-almost every `x`
  (`densityForm_ae`), so that `T(γ)(φ) = ∫ φ L_x(γ) dσ_T` (`apply_eq_integral_densityForm`), and
  **nonnegative on the strongly positive cone for `σ_T`-almost every `x`**
  (`ae_densityForm_nonneg`).  For `q = n - 1` (a `(1,1)`-current) `L_x` is, by duality, the
  positive `(1,1)`-form of densities of `T` at `x`.
* `ofMeasure hT ν` — for a measure `ν ≤ σ_T`, the positive current `γ ↦ L_x(γ) ν`
  (`isPositive_ofMeasure`); additive in `ν`, and equal to `T` for `ν = σ_T`.
* **The Lebesgue decomposition** `T = T_sg + T_ac` (`sgPart_add_acPart`) with respect to Lebesgue
  measure `λ`: `σ_T` is σ-finite, `σ_T = σ_T^sing + (dσ_T/dλ) λ`, and
  `T_ac(γ) = (dσ_T/dλ) L_x(γ) λ` (`acPart_apply`), `T_sg(γ) = L_x(γ) σ_T^sing`.  Both parts are
  positive currents; the coefficients of `T_ac` are locally integrable functions on `U`
  (`locallyIntegrableOn_acDensity`), its density form `(dσ_T/dλ) L_x` is nonnegative on the
  strongly positive cone for `λ`-almost every `x` (`ae_volume_acDensity_nonneg`), `σ_T^sing ⟂ λ`,
  and `T_ac = T` when `σ_T ≪ λ` (`acPart_eq_self_of_absolutelyContinuous`).
* **Locality**: both parts commute with restriction to open subsets (`acPart_restrict`,
  `sgPart_restrict`), through `ofMeasure_restrict`, `acMeasure_restrict`, `sgMeasure_restrict`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal

namespace SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue

open FirstPass StronglyPositiveForms LocalProductCurrents

variable {n : ℕ}

local notation "E" => ComplexModel n

/-- The constant forms `Λ_q` make a finite-dimensional space. -/
instance instFiniteDimensionalFormSpan (q : ℕ) : FiniteDimensional ℝ (formSpan n q) :=
  haveI := ProductTestForms.realForm_finiteDimensional (n := n) (2 * q)
  inferInstance

/-- `Λ_q` is a free module (a vector space; instance search does not find the additive
group of the submodule through `RealForm`). -/
instance instFreeFormSpan (q : ℕ) : Module.Free ℝ (formSpan n q) :=
  @Module.Free.of_divisionRing ℝ (formSpan n q) _ (Submodule.addCommGroup _) _

/-- The additive group structure of `Λ_q`, made directly available to instance search inside
this file. -/
abbrev addCommGroupFormSpan (q : ℕ) : AddCommGroup (formSpan n q) := Submodule.addCommGroup _

attribute [local instance] addCommGroupFormSpan

variable (n) in
/-- The strongly positive cone, as a subset of `Λ_q`. -/
def posCone (q : ℕ) : Set (formSpan n q) := {γ | (γ : RealForm n (2 * q)) ∈ spCone q}

variable (n) in
/-- The basis of `Λ_q` in which the density form is assembled. -/
abbrev formBasis (q : ℕ) := Module.finBasis ℝ (formSpan n q)

variable {U : Opens (ComplexModel n)} {q : ℕ} {T : LocalProductCurrent n U q}

/-! ### The pointwise density form -/

/-- **The pointwise density form** of a positive current: `L_x(γ) = ∑ᵢ γᵢ f_{bᵢ}(x)` in the
basis `b` of `Λ_q`. -/
def densityForm (hT : IsPositive T) (x : E) : formSpan n q →ₗ[ℝ] ℝ :=
  ∑ i, hT.density (formBasis n q i) x • (formBasis n q).coord i

theorem densityForm_apply (hT : IsPositive T) (x : E) (γ : formSpan n q) :
    densityForm hT x γ = ∑ i, (formBasis n q).repr γ i * hT.density (formBasis n q i) x := by
  simp only [densityForm, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem measurable_densityForm (hT : IsPositive T) (γ : formSpan n q) :
    Measurable fun x => densityForm hT x γ := by
  simp_rw [densityForm_apply]
  exact Finset.measurable_sum _ fun i _ => (hT.measurable_density _).const_mul _

/-- The density form is bounded on each constant form. -/
theorem exists_abs_densityForm_le (hT : IsPositive T) (γ : formSpan n q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |densityForm hT x γ| ≤ C := by
  choose C hC0 hC using fun i => hT.exists_abs_density_le (formBasis n q i)
  refine ⟨∑ i, |(formBasis n q).repr γ i| * C i,
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hC0 i), fun x => ?_⟩
  rw [densityForm_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC i x) (abs_nonneg _)

/-- **`L_x(γ) = f_γ(x)` for `σ_T`-almost every `x`.** -/
theorem densityForm_ae (hT : IsPositive T) (γ : formSpan n q) :
    (fun x => densityForm hT x γ) =ᵐ[hT.traceMeasure] hT.density γ := by
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT γ
  obtain ⟨D, -, hD⟩ := hT.exists_abs_density_le γ
  refine hT.ae_eq_of_forall_integral_eq (measurable_densityForm hT γ) (hT.measurable_density γ)
    ⟨C, hC⟩ ⟨D, hD⟩ fun φ => ?_
  have hi : ∀ i, Integrable (fun x => φ x * hT.density (formBasis n q i) x) hT.traceMeasure :=
    fun i => hT.integrable_mul_of_bounded φ.continuous φ.hasCompactSupport φ.tsupport_subset
      (hT.measurable_density _).aestronglyMeasurable
      (by
        obtain ⟨D, -, hD⟩ := hT.exists_abs_density_le (formBasis n q i)
        exact ⟨D, fun x _ => hD x⟩)
  rw [← hT.apply_eq_integral_density]
  simp only [densityForm_apply, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => ((hi i).const_mul ((formBasis n q).repr γ i)).congr
    (Eventually.of_forall fun x => by ring)]
  conv_rhs => rw [← (formBasis n q).sum_repr γ, map_sum, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, _root_.smul_apply, smul_eq_mul, hT.apply_eq_integral_density,
    ← integral_const_mul]
  congr 1
  funext x
  ring

/-- **Coefficients through the density form**: `T(γ)(φ) = ∫ φ L_x(γ) dσ_T`. -/
theorem apply_eq_integral_densityForm (hT : IsPositive T) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    T γ φ = ∫ x, φ x * densityForm hT x γ ∂hT.traceMeasure := by
  rw [hT.apply_eq_integral_density]
  refine integral_congr_ae ?_
  filter_upwards [densityForm_ae hT γ] with x hx
  rw [hx]

/-- The coefficient density of a strongly positive constant form is nonnegative
`σ_T`-almost everywhere. -/
theorem ae_density_nonneg (hT : IsPositive T) {γ : formSpan n q} (hγ : γ ∈ posCone n q) :
    ∀ᵐ x ∂hT.traceMeasure, 0 ≤ hT.density γ x := by
  have := hT.isLocallyFiniteMeasure_traceMeasureOn
  obtain ⟨D, -, hD⟩ := hT.exists_abs_density_le γ
  have hloc : LocallyIntegrable (fun x : U => hT.density γ x) hT.traceMeasureOn := by
    intro x
    obtain ⟨s, hs, hfin⟩ := hT.traceMeasureOn.finiteAt_nhds x
    refine ⟨s, hs, Measure.integrableOn_of_bounded (M := D) hfin.ne
      ((hT.measurable_density γ).comp measurable_subtype_coe).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)⟩
    rw [Real.norm_eq_abs]
    exact hD y
  have h := Pending.ae_nonneg_of_positiveDistribution_integral (hT.positiveDistribution hγ)
    hT.traceMeasureOn ((hT.measurable_density γ).comp measurable_subtype_coe) hloc
    fun φ => by rw [hT.apply_eq_integral_density, hT.integral_traceMeasure_eq]; rfl
  rw [show hT.traceMeasure = hT.traceMeasureOn.map Subtype.val from rfl,
    (IsPositive.measurableEmbedding_val (U := U)).ae_map_iff]
  exact h

/-- Nonnegativity on the strongly positive cone, almost everywhere for all forms at once (a
countable dense subset of the cone and continuity of linear forms). -/
theorem ae_forall_posCone_nonneg {ν : Measure (ComplexModel n)} {g : (ComplexModel n)
    → formSpan n q →ₗ[ℝ] ℝ}
    (hgp : ∀ γ ∈ posCone n q, ∀ᵐ x ∂ν, 0 ≤ g x γ) :
    ∀ᵐ x ∂ν, ∀ γ ∈ posCone n q, 0 ≤ g x γ := by
  let : SecondCountableTopology (formSpan n q) :=
    (formBasis n q).equivFunL.toHomeomorph.secondCountableTopology
  let : SeparableSpace (formSpan n q) := SecondCountableTopology.to_separableSpace
  obtain ⟨D, hDC, hDc, hCD⟩ :=
    (IsSeparable.of_separableSpace (posCone n q)).exists_countable_dense_subset
  have _ := hDc.to_subtype
  have h : ∀ᵐ x ∂ν, ∀ γ : D, 0 ≤ g x γ := by
    rw [ae_all_iff]
    exact fun γ => hgp γ (hDC γ.2)
  filter_upwards [h] with x hx γ hγ
  have hcont : Continuous (g x) := (g x).continuous_of_finiteDimensional
  have hclosed : IsClosed {γ : formSpan n q | 0 ≤ g x γ} := isClosed_le continuous_const hcont
  exact closure_minimal (fun γ hγD => hx ⟨γ, hγD⟩) hclosed (hCD hγ)

/-- **The density form is nonnegative on the strongly positive cone**, for `σ_T`-almost every
point (a countable dense subset of the cone, then continuity of `L_x`). -/
theorem ae_densityForm_nonneg (hT : IsPositive T) :
    ∀ᵐ x ∂hT.traceMeasure, ∀ γ ∈ posCone n q, 0 ≤ densityForm hT x γ := by
  refine ae_forall_posCone_nonneg fun γ hγ => ?_
  filter_upwards [densityForm_ae hT γ, ae_density_nonneg hT hγ] with x h1 h2
  rwa [h1]

/-! ### Parts of a positive current carried by a measure below its trace measure -/

theorem locallyIntegrableOn_densityForm (hT : IsPositive T) {ν : Measure E}
    (hν : ν ≤ hT.traceMeasure) (γ : formSpan n q) :
    LocallyIntegrableOn (fun x => densityForm hT x γ) U ν := by
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT γ
  intro x hx
  obtain ⟨K, hK, hKn, hKU⟩ := exists_compact_subset U.isOpen hx
  refine ⟨K, nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hKn), ?_⟩
  exact Measure.integrableOn_of_bounded (M := C)
    ((Measure.le_iff'.mp hν K).trans_lt (hT.traceMeasure_lt_top hK hKU)).ne
    (measurable_densityForm hT γ).aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)

theorem integrable_densityForm (hT : IsPositive T) {ν : Measure E}
    (hν : ν ≤ hT.traceMeasure) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    Integrable (fun x => φ x * densityForm hT x γ) ν := by
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT γ
  exact MeasureLocality.integrable_mul_of_ae_bounded_on_tsupport φ.continuous
    φ.hasCompactSupport ((Measure.le_iff'.mp hν _).trans_lt
      (hT.traceMeasure_lt_top φ.hasCompactSupport φ.tsupport_subset))
    (measurable_densityForm hT γ).aestronglyMeasurable (ae_restrict_of_ae (Eventually.of_forall hC))

/-- **The part of a positive current carried by a measure** `ν ≤ σ_T`: `γ ↦ L_x(γ) ν`. -/
def ofMeasure (hT : IsPositive T) (ν : Measure E) (hν : ν ≤ hT.traceMeasure) :
    LocalProductCurrent n U q where
  toFun γ := regularDistribution ν (fun x => densityForm hT x γ)
    (locallyIntegrableOn_densityForm hT hν γ)
  map_add' γ γ' := by
    ext φ
    rw [_root_.add_apply, regularDistribution_apply, regularDistribution_apply,
      regularDistribution_apply, ← integral_add (integrable_densityForm hT hν γ φ)
        (integrable_densityForm hT hν γ' φ)]
    simp only [map_add, mul_add]
  map_smul' c γ := by
    ext φ
    rw [RingHom.id_apply, _root_.smul_apply, regularDistribution_apply, regularDistribution_apply,
      smul_eq_mul, ← integral_const_mul]
    simp only [map_smul, smul_eq_mul]
    congr 1
    funext x
    ring

theorem ofMeasure_apply (hT : IsPositive T) {ν : Measure E} (hν : ν ≤ hT.traceMeasure)
    (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    ofMeasure hT ν hν γ φ = ∫ x, φ x * densityForm hT x γ ∂ν :=
  regularDistribution_apply _ _ (locallyIntegrableOn_densityForm hT hν γ) φ

/-- **The part of a positive current carried by `ν ≤ σ_T` is positive.** -/
theorem isPositive_ofMeasure (hT : IsPositive T) {ν : Measure E} (hν : ν ≤ hT.traceMeasure) :
    IsPositive (ofMeasure hT ν hν) := by
  intro ι _ γ φ hγ
  simp only [ofMeasure_apply]
  rw [← integral_finsetSum _ fun i _ => integrable_densityForm hT hν (γ i) (φ i)]
  refine integral_nonneg_of_ae ?_
  have hac : ν ≪ hT.traceMeasure := Measure.absolutelyContinuous_of_le hν
  filter_upwards [hac.ae_le (ae_densityForm_nonneg hT)] with x hx
  have hmem : (∑ i, φ i x • γ i) ∈ posCone n q := by
    change ((∑ i, φ i x • γ i : formSpan n q) : RealForm n (2 * q)) ∈ spCone q
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hγ x
  have h := hx _ hmem
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simpa only [Pi.zero_apply] using h

/-- The whole trace measure gives back the current. -/
theorem ofMeasure_traceMeasure (hT : IsPositive T) : ofMeasure hT hT.traceMeasure le_rfl = T := by
  ext γ φ
  rw [ofMeasure_apply, apply_eq_integral_densityForm hT]

theorem ofMeasure_add (hT : IsPositive T) {ν₁ ν₂ : Measure E} (h₁ : ν₁ ≤ hT.traceMeasure)
    (h₂ : ν₂ ≤ hT.traceMeasure) (h : ν₁ + ν₂ ≤ hT.traceMeasure) :
    ofMeasure hT (ν₁ + ν₂) h = ofMeasure hT ν₁ h₁ + ofMeasure hT ν₂ h₂ := by
  ext γ φ
  rw [LinearMap.add_apply, _root_.add_apply, ofMeasure_apply, ofMeasure_apply, ofMeasure_apply,
    integral_add_measure (integrable_densityForm hT h₁ γ φ) (integrable_densityForm hT h₂ γ φ)]

/-! ### The Lebesgue decomposition -/

/-- The trace measure of a positive current is σ-finite. -/
instance sigmaFinite_traceMeasure (hT : IsPositive T) : SigmaFinite hT.traceMeasure := by
  have := hT.isLocallyFiniteMeasure_traceMeasureOn
  have : SigmaFinite hT.traceMeasureOn := sigmaFinite_of_locallyFinite
  exact (IsPositive.measurableEmbedding_val (U := U)).sigmaFinite_map

/-- The density `dσ_T/dλ` of the absolutely continuous part of the trace measure. -/
def acWeight (hT : IsPositive T) (x : E) : ℝ := (hT.traceMeasure.rnDeriv volume x).toReal

/-- The absolutely continuous part `(dσ_T/dλ) λ` of the trace measure. -/
def acMeasure (hT : IsPositive T) : Measure E := volume.withDensity (hT.traceMeasure.rnDeriv
    volume)

/-- The singular part of the trace measure with respect to Lebesgue measure. -/
def sgMeasure (hT : IsPositive T) : Measure E := hT.traceMeasure.singularPart volume

theorem acMeasure_le (hT : IsPositive T) : acMeasure hT ≤ hT.traceMeasure :=
  Measure.withDensity_rnDeriv_le _ _

theorem sgMeasure_le (hT : IsPositive T) : sgMeasure hT ≤ hT.traceMeasure :=
  Measure.singularPart_le _ _

theorem sgMeasure_add_acMeasure (hT : IsPositive T) :
    sgMeasure hT + acMeasure hT = hT.traceMeasure :=
  (Measure.haveLebesgueDecomposition_add _ _).symm

theorem acMeasure_absolutelyContinuous (hT : IsPositive T) : acMeasure hT ≪ volume :=
  withDensity_absolutelyContinuous _ _

theorem sgMeasure_mutuallySingular (hT : IsPositive T) : sgMeasure hT ⟂ₘ volume :=
  Measure.mutuallySingular_singularPart _ _

/-- **The absolutely continuous part** `T_ac` of a positive current. -/
def acPart (hT : IsPositive T) : LocalProductCurrent n U q :=
  ofMeasure hT (acMeasure hT) (acMeasure_le hT)

/-- **The singular part** `T_sg` of a positive current. -/
def sgPart (hT : IsPositive T) : LocalProductCurrent n U q :=
  ofMeasure hT (sgMeasure hT) (sgMeasure_le hT)

theorem isPositive_acPart (hT : IsPositive T) : IsPositive (acPart hT) :=
  isPositive_ofMeasure hT _

theorem isPositive_sgPart (hT : IsPositive T) : IsPositive (sgPart hT) :=
  isPositive_ofMeasure hT _

/-- **The Lebesgue decomposition** `T = T_sg + T_ac`. -/
theorem sgPart_add_acPart (hT : IsPositive T) : sgPart hT + acPart hT = T := by
  ext γ φ
  rw [LinearMap.add_apply, _root_.add_apply, sgPart, acPart, ofMeasure_apply, ofMeasure_apply,
    ← integral_add_measure (integrable_densityForm hT (sgMeasure_le hT) γ φ)
      (integrable_densityForm hT (acMeasure_le hT) γ φ), sgMeasure_add_acMeasure,
    apply_eq_integral_densityForm hT]

/-- **The coefficients of `T_ac` are functions**: `T_ac(γ)(φ) = ∫ φ (dσ_T/dλ) L_x(γ) dλ`. -/
theorem acPart_apply (hT : IsPositive T) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    acPart hT γ φ = ∫ x, φ x * (acWeight hT x * densityForm hT x γ) := by
  rw [acPart, ofMeasure_apply, acMeasure,
    integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)]
  congr 1
  funext x
  rw [smul_eq_mul, acWeight]
  ring

theorem acWeight_nonneg (hT : IsPositive T) (x : E) : 0 ≤ acWeight hT x :=
  ENNReal.toReal_nonneg

theorem measurable_acWeight (hT : IsPositive T) : Measurable (acWeight hT) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- The coefficient densities `(dσ_T/dλ) L_x(γ)` of `T_ac` are locally integrable on `U`. -/
theorem locallyIntegrableOn_acDensity (hT : IsPositive T) (γ : formSpan n q) :
    LocallyIntegrableOn (fun x => acWeight hT x * densityForm hT x γ) U volume := by
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT γ
  intro x hx
  obtain ⟨K, hK, hKn, hKU⟩ := exists_compact_subset U.isOpen hx
  refine ⟨K, nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hKn), ?_⟩
  have hw : IntegrableOn (acWeight hT) K volume :=
    Measure.integrableOn_toReal_rnDeriv (hT.traceMeasure_lt_top hK hKU).ne
  have hb : IntegrableOn (fun x => C * acWeight hT x) K volume := hw.const_mul C
  refine hb.mono' ((measurable_acWeight hT).mul
    (measurable_densityForm hT γ)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (acWeight_nonneg hT y), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC y) (acWeight_nonneg hT y)

/-- **The density form of `T_ac` is nonnegative on the strongly positive cone for Lebesgue-almost
every point.** -/
theorem ae_volume_acDensity_nonneg (hT : IsPositive T) :
    ∀ᵐ x ∂(volume : Measure E), ∀ γ ∈ posCone n q, 0 ≤ acWeight hT x * densityForm hT x γ := by
  set N : Set E := {x | ¬ ∀ γ ∈ posCone n q, 0 ≤ densityForm hT x γ} with hN
  have hσN : hT.traceMeasure N = 0 := by
    have := ae_densityForm_nonneg hT
    rwa [ae_iff] at this
  have hacN : acMeasure hT N = 0 :=
    le_antisymm ((Measure.le_iff'.mp (acMeasure_le hT) N).trans hσN.le) zero_le
  rw [acMeasure, withDensity_apply_eq_zero' (Measure.measurable_rnDeriv _ _).aemeasurable] at hacN
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hacN] with x hx γ hγ
  by_cases hxN : x ∈ N
  · have h0 : hT.traceMeasure.rnDeriv volume x = 0 := by
      by_contra hne
      exact hx ⟨hne, hxN⟩
    rw [acWeight, h0, ENNReal.toReal_zero, zero_mul]
  · have hpos : ∀ γ ∈ posCone n q, 0 ≤ densityForm hT x γ := by
      by_contra h
      exact hxN h
    exact mul_nonneg (acWeight_nonneg hT x) (hpos γ hγ)

/-- **A positive current whose trace measure is absolutely continuous is its own absolutely
continuous part.** -/
theorem acPart_eq_self_of_absolutelyContinuous (hT : IsPositive T)
    (hac : hT.traceMeasure ≪ volume) : acPart hT = T := by
  have hsg : sgPart hT = 0 := by
    ext γ φ
    rw [sgPart, ofMeasure_apply, sgMeasure, Measure.singularPart_eq_zero_of_ac hac,
      integral_zero_measure]
    rfl
  conv_rhs => rw [← sgPart_add_acPart hT, hsg, zero_add]

/-! ### Compatibility with restriction to open subsets -/

/-- If two families of linear functionals on `Λ_q` agree almost everywhere on each
    strongly positive form, they
agree almost everywhere on all of `Λ_q` (every form is a difference of two strongly positive ones;
    use a basis). -/
theorem ae_forall_eq_of_posCone {μ : Measure (ComplexModel n)} {P : ComplexModel n → Prop}
    (L₁ L₂ : ComplexModel n → formSpan n q →ₗ[ℝ] ℝ)
    (h : ∀ γ ∈ posCone n q, ∀ᵐ x ∂μ, P x → L₁ x γ = L₂ x γ) :
    ∀ᵐ x ∂μ, P x → ∀ γ, L₁ x γ = L₂ x γ := by
  have hω : kahlerPower n q ∈ posCone n q := formPower_mem_spCone isSemipositiveOneOne_kahlerForm q
  have key : ∀ i, ∃ c₁ c₂ : formSpan n q, c₁ ∈ posCone n q ∧ c₂ ∈ posCone n q ∧ formBasis n q i =
    c₁ - c₂ := by
    intro i
    obtain ⟨C, hC, -, h2⟩ := exists_orderUnit (formBasis n q i).2
    exact ⟨C • kahlerPower n q + formBasis n q i, C • kahlerPower n q, h2, smul_mem_spCone hω hC,
      (add_sub_cancel_left _ _).symm⟩
  choose c₁ c₂ hc₁ hc₂ hc using key
  have hall := ae_all_iff.mpr fun i => (h _ (hc₁ i)).and (h _ (hc₂ i))
  filter_upwards [hall] with x hx hPx γ
  have hL : L₁ x = L₂ x := by
    refine (formBasis n q).ext fun i => ?_
    rw [hc i, map_sub, map_sub, (hx i).1 hPx, (hx i).2 hPx]
  rw [hL]

section Restrict

open LocalBedfordTaylorLocality

variable {V : Opens (ComplexModel n)}

/-- The density form of `T|_V` is that of `T`, almost everywhere for the trace measure of `T|_V`.
-/
theorem densityForm_restrict_ae (hT : IsPositive T) (hVU : V ≤ U) (γ : formSpan n q) :
    (fun x => densityForm (isPositive_restrict hT hVU) x γ)
      =ᵐ[(isPositive_restrict hT hVU).traceMeasure] fun x => densityForm hT x γ := by
  have hle : (isPositive_restrict hT hVU).traceMeasure ≪ hT.traceMeasure := by
    rw [traceMeasure_restrict hT hVU]
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  filter_upwards [densityForm_ae (isPositive_restrict hT hVU) γ, density_restrict_ae hT hVU γ,
    hle.ae_le (densityForm_ae hT γ)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- Almost everywhere for the trace measure of `T|_V`, the density forms of `T|_V` and `T` agree
    on all of `Λ_q`. -/
theorem ae_densityForm_restrict_eq (hT : IsPositive T) (hVU : V ≤ U) :
    ∀ᵐ y ∂(isPositive_restrict hT hVU).traceMeasure,
      densityForm (isPositive_restrict hT hVU) y = densityForm hT y := by
  have hall := ae_all_iff.mpr fun i => densityForm_restrict_ae hT hVU (formBasis n q i)
  filter_upwards [hall] with y hy
  exact (formBasis n q).ext fun i => hy i

theorem ofMeasure_congr (hT : IsPositive T) {ν ν' : Measure E} (hν : ν ≤ hT.traceMeasure)
    (hν' : ν' ≤ hT.traceMeasure) (h : ν = ν') : ofMeasure hT ν hν = ofMeasure hT ν' hν' := by
  subst h
  rfl

/-- **Restriction of the part carried by `ν`**: `(L ν)|_V = L' (ν|_V)`. -/
theorem ofMeasure_restrict (hT : IsPositive T) (hVU : V ≤ U) {ν : Measure E}
    (hν : ν ≤ hT.traceMeasure) (hν' : ν.restrict V ≤ (isPositive_restrict hT hVU).traceMeasure) :
    LocalBedfordTaylorLocality.restrict hVU (ofMeasure hT ν hν) =
      ofMeasure (isPositive_restrict hT hVU) (ν.restrict V) hν' := by
  ext γ φ
  rw [LocalBedfordTaylorLocality.restrict_apply, ofMeasure_apply, ofMeasure_apply]
  have hf : (extTest hVU φ : E → ℝ) = (φ : E → ℝ) := funext (extTest_apply hVU φ)
  rw [hf, ← integral_restrict_mul φ ν]
  refine integral_congr_ae ?_
  filter_upwards [(Measure.absolutelyContinuous_of_le hν').ae_le
    (densityForm_restrict_ae hT hVU γ)] with x hx
  rw [hx]

theorem acMeasure_restrict (hT : IsPositive T) (hVU : V ≤ U) :
    acMeasure (isPositive_restrict hT hVU) = (acMeasure hT).restrict V := by
  rw [acMeasure, acMeasure, restrict_withDensity V.isOpen.measurableSet,
    ← withDensity_indicator V.isOpen.measurableSet]
  refine withDensity_congr_ae ?_
  rw [traceMeasure_restrict hT hVU]
  exact Measure.rnDeriv_restrict _ _ V.isOpen.measurableSet

theorem sgMeasure_restrict (hT : IsPositive T) (hVU : V ≤ U) :
    sgMeasure (isPositive_restrict hT hVU) = (sgMeasure hT).restrict V := by
  have hV : MeasurableSet (V : Set E) := V.isOpen.measurableSet
  rw [sgMeasure, traceMeasure_restrict hT hVU]
  symm
  refine Measure.eq_singularPart ((Measure.measurable_rnDeriv hT.traceMeasure volume).indicator hV)
    ((sgMeasure_mutuallySingular hT).restrict _) ?_
  rw [withDensity_indicator hV, ← restrict_withDensity hV, ← Measure.restrict_add]
  exact congrArg (fun μ : Measure E => μ.restrict (V : Set E)) (sgMeasure_add_acMeasure hT).symm

/-- **The absolutely continuous part commutes with restriction**: `(T_ac)|_V = (T|_V)_ac`. -/
theorem acPart_restrict (hT : IsPositive T) (hVU : V ≤ U) :
    LocalBedfordTaylorLocality.restrict hVU (acPart hT) = acPart (isPositive_restrict hT hVU) := by
  rw [acPart, acPart, ofMeasure_restrict hT hVU (acMeasure_le hT)
    (by rw [← acMeasure_restrict hT hVU]; exact acMeasure_le _)]
  exact ofMeasure_congr _ _ _ (acMeasure_restrict hT hVU).symm

/-- **The singular part commutes with restriction**: `(T_sg)|_V = (T|_V)_sg`. -/
theorem sgPart_restrict (hT : IsPositive T) (hVU : V ≤ U) :
    LocalBedfordTaylorLocality.restrict hVU (sgPart hT) = sgPart (isPositive_restrict hT hVU) := by
  rw [sgPart, sgPart, ofMeasure_restrict hT hVU (sgMeasure_le hT)
    (by rw [← sgMeasure_restrict hT hVU]; exact sgMeasure_le _)]
  exact ofMeasure_congr _ _ _ (sgMeasure_restrict hT hVU).symm

end Restrict

end SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
