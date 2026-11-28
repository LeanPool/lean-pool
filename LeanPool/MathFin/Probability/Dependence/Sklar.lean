/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Dependence.Copula

/-!
# Sklar's theorem

**Sklar's theorem** (McNeil–Frey–Embrechts, *Quantitative Risk Management*, 2015, Theorem 7.3) says
that a joint distribution function is its copula evaluated at its marginal distribution functions,
`F(x) = C(F₁(x₁), …, F_d(x_d))`, and that the copula is unique when the margins are continuous.
The converse builds a joint law from any copula and any margins.

Both directions are the one-dimensional transforms of `Probability/Laws/Quantile.lean`, applied
coordinate by coordinate.

* **Existence (continuous margins).** The *copula of a random vector* `X` is the joint law of its
  probability-integral transforms `Uᵢ = Fᵢ(Xᵢ)` (`copulaOf`). Each `Uᵢ` is uniform
  (`hasLaw_cdf`), so this law is a copula (`isCopula_copulaOf`). The events `{Xᵢ ≤ xᵢ}` and
  `{Fᵢ(Xᵢ) ≤ Fᵢ(xᵢ)}` are nested and have the same probability `Fᵢ(xᵢ)`, so they agree almost
  surely. That gives the Sklar identity `P(X ≤ x) = C(F(x))` (`measureReal_le_eq_copulaOf`).
* **Converse (arbitrary margins).** Under any copula `C`, the vector of quantiles
  `(quantile μᵢ (vᵢ))ᵢ` has margins `μᵢ` (the quantile transform) and joint distribution function
  `x ↦ C(F₁(x₁), …, F_d(x_d))` (`measureReal_quantile_le_eq`). This needs no continuity, only the
  Galois connection `quantile μᵢ p ≤ x ↔ p ≤ Fᵢ(x)`.
* **Uniqueness (continuous margins).** A copula satisfying the Sklar identity is `copulaOf X`
  (`eq_copulaOf_of_measureReal_le`). By the converse its quantile vector has the joint distribution
  function of `X`, hence the law of `X` (`ext_of_measure_Iic_pi`). Pushing forward along the
  margins returns the copula, because `Fᵢ ∘ quantile μᵢ` is the identity on `(0, 1)` when `Fᵢ` is
  continuous.
* **Invariance.** Strictly increasing transformations of the coordinates leave the copula
  unchanged (`copulaOf_comp_strictMono`, MFE Proposition 7.7). The probability-integral transform
  of `Tᵢ(Xᵢ)` at `Tᵢ(y)` is that of `Xᵢ` at `y`.

The existence and uniqueness halves assume continuous margins. For general margins a copula still
exists, but the construction needs the randomized distributional transform, and uniqueness holds
only on the product of the ranges of the `Fᵢ`. Neither is formalized here.

## Main definitions

* `copulaOf`: the copula of a random vector `X` under `P`, the joint law of its
  probability-integral transforms `Uᵢ = Fᵢ(Xᵢ)`.

## Main results

* `isCopula_copulaOf`, `measureReal_le_eq_copulaOf`: Sklar's theorem, existence (continuous
  margins).
* `eq_copulaOf_of_measureReal_le`: Sklar's theorem, uniqueness (continuous margins).
* `hasLaw_quantile_coord`, `measureReal_quantile_le_eq`: the converse of Sklar's theorem.
* `copulaOf_comp_strictMono`: the copula is invariant under strictly increasing transformations.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Proposition 7.7; Theorem 7.3
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 7.2
* [Sklar (1959)][Sklar1959]

## Tags

Sklar's theorem, copula, marginal distributions, probability integral transform,
dependence structure, copula invariance, MSC 62H05, MSC 60E05, MSC 91G70
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {ι : Type*} [Fintype ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : Ω → ι → ℝ}

/-- The **copula of a random vector** `X`: the joint law of its probability-integral transforms
`Uᵢ = Fᵢ(Xᵢ)`, where `Fᵢ` is the CDF of the `i`-th coordinate. For continuous margins it is the
unique copula of Sklar's theorem. -/
noncomputable def copulaOf (X : Ω → ι → ℝ) (P : Measure Ω) : Measure (ι → ℝ) :=
  P.map fun ω i ↦ cdf (P.map fun ω ↦ X ω i) (X ω i)

omit [Fintype ι] in
/-- The probability-integral transform of a random vector is measurable. -/
lemma aemeasurable_cdf_coord [Finite ι] (hX : AEMeasurable X P) :
    AEMeasurable (fun ω i ↦ cdf (P.map fun ω ↦ X ω i) (X ω i)) P :=
  aemeasurable_pi_iff.2 fun i ↦ (monotone_cdf _).measurable.comp_aemeasurable (hX.eval i)

variable [IsProbabilityMeasure P]

omit [Fintype ι] in
/-- **Sklar's theorem, existence of the copula** (continuous margins): the joint law of the
probability-integral transforms of `X` is a copula. -/
theorem isCopula_copulaOf [Finite ι] (hX : AEMeasurable X P)
    (hF : ∀ i, Continuous (cdf (P.map fun ω ↦ X ω i))) : IsCopula (copulaOf X P) where
  isProbabilityMeasure :=
    inferInstanceAs (IsProbabilityMeasure
      (P.map fun ω i ↦ cdf (P.map fun ω ↦ X ω i) (X ω i)))
  map_eval i := by
    rw [copulaOf, AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply i).aemeasurable
      (aemeasurable_cdf_coord hX)]
    exact (hasLaw_cdf ⟨hX.eval i, rfl⟩ (hF i)).map_eq

/-- For a real random variable `Y` with continuous CDF `F`, the events `{Y ≤ y}` and
`{F(Y) ≤ F(y)}` agree almost surely. They are nested and both have probability `F(y)`. -/
lemma ae_eq_le_iff_cdf_le {Y : Ω → ℝ} (hY : AEMeasurable Y P)
    (hF : Continuous (cdf (P.map Y))) (y : ℝ) :
    {ω | Y ω ≤ y} =ᵐ[P] {ω | cdf (P.map Y) (Y ω) ≤ cdf (P.map Y) y} := by
  have hU := hasLaw_cdf (μ := P.map Y) ⟨hY, rfl⟩ hF
  refine ae_eq_of_subset_of_measure_ge (fun ω hω ↦ monotone_cdf _ hω)
    (le_of_eq ?_) (hY.nullMeasurable measurableSet_Iic) (measure_ne_top _ _)
  rw [show {ω | cdf (P.map Y) (Y ω) ≤ cdf (P.map Y) y} =
      (fun ω ↦ cdf (P.map Y) (Y ω)) ⁻¹' Iic (cdf (P.map Y) y) from rfl,
    ← Measure.map_apply_of_aemeasurable hU.aemeasurable measurableSet_Iic, hU.map_eq,
    ← ofReal_measureReal, uniformIoo_real_Iic (cdf_nonneg _ y) (cdf_le_one _ y), ofReal_cdf,
    Measure.map_apply_of_aemeasurable hY measurableSet_Iic]
  rfl

omit [Fintype ι] in
/-- **Sklar's theorem, the identity** (continuous margins): the joint distribution function of `X`
is its copula evaluated at the marginal distribution functions,
`P(X ≤ x) = C(F₁(x₁), …, F_d(x_d))`. -/
theorem measureReal_le_eq_copulaOf [Finite ι] (hX : AEMeasurable X P)
    (hF : ∀ i, Continuous (cdf (P.map fun ω ↦ X ω i))) (x : ι → ℝ) :
    P.real {ω | X ω ≤ x} =
      (copulaOf X P).real (Iic fun i ↦ cdf (P.map fun ω ↦ X ω i) (x i)) := by
  rw [copulaOf, map_measureReal_apply_of_aemeasurable (aemeasurable_cdf_coord hX)
    measurableSet_Iic]
  refine measureReal_congr ?_
  filter_upwards [ae_all_iff.2 fun i ↦ ae_eq_le_iff_cdf_le (hX.eval i) (hF i) (x i)] with ω hω
  simp only [Pi.le_def]
  exact forall_congr' hω

/-! ### The converse: a joint law from a copula and margins -/

section Converse

variable {C : Measure (ι → ℝ)} (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

omit [Fintype ι] in
/-- **The converse of Sklar's theorem, margins**: under a copula `C`, the quantile transform of the
`i`-th coordinate has law `μᵢ`. -/
theorem hasLaw_quantile_coord (hC : IsCopula C) (i : ι) :
    HasLaw (fun v : ι → ℝ ↦ quantile (μ i) (v i)) (μ i) C :=
  (hasLaw_quantile (μ i)).comp (hC.hasLaw_eval i)

omit [Fintype ι] in
/-- The vector of coordinatewise quantile transforms is measurable under a copula. -/
lemma aemeasurable_quantile_coord [Finite ι] (hC : IsCopula C) :
    AEMeasurable (fun v : ι → ℝ ↦ fun i ↦ quantile (μ i) (v i)) C :=
  aemeasurable_pi_iff.2 fun i ↦ (hasLaw_quantile_coord μ hC i).aemeasurable

omit [∀ i, IsProbabilityMeasure (μ i)] [Fintype ι] in
/-- **The converse of Sklar's theorem, joint law**: under a copula `C`, the vector of quantiles
`(quantile μᵢ (vᵢ))ᵢ` has joint distribution function `x ↦ C(F₁(x₁), …, F_d(x_d))`. No continuity
of the margins is needed. -/
theorem measureReal_quantile_le_eq [Finite ι] (hC : IsCopula C) (x : ι → ℝ) :
    C.real {v | (fun i ↦ quantile (μ i) (v i)) ≤ x} = C.real (Iic fun i ↦ cdf (μ i) (x i)) := by
  refine measureReal_congr ?_
  filter_upwards [hC.ae_mem_Ioo] with v hv
  simp only [Pi.le_def]
  exact forall_congr' fun i ↦ quantile_le_iff (hv i)

end Converse

/-! ### Uniqueness -/

omit [Fintype ι] in
/-- **Sklar's theorem, uniqueness** (continuous margins): a copula whose value at the marginal
distribution functions is the joint distribution function of `X` is the copula of `X`. -/
theorem eq_copulaOf_of_measureReal_le [Finite ι] (hX : AEMeasurable X P)
    (hF : ∀ i, Continuous (cdf (P.map fun ω ↦ X ω i))) {C : Measure (ι → ℝ)} (hC : IsCopula C)
    (hCX : ∀ x, P.real {ω | X ω ≤ x} =
      C.real (Iic fun i ↦ cdf (P.map fun ω ↦ X ω i) (x i))) :
    C = copulaOf X P := by
  set μ : ι → Measure ℝ := fun i ↦ P.map fun ω ↦ X ω i
  have : ∀ i, IsProbabilityMeasure (μ i) := fun _ ↦ inferInstance
  have := hC.isProbabilityMeasure
  set q : (ι → ℝ) → ι → ℝ := fun v i ↦ quantile (μ i) (v i)
  set F : (ι → ℝ) → ι → ℝ := fun y i ↦ cdf (μ i) (y i)
  have hq : AEMeasurable q C := aemeasurable_quantile_coord μ hC
  have hFmeas : Measurable F := .of_eval fun i ↦
    (monotone_cdf (μ i)).measurable.comp (measurable_pi_apply i)
  -- the quantile vector of `C` has the law of `X`
  have hlaw : C.map q = P.map X := by
    refine ext_of_measure_Iic_pi fun x ↦ ?_
    rw [Measure.map_apply_of_aemeasurable hq measurableSet_Iic,
      Measure.map_apply_of_aemeasurable hX measurableSet_Iic, ← ofReal_measureReal,
      ← ofReal_measureReal]
    congr 1
    exact (measureReal_quantile_le_eq μ hC x).trans (hCX x).symm
  -- pushing the law of `X` forward along the margins returns `C`
  have hFq : (fun v ↦ F (q v)) =ᵐ[C] id := by
    filter_upwards [hC.ae_mem_Ioo] with v hv
    exact funext fun i ↦ cdf_quantile (hF i) (hv i)
  calc C = C.map (fun v ↦ F (q v)) := by rw [Measure.map_congr hFq, Measure.map_id]
    _ = (C.map q).map F := (AEMeasurable.map_map_of_aemeasurable hFmeas.aemeasurable hq).symm
    _ = (P.map X).map F := by rw [hlaw]
    _ = copulaOf X P := AEMeasurable.map_map_of_aemeasurable hFmeas.aemeasurable hX

/-! ### Invariance under increasing transformations -/

omit [Fintype ι] in
/-- **The copula is invariant under strictly increasing transformations of the margins**
(McNeil–Frey–Embrechts, Proposition 7.7): transforming each coordinate by a strictly increasing
map leaves the copula of the vector unchanged. The probability-integral transform of `Tᵢ(Xᵢ)` at
`Tᵢ(y)` equals that of `Xᵢ` at `y`. -/
theorem copulaOf_comp_strictMono (hX : AEMeasurable X P)
    {T : ι → ℝ → ℝ} (hT : ∀ i, StrictMono (T i)) :
    copulaOf (fun ω i ↦ T i (X ω i)) P = copulaOf X P := by
  have hcdf (i : ι) (y : ℝ) :
      cdf (P.map fun ω ↦ T i (X ω i)) (T i y) = cdf (P.map fun ω ↦ X ω i) y := by
    have hTi : AEMeasurable (fun ω ↦ T i (X ω i)) P :=
      (hT i).monotone.measurable.comp_aemeasurable (hX.eval i)
    rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply_of_aemeasurable hTi measurableSet_Iic,
      map_measureReal_apply_of_aemeasurable (hX.eval i) measurableSet_Iic]
    congr 1
    ext ω
    exact (hT i).le_iff_le
  simp only [copulaOf, hcdf]

end MathFin
