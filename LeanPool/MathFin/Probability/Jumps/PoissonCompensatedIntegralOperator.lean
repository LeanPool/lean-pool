/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.PoissonCompensatedSimpleIntegrand
public import LeanPool.MathFin.Probability.Analysis.ExtendOfNormIsometry
public import LeanPool.MathFin.Probability.Analysis.LpMulIsometry
public import LeanPool.MathFin.Probability.Jumps.PoissonCompensatedBilinear

/-!
# The compensated-Poisson integral operator on marked simple integrands

The two linear maps out of the marked simple-integrand module `levySimpleModule`, mirroring the
continuous `ItoIntegralL2.itoAssembly` / `simpleAssembly`:

* `intAssembly : levySimpleModule N →ₗ[ℝ] Lp ℝ 2 P` — the elementary compensated integral
  `∑_b φ_b · Ñ(box b)`, viewed in `L²(P)`;
* `emb : levySimpleModule N →ₗ[ℝ] Lp ℝ 2 (P.prod (referenceIntensity ν))` — the integrand
  `∑_b φ_b · 𝟙_{box b}`, viewed in `L²(dP ⊗ dν̂)` (the sibling module).

The `L²` isometry `‖intAssembly V‖ = ‖emb V‖`, obtained by summing the overlapping-box bilinear
pairing `integral_bilinear_pairing`, and the `extendOfNorm` CLM are built on these.

## Provenance

Mirrors the continuous `ItoIntegralL2` assembly; the compensated-integral content is our own.

## Main definitions

* `intSum`, `intSumLp`: the elementary compensated integral `∑_b φ_b · Ñ(box b)` of a marked
  simple integrand `V`, as a function and as a class in `L²(P)`.
* `intAssembly`: the elementary compensated integral as a linear map
  `levySimpleModule N →ₗ[ℝ] L²(P)`.
* `embFun`, `embLp`: the integrand `∑_b φ_b · 𝟙_{box b}`, as a function on `Ω × (ℝ × E)` and as a
  class in `L²(P ⊗ ν̂)`.
* `emb`: the integrand embedding as a linear map `levySimpleModule N →ₗ[ℝ] L²(P ⊗ ν̂)`.
* `levyClosure`: the `L²(P ⊗ ν̂)` closure of the range of `emb`.
* `embCorestrict`: `emb` corestricted to `levyClosure`.
* `itoLevyIntegralL2`: the continuous linear extension of the elementary integral to
  `levyClosure N →L[ℝ] L²(P)`.

## Main results

* `assembly_isometry`: `‖intAssembly N V‖ = ‖emb N V‖` for every marked simple integrand `V`.
* `embCorestrict_denseRange`: the marked simple integrands are dense in `levyClosure N`.
* `itoLevyIntegralL2_norm`: `‖itoLevyIntegralL2 N H‖ = ‖H‖` for every `H` in `levyClosure N`.
* `intSum_sq_integral`, `embFun_sq_integral`: the squared norms of `intSum` and `embFun` expand
  as double sums over the box family.

## References

* [Applebaum (2009)][Applebaum2009], Thm 4.2.3
* [*cgarryZA/LevyStochCalc*][LevyStochCalc], cited axiom #6

## Tags

compensated Poisson integral, marked simple integrands, elementary integral,
Itô–Lévy integral operator, Lévy stochastic integral, MSC 60G51, MSC 60H05, MSC 60G55
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- A marked simple integrand's coefficient is in `L²(P)`: it is bounded (hence `L^∞`) and
measurable, so on the probability space it is `L²`. -/
lemma IsLevySimple.memLp_coe {N : PoissonRandomMeasure P ν} {V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)}
    (hV : IsLevySimple N V) (b : ℝ × ℝ × Set E) : MemLp (V b) 2 P := by
  obtain ⟨C, _, hC⟩ := hV.bound_coe
  have hm : Measurable (V b) := (hV.measurable_coe b).mono (N.pastFiltration.le b.1) le_rfl
  exact (memLp_top_of_bound hm.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC b ω)).mono_exponent le_top

/-! ### The elementary compensated integral as a linear map -/

/-- The **elementary compensated integral** `∑_{b} φ_b(·) · Ñ(box b)(·)` of a marked simple
integrand, as a function `Ω → ℝ`. -/
noncomputable def intSum (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) : Ω → ℝ :=
  V.1.sum fun b φ => fun ω => φ ω * N.compensated (indexBox b) ω

/-- The elementary integral is in `L²(P)`: a finite sum of `L²` terms `φ_b · Ñ(box b)`
(`memLp_adapted_mul_compensated`). -/
lemma memLp_intSum (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    MemLp (intSum N V) 2 P := by
  have hrw : intSum N V
      = fun ω => ∑ b ∈ V.1.support, V.1 b ω * N.compensated (indexBox b) ω := by
    funext ω; simp only [intSum, Finsupp.sum, Finset.sum_apply]
  rw [hrw]
  exact memLp_finsetSum V.1.support fun b hb =>
    memLp_adapted_mul_compensated N (V.2.markMeasurable b hb) (V.2.markFinite b hb)
      (V.2.adapted b hb) (V.2.memLp_coe b)

/-- The elementary integral is additive in the integrand. -/
lemma intSum_add (N : PoissonRandomMeasure P ν) (V W : levySimpleModule N) :
    intSum N (V + W) = intSum N V + intSum N W := by
  have key : ((V + W : levySimpleModule N) : (ℝ × ℝ × Set E) →₀ (Ω → ℝ))
      = (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) + (W : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) := rfl
  simp only [intSum, key]
  exact Finsupp.sum_add_index' (fun b => funext fun ω => by simp)
    (fun b φ ψ => funext fun ω => by simp [add_mul])

/-- The elementary integral is homogeneous in the integrand. -/
lemma intSum_smul (N : PoissonRandomMeasure P ν) (c : ℝ) (V : levySimpleModule N) :
    intSum N (c • V) = c • intSum N V := by
  have key : ((c • V : levySimpleModule N) : (ℝ × ℝ × Set E) →₀ (Ω → ℝ))
      = c • (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) := rfl
  simp only [intSum, key]
  rw [Finsupp.sum_smul_index' (fun b => funext fun ω => by simp)]
  simp only [Finsupp.sum]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun b _ => funext fun ω => by simp [smul_eq_mul, mul_assoc]

/-- The elementary integral, in `L²(P)`. -/
noncomputable def intSumLp (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) : Lp ℝ 2 P :=
  (memLp_intSum N V).toLp

/-- **The compensated-Poisson integral as a linear map** `levySimpleModule →ₗ[ℝ] L²(P)`. -/
noncomputable def intAssembly (N : PoissonRandomMeasure P ν) :
    levySimpleModule N →ₗ[ℝ] Lp ℝ 2 P where
  toFun V := intSumLp N V
  map_add' V W := by
    rw [intSumLp, intSumLp, intSumLp,
      ← MemLp.toLp_add (memLp_intSum N V) (memLp_intSum N W)]
    congr 1
    exact intSum_add N V W
  map_smul' c V := by
    rw [intSumLp, intSumLp, RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_intSum N V)]
    congr 1
    exact intSum_smul N c V

/-! ### The integrand embedding into the predictable `L²(dP ⊗ dν̂)` -/

omit [IsProbabilityMeasure P] in
/-- A single box term `φ(ω)·𝟙_{(s,t]×A}(z)` is in `L²(P ⊗ ν̂)`: its square is
`φ(ω)² · 𝟙_box(z)`, an `L¹` product of `φ² ∈ L¹(P)` and the finite-box indicator `∈ L¹(ν̂)`
(`Integrable.mul_prod`). -/
lemma memLp_indicatorTerm {s t : ℝ} {A : Set E}
    (hA : MeasurableSet A) (hAfin : ν A ≠ ⊤) {φ : Ω → ℝ} (hφm : Measurable φ)
    (hφL2 : MemLp φ 2 P) :
    MemLp (fun p : Ω × (ℝ × E) => φ p.1 * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2) 2
      (P.prod (referenceIntensity ν)) := by
  have hboxms : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hboxfin : referenceIntensity ν (Set.Ioc s t ×ˢ A) ≠ ⊤ := referenceIntensity_box_ne_top hAfin
  have hgm : Measurable
      (fun p : Ω × (ℝ × E) => φ p.1 * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2) :=
    (hφm.comp measurable_fst).mul ((measurable_const.indicator hboxms).comp measurable_snd)
  refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr ?_
  have hform : (fun p : Ω × (ℝ × E) =>
        (φ p.1 * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2) ^ 2)
      = fun p => (φ p.1) ^ 2 * ((Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2
          * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2) := by
    funext p; ring
  rw [hform]
  have hg : Integrable (fun z : ℝ × E => (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) z
      * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) z) (referenceIntensity ν) := by
    rw [show (fun z : ℝ × E => (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) z
          * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) z)
        = (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) from by
      funext z; by_cases hz : z ∈ Set.Ioc s t ×ˢ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]]
    exact (integrable_indicator_iff hboxms).mpr (integrableOn_const (hs := hboxfin))
  exact (hφL2.integrable_sq).mul_prod hg

/-- The **integrand** `∑_b φ_b(·) · 𝟙_{box b}(·)` of a marked simple integrand, a function on
`Ω × (ℝ × E)`. -/
noncomputable def embFun (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    Ω × (ℝ × E) → ℝ :=
  V.1.sum fun b φ => fun p => φ p.1 * (indexBox b).indicator (fun _ => (1 : ℝ)) p.2

/-- The integrand is in `L²(P ⊗ ν̂)`: a finite sum of `L²` box terms (`memLp_indicatorTerm`). -/
lemma memLp_embFun (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    MemLp (embFun N V) 2 (P.prod (referenceIntensity ν)) := by
  have hrw : embFun N V = fun p => ∑ b ∈ V.1.support,
      V.1 b p.1 * (Set.Ioc b.1 b.2.1 ×ˢ b.2.2).indicator (fun _ => (1 : ℝ)) p.2 := by
    funext p; simp only [embFun, indexBox, Finsupp.sum, Finset.sum_apply]
  rw [hrw]
  refine memLp_finsetSum V.1.support ?_
  intro b hb
  exact memLp_indicatorTerm (V.2.markMeasurable b hb) (V.2.markFinite b hb)
    ((V.2.measurable_coe b).mono (N.pastFiltration.le b.1) le_rfl) (V.2.memLp_coe b)

/-- The integrand embedding is additive in the integrand. -/
lemma embFun_add (N : PoissonRandomMeasure P ν) (V W : levySimpleModule N) :
    embFun N (V + W) = embFun N V + embFun N W := by
  have key : ((V + W : levySimpleModule N) : (ℝ × ℝ × Set E) →₀ (Ω → ℝ))
      = (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) + (W : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) := rfl
  simp only [embFun, key]
  exact Finsupp.sum_add_index' (fun b => funext fun p => by simp)
    (fun b φ ψ => funext fun p => by simp [add_mul])

/-- The integrand embedding is homogeneous in the integrand. -/
lemma embFun_smul (N : PoissonRandomMeasure P ν) (c : ℝ) (V : levySimpleModule N) :
    embFun N (c • V) = c • embFun N V := by
  have key : ((c • V : levySimpleModule N) : (ℝ × ℝ × Set E) →₀ (Ω → ℝ))
      = c • (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) := rfl
  simp only [embFun, key]
  rw [Finsupp.sum_smul_index' (fun b => funext fun p => by simp)]
  simp only [Finsupp.sum]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun b _ => funext fun p => by simp [smul_eq_mul, mul_assoc]

/-- The integrand, in `L²(P ⊗ ν̂)`. -/
noncomputable def embLp (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    Lp ℝ 2 (P.prod (referenceIntensity ν)) := (memLp_embFun N V).toLp

/-- **The integrand embedding as a linear map** `levySimpleModule →ₗ[ℝ] L²(dP ⊗ dν̂)`. -/
noncomputable def emb (N : PoissonRandomMeasure P ν) :
    levySimpleModule N →ₗ[ℝ] Lp ℝ 2 (P.prod (referenceIntensity ν)) where
  toFun V := embLp N V
  map_add' V W := by
    rw [embLp, embLp, embLp, ← MemLp.toLp_add (memLp_embFun N V) (memLp_embFun N W)]
    congr 1
    exact embFun_add N V W
  map_smul' c V := by
    rw [embLp, embLp, RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_embFun N V)]
    congr 1
    exact embFun_smul N c V

/-! ### The isometry `‖intAssembly V‖ = ‖emb V‖` (summing the bilinear pairing) -/

/-- Each box term of the elementary integral is in `L²(P)`. -/
lemma memLp_intTerm (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {b : ℝ × ℝ × Set E} (hb : b ∈ V.1.support) :
    MemLp (fun ω => V.1 b ω * N.compensated (indexBox b) ω) 2 P :=
  memLp_adapted_mul_compensated N (V.2.markMeasurable b hb) (V.2.markFinite b hb)
    (V.2.adapted b hb) (V.2.memLp_coe b)

/-- Each box term of the integrand is in `L²(P ⊗ ν̂)`. -/
lemma memLp_embTerm (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {b : ℝ × ℝ × Set E} (hb : b ∈ V.1.support) :
    MemLp (fun p : Ω × (ℝ × E) => V.1 b p.1 * (indexBox b).indicator (fun _ => (1 : ℝ)) p.2) 2
      (P.prod (referenceIntensity ν)) :=
  memLp_indicatorTerm (V.2.markMeasurable b hb) (V.2.markFinite b hb)
    ((V.2.measurable_coe b).mono (N.pastFiltration.le b.1) le_rfl) (V.2.memLp_coe b)

/-- A pair of elementary-integral box terms has an integrable product (`L² · L²`), in scalar-lambda
form (so the double-sum `∫ = ∑∫` rewrites match). -/
lemma integrable_intPair (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {ba bb : ℝ × ℝ × Set E} (hba : ba ∈ V.1.support) (hbb : bb ∈ V.1.support) :
    Integrable (fun ω => (V.1 ba ω * N.compensated (indexBox ba) ω)
      * (V.1 bb ω * N.compensated (indexBox bb) ω)) P :=
  (memLp_intTerm N V hba).integrable_mul (memLp_intTerm N V hbb)

/-- A pair of integrand box terms has an integrable product (`L² · L²`), in scalar-lambda form. -/
lemma integrable_embPair (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {ba bb : ℝ × ℝ × Set E} (hba : ba ∈ V.1.support) (hbb : bb ∈ V.1.support) :
    Integrable (fun p : Ω × (ℝ × E) =>
      (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
        * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2))
      (P.prod (referenceIntensity ν)) :=
  (memLp_embTerm N V hba).integrable_mul (memLp_embTerm N V hbb)

/-- **The `L²(P)` second moment as a double sum** over the box family. -/
lemma intSum_sq_integral (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    ∫ ω, (intSum N V ω) ^ 2 ∂P
      = ∑ ba ∈ V.1.support, ∑ bb ∈ V.1.support,
          ∫ ω, (V.1 ba ω * N.compensated (indexBox ba) ω)
                * (V.1 bb ω * N.compensated (indexBox bb) ω) ∂P := by
  have hrw : intSum N V
      = fun ω => ∑ b ∈ V.1.support, V.1 b ω * N.compensated (indexBox b) ω := by
    funext ω; simp only [intSum, Finsupp.sum, Finset.sum_apply]
  rw [hrw]
  have hsq : (fun ω => (∑ b ∈ V.1.support, V.1 b ω * N.compensated (indexBox b) ω) ^ 2)
      = fun ω => ∑ ba ∈ V.1.support, ∑ bb ∈ V.1.support,
          (V.1 ba ω * N.compensated (indexBox ba) ω)
            * (V.1 bb ω * N.compensated (indexBox bb) ω) := by
    funext ω; rw [sq, Finset.sum_mul_sum]
  rw [hsq]
  rw [integral_finsetSum V.1.support fun ba hba => integrable_finsetSum V.1.support fun bb hbb =>
    integrable_intPair N V hba hbb]
  refine Finset.sum_congr rfl fun ba hba => ?_
  exact integral_finsetSum V.1.support fun bb hbb =>
    integrable_intPair N V hba hbb

/-- **The `L²(P ⊗ ν̂)` integrand norm as a double sum** over the box family. -/
lemma embFun_sq_integral (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    ∫ p, (embFun N V p) ^ 2 ∂(P.prod (referenceIntensity ν))
      = ∑ ba ∈ V.1.support, ∑ bb ∈ V.1.support,
          ∫ p, (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
                * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2)
            ∂(P.prod (referenceIntensity ν)) := by
  have hrw : embFun N V = fun p => ∑ b ∈ V.1.support,
      V.1 b p.1 * (indexBox b).indicator (fun _ => (1 : ℝ)) p.2 := by
    funext p; simp only [embFun, Finsupp.sum, Finset.sum_apply]
  rw [hrw]
  have hsq : (fun p : Ω × (ℝ × E) =>
        (∑ b ∈ V.1.support, V.1 b p.1 * (indexBox b).indicator (fun _ => (1 : ℝ)) p.2) ^ 2)
      = fun p => ∑ ba ∈ V.1.support, ∑ bb ∈ V.1.support,
          (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
            * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2) := by
    funext p; rw [sq, Finset.sum_mul_sum]
  rw [hsq]
  rw [integral_finsetSum V.1.support fun ba hba => integrable_finsetSum V.1.support fun bb hbb =>
    integrable_embPair N V hba hbb]
  refine Finset.sum_congr rfl fun ba hba => ?_
  exact integral_finsetSum V.1.support fun bb hbb =>
    integrable_embPair N V hba hbb

/-- **The per-pair identity** connecting the two double sums: the compensated-integral pairing of
two box terms equals the `L²(P ⊗ ν̂)` pairing of the two integrand terms — both are
`𝔼[φ_ba φ_bb] · ν̂(box ba ∩ box bb)`. The `⟵` is the overlapping-box bilinear pairing
`integral_bilinear_pairing` (rung 2, ordering the pair by start), the `⟶` is Fubini
(`integral_prod_mul`) on the product measure. -/
lemma pair_integral_eq (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {ba bb : ℝ × ℝ × Set E} (hba : ba ∈ V.1.support) (hbb : bb ∈ V.1.support) :
    ∫ ω, (V.1 ba ω * N.compensated (indexBox ba) ω)
          * (V.1 bb ω * N.compensated (indexBox bb) ω) ∂P
      = ∫ p, (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
              * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2)
          ∂(P.prod (referenceIntensity ν)) := by
  obtain ⟨C, _, hC⟩ := V.2.bound_coe
  have hboxams : MeasurableSet (indexBox ba) := measurableSet_Ioc.prod (V.2.markMeasurable ba hba)
  have hboxbms : MeasurableSet (indexBox bb) := measurableSet_Ioc.prod (V.2.markMeasurable bb hbb)
  -- the compensated pairing equals `𝔼[φ_ba φ_bb] · ν̂(box ba ∩ box bb)` (WLOG order by start)
  have hLHS : ∫ ω, (V.1 ba ω * N.compensated (indexBox ba) ω)
        * (V.1 bb ω * N.compensated (indexBox bb) ω) ∂P
      = (∫ ω, V.1 ba ω * V.1 bb ω ∂P)
          * (referenceIntensity ν (indexBox ba ∩ indexBox bb)).toReal := by
    rcases le_total ba.1 bb.1 with hab | hab
    · exact integral_bilinear_pairing N hab (V.2.markMeasurable ba hba) (V.2.markMeasurable bb hbb)
        (V.2.markFinite ba hba) (V.2.markFinite bb hbb) (V.2.adapted ba hba) (V.2.adapted bb hbb)
        (fun ω => hC ba ω) (fun ω => hC bb ω)
    · have hpair := integral_bilinear_pairing N (ta := bb.2.1) (tb := ba.2.1) hab
        (V.2.markMeasurable bb hbb) (V.2.markMeasurable ba hba) (V.2.markFinite bb hbb)
        (V.2.markFinite ba hba) (V.2.adapted bb hbb) (V.2.adapted ba hba)
        (fun ω => hC bb ω) (fun ω => hC ba ω)
      calc ∫ ω, (V.1 ba ω * N.compensated (indexBox ba) ω)
              * (V.1 bb ω * N.compensated (indexBox bb) ω) ∂P
          = ∫ ω, (V.1 bb ω * N.compensated (indexBox bb) ω)
              * (V.1 ba ω * N.compensated (indexBox ba) ω) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
        _ = (∫ ω, V.1 bb ω * V.1 ba ω ∂P)
              * (referenceIntensity ν (indexBox bb ∩ indexBox ba)).toReal := hpair
        _ = (∫ ω, V.1 ba ω * V.1 bb ω ∂P)
              * (referenceIntensity ν (indexBox ba ∩ indexBox bb)).toReal := by
            rw [Set.inter_comm (indexBox bb) (indexBox ba)]
            congr 1
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  -- the integrand pairing equals the same, by Fubini
  have hRHS : ∫ p, (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
        * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2)
          ∂(P.prod (referenceIntensity ν))
      = (∫ ω, V.1 ba ω * V.1 bb ω ∂P)
          * (referenceIntensity ν (indexBox ba ∩ indexBox bb)).toReal := by
    have hind : (fun z : ℝ × E => (indexBox ba).indicator (fun _ => (1 : ℝ)) z
          * (indexBox bb).indicator (fun _ => (1 : ℝ)) z)
        = (indexBox ba ∩ indexBox bb).indicator (fun _ => (1 : ℝ)) := by
      funext z; by_cases hzi : z ∈ indexBox ba <;> by_cases hzj : z ∈ indexBox bb <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, hzi, hzj]
    rw [show (fun p : Ω × (ℝ × E) =>
            (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
              * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2))
          = fun p => (V.1 ba p.1 * V.1 bb p.1)
              * ((indexBox ba).indicator (fun _ => (1 : ℝ)) p.2
                  * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2) from by funext p; ring,
      integral_prod_mul (fun ω => V.1 ba ω * V.1 bb ω)
        (fun z => (indexBox ba).indicator (fun _ => (1 : ℝ)) z
          * (indexBox bb).indicator (fun _ => (1 : ℝ)) z),
      hind, integral_indicator (hboxams.inter hboxbms), setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def]
  rw [hLHS, hRHS]

/-- **The Itô–Lévy isometry on marked simple integrands** (the identity `extendOfNorm` consumes):
`‖intAssembly V‖ = ‖emb V‖`. Both squared norms expand into the same box-family double sum, equal
term-by-term by `pair_integral_eq` — i.e. the compensated integral into `L²(P)` and the integrand in
`L²(P ⊗ ν̂)` have equal norms. -/
theorem assembly_isometry (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    ‖intAssembly N V‖ = ‖emb N V‖ := by
  have hsq : ‖intAssembly N V‖ ^ 2 = ‖emb N V‖ ^ 2 := by
    change ‖(intSumLp N V : Lp ℝ 2 P)‖ ^ 2 =
        ‖(embLp N V : Lp ℝ 2 (P.prod (referenceIntensity ν)))‖ ^ 2
    rw [lp_two_norm_sq, lp_two_norm_sq]
    rw [show (∫ ω, ((intSumLp N V : Ω → ℝ) ω) ^ 2 ∂P) = ∫ ω, (intSum N V ω) ^ 2 ∂P from
        integral_congr_ae (by
          filter_upwards [(memLp_intSum N V).coeFn_toLp] with ω hω; simp only [intSumLp]; rw [hω]),
      show (∫ p, ((embLp N V : Ω × (ℝ × E) → ℝ) p) ^ 2 ∂(P.prod (referenceIntensity ν)))
          = ∫ p, (embFun N V p) ^ 2 ∂(P.prod (referenceIntensity ν)) from
        integral_congr_ae (by
          filter_upwards [(memLp_embFun N V).coeFn_toLp] with p hp; simp only [embLp]; rw [hp]),
      intSum_sq_integral, embFun_sq_integral]
    exact Finset.sum_congr rfl fun ba hba => Finset.sum_congr rfl fun bb hbb =>
      pair_integral_eq N V hba hbb
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-! ### The Itô–Lévy integral CLM on the `L²` closure of the simple integrands -/

/-- **The `L²(dP ⊗ dν̂)` closure of the marked simple integrands** — the domain of the extended
Itô–Lévy integral. Concretely the topological closure of `emb`'s range: every element is an `L²`
limit of marked simple integrands `∑_b φ_b · 𝟙_{box b}`. Defining the target *as* this closure makes
the extension's density hypothesis a soft topological fact (`embCorestrict_denseRange`),
sidestepping an explicit marked-predictable `σ`-algebra characterisation. -/
noncomputable def levyClosure (N : PoissonRandomMeasure P ν) :
    Submodule ℝ (Lp ℝ 2 (P.prod (referenceIntensity ν))) :=
  (LinearMap.range (emb N)).topologicalClosure

/-- The integrand embedding `emb`, corestricted to the closure `levyClosure` of its range — the
dense-range map along which the elementary integral extends. -/
noncomputable def embCorestrict (N : PoissonRandomMeasure P ν) :
    levySimpleModule N →ₗ[ℝ] levyClosure N :=
  (emb N).codRestrict (levyClosure N)
    (fun V => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (emb N) V))

/-- **Marked simple integrands are dense in their `L²` closure** `levyClosure`. Pushed into the
ambient `L²` the corestricted embedding's range is exactly `emb`'s range, whose closure is
`levyClosure` by construction; so every element of the closure subtype lies in the closure of that
range (`IsInducing.subtypeVal.dense_iff`). -/
theorem embCorestrict_denseRange (N : PoissonRandomMeasure P ν) :
    DenseRange (embCorestrict N) := by
  have hind : Topology.IsInducing ((↑) : levyClosure N → Lp ℝ 2 (P.prod (referenceIntensity ν))) :=
    Topology.IsInducing.subtypeVal
  rw [DenseRange, hind.dense_iff]
  intro x
  have himg : ((↑) : levyClosure N → Lp ℝ 2 (P.prod (referenceIntensity ν)))
        '' Set.range (embCorestrict N)
      = Set.range (emb N) := by
    rw [← Set.range_comp]; rfl
  rw [himg, ← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
  exact x.2

/-- **The Itô–Lévy compensated-Poisson integral as a CLM** on the `L²` closure of the marked simple
integrands: the norm-continuous extension of the elementary integral `intAssembly` along the dense
embedding `embCorestrict` (`LinearMap.extendOfNorm`). -/
noncomputable def itoLevyIntegralL2 (N : PoissonRandomMeasure P ν) :
    levyClosure N →L[ℝ] Lp ℝ 2 P := by
  -- `refine … ?_; exact` rather than a bare `(intAssembly N).extendOfNorm (embCorestrict N)`: the
  -- CLM goal type pins `Eₗ = ↥(levyClosure N)` with its seminormed-group instances, so `exact`
  -- bridges the `Submodule.addCommMonoid` vs seminormed `AddCommMonoid` diamond in one cheap
  -- `isDefEq`. (docs/patterns.md — "extendOfNorm into a submodule".)
  refine LinearMap.extendOfNorm (E := ↥(levySimpleModule N)) (F := Lp ℝ 2 P) (intAssembly N) ?_
  exact embCorestrict N

/-- **The Itô–Lévy `L²` isometry, in full generality** — LevyStochCalc's cited axiom #6: on the
whole `L²` closure `levyClosure`, `‖itoLevyIntegralL2 H‖ = ‖H‖`. The compensated-Poisson stochastic
integral is an `L²` isometry — proven on marked simple integrands (`assembly_isometry`, summing the
overlapping-box bilinear pairing) and extended by continuity to their closure. -/
theorem itoLevyIntegralL2_norm (N : PoissonRandomMeasure P ν) (H : levyClosure N) :
    ‖itoLevyIntegralL2 N H‖ = ‖H‖ := by
  have key : ∀ V : levySimpleModule N, ‖intAssembly N V‖ = ‖embCorestrict N V‖ :=
    fun V => by rw [← Submodule.norm_coe]; exact assembly_isometry N V
  -- `unfold` exposes the def's already-bridged `extendOfNorm` term; discharging the isometry kernel
  -- against the submodule codomain reuses the finite instance comparison.
  unfold itoLevyIntegralL2
  exact LinearMap.norm_extendOfNorm_eq_of_isometry (embCorestrict_denseRange N) key H

end MathFin
