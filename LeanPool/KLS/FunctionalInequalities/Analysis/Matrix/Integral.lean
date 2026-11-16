/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Sign
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Trace energies of symmetric matrix fields under a measure

Letwin, arXiv:2607.24164v1, Theorem 2.5, the extension step from positive semidefinite to all
symmetric `B`, for a
measurable field `H : Ω → Matrix ι ι ℝ` of positive semidefinite matrices under an arbitrary measure
`ν` on an arbitrary
measurable space, over every finite index type (the empty one included): if every positive
semidefinite `A` has
`x ↦ tr(A H(x) A H(x))` integrable with `∫ tr(A H A H) dν ≤ C tr(A²)` for a real `C`, then every
symmetric `B` has the
same (`symmetric_trace_integral_extension_mul`, a.e. form
`symmetric_trace_integral_extension_mul_of_ae_posSemidef`; the
source coefficient `C = 2` is `symmetric_trace_integral_extension`). The integrability for `B` is
derived (pointwise Jordan domination of
`Matrix/Sign.lean` and `Matrix/Trace/Energy.lean`); no finiteness of `ν`, nonemptiness or
commutation is assumed. The positive
semidefinite bound is a named hypothesis: it is not constructed here, nor is the moment map,
Brascamp–Lieb or Theorem
2.5 itself.
Finite flux contraction (`integral_quadratic_flux_le_of_posSemidef`): entrywise integrable matrix
fields with
`∫ Fᵢⱼ = -∫ Eᵢⱼ` and `E + H` a.e. positive semidefinite satisfy `∫ v ⬝ Fv ≤ ∫ v ⬝ Hv`, under an
arbitrary measure and finite index
type (the empty one included).
-/

@[expose] public section

namespace FunctionalInequalities.Analysis

section TraceExtensions

open Matrix MeasureTheory

variable {ι : Type*} [Fintype ι]
/--
Arbitrary real coefficient, almost-everywhere positive semidefinite field: if every positive
semidefinite `A`
has `x ↦ tr(A H(x) A H(x))` integrable with `∫ tr(A H A H) dν ≤ C tr(A²)`, then every symmetric `B`
has the same.
No sign condition on `C`; arbitrary measure and finite index type (empty allowed). -/
theorem symmetric_trace_integral_extension_mul_of_ae_posSemidef {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {C : ℝ} (H : Ω → Matrix ι ι ℝ)
    (hH_meas : ∀ i j, Measurable (fun x => H x i j)) (hH_psd : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hPSD :
      ∀ A : Matrix ι ι ℝ,
        A.PosSemidef →
          Integrable (fun x => (A * H x * A * H x).trace) ν ∧
            (∫ x, (A * H x * A * H x).trace ∂ν) ≤ C * (A * A).trace)
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤ C * (B * B).trace := by
  classical
  obtain ⟨P, N, hP, hN, hdec, hPN, hNP, htrace⟩ := symmetric_jordan_decomposition B hB
  obtain ⟨hP_int, hP_bound⟩ := hPSD P hP
  obtain ⟨hN_int, hN_bound⟩ := hPSD N hN
  have hmeas (A : Matrix ι ι ℝ) : Measurable (fun x => (A * H x * A * H x).trace) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.mul ?_ (hH_meas j i)
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine Measurable.mul ?_ measurable_const
    refine Finset.measurable_sum _ (fun l _ => ?_)
    exact measurable_const.mul (hH_meas l k)
  have hP_nonneg : ∀ᵐ x ∂ν, 0 ≤ (P * H x * P * H x).trace := by
    filter_upwards [hH_psd] with x hx
    exact
      trace_energy_nonneg (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hP))
        hx
  have hN_nonneg : ∀ᵐ x ∂ν, 0 ≤ (N * H x * N * H x).trace := by
    filter_upwards [hH_psd] with x hx
    exact
      trace_energy_nonneg (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hN))
        hx
  have hB_nonneg : ∀ᵐ x ∂ν, 0 ≤ (B * H x * B * H x).trace := by
    filter_upwards [hH_psd] with x hx
    exact trace_energy_nonneg hB hx
  have hdom :
    ∀ᵐ x ∂ν,
      (B * H x * B * H x).trace ≤ (P * H x * P * H x).trace + (N * H x * N * H x).trace := by
    filter_upwards [hH_psd] with x hx
    rw [hdec]
    exact
      jordan_trace_domination hP hN
        (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hx))
  have hsum_int :
    Integrable (fun x => (P * H x * P * H x).trace + (N * H x * N * H x).trace) ν := by
    exact hP_int.add hN_int
  have hB_int : Integrable (fun x => (B * H x * B * H x).trace) ν := by
    refine hsum_int.mono (hmeas B).aestronglyMeasurable ?_
    filter_upwards [hB_nonneg, hP_nonneg, hN_nonneg, hdom] with x hB0 hP0 hN0 hd
    rw [Real.norm_eq_abs, abs_of_nonneg hB0]
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hP0 hN0)]
    exact hd
  have hIntDom :
    (∫ x, (B * H x * B * H x).trace ∂ν) ≤
      ∫ x, ((P * H x * P * H x).trace + (N * H x * N * H x).trace) ∂ν := by
    exact integral_mono_ae hB_int hsum_int hdom
  refine ⟨hB_int, ?_⟩
  calc
    (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        ∫ x, ((P * H x * P * H x).trace + (N * H x * N * H x).trace) ∂ν :=
      hIntDom
    _ = (∫ x, (P * H x * P * H x).trace ∂ν) + ∫ x, (N * H x * N * H x).trace ∂ν :=
      integral_add hP_int hN_int
    _ ≤ C * (P * P).trace + C * (N * N).trace := add_le_add hP_bound hN_bound
    _ = C * (B * B).trace := by
      calc
        C * (P * P).trace + C * (N * N).trace = C * ((P * P).trace + (N * N).trace) := by ring
        _ = C * (B * B).trace := by rw [← htrace]


/-- Arbitrary real coefficient, pointwise positive semidefinite field: the specialization of
`symmetric_trace_integral_extension_mul_of_ae_posSemidef` through `ae_of_all`. -/
theorem symmetric_trace_integral_extension_mul
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {C : ℝ}
    (H : Ω → Matrix ι ι ℝ)
    (hH_meas : ∀ i j, Measurable (fun x => H x i j))
    (hH_psd : ∀ x, (H x).PosSemidef)
    (hPSD : ∀ A : Matrix ι ι ℝ, A.PosSemidef →
      Integrable (fun x => (A * H x * A * H x).trace) ν ∧
        (∫ x, (A * H x * A * H x).trace ∂ν) ≤
          C * (A * A).trace)
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        C * (B * B).trace :=
  symmetric_trace_integral_extension_mul_of_ae_posSemidef ν H hH_meas (ae_of_all ν hH_psd) hPSD hB

/-- Supporting measure extension from the PSD integral estimate to every symmetric
real matrix. This theorem does not construct the PSD estimate or any source-law
moment-map data. -/
theorem symmetric_trace_integral_extension
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (H : Ω → Matrix ι ι ℝ)
    (hH_meas : ∀ i j, Measurable (fun x => H x i j))
    (hH_psd : ∀ x, (H x).PosSemidef)
    (hPSD : ∀ A : Matrix ι ι ℝ, A.PosSemidef →
      Integrable (fun x => (A * H x * A * H x).trace) ν ∧
        (∫ x, (A * H x * A * H x).trace ∂ν) ≤
          2 * (A * A).trace)
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        2 * (B * B).trace :=
  symmetric_trace_integral_extension_mul ν H hH_meas hH_psd hPSD hB

/--
The symmetric trace-integral extension of `symmetric_trace_integral_extension` from
almost-everywhere positive
semidefinite matrix fields: the bound `∫ tr(A H A H) ≤ 2 tr(A A)` for every PSD `A` gives it for
every symmetric `B`.
Arbitrary finite index type (empty allowed) and measure. -/
theorem symmetric_trace_integral_extension_of_ae_posSemidef {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (H : Ω → Matrix ι ι ℝ) (hH_meas : ∀ i j, Measurable (fun x => H x i j))
    (hH_psd : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hPSD :
      ∀ A : Matrix ι ι ℝ,
        A.PosSemidef →
          Integrable (fun x => (A * H x * A * H x).trace) ν ∧
            (∫ x, (A * H x * A * H x).trace ∂ν) ≤ 2 * (A * A).trace)
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤ 2 * (B * B).trace :=
  symmetric_trace_integral_extension_mul_of_ae_posSemidef ν H hH_meas hH_psd hPSD hB

end TraceExtensions

/-! ### Trace against a mean-identity matrix field

If every entry of a random matrix `H` is integrable with mean `Id`, then `tr (B H)` is integrable
with integral `tr B`. -/

section MeanIdentity

open MeasureTheory Matrix

theorem integral_trace_mul_of_mean_one {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (ρ : Measure Ω) (H : Ω → Matrix ι ι ℝ)
    (hInt : ∀ i j, Integrable (fun y => H y i j) ρ)
    (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix ι ι ℝ) i j) (B : Matrix ι ι ℝ) :
    Integrable (fun y => Matrix.trace (B * H y)) ρ ∧
      (∫ y, Matrix.trace (B * H y) ∂ρ) = Matrix.trace B := by
  have hterms (i j : ι) : Integrable (fun y => B i j * H y j i) ρ := (hInt j i).const_mul _
  have hsum (i : ι) : Integrable (fun y => ∑ j, B i j * H y j i) ρ := by
    apply integrable_finsetSum
    intro j _
    exact hterms i j
  have ht : Integrable (fun y => Matrix.trace (B * H y)) ρ := by
    change Integrable (fun y => ∑ i, ∑ j, B i j * H y j i) ρ
    apply integrable_finsetSum
    intro i _
    exact hsum i
  refine ⟨ht, ?_⟩
  change (∫ y, ∑ i, ∑ j, B i j * H y j i ∂ρ) = _
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hsum i)]
  have he (i : ι) : (∫ y, ∑ j, B i j * H y j i ∂ρ) = B i i := by
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hterms i j)]
    calc
      (∑ j, ∫ y, B i j * H y j i ∂ρ) = ∑ j, B i j * (1 : Matrix ι ι ℝ) j i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul, hmean]
      _ = (B * (1 : Matrix ι ι ℝ)) i i := rfl
      _ = B i i := by rw [Matrix.mul_one]
  simp_rw [he]
  rfl

end MeanIdentity

/-! ### Finite contraction of matrix flux identities -/

section FluxContraction

open Matrix MeasureTheory

/-- Finite contraction of matrix-valued weak flux identities with PSD forcing.
The entries may already include a fixed nonnegative compact test function and weight. -/
theorem integral_quadratic_flux_le_of_posSemidef
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) (F E H : X → Matrix ι ι ℝ) (v : ι → ℝ)
    (hF : ∀ i j, Integrable (fun x => F x i j) ν)
    (hE : ∀ i j, Integrable (fun x => E x i j) ν)
    (hH : ∀ i j, Integrable (fun x => H x i j) ν)
    (hflux : ∀ i j, (∫ x, F x i j ∂ν) = -(∫ x, E x i j ∂ν))
    (hpos : ∀ᵐ x ∂ν, (E x + H x).PosSemidef) :
    (∫ x, dotProduct v ((F x).mulVec v) ∂ν) ≤
      ∫ x, dotProduct v ((H x).mulVec v) ∂ν := by
  classical
  have hint (A : X → Matrix ι ι ℝ)
      (hA : ∀ i j, Integrable (fun x => A x i j) ν) :
      Integrable (fun x => dotProduct v ((A x).mulVec v)) ν := by
    change Integrable (fun x => ∑ i, v i * ∑ j, A x i j * v j) ν
    apply integrable_finsetSum Finset.univ
    intro i _
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ fun j _ => (hA i j).mul_const (v j)
  have hrep (A : X → Matrix ι ι ℝ)
      (hA : ∀ i j, Integrable (fun x => A x i j) ν) :
      (∫ x, dotProduct v ((A x).mulVec v) ∂ν) =
        ∑ i, v i * ∑ j, (∫ x, A x i j ∂ν) * v j := by
    change (∫ x, ∑ i, v i * ∑ j, A x i j * v j ∂ν) = _
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (integrable_finsetSum Finset.univ fun j _ => (hA i j).mul_const (v j)).const_mul (v i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => (hA i j).mul_const (v j))]
    simp only [integral_mul_const]
  have heq : (∫ x, dotProduct v ((F x).mulVec v) ∂ν) =
      -(∫ x, dotProduct v ((E x).mulVec v) ∂ν) := by
    rw [hrep F hF, hrep E hE]
    simp only [hflux, neg_mul, Finset.sum_neg_distrib, mul_neg]
  have hpoint : ∀ᵐ x ∂ν, -dotProduct v ((E x).mulVec v) ≤
      dotProduct v ((H x).mulVec v) := by
    filter_upwards [hpos] with x hx
    have h := hx.dotProduct_mulVec_nonneg v
    rw [Matrix.add_mulVec, dotProduct_add] at h
    simp only [star_trivial] at h
    linarith
  calc
    _ = ∫ x, -dotProduct v ((E x).mulVec v) ∂ν := by rw [integral_neg, heq]
    _ ≤ _ := integral_mono_ae (hint E hE).neg (hint H hH) hpoint

end FluxContraction

end FunctionalInequalities.Analysis
