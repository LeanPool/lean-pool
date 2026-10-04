/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.Morrey
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure


/-!
# Sobolev embedding of `H₀¹(Ω)`

The Gagliardo-Nirenberg-Sobolev inequality `‖u‖_{L^{2⋆}} ≤ C ‖∇u‖_{L²}`, with `2⋆` the Sobolev
conjugate `1/2⋆ = 1/2 - 1/d`, is Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` for a smooth compactly supported function. This
file passes it from the test functions to their closure `H₀¹(Ω)` and bundles the result as a
continuous linear map.

## Lower semicontinuity in place of continuity

`EllipticPdes.Poincare.poincare_H01` extends the Poincaré inequality to `H₀¹(Ω)` by observing that
the estimate is a closed condition on a continuous function of the graph. That argument is
unavailable here: the two sides of the Sobolev estimate live at different exponents, and the
`L^q` seminorm of the function coordinate is not a continuous function of the `H¹` graph.

What survives is lower semicontinuity. Convergence in `H¹` gives convergence of the function
coordinate in `L²(Ω)`, hence convergence in measure, and
`MeasureTheory.eLpNorm_le_of_tendstoInMeasure` passes an eventual bound at the exponent `q` to the
limit through Fatou's lemma. The bound along the sequence is not constant, so it is the limit of
the right-hand sides that is used, one strict upper bound at a time.

The transfer takes the test-function estimate as a hypothesis at an arbitrary exponent and an
arbitrary constant, in the manner of `EllipticPdes.Poincare.poincare_H01`, so each
Gagliardo-Nirenberg-Sobolev variant proved for test functions reaches `H₀¹(Ω)` by supplying it.
Two are supplied: the critical exponent on any `Ω`, and every exponent below it on a bounded `Ω`.

## Main declarations

* `EllipticPdes.Embedding.eLpNorm_testGraph_le`: the estimate on a test function at the critical
  exponent, read off the graph coordinates.
* `EllipticPdes.Embedding.eLpNorm_testGraph_le_of_isBounded`: the same at every exponent below the
  critical one, on a bounded domain.
* `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_forall_testFn`: the transfer principle, from an
  estimate on test functions to the same estimate on `H₀¹(Ω)`.
* `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01` and
  `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_isBounded`: the two estimates on `H₀¹(Ω)`.
* `EllipticPdes.Embedding.sobolevEmbL`: the embedding `H₀¹(Ω) →L[ℝ] L^q(Ω)` built from such an
  estimate, with `EllipticPdes.Embedding.coeFn_sobolevEmbL` identifying it with the function
  coordinate and `EllipticPdes.Embedding.norm_sobolevEmbL_le` bounding it by the gradient alone.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.1, Theorem 1; H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Corollary 9.9.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {p' : ℝ≥0}

/-- Mathlib's Gagliardo-Nirenberg-Sobolev constant at `p = 2` on `ℝ^d`. It depends on the
dimension and the exponent alone, not on the function or the domain. -/
def sobolevConst (d : ℕ) : ℝ≥0 :=
  SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin d))) ((2 : ℝ≥0) : ℝ)

/-- Mathlib's Gagliardo-Nirenberg-Sobolev constant at `p = 2` for an exponent `q` below the
critical one, on a domain of finite measure. -/
def sobolevConstOfLe (Ω : Set (EuclideanSpace ℝ (Fin d))) (q : ℝ≥0) : ℝ≥0 :=
  eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin d))) Ω 2 q

/-! ### The estimate on a test function -/

/-- A function supported in `Ω` has the same `Lᵖ` seminorm over `Ω` as over the whole space. -/
lemma eLpNorm_restrict_eq_of_tsupport_subset (hΩm : MeasurableSet Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : tsupport f ⊆ Ω) (p : ℝ≥0∞) :
    eLpNorm f p (volume.restrict Ω) = eLpNorm f p volume := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hΩm]
  refine eLpNorm_congr_ae (EventuallyEq.of_eq (funext fun x => ?_))
  by_cases hx : x ∈ Ω
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun hc => hx (hf hc))]

/-- The `L²` seminorm of the derivative of a test function is bounded by the sum of the `L²(Ω)`
norms of its graph's gradient coordinates. -/
lemma eLpNorm_fderiv_le_sum (hΩm : MeasurableSet Ω)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    eLpNorm (fderiv ℝ φ) 2 volume ≤ ∑ i : Fin d, ‖h.testGraph i.succ‖ₑ := by
  have hmeas : ∀ i : Fin d, AEStronglyMeasurable (partialD i φ) volume := fun i =>
    (h.continuous_partialD i).aestronglyMeasurable
  calc eLpNorm (fderiv ℝ φ) 2 volume
      ≤ eLpNorm (fun x => ∑ k : Fin d, ‖partialD k φ x‖) 2 volume := by
        refine eLpNorm_mono
          ((h.1.continuous_fderiv (by simp)).aestronglyMeasurable) (fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        exact norm_fderiv_le_sum_partialD φ x
    _ = eLpNorm (∑ k : Fin d, fun x => ‖partialD k φ x‖) 2 volume := by
        refine eLpNorm_congr_ae (EventuallyEq.of_eq (funext fun x => ?_))
        rw [Finset.sum_apply]
    _ ≤ ∑ k : Fin d, eLpNorm (fun x => ‖partialD k φ x‖) 2 volume :=
        eLpNorm_sum_le one_le_two
    _ = ∑ i : Fin d, ‖h.testGraph i.succ‖ₑ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [eLpNorm_norm _ (hmeas i), ← eLpNorm_restrict_eq_of_tsupport_subset hΩm
          ((tsupport_partialD_subset i φ).trans h.2.2) 2,
          IsTestFn.testGraph_succ, Lp.enorm_def, IsTestFn.partialCls]
        exact (eLpNorm_congr_ae (h.memLp_partialD i).coeFn_toLp).symm

/-- The function coordinate of a test graph is the test function. -/
lemma eLpNorm_testGraph_zero (q : ℝ≥0∞) {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    eLpNorm (h.testGraph 0 : L2D Ω) q (volume.restrict Ω) = eLpNorm φ q (volume.restrict Ω) := by
  rw [IsTestFn.testGraph_zero, IsTestFn.testCls]
  exact eLpNorm_congr_ae h.mem_lp.coeFn_toLp

/-- **Gagliardo-Nirenberg-Sobolev inequality on a test function**, read off the graph
coordinates: the `L^{2⋆}(Ω)` seminorm of the function coordinate is bounded by the sum of the
`L²(Ω)` norms of the gradient coordinates. -/
theorem eLpNorm_testGraph_le (hΩm : MeasurableSet Ω) (hd : 0 < d)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    eLpNorm (h.testGraph 0 : L2D Ω) p' (volume.restrict Ω)
      ≤ sobolevConst d * ∑ i : Fin d, ‖h.testGraph i.succ‖ₑ := by
  have hrank : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
    rw [finrank_euclideanSpace_fin]; exact hd
  have hp'' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹
      - (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ)⁻¹ := by
    rw [finrank_euclideanSpace_fin]; exact hp'
  calc eLpNorm (h.testGraph 0 : L2D Ω) p' (volume.restrict Ω)
      = eLpNorm φ p' (volume.restrict Ω) := eLpNorm_testGraph_zero _ h
    _ ≤ eLpNorm φ p' volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ sobolevConst d * eLpNorm (fderiv ℝ φ) 2 volume :=
        eLpNorm_le_eLpNorm_fderiv_of_eq volume (h.1.of_le (by simp)) h.2.1 one_le_two hrank hp''
    _ ≤ sobolevConst d * ∑ i : Fin d, ‖h.testGraph i.succ‖ₑ := by
        gcongr
        exact eLpNorm_fderiv_le_sum hΩm h

/-- **Gagliardo-Nirenberg-Sobolev inequality on a test function at a subcritical exponent.**
On a bounded domain the estimate is available at every `q` with `1/q ≥ 1/2 - 1/d`, the critical
exponent included, since the domain has finite measure. The dimension must exceed `2`, which is
what the critical exponent asks for. -/
theorem eLpNorm_testGraph_le_of_isBounded (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (hd : 2 < d) {q : ℝ≥0}
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    eLpNorm (h.testGraph 0 : L2D Ω) q (volume.restrict Ω)
      ≤ sobolevConstOfLe Ω q * ∑ i : Fin d, ‖h.testGraph i.succ‖ₑ := by
  have hrank : (2 : ℝ≥0) < (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ≥0) := by
    rw [finrank_euclideanSpace_fin]
    exact_mod_cast hd
  have hq' : ((2 : ℝ≥0) : ℝ)⁻¹
      - (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
    rw [finrank_euclideanSpace_fin]; exact hq
  calc eLpNorm (h.testGraph 0 : L2D Ω) q (volume.restrict Ω)
      = eLpNorm φ q (volume.restrict Ω) := eLpNorm_testGraph_zero _ h
    _ ≤ eLpNorm φ q volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ sobolevConstOfLe Ω q * eLpNorm (fderiv ℝ φ) 2 volume :=
        eLpNorm_le_eLpNorm_fderiv_of_le volume (h.1.of_le (by simp))
          ((subset_tsupport φ).trans h.2.2) one_le_two hrank hq' hΩb
    _ ≤ sobolevConstOfLe Ω q * ∑ i : Fin d, ‖h.testGraph i.succ‖ₑ := by
        gcongr
        exact eLpNorm_fderiv_le_sum hΩm h

/-! ### The transfer to `H₀¹(Ω)` -/

/-- Each coordinate of the graph is bounded by the ambient `H¹` norm. -/
lemma norm_apply_le (U : H1amb Ω) (j : Fin (d + 1)) : ‖U j‖ ≤ ‖U‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (U j)), ← Real.sqrt_sq (norm_nonneg U)]
  apply Real.sqrt_le_sqrt
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d + 1) => L2D Ω) U]
  exact Finset.single_le_sum (f := fun i : Fin (d + 1) => ‖U i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- **Transfer principle.** An estimate of the function coordinate by the gradient
coordinates, valid on every test graph, is valid on all of `H₀¹(Ω)`.

The two sides live at different exponents, so the estimate is not a closed condition on a
continuous function of the graph, as it is for the Poincaré inequality
(`EllipticPdes.Poincare.poincare_H01`). It is still lower semicontinuous: the test graphs
converging to `U` in `H¹` have function coordinates converging in `L²(Ω)`, hence in measure, and
Fatou's lemma passes the bound to the limit. -/
theorem eLpNorm_le_of_mem_H01_of_forall_testFn {q : ℝ≥0∞} {C : ℝ≥0}
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      eLpNorm (h.testGraph 0 : L2D Ω) q (volume.restrict Ω)
        ≤ C * ∑ i : Fin d, ‖h.testGraph i.succ‖ₑ)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    eLpNorm (U 0) q (volume.restrict Ω) ≤ C * ∑ i : Fin d, ‖U i.succ‖ₑ := by
  -- A sequence of test graphs converging to `U` in `H¹`.
  have hUcl : U ∈ closure
      ((Submodule.span ℝ (testGraphSet Ω) : Submodule ℝ (H1amb Ω)) : Set (H1amb Ω)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hU
  obtain ⟨V, hVmem, hVtend⟩ := mem_closure_iff_seq_limit.mp hUcl
  -- The estimate along the sequence, from the test-function case.
  have hVbound : ∀ n, eLpNorm (V n 0) q (volume.restrict Ω)
      ≤ C * ∑ i : Fin d, ‖V n i.succ‖ₑ := by
    intro n
    obtain ⟨φ, h, hφ⟩ : V n ∈ testGraphSet Ω := by
      have hmem := hVmem n
      rw [SetLike.mem_coe, span_testGraphSet] at hmem
      exact hmem
    rw [hφ]
    exact hbase h
  -- Every coordinate converges, the function coordinate in `L²(Ω)` hence in measure.
  have hconv : ∀ j : Fin (d + 1), Tendsto (fun n => V n j) atTop (𝓝 (U j)) := by
    intro j
    refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
      (fun n => ?_) (tendsto_iff_norm_sub_tendsto_zero.mp hVtend))
    have := norm_apply_le (V n - U) j
    simpa using this
  have hmeasure : TendstoInMeasure (volume.restrict Ω) (fun n => (V n 0 : _ → ℝ)) atTop (U 0) :=
    tendstoInMeasure_of_tendsto_Lp (hconv 0)
  -- The right-hand sides converge, so every strict upper bound of the limit bounds the tail.
  have hrhs : Tendsto (fun n => (C : ℝ≥0∞) * ∑ i : Fin d, ‖V n i.succ‖ₑ) atTop
      (𝓝 ((C : ℝ≥0∞) * ∑ i : Fin d, ‖U i.succ‖ₑ)) := by
    refine ENNReal.Tendsto.const_mul (tendsto_finsetSum _ (fun i _ => ?_))
      (Or.inr ENNReal.coe_ne_top)
    exact (continuous_enorm.tendsto (U i.succ)).comp (hconv i.succ)
  refine le_of_forall_gt_imp_ge_of_dense (fun b hb => ?_)
  refine eLpNorm_le_of_tendstoInMeasure ?_ hmeasure (fun n => (Lp.aestronglyMeasurable _))
  filter_upwards [hrhs.eventually_lt_const hb] with n hn
  exact (hVbound n).trans hn.le

/-- **Sobolev estimate on `H₀¹(Ω)` at the critical exponent.** -/
theorem eLpNorm_le_of_mem_H01 (hΩm : MeasurableSet Ω) (hd : 0 < d)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    eLpNorm (U 0) p' (volume.restrict Ω) ≤ sobolevConst d * ∑ i : Fin d, ‖U i.succ‖ₑ :=
  eLpNorm_le_of_mem_H01_of_forall_testFn (fun h => eLpNorm_testGraph_le hΩm hd hp' h) hU

/-- **Sobolev estimate on `H₀¹(Ω)` at every exponent up to the critical one**, on a bounded
domain. -/
theorem eLpNorm_le_of_mem_H01_of_isBounded (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (hd : 2 < d) {q : ℝ≥0}
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    eLpNorm (U 0) q (volume.restrict Ω) ≤ sobolevConstOfLe Ω q * ∑ i : Fin d, ‖U i.succ‖ₑ :=
  eLpNorm_le_of_mem_H01_of_forall_testFn
    (fun h => eLpNorm_testGraph_le_of_isBounded hΩm hΩb hd hq h) hU

/-- An element of `H₀¹(Ω)` is `L^q(Ω)` at any exponent the estimate reaches. -/
theorem memLp_of_mem_H01 {q : ℝ≥0∞} {C : ℝ≥0} {U : H1amb Ω}
    (hbound : eLpNorm (U 0) q (volume.restrict Ω) ≤ C * ∑ i : Fin d, ‖U i.succ‖ₑ) :
    MemLp (U 0) q (volume.restrict Ω) := by
  refine lt_of_le_of_lt hbound ?_
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  rw [Lp.enorm_def]
  exact (Lp.memLp (U i.succ)).eLpNorm_lt_top

/-! ### The embedding as a continuous linear map -/

section Bundled

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] {C : ℝ≥0}

/-- The sum of the gradient coordinates of an element of `H₀¹(Ω)`, bounded through the ambient
norm one coordinate at a time. -/
lemma sum_enorm_succ_le (U : H01 Ω) :
    ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ₑ ≤ ENNReal.ofReal (d * ‖U‖) := by
  have hnorm : ‖U‖ = ‖(U : H1amb Ω)‖ := rfl
  calc ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ₑ
      ≤ ∑ _i : Fin d, ENNReal.ofReal ‖(U : H1amb Ω)‖ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_apply_le _ _)
    _ = ENNReal.ofReal (d * ‖U‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (Nat.cast_nonneg d), hnorm]

/-- **Sobolev embedding `H₀¹(Ω) →L[ℝ] L^q(Ω)`**, built from an estimate of the function
coordinate by the gradient coordinates. The map sends an element of `H₀¹(Ω)` to its function
coordinate, read at the exponent `q`.

The operator-norm bound supplied here is `C * d`, from the coordinate bound `‖U i‖ ≤ ‖U‖` applied
`d` times. `norm_sobolevEmbL_le` states the sharper bound, by the gradient coordinates
themselves. -/
def sobolevEmbL (hbound : ∀ U : H1amb Ω, U ∈ H01 Ω →
      eLpNorm (U 0) q (volume.restrict Ω) ≤ C * ∑ i : Fin d, ‖U i.succ‖ₑ) :
    H01 Ω →L[ℝ] Lp ℝ q (volume.restrict Ω) :=
  LinearMap.mkContinuous
    { toFun := fun U => (memLp_of_mem_H01 (hbound (U : H1amb Ω) U.2)).toLp ((U : H1amb Ω) 0)
      map_add' := fun U V => by
        rw [MemLp.toLp_congr _ ((memLp_of_mem_H01 (hbound (U : H1amb Ω) U.2)).add
              (memLp_of_mem_H01 (hbound (V : H1amb Ω) V.2)))
            (show ⇑(((U + V : H01 Ω) : H1amb Ω) 0)
              =ᵐ[volume.restrict Ω] ⇑((U : H1amb Ω) 0) + ⇑((V : H1amb Ω) 0) from
              Lp.coeFn_add _ _),
          MemLp.toLp_add]
      map_smul' := fun c U => by
        rw [MemLp.toLp_congr _ ((memLp_of_mem_H01 (hbound (U : H1amb Ω) U.2)).const_smul c)
            (show ⇑(((c • U : H01 Ω) : H1amb Ω) 0)
              =ᵐ[volume.restrict Ω] c • ⇑((U : H1amb Ω) 0) from Lp.coeFn_smul _ _),
          MemLp.toLp_const_smul]
        rfl }
    (C * d) (fun U => by
      change ‖(memLp_of_mem_H01 (hbound (U : H1amb Ω) U.2)).toLp ((U : H1amb Ω) 0)‖
          ≤ (C * d) * ‖U‖
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      calc eLpNorm ((U : H1amb Ω) 0) q (volume.restrict Ω)
          ≤ C * ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ₑ := hbound (U : H1amb Ω) U.2
        _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (d * ‖U‖) := by
            gcongr
            exact sum_enorm_succ_le U
        _ = ENNReal.ofReal (C * d * ‖U‖) := by
            rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), mul_assoc])

@[simp] lemma coeFn_sobolevEmbL
    (hbound : ∀ U : H1amb Ω, U ∈ H01 Ω →
      eLpNorm (U 0) q (volume.restrict Ω) ≤ C * ∑ i : Fin d, ‖U i.succ‖ₑ) (U : H01 Ω) :
    ⇑(sobolevEmbL hbound U) =ᵐ[volume.restrict Ω] ⇑((U : H1amb Ω) 0) :=
  MemLp.coeFn_toLp (memLp_of_mem_H01 (hbound (U : H1amb Ω) U.2))

/-- The embedding is bounded by the gradient coordinates alone, with no Poincaré inequality and
no bound on the domain. -/
theorem norm_sobolevEmbL_le
    (hbound : ∀ U : H1amb Ω, U ∈ H01 Ω →
      eLpNorm (U 0) q (volume.restrict Ω) ≤ C * ∑ i : Fin d, ‖U i.succ‖ₑ) (U : H01 Ω) :
    ‖sobolevEmbL hbound U‖ ≤ C * ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ := by
  change ‖(memLp_of_mem_H01 (hbound (U : H1amb Ω) U.2)).toLp ((U : H1amb Ω) 0)‖
      ≤ C * ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖
  rw [Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (hbound (U : H1amb Ω) U.2).trans_eq ?_
  calc (C : ℝ≥0∞) * ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ₑ
      = ENNReal.ofReal (C : ℝ)
          * ENNReal.ofReal (∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖) := by
        rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
        exact congrArg _ (Finset.sum_congr rfl (fun i _ => (ofReal_norm _).symm))
    _ = ENNReal.ofReal (C * ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖) :=
        (ENNReal.ofReal_mul (by positivity)).symm

end Bundled

end EllipticPdes.Embedding
