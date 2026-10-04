/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Local.WeakSolution


/-!
# Cutoff reduction of a local weak solution to an `H₀¹` problem

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 1, step 1 tests the equation
against `-D_k^{-h}(ζ² D_k^h u)`, which is admissible for `u ∈ H¹(U)` because the cutoff `ζ`
removes the boundary. This file uses the same cutoff differently: for a local weak solution
`U ∈ W12 Ω` and a test function `η` of `Ω`, the product `η U` lies in `H₀¹(Ω)`
(`cutoffMul_mem_H01_of_mem_W12`) and solves `B[η U, w] = ∫ F w` for every `w ∈ H₀¹(Ω)`, with

`F = η f − Σ a_{ij} ∂_j η U_i − Σ ∂_j a_{ij} ∂_i η U_0 − Σ a_{ij} ∂_i η U_j`
`    − Σ a_{ij} ∂_{ij} η U_0 + Σ b_i ∂_i η U_0`.

Every term of `F` is in `L²(Ω)` with a bound in `‖f‖` and `‖U‖`, so the interior chain for
`H₀¹` solutions applies to `η U` unchanged, and `η = 1` near the set of interest makes the
cutoff invisible in its conclusion.

The derivative `∂_j a_{ij}` enters through one integration by parts, the only place a derivative
of a coefficient appears. `CoeffWeakGrad` records what that step needs: a weak partial derivative
of each entry, measurable and essentially bounded. Both a `C¹` bundle
(`IsC1Coeff.coeffWeakGrad`) and a `W^{k+1,∞}` bundle (`IsWkInftyCoeff.coeffWeakGrad`) supply it,
so one reduction serves the `H²` estimate and the higher-order induction.

## Main declarations

* `CoeffWeakGrad`, `IsC1Coeff.coeffWeakGrad`, `IsWkInftyCoeff.coeffWeakGrad`.
* `principal_leibniz`: the integration by parts moving `∂_j` off the test function.
* `reduction_testFn`: the reduced identity against test functions.
* `redDatum`, `reduction_weakForm`: the datum as an `L²(Ω)` class, and the identity on `H₀¹(Ω)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Extension

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- **Weak gradient of the principal coefficients.** For each direction `l` and entry `(i, j)`,
a measurable function `da l i j`, essentially bounded by one constant, that is the weak partial
derivative of `a_{ij}` in direction `l`. This is all the cutoff reduction asks of the principal
part beyond `FullEllipticOp`. -/
structure CoeffWeakGrad (A : EllipticCoeff d) where
  /-- The weak partial derivative `∂_l a_{ij}`, indexed as `da l i j`. -/
  da : Fin d → Fin d → Fin d → EuclideanSpace ℝ (Fin d) → ℝ
  /-- Every derivative is measurable. -/
  measurable : ∀ l i j, Measurable (da l i j)
  /-- The common essential bound. -/
  bound : ℝ
  /-- Every derivative is essentially bounded by `bound`. -/
  ae_abs_le : ∀ l i j,
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |da l i j x| ≤ bound
  /-- `da l i j` is the weak partial derivative of `a_{ij}` in direction `l`. -/
  hasWeakPartial : ∀ l i j, HasWeakPartial l (fun x => A.a x i j) (da l i j)

/-- Pointwise bound on a partial of a `C¹` coefficient. -/
theorem IsC1Coeff.abs_partialD_le {A : EllipticCoeff d} (hA : IsC1Coeff A) (i j k : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : |partialD k (fun y => A.a y i j) x| ≤ hA.A1 := by
  have h := (fderiv ℝ (fun y => A.a y i j) x).le_opNorm (EuclideanSpace.single k 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  exact (Real.norm_eq_abs _ ▸ h).trans (hA.grad_bdd i j x)

/-- A partial of a `C¹` coefficient is measurable, being continuous. -/
theorem IsC1Coeff.measurable_partialD {A : EllipticCoeff d} (hA : IsC1Coeff A)
    (i j k : Fin d) : Measurable (partialD k (fun y => A.a y i j)) :=
  (((hA.contDiff i j).continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable

/-- The classical partials of a `C¹` coefficient are its weak partials. -/
def IsC1Coeff.coeffWeakGrad {A : EllipticCoeff d} (hA : IsC1Coeff A) : CoeffWeakGrad A where
  da l i j := partialD l (fun y => A.a y i j)
  measurable l i j := hA.measurable_partialD i j l
  bound := hA.A1
  ae_abs_le l i j := Eventually.of_forall (hA.abs_partialD_le i j l)
  hasWeakPartial l i j := hasWeakPartial_partialD (hA.contDiff i j) l

/-- The first-order members of a `W^{k+1,∞}` family are weak partials of the coefficient. -/
def IsWkInftyCoeff.coeffWeakGrad {A : EllipticCoeff d} {k : ℕ}
    (hA : IsWkInftyCoeff A (k + 1)) : CoeffWeakGrad A where
  da l i j := hA.D [l] i j
  measurable l i j := hA.D_meas i j [l] (by simp)
  bound := hA.bound 1
  ae_abs_le l i j := hA.ess_bdd i j [l] (by simp)
  hasWeakPartial l i j := by
    have h := hA.D_step i j l [] (Nat.succ_pos k)
    rwa [hA.D_nil i j] at h

/-- A bounded measurable weight times an `L²(Ω)` class times a continuous compactly supported
function is integrable on `Ω`. -/
theorem integrable_weight_L2D_mul {g : L2D Ω} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcm : Measurable c) {M : ℝ}
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ M)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    Integrable (fun x => c x * (g x : ℝ) * ψ x) (volume.restrict Ω) := by
  have h := (integrable_L2D_mul (g := g) hψ hψcs).bdd_mul (c := M) hcm.aestronglyMeasurable
    (ae_restrict_of_ae (hc.mono fun x hx => by simpa [Real.norm_eq_abs] using hx))
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only; ring

/-- **Integration by parts on the principal term.** The term `∫ a_{ij} U₀ ∂_i η ∂_j v` with the
derivative moved off `v`. It is the only place a derivative of a coefficient enters, and it is
taken in the weak sense through `HasWeakDerivOn.mul_isWkInfty_left`, so the test function stays
smooth and `Ω` need not have finite measure. -/
theorem principal_leibniz (Op : FullEllipticOp d) (D : CoeffWeakGrad Op.toEllipticCoeff)
    {U : H1amb Ω} (hU : U ∈ W12 Ω) (i j : Fin d)
    {η v : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) (hv : IsTestFn Ω v) :
    ∫ x in Ω, Op.a x i j * (U 0 x : ℝ) * (partialD i η x * partialD j v x)
      = -(∫ x in Ω, D.da j i j x * (U 0 x : ℝ) * (partialD i η x * v x))
        - (∫ x in Ω, Op.a x i j * (U j.succ x : ℝ) * (partialD i η x * v x))
        - ∫ x in Ω, Op.a x i j * (U 0 x : ℝ) * (partialD j (partialD i η) x * v x) := by
  classical
  have hdi : IsTestFn Ω (partialD i η) := isTestFn_partialD hη i
  have hψ : IsTestFn Ω (fun x => partialD i η x * v x) := isTestFn_mul hdi hv
  set dag : L2D Ω :=
    mulCoeffL (D.measurable j i j) (ae_restrict_of_ae (D.ae_abs_le j i j)) (U 0)
      + Op.toEllipticCoeff.actL i j (U j.succ) with hdag
  have hdagae : dag =ᵐ[volume.restrict Ω]
      fun x => D.da j i j x * (U 0 x : ℝ) + Op.a x i j * (U j.succ x : ℝ) := by
    filter_upwards [Lp.coeFn_add (mulCoeffL (D.measurable j i j)
        (ae_restrict_of_ae (D.ae_abs_le j i j)) (U 0))
        (Op.toEllipticCoeff.actL i j (U j.succ)),
      mulCoeffL_coeFn (D.measurable j i j) (ae_restrict_of_ae (D.ae_abs_le j i j)) (U 0),
      Op.toEllipticCoeff.actL_coeFn i j (U j.succ)] with x h1 h2 h3
    rw [hdag, h1, Pi.add_apply, h2, h3]
  have hwd := HasWeakDerivOn.mul_isWkInfty_left j (hasWeakDerivOn_of_mem_W12 hU j)
    (Op.measurable i j) (D.measurable j i j) (D.hasWeakPartial j i j) (Op.bdd i j)
    (D.ae_abs_le j i j) (Op.toEllipticCoeff.actL i j (U 0))
    (Op.toEllipticCoeff.actL_coeFn i j (U 0)) dag hdagae
  have key := hwd _ hψ.1 hψ.2.1 hψ.2.2
  rw [partialD_mul (hdi.1.differentiable (by simp)) (hv.1.differentiable (by simp)) j] at key
  have hdiv : Continuous (partialD i η) := hη.continuous_partialD i
  have hdjv : Continuous (partialD j v) := hv.continuous_partialD j
  have hdji : Continuous (partialD j (partialD i η)) := hdi.continuous_partialD j
  have i1 := integrable_weight_L2D_mul (g := U 0)
    (ψ := fun x => partialD i η x * partialD j v x) (Op.measurable i j) (Op.bdd i j)
    (hdiv.mul hdjv) (hv.hasCompactSupport_partialD j).mul_left
  have i2 := integrable_weight_L2D_mul (g := U 0)
    (ψ := fun x => partialD j (partialD i η) x * v x) (Op.measurable i j) (Op.bdd i j)
    (hdji.mul hv.continuous) hv.2.1.mul_left
  have i3 := integrable_weight_L2D_mul (g := U 0) (ψ := fun x => partialD i η x * v x)
    (D.measurable j i j) (D.ae_abs_le j i j) (hdiv.mul hv.continuous) hv.2.1.mul_left
  have i4 := integrable_weight_L2D_mul (g := U j.succ) (ψ := fun x => partialD i η x * v x)
    (Op.measurable i j) (Op.bdd i j) (hdiv.mul hv.continuous) hv.2.1.mul_left
  have hL : ∫ x in Ω, (Op.toEllipticCoeff.actL i j (U 0) x : ℝ)
        * (partialD i η x * partialD j v x + partialD j (partialD i η) x * v x)
      = (∫ x in Ω, Op.a x i j * (U 0 x : ℝ) * (partialD i η x * partialD j v x))
        + ∫ x in Ω, Op.a x i j * (U 0 x : ℝ) * (partialD j (partialD i η) x * v x) := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [Op.toEllipticCoeff.actL_coeFn i j (U 0)] with x hx
    rw [hx]; ring
  have hR : ∫ x in Ω, (dag x : ℝ) * (partialD i η x * v x)
      = (∫ x in Ω, D.da j i j x * (U 0 x : ℝ) * (partialD i η x * v x))
        + ∫ x in Ω, Op.a x i j * (U j.succ x : ℝ) * (partialD i η x * v x) := by
    rw [← integral_add i3 i4]
    refine integral_congr_ae ?_
    filter_upwards [hdagae] with x hx
    rw [hx]; ring
  rw [hL, hR] at key
  linarith [key]

/-- **Cutoff reduction against test functions.** For a local weak solution `U ∈ W12 Ω` and a
test function `η` of `Ω`, the element `η U ∈ H₀¹(Ω)` satisfies `B[η U, v] = ∫ F v` for every
test function `v`, with `F` spelled out as separate integrals. -/
theorem reduction_testFn (Op : FullEllipticOp d) (hΩo : IsOpen Ω)
    (D : CoeffWeakGrad Op.toEllipticCoeff) {U : H1amb Ω} {f : L2D Ω}
    (hsol : IsLocalWeakSolution Op Ω U f) {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : IsTestFn Ω v) :
    Op.fullBilin Ω ⟨cutoffMul hη U, cutoffMul_mem_H01_of_mem_W12 hΩo hη hsol.1⟩
        ⟨hv.testGraph, testGraph_mem_H01 hv⟩
      = (∫ x in Ω, (f x : ℝ) * (η x * v x))
        - (∑ i : Fin d, ∑ j : Fin d,
            ∫ x in Ω, Op.a x i j * (U i.succ x : ℝ) * (partialD j η x * v x))
        - (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω,
            D.da j i j x * (U 0 x : ℝ) * (partialD i η x * v x))
        - (∑ i : Fin d, ∑ j : Fin d,
            ∫ x in Ω, Op.a x i j * (U j.succ x : ℝ) * (partialD i η x * v x))
        - (∑ i : Fin d, ∑ j : Fin d,
            ∫ x in Ω, Op.a x i j * (U 0 x : ℝ) * (partialD j (partialD i η) x * v x))
        + (∑ i : Fin d, ∫ x in Ω, Op.b x i * (U 0 x : ℝ) * (partialD i η x * v x)) := by
  classical
  set W : H01 Ω := ⟨cutoffMul hη U, cutoffMul_mem_H01_of_mem_W12 hΩo hη hsol.1⟩ with hWdef
  have hW0 : ((W : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => η x * (U 0 x : ℝ) := by
    change ((cutoffMul hη U) 0 : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[_] _
    rw [cutoffMul_apply_zero]; exact mulTest_coeFn hη (U 0)
  have hWs : ∀ i : Fin d, ((W : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω]
        fun x => η x * (U i.succ x : ℝ) + partialD i η x * (U 0 x : ℝ) := by
    intro i
    change ((cutoffMul hη U) i.succ : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[_] _
    rw [cutoffMul_apply_succ]
    filter_upwards [Lp.coeFn_add (mulTest hη (U i.succ)) (mulTestPartial hη i (U 0)),
      mulTest_coeFn hη (U i.succ), mulTestPartial_coeFn hη i (U 0)] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  have hηv : IsTestFn Ω (fun x => η x * v x) := isTestFn_mul hη hv
  have hloc := hsol.2 _ hηv
  rw [pairL_testGraph_eq] at hloc
  simp only [partialD_mul (hη.1.differentiable (by simp)) (hv.1.differentiable (by simp))]
    at hloc
  have hηc := hη.continuous
  have hvc := hv.continuous
  have hdη : ∀ i, Continuous (partialD i η) := hη.continuous_partialD
  have hdv : ∀ j, Continuous (partialD j v) := hv.continuous_partialD
  -- Principal terms, one pair at a time.
  have hprin : ∀ i j : Fin d,
      ∫ x in Ω, Op.a x i j * ((W : H1amb Ω) i.succ x : ℝ) * partialD j v x
        = (∫ x in Ω, Op.a x i j * (U i.succ x : ℝ)
              * (η x * partialD j v x + partialD j η x * v x))
          - (∫ x in Ω, Op.a x i j * (U i.succ x : ℝ) * (partialD j η x * v x))
          + (-(∫ x in Ω, D.da j i j x * (U 0 x : ℝ) * (partialD i η x * v x))
            - (∫ x in Ω, Op.a x i j * (U j.succ x : ℝ) * (partialD i η x * v x))
            - ∫ x in Ω, Op.a x i j * (U 0 x : ℝ) * (partialD j (partialD i η) x * v x)) := by
    intro i j
    rw [← principal_leibniz Op D hsol.1 i j hη hv]
    have j1 := integrable_weight_L2D_mul (g := U i.succ)
      (ψ := fun x => η x * partialD j v x + partialD j η x * v x)
      (Op.measurable i j) (Op.bdd i j) ((hηc.mul (hdv j)).add ((hdη j).mul hvc))
      (((hv.hasCompactSupport_partialD j).mul_left).add hv.2.1.mul_left)
    have j2 := integrable_weight_L2D_mul (g := U i.succ) (ψ := fun x => partialD j η x * v x)
      (Op.measurable i j) (Op.bdd i j) ((hdη j).mul hvc) hv.2.1.mul_left
    have j3 := integrable_weight_L2D_mul (g := U 0)
      (ψ := fun x => partialD i η x * partialD j v x) (Op.measurable i j) (Op.bdd i j)
      ((hdη i).mul (hdv j)) (hv.hasCompactSupport_partialD j).mul_left
    have e : ∫ x in Ω, Op.a x i j * ((W : H1amb Ω) i.succ x : ℝ) * partialD j v x
        = ∫ x in Ω, ((Op.a x i j * (U i.succ x : ℝ)
              * (η x * partialD j v x + partialD j η x * v x)
            - Op.a x i j * (U i.succ x : ℝ) * (partialD j η x * v x))
            + Op.a x i j * (U 0 x : ℝ) * (partialD i η x * partialD j v x)) := by
      refine integral_congr_ae ?_
      filter_upwards [hWs i] with x hx
      rw [hx]; ring
    have j12 : Integrable (fun x =>
        Op.a x i j * (U i.succ x : ℝ) * (η x * partialD j v x + partialD j η x * v x)
          - Op.a x i j * (U i.succ x : ℝ) * (partialD j η x * v x)) (volume.restrict Ω) :=
      j1.sub j2
    rw [e, integral_add j12 j3, integral_sub j1 j2]
  have htrans : ∀ i : Fin d,
      ∫ x in Ω, Op.b x i * ((W : H1amb Ω) i.succ x : ℝ) * v x
        = (∫ x in Ω, Op.b x i * (U i.succ x : ℝ) * (η x * v x))
          + ∫ x in Ω, Op.b x i * (U 0 x : ℝ) * (partialD i η x * v x) := by
    intro i
    have j1 := integrable_weight_L2D_mul (g := U i.succ) (ψ := fun x => η x * v x)
      (Op.b_meas i) (Op.b_bdd i) (hηc.mul hvc) hv.2.1.mul_left
    have j2 := integrable_weight_L2D_mul (g := U 0) (ψ := fun x => partialD i η x * v x)
      (Op.b_meas i) (Op.b_bdd i) ((hdη i).mul hvc) hv.2.1.mul_left
    rw [← integral_add j1 j2]
    refine integral_congr_ae ?_
    filter_upwards [hWs i] with x hx
    rw [hx]; ring
  have hzero : ∫ x in Ω, Op.c x * ((W : H1amb Ω) 0 x : ℝ) * v x
      = ∫ x in Ω, Op.c x * (U 0 x : ℝ) * (η x * v x) := by
    refine integral_congr_ae ?_
    filter_upwards [hW0] with x hx
    rw [hx]; ring
  rw [fullBilin_testGraph_eq, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      hprin i j, Finset.sum_congr rfl fun i _ => htrans i, hzero]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linarith [hloc]

/-! ### The datum as an `L²(Ω)` class -/

/-- Multiplication by `c · ψ` on `L²(Ω)`, for `c` essentially bounded and `ψ` continuous with
compact support. -/
def weightL (Ω : Set (EuclideanSpace ℝ (Fin d))) {c ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcm : Measurable c) {M : ℝ}
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ M)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (f := fun x => c x * ψ x) (hcm.mul hψ.measurable)
    (M := max M 0 * (hψcs.exists_bound_of_continuous hψ).choose)
    (ae_restrict_of_ae (hc.mono fun x hx => by
      have hK := (hψcs.exists_bound_of_continuous hψ).choose_spec
      rw [abs_mul]
      exact mul_le_mul (le_max_of_le_left hx) (by simpa [Real.norm_eq_abs] using hK x)
        (abs_nonneg _) (le_max_right _ _)))

theorem weightL_bound_nonneg {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : Continuous ψ)
    (hψcs : HasCompactSupport ψ) {M : ℝ} :
    0 ≤ max M 0 * (hψcs.exists_bound_of_continuous hψ).choose :=
  mul_nonneg (le_max_right _ _)
    (le_trans (norm_nonneg _) ((hψcs.exists_bound_of_continuous hψ).choose_spec 0))

theorem norm_weightL_le {c ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcm : Measurable c) {M : ℝ}
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ M)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) (g : L2D Ω) :
    ‖weightL Ω hcm hc hψ hψcs g‖
      ≤ (max M 0 * (hψcs.exists_bound_of_continuous hψ).choose) * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

theorem inner_weightL_testCls {c ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcm : Measurable c) {M : ℝ}
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ M)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) (g : L2D Ω)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : IsTestFn Ω v) :
    ⟪weightL Ω hcm hc hψ hψcs g, hv.testCls⟫ = ∫ x in Ω, c x * (g x : ℝ) * (ψ x * v x) := by
  rw [weightL, inner_mulCoeffL_eq]
  refine integral_congr_ae ?_
  filter_upwards [hv.mem_lp.coeFn_toLp] with x hx
  rw [IsTestFn.testCls, hx]; ring

theorem inner_testCls_eq {g : L2D Ω} {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : IsTestFn Ω v) :
    ⟪g, hv.testCls⟫ = ∫ x in Ω, (g x : ℝ) * v x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hv.mem_lp.coeFn_toLp] with x hx
  rw [Real.inner_apply, IsTestFn.testCls, hx, mul_comm]

section Datum

variable (Op : FullEllipticOp d) (D : CoeffWeakGrad Op.toEllipticCoeff)
  {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η)

/-- **Reduction datum** `F` for `η U`, as an `L²(Ω)` class: each term is a bounded weight
supported in `tsupport η` against `f`, `U₀` or a gradient coordinate of `U`. -/
def redDatum (U : H1amb Ω) (f : L2D Ω) : L2D Ω :=
  mulTest hη f
    - (∑ i : Fin d, ∑ j : Fin d, weightL Ω (Op.measurable i j) (Op.bdd i j)
        (hη.continuous_partialD j) (hη.hasCompactSupport_partialD j) (U i.succ))
    - (∑ i : Fin d, ∑ j : Fin d, weightL Ω (D.measurable j i j) (D.ae_abs_le j i j)
        (hη.continuous_partialD i) (hη.hasCompactSupport_partialD i) (U 0))
    - (∑ i : Fin d, ∑ j : Fin d, weightL Ω (Op.measurable i j) (Op.bdd i j)
        (hη.continuous_partialD i) (hη.hasCompactSupport_partialD i) (U j.succ))
    - (∑ i : Fin d, ∑ j : Fin d, weightL Ω (Op.measurable i j) (Op.bdd i j)
        ((isTestFn_partialD hη i).continuous_partialD j)
        ((isTestFn_partialD hη i).hasCompactSupport_partialD j) (U 0))
    + (∑ i : Fin d, weightL Ω (Op.b_meas i) (Op.b_bdd i)
        (hη.continuous_partialD i) (hη.hasCompactSupport_partialD i) (U 0))

/-- **Cutoff reduction on `H₀¹(Ω)`.** For a local weak solution `U ∈ W12 Ω` and a test function
`η` of `Ω`, `B[η U, w] = ∫ F w` for every `w ∈ H₀¹(Ω)`, with `F = redDatum`. -/
theorem reduction_weakForm (hΩo : IsOpen Ω) {U : H1amb Ω} {f : L2D Ω}
    (hsol : IsLocalWeakSolution Op Ω U f) (w : H01 Ω) :
    Op.fullBilin Ω ⟨cutoffMul hη U, cutoffMul_mem_H01_of_mem_W12 hΩo hη hsol.1⟩ w
      = ∫ x in Ω, (redDatum Op D hη U f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ) := by
  refine weakForm_of_testFn Op _ _ (fun v hv => ?_) w
  rw [reduction_testFn Op hΩo D hsol hη hv, ← inner_testCls_eq hv, redDatum]
  simp only [inner_add_left, inner_sub_left, sum_inner, inner_weightL_testCls]
  rw [inner_testCls_eq hv]
  have h0 : ∫ x in Ω, ((mulTest hη f) x : ℝ) * v x = ∫ x in Ω, (f x : ℝ) * (η x * v x) := by
    refine integral_congr_ae ?_
    filter_upwards [mulTest_coeFn hη f] with x hx
    rw [hx]; ring
  rw [h0]

end Datum

end EllipticPdes.Regularity
