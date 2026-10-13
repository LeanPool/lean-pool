/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.DivFreePairing

/-!
# WeakIBP

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The genuine weak integration by parts for the `D_h` splitting

Source: ABK26 (`e.sensitivity.basic.split`), second step.  For an a.e.
antisymmetric matrix field `h` with essentially bounded weak first derivatives
and every `u ∈ H¹₀(U)`, `w ∈ H¹(U)`,

  `∫ ∇u · h ∇w = -∫ u (∇·h) · ∇w`,  `(∇·h)_j = ∑ i ∂_i h_{ij}`.

This is the genuine weak integration by parts of the splitting identity: it
requires the test combination to lie in `H¹₀` (zero trace), in contrast to
the purely algebraic skew cancellation in `SkewCancellation.lean`.  The proof
first establishes the identity for smooth compactly supported tests through
the divergence-free pairing lemma
(`integral_euclideanGradient_dot_matVecMul_grad_eq_neg`), then closes it under
the `H¹₀` approximation package
(`integral_grad_dot_matVecMul_grad_eq_neg_of_hasWeakDeriv`).
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound

open HCPolySupport MeasureTheory Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The weak column divergence `(∇·h)_j = ∑ i ∂_i h_{ij}` assembled from
first-derivative data `Dh k x i j = ∂_k h_{ij} (x)`. -/
def matWeakDiv (Dh : Fin d → Vec d → Mat d) (x : Vec d) : Vec d :=
  fun j => ∑ i, Dh i x i j

/-- Bounded continuous functions are square integrable on a finite-volume
carrier. -/
theorem memScalarL2_of_continuous_of_bounded {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {g : Vec d → ℝ}
    (hgc : Continuous g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    MemScalarL2 U g :=
  MemLp.of_bound hgc.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hgb x)

/-- The weak-divergence pairing `x ↦ (∇·h)(x) · g(x)` expanded as a double
sum. -/
theorem vecDot_matWeakDiv_eq_sum {Dh : Fin d → Vec d → Mat d}
    {g : Vec d → Vec d} :
    (fun x => vecDot (matWeakDiv Dh x) (g x)) =
      fun x => ∑ j, ∑ i, Dh i x i j * g x j := by
  funext x
  unfold vecDot matWeakDiv
  exact Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _

/-- The weak-divergence pairing against an `L²` gradient is integrable from
square-integrable derivative data. -/
theorem integrable_vecDot_matWeakDiv {U : Set (Vec d)}
    {Dh : Fin d → Vec d → Mat d}
    (hDmem2 : ∀ k i j, MemScalarL2 U fun x => Dh k x i j)
    {g : Vec d → Vec d} (hg : ∀ j, MemScalarL2 U fun x => g x j) :
    Integrable (fun x => vecDot (matWeakDiv Dh x) (g x))
      (volumeMeasureOn U) := by
  rw [vecDot_matWeakDiv_eq_sum]
  exact integrable_finsetSum Finset.univ fun j _ =>
    integrable_finsetSum Finset.univ fun i _ =>
      (hDmem2 i i j).integrable_mul (hg j)

/-- The weak-divergence pairing is square integrable when the derivative data
is essentially bounded. -/
theorem memScalarL2_vecDot_matWeakDiv {U : Set (Vec d)}
    {Dh : Fin d → Vec d → Mat d}
    (hDmem : ∀ k i j, MemLp (fun x => Dh k x i j) ∞ (volumeMeasureOn U))
    {g : Vec d → Vec d} (hg : ∀ j, MemScalarL2 U fun x => g x j) :
    MemScalarL2 U (fun x => vecDot (matWeakDiv Dh x) (g x)) := by
  rw [vecDot_matWeakDiv_eq_sum]
  exact memLp_finsetSum Finset.univ fun j _ =>
    memLp_finsetSum Finset.univ fun i _ => (hDmem i i j).fun_mul (r := 2) (hg j)

/-- Coordinates of the skew-multiplied gradient are square integrable when the
matrix entries are essentially bounded. -/
theorem memScalarL2_matVecMul_coord {U : Set (Vec d)}
    {h : Vec d → Mat d}
    (hmem : ∀ i j, MemLp (fun x => h x i j) ∞ (volumeMeasureOn U))
    {g : Vec d → Vec d} (hg : ∀ j, MemScalarL2 U fun x => g x j) (i : Fin d) :
    MemScalarL2 U (fun x => matVecMul (h x) (g x) i) := by
  have hexp : (fun x => matVecMul (h x) (g x) i) =
      fun x => ∑ j, h x i j * g x j := rfl
  rw [hexp]
  exact memLp_finsetSum Finset.univ fun j _ => (hmem i j).fun_mul (r := 2) (hg j)

/-- **Weak integration by parts at a smooth compactly supported test.**  For
a.e. antisymmetric `h` with square-integrable weak first derivatives and every
smooth compactly supported `φ` with support in `U`,

  `∫ ∇φ · h ∇w = -∫ φ (∇·h) · ∇w`.

Only `L²` control of `h` and `Dh` is used at this stage. -/
theorem integral_euclideanGradient_dot_matVecMul_grad_eq_neg
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hUne : U.Nonempty)
    {h : Vec d → Mat d} {Dh : Fin d → Vec d → Mat d}
    (hskew : ∀ᵐ x ∂ volumeMeasureOn U, symmPart (h x) = 0)
    (hmem2 : ∀ i j, MemScalarL2 U fun x => h x i j)
    (hDmem2 : ∀ k i j, MemScalarL2 U fun x => Dh k x i j)
    (hweak : ∀ k i j,
      HasWeakPartialDerivOn U k (fun x => h x i j) fun x => Dh k x i j)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφsub : tsupport φ ⊆ U) (w : H1Function U) :
    ∫ x in U, vecDot (euclideanGradient φ x) (matVecMul (h x) (w.grad x))
        ∂MeasureTheory.volume =
      -∫ x in U, φ x * vecDot (matWeakDiv Dh x) (w.grad x)
        ∂MeasureTheory.volume := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  -- the skew test field pairing vanishes
  have hkey : ∫ x in U, vecDot (skewTestField h Dh φ x) (w.grad x)
      ∂MeasureTheory.volume = 0 :=
    integral_vecDot_grad_eq_zero_of_weak_div_free hU hUne
      (memScalarL2_skewTestField hmem2 hDmem2 hφ hφc) hφc hφsub
      (fun x hx => skewTestField_eq_zero_of_notMem_tsupport hx)
      (fun ψ hψ hψc hψsub =>
        sum_integral_skewTestField_mul_deriv_eq_zero hskew hmem2 hDmem2 hweak
          hφ hφc hψ hψc hψsub) w
  -- pointwise decomposition of the skew test field pairing
  have hpt : ∀ x,
      vecDot (skewTestField h Dh φ x) (w.grad x) =
        vecDot (euclideanGradient φ x) (matVecMul (h x) (w.grad x)) +
          φ x * vecDot (matWeakDiv Dh x) (w.grad x) := by
    intro x
    unfold vecDot skewTestField euclideanGradient matVecMul matWeakDiv
    rw [Finset.mul_sum]
    rw [show (∑ i, euclideanCoordDeriv i φ x *
          ∑ j, h x i j * w.grad x j) =
        ∑ i, ∑ j, euclideanCoordDeriv i φ x * (h x i j * w.grad x j) from
      Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _]
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- integrability of the two pieces
  obtain ⟨Cφ, hCφ⟩ :=
    exists_abs_bound_of_continuous_of_hasCompactSupport hφ.continuous hφc
  have hB_int : Integrable
      (fun x => φ x * vecDot (matWeakDiv Dh x) (w.grad x))
      (volumeMeasureOn U) :=
    (integrable_vecDot_matWeakDiv hDmem2 w.gradMemL2).bdd_mul
      hφ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hCφ x)
  have htotal_int : Integrable
      (fun x => vecDot (skewTestField h Dh φ x) (w.grad x))
      (volumeMeasureOn U) := by
    have hvec : MemVectorL2 U (skewTestField h Dh φ) := by
      rw [MemVectorL2]
      refine memLp_pi_iff.2 fun j => ?_
      exact memScalarL2_skewTestField hmem2 hDmem2 hφ hφc j
    exact integrableOn_vecDot_of_memVectorL2 hvec w.grad_memVectorL2
  have hA_int : Integrable
      (fun x => vecDot (euclideanGradient φ x) (matVecMul (h x) (w.grad x)))
      (volumeMeasureOn U) := by
    refine (htotal_int.sub hB_int).congr
      (Filter.Eventually.of_forall fun x => ?_)
    show vecDot (skewTestField h Dh φ x) (w.grad x) -
        φ x * vecDot (matWeakDiv Dh x) (w.grad x) =
      vecDot (euclideanGradient φ x) (matVecMul (h x) (w.grad x))
    rw [hpt x]
    ring
  -- split the vanishing integral
  have hsplit :
      (∫ x in U, vecDot (skewTestField h Dh φ x) (w.grad x)
          ∂MeasureTheory.volume) =
        (∫ x in U,
            vecDot (euclideanGradient φ x) (matVecMul (h x) (w.grad x))
            ∂MeasureTheory.volume) +
          ∫ x in U, φ x * vecDot (matWeakDiv Dh x) (w.grad x)
            ∂MeasureTheory.volume := by
    rw [← integral_add hA_int hB_int]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x)
  rw [hkey] at hsplit
  linarith

/-- **The genuine weak integration by parts for the `D_h` splitting.**  For an
a.e. antisymmetric matrix field `h` with essentially bounded entries and
essentially bounded weak first derivatives `Dh`, every `u ∈ H¹₀(U)` and every
`w ∈ H¹(U)` on an open bounded convex carrier satisfy

  `∫ ∇u · h ∇w = -∫ u (∇·h) · ∇w`.

The zero-trace hypothesis on `u` is the exact structural input demanded by the
source display `e.sensitivity.basic.split`; the response combination
`w + w* + ℓ_p` is inserted here once its `H¹₀` membership is provided. -/
theorem integral_grad_dot_matVecMul_grad_eq_neg_of_hasWeakDeriv
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hUne : U.Nonempty)
    {h : Vec d → Mat d} {Dh : Fin d → Vec d → Mat d}
    (hskew : ∀ᵐ x ∂ volumeMeasureOn U, symmPart (h x) = 0)
    (hmem : ∀ i j, MemLp (fun x => h x i j) ∞ (volumeMeasureOn U))
    (hDmem : ∀ k i j, MemLp (fun x => Dh k x i j) ∞ (volumeMeasureOn U))
    (hweak : ∀ k i j,
      HasWeakPartialDerivOn U k (fun x => h x i j) fun x => Dh k x i j)
    (u : H10Function U) (w : H1Function U) :
    ∫ x in U,
        vecDot (u.toH1Function.grad x) (matVecMul (h x) (w.grad x))
        ∂MeasureTheory.volume =
      -∫ x in U,
          u.toH1Function.toFun x * vecDot (matWeakDiv Dh x) (w.grad x)
          ∂MeasureTheory.volume := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hmem2 : ∀ i j, MemScalarL2 U fun x => h x i j := fun i j =>
    (hmem i j).mono_exponent le_top
  have hDmem2 : ∀ k i j, MemScalarL2 U fun x => Dh k x i j := fun k i j =>
    (hDmem k i j).mono_exponent le_top
  -- fixed L² factors
  have hHg : ∀ i, MemScalarL2 U (fun x => matVecMul (h x) (w.grad x) i) :=
    memScalarL2_matVecMul_coord hmem w.gradMemL2
  have hDg : MemScalarL2 U (fun x => vecDot (matWeakDiv Dh x) (w.grad x)) :=
    memScalarL2_vecDot_matWeakDiv hDmem w.gradMemL2
  -- L² data for the approximating sequence
  have happrox_mem : ∀ n, MemScalarL2 U (u.approx n) := fun n => by
    obtain ⟨C, hC⟩ :=
      exists_abs_bound_of_continuous_of_hasCompactSupport
        (u.approx_smooth n).continuous (u.approx_hasCompactSupport n)
    exact memScalarL2_of_continuous_of_bounded (u.approx_smooth n).continuous hC
  have happrox_grad_mem : ∀ n i,
      MemScalarL2 U (fun x => euclideanCoordDeriv i (u.approx n) x) := by
    intro n i
    obtain ⟨C, hC⟩ :=
      exists_abs_bound_of_continuous_of_hasCompactSupport
        (contDiff_euclideanCoordDeriv (u.approx_smooth n) i).continuous
        (hasCompactSupport_euclideanCoordDeriv (u.approx_hasCompactSupport n) i)
    exact memScalarL2_of_continuous_of_bounded
      (contDiff_euclideanCoordDeriv (u.approx_smooth n) i).continuous hC
  -- the smooth identity along the approximating sequence
  have hIBP : ∀ n,
      (∫ x in U,
          vecDot (euclideanGradient (u.approx n) x)
            (matVecMul (h x) (w.grad x)) ∂MeasureTheory.volume) =
        -∫ x in U,
            u.approx n x * vecDot (matWeakDiv Dh x) (w.grad x)
            ∂MeasureTheory.volume := fun n =>
    integral_euclideanGradient_dot_matVecMul_grad_eq_neg hU hUne hskew hmem2
      hDmem2 hweak (u.approx_smooth n) (u.approx_hasCompactSupport n)
      (u.approx_support_subset n) w
  -- limit of the gradient side
  have hL_coord : ∀ i : Fin d,
      Tendsto (fun n =>
          ∫ x in U,
            matVecMul (h x) (w.grad x) i * euclideanCoordDeriv i (u.approx n) x
            ∂MeasureTheory.volume)
        atTop
        (nhds (∫ x in U,
          matVecMul (h x) (w.grad x) i * u.toH1Function.grad x i
          ∂MeasureTheory.volume)) := by
    intro i
    refine tendsto_integral_mul_of_tendsto_toScalarL2 (hHg i)
      (fun n => happrox_grad_mem n i) (u.toH1Function.gradMemL2 i) ?_
    refine tendsto_toScalarL2_of_tendsto_eLpNorm
      (fun n => happrox_grad_mem n i) (u.toH1Function.gradMemL2 i) ?_
    have htend := u.tendsto_approx_grad i
    simpa [euclideanCoordDeriv, volumeMeasureOn] using htend
  -- limit of the function side
  have hR : Tendsto (fun n =>
        ∫ x in U,
          vecDot (matWeakDiv Dh x) (w.grad x) * u.approx n x
          ∂MeasureTheory.volume)
      atTop
      (nhds (∫ x in U,
        vecDot (matWeakDiv Dh x) (w.grad x) * u.toH1Function.toFun x
        ∂MeasureTheory.volume)) := by
    refine tendsto_integral_mul_of_tendsto_toScalarL2 hDg happrox_mem
      u.toH1Function.memL2 ?_
    refine tendsto_toScalarL2_of_tendsto_eLpNorm happrox_mem
      u.toH1Function.memL2 ?_
    simpa [volumeMeasureOn] using u.tendsto_approx
  -- assemble the gradient-side limit into the vector pairing
  have hgrad_int : ∀ n i, Integrable
      (fun x =>
        matVecMul (h x) (w.grad x) i * euclideanCoordDeriv i (u.approx n) x)
      (volumeMeasureOn U) := fun n i =>
    (hHg i).integrable_mul (happrox_grad_mem n i)
  have hgradU_int : ∀ i, Integrable
      (fun x => matVecMul (h x) (w.grad x) i * u.toH1Function.grad x i)
      (volumeMeasureOn U) := fun i =>
    (hHg i).integrable_mul (u.toH1Function.gradMemL2 i)
  have hL : Tendsto (fun n =>
        ∫ x in U,
          vecDot (euclideanGradient (u.approx n) x)
            (matVecMul (h x) (w.grad x)) ∂MeasureTheory.volume)
      atTop
      (nhds (∫ x in U,
        vecDot (u.toH1Function.grad x) (matVecMul (h x) (w.grad x))
        ∂MeasureTheory.volume)) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d))
      fun i _ => hL_coord i
    have hseq_eq : ∀ n,
        (∑ i, ∫ x in U,
          matVecMul (h x) (w.grad x) i * euclideanCoordDeriv i (u.approx n) x
          ∂MeasureTheory.volume) =
          ∫ x in U,
            vecDot (euclideanGradient (u.approx n) x)
              (matVecMul (h x) (w.grad x)) ∂MeasureTheory.volume := by
      intro n
      rw [← integral_finsetSum Finset.univ fun i _ => hgrad_int n i]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, matVecMul (h x) (w.grad x) i *
          euclideanCoordDeriv i (u.approx n) x) =
        vecDot (euclideanGradient (u.approx n) x) (matVecMul (h x) (w.grad x))
      unfold vecDot euclideanGradient
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hlim_eq :
        (∑ i, ∫ x in U,
          matVecMul (h x) (w.grad x) i * u.toH1Function.grad x i
          ∂MeasureTheory.volume) =
          ∫ x in U,
            vecDot (u.toH1Function.grad x) (matVecMul (h x) (w.grad x))
            ∂MeasureTheory.volume := by
      rw [← integral_finsetSum Finset.univ fun i _ => hgradU_int i]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, matVecMul (h x) (w.grad x) i * u.toH1Function.grad x i) =
        vecDot (u.toH1Function.grad x) (matVecMul (h x) (w.grad x))
      unfold vecDot
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← hlim_eq]
    refine hsum.congr fun n => hseq_eq n
  -- convert the function-side limit to the stated order
  have hR' : Tendsto (fun n =>
        ∫ x in U,
          u.approx n x * vecDot (matWeakDiv Dh x) (w.grad x)
          ∂MeasureTheory.volume)
      atTop
      (nhds (∫ x in U,
        u.toH1Function.toFun x * vecDot (matWeakDiv Dh x) (w.grad x)
        ∂MeasureTheory.volume)) := by
    have hcomm : ∀ n,
        (∫ x in U,
          vecDot (matWeakDiv Dh x) (w.grad x) * u.approx n x
          ∂MeasureTheory.volume) =
          ∫ x in U,
            u.approx n x * vecDot (matWeakDiv Dh x) (w.grad x)
            ∂MeasureTheory.volume := fun n =>
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    have hcommU :
        (∫ x in U,
          vecDot (matWeakDiv Dh x) (w.grad x) * u.toH1Function.toFun x
          ∂MeasureTheory.volume) =
          ∫ x in U,
            u.toH1Function.toFun x * vecDot (matWeakDiv Dh x) (w.grad x)
            ∂MeasureTheory.volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [← hcommU]
    exact hR.congr fun n => hcomm n
  -- both limits agree along the identity
  have hL' : Tendsto (fun n =>
        -∫ x in U,
          u.approx n x * vecDot (matWeakDiv Dh x) (w.grad x)
          ∂MeasureTheory.volume)
      atTop
      (nhds (∫ x in U,
        vecDot (u.toH1Function.grad x) (matVecMul (h x) (w.grad x))
        ∂MeasureTheory.volume)) := by
    refine hL.congr fun n => ?_
    rw [hIBP n]
  exact tendsto_nhds_unique hL' hR'.neg

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound
