/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DirichletSolvability
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.VectorPairing

/-!
# SolutionCoefficientContinuity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The solution depends continuously on the coefficient field

Two Dirichlet solutions on `y + □_n` for the *same* forcing field but different
coefficient fields differ, in the energy norm, by at most the supremum distance
of the coefficient fields times the energy of one of them:

```text
  ‖∇(u_a − u_b)‖_{L²} ≤ lam⁻¹ · d² · ‖a − b‖_∞ · ‖∇u_b‖_{L²} .
```

The proof is the printed one: subtract the two weak equations, test with the
difference, use ellipticity on the left and the pairing bound on the right.  The
dimensional factor `d²` is the price of the supremum-norm carrier — one `d` from
the pairing bound and one from the action of a matrix with entries bounded by
`‖a − b‖_∞`.

## Main results

* `sqrt_energy_grad_sub_le` — the estimate above.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. Auxiliary bounds -/

theorem norm_le_sqrt_vecNormSq (xi : Vec d) : ‖xi‖ ≤ Real.sqrt (vecNormSq xi) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_apply_le_vecNormSq xi i)

theorem sq_norm_le_vecNormSq (xi : Vec d) : ‖xi‖ ^ (2 : ℕ) ≤ vecNormSq xi := by
  have h := norm_le_sqrt_vecNormSq xi
  have hsq := mul_self_le_mul_self (norm_nonneg xi) h
  rw [← pow_two, ← pow_two] at hsq
  rwa [Real.sq_sqrt (vecNormSq_nonneg xi)] at hsq

/-- The pairing bound with the first field controlled pointwise by a second one;
this avoids any measurability assumption on the first field. -/
theorem abs_setIntegral_vecDot_le_of_norm_le (U : Set (Vec d)) (hU : MeasurableSet U)
    {F G H : Vec d → Vec d} {c : ℝ} (hc : 0 ≤ c)
    (hH : MemVectorL2 U H) (hG : MemVectorL2 U G)
    (hFH : ∀ x ∈ U, ‖F x‖ ≤ c * ‖H x‖) :
    |∫ x in U, vecDot (F x) (G x) ∂volume| ≤
      (d : ℝ) * c * (Real.sqrt (∫ x in U, ‖H x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in U, ‖G x‖ ^ (2 : ℕ) ∂volume)) := by
  have hHn : MemLp (fun x => ‖H x‖) 2 (volume.restrict U) := hH.norm
  have hGn : MemLp (fun x => ‖G x‖) 2 (volume.restrict U) := hG.norm
  have hint : Integrable (fun x => ‖H x‖ * ‖G x‖) (volume.restrict U) := by
    simpa [Pi.mul_apply] using! hHn.integrable_mul hGn
  have h1 : |∫ x in U, vecDot (F x) (G x) ∂volume| ≤
      ∫ x in U, |vecDot (F x) (G x)| ∂volume := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict U)
        (f := fun x => vecDot (F x) (G x))
  have h2 : ∫ x in U, |vecDot (F x) (G x)| ∂volume ≤
      ∫ x in U, ((d : ℝ) * c) * (‖H x‖ * ‖G x‖) ∂volume := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (hint.const_mul ((d : ℝ) * c)) ?_
    refine (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx => ?_)
    calc |vecDot (F x) (G x)| ≤ (d : ℝ) * (‖F x‖ * ‖G x‖) := abs_vecDot_le_dim_mul _ _
      _ ≤ (d : ℝ) * ((c * ‖H x‖) * ‖G x‖) := by
          have := mul_le_mul_of_nonneg_right (hFH x hx) (norm_nonneg (G x))
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = ((d : ℝ) * c) * (‖H x‖ * ‖G x‖) := by ring
  have h3 : ∫ x in U, ((d : ℝ) * c) * (‖H x‖ * ‖G x‖) ∂volume =
      ((d : ℝ) * c) * ∫ x in U, ‖H x‖ * ‖G x‖ ∂volume := integral_const_mul _ _
  have h4 : ∫ x in U, ‖H x‖ * ‖G x‖ ∂volume ≤
      Real.sqrt (∫ x in U, ‖H x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in U, ‖G x‖ ^ (2 : ℕ) ∂volume) := by
    have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict U)
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => norm_nonneg (H x))
      (Filter.Eventually.of_forall fun x => norm_nonneg (G x))
      (by simpa using hHn) (by simpa using hGn)
    have hrw : ∀ K : Vec d → Vec d,
        ∫ x in U, ‖K x‖ ^ (2 : ℝ) ∂volume = ∫ x in U, ‖K x‖ ^ (2 : ℕ) ∂volume := by
      intro K
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ‖K x‖ ^ (2 : ℝ) = ‖K x‖ ^ (2 : ℕ)
      rw [← Real.rpow_natCast (‖K x‖) 2]
      norm_num
    rw [hrw H, hrw G, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow] at *
    exact hhold
  calc |∫ x in U, vecDot (F x) (G x) ∂volume|
      ≤ ∫ x in U, |vecDot (F x) (G x)| ∂volume := h1
    _ ≤ ∫ x in U, ((d : ℝ) * c) * (‖H x‖ * ‖G x‖) ∂volume := h2
    _ = ((d : ℝ) * c) * ∫ x in U, ‖H x‖ * ‖G x‖ ∂volume := h3
    _ ≤ ((d : ℝ) * c) * (Real.sqrt (∫ x in U, ‖H x‖ ^ (2 : ℕ) ∂volume) *
          Real.sqrt (∫ x in U, ‖G x‖ ^ (2 : ℕ) ∂volume)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

/-! ## 2. The estimate -/

private theorem h10Sub_toH1Function' {U : Set (Vec d)} (v w : H10Function U) :
    (v - w).toH1Function = v.toH1Function - w.toH1Function := rfl

/-- **The solution map is continuous in the coefficient field**, in the energy
norm, with the dimensional factor `d²` of the supremum-norm carrier.

`hbv` is the minimal integrability datum the subtraction of the two weak
equations needs; at the use sites it is supplied by the ellipticity of the
second coefficient field. -/
theorem sqrt_energy_grad_sub_le {y : Vec d} {n : ℤ} {a b : CoeffField d} {lam Lam : ℝ}
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    (hab : ∀ x ∈ cubeSetAt y n, ∀ i j, |a x i j - b x i j| ≤ delta)
    {u v : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hbv : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (b x) (v.grad x))
    (hu : IsDirichletSolutionAt a y n u g) (hv : IsDirichletSolutionAt b y n v g) :
    Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x - v.grad x‖ ^ (2 : ℕ) ∂volume) ≤
      lam⁻¹ * ((d : ℝ) * (d : ℝ) * delta) *
        Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) := by
  have hUmeas : MeasurableSet (cubeSetAt y n) := measurableSet_cubeSetAt y n
  have hlam : 0 < lam := (hEll.2 y (mem_cubeSetAt_self y n)).1
  obtain ⟨w, hwf, hwg⟩ :
      ∃ w : H10Function (cubeSetAt y n),
        (∀ x, w.toH1Function.toFun x = u.toFun x - v.toFun x) ∧
          (∀ x, w.toH1Function.grad x = u.grad x - v.grad x) := by
    obtain ⟨w1, h1f, h1g⟩ := hu.1
    obtain ⟨w2, h2f, h2g⟩ := hv.1
    refine ⟨w1 - w2, fun x => ?_, fun x => ?_⟩
    · rw [h1f x, h2f x, h10Sub_toH1Function']
      simp only [H1Function.sub_toFun]
    · rw [h1g x, h2g x, h10Sub_toH1Function']
      simp only [H1Function.sub_grad]
  have hwL2 : MemVectorL2 (cubeSetAt y n) w.toH1Function.grad :=
    w.toH1Function.grad_memVectorL2
  have hvL2 : MemVectorL2 (cubeSetAt y n) v.grad := v.grad_memVectorL2
  have hAw : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (w.toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hwL2
  have hAu : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hAv : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (v.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hvL2
  -- the energy identity
  have hsplitW : ∀ x, matVecMul (a x) (w.toH1Function.grad x) =
      matVecMul (a x) (u.grad x) - matVecMul (a x) (v.grad x) := by
    intro x
    rw [hwg x, sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
  have hsplitP : ∀ x, matVecMul (a x - b x) (v.grad x) =
      matVecMul (a x) (v.grad x) - matVecMul (b x) (v.grad x) := by
    intro x
    funext i
    simp only [matVecMul, Pi.sub_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hkey : ∫ x in cubeSetAt y n,
      vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x) ∂volume =
      -∫ x in cubeSetAt y n,
        vecDot (matVecMul (a x - b x) (v.grad x)) (w.toH1Function.grad x) ∂volume := by
    rw [Section4.Provider.Schauder.integral_vecDot_sub_split hAu hAv hsplitW w,
      Section4.Provider.Schauder.integral_vecDot_sub_split hAv hbv hsplitP w,
      hu.2 w, hv.2 w]
    ring
  -- ellipticity on the left
  have hEnergyInt : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x))
      (cubeSetAt y n) := integrableOn_vecDot_of_memVectorL2 hAw hwL2
  have hSqInt : IntegrableOn (fun x => lam * vecNormSq (w.toH1Function.grad x))
      (cubeSetAt y n) :=
    (integrableOn_vecDot_of_memVectorL2 hwL2 hwL2).const_mul lam
  have hlower : ∫ x in cubeSetAt y n, lam * vecNormSq (w.toH1Function.grad x) ∂volume ≤
      ∫ x in cubeSetAt y n,
        vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x) ∂volume := by
    refine integral_mono_ae hSqInt hEnergyInt ((ae_restrict_iff' hUmeas).2 ?_)
    refine Filter.Eventually.of_forall fun x hx => ?_
    show lam * vecNormSq (w.toH1Function.grad x) ≤
      vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x)
    rw [vecDot_comm]
    exact (hEll.2 x hx).2.2.1 (w.toH1Function.grad x)
  -- the norm-square integral is dominated by the Euclidean energy
  have hNormInt : IntegrableOn (fun x => ‖w.toH1Function.grad x‖ ^ (2 : ℕ))
      (cubeSetAt y n) := by
    have hn : MemLp (fun x => ‖w.toH1Function.grad x‖) 2
        (volume.restrict (cubeSetAt y n)) := hwL2.norm
    have := hn.integrable_mul hn
    simpa [Pi.mul_apply, pow_two] using! this
  have hEucInt : IntegrableOn (fun x => vecNormSq (w.toH1Function.grad x))
      (cubeSetAt y n) := integrableOn_vecDot_of_memVectorL2 hwL2 hwL2
  have hcompare : ∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume ≤
      ∫ x in cubeSetAt y n, vecNormSq (w.toH1Function.grad x) ∂volume :=
    integral_mono hNormInt hEucInt fun x => sq_norm_le_vecNormSq _
  -- the right-hand side
  have hpert : ∀ x ∈ cubeSetAt y n,
      ‖matVecMul (a x - b x) (v.grad x)‖ ≤ ((d : ℝ) * delta) * ‖v.grad x‖ := by
    intro x hx
    exact norm_matVecMul_le_of_entry_bound hdelta
      (fun i j => by simpa [Matrix.sub_apply] using hab x hx i j) (v.grad x)
  have hupper := abs_setIntegral_vecDot_le_of_norm_le (cubeSetAt y n) hUmeas
    (by positivity : (0 : ℝ) ≤ (d : ℝ) * delta) hvL2 hwL2 hpert
  -- assemble
  have hSnn : (0 : ℝ) ≤ Real.sqrt (∫ x in cubeSetAt y n,
      ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) := Real.sqrt_nonneg _
  have hTnn : (0 : ℝ) ≤ Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) :=
    Real.sqrt_nonneg _
  have hNormNonneg : (0 : ℝ) ≤ ∫ x in cubeSetAt y n,
      ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume :=
    integral_nonneg fun x => by positivity
  have hchain : lam * (Real.sqrt (∫ x in cubeSetAt y n,
        ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume)) ^ (2 : ℕ) ≤
      (d : ℝ) * ((d : ℝ) * delta) *
        (Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) *
          Real.sqrt (∫ x in cubeSetAt y n,
            ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume)) := by
    have hsq := Real.sq_sqrt hNormNonneg
    rw [hsq]
    have hmid : lam * ∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume ≤
        ∫ x in cubeSetAt y n, lam * vecNormSq (w.toH1Function.grad x) ∂volume := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hcompare hlam.le
    refine le_trans hmid (le_trans hlower ?_)
    rw [hkey]
    exact le_trans (neg_le_abs _) hupper
  have hgrad : (∫ x in cubeSetAt y n, ‖u.grad x - v.grad x‖ ^ (2 : ℕ) ∂volume) =
      ∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖u.grad x - v.grad x‖ ^ (2 : ℕ) = ‖w.toH1Function.grad x‖ ^ (2 : ℕ)
    rw [hwg x]
  rw [hgrad]
  rcases eq_or_lt_of_le hSnn with hzero | hpos
  · rw [← hzero]
    positivity
  · have hdiv : lam * Real.sqrt (∫ x in cubeSetAt y n,
        ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) ≤
        (d : ℝ) * ((d : ℝ) * delta) *
          Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) := by
      have h := hchain
      rw [pow_two] at h
      have hmul : (lam * Real.sqrt (∫ x in cubeSetAt y n,
            ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume)) *
            Real.sqrt (∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) ≤
          ((d : ℝ) * ((d : ℝ) * delta) *
            Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume)) *
            Real.sqrt (∫ x in cubeSetAt y n,
              ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) := by
        linarith [h]
      exact le_of_mul_le_mul_right hmul hpos
    rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hlam]
    linarith [hdiv]

end

end Algsuperdiff.Section5.Support
