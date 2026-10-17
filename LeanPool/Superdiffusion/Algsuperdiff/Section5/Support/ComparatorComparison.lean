/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DirichletSolvability
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.MatchedTrace

/-!
# ComparatorComparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The weak comparison principle for the constant-coefficient problem on a cube

The homogenized exit-time profile solves `-σ Δ w = 1` on `y + □_n` with zero
boundary values.  Every lower bound for it is obtained from a barrier: a
zero-trace function `v` with `-σ Δ v ≤ 1` weakly lies below `w`.  This module
proves that comparison, in the form used twice by the exit-time estimate — once
with the barrier `v = 0`, which gives `w ≥ 0`, and once with a bump barrier,
which gives the lower bound on the inner cube.

The argument is the standard energy argument: the positive part `(v - w)₊` of
the difference has zero trace, its gradient is `1_{v>w} ∇(v - w)`, and testing
the two relations against it gives `σ ∫ |∇(v-w)₊|² ≤ 0`; the Poincaré inequality
on `H¹₀` then forces `(v - w)₊ = 0`.

## Main results

* `ae_le_of_constantForcingSubsolution` — the comparison.
* `le_of_ae_le_of_continuousOn` — an almost-everywhere inequality between two
  functions continuous on an open set is a pointwise inequality.

## References

* ABK26, the exit-time comparison of Section 5.2.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. From an almost-everywhere inequality to a pointwise one -/

/-- **On an open set, an almost-everywhere inequality between functions
continuous there is a pointwise inequality.**  The set where it fails is open
and null, hence empty. -/
theorem le_of_ae_le_of_continuousOn {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hae : ∀ᵐ x ∂(volume.restrict U), f x ≤ g x)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) :
    ∀ x ∈ U, f x ≤ g x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxU, hxlt⟩ := hcon
  have hbad : U ∩ {z | g z < f z} = (g - f) ⁻¹' Set.Iio (0 : ℝ) ∩ U := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio,
      Pi.sub_apply, sub_neg]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hopen : IsOpen (U ∩ {z | g z < f z}) := by
    obtain ⟨W, hWopen, hW⟩ := (continuousOn_iff'.1 (hg.sub hf)) (Set.Iio (0 : ℝ)) isOpen_Iio
    rw [hbad, hW]
    exact hWopen.inter hU
  have hpos : 0 < volume (U ∩ {z | g z < f z}) := hopen.measure_pos volume ⟨x, hxU, hxlt⟩
  have hzero : volume (U ∩ {z | g z < f z}) = 0 := by
    have hres : (volume.restrict U) {z | ¬ f z ≤ g z} = 0 := by
      rw [ae_iff] at hae
      exact hae
    rw [Measure.restrict_apply₀' hU.measurableSet.nullMeasurableSet] at hres
    have hsets : {z | ¬ f z ≤ g z} ∩ U = U ∩ {z | g z < f z} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_le]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rwa [hsets] at hres
  exact hpos.ne' hzero

/-! ## 2. The comparison -/

private theorem h10Sub_toH1Function' {U : Set (Vec d)} (v w : H10Function U) :
    (v - w).toH1Function = v.toH1Function - w.toH1Function := rfl

/-- **The weak comparison principle for `-σ Δ · = 1` on the cube `y + □_n`.**
A zero-trace subsolution lies below the zero-trace solution almost everywhere.

`hw0` records that `w` has zero trace, `hw` that it solves the equation, and
`hv` that `v` is a subsolution: both relations are stated in the constant-forcing
weak form `σ ∫ ∇u·∇φ = ∫ φ` in which the linear datum puts the problem. -/
theorem ae_le_of_constantForcingSubsolution {y : Vec d} {n : ℤ} (hd : 0 < d)
    {sig : ℝ} (hsig : 0 < sig) {w : H1Function (cubeSetAt y n)}
    (hw0 : ∃ w0 : H10Function (cubeSetAt y n),
        (∀ x, w.toFun x = w0.toH1Function.toFun x) ∧
          (∀ x, w.grad x = w0.toH1Function.grad x))
    (hw : ∀ phi : H10Function (cubeSetAt y n),
        sig * ∫ x in cubeSetAt y n, vecDot (w.grad x) (phi.toH1Function.grad x) ∂volume =
          ∫ x in cubeSetAt y n, phi.toH1Function.toFun x ∂volume)
    (v : H10Function (cubeSetAt y n))
    (hv : ∀ phi : H10Function (cubeSetAt y n),
        (∀ x, 0 ≤ phi.toH1Function.toFun x) →
        sig * ∫ x in cubeSetAt y n,
            vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume ≤
          ∫ x in cubeSetAt y n, phi.toH1Function.toFun x ∂volume) :
    ∀ᵐ x ∂(volume.restrict (cubeSetAt y n)), v.toH1Function.toFun x ≤ w.toFun x := by
  classical
  have : NeZero d := ⟨hd.ne'⟩
  have hU : IsOpenBoundedConvexDomain (cubeSetAt y n) := isOpenBoundedConvexDomain_cubeSetAt y n
  have hQmeas : MeasurableSet (cubeSetAt y n) := measurableSet_cubeSetAt y n
  obtain ⟨w0, hw0f, hw0g⟩ := hw0
  set D : H10Function (cubeSetAt y n) := v - w0 with hD_def
  have hDf : ∀ x, D.toH1Function.toFun x = v.toH1Function.toFun x - w.toFun x := by
    intro x
    rw [hD_def, h10Sub_toH1Function', H1Function.sub_toFun, hw0f x]
  have hDg : ∀ x, D.toH1Function.grad x = v.toH1Function.grad x - w.grad x := by
    intro x
    rw [hD_def, h10Sub_toH1Function', H1Function.sub_grad, hw0g x]
  -- the positive part of the difference, as an `H¹` function with its gradient
  obtain ⟨P, hPf, hPg⟩ := exists_h1_max_sub_const hU D.toH1Function 0
  -- and as a zero-trace function
  have hmatch : MemH10 (cubeSetAt y n) fun x =>
      D.toH1Function.toFun x - (0 : H1Function (cubeSetAt y n)).toFun x := by
    refine ⟨D, funext fun x => ?_⟩
    simp
  have hPmem : MemH10 (cubeSetAt y n) P.toFun := by
    have h := memH10_max_sub_matched hU D.toH1Function 0 hmatch 0
    have hfun : (fun x => max (D.toH1Function.toFun x - 0) 0 -
        max ((0 : H1Function (cubeSetAt y n)).toFun x - 0) 0) = P.toFun := by
      funext x
      rw [hPf]
      simp
    rwa [hfun] at h
  obtain ⟨psi, hpsif⟩ := hPmem
  -- `psi` is nonnegative
  have hpsinn : ∀ x, 0 ≤ psi.toH1Function.toFun x := by
    intro x
    rw [hpsif, hPf]
    exact le_max_right _ _
  -- the gradient of `psi` is the truncated gradient of the difference
  have hloc : ∀ (z : H1Function (cubeSetAt y n)) (i : Fin d),
      LocallyIntegrableOn (fun x => z.grad x i) (cubeSetAt y n) volume := fun z i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hpsiP : ∀ i : Fin d, (fun x => psi.toH1Function.grad x i) =ᵐ[volumeMeasureOn
      (cubeSetAt y n)] fun x => P.grad x i := by
    intro i
    have hwk := psi.toH1Function.hasWeakGradient i
    rw [hpsif] at hwk
    exact HasWeakPartialDerivOn.ae_eq hU.isOpen (hloc _ i) (hloc _ i) hwk
      (P.hasWeakGradient i)
  have hpsiPvec : psi.toH1Function.grad =ᵐ[volumeMeasureOn (cubeSetAt y n)] P.grad := by
    have hall : ∀ᵐ x ∂(volumeMeasureOn (cubeSetAt y n)),
        ∀ i : Fin d, psi.toH1Function.grad x i = P.grad x i :=
      (ae_all_iff).2 fun i => hpsiP i
    filter_upwards [hall] with x hx
    exact funext hx
  have hpsigrad : psi.toH1Function.grad =ᵐ[volumeMeasureOn (cubeSetAt y n)]
      {z | (0 : ℝ) < D.toH1Function.toFun z}.indicator D.toH1Function.grad := by
    filter_upwards [hpsiPvec, hPg] with x h1 h2
    rw [h1, h2]
  -- the key pointwise identity
  have hkey : (fun x => vecDot (D.toH1Function.grad x) (psi.toH1Function.grad x))
      =ᵐ[volumeMeasureOn (cubeSetAt y n)]
        fun x => vecNormSq (psi.toH1Function.grad x) := by
    filter_upwards [hpsigrad] with x hx
    by_cases hcase : (0 : ℝ) < D.toH1Function.toFun x
    · have : psi.toH1Function.grad x = D.toH1Function.grad x := by
        rw [hx]
        exact Set.indicator_of_mem (show x ∈ {z | (0 : ℝ) < D.toH1Function.toFun z} from hcase)
          D.toH1Function.grad
      rw [this]
      rfl
    · have : psi.toH1Function.grad x = 0 := by
        rw [hx]
        exact Set.indicator_of_notMem
          (show x ∉ {z | (0 : ℝ) < D.toH1Function.toFun z} from hcase) D.toH1Function.grad
      rw [this]
      simp [vecNormSq, vecDot]
  -- energy comparison
  have hintD : IntegrableOn
      (fun x => vecDot (D.toH1Function.grad x) (psi.toH1Function.grad x))
      (cubeSetAt y n) volume :=
    integrableOn_vecDot_of_memVectorL2 D.toH1Function.grad_memVectorL2
      psi.toH1Function.grad_memVectorL2
  have hintV : IntegrableOn
      (fun x => vecDot (v.toH1Function.grad x) (psi.toH1Function.grad x))
      (cubeSetAt y n) volume :=
    integrableOn_vecDot_of_memVectorL2 v.toH1Function.grad_memVectorL2
      psi.toH1Function.grad_memVectorL2
  have hintW : IntegrableOn (fun x => vecDot (w.grad x) (psi.toH1Function.grad x))
      (cubeSetAt y n) volume :=
    integrableOn_vecDot_of_memVectorL2 w.grad_memVectorL2
      psi.toH1Function.grad_memVectorL2
  have hsplit : ∫ x in cubeSetAt y n,
      vecDot (D.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        (∫ x in cubeSetAt y n, vecDot (v.toH1Function.grad x) (psi.toH1Function.grad x)
            ∂volume) -
          ∫ x in cubeSetAt y n, vecDot (w.grad x) (psi.toH1Function.grad x) ∂volume := by
    rw [← integral_sub hintV hintW]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change vecDot (D.toH1Function.grad x) (psi.toH1Function.grad x) =
      vecDot (v.toH1Function.grad x) (psi.toH1Function.grad x) -
        vecDot (w.grad x) (psi.toH1Function.grad x)
    rw [hDg x]
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hle0 : ∫ x in cubeSetAt y n,
      vecDot (D.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume ≤ 0 := by
    have h1 := hv psi hpsinn
    have h2 := hw psi
    have hmul : sig * ∫ x in cubeSetAt y n,
        vecDot (D.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume ≤ 0 := by
      rw [hsplit, mul_sub, h2]
      linarith only [h1]
    nlinarith only [hmul, hsig]
  have hsqle : ∫ x in cubeSetAt y n, vecNormSq (psi.toH1Function.grad x) ∂volume ≤ 0 := by
    rw [← integral_congr_ae hkey]
    exact hle0
  have hsqnn : (0 : ℝ) ≤ ∫ x in cubeSetAt y n, vecNormSq (psi.toH1Function.grad x) ∂volume :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hintSq : IntegrableOn (fun x => vecNormSq (psi.toH1Function.grad x))
      (cubeSetAt y n) volume :=
    integrableOn_vecDot_of_memVectorL2 psi.toH1Function.grad_memVectorL2
      psi.toH1Function.grad_memVectorL2
  have haeSq : (fun x => vecNormSq (psi.toH1Function.grad x))
      =ᵐ[volume.restrict (cubeSetAt y n)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => vecNormSq_nonneg _) hintSq).1
      (le_antisymm hsqle hsqnn)
  have haeGrad : psi.toH1Function.grad =ᵐ[volume.restrict (cubeSetAt y n)] 0 := by
    filter_upwards [haeSq] with x hx
    simp only [Pi.zero_apply] at hx
    exact vecNormSq_eq_zero hx
  have hzeroVec : MemVectorL2 (cubeSetAt y n) (0 : Vec d → Vec d) := MemLp.zero
  have hgradzero : psi.toH1Function.gradToVectorL2 = 0 :=
    (toVectorL2_eq_toVectorL2_iff psi.toH1Function.grad_memVectorL2 hzeroVec).2 haeGrad
  have hscalar :=
    H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hU) psi hgradzero
  have hzeroSc : MemScalarL2 (cubeSetAt y n) (0 : Vec d → ℝ) := MemLp.zero
  have haeFun : psi.toH1Function.toFun =ᵐ[volume.restrict (cubeSetAt y n)] 0 :=
    (toScalarL2_eq_toScalarL2_iff psi.toH1Function.memL2 hzeroSc).1 hscalar
  filter_upwards [haeFun] with x hx
  have h : psi.toH1Function.toFun x = 0 := hx
  rw [hpsif, hPf] at h
  have hle : D.toH1Function.toFun x ≤ 0 := by
    have h' : max (D.toH1Function.toFun x - 0) 0 = 0 := h
    have hmax := max_eq_right_iff.1 h'
    linarith only [hmax]
  rw [hDf x] at hle
  linarith only [hle]

end

end Algsuperdiff.Section5.Support
