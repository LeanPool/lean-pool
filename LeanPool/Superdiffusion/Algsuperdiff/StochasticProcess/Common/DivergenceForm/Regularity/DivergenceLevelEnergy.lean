/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.MatchedTrace
public import LeanPool.Superdiffusion.Support.CoarseGraining.QuadraticStability.Integral
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.DifferenceQuotient
public import LeanPool.Superdiffusion.Support.HighContrast.Coupled.LocalEnergy.Bounds
public import LeanPool.Superdiffusion.Support.HighContrast.Coupled.Stampacchia.LevelEnergy
public import Mathlib.Algebra.Order.Chebyshev

/-!
# DivergenceLevelEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Superlevel energy for divergence forcing

This file derives the single-function superlevel gradient estimate for a
zero-trace divergence-forced weak solution.

The existing predicate is used through its literal weak identity
`integral (a grad u) dot grad phi = integral g dot grad phi`.  In the standard
distributional convention this is `-div (a grad u) = -div g`; the opposite
forcing convention is obtained by replacing `g` with `-g`.
-/

namespace HCPolySupport.IsZeroTraceDirichletRhsWeakSolution

open HCPolySupport MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Under the displayed positive-sign weak identity, a bounded vector forcing
controls the coordinate `L²` norms of the gradient on every nonnegative
superlevel set. -/
theorem levelEnergy_sumCoordNorm_le
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    {u : H10Function U} {g : Vec d → Vec d}
    (hsol : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (huMeas : Measurable u.toH1Function.toFun)
    (hg : MemVectorL2 U g)
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k)
    (hgBound : ∀ᵐ x ∂volumeMeasureOn U,
      Real.sqrt (vecNormSq (g x)) ≤ M) :
    (∑ i : Fin d,
      (eLpNorm
        ({x | x ∈ U ∧ k < u.toH1Function.toFun x}.indicator
          (fun x => u.toH1Function.grad x i))
        2 (volumeMeasureOn U)).toReal) ≤
      (Real.sqrt d / lam) * M *
        Real.sqrt
          (volume {x | x ∈ U ∧ k < u.toH1Function.toFun x}).toReal := by
  classical
  let A : Set (Vec d) := {x | x ∈ U ∧ k < u.toH1Function.toFun x}
  have hAm : MeasurableSet A :=
    (measurableSet_of_isEllipticFieldOn hEll).inter
      (measurableSet_lt measurable_const huMeas)
  have hAU : A ⊆ U := fun _ hx => hx.1
  have : IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hUtop : volume U ≠ ⊤ := by
    have h := (measure_lt_top (volumeMeasureOn U) Set.univ).ne
    rwa [Measure.restrict_apply_univ] at h
  have hAtop : volume A ≠ ⊤ := ne_top_of_le_ne_top hUtop (measure_mono hAU)
  obtain ⟨v, hvfun, hvgrad⟩ := exists_h1_max_sub_const hU u.toH1Function k
  have humatch : MemH10 U (fun x => u.toH1Function.toFun x - (0 : ℝ)) := by
    refine ⟨u, ?_⟩
    funext x
    ring
  obtain ⟨w, hwfun⟩ :=
    memH10_max_sub_matched hU u.toH1Function (0 : H1Function U) humatch k
  have hwvfun : w.toH1Function.toFun = v.toFun := by
    rw [hwfun, hvfun]
    funext x
    rw [H1Function.zero_toFun, Pi.zero_apply, zero_sub,
      max_eq_right (neg_nonpos.mpr hk)]
    ring
  have hwvgrad : w.toH1Function.grad =ᵐ[volumeMeasureOn U] v.grad := by
    have hcoord : ∀ i : Fin d,
        (fun x => w.toH1Function.grad x i) =ᵐ[volumeMeasureOn U]
          fun x => v.grad x i := by
      intro i
      apply HasWeakPartialDerivOn.ae_eq hU.isOpen
      · exact locallyIntegrableOn_of_locallyIntegrable_restrict
          ((w.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num))
      · exact locallyIntegrableOn_of_locallyIntegrable_restrict
          ((v.gradMemL2 i).locallyIntegrable (by norm_num))
      · exact w.toH1Function.hasWeakPartialDerivOn i
      · rw [hwvfun]
        exact v.hasWeakPartialDerivOn i
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    funext i
    exact hx i
  have hwgrad : w.toH1Function.grad =ᵐ[volumeMeasureOn U]
      A.indicator u.toH1Function.grad := by
    filter_upwards [hwvgrad, hvgrad, ae_restrict_mem
      (measurableSet_of_isEllipticFieldOn hEll)] with x hwx hvx hxU
    rw [hwx, hvx]
    by_cases hx : k < u.toH1Function.toFun x <;>
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, A, hx, hxU,
        and_self, and_false, ite_true, ite_false]
  have hfluxInt : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.toH1Function.grad x))
        (u.toH1Function.grad x)) U :=
    by
      simpa only [vecDot_comm] using
        integrableOn_dirichletEnergyDensity_of_isEllipticFieldOn hEll u
  have hrhsInt : IntegrableOn
      (fun x => vecDot (g x) (u.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hg u.toH1Function.grad_memVectorL2
  have hcoeffEq :
      ∫ x in A, vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (u.toH1Function.grad x) ∂volume =
        ∫ x in A, vecDot (g x) (u.toH1Function.grad x) ∂volume := by
    calc
      _ = ∫ x in U, A.indicator (fun y =>
          vecDot (matVecMul (a y) (u.toH1Function.grad y))
            (u.toH1Function.grad y)) x ∂volume := by
        symm
        exact setIntegral_indicator_subset hAm hAU _
      _ = ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (w.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hwgrad] with x hx
        rw [hx]
        by_cases h : x ∈ A <;> simp [h, vecDot]
      _ = ∫ x in U, vecDot (g x) (w.toH1Function.grad x) ∂volume := hsol w
      _ = ∫ x in U, A.indicator
          (fun y => vecDot (g y) (u.toH1Function.grad y)) x ∂volume := by
        apply integral_congr_ae
        filter_upwards [hwgrad] with x hx
        rw [hx]
        by_cases h : x ∈ A <;> simp [h, vecDot]
      _ = _ := setIntegral_indicator_subset hAm hAU _
  let E : ℝ := ∫ x in A, vecNormSq (u.toH1Function.grad x) ∂volume
  have hE0 : 0 ≤ E := integral_nonneg fun _ => vecNormSq_nonneg _
  have hEllLe : lam * E ≤
      ∫ x in A, vecDot (matVecMul (a x) (u.toH1Function.grad x))
        (u.toH1Function.grad x) ∂volume := by
    change lam * ∫ x in A, vecNormSq (u.toH1Function.grad x) ∂volume ≤ _
    calc
      _ = ∫ x in A, lam * vecNormSq (u.toH1Function.grad x) ∂volume := by
        rw [integral_const_mul]
      _ ≤ _ := setIntegral_mono_ae_restrict
        ((integrableOn_vecNormSq_zeroTraceGrad u).mono_set hAU |>.const_mul lam)
        (hfluxInt.mono_set hAU) (by
          filter_upwards [ae_restrict_mem hAm] with x hx
          simpa only [vecDot_comm] using
            (hEll.2 x (hAU hx)).2.2.1 (u.toH1Function.grad x))
  have hpairLe :
      ∫ x in A, vecDot (g x) (u.toH1Function.grad x) ∂volume ≤
        M * Real.sqrt (volume A).toReal * Real.sqrt E := by
    have hgsqInt : IntegrableOn (fun x => vecNormSq (g x)) A := by
      simpa only [vecNormSq] using
        (integrableOn_vecDot_of_memVectorL2 hg hg).mono_set hAU
    have husqInt : IntegrableOn
        (fun x => vecNormSq (u.toH1Function.grad x)) A :=
      (integrableOn_vecNormSq_zeroTraceGrad u).mono_set hAU
    let : IsFiniteMeasure (volume.restrict A) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hAtop.lt_top⟩
    have sqrtMemL2 (f : Vec d → ℝ) (hf : IntegrableOn f A)
        (hf0 : ∀ᵐ x ∂volume.restrict A, 0 ≤ f x) :
        MemLp (fun x => Real.sqrt (f x)) 2 (volume.restrict A) := by
      have hsmeas : AEStronglyMeasurable (fun x => Real.sqrt (f x))
          (volume.restrict A) := Real.continuous_sqrt.comp_aestronglyMeasurable hf.1
      have hsquare : (fun x => Real.sqrt (f x) ^ 2) =ᵐ[volume.restrict A] f := by
        filter_upwards [hf0] with x hx
        rw [Real.sq_sqrt hx]
      exact (memLp_two_iff_integrable_sq hsmeas).2 (hf.congr hsquare.symm)
    have hgsqrtMem := sqrtMemL2 _ hgsqInt
      (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
    have husqrtMem := sqrtMemL2 _ husqInt
      (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
    have hsqrtInt : IntegrableOn
        (fun x => Real.sqrt (vecNormSq (u.toH1Function.grad x))) A :=
      husqrtMem.integrable (by norm_num)
    calc
      _ ≤ ∫ x in A, Real.sqrt (vecNormSq (g x)) *
          Real.sqrt (vecNormSq (u.toH1Function.grad x)) ∂volume := by
        exact setIntegral_mono_ae_restrict (hrhsInt.mono_set hAU)
          (hgsqrtMem.integrable_mul husqrtMem) (by
              filter_upwards [ae_restrict_mem hAm] with x _
              exact le_trans (le_abs_self _) (abs_vecDot_le_sqrt_mul_sqrt _ _))
      _ ≤ ∫ x in A, M * Real.sqrt (vecNormSq (u.toH1Function.grad x)) ∂volume := by
        exact setIntegral_mono_ae_restrict
          (hgsqrtMem.integrable_mul husqrtMem)
          (hsqrtInt.const_mul M) (by
            filter_upwards [ae_restrict_mem hAm,
              ae_mono (Measure.restrict_mono hAU le_rfl) hgBound] with x _ hx
            exact mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _))
      _ = M * ∫ x in A, Real.sqrt (vecNormSq (u.toH1Function.grad x)) ∂volume := by
        rw [integral_const_mul]
      _ ≤ M * (Real.sqrt (volume A).toReal * Real.sqrt E) := by
        apply mul_le_mul_of_nonneg_left _ hM
        have honeInt : IntegrableOn (fun _ : Vec d => (1 : ℝ)) A :=
          integrableOn_const hAtop
        have hcs := integral_sqrt_mul_sqrt_le honeInt husqInt
          (Filter.Eventually.of_forall fun _ => zero_le_one)
          (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
        rw [setIntegral_one_eq_measureReal] at hcs
        simpa only [Real.sqrt_one, one_mul, E] using! hcs
      _ = M * Real.sqrt (volume A).toReal * Real.sqrt E := by ring
  have hEle : lam * E ≤ M * Real.sqrt (volume A).toReal * Real.sqrt E :=
    hEllLe.trans (hcoeffEq ▸ hpairLe)
  let C : ℝ := M / lam * Real.sqrt (volume A).toReal
  have hC0 : 0 ≤ C := mul_nonneg (div_nonneg hM hlam.le) (Real.sqrt_nonneg _)
  have hEbase : E ≤ C * Real.sqrt E := by
    rw [show C * Real.sqrt E =
      (M * Real.sqrt (volume A).toReal * Real.sqrt E) / lam by
        dsimp [C]
        field_simp]
    exact (le_div_iff₀ hlam).2 (by simpa only [mul_comm] using hEle)
  have hEsq : E ≤ C ^ 2 := le_sq_of_le_mul_sqrt hE0 hC0 hEbase
  let S : ℝ := ∑ i : Fin d,
    (eLpNorm (A.indicator (fun x => u.toH1Function.grad x i))
      2 (volumeMeasureOn U)).toReal
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hnormSq : ∀ i : Fin d,
      ((eLpNorm (A.indicator (fun x => u.toH1Function.grad x i))
        2 (volumeMeasureOn U)).toReal) ^ 2 =
        ∫ x in A, (u.toH1Function.grad x i) ^ 2 ∂volume := by
    intro i
    rw [toReal_eLpNorm_two_sq_eq_integral_sq
      ((u.toH1Function.gradMemL2 i).indicator hAm)]
    have hind : (fun x => (A.indicator
        (fun y => u.toH1Function.grad y i) x) ^ 2) =
        A.indicator (fun x => (u.toH1Function.grad x i) ^ 2) := by
      funext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [hind]
    exact setIntegral_indicator_subset hAm hAU _
  have hsumSq : (∑ i : Fin d,
      ((eLpNorm (A.indicator (fun x => u.toH1Function.grad x i))
        2 (volumeMeasureOn U)).toReal) ^ 2) = E := by
    rw [Finset.sum_congr rfl (fun i _ => hnormSq i), ← integral_finsetSum]
    · apply setIntegral_congr_fun hAm
      intro x _
      simp only [vecNormSq, vecDot, pow_two]
    · intro i _
      simpa only [pow_two] using!
        ((u.toH1Function.gradMemL2 i).integrable_mul
          (u.toH1Function.gradMemL2 i)).mono_measure
            (Measure.restrict_mono hAU le_rfl)
  have hSsq : S ^ 2 ≤ (d : ℝ) * E := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => (eLpNorm (A.indicator (fun x => u.toH1Function.grad x i))
        2 (volumeMeasureOn U)).toReal)
    simpa only [S, Finset.card_univ, Fintype.card_fin, Nat.cast_id, hsumSq] using h
  have hSsqC : S ^ 2 ≤ (d : ℝ) * C ^ 2 :=
    hSsq.trans (mul_le_mul_of_nonneg_left hEsq (Nat.cast_nonneg d))
  have htarget : S ≤ Real.sqrt d * C := by
    have hright0 : 0 ≤ Real.sqrt d * C :=
      mul_nonneg (Real.sqrt_nonneg _) hC0
    apply (sq_le_sq₀ hS0 hright0).mp
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    exact hSsqC
  change S ≤ _
  calc
    S ≤ Real.sqrt d * C := htarget
    _ = (Real.sqrt d / lam) * M * Real.sqrt (volume A).toReal := by
      dsimp [C]
      ring

end
end HCPolySupport.IsZeroTraceDirichletRhsWeakSolution
