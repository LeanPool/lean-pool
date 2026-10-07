/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureGradientClosure
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildJClosure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm

/-!
# The force pressure on one time slice

For a real spatial L² field f, the gradient field (I - ℙ) f of
`lem:force-pressure` is an L² limit of test gradients. The homogeneous
Sobolev inequality makes the test functions Cauchy in L⁶, and their limit is
an L⁶ pressure with weak gradient (I - ℙ) f. The L⁶ function with a
given weak gradient is unique: an L⁶ function with zero weak gradient
vanishes almost everywhere.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem forcePressure_integrable_mul_of_test
    {f g : Vec3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) volume :=
  (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

/-- Integration by parts between two whole-space test functions. -/
theorem forcePressureTest_integral_mul_partialDeriv
    (φ ψ : WeakTestFunction (Set.univ : Set Vec3)) (i : Fin 3) :
    ∫ x, φ x * ψ.partialDeriv i x = -∫ x, φ.partialDeriv i x * ψ x := by
  have hφc : Continuous φ.toFun := φ.contDiff.continuous
  have hψc : Continuous ψ.toFun := ψ.contDiff.continuous
  have hφd : Continuous fun x => φ.partialDeriv i x :=
    (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψd : Continuous fun x => ψ.partialDeriv i x :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (forcePressure_integrable_mul_of_test hφd hψc ψ.hasCompactSupport)
    (forcePressure_integrable_mul_of_test hφc hψd
      (ψ.hasCompactSupport.fderiv (𝕜 := ℝ) |>.comp_left
        (g := fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (by simp)))
    (forcePressure_integrable_mul_of_test hφc hψc ψ.hasCompactSupport)
    (fun x _ => (φ.contDiff.differentiable (by simp)) x)
    (fun x _ => (ψ.contDiff.differentiable (by simp)) x)

/-- A whole-space test function has its classical gradient as weak
gradient. -/
theorem forcePressureTest_hasWeakGradientOn
    (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    HasWeakGradientOn (Set.univ : Set Vec3) φ.toFun (forcePressureTestGradient φ) := by
  intro i
  rw [hasWeakPartialDerivOn_iff_forall_testFunction]
  intro ψ
  rw [setIntegral_univ, setIntegral_univ]
  exact forcePressureTest_integral_mul_partialDeriv φ ψ i

/-- The homogeneous Sobolev inequality for whole-space test functions. -/
theorem forcePressureTest_eLpNorm_six_le
    (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    eLpNorm φ.toFun 6 volume ≤
      gagliardoNirenbergSobolevConstant * eLpNorm (forcePressureTestGradient φ) 2 volume := by
  have hφ2 : MemLp φ.toFun 2 volume :=
    φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hgrad2 := forcePressureTestGradient_memLp φ
  let v : H1Function (Set.univ : Set Vec3) :=
    { toFun := φ.toFun
      grad := forcePressureTestGradient φ
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hφ2
      gradMemL2 := by
        intro m
        simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using (memLp_pi_iff.mp hgrad2) m
      hasWeakGradient := forcePressureTest_hasWeakGradientOn φ }
  simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
    CKN.weakGradientLpNormOn, Measure.restrict_univ, v] using
    (Classical.choose_spec CKN.sobolev_L6_global).2 v

/-- Pairings with a fixed L^q function pass to the limit along a sequence
converging in the dual exponent. -/
theorem forcePressure_tendsto_integral_mul {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {F : ℕ → Vec3 → ℝ} {f h : Vec3 → ℝ}
    (hF : ∀ n, MemLp (F n) p volume) (hf : MemLp f p volume) (hh : MemLp h q volume)
    (hlim : Tendsto (fun n => eLpNorm (F n - f) p volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * h x) atTop (𝓝 (∫ x, f x * h x)) := by
  apply tendsto_integral_of_L1' (fun x => f x * h x)
  · exact Eventually.of_forall fun n => (hF n).integrable_mul hh
  · have hbound (n : ℕ) : eLpNorm ((fun x => F n x * h x) - fun x => f x * h x) 1 volume ≤
        eLpNorm (F n - f) p volume * eLpNorm h q volume := by
      have heq : ((fun x => F n x * h x) - fun x => f x * h x) =
          fun x => (F n - f) x * h x := by
        funext x
        simp only [Pi.sub_apply]
        ring
      rw [heq]
      simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := p) (q := q) (r := 1)
        (fun a b : ℝ => a * b) 1 continuous_mul
        ((hF n).sub hf).aestronglyMeasurable hh.aestronglyMeasurable
        (Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
    have hlim' : Tendsto (fun n => eLpNorm (F n - f) p volume * eLpNorm h q volume)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hlim (Or.inr hh.eLpNorm_lt_top.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
      (fun _ => zero_le) hbound

/-- The exponents 6 and 6/5 are Hölder conjugate. -/
theorem holderTriple_six_ofReal_sixFifths :
    ENNReal.HolderTriple (6 : ℝ≥0∞) (ENNReal.ofReal (6 / 5 : ℝ)) 1 := by
  have hreal : Real.HolderTriple 6 (6 / 5) 1 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have h := hreal.ennrealOfReal
  rwa [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] at h

private theorem forcePressureTest_sub_eLpNorm_le
    (φ ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    eLpNorm (φ.toFun - ψ.toFun) 6 volume ≤
      gagliardoNirenbergSobolevConstant *
        eLpNorm (forcePressureTestGradientL2 φ - forcePressureTestGradientL2 ψ) 2 volume := by
  let χ := forcePressureTestAdd φ (forcePressureTestSmul (-1) ψ)
  have hχ : χ.toFun = φ.toFun - ψ.toFun := by
    funext x
    simp only [χ, forcePressureTestAdd, forcePressureTestSmul, Pi.sub_apply]
    ring
  have hgrad : forcePressureTestGradient χ =
      forcePressureTestGradient φ - forcePressureTestGradient ψ := by
    simp only [χ, forcePressureTestGradient_add, forcePressureTestGradient_smul]
    funext x i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hrep : forcePressureTestGradient φ - forcePressureTestGradient ψ =ᵐ[volume]
      realVectorL2Representative (forcePressureTestGradientL2 φ) -
        realVectorL2Representative (forcePressureTestGradientL2 ψ) := by
    filter_upwards [realVectorL2OfCoordinateFunction_rep (forcePressureTestGradient φ)
        (forcePressureTestGradient_memLp φ),
      realVectorL2OfCoordinateFunction_rep (forcePressureTestGradient ψ)
        (forcePressureTestGradient_memLp ψ)] with x h1 h2
    change _ = realVectorL2Representative (forcePressureTestGradientL2 φ) x -
      realVectorL2Representative (forcePressureTestGradientL2 ψ) x
    rw [forcePressureTestGradientL2, forcePressureTestGradientL2, h1, h2]
    rfl
  calc
    eLpNorm (φ.toFun - ψ.toFun) 6 volume = eLpNorm χ.toFun 6 volume := by rw [hχ]
    _ ≤ gagliardoNirenbergSobolevConstant *
        eLpNorm (forcePressureTestGradient χ) 2 volume :=
      forcePressureTest_eLpNorm_six_le χ
    _ ≤ gagliardoNirenbergSobolevConstant *
        eLpNorm (forcePressureTestGradientL2 φ - forcePressureTestGradientL2 ψ) 2 volume := by
      gcongr
      rw [hgrad, eLpNorm_congr_ae hrep]
      exact realVectorL2Representative_sub_eLpNorm_le _ _

/-- The chosen homogeneous Sobolev constant is finite. -/
theorem gagliardoNirenbergSobolevConstant_ne_top :
    gagliardoNirenbergSobolevConstant ≠ ⊤ :=
  (Classical.choose_spec CKN.sobolev_L6_global).1

/-- Existence in `lem:force-pressure` on one time slice: for every real
spatial L² field there is an L⁶ pressure whose weak gradient is the
field (I - ℙ) f, with the homogeneous Sobolev bound. -/
theorem exists_forcePressureSlice (v : RealVectorL2) :
    ∃ p : Vec3 → ℝ, MemLp p 6 volume ∧
      eLpNorm p 6 volume ≤
        gagliardoNirenbergSobolevConstant * eLpNorm (forcePressureGradientL2 v) 2 volume ∧
      HasWeakGradientOn (Set.univ : Set Vec3) p
        (realVectorL2Representative (forcePressureGradientL2 v)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩
  obtain ⟨φ, hφ⟩ := exists_testGradient_tendsto_forcePressureGradientL2 v
  set g := forcePressureGradientL2 v
  set C := gagliardoNirenbergSobolevConstant
  have hCtop : C ≠ ⊤ := gagliardoNirenbergSobolevConstant_ne_top
  have hmem6 (n : ℕ) : MemLp (φ n).toFun 6 volume :=
    (φ n).contDiff.continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport
  let P : ℕ → Lp ℝ 6 (volume : Measure Vec3) := fun n => (hmem6 n).toLp (φ n).toFun
  have hdist (m n : ℕ) : dist (P m) (P n) ≤
      C.toReal * dist (forcePressureTestGradientL2 (φ m))
        (forcePressureTestGradientL2 (φ n)) := by
    rw [Lp.dist_def, Lp.dist_def]
    have hcongr : eLpNorm (⇑(P m) - ⇑(P n)) 6 volume =
        eLpNorm ((φ m).toFun - (φ n).toFun) 6 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [(hmem6 m).coeFn_toLp, (hmem6 n).coeFn_toLp] with x h1 h2
      simp only [Pi.sub_apply, P, h1, h2]
    rw [hcongr, ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ C.toReal),
      ← ENNReal.toReal_mul, ENNReal.ofReal_toReal hCtop]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hCtop (by
      rw [← eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
      exact Lp.eLpNorm_ne_top _)) ?_
    exact (forcePressureTest_sub_eLpNorm_le (φ m) (φ n)).trans (by
      gcongr
      exact le_of_eq (eLpNorm_congr_ae (Lp.coeFn_sub _ _)))
  have hcauchyG := hφ.cauchySeq
  have hcauchy : CauchySeq P := by
    rw [Metric.cauchySeq_iff] at hcauchyG ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchyG (ε / (C.toReal + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    calc
      dist (P m) (P n) ≤ C.toReal * dist (forcePressureTestGradientL2 (φ m))
          (forcePressureTestGradientL2 (φ n)) := hdist m n
      _ ≤ (C.toReal + 1) * dist (forcePressureTestGradientL2 (φ m))
          (forcePressureTestGradientL2 (φ n)) := by
        gcongr
        linarith only
      _ < (C.toReal + 1) * (ε / (C.toReal + 1)) := by
        gcongr
      _ = ε := by field_simp
  obtain ⟨Plim, hPlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨⇑Plim, Lp.memLp Plim, ?_, ?_⟩
  · -- the Sobolev bound in the limit
    have hnorm (n : ℕ) : ‖P n‖ ≤ C.toReal * ‖forcePressureTestGradientL2 (φ n)‖ := by
      have h := hdist n n
      rw [Lp.norm_def, Lp.norm_def]
      have hP : eLpNorm (⇑(P n)) 6 volume = eLpNorm (φ n).toFun 6 volume :=
        eLpNorm_congr_ae (hmem6 n).coeFn_toLp
      rw [hP, ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ C.toReal),
        ← ENNReal.toReal_mul, ENNReal.ofReal_toReal hCtop]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top hCtop (Lp.eLpNorm_ne_top _)) ?_
      have hzero := forcePressureTest_sub_eLpNorm_le (φ n) forcePressureTestZero
      have hz1 : (φ n).toFun - forcePressureTestZero.toFun = (φ n).toFun := by
        funext x
        simp [forcePressureTestZero]
      rw [hz1, forcePressureTestGradientL2_zero, sub_zero] at hzero
      exact hzero
    have hlimP : Tendsto (fun n => ‖P n‖) atTop (𝓝 ‖Plim‖) :=
      (continuous_norm.tendsto _).comp hPlim
    have hlimG : Tendsto (fun n => C.toReal * ‖forcePressureTestGradientL2 (φ n)‖) atTop
        (𝓝 (C.toReal * ‖g‖)) :=
      ((continuous_norm.tendsto _).comp hφ).const_mul _
    have hle : ‖Plim‖ ≤ C.toReal * ‖g‖ :=
      le_of_tendsto_of_tendsto' hlimP hlimG hnorm
    rw [Lp.norm_def, Lp.norm_def] at hle
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top Plim),
      ← ENNReal.ofReal_toReal (ENNReal.mul_ne_top hCtop (Lp.eLpNorm_ne_top g)),
      ENNReal.toReal_mul]
    exact ENNReal.ofReal_le_ofReal hle
  · -- the weak gradient
    intro i
    rw [hasWeakPartialDerivOn_iff_forall_testFunction]
    intro ψ
    rw [setIntegral_univ, setIntegral_univ]
    have hψd : Continuous fun x => ψ.partialDeriv i x :=
      (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport fun x => ψ.partialDeriv i x :=
      ψ.hasCompactSupport.fderiv (𝕜 := ℝ) |>.comp_left
        (g := fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (by simp)
    have := holderTriple_six_ofReal_sixFifths
    have hleft : Tendsto (fun n => ∫ x, (φ n).toFun x * ψ.partialDeriv i x) atTop
        (𝓝 (∫ x, Plim x * ψ.partialDeriv i x)) := by
      apply forcePressure_tendsto_integral_mul (p := 6) (q := ENNReal.ofReal (6 / 5 : ℝ))
        hmem6 (Lp.memLp Plim) (hψd.memLp_of_hasCompactSupport hψdc)
      have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' P Plim).1 hPlim
      refine h.congr' (Eventually.of_forall fun n => ?_)
      apply eLpNorm_congr_ae
      filter_upwards [(hmem6 n).coeFn_toLp] with x hx
      simp only [Pi.sub_apply, P, hx]
    have hψ2 : MemLp ψ.toFun 2 volume :=
      ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
    have hcomp (u : Vec3 → Vec3) (hu : MemLp u 2 volume) :
        MemLp (fun x => u x i) 2 volume := memLp_pi_iff.mp hu i
    have hright : Tendsto (fun n => ∫ x, (φ n).partialDeriv i x * ψ x) atTop
        (𝓝 (∫ x, realVectorL2Representative g x i * ψ x)) := by
      apply forcePressure_tendsto_integral_mul (p := 2) (q := 2)
        (fun n => hcomp _ (forcePressureTestGradient_memLp (φ n)))
        (hcomp _ (realVectorL2Representative_memLp_two g)) hψ2
      have hG := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ g).1 hφ
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG
        (fun _ => zero_le) (fun n => ?_)
      have hrep := realVectorL2OfCoordinateFunction_rep (forcePressureTestGradient (φ n))
        (forcePressureTestGradient_memLp (φ n))
      calc
        eLpNorm ((fun x => (φ n).partialDeriv i x) -
            fun x => realVectorL2Representative g x i) 2 volume ≤
            eLpNorm (realVectorL2Representative (forcePressureTestGradientL2 (φ n)) -
              realVectorL2Representative g) 2 volume := by
          apply eLpNorm_mono_ae (((hcomp _ (forcePressureTestGradient_memLp (φ n))).sub
            (hcomp _ (realVectorL2Representative_memLp_two g))).aestronglyMeasurable)
          filter_upwards [hrep] with x hx
          change ‖forcePressureTestGradient (φ n) x i -
            realVectorL2Representative g x i‖ ≤ _
          rw [← hx]
          exact norm_le_pi_norm
            (realVectorL2Representative (forcePressureTestGradientL2 (φ n)) x -
              realVectorL2Representative g x) i
        _ ≤ eLpNorm (forcePressureTestGradientL2 (φ n) - g) 2 volume :=
          realVectorL2Representative_sub_eLpNorm_le _ _
        _ = eLpNorm (⇑(forcePressureTestGradientL2 (φ n)) - ⇑g) 2 volume :=
          eLpNorm_congr_ae (Lp.coeFn_sub _ _)
    have hIBP (n : ℕ) : ∫ x, (φ n).toFun x * ψ.partialDeriv i x =
        -∫ x, (φ n).partialDeriv i x * ψ x :=
      forcePressureTest_integral_mul_partialDeriv (φ n) ψ i
    have hright' := hright.neg
    exact tendsto_nhds_unique hleft (hright'.congr (fun n => (hIBP n).symm))

end CKN.Leray
