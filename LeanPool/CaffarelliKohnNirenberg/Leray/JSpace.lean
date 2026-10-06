/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.SmoothIBP
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.TestFunction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import LeanPool.CaffarelliKohnNirenberg.Foundation.HomogeneousSobolev
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpacePotential
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The divergence-free initial-data space

The closure characterization of the Leray space in `def:leray-hopf`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The weak-divergence formulation used in `lem:J-weak-div`. -/
@[expose]
def IsWeakDivFreeL2 (a : Vec3 → Vec3) : Prop :=
  MemLp a (2 : ℝ≥0∞) volume ∧
    ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, a x i * ψ.partialDeriv i x = 0

/-- The linear functional pairing a vector field with gradients of weak test functions. -/
@[expose]
def dotLinear : Vec3 →ₗ[ℝ] Vec3 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i : Fin 3, x i * y i)
    (by intro x y z; simp [Finset.sum_add_distrib, add_mul])
    (by
      intro c x y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring)
    (by intro x y z; simp [Finset.sum_add_distrib, mul_add])
    (by
      intro c x y
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        (∑ i : Fin 3, x i * (c * y i)) =
            ∑ i : Fin 3, c * (x i * y i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = c * ∑ i : Fin 3, x i * y i := (Finset.mul_sum _ _ _).symm
    )

/-- The continuous extension of the weak gradient-pairing functional. -/
@[expose]
def dotContinuous : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ :=
  dotLinear.mkContinuous₂ 3 (by
    intro x y
    calc
      ‖∑ i : Fin 3, x i * y i‖ ≤ ∑ i : Fin 3, ‖x i * y i‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, ‖x i‖ * ‖y i‖ := by simp [norm_mul]
      _ ≤ ∑ i : Fin 3, ‖x‖ * ‖y‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul
          (norm_le_pi_norm x i) (norm_le_pi_norm y i) (norm_nonneg _) (norm_nonneg _)
      _ = 3 * ‖x‖ * ‖y‖ := by simp [Finset.sum_const, nsmul_eq_mul]; ring
    )

/-- The coordinate gradient of a scalar weak test function. -/
@[expose]
def testGradient (ψ : WeakTestFunction (Set.univ : Set Vec3)) : Vec3 → Vec3 :=
  fun x i => ψ.partialDeriv i x

private theorem testGradient_contDiff
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => testGradient ψ x i) := by
  change ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ.toFun i)
  exact contDiff_spatialDeriv_smooth ψ.contDiff i

private theorem testGradient_hasCompactSupport
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    HasCompactSupport (testGradient ψ) := by
  let K : Set Vec3 := ⋃ i : Fin 3, tsupport (fun x : Vec3 => testGradient ψ x i)
  have hcomp (i : Fin 3) : HasCompactSupport (fun x : Vec3 => testGradient ψ x i) := by
    change HasCompactSupport (fun x => (fderiv ℝ ψ.toFun x) (basisVec i))
    exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hKc : IsCompact K := by
    apply isCompact_iUnion
    intro i
    exact (hcomp i).isCompact
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite fun i =>
    isClosed_tsupport (f := fun x : Vec3 => testGradient ψ x i)
  refine HasCompactSupport.intro' hKc hKclosed ?_
  intro x hx
  funext i
  apply image_eq_zero_of_notMem_tsupport (f := fun y : Vec3 => testGradient ψ y i) (x := x)
  intro hxi
  exact hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)

theorem testGradient_memLp
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    MemLp (testGradient ψ) (2 : ℝ≥0∞) volume := by
  apply (continuous_pi fun i => (testGradient_contDiff ψ i).continuous).memLp_of_hasCompactSupport
  exact testGradient_hasCompactSupport ψ

/-- The integral pairing of a vector field with the gradient of a weak test function. -/
@[expose]
def testPairing
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume →L[ℝ] ℝ :=
  (dotContinuous.lpPairing volume (2 : ℝ≥0∞) (2 : ℝ≥0∞)).flip
    ((testGradient_memLp ψ).toLp (testGradient ψ))

private theorem testPairing_eq_integral
    (ψ : WeakTestFunction (Set.univ : Set Vec3))
    (u : Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume) :
    testPairing ψ u =
      ∫ x : Vec3, ∑ i : Fin 3, u x i * testGradient ψ x i := by
  rw [testPairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [((testGradient_memLp ψ).coeFn_toLp)] with x hx
  simp [dotContinuous, dotLinear, hx]

/-- A smooth solenoidal field pairs to zero with gradients of compactly
supported smooth scalar tests. -/
theorem smoothSolenoidal_test_integral_zero
    (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hdiv : ∀ x, ∑ i : Fin 3, spatialDeriv (fun y => v y i) i x = 0)
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    ∫ x : Vec3, ∑ i : Fin 3, v x i * ψ.partialDeriv i x = 0 := by
  have hvi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => v x i) :=
    (contDiff_pi.mp hv) i
  have hparts (i : Fin 3) :
      ∫ x : Vec3, v x i * ψ.partialDeriv i x =
        -∫ x : Vec3, spatialDeriv (fun y => v y i) i x * ψ x := by
    simpa [WeakTestFunction.partialDeriv, spatialDeriv] using
      CKN.integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
        (u := fun x => v x i) (φ := ψ.toFun) (hvi i) ψ.contDiff
        ψ.hasCompactSupport i
  have hleftInt (i : Fin 3) :
    Integrable (fun x : Vec3 => v x i * ψ.partialDeriv i x) volume := by
    have hderivC := (testGradient_contDiff ψ i).continuous
    have hderivS : HasCompactSupport (fun x : Vec3 => ψ.partialDeriv i x) := by
      change HasCompactSupport (fun x => (fderiv ℝ ψ.toFun x) (basisVec i))
      exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hvi i).continuous.mul hderivC |>.integrable_of_hasCompactSupport
      (hderivS.mul_left (f := fun x => v x i))
  have hrightInt (i : Fin 3) :
      Integrable (fun x : Vec3 => spatialDeriv (fun y => v y i) i x * ψ x) volume := by
    have hderiv : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (fun y => v y i) i) :=
      contDiff_spatialDeriv_smooth (hvi i) i
    exact hderiv.continuous.mul ψ.contDiff.continuous |>.integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.mul_left)
  have hsumInt :
    Integrable (fun x : Vec3 =>
        (∑ i : Fin 3, spatialDeriv (fun y => v y i) i x) * ψ x) volume := by
    have hsumD : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
        ∑ i : Fin 3, spatialDeriv (fun y => v y i) i x) :=
      ContDiff.sum fun i _ => contDiff_spatialDeriv_smooth (hvi i) i
    exact (hsumD.continuous.mul ψ.contDiff.continuous).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.mul_left)
  have hleftSum :
      ∫ x : Vec3, ∑ i : Fin 3, v x i * ψ.partialDeriv i x =
        ∑ i : Fin 3, ∫ x : Vec3, v x i * ψ.partialDeriv i x := by
    simpa using integral_finsetSum (μ := volume) Finset.univ
      (f := fun i x => v x i * ψ.partialDeriv i x) (by
        intro i hi
        exact hleftInt i)
  have hrightSum :
      ∫ x : Vec3, ∑ i : Fin 3, spatialDeriv (fun y => v y i) i x * ψ x =
        ∑ i : Fin 3, ∫ x : Vec3, spatialDeriv (fun y => v y i) i x * ψ x := by
    simpa using integral_finsetSum (μ := volume) Finset.univ
      (f := fun i x => spatialDeriv (fun y => v y i) i x * ψ x) (by
        intro i hi
        exact hrightInt i)
  have hprod : ∀ x : Vec3,
      (∑ i : Fin 3, spatialDeriv (fun y => v y i) i x) * ψ x =
        ∑ i : Fin 3, spatialDeriv (fun y => v y i) i x * ψ x := by
    intro x
    rw [Finset.sum_mul]
  have hsumIntegrals :
      ∫ x : Vec3, (∑ i : Fin 3, spatialDeriv (fun y => v y i) i x) * ψ x =
        ∑ i : Fin 3, ∫ x : Vec3, spatialDeriv (fun y => v y i) i x * ψ x := by
    calc
      ∫ x : Vec3, (∑ i : Fin 3, spatialDeriv (fun y => v y i) i x) * ψ x =
          ∫ x : Vec3, ∑ i : Fin 3, spatialDeriv (fun y => v y i) i x * ψ x := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact hprod x
      _ = ∑ i : Fin 3,
          ∫ x : Vec3, spatialDeriv (fun y => v y i) i x * ψ x := hrightSum
  calc
    ∫ x : Vec3, ∑ i : Fin 3, v x i * ψ.partialDeriv i x =
        ∑ i : Fin 3, ∫ x : Vec3, v x i * ψ.partialDeriv i x := hleftSum
    _ = -∑ i : Fin 3,
        ∫ x : Vec3, spatialDeriv (fun y => v y i) i x * ψ x := by
          simp_rw [hparts, ← Finset.sum_neg_distrib]
    _ = -∫ x : Vec3,
        (∑ i : Fin 3, spatialDeriv (fun y => v y i) i x) * ψ x := by
          rw [hsumIntegrals]
    _ = 0 := by simp [hdiv]

/-- Compactly supported smooth solenoidal approximants imply weak
divergence-freeness of their `L²` limit. -/
theorem isInJ_weakDivFree {a : Vec3 → Vec3} (ha : IsInJ a) :
    IsWeakDivFreeL2 a := by
  rcases ha with ⟨haLp, aSeq, hSeqDiff, hSeqSupport, hSeqDiv, hSeqLimit⟩
  refine ⟨haLp, ?_⟩
  intro ψ
  have hSeqLp (k : ℕ) : MemLp (aSeq k) (2 : ℝ≥0∞) volume :=
    (hSeqDiff k).continuous.memLp_of_hasCompactSupport (hSeqSupport k)
  let f : ℕ → Lp (α := Vec3) Vec3 (2 : ℝ≥0∞) volume :=
    fun k => (hSeqLp k).toLp (aSeq k)
  have hfLimit : Tendsto f atTop (nhds (haLp.toLp a)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' aSeq hSeqLp a haLp).2 hSeqLimit
  let P := testPairing ψ
  have hPLimit : Tendsto (fun k => P (f k)) atTop
      (nhds (P (haLp.toLp a))) :=
    (P.continuous.tendsto (haLp.toLp a)).comp hfLimit
  have hPSeq (k : ℕ) : P (f k) = 0 := by
    rw [testPairing_eq_integral]
    calc
      ∫ x : Vec3, ∑ i : Fin 3, f k x i * testGradient ψ x i =
          ∫ x : Vec3, ∑ i : Fin 3, aSeq k x i * testGradient ψ x i := by
            apply integral_congr_ae
            filter_upwards [(hSeqLp k).coeFn_toLp] with x hx
            simp [f, hx]
      _ = 0 := smoothSolenoidal_test_integral_zero (aSeq k) (hSeqDiff k)
        (hSeqDiv k) ψ
  have hPconstant : (fun k : ℕ => P (f k)) = fun _ => (0 : ℝ) :=
    funext hPSeq
  rw [hPconstant] at hPLimit
  have hPvalue : P (haLp.toLp a) = 0 :=
    tendsto_nhds_unique hPLimit tendsto_const_nhds
  rw [testPairing_eq_integral] at hPvalue
  apply (integral_congr_ae ?_).trans hPvalue
  filter_upwards [haLp.coeFn_toLp] with x hx
  simp [testGradient, hx, WeakTestFunction.partialDeriv]

/-- A smooth `L²` vector potential with `L²` curl yields data in the Leray
closure by cutting the potential off on expanding balls. -/
theorem smoothL2Potential_curl_memJ {A : Vec3 → Vec3}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hA2 : MemLp A (2 : ℝ≥0∞) volume)
    (hcurl2 : MemLp (curlVec3 A) (2 : ℝ≥0∞) volume) :
    IsInJ (curlVec3 A) := by
  let r : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ)
  let R : ℕ → ℝ := fun k => 2 * r k
  let aSeq : ℕ → Vec3 → Vec3 := fun k =>
    curlVec3 (fun x => CKN.canonicalBallCutoff (0 : Vec3) (r k) (R k) x • A x)
  have hr (k : ℕ) : 0 ≤ r k := by
    dsimp [r]
    positivity
  have hrR (k : ℕ) : r k < R k := by
    dsimp [R]
    linarith only [hr k, show 0 < r k by dsimp [r]; positivity]
  have hcutSmooth (k : ℕ) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
        CKN.canonicalBallCutoff (0 : Vec3) (r k) (R k) x) :=
    CKN.canonicalBallCutoff_smooth (0 : Vec3) (hr k) (hrR k)
  have hSeqSmooth (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (aSeq k) := by
    exact smooth_cutoffCurl_contDiff (hcutSmooth k) hA
  have hSeqSupport (k : ℕ) : HasCompactSupport (aSeq k) := by
    apply cutoffCurl_hasCompactSupport
    exact CKN.canonicalBallCutoff_hasCompactSupport (x₀ := (0 : Vec3)) (hr k) (hrR k)
  have hSeqDiv (k : ℕ) (x : Vec3) :
      ∑ i : Fin 3, spatialDeriv (fun y => aSeq k y i) i x = 0 := by
    exact smooth_cutoffCurl_divergence_eq_zero (hcutSmooth k) hA x
  have htailBase := eLpNorm_indicator_compl_euclideanBall_tendsto_zero hcurl2
  have htail : Tendsto
      (fun k : ℕ => eLpNorm
        ((CKN.euclideanBall (0 : Vec3) (r k))ᶜ.indicator (curlVec3 A))
        (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
    have h := htailBase.comp (tendsto_add_atTop_nat 1)
    exact h
  have hdenom : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdenom' : Tendsto r atTop atTop := by simpa [r] using hdenom
  have hcoefReal : Tendsto (fun k : ℕ => (64 : ℝ) / r k)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (64 : ℝ)) atTop (nhds 64)).div_atTop hdenom'
  have hcoefAbs : Tendsto (fun k : ℕ => |(64 : ℝ) / r k|)
      atTop (nhds 0) := by
    exact hcoefReal.congr' (Filter.Eventually.of_forall fun k =>
      (abs_of_nonneg (by positivity : 0 ≤ (64 : ℝ) / r k)).symm)
  have hcoef : Tendsto (fun k : ℕ => ‖((64 : ℝ) / r k)‖ₑ)
      atTop (nhds 0) := by
    simpa only [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal hcoefAbs
  have hcorrection : Tendsto
      (fun k : ℕ => ‖((64 : ℝ) / r k)‖ₑ * eLpNorm A (2 : ℝ≥0∞) volume)
      atTop (nhds 0) :=
    by
      simpa using ENNReal.Tendsto.mul_const hcoef (Or.inr hA2.eLpNorm_lt_top.ne)
  have hbound (k : ℕ) :
      eLpNorm (aSeq k - curlVec3 A) (2 : ℝ≥0∞) volume ≤
        eLpNorm ((CKN.euclideanBall (0 : Vec3) (r k))ᶜ.indicator (curlVec3 A))
          (2 : ℝ≥0∞) volume +
        ‖((64 : ℝ) / r k)‖ₑ * eLpNorm A (2 : ℝ≥0∞) volume := by
    have h := cutoffCurl_eLpNorm_sub_le hA hA2 hcurl2 (hr k) (hrR k)
    have hRadius : R k - r k = r k := by
      dsimp [R]
      ring
    rw [hRadius] at h
    simpa [aSeq, r, R] using h
  have hmajor : Tendsto
      (fun k : ℕ => eLpNorm
        ((CKN.euclideanBall (0 : Vec3) (r k))ᶜ.indicator (curlVec3 A))
          (2 : ℝ≥0∞) volume +
        ‖((64 : ℝ) / r k)‖ₑ * eLpNorm A (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by simpa using htail.add hcorrection
  have hlimit : Tendsto
      (fun k : ℕ => eLpNorm (aSeq k - curlVec3 A) (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
    have hlower : ∀ᶠ k : ℕ in atTop,
      0 ≤ eLpNorm (aSeq k - curlVec3 A) (2 : ℝ≥0∞) volume :=
      Filter.Eventually.of_forall
        (fun k : ℕ => (show 0 ≤ eLpNorm (aSeq k - curlVec3 A)
          (2 : ℝ≥0∞) volume from bot_le))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
      hlower (Filter.Eventually.of_forall hbound)
  exact ⟨hcurl2, aSeq, hSeqSmooth, hSeqSupport, hSeqDiv, hlimit⟩

/-- The `L²` closure of smooth compactly supported solenoidal fields is closed
under `L²` limits. -/
theorem isInJ_closed_under_L2_limit {aSeq : ℕ → Vec3 → Vec3} {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume)
    (haSeq : ∀ n, IsInJ (aSeq n))
    (hlim : Tendsto (fun n => eLpNorm (aSeq n - a) (2 : ℝ≥0∞) volume)
      atTop (nhds 0)) :
    IsInJ a := by
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ))
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hdenom : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hreal : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).div_atTop hdenom
  have hε : Tendsto ε atTop (nhds 0) := by
    have h := ENNReal.tendsto_ofReal hreal
    simpa [ε] using h
  have houterSmall (n : ℕ) :
      ∀ᶠ j : ℕ in atTop, eLpNorm (aSeq j - a) (2 : ℝ≥0∞) volume < ε n :=
    hlim.eventually (Iio_mem_nhds (hεpos n))
  let outerIndex : ℕ → ℕ := fun n =>
    Classical.choose (Filter.Eventually.exists (houterSmall n))
  have houterIndex (n : ℕ) :
      eLpNorm (aSeq (outerIndex n) - a) (2 : ℝ≥0∞) volume < ε n :=
    Classical.choose_spec (Filter.Eventually.exists (houterSmall n))
  have hseqData (n : ℕ) :
      ∃ bSeq : ℕ → Vec3 → Vec3,
        (∀ k, ContDiff ℝ (⊤ : ℕ∞) (bSeq k)) ∧
        (∀ k, HasCompactSupport (bSeq k)) ∧
        (∀ k x, ∑ i : Fin 3, spatialDeriv (fun y => bSeq k y i) i x = 0) ∧
        Tendsto (fun k => eLpNorm (bSeq k - aSeq n) (2 : ℝ≥0∞) volume)
          atTop (nhds 0) := by
    rcases haSeq n with ⟨_, bSeq, hbSeq, hcompact, hdiv, happrox⟩
    exact ⟨bSeq, hbSeq, hcompact, hdiv, happrox⟩
  let innerSeq : ℕ → ℕ → Vec3 → Vec3 := fun n => Classical.choose (hseqData n)
  have hinnerSeq (n : ℕ) := Classical.choose_spec (hseqData n)
  have hinnerSmall (n : ℕ) :
      ∀ᶠ k : ℕ in atTop,
        eLpNorm (innerSeq (outerIndex n) k - aSeq (outerIndex n))
          (2 : ℝ≥0∞) volume < ε n := by
    exact (hinnerSeq (outerIndex n)).2.2.2.eventually
      (Iio_mem_nhds (hεpos n))
  let innerIndex : ℕ → ℕ := fun n =>
    Classical.choose (Filter.Eventually.exists (hinnerSmall n))
  have hinnerIndex (n : ℕ) :
      eLpNorm (innerSeq (outerIndex n) (innerIndex n) - aSeq (outerIndex n))
          (2 : ℝ≥0∞) volume < ε n :=
    Classical.choose_spec (Filter.Eventually.exists (hinnerSmall n))
  let cSeq : ℕ → Vec3 → Vec3 := fun n => innerSeq (outerIndex n) (innerIndex n)
  have hcSmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cSeq n) :=
    (hinnerSeq (outerIndex n)).1 (innerIndex n)
  have hcCompact (n : ℕ) : HasCompactSupport (cSeq n) :=
    (hinnerSeq (outerIndex n)).2.1 (innerIndex n)
  have hcDiv (n : ℕ) (x : Vec3) :
      ∑ i : Fin 3, spatialDeriv (fun y => cSeq n y i) i x = 0 :=
    (hinnerSeq (outerIndex n)).2.2.1 (innerIndex n) x
  have htriangle (n : ℕ) :
      eLpNorm (cSeq n - a) (2 : ℝ≥0∞) volume ≤
        eLpNorm (cSeq n - aSeq (outerIndex n)) (2 : ℝ≥0∞) volume +
          eLpNorm (aSeq (outerIndex n) - a) (2 : ℝ≥0∞) volume := by
    have hfun : (fun x => cSeq n x - a x) =
        (fun x => (cSeq n x - aSeq (outerIndex n) x) +
          (aSeq (outerIndex n) x - a x)) := by
      funext x
      abel
    change eLpNorm (fun x => cSeq n x - a x) (2 : ℝ≥0∞) volume ≤ _
    rw [hfun]
    exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hbound (n : ℕ) :
      eLpNorm (cSeq n - a) (2 : ℝ≥0∞) volume ≤ ε n + ε n := by
    exact (htriangle n).trans
      (add_le_add (le_of_lt (hinnerIndex n)) (le_of_lt (houterIndex n)))
  have hlimSeq : Tendsto (fun n => eLpNorm (cSeq n - a) (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
    have hnonneg : ∀ᶠ n : ℕ in atTop,
        0 ≤ eLpNorm (cSeq n - a) (2 : ℝ≥0∞) volume :=
      Filter.Eventually.of_forall fun n => bot_le
    have hmajor : Tendsto (fun n => ε n + ε n) atTop (nhds 0) := by
      simpa using hε.add hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hmajor hnonneg (Filter.Eventually.of_forall hbound)
  exact ⟨ha, cSeq, hcSmooth, hcCompact, hcDiv, hlimSeq⟩

end CKN
