/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallTopology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.HomogeneousSobolev
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Curl fields for the Leray data space

The cutoff construction in `lem:J-weak-div` uses compactly supported curls
as divergence-free approximants.
-/

public section

open CKN.Foundation.Parabolic
open Filter MeasureTheory
open scoped ENNReal Topology

namespace CKN

noncomputable section

/-- The curl of a smooth vector field, in the native three-dimensional
coordinates. -/
@[expose]
def curlVec3 (A : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  fun i => if i = 0 then
      CKN.spatialDeriv (fun y => A y 2) 1 x -
        CKN.spatialDeriv (fun y => A y 1) 2 x
    else if i = 1 then
      CKN.spatialDeriv (fun y => A y 0) 2 x -
        CKN.spatialDeriv (fun y => A y 2) 0 x
    else
      CKN.spatialDeriv (fun y => A y 1) 0 x -
        CKN.spatialDeriv (fun y => A y 0) 1 x

/-- The cross product on the native three-dimensional carrier. -/
@[expose]
def crossVec3 (u v : Vec3) : Vec3 :=
  fun i => if i = 0 then u 1 * v 2 - u 2 * v 1
    else if i = 1 then u 2 * v 0 - u 0 * v 2
    else u 0 * v 1 - u 1 * v 0

private theorem crossVec3_norm_le (u v : Vec3) :
    ‖crossVec3 u v‖ ≤ 2 * CKN.vecEuclideanNorm u * ‖v‖ := by
  have hE : 0 ≤ CKN.vecEuclideanNorm u := CKN.vecEuclideanNorm_nonneg u
  have hterm (j k : Fin 3) : |u j| * ‖v k‖ ≤ CKN.vecEuclideanNorm u * ‖v‖ :=
    mul_le_mul (CKN.abs_apply_le_vecEuclideanNorm u j) (norm_le_pi_norm v k)
      (norm_nonneg _) hE
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hE) (norm_nonneg v))).2
  intro i
  have hu (j : Fin 3) : |u j| ≤ CKN.vecEuclideanNorm u :=
    CKN.abs_apply_le_vecEuclideanNorm u j
  have hv (j : Fin 3) : ‖v j‖ ≤ ‖v‖ := norm_le_pi_norm v j
  fin_cases i <;> simp only [crossVec3] <;> first
    | calc
        |u 1 * v 2 - u 2 * v 1| ≤ |u 1 * v 2| + |u 2 * v 1| := abs_sub _ _
        _ = |u 1| * ‖v 2‖ + |u 2| * ‖v 1‖ := by simp [abs_mul, Real.norm_eq_abs]
        _ ≤ CKN.vecEuclideanNorm u * ‖v‖ + CKN.vecEuclideanNorm u * ‖v‖ :=
          add_le_add (hterm 1 2) (hterm 2 1)
        _ = 2 * CKN.vecEuclideanNorm u * ‖v‖ := by ring
    | calc
        |u 2 * v 0 - u 0 * v 2| ≤ |u 2 * v 0| + |u 0 * v 2| := abs_sub _ _
        _ = |u 2| * ‖v 0‖ + |u 0| * ‖v 2‖ := by simp [abs_mul, Real.norm_eq_abs]
        _ ≤ CKN.vecEuclideanNorm u * ‖v‖ + CKN.vecEuclideanNorm u * ‖v‖ :=
          add_le_add (hterm 2 0) (hterm 0 2)
        _ = 2 * CKN.vecEuclideanNorm u * ‖v‖ := by ring
    | calc
        |u 0 * v 1 - u 1 * v 0| ≤ |u 0 * v 1| + |u 1 * v 0| := abs_sub _ _
        _ = |u 0| * ‖v 1‖ + |u 1| * ‖v 0‖ := by simp [abs_mul, Real.norm_eq_abs]
        _ ≤ CKN.vecEuclideanNorm u * ‖v‖ + CKN.vecEuclideanNorm u * ‖v‖ :=
          add_le_add (hterm 0 1) (hterm 1 0)
        _ = 2 * CKN.vecEuclideanNorm u * ‖v‖ := by ring

/-- The product rule for the curl of a scalar multiple of a vector field. -/
theorem curlVec3_smul_scalar {η : Vec3 → ℝ} {A : Vec3 → Vec3}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (x : Vec3) :
    curlVec3 (fun y => η y • A y) x =
      η x • curlVec3 A x +
        crossVec3 (fun i => CKN.spatialDeriv η i x) (A x) := by
  funext i
  have hηd := hη.differentiable (by simp) x
  have hAi (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => A y j) :=
    (contDiff_pi.mp hA) j
  fin_cases i
  · change CKN.spatialDeriv (fun y => η y * A y 2) 1 x -
        CKN.spatialDeriv (fun y => η y * A y 1) 2 x =
      η x * (CKN.spatialDeriv (fun y => A y 2) 1 x -
        CKN.spatialDeriv (fun y => A y 1) 2 x) +
        (CKN.spatialDeriv η 1 x * A x 2 - CKN.spatialDeriv η 2 x * A x 1)
    rw [CKN.spatialDeriv_mul hηd ((hAi 2).differentiable (by simp) x) 1,
      CKN.spatialDeriv_mul hηd ((hAi 1).differentiable (by simp) x) 2]
    ring
  · change CKN.spatialDeriv (fun y => η y * A y 0) 2 x -
        CKN.spatialDeriv (fun y => η y * A y 2) 0 x =
      η x * (CKN.spatialDeriv (fun y => A y 0) 2 x -
        CKN.spatialDeriv (fun y => A y 2) 0 x) +
        (CKN.spatialDeriv η 2 x * A x 0 - CKN.spatialDeriv η 0 x * A x 2)
    rw [CKN.spatialDeriv_mul hηd ((hAi 0).differentiable (by simp) x) 2,
      CKN.spatialDeriv_mul hηd ((hAi 2).differentiable (by simp) x) 0]
    ring
  · change CKN.spatialDeriv (fun y => η y * A y 1) 0 x -
        CKN.spatialDeriv (fun y => η y * A y 0) 1 x =
      η x * (CKN.spatialDeriv (fun y => A y 1) 0 x -
        CKN.spatialDeriv (fun y => A y 0) 1 x) +
        (CKN.spatialDeriv η 0 x * A x 1 - CKN.spatialDeriv η 1 x * A x 0)
    rw [CKN.spatialDeriv_mul hηd ((hAi 1).differentiable (by simp) x) 0,
      CKN.spatialDeriv_mul hηd ((hAi 0).differentiable (by simp) x) 1]
    ring

/-- Splitting the cutoff curl error into the potential-gradient term and the
tail of the original curl. -/
theorem curlVec3_cutoff_error {η : Vec3 → ℝ} {A : Vec3 → Vec3}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (x : Vec3) :
    curlVec3 (fun y => η y • A y) x - curlVec3 A x =
      (η x - 1) • curlVec3 A x +
        crossVec3 (fun i => CKN.spatialDeriv η i x) (A x) := by
  rw [curlVec3_smul_scalar hη hA x]
  funext i
  simp [Pi.smul_apply, smul_eq_mul, crossVec3]
  ring

private theorem component_hasCompactSupport {A : Vec3 → Vec3}
    (hA : HasCompactSupport A) (j : Fin 3) :
    HasCompactSupport (fun x => A x j) := by
  refine HasCompactSupport.intro' hA.isCompact (isClosed_tsupport (f := A)) ?_
  intro x hx
  have hzero := image_eq_zero_of_notMem_tsupport (f := A) (x := x) hx
  simp [hzero]

private theorem spatialDeriv_hasCompactSupport {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (CKN.spatialDeriv f i) := by
  change HasCompactSupport (fun x => (fderiv ℝ f x) (CKN.basisVec i))
  exact hf.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)

private theorem scalarMul_hasCompactSupport {η : Vec3 → ℝ} {A : Vec3 → Vec3}
    (hη : HasCompactSupport η) : HasCompactSupport (fun x => η x • A x) := by
  refine HasCompactSupport.intro' hη.isCompact (isClosed_tsupport (f := η)) ?_
  intro x hx
  have hη0 := image_eq_zero_of_notMem_tsupport (f := η) (x := x) hx
  funext i
  simp [hη0]

/-- The curl preserves compact support. -/
theorem curlVec3_hasCompactSupport {A : Vec3 → Vec3}
    (hA : HasCompactSupport A) : HasCompactSupport (curlVec3 A) := by
  let K : Set Vec3 := ⋃ i : Fin 3, ⋃ j : Fin 3,
    tsupport (fun x => CKN.spatialDeriv (fun y => A y j) i x)
  have hderiv (i j : Fin 3) :
      HasCompactSupport (fun x => CKN.spatialDeriv (fun y => A y j) i x) :=
    spatialDeriv_hasCompactSupport (component_hasCompactSupport hA j) i
  have hKc : IsCompact K := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro j
    exact (hderiv i j).isCompact
  have hKclosed : IsClosed K := by
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    exact isClosed_tsupport (f := fun x => CKN.spatialDeriv
      (fun y => A y j) i x)
  refine HasCompactSupport.intro' hKc hKclosed ?_
  intro x hx
  funext i
  have hzero (j k : Fin 3) : CKN.spatialDeriv (fun y => A y j) k x = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := fun y => CKN.spatialDeriv
      (fun z => A z j) k y) (x := x)
    intro hmem
    exact hx (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨j, hmem⟩⟩)
  fin_cases i <;> simp [curlVec3, hzero]

/-- A curl obtained from a compactly supported scalar cutoff has compact
support even when the underlying vector field does not. -/
theorem cutoffCurl_hasCompactSupport {η : Vec3 → ℝ} {A : Vec3 → Vec3}
    (hη : HasCompactSupport η) :
    HasCompactSupport (curlVec3 (fun x => η x • A x)) :=
  curlVec3_hasCompactSupport (scalarMul_hasCompactSupport hη)

/-- The curl of a smooth vector field is smooth. -/
theorem curlVec3_contDiff {A : Vec3 → Vec3}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    ContDiff ℝ (⊤ : ℕ∞) (curlVec3 A) := by
  apply contDiff_pi.mpr
  intro i
  have hAi (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => A x j) :=
    (contDiff_pi.mp hA) j
  fin_cases i <;> dsimp only [curlVec3] <;>
    exact (CKN.contDiff_spatialDeriv_smooth (hAi _) _).sub
      (CKN.contDiff_spatialDeriv_smooth (hAi _) _)

private theorem spatialDeriv_sub_smooth {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 3) :
    CKN.spatialDeriv (fun y => f y - g y) i =
      fun x => CKN.spatialDeriv f i x - CKN.spatialDeriv g i x := by
  funext x
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x))
  simpa [CKN.spatialDeriv] using h

/-- The divergence of the curl of a smooth vector field vanishes pointwise. -/
theorem curlVec3_divergence_eq_zero {A : Vec3 → Vec3}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (x : Vec3) :
    ∑ i : Fin 3, CKN.spatialDeriv (fun y => curlVec3 A y i) i x = 0 := by
  have hAi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => A y i) :=
    (contDiff_pi.mp hA) i
  have hcurl (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => curlVec3 A y i) := by
    fin_cases i <;> dsimp only [curlVec3] <;>
      exact (CKN.contDiff_spatialDeriv_smooth (hAi _) _).sub
        (CKN.contDiff_spatialDeriv_smooth (hAi _) _)
  have h0 := spatialDeriv_sub_smooth
    (CKN.contDiff_spatialDeriv_smooth (hAi 2) 1)
    (CKN.contDiff_spatialDeriv_smooth (hAi 1) 2) 0
  have h1 := spatialDeriv_sub_smooth
    (CKN.contDiff_spatialDeriv_smooth (hAi 0) 2)
    (CKN.contDiff_spatialDeriv_smooth (hAi 2) 0) 1
  have h2 := spatialDeriv_sub_smooth
    (CKN.contDiff_spatialDeriv_smooth (hAi 1) 0)
    (CKN.contDiff_spatialDeriv_smooth (hAi 0) 1) 2
  have hsum :
      (∑ i : Fin 3, CKN.spatialDeriv (fun y => curlVec3 A y i) i x) =
        (CKN.mixedSecond (fun y => A y 2) 0 1 x -
          CKN.mixedSecond (fun y => A y 1) 0 2 x) +
        (CKN.mixedSecond (fun y => A y 0) 1 2 x -
          CKN.mixedSecond (fun y => A y 2) 1 0 x) +
        (CKN.mixedSecond (fun y => A y 1) 2 0 x -
          CKN.mixedSecond (fun y => A y 0) 2 1 x) := by
    simp [Fin.sum_univ_succ, curlVec3, h0, h1, h2, CKN.mixedSecond]
    ring
  rw [hsum]
  rw [CKN.mixedSecond_swap (hAi 2) 0 1 x,
      CKN.mixedSecond_swap (hAi 1) 0 2 x,
      CKN.mixedSecond_swap (hAi 0) 1 2 x]
  ring

/-- Multiplying a smooth potential by a smooth scalar cutoff and taking its
curl gives a smooth divergence-free vector field. -/
theorem smooth_cutoffCurl_divergence_eq_zero {η : Vec3 → ℝ} {A : Vec3 → Vec3}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (x : Vec3) :
    ∑ i : Fin 3, CKN.spatialDeriv
      (fun y => curlVec3 (fun z => η z • A z) y i) i x = 0 := by
  apply curlVec3_divergence_eq_zero
  exact hη.smul hA

/-- The cutoff curl is smooth whenever the cutoff and potential are smooth. -/
theorem smooth_cutoffCurl_contDiff {η : Vec3 → ℝ} {A : Vec3 → Vec3}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    ContDiff ℝ (⊤ : ℕ∞) (curlVec3 (fun x => η x • A x)) :=
  curlVec3_contDiff (hη.smul hA)

/-- Cutting off an `L²` vector potential approximates its curl in `L²`.
The first term is the curl tail and the second is the cutoff-gradient error. -/
theorem cutoffCurl_eLpNorm_sub_le {A : Vec3 → Vec3}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hA2 : MemLp A (2 : ℝ≥0∞) volume)
    (hcurl2 : MemLp (curlVec3 A) (2 : ℝ≥0∞) volume)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    eLpNorm
        (curlVec3 (fun x => CKN.canonicalBallCutoff 0 r R x • A x) - curlVec3 A)
        (2 : ℝ≥0∞) volume ≤
      eLpNorm ((CKN.euclideanBall (0 : Vec3) r)ᶜ.indicator (curlVec3 A))
        (2 : ℝ≥0∞) volume +
      ‖(64 / (R - r) : ℝ)‖ₑ * eLpNorm A (2 : ℝ≥0∞) volume := by
  let η : Vec3 → ℝ := CKN.canonicalBallCutoff 0 r R
  let tail : Vec3 → Vec3 := (CKN.euclideanBall 0 r)ᶜ.indicator (curlVec3 A)
  let C : ℝ := 64 / (R - r)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
    exact CKN.canonicalBallCutoff_smooth 0 hr hrR
  have hηnonneg (x : Vec3) : 0 ≤ η x := by
    exact CKN.canonicalBallCutoff_nonneg 0 r R x
  have hηle (x : Vec3) : η x ≤ 1 := by
    exact CKN.canonicalBallCutoff_le_one 0 r R x
  have hηone {x : Vec3} (hx : x ∈ CKN.euclideanBall 0 r) : η x = 1 := by
    exact CKN.canonicalBallCutoff_eq_one_on_inner hr hrR hx
  have hgrad (x : Vec3) :
      CKN.vecEuclideanNorm (fun i => CKN.spatialDeriv η i x) ≤ 32 / (R - r) := by
    have h := CKN.canonicalBallCutoff_gradient_bound (x₀ := 0) hr hrR x
    have h' : CKN.vecEuclideanNorm (CKN.classicalGradient η x) ≤ 32 / (R - r) := by
      simpa [η] using h
    change CKN.vecEuclideanNorm (CKN.classicalGradient η x) ≤ 32 / (R - r)
    exact h'
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfirst (x : Vec3) :
      ‖(η x - 1) • curlVec3 A x‖ ≤ ‖tail x‖ := by
    by_cases hx : x ∈ CKN.euclideanBall 0 r
    · rw [hηone hx]
      simp [tail, hx]
    · have hfactor : |η x - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith only [hηnonneg x, hηle x]
      have hxcompl : x ∈ (CKN.euclideanBall 0 r)ᶜ := hx
      change ‖(η x - 1) • curlVec3 A x‖ ≤
        ‖(CKN.euclideanBall 0 r)ᶜ.indicator (curlVec3 A) x‖
      rw [Set.indicator_of_mem hxcompl]
      calc
        ‖(η x - 1) • curlVec3 A x‖ = |η x - 1| * ‖curlVec3 A x‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖curlVec3 A x‖ :=
          mul_le_of_le_one_left (norm_nonneg _) hfactor
  have hcross (x : Vec3) :
      ‖crossVec3 (fun i => CKN.spatialDeriv η i x) (A x)‖ ≤ C * ‖A x‖ := by
    calc
      ‖crossVec3 (fun i => CKN.spatialDeriv η i x) (A x)‖ ≤
          2 * CKN.vecEuclideanNorm (fun i => CKN.spatialDeriv η i x) * ‖A x‖ :=
        crossVec3_norm_le _ _
      _ ≤ 2 * (32 / (R - r)) * ‖A x‖ := by
        gcongr
        exact hgrad x
      _ = C * ‖A x‖ := by
        dsimp [C]
        ring
  let error : Vec3 → Vec3 :=
    curlVec3 (fun x => η x • A x) - curlVec3 A
  let major : Vec3 → ℝ := fun x => ‖tail x‖ + C * ‖A x‖
  have herrorSmooth : ContDiff ℝ (⊤ : ℕ∞) error := by
    exact (smooth_cutoffCurl_contDiff hη hA).sub (curlVec3_contDiff hA)
  have herrorMeas : AEStronglyMeasurable error volume :=
    herrorSmooth.continuous.aestronglyMeasurable
  have htailMeas : AEStronglyMeasurable tail volume :=
    hcurl2.aestronglyMeasurable.indicator (CKN.measurableSet_euclideanBall 0 r).compl
  have hmajorPoint (x : Vec3) : ‖error x‖ ≤ ‖major x‖ := by
    have hsplit := curlVec3_cutoff_error hη hA x
    have hsum : ‖error x‖ ≤
        ‖(η x - 1) • curlVec3 A x‖ +
          ‖crossVec3 (fun i => CKN.spatialDeriv η i x) (A x)‖ := by
      dsimp [error]
      rw [hsplit]
      exact norm_add_le _ _
    have hmaj : 0 ≤ major x := by
      simp only [major]
      positivity
    calc
      ‖error x‖ ≤ ‖tail x‖ + C * ‖A x‖ :=
        hsum.trans (add_le_add (hfirst x) (hcross x))
      _ = ‖major x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hmaj]
  have hmono : eLpNorm error (2 : ℝ≥0∞) volume ≤ eLpNorm major 2 volume :=
    eLpNorm_mono herrorMeas hmajorPoint
  have hsumLp : eLpNorm major (2 : ℝ≥0∞) volume ≤
      eLpNorm (fun x => ‖tail x‖) 2 volume +
        eLpNorm (fun x => C * ‖A x‖) 2 volume := by
    change eLpNorm ((fun x => ‖tail x‖) + (fun x => C * ‖A x‖))
      (2 : ℝ≥0∞) volume ≤ _
    exact eLpNorm_add_le (p := (2 : ℝ≥0∞)) (by norm_num)
  have htailNormLp : eLpNorm (fun x => ‖tail x‖) 2 volume = eLpNorm tail 2 volume := by
    exact eLpNorm_norm tail htailMeas
  have hALpNorm : eLpNorm (fun x => ‖A x‖) 2 volume = eLpNorm A 2 volume := by
    exact eLpNorm_norm A hA2.aestronglyMeasurable
  have hCsmul : eLpNorm (fun x => C * ‖A x‖) 2 volume =
      ‖(C : ℝ)‖ₑ * eLpNorm A 2 volume := by
    rw [show (fun x => C * ‖A x‖) = C • (fun x => ‖A x‖) by rfl,
      eLpNorm_const_smul, hALpNorm]
  change eLpNorm error 2 volume ≤ _
  calc
    eLpNorm error 2 volume ≤ eLpNorm major 2 volume := hmono
    _ ≤ eLpNorm (fun x => ‖tail x‖) 2 volume +
        eLpNorm (fun x => C * ‖A x‖) 2 volume := hsumLp
    _ = eLpNorm ((CKN.euclideanBall 0 r)ᶜ.indicator (curlVec3 A)) 2 volume +
          ‖(64 / (R - r) : ℝ)‖ₑ * eLpNorm A 2 volume := by
      rw [htailNormLp, hCsmul]

end

end CKN
