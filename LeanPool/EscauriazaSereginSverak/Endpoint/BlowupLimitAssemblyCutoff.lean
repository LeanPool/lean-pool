/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyModulus
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.Product
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Growing cutoffs for the blow-up sequence

The blow-up fields of `prop:blowup-limit` are controlled on each fixed
bounded past cylinder only for all sufficiently large indices. To apply
`lem:compactness` of the CKN manuscript once on all of space and all negative times, the k-th
field of a reindexed sequence is multiplied by a smooth spatial cutoff equal
to one on the ball of radius k and by a Lipschitz time ramp equal to one
after time -k. On every fixed compact set the modified fields agree with
the original ones from some index on.
-/

public section


open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The smooth spatial cutoff of the k-th modified field: one on the ball
of radius k, supported in the ball of radius k + 1/2. -/
@[expose] def blowupLimitAssemblySpaceCutoff (k : ℕ) : Vec3 → ℝ :=
  canonicalBallCutoff (0 : Vec3) (k : ℝ) ((k : ℝ) + 1 / 2)

/-- The Lipschitz time ramp of the k-th modified field: zero before time
-(k + 1) and one after time -k. -/
@[expose] def blowupLimitAssemblyTimeRamp (k : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (t + ((k : ℝ) + 1)))

/-- The k-th modified velocity: the ν k-th field times the cutoffs. -/
@[expose] def blowupLimitAssemblyCutoffField (f : ℕ → ParabolicPoint → Vec3)
    (ν : ℕ → ℕ) (k : ℕ) : ParabolicPoint → Vec3 :=
  fun z => (blowupLimitAssemblyTimeRamp k z.2 *
    blowupLimitAssemblySpaceCutoff k z.1) • f (ν k) z

/-- The weak spatial gradient of the k-th modified velocity, by the
product rule. -/
@[expose] def blowupLimitAssemblyCutoffGradient (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3) (ν : ℕ → ℕ) (k : ℕ) :
    ParabolicPoint → Fin 3 → Vec3 :=
  fun z i => blowupLimitAssemblyTimeRamp k z.2 •
    (blowupLimitAssemblySpaceCutoff k z.1 • Df (ν k) z i +
      f (ν k) z i • classicalGradient (blowupLimitAssemblySpaceCutoff k) z.1)

/-! ### The time ramp -/

theorem blowupLimitAssemblyTimeRamp_nonneg (k : ℕ) (t : ℝ) :
    0 ≤ blowupLimitAssemblyTimeRamp k t :=
  le_max_left _ _

theorem blowupLimitAssemblyTimeRamp_le_one (k : ℕ) (t : ℝ) :
    blowupLimitAssemblyTimeRamp k t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem blowupLimitAssemblyTimeRamp_eq_zero {k : ℕ} {t : ℝ}
    (ht : t ≤ -((k : ℝ) + 1)) :
    blowupLimitAssemblyTimeRamp k t = 0 := by
  unfold blowupLimitAssemblyTimeRamp
  have hle : min 1 (t + ((k : ℝ) + 1)) ≤ 0 :=
    (min_le_right _ _).trans (by linarith only [ht])
  exact max_eq_left hle

theorem blowupLimitAssemblyTimeRamp_eq_one {k : ℕ} {t : ℝ}
    (ht : -(k : ℝ) ≤ t) :
    blowupLimitAssemblyTimeRamp k t = 1 := by
  unfold blowupLimitAssemblyTimeRamp
  have hmin : min 1 (t + ((k : ℝ) + 1)) = 1 :=
    min_eq_left (by linarith only [ht])
  rw [hmin]
  exact max_eq_right zero_le_one

/-- The time ramp is 1-Lipschitz. -/
theorem blowupLimitAssemblyTimeRamp_lipschitz (k : ℕ) (s t : ℝ) :
    |blowupLimitAssemblyTimeRamp k t - blowupLimitAssemblyTimeRamp k s| ≤
      dist t s := by
  unfold blowupLimitAssemblyTimeRamp
  rw [Real.dist_eq]
  calc
    |max 0 (min 1 (t + ((k : ℝ) + 1))) - max 0 (min 1 (s + ((k : ℝ) + 1)))|
        ≤ max |(0 : ℝ) - 0|
            |min 1 (t + ((k : ℝ) + 1)) - min 1 (s + ((k : ℝ) + 1))| :=
      abs_max_sub_max_le_max _ _ _ _
    _ = |min 1 (t + ((k : ℝ) + 1)) - min 1 (s + ((k : ℝ) + 1))| := by
      rw [sub_self, abs_zero]
      exact max_eq_right (abs_nonneg _)
    _ ≤ max |(1 : ℝ) - 1| |(t + ((k : ℝ) + 1)) - (s + ((k : ℝ) + 1))| :=
      abs_min_sub_min_le_max _ _ _ _
    _ = |t - s| := by
      rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
      ring_nf

/-- The time ramp does not see times before -(k + 1). -/
theorem blowupLimitAssemblyTimeRamp_clamp (k : ℕ) (t : ℝ) :
    blowupLimitAssemblyTimeRamp k t =
      blowupLimitAssemblyTimeRamp k (max t (-((k : ℝ) + 1))) := by
  rcases le_total t (-((k : ℝ) + 1)) with ht | ht
  · rw [max_eq_right ht, blowupLimitAssemblyTimeRamp_eq_zero ht,
      blowupLimitAssemblyTimeRamp_eq_zero le_rfl]
  · rw [max_eq_left ht]

theorem continuous_blowupLimitAssemblyTimeRamp (k : ℕ) :
    Continuous (blowupLimitAssemblyTimeRamp k) :=
  continuous_const.max (continuous_const.min
    (continuous_id.add continuous_const))

/-! ### The spatial cutoff -/

theorem blowupLimitAssemblySpaceCutoff_contDiff (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (blowupLimitAssemblySpaceCutoff k) :=
  canonicalBallCutoff_smooth 0 (Nat.cast_nonneg k) (by linarith only)

theorem blowupLimitAssemblySpaceCutoff_hasCompactSupport (k : ℕ) :
    HasCompactSupport (blowupLimitAssemblySpaceCutoff k) :=
  canonicalBallCutoff_hasCompactSupport (Nat.cast_nonneg k) (by linarith only)

theorem blowupLimitAssemblySpaceCutoff_nonneg (k : ℕ) (x : Vec3) :
    0 ≤ blowupLimitAssemblySpaceCutoff k x :=
  canonicalBallCutoff_nonneg _ _ _ _

theorem blowupLimitAssemblySpaceCutoff_le_one (k : ℕ) (x : Vec3) :
    blowupLimitAssemblySpaceCutoff k x ≤ 1 :=
  canonicalBallCutoff_le_one _ _ _ _

/-- The closed support of the k-th spatial cutoff lies in the ball of
radius k + 1. -/
theorem blowupLimitAssemblySpaceCutoff_tsupport_subset (k : ℕ) :
    tsupport (blowupLimitAssemblySpaceCutoff k) ⊆
      vec3Ball (0 : Vec3) ((k : ℝ) + 1) := by
  have hsub := canonicalBallCutoff_tsupport_subset_outer
    (x₀ := (0 : Vec3)) (Nat.cast_nonneg k)
    (by linarith only : (k : ℝ) < (k : ℝ) + 1 / 2)
  have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  rw [euclideanBall_eq_vec3Ball hpos] at hsub
  intro x hx
  have hx' := hsub hx
  rw [mem_vec3Ball] at hx' ⊢
  linarith only [hx']

/-- The spatial cutoff is one on the open ball of radius k. -/
theorem blowupLimitAssemblySpaceCutoff_eq_one {k : ℕ} {x : Vec3}
    (hx : x ∈ vec3Ball (0 : Vec3) (k : ℝ)) :
    blowupLimitAssemblySpaceCutoff k x = 1 := by
  have hk : (0 : ℝ) < k := by
    rw [mem_vec3Ball] at hx
    exact lt_of_le_of_lt (vec3EuclideanNorm_nonneg _) hx
  apply canonicalBallCutoff_eq_one_on_inner (Nat.cast_nonneg k)
    (by linarith only)
  rw [euclideanBall_eq_vec3Ball hk]
  exact hx

/-- The gradient of the spatial cutoff vanishes on the open ball of radius
k. -/
theorem blowupLimitAssemblySpaceCutoff_gradient_eq_zero {k : ℕ} {x : Vec3}
    (hx : x ∈ vec3Ball (0 : Vec3) (k : ℝ)) :
    classicalGradient (blowupLimitAssemblySpaceCutoff k) x = 0 := by
  have hev : blowupLimitAssemblySpaceCutoff k =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_vec3Ball (0 : Vec3) (k : ℝ)).mem_nhds hx] with y hy
    exact blowupLimitAssemblySpaceCutoff_eq_one hy
  funext i
  simp [classicalGradient, hev.fderiv_eq]

/-- The gradient of the spatial cutoff vanishes outside the ball of radius
k + 1. -/
theorem blowupLimitAssemblySpaceCutoff_gradient_eq_zero_of_notMem {k : ℕ}
    {x : Vec3} (hx : x ∉ vec3Ball (0 : Vec3) ((k : ℝ) + 1)) :
    classicalGradient (blowupLimitAssemblySpaceCutoff k) x = 0 := by
  have hxt : x ∉ tsupport (blowupLimitAssemblySpaceCutoff k) :=
    fun h => hx (blowupLimitAssemblySpaceCutoff_tsupport_subset k h)
  funext i
  simp [classicalGradient, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt]

/-- The spatial cutoff vanishes outside the ball of radius k + 1. -/
theorem blowupLimitAssemblySpaceCutoff_eq_zero_of_notMem {k : ℕ}
    {x : Vec3} (hx : x ∉ vec3Ball (0 : Vec3) ((k : ℝ) + 1)) :
    blowupLimitAssemblySpaceCutoff k x = 0 :=
  image_eq_zero_of_notMem_tsupport
    (fun h => hx (blowupLimitAssemblySpaceCutoff_tsupport_subset k h))

/-- The gradient of every spatial cutoff has Euclidean norm at most 64. -/
theorem blowupLimitAssemblySpaceCutoff_gradient_sq_le (k : ℕ) (x : Vec3) :
    ∑ j : Fin 3,
        (classicalGradient (blowupLimitAssemblySpaceCutoff k) x j) ^ 2 ≤
      64 ^ 2 := by
  have hbound := canonicalBallCutoff_gradient_bound (x₀ := (0 : Vec3))
    (Nat.cast_nonneg k) (by linarith only : (k : ℝ) < (k : ℝ) + 1 / 2) x
  have hgap : (32 : ℝ) / ((k : ℝ) + 1 / 2 - k) = 64 := by
    ring_nf
  rw [hgap] at hbound
  have hsq := vecEuclideanNorm_sq
    (classicalGradient (blowupLimitAssemblySpaceCutoff k) x)
  rw [vecNormSq_eq_sum_sq] at hsq
  rw [← hsq]
  have hnn := vecEuclideanNorm_nonneg
    (classicalGradient (blowupLimitAssemblySpaceCutoff k) x)
  exact pow_le_pow_left₀ hnn hbound 2

theorem continuous_blowupLimitAssemblySpaceCutoff_gradient (k : ℕ) :
    Continuous (classicalGradient (blowupLimitAssemblySpaceCutoff k)) := by
  have hs := blowupLimitAssemblySpaceCutoff_contDiff k
  apply continuous_pi
  intro i
  exact (hs.continuous_fderiv (by simp)).clm_apply continuous_const

/-! ### The modified fields -/

theorem measurable_blowupLimitAssemblyCutoffField
    (f : ℕ → ParabolicPoint → Vec3) (ν : ℕ → ℕ)
    (hf : ∀ n, Measurable (f n)) (k : ℕ) :
    Measurable (blowupLimitAssemblyCutoffField f ν k) := by
  have hT : Measurable (fun z : ParabolicPoint =>
      blowupLimitAssemblyTimeRamp k z.2) :=
    (continuous_blowupLimitAssemblyTimeRamp k).measurable.comp measurable_snd
  have hS : Measurable (fun z : ParabolicPoint =>
      blowupLimitAssemblySpaceCutoff k z.1) :=
    (blowupLimitAssemblySpaceCutoff_contDiff k).continuous.measurable.comp
      measurable_fst
  exact (hT.mul hS).smul (hf (ν k))

theorem measurable_blowupLimitAssemblyCutoffGradient
    (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3) (ν : ℕ → ℕ)
    (hf : ∀ n, Measurable (f n)) (hDf : ∀ n, Measurable (Df n)) (k : ℕ) :
    Measurable (blowupLimitAssemblyCutoffGradient f Df ν k) := by
  have hT : Measurable (fun z : ParabolicPoint =>
      blowupLimitAssemblyTimeRamp k z.2) :=
    (continuous_blowupLimitAssemblyTimeRamp k).measurable.comp measurable_snd
  have hS : Measurable (fun z : ParabolicPoint =>
      blowupLimitAssemblySpaceCutoff k z.1) :=
    (blowupLimitAssemblySpaceCutoff_contDiff k).continuous.measurable.comp
      measurable_fst
  have hG : Measurable (fun z : ParabolicPoint =>
      classicalGradient (blowupLimitAssemblySpaceCutoff k) z.1) :=
    (continuous_blowupLimitAssemblySpaceCutoff_gradient k).measurable.comp
      measurable_fst
  apply Measurable.of_eval
  intro i
  have hDi : Measurable (fun z => Df (ν k) z i) :=
    (measurable_pi_apply i).comp (hDf (ν k))
  have hfi : Measurable (fun z => f (ν k) z i) :=
    (measurable_pi_apply i).comp (hf (ν k))
  exact hT.smul ((hS.smul hDi).add (hfi.smul hG))

/-- The modified velocity is pointwise no larger than the original one. -/
theorem blowupLimitAssemblyCutoffField_norm_le
    (f : ℕ → ParabolicPoint → Vec3) (ν : ℕ → ℕ) (k : ℕ) (z : ParabolicPoint) :
    vec3EuclideanNorm (blowupLimitAssemblyCutoffField f ν k z) ≤
      vec3EuclideanNorm (f (ν k) z) := by
  set c : ℝ := blowupLimitAssemblyTimeRamp k z.2 *
    blowupLimitAssemblySpaceCutoff k z.1 with hc
  have hc0 : 0 ≤ c := mul_nonneg (blowupLimitAssemblyTimeRamp_nonneg k z.2)
    (blowupLimitAssemblySpaceCutoff_nonneg k z.1)
  have hc1 : c ≤ 1 := by
    have h1 := blowupLimitAssemblyTimeRamp_le_one k z.2
    have h2 := blowupLimitAssemblySpaceCutoff_le_one k z.1
    have h3 := blowupLimitAssemblyTimeRamp_nonneg k z.2
    calc
      c ≤ 1 * 1 := mul_le_mul h1 h2
        (blowupLimitAssemblySpaceCutoff_nonneg k z.1) zero_le_one
      _ = 1 := one_mul 1
  change vec3EuclideanNorm (c • f (ν k) z) ≤ vec3EuclideanNorm (f (ν k) z)
  have hsq : ∑ i : Fin 3, (c • f (ν k) z) i ^ 2 ≤ ∑ i : Fin 3, (f (ν k) z i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    have hc2 : c ^ 2 ≤ 1 := by nlinarith only [hc0, hc1]
    have hsq0 : 0 ≤ (f (ν k) z i) ^ 2 := sq_nonneg _
    calc
      c ^ 2 * f (ν k) z i ^ 2 ≤ 1 * f (ν k) z i ^ 2 :=
        mul_le_mul_of_nonneg_right hc2 hsq0
      _ = f (ν k) z i ^ 2 := one_mul _
  exact Real.sqrt_le_sqrt hsq

/-- On the cylinder where both cutoffs equal one, the modified velocity and
its gradient are the original fields. -/
theorem blowupLimitAssemblyCutoff_eq_of_mem
    (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3) (ν : ℕ → ℕ) {k : ℕ}
    {z : ParabolicPoint} (hx : z.1 ∈ vec3Ball (0 : Vec3) (k : ℝ))
    (ht : -(k : ℝ) ≤ z.2) :
    blowupLimitAssemblyCutoffField f ν k z = f (ν k) z ∧
      blowupLimitAssemblyCutoffGradient f Df ν k z = Df (ν k) z := by
  have hT := blowupLimitAssemblyTimeRamp_eq_one (k := k) ht
  have hS := blowupLimitAssemblySpaceCutoff_eq_one hx
  have hG := blowupLimitAssemblySpaceCutoff_gradient_eq_zero hx
  constructor
  · simp [blowupLimitAssemblyCutoffField, hT, hS]
  · funext i
    simp [blowupLimitAssemblyCutoffGradient, hT, hS, hG]

/-- For every point, the modified fields agree with the original fields from
some index on, uniformly on bounded sets. -/
theorem blowupLimitAssemblyCutoff_eventually_eq
    (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3) (ν : ℕ → ℕ) (ρ : ℝ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ z : ParabolicPoint,
      vec3EuclideanNorm z.1 ≤ ρ → -ρ ≤ z.2 →
        blowupLimitAssemblyCutoffField f ν k z = f (ν k) z ∧
          blowupLimitAssemblyCutoffGradient f Df ν k z = Df (ν k) z := by
  obtain ⟨K, hK⟩ := exists_nat_gt ρ
  refine ⟨K, fun k hk z hz ht => ?_⟩
  have hkK : (K : ℝ) ≤ k := by exact_mod_cast hk
  apply blowupLimitAssemblyCutoff_eq_of_mem f Df ν
  · rw [mem_vec3Ball, sub_zero]
    linarith only [hz, hK, hkK]
  · linarith only [ht, hK, hkK]

/-- Scalar multiples preserve whole-space weak gradients. -/
theorem blowupLimitAssembly_hasWeakGradientOn_univ_const_mul
    {u : Vec3 → ℝ} {G : Vec3 → Vec3} (c : ℝ)
    (h : HasWeakGradientOn (Set.univ : Set Vec3) u G) :
    HasWeakGradientOn (Set.univ : Set Vec3) (fun x => c * u x)
      (fun x => c • G x) := by
  intro i φ hφ hφc hφU
  have hi := h i φ hφ hφc hφU
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∫ x in Set.univ, c * u x * (fderiv ℝ φ x) (basisVec i)) =
        c * ∫ x in Set.univ, u x * (fderiv ℝ φ x) (basisVec i) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = c * -∫ x in Set.univ, G x i * φ x := by rw [hi]
    _ = -∫ x in Set.univ, c * G x i * φ x := by
      rw [mul_neg, ← integral_const_mul]
      congr 1
      congr 1
      funext x
      ring

/-- The modified velocity slices have the modified gradient as weak
gradient on all of space, for almost every negative time, once the original
slices have weak gradients in the ball of radius k + 1 after time
-(k + 1) with locally integrable data. -/
theorem blowupLimitAssemblyCutoff_hasWeakGradientOn
    (f : ℕ → ParabolicPoint → Vec3)
    (Df : ℕ → ParabolicPoint → Fin 3 → Vec3) (ν : ℕ → ℕ) (k : ℕ)
    (hweak : ∀ᵐ t ∂(volume.restrict (Ioo (-((k : ℝ) + 1)) 0)),
      (∀ i : Fin 3, HasWeakGradientOn (vec3Ball (0 : Vec3) ((k : ℝ) + 1))
        (fun x => f (ν k) (x,t) i) (fun x => Df (ν k) (x,t) i)) ∧
      (∀ i : Fin 3, IntegrableOn (fun x => f (ν k) (x,t) i)
        (vec3Ball (0 : Vec3) ((k : ℝ) + 1))) ∧
      (∀ i j : Fin 3, IntegrableOn (fun x => Df (ν k) (x,t) i j)
        (vec3Ball (0 : Vec3) ((k : ℝ) + 1)))) :
    ∀ᵐ t ∂(volume.restrict (Iio (0 : ℝ))), ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => blowupLimitAssemblyCutoffField f ν k (x,t) i)
        (fun x => blowupLimitAssemblyCutoffGradient f Df ν k (x,t) i) := by
  have hweak' := (ae_restrict_iff' measurableSet_Ioo).1 hweak
  rw [ae_restrict_iff' measurableSet_Iio]
  filter_upwards [hweak'] with t ht htneg i
  rcases le_or_gt t (-((k : ℝ) + 1)) with hle | hlt
  · have hT := blowupLimitAssemblyTimeRamp_eq_zero hle
    have hfun : (fun x => blowupLimitAssemblyCutoffField f ν k (x,t) i) =
        fun x => (0 : ℝ) * (0 : ℝ) := by
      funext x
      simp [blowupLimitAssemblyCutoffField, hT]
    have hgrad : (fun x => blowupLimitAssemblyCutoffGradient f Df ν k (x,t) i) =
        fun x => (0 : ℝ) • (0 : Vec3) := by
      funext x
      simp [blowupLimitAssemblyCutoffGradient, hT]
    rw [hfun, hgrad]
    intro m φ _ _ _
    simp
  · obtain ⟨hgradt, hfint, hDint⟩ := ht ⟨hlt, htneg⟩
    let U : Set Vec3 := vec3Ball (0 : Vec3) ((k : ℝ) + 1)
    have hU : IsOpen U := isOpen_vec3Ball _ _
    have hprod := HasWeakGradientOn.mul_smooth_zeroExtend hU
      ((hfint i).locallyIntegrableOn)
      (fun m => (hDint i m).locallyIntegrableOn) (hgradt i)
      (blowupLimitAssemblySpaceCutoff_contDiff k)
      (blowupLimitAssemblySpaceCutoff_hasCompactSupport k)
      (blowupLimitAssemblySpaceCutoff_tsupport_subset k)
    have hscaled := blowupLimitAssembly_hasWeakGradientOn_univ_const_mul
      (blowupLimitAssemblyTimeRamp k t) hprod
    have hfun : (fun x => blowupLimitAssemblyCutoffField f ν k (x,t) i) =
        fun x => blowupLimitAssemblyTimeRamp k t *
          (blowupLimitAssemblySpaceCutoff k x * f (ν k) (x,t) i) := by
      funext x
      simp only [blowupLimitAssemblyCutoffField, Pi.smul_apply, smul_eq_mul]
      ring
    have hgrad : (fun x => blowupLimitAssemblyCutoffGradient f Df ν k (x,t) i) =
        fun x => blowupLimitAssemblyTimeRamp k t •
          (blowupLimitAssemblySpaceCutoff k x • Df (ν k) (x,t) i +
            f (ν k) (x,t) i • classicalGradient
              (blowupLimitAssemblySpaceCutoff k) x) := by
      funext x
      rfl
    rw [hfun, hgrad]
    exact hscaled

end ESS

end
