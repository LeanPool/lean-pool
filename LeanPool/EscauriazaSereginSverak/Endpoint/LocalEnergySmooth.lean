/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.IntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Foundation.SpaceTimeMollifier
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivMollify
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Constructor
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace ESS

local instance localEnergyVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

/-- Directional derivative on product spacetime. -/
@[expose] def dirDeriv (f : Vec3 × ℝ → ℝ) (v z : Vec3 × ℝ) : ℝ :=
  (fderiv ℝ f z) v

/-- The `i`th spatial coordinate direction on product spacetime. -/
@[expose] def spatialDir (i : Fin 3) : Vec3 × ℝ := (basisVec i, 0)

/-- The time coordinate direction on product spacetime. -/
@[expose] def timeDir : Vec3 × ℝ := (0, 1)

/-- The squared Euclidean norm of a vector-valued velocity. -/
@[expose] def velocitySq (u : Vec3 × ℝ → Vec3) : Vec3 × ℝ → ℝ :=
  fun z => ∑ i : Fin 3, u z i * u z i

/-- A directional derivative of a smooth scalar function is continuously differentiable. -/
theorem dirDeriv_contDiff_one {f : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec3 × ℝ) :
    ContDiff ℝ (1 : ℕ∞) (fun z => dirDeriv f v z) := by
  have hfd : ContDiff ℝ (1 : ℕ∞)
      (fun q : (Vec3 × ℝ) × (Vec3 × ℝ) => (fderiv ℝ f q.1) q.2) := by
    exact hf.contDiff_fderiv_apply (m := (1 : ℕ∞)) (by norm_num)
  have hmap : ContDiff ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => (z, v)) := by
    fun_prop
  change ContDiff ℝ (1 : ℕ∞) (fun z => (fderiv ℝ f z) v)
  convert hfd.comp hmap using 1
  funext z
  rfl

private theorem dirDeriv_mul
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ∞) f)
    (hg : ContDiff ℝ (1 : ℕ∞) g) (v z : Vec3 × ℝ) :
    dirDeriv (fun y => f y * g y) v z =
      dirDeriv f v z * g z + f z * dirDeriv g v z := by
  rw [dirDeriv, fderiv_fun_mul
    ((hf.differentiable (by norm_num)).differentiableAt)
    ((hg.differentiable (by norm_num)).differentiableAt)]
  simp [dirDeriv, smul_eq_mul]
  ring

private theorem dirDeriv_sum {ι : Type*} [Fintype ι]
    (f : ι → Vec3 × ℝ → ℝ) (v z : Vec3 × ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    dirDeriv (fun y => ∑ i, f i y) v z = ∑ i, dirDeriv (f i) v z := by
  change (fderiv ℝ (fun y => ∑ i : ι, f i y) z) v = _
  rw [fderiv_fun_sum (u := Finset.univ) (fun i hi => hf i)]
  simp [dirDeriv]

private theorem dirDeriv_velocitySq
    {u : Vec3 × ℝ → Vec3} (hu : ∀ i, ContDiff ℝ (1 : ℕ∞) (fun z => u z i))
    (v z : Vec3 × ℝ) :
    dirDeriv (velocitySq u) v z =
      2 * ∑ i : Fin 3, u z i * dirDeriv (fun y => u y i) v z := by
  unfold velocitySq
  rw [dirDeriv_sum (f := fun i y => u y i * u y i)
    (v := v) (z := z)
    (hf := fun i => ((((hu i).mul (hu i)).differentiable (by norm_num)).differentiableAt))]
  calc
    (∑ i : Fin 3,
      dirDeriv (fun y => u y i * u y i) v z) =
        ∑ i : Fin 3, 2 * (u z i * dirDeriv (fun y => u y i) v z) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [dirDeriv_mul (hu i) (hu i) v z]
          ring
    _ = 2 * ∑ i : Fin 3,
        u z i * dirDeriv (fun y => u y i) v z := by
          rw [Finset.mul_sum]

/-- Integration by parts in a fixed space-time direction for smooth functions when the
second factor is compactly supported. -/
theorem smoothIntegral_dirDeriv_mul_eq_neg
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ∞) f)
    (hg : ContDiff ℝ (1 : ℕ∞) g) (hgc : HasCompactSupport g)
    (v : Vec3 × ℝ) :
    ∫ z, f z * dirDeriv g v z ∂(volume : Measure (Vec3 × ℝ)) =
      -∫ z, dirDeriv f v z * g z ∂(volume : Measure (Vec3 × ℝ)) := by
  have hDf : Continuous (fun z => dirDeriv f v z) := by
    exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDg : Continuous (fun z => dirDeriv g v z) := by
    exact (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDgc : HasCompactSupport (fun z => dirDeriv g v z) := by
    exact hgc.fderiv_apply (𝕜 := ℝ) v
  have hfg : Integrable (fun z => f z * g z) (volume : Measure (Vec3 × ℝ)) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hgc.mul_left)
  have hfDg : Integrable (fun z => f z * dirDeriv g v z)
      (volume : Measure (Vec3 × ℝ)) :=
    (hf.continuous.mul hDg).integrable_of_hasCompactSupport (hDgc.mul_left)
  have hDfg : Integrable (fun z => dirDeriv f v z * g z)
      (volume : Measure (Vec3 × ℝ)) :=
    (hDf.mul hg.continuous).integrable_of_hasCompactSupport (hgc.mul_left)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hDfg hfDg hfg
    (fun z hz => (hf.differentiable (by norm_num)).differentiableAt)
    (fun z hz => (hg.differentiable (by norm_num)).differentiableAt)

private theorem dirDeriv_const_mul
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ∞) f)
    (c : ℝ) (v z : Vec3 × ℝ) :
    dirDeriv (fun y => c * f y) v z = c * dirDeriv f v z := by
  rw [dirDeriv, fderiv_fun_mul
    ((contDiff_const : ContDiff ℝ (1 : ℕ∞) fun _ : Vec3 × ℝ => c).differentiable
      (by norm_num) |>.differentiableAt)
    ((hf.differentiable (by norm_num)).differentiableAt)]
  simp [dirDeriv, smul_eq_mul]

/-- The weak momentum integrand after substituting a smooth velocity test. -/
@[expose] def smoothMomentumTestIntegrand
    (u : Vec3 × ℝ → Vec3) (R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (p : Vec3 × ℝ → ℝ) (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ :=
  (-(∑ i : Fin 3, u z i * dirDeriv (fun y => φ y i) timeDir z))
    - ∑ i : Fin 3, ∑ j : Fin 3,
        (u z i * u z j + R z i j) * dirDeriv (fun y => φ y i) (spatialDir j) z
    + ∑ i : Fin 3, ∑ j : Fin 3,
        G z i j * dirDeriv (fun y => φ y i) (spatialDir j) z
    - p z * ∑ i : Fin 3, dirDeriv (fun y => φ y i) (spatialDir i) z

/-- The expanded energy integrand after the smooth velocity test substitution. -/
@[expose] def smoothEnergyTestIntegrand
    (u : Vec3 × ℝ → Vec3) (R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (p ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  -2 * velocitySq u z * dirDeriv ψ timeDir z
    - ψ z * dirDeriv (velocitySq u) timeDir z
    - 2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (u z i * u z j + R z i j) *
          (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)
    + 2 * ∑ i : Fin 3, ∑ j : Fin 3,
        G z i j * (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)
    - ∑ i : Fin 3, p z *
        (2 * (u z i * dirDeriv ψ (spatialDir i) z +
          ψ z * G z i i))

private theorem smoothEnergy_timeSum
    {u : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hu : ∀ i, ContDiff ℝ (1 : ℕ∞) (fun z => u z i))
    (hψ : ContDiff ℝ (1 : ℕ∞) ψ) (z : Vec3 × ℝ) :
    ∑ i : Fin 3, u z i *
        dirDeriv (fun y => 2 * ψ y * u y i) timeDir z =
      2 * velocitySq u z * dirDeriv ψ timeDir z +
        ψ z * dirDeriv (velocitySq u) timeDir z := by
  have hdt (i : Fin 3) :
      dirDeriv (fun y => 2 * ψ y * u y i) timeDir z =
        2 * (dirDeriv ψ timeDir z * u z i +
          ψ z * dirDeriv (fun y => u y i) timeDir z) := by
    have hfun : (fun y => 2 * ψ y * u y i) = fun y => 2 * (ψ y * u y i) := by
      funext y
      ring
    rw [hfun, dirDeriv_const_mul ((hψ.of_le (by norm_num)).mul (hu i)) 2 timeDir z,
      dirDeriv_mul hψ (hu i)]
  simp_rw [hdt]
  have hsum :
      (∑ i : Fin 3,
        u z i * (2 * (dirDeriv ψ timeDir z * u z i +
          ψ z * dirDeriv (fun y => u y i) timeDir z))) =
       2 * dirDeriv ψ timeDir z * ∑ i : Fin 3, u z i * u z i +
         2 * ψ z * ∑ i : Fin 3, u z i * dirDeriv (fun y => u y i) timeDir z := by
    calc
      _ = ∑ i : Fin 3,
          ((2 * dirDeriv ψ timeDir z) * (u z i * u z i) +
            (2 * ψ z) * (u z i * dirDeriv (fun y => u y i) timeDir z)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsum, dirDeriv_velocitySq hu timeDir z]
  unfold velocitySq
  ring

/-- Substituting the smooth velocity test `2 ψ u` into the momentum identity gives the
expanded integrand used in the local energy calculation. -/
private theorem smoothMomentumTestIntegrand_eq_energy_on_support
    {u : Vec3 × ℝ → Vec3} {R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p ψ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => u z i))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hgrad : ∀ i j : Fin 3,
      dirDeriv (fun y => u y i) (spatialDir j) z = G z i j) :
    smoothMomentumTestIntegrand u R G p ((fun z => 2 * ψ z) • u) z =
      smoothEnergyTestIntegrand u R G p ψ z := by
  have hdt (i : Fin 3) :
      dirDeriv (fun y => 2 * ψ y * u y i) timeDir z =
        2 * (dirDeriv ψ timeDir z * u z i +
          ψ z * dirDeriv (fun y => u y i) timeDir z) := by
    have hfun : (fun y => 2 * ψ y * u y i) = fun y => 2 * (ψ y * u y i) := by
      funext y
      ring
    rw [hfun, dirDeriv_const_mul ((hψ.of_le (by norm_num)).mul
        ((hu i).of_le (by norm_num))) 2 timeDir z,
      dirDeriv_mul (hψ.of_le (by norm_num)) ((hu i).of_le (by norm_num))]
  have hdx (i j : Fin 3) :
      dirDeriv (fun y => 2 * ψ y * u y i) (spatialDir j) z =
        2 * (dirDeriv ψ (spatialDir j) z * u z i + ψ z * G z i j) := by
    have hfun : (fun y => 2 * ψ y * u y i) = fun y => 2 * (ψ y * u y i) := by
      funext y
      ring
    rw [hfun, dirDeriv_const_mul ((hψ.of_le (by norm_num)).mul
        ((hu i).of_le (by norm_num))) 2 (spatialDir j) z,
      dirDeriv_mul (hψ.of_le (by norm_num)) ((hu i).of_le (by norm_num)),
      hgrad i j]
  have htimeSum :
      ∑ i : Fin 3, u z i *
          dirDeriv (fun y => 2 * ψ y * u y i) timeDir z =
        2 * velocitySq u z * dirDeriv ψ timeDir z +
          ψ z * dirDeriv (velocitySq u) timeDir z := by
    simpa [mul_assoc] using smoothEnergy_timeSum
      (fun i => (hu i).of_le (by norm_num)) (hψ.of_le (by norm_num)) z
  dsimp [smoothMomentumTestIntegrand, smoothEnergyTestIntegrand]
  rw [htimeSum]
  simp_rw [hdx]
  have hconv :
      (∑ i : Fin 3, ∑ j : Fin 3,
        (u z i * u z j + R z i j) *
          (2 * (dirDeriv ψ (spatialDir j) z * u z i + ψ z * G z i j))) =
        2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (u z i * u z j + R z i j) *
            (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          2 * ((u z i * u z j + R z i j) *
            (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = _ := by simp_rw [Finset.mul_sum]
  have hvisc :
      (∑ i : Fin 3, ∑ j : Fin 3,
        G z i j *
          (2 * (dirDeriv ψ (spatialDir j) z * u z i + ψ z * G z i j))) =
        2 * ∑ i : Fin 3, ∑ j : Fin 3,
          G z i j *
            (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          2 * (G z i j *
            (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = _ := by simp_rw [Finset.mul_sum]
  have hpressure :
      p z * (∑ i : Fin 3,
        2 * (dirDeriv ψ (spatialDir i) z * u z i + ψ z * G z i i)) =
        ∑ i : Fin 3,
          p z * (2 * (u z i * dirDeriv ψ (spatialDir i) z + ψ z * G z i i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hconv, hvisc, hpressure]
  ring

@[expose] def smoothVelocityTest (u : Vec3 × ℝ → Vec3) (ψ : Vec3 × ℝ → ℝ) :
    Vec3 × ℝ → Vec3 := (fun z => 2 * ψ z) • u

private theorem smoothVelocityTest_contDiff
    {u : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => u z i))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothVelocityTest u ψ) := by
  have huVec : ContDiff ℝ (⊤ : ℕ∞) u := by
    rw [contDiff_pi]
    exact hu
  change ContDiff ℝ (⊤ : ℕ∞) (fun z => (2 * ψ z) • u z)
  have hscalar : ContDiff ℝ (⊤ : ℕ∞) (fun z => 2 * ψ z) := by fun_prop
  exact hscalar.smul huVec

private theorem smoothVelocityTest_support
    {u : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ} :
    Function.support (smoothVelocityTest u ψ) ⊆ tsupport ψ := by
  change Function.support ((fun z => 2 * ψ z) • u) ⊆ tsupport ψ
  calc
    Function.support ((fun z => 2 * ψ z) • u) ⊆ Function.support (fun z => 2 * ψ z) :=
      Function.support_smul_subset_left _ _
    _ ⊆ tsupport (fun z => 2 * ψ z) := subset_tsupport _
    _ ⊆ tsupport ψ := tsupport_mul_subset_right

private theorem smoothVelocityTest_tsupport
    {u : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ} :
    tsupport (smoothVelocityTest u ψ) ⊆ tsupport ψ := by
  apply closure_minimal smoothVelocityTest_support
  exact isClosed_tsupport (f := ψ)

private theorem smoothMomentumTestIntegrand_eq_energy_off_support
    {u : Vec3 × ℝ → Vec3} {R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p ψ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hφtsupport : tsupport (smoothVelocityTest u ψ) ⊆ tsupport ψ)
    (hz : z ∉ tsupport ψ) :
    smoothMomentumTestIntegrand u R G p (smoothVelocityTest u ψ) z =
      smoothEnergyTestIntegrand u R G p ψ z := by
  have hφderiv (i : Fin 3) (v : Vec3 × ℝ) :
      dirDeriv (fun y => smoothVelocityTest u ψ y i) v z = 0 := by
    have hzφ : z ∉ tsupport (smoothVelocityTest u ψ) := fun h => hz (hφtsupport h)
    have hnear : (fun y => smoothVelocityTest u ψ y i) =ᶠ[𝓝 z] 0 := by
      filter_upwards [(isClosed_tsupport (f := smoothVelocityTest u ψ)).isOpen_compl.eventually_mem hzφ]
        with y hy
      have hyzero : smoothVelocityTest u ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hyzero]
    rw [dirDeriv, Filter.EventuallyEq.fderiv_eq hnear]
    simp
  have hψderiv (v : Vec3 × ℝ) : dirDeriv ψ v z = 0 := by
    rw [dirDeriv, fderiv_of_notMem_tsupport ℝ hz]
    simp
  have hψzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [smoothMomentumTestIntegrand, smoothEnergyTestIntegrand,
    hφderiv, hψderiv, hψzero]

private theorem smoothMomentumTestIntegrand_eq_energy_everywhere
    {u : Vec3 × ℝ → Vec3} {R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p ψ : Vec3 × ℝ → ℝ}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => u z i))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hφtsupport : tsupport (smoothVelocityTest u ψ) ⊆ tsupport ψ)
    (hgrad : ∀ z ∈ tsupport ψ, ∀ i j : Fin 3,
      dirDeriv (fun y => u y i) (spatialDir j) z = G z i j) :
    ∀ z, smoothMomentumTestIntegrand u R G p (smoothVelocityTest u ψ) z =
      smoothEnergyTestIntegrand u R G p ψ z := by
  intro z
  by_cases hz : z ∈ tsupport ψ
  · change smoothMomentumTestIntegrand u R G p ((fun z => 2 * ψ z) • u) z =
      smoothEnergyTestIntegrand u R G p ψ z
    exact smoothMomentumTestIntegrand_eq_energy_on_support hu hψ
      (fun i j => hgrad z hz i j)
  · exact smoothMomentumTestIntegrand_eq_energy_off_support hφtsupport hz

/-- Testing a smooth momentum identity with twice the velocity times a compact scalar test
produces the expanded energy identity. -/
theorem smoothMomentum_tested_energy
    {u : Vec3 × ℝ → Vec3} {R : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ} {p ψ : Vec3 × ℝ → ℝ}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => u z i))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hweak : ∀ φ : Vec3 × ℝ → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ tsupport ψ →
      ∫ z, smoothMomentumTestIntegrand u R G p φ z = 0)
    (hgrad : ∀ z ∈ tsupport ψ, ∀ i j : Fin 3,
      dirDeriv (fun y => u y i) (spatialDir j) z = G z i j) :
    ∫ z, smoothEnergyTestIntegrand u R G p ψ z = 0 := by
  let φ := smoothVelocityTest u ψ
  have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    change ContDiff ℝ (⊤ : ℕ∞) (smoothVelocityTest u ψ)
    exact smoothVelocityTest_contDiff hu hψ
  have hφcompact : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact hψc.isCompact
      (by change Function.support (smoothVelocityTest u ψ) ⊆ tsupport ψ
          exact smoothVelocityTest_support)
  have hφtsupport : tsupport φ ⊆ tsupport ψ := by
    change tsupport (smoothVelocityTest u ψ) ⊆ tsupport ψ
    exact smoothVelocityTest_tsupport
  have htest : ∫ z, smoothMomentumTestIntegrand u R G p φ z = 0 :=
    hweak φ hφsmooth hφcompact hφtsupport
  have hEq := smoothMomentumTestIntegrand_eq_energy_everywhere
    (R := R) (p := p) hu hψ
    hφtsupport hgrad
  calc
    ∫ z, smoothEnergyTestIntegrand u R G p ψ z =
        ∫ z, smoothMomentumTestIntegrand u R G p φ z := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (hEq z).symm
    _ = 0 := htest

/-- The base energy density produced from a smooth momentum identity after collecting the
velocity, pressure, stress, and gradient terms. -/
@[expose] def smoothEnergyBaseIntegrand
    (u : Vec3 × ℝ → Vec3) (R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (p ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  -velocitySq u z *
      (dirDeriv ψ timeDir z + ∑ j : Fin 3,
        dirDeriv (fun y => dirDeriv ψ (spatialDir j) y) (spatialDir j) z)
    - (velocitySq u z + 2 * p z) *
        ∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z
    - 2 * ∑ i : Fin 3, ∑ j : Fin 3,
        R z i j * (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)
    + 2 * (∑ i : Fin 3, ∑ j : Fin 3, G z i j * G z i j) * ψ z

/-- The total derivative terms in the smooth energy test identity. -/
@[expose] def smoothEnergyTotalDerivative
    (u : Vec3 × ℝ → Vec3) (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  -dirDeriv (fun y => velocitySq u y * ψ y) timeDir z
    - ∑ j : Fin 3,
        dirDeriv (fun y => ψ y * velocitySq u y * u y j) (spatialDir j) z
    + ∑ j : Fin 3,
        dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
          (spatialDir j) z

/-- The smooth energy test density is the sum of its base density and a total derivative. -/
theorem smoothEnergyTestIntegrand_eq_base_add_totalDerivative
    {u : Vec3 × ℝ → Vec3} {R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p ψ : Vec3 × ℝ → ℝ}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => u z i))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hgrad : ∀ z ∈ tsupport ψ, ∀ i j : Fin 3,
      dirDeriv (fun y => u y i) (spatialDir j) z = G z i j)
    (hdiv : ∀ z ∈ tsupport ψ, ∑ i : Fin 3, G z i i = 0)
    (z : Vec3 × ℝ) (hz : z ∈ tsupport ψ) :
    smoothEnergyTestIntegrand u R G p ψ z =
      smoothEnergyBaseIntegrand u R G p ψ z +
        smoothEnergyTotalDerivative u ψ z := by
  have hu1 (i : Fin 3) : ContDiff ℝ (1 : ℕ∞) (fun y => u y i) :=
    (hu i).of_le (by norm_num)
  have hψ1 : ContDiff ℝ (1 : ℕ∞) ψ := hψ.of_le (by norm_num)
  have hq : ContDiff ℝ (⊤ : ℕ∞) (velocitySq u) := by
    unfold velocitySq
    fun_prop
  have hq1 : ContDiff ℝ (1 : ℕ∞) (velocitySq u) := hq.of_le (by norm_num)
  have hqSpatial (j : Fin 3) :
      dirDeriv (velocitySq u) (spatialDir j) z =
        2 * ∑ i : Fin 3, u z i * G z i j := by
    rw [dirDeriv_velocitySq hu1]
    apply congrArg (fun a : ℝ => 2 * a)
    apply Finset.sum_congr rfl
    intro i hi
    rw [hgrad z hz i j]
  have hconvAlg :
      2 * ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * G z i j =
        ∑ j : Fin 3, u z j * dirDeriv (velocitySq u) (spatialDir j) z := by
    calc
      _ = 2 * ∑ j : Fin 3, ∑ i : Fin 3, u z i * u z j * G z i j := by
        congr 1
        exact Finset.sum_comm
      _ = 2 * ∑ j : Fin 3, u z j * (∑ i : Fin 3, u z i * G z i j) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (∑ i : Fin 3, u z i * u z j * G z i j) =
              ∑ i : Fin 3, u z j * (u z i * G z i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = u z j * (∑ i : Fin 3, u z i * G z i j) := by
            rw [Finset.mul_sum]
      _ = ∑ j : Fin 3, u z j * dirDeriv (velocitySq u) (spatialDir j) z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        calc
          2 * (u z j * (∑ i : Fin 3, u z i * G z i j)) =
              u z j * (2 * ∑ i : Fin 3, u z i * G z i j) := by ring
          _ = u z j * dirDeriv (velocitySq u) (spatialDir j) z := by
            rw [← hqSpatial j]
  have htimeFlux :
      dirDeriv (fun y => velocitySq u y * ψ y) timeDir z =
        dirDeriv (velocitySq u) timeDir z * ψ z +
          velocitySq u z * dirDeriv ψ timeDir z :=
    dirDeriv_mul hq1 hψ1 timeDir z
  have hconvFlux (j : Fin 3) :
      dirDeriv (fun y => ψ y * velocitySq u y * u y j) (spatialDir j) z =
        dirDeriv ψ (spatialDir j) z * velocitySq u z * u z j
          + ψ z * dirDeriv (velocitySq u) (spatialDir j) z * u z j
          + ψ z * velocitySq u z * G z j j := by
    have hleft : ContDiff ℝ (1 : ℕ∞) (fun y => ψ y * velocitySq u y) := hψ1.mul hq1
    rw [dirDeriv_mul hleft (hu1 j) (spatialDir j) z,
      dirDeriv_mul hψ1 hq1 (spatialDir j) z, hgrad z hz j j]
    ring
  have hviscFlux (j : Fin 3) :
      dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
          (spatialDir j) z =
        dirDeriv (velocitySq u) (spatialDir j) z *
            dirDeriv ψ (spatialDir j) z
          + velocitySq u z *
            dirDeriv (fun y => dirDeriv ψ (spatialDir j) y) (spatialDir j) z := by
    exact dirDeriv_mul hq1 (dirDeriv_contDiff_one (f := ψ) hψ (spatialDir j))
      (spatialDir j) z
  have hquad :
      ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * (u z i * dirDeriv ψ (spatialDir j) z) =
      velocitySq u z * (∑ j : Fin 3, u z j * dirDeriv ψ (spatialDir j) z) := by
    calc
      _ = ∑ j : Fin 3, ∑ i : Fin 3,
          (u z i * u z i) * (u z j * dirDeriv ψ (spatialDir j) z) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ j : Fin 3,
          (velocitySq u z) * (u z j * dirDeriv ψ (spatialDir j) z) := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold velocitySq
        rw [← Finset.sum_mul]
      _ = velocitySq u z * (∑ j : Fin 3, u z j * dirDeriv ψ (spatialDir j) z) := by
        rw [← Finset.mul_sum]
  have hconvG :
      2 * ψ z * (∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * G z i j) =
        ψ z * (∑ j : Fin 3, u z j * dirDeriv (velocitySq u) (spatialDir j) z) := by
    calc
      _ = ψ z * (2 * ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * G z i j) := by ring
      _ = _ := congrArg (fun a : ℝ => ψ z * a) hconvAlg
  have hviscG :
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
          G z i j * (u z i * dirDeriv ψ (spatialDir j) z) =
        ∑ j : Fin 3,
          dirDeriv (velocitySq u) (spatialDir j) z * dirDeriv ψ (spatialDir j) z := by
    calc
      _ = 2 * ∑ j : Fin 3, ∑ i : Fin 3,
          (u z i * G z i j) * dirDeriv ψ (spatialDir j) z := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ j : Fin 3,
          (2 * ∑ i : Fin 3, u z i * G z i j) *
            dirDeriv ψ (spatialDir j) z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_mul]
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hqSpatial j]
  have hdivTerm :
      velocitySq u z * ψ z * (∑ i : Fin 3, G z i i) = 0 := by
    rw [hdiv z hz]
    ring
  have hconvU :
      -(2 * ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)) =
      -2 * velocitySq u z * (∑ j : Fin 3, u z j * dirDeriv ψ (spatialDir j) z)
        - ψ z * (∑ j : Fin 3, u z j * dirDeriv (velocitySq u) (spatialDir j) z) := by
    have hsplit :
        ∑ i : Fin 3, ∑ j : Fin 3,
          u z i * u z j * (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j) =
          (∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * (u z i * dirDeriv ψ (spatialDir j) z))
            + ψ z * (∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * G z i j) := by
      calc
        _ = (∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * (u z i * dirDeriv ψ (spatialDir j) z))
            + ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * (ψ z * G z i j) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
        _ = (∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * (u z i * dirDeriv ψ (spatialDir j) z))
            + ψ z * (∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * G z i j) := by
          congr 1
          calc
            (∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * (ψ z * G z i j)) =
              ∑ i : Fin 3, ∑ j : Fin 3,
                ψ z * (u z i * u z j * G z i j) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = ψ z * (∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * G z i j) := by
              calc
                _ = ∑ i : Fin 3, ψ z *
                    (∑ j : Fin 3, u z i * u z j * G z i j) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [← Finset.mul_sum]
                _ = _ := by rw [← Finset.mul_sum]
    rw [hsplit, hquad]
    calc
      -(2 * (velocitySq u z * (∑ j : Fin 3,
          u z j * dirDeriv ψ (spatialDir j) z) +
          ψ z * (∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * G z i j))) =
          -2 * velocitySq u z * (∑ j : Fin 3,
            u z j * dirDeriv ψ (spatialDir j) z) -
            ψ z * (2 * ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * G z i j) := by ring
      _ = _ := by rw [hconvAlg]
  have hviscBase :
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        G z i j * (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j) =
      (∑ j : Fin 3,
        dirDeriv (velocitySq u) (spatialDir j) z * dirDeriv ψ (spatialDir j) z)
        + 2 * ψ z * (∑ i : Fin 3, ∑ j : Fin 3, G z i j * G z i j) := by
    have hsplit :
        ∑ i : Fin 3, ∑ j : Fin 3,
          G z i j * (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j) =
          (∑ i : Fin 3, ∑ j : Fin 3,
            G z i j * (u z i * dirDeriv ψ (spatialDir j) z))
            + ψ z * (∑ i : Fin 3, ∑ j : Fin 3, G z i j * G z i j) := by
      calc
        _ = (∑ i : Fin 3, ∑ j : Fin 3,
              G z i j * (u z i * dirDeriv ψ (spatialDir j) z))
            + ∑ i : Fin 3, ∑ j : Fin 3,
              G z i j * (ψ z * G z i j) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
        _ = (∑ i : Fin 3, ∑ j : Fin 3,
              G z i j * (u z i * dirDeriv ψ (spatialDir j) z))
            + ψ z * (∑ i : Fin 3, ∑ j : Fin 3,
              G z i j * G z i j) := by
          congr 1
          calc
            (∑ i : Fin 3, ∑ j : Fin 3,
                G z i j * (ψ z * G z i j)) =
              ∑ i : Fin 3, ∑ j : Fin 3,
                ψ z * (G z i j * G z i j) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = ψ z * (∑ i : Fin 3, ∑ j : Fin 3,
                G z i j * G z i j) := by
              calc
                _ = ∑ i : Fin 3, ψ z *
                    (∑ j : Fin 3, G z i j * G z i j) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [← Finset.mul_sum]
                _ = _ := by rw [← Finset.mul_sum]
    rw [hsplit]
    calc
      2 * ((∑ i : Fin 3, ∑ j : Fin 3,
          G z i j * (u z i * dirDeriv ψ (spatialDir j) z)) +
          ψ z * (∑ i : Fin 3, ∑ j : Fin 3, G z i j * G z i j)) =
          (2 * ∑ i : Fin 3, ∑ j : Fin 3,
            G z i j * (u z i * dirDeriv ψ (spatialDir j) z)) +
          2 * ψ z * (∑ i : Fin 3, ∑ j : Fin 3, G z i j * G z i j) := by ring
      _ = _ := by rw [hviscG]
  have hpressure :
      ∑ i : Fin 3, p z *
        (2 * (u z i * dirDeriv ψ (spatialDir i) z + ψ z * G z i i)) =
        2 * p z * (∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z) := by
    calc
      _ = ∑ i : Fin 3,
          (2 * p z * (u z i * dirDeriv ψ (spatialDir i) z) +
            (2 * p z * ψ z) * G z i i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 2 * p z * (∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z)
          + (2 * p z * ψ z) * (∑ i : Fin 3, G z i i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * p z * (∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z) := by
        rw [hdiv z hz]
        ring
  have hstressSplit :
      ∑ i : Fin 3, ∑ j : Fin 3,
        (u z i * u z j + R z i j) *
          (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j *
          (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        R z i j *
          (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
  have hfluxVelocity :
      ∑ j : Fin 3,
        dirDeriv ψ (spatialDir j) z * velocitySq u z * u z j =
      velocitySq u z * (∑ j : Fin 3,
        u z j * dirDeriv ψ (spatialDir j) z) := by
    calc
      _ = ∑ j : Fin 3,
          velocitySq u z * (u z j * dirDeriv ψ (spatialDir j) z) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [← Finset.mul_sum]
  have hfluxGradient :
      ∑ j : Fin 3,
        ψ z * dirDeriv (velocitySq u) (spatialDir j) z * u z j =
      ψ z * (∑ j : Fin 3,
        u z j * dirDeriv (velocitySq u) (spatialDir j) z) := by
    calc
      _ = ∑ j : Fin 3,
          ψ z * (u z j * dirDeriv (velocitySq u) (spatialDir j) z) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [← Finset.mul_sum]
  have hfluxDivergence :
      ∑ j : Fin 3, ψ z * velocitySq u z * G z j j = 0 := by
    calc
      _ = ψ z * velocitySq u z * (∑ j : Fin 3, G z j j) := by
        rw [← Finset.mul_sum]
      _ = 0 := by rw [hdiv z hz]; ring
  have hlaplacianFlux :
      velocitySq u z * (∑ j : Fin 3,
        dirDeriv (fun y => dirDeriv ψ (spatialDir j) y) (spatialDir j) z) =
      ∑ j : Fin 3, velocitySq u z *
        dirDeriv (fun y => dirDeriv ψ (spatialDir j) y) (spatialDir j) z := by
    rw [Finset.mul_sum]
  dsimp [smoothEnergyTestIntegrand, smoothEnergyBaseIntegrand,
    smoothEnergyTotalDerivative]
  rw [htimeFlux]
  simp_rw [hconvFlux, hviscFlux]
  rw [hpressure]
  simp_rw [Finset.sum_add_distrib]
  linear_combination -2 * hstressSplit + hconvU + hviscBase +
    hfluxVelocity + hfluxGradient + hfluxDivergence + hlaplacianFlux

end ESS
