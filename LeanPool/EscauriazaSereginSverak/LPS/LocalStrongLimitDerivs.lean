/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitIBP
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitTimeDeriv
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegVelocity

/-!
# Space-time weak derivatives of the compactness limit

The compactness limit of the regularized velocities, its gradient, its Hessian, and the weak limit of
the time derivatives satisfy the space-time weak derivative relations against smooth compactly
supported tests (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- The first and second spatial derivatives of the regularized velocity are square integrable on
every positive-time slab (`thm:regularised` of the CKN manuscript, (R3)). -/
theorem lps_regR12_derivs_memLp_slab {δ T : ℝ} (hδ : 0 < δ) (hδT : δ < T) (i j k : Fin 3) :
    MemLp (fun z : ParabolicPoint =>
      spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j z) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) ∧
    MemLp (fun z : ParabolicPoint => spatialPartial
      (fun y => spatialPartial (fun x => lpsRegU ρ ε hε b hb x i) j y) k z) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
  have h := CKN.Leray.regR12_regularised_unconditional ρ b hb ε hε
  simp only [CKN.Leray.regR12Uε, CKN.Leray.regR12Pε, hε, ↓reduceDIte] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hL2, -, -, -⟩ := h
  exact ⟨(hL2 δ T hδ hδT).2.1 i j, (hL2 δ T hδ hδT).2.2.1 i j k⟩

/-- Integration by parts for the gradient of the regularized velocity on a slab:
`∫ ∂ⱼUᵢ ∂ₖφ = -∫ ∂ₖ∂ⱼUᵢ φ`. -/
theorem lps_regR12_hessian_ibp {T : ℝ} (hT : 0 < T) (i j k : Fin 3) {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 T)) :
    ∫ z in vlSlab 0 T, spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j z *
        spatialPartial φ k z =
      -∫ z in vlSlab 0 T, spatialPartial
        (fun y => spatialPartial (fun x => lpsRegU ρ ε hε b hb x i) j y) k z * φ z := by
  refine lps_slab_spatial_weak_of_slices hT k
    (F := fun z : Vec3 × ℝ => spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j
      ((z.1, z.2) : ParabolicPoint))
    (G := fun z : Vec3 × ℝ => spatialPartial
      (fun y => spatialPartial (fun x => lpsRegU ρ ε hε b hb x i) j y) k
      ((z.1, z.2) : ParabolicPoint)) ?_ ?_ ?_ hφ
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact lps_smooth_hasWeakPartialDerivOn
      (contDiff_spatialDeriv_smooth (lps_regR12_slice_smooth ρ ε hε b hb t ht.1.le i) j) k
  · intro a' b' ha' hab' hb'
    exact (lps_regR12_derivs_memLp_slab ρ ε hε b hb ha' hab' i j k).1
  · intro a' b' ha' hab' hb'
    exact (lps_regR12_derivs_memLp_slab ρ ε hε b hb ha' hab' i j k).2

end

/-- The weak limit of the time derivatives of the regularized velocities along the compactness
subsequence is the weak time derivative of the limit (`prop:lps-local-strong`). -/
theorem lps_strong_limit_time_derivative
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hb : (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => b x i) ∧
        h.grad = (fun x : Vec3 => Db x i)) ∧ CKN.IsInJ b)
    (T M : ℝ) (hT : 0 < T)
    (hUniformBounds :
      ∀ (ε : ℝ) (hε : 0 < ε),
        let Uε : ParabolicPoint → Vec3 :=
          CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hb.2)
        let Dε : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
          spatialPartial (fun y => Uε y i) j z
        let D2ε : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j =>
          fun k => spatialPartial
            (fun y => spatialPartial (fun x => Uε x i) j y) k z
        (∀ t : ℝ, t ∈ Icc 0 T →
          ∫ x : Vec3,
            vec3EuclideanNorm (Uε (x, t)) ^ (2 : ℕ) +
              spatialGradientSq Uε Dε (x, t) ≤ M) ∧
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ∑ i : Fin 3, ∑ j : Fin 3,
            vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M)
    {σ : ℕ → ℕ} {u : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hUconv : Tendsto
      (fun n => eLpNorm
        (CKN.Leray.regR12Uε ρ b hb.2 ((fun m : ℕ => 1 / ((m : ℝ) + 1)) (σ n)) - u)
        2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
      atTop (nhds 0)) :
    ∃ Dtu : ParabolicPoint → Vec3,
      MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      ∀ φ : ParabolicPoint → ℝ,
        φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 T) →
        ∀ i : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), u z i * timePartial φ z =
            -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), Dtu z i * φ z := by
  classical
  set μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) with hμ
  set εs : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hεs
  have hεpos : ∀ m, 0 < εs m := fun m => by positivity
  have hUB := fun n => hUniformBounds (εs (σ n)) (hεpos (σ n))
  have hy : ∀ n, ∀ t ∈ Ioc 0 T,
      lpsRegGradEnergy ρ (εs (σ n)) (hεpos (σ n)) b hb.2 t ≤ M := fun n t ht =>
    lps_regR12_gradEnergy_le ρ _ (hεpos _) b hb.2 ht.1.le ((hUB n).1 t ⟨ht.1.le, ht.2⟩)
  have hl2 : ∀ n, ∀ t ∈ Ioc 0 T, (∫ x : Vec3, ∑ i : Fin 3,
      lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 (x, t) i ^ 2) ≤ M := fun n t ht =>
    lps_regR12_l2Energy_le ρ _ (hεpos _) b hb.2 ht.1.le ((hUB n).1 t ⟨ht.1.le, ht.2⟩)
  have hHb : ∀ n, (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (spatialPartial
        (fun y => spatialPartial (fun x => lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 x i) j y)
          k z) ^ 2) ≤ M := by
    intro n
    refine le_trans (le_of_eq ?_) (hUB n).2
    congr 1; funext z
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact (lps_vec3EuclideanNorm_sq_eq_sum_sq _).symm
  have hM0 : 0 ≤ M := by
    have := hy 0 (T / 2) ⟨by linarith only [hT], by linarith only [hT]⟩
    exact le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      integral_nonneg fun x => sq_nonneg _) this
  set K : ℝ := (3 + 81 * (gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) *
      M ^ (3 / 2 : ℝ))) * M + 81 * (gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) *
      M ^ (3 / 2 : ℝ)) * T with hK
  have hQ := fun n => lps_regR12_Q_slab ρ (εs (σ n)) (hεpos (σ n)) b hb.2 hT (hy n) (hHb n)
  have hUn : ∀ n i, MemLp (fun z : ParabolicPoint =>
      lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i) 2 μ := fun n i =>
    lps_regR12_velocity_memLp_open_slab ρ _ (hεpos _) b hb.2 (hl2 n) i
  have hQn : ∀ n i, MemLp (fun z : ParabolicPoint =>
      lpsRegQ ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i) 2 μ := fun n i => (hQ n).1 i
  have hui : ∀ i, MemLp (fun z : ParabolicPoint => u z i) 2 μ := fun i => memLp_pi_iff.1 hu i
  have hbound : ∀ n i, ‖(hQn n i).toLp (fun z : ParabolicPoint =>
      lpsRegQ ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i)‖ ≤ Real.sqrt K := by
    intro n i
    have h1 := vl_norm_toLp_sq (hQn n i)
    have h2 : (∫ z, lpsRegQ ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i ^ 2 ∂μ) ≤ K := by
      refine le_trans ?_ (hQ n).2
      refine integral_mono (hQn n i).integrable_sq
        (integrable_finsetSum _ fun j _ => (hQn n j).integrable_sq) fun z => ?_
      exact Finset.single_le_sum (f := fun j : Fin 3 =>
        (lpsRegQ ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by rw [h1]; exact h2))
  -- strong convergence of the components
  have hUeq : ∀ n, CKN.Leray.regR12Uε ρ b hb.2 (εs (σ n)) =
      fun z => lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z := fun n => by
    unfold CKN.Leray.regR12Uε
    exact dite_eq_left_of_eq_true (eq_true (hεpos _))
  have hΔ : Tendsto (fun n => (eLpNorm
      (CKN.Leray.regR12Uε ρ b hb.2 (εs (σ n)) - u) 2 μ).toReal) atTop (nhds 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hUconv
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  have hconv : ∀ i, Tendsto (fun n => ∫ z, (lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i -
      u z i) ^ 2 ∂μ) atTop (nhds 0) := by
    intro i
    refine squeeze_zero (fun n => integral_nonneg fun z => sq_nonneg _) (fun n => ?_)
      (by simpa using hΔ.pow 2)
    have hd : MemLp (fun z : ParabolicPoint => lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i -
        u z i) 2 μ := (hUn n i).sub (hui i)
    have hdv : MemLp (CKN.Leray.regR12Uε ρ b hb.2 (εs (σ n)) - u) 2 μ := by
      rw [hUeq n]
      exact memLp_pi_iff.2 fun j => (hUn n j).sub (hui j)
    have h1 := vl_norm_toLp_sq hd
    rw [← h1, Lp.norm_toLp]
    have hle : eLpNorm (fun z : ParabolicPoint =>
        lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i - u z i) 2 μ ≤
        eLpNorm (CKN.Leray.regR12Uε ρ b hb.2 (εs (σ n)) - u) 2 μ := by
      refine eLpNorm_mono hd.aestronglyMeasurable fun z => ?_
      rw [hUeq n]
      exact norm_le_pi_norm (fun j => lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z j - u z j) i
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hdv.eLpNorm_ne_top hle) 2
  -- the weak limit
  obtain ⟨Dt, hDtmem, hDtid⟩ := lps_weak_limit_time_derivative (μ := μ)
    (Un := fun n i z => lpsRegU ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i)
    (Qn := fun n i z => lpsRegQ ρ (εs (σ n)) (hεpos (σ n)) b hb.2 z i)
    (u := fun i z => u z i) hUn hQn hui hconv (Real.sqrt_nonneg K) hbound
    (fun θ Dθ => ∃ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 T) ∧
        θ = φ ∧ Dθ = fun z => timePartial φ z) (by
      rintro θ Dθ ⟨φ, hφ, rfl, rfl⟩
      obtain ⟨hT0, -, hT2⟩ := lps_test_memLp_slab hφ 0
      exact ⟨hT0, hT2, fun n i => lps_regR12_weak_time ρ _ (hεpos _) b hb.2 hT i hφ⟩)
  refine ⟨fun z i => Dt i z, memLp_pi_iff.2 hDtmem, fun φ hφ i => ?_⟩
  exact hDtid i φ (fun z => timePartial φ z) ⟨φ, hφ, rfl, rfl⟩

end ESS.LPS

end
