/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1TransportBound
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Energy
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Comparison

/-!
# Uniform `H¹` and `H²` bounds for the regularized solutions

The squared gradient norm `y = ‖∇U_ε‖₂²` of the regularized velocity satisfies
`y' + ‖∇²U_ε‖₂² ≤ C y³` with an absolute constant, on every positive time, by the differentiated
energy identity and the transport estimate. With the `L²` energy identity, the scalar comparison of
`RegularisedH1Comparison` gives a common lifespan `≥ c (1 + ‖b‖_{H¹})⁻⁴` and bounds on
`sup_t ‖U_ε(t)‖_{H¹}` and `‖∇²U_ε‖_{L²_{t,x}}` independent of `ε`
(`prop:lps-local-strong`, `eq:lps-uniform-H1`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped Interval
open CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS.LPS

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- The squared norm of an `L²` class is the integral of squares of any representative. -/
theorem lps_norm_sq_eq_integral_of_ae {F : Lp ℝ 2 (volume : Measure Vec3)} {f : Vec3 → ℝ}
    (h : (F : Vec3 → ℝ) =ᵐ[volume] f) : ‖F‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]
  simp [sq]

/-- The squared `L²` norm of every ordered derivative of the regularized velocity is continuous in time on `[0, ∞)`. -/
theorem lps_regR12_word_sq_continuous (i : Fin 3) (α : List (Fin 3)) :
    Continuous (fun t : ℝ => ∫ x, wordDeriv α (fun y => lpsRegU ρ ε hε b hb (y, max t 0) i) x ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro s
  obtain ⟨F, hFc, hF⟩ := lps_regR12Velocity_wordDeriv_continuous_L2 ρ ε hε b hb (|s| + 1)
    (by positivity) i α
  have hcont : ContinuousAt (fun t : ℝ => ‖F (max t 0)‖ ^ 2) s :=
    ((continuous_norm.comp (hFc.comp (continuous_id.max continuous_const))).pow 2).continuousAt
  refine hcont.congr ?_
  filter_upwards [Iio_mem_nhds (show s < |s| + 1 by linarith only [le_abs_self s])] with t ht
  have hmem : max t 0 ∈ Icc 0 (|s| + 1) := ⟨le_max_right _ _, max_le (by simpa using ht.le) (by positivity)⟩
  exact lps_norm_sq_eq_integral_of_ae (hF _ hmem)

/-- The squared `L²` seminorm of the Euclidean carrier field of a vector field is the integral of the sum of squared components. -/
theorem lps_eLpNorm_field_sq {f : Vec3 → Vec3} (hf : MemLp f 2 volume) :
    eLpNorm (CKN.Leray.regUniformSpatialField f) 2 volume ^ (2 : ℕ) =
      ENNReal.ofReal (∫ x, ∑ i : Fin 3, f x i ^ 2) := by
  rw [CKN.Leray.regUniformSpatialField_eLpNorm_sq_eq_ofReal f hf]
  congr 1
  have h := CKN.Leray.inner_realVectorL2OfCoordinateFunction
    (W := CKN.Leray.realVectorL2OfCoordinateFunction f hf) (w := f)
    (CKN.Leray.realVectorL2OfCoordinateFunction_rep f hf).symm f hf
  rw [real_inner_self_eq_norm_sq] at h
  rw [h]
  congr 1; funext x
  exact Finset.sum_congr rfl fun i _ => (sq (f x i)).symm

/-- The kinetic energy of the regularized velocity does not exceed that of the datum, by the energy equality (R5) and the contraction of the mollifier. -/
theorem lps_regR12_kinetic_le {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, ∑ i : Fin 3, lpsRegU ρ ε hε b hb (x, t) i ^ 2) ≤ ∫ x, ∑ i : Fin 3, b x i ^ 2 := by
  have h := CKN.Leray.regR12_regularised_unconditional ρ b hb ε hε
  simp only [CKN.Leray.regR12Uε, CKN.Leray.regR12Pε, hε, ↓reduceDIte] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hR5⟩ := h
  have hU : MemLp (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, t)) 2 volume :=
    (lps_regR12Velocity_slice_isInJ ρ ε hε b hb t ht).1
  have h1 : eLpNorm (CKN.Leray.regUniformSpatialField (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, t)))
      2 volume ^ (2 : ℕ) ≤ eLpNorm (CKN.Leray.regUniformSpatialField b) 2 volume ^ (2 : ℕ) := by
    have h2 := hR5 t ht
    have h3 : eLpNorm (CKN.Leray.regUniformVelocitySlice (lpsRegU ρ ε hε b hb) t) 2 volume ^ (2 : ℕ) ≤
        eLpNorm (CKN.Leray.regMollifyVector ρ ε hε (CKN.Leray.regUniformSpatialField b)) 2 volume ^ (2 : ℕ) := by
      rw [← h2]; exact le_self_add
    have h4 := pow_le_pow_left₀ (by positivity)
      (lps_regularised_initial_velocity_l2_contraction ρ ε hε b hb.1) (2 : ℕ)
    exact h3.trans h4
  rw [lps_eLpNorm_field_sq hU, lps_eLpNorm_field_sq hb.1] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => sq_nonneg _)).1 h1

/-- At time zero the regularized velocity is the mollified datum. -/
theorem lps_regR12_initial_eq (i : Fin 3) (x : Vec3) :
    lpsRegU ρ ε hε b hb (x, 0) i = CKN.Leray.regUniformMollifiedInitial ρ ε hε b x i := by
  have h := CKN.Leray.regR12_regularised_unconditional ρ b hb ε hε
  simp only [CKN.Leray.regR12Uε, CKN.Leray.regR12Pε, hε, ↓reduceDIte] at h
  obtain ⟨⟨_, _, hae, _⟩, -⟩ := h
  have hc1 : Continuous (fun y : Vec3 => lpsRegU ρ ε hε b hb (y, 0)) :=
    continuous_pi fun j => (lps_regR12_slice_smooth ρ ε hε b hb 0 le_rfl j).continuous
  have hc2 : Continuous (fun y : Vec3 => CKN.Leray.regUniformMollifiedInitial ρ ε hε b y) :=
    continuous_pi fun j => (lps_regUniformMollifiedInitial_smooth ρ ε hε hb j).continuous
  have := (Continuous.ae_eq_iff_eq (μ := (volume : Measure Vec3)) hc1 hc2).1 hae
  exact congrFun (congrFun this x) i

/-- The initial gradient energy of the regularized velocity is at most the squared `L²` norm of the datum's weak gradient. -/
theorem lps_regR12_initial_gradient_le (Db : Vec3 → Fin 3 → Vec3)
    (hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x => b x i) ∧ h.grad = (fun x j => Db x i j)) :
    lpsRegGradEnergy ρ ε hε b hb 0 ≤ ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, Db x i j ^ 2 := by
  have hDb (i j : Fin 3) : MemLp (fun x : Vec3 => Db x i j) 2 volume := by
    rcases hH1 i with ⟨h, _hfun, hgrad⟩
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ,
      hgrad] using h.gradMemL2 j
  have hrow (i : Fin 3) := lps_regularised_initial_gradient_row_l2_contraction ρ ε hε b Db hb hH1 i
  have hderiv (i j : Fin 3) (x : Vec3) :
      spatialDeriv (fun y => CKN.Leray.regUniformMollifiedInitial ρ ε hε b y i) j x =
        spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, 0) i) j x := by
    have : (fun y => CKN.Leray.regUniformMollifiedInitial ρ ε hε b y i) =
        fun y => lpsRegU ρ ε hε b hb (y, 0) i := funext fun y => (lps_regR12_initial_eq ρ ε hε b hb i y).symm
    rw [this]
  have hmemU (i : Fin 3) : MemLp (fun x j => spatialDeriv
      (fun y => CKN.Leray.regUniformMollifiedInitial ρ ε hε b y i) j x) 2 volume := by
    refine (memLp_pi_iff).2 fun j => ?_
    have : MemLp (fun x => spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, 0) i) j x) 2 volume :=
      lps_regR12_slice_memLp ρ ε hε b hb 0 le_rfl i [j]
    simpa only [hderiv] using this
  have hmemDb (i : Fin 3) : MemLp (fun x => Db x i) 2 volume := (memLp_pi_iff).2 (hDb i)
  have hrowInt (i : Fin 3) : (∫ x, ∑ j : Fin 3,
      spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, 0) i) j x ^ 2) ≤
      ∫ x, ∑ j : Fin 3, Db x i j ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) (hrow i) (2 : ℕ)
    rw [lps_eLpNorm_field_sq (hmemU i), lps_eLpNorm_field_sq (hmemDb i)] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x =>
      Finset.sum_nonneg fun j _ => sq_nonneg _)).1 h1
    simpa only [hderiv] using h2
  have hint (i : Fin 3) : Integrable (fun x => ∑ j : Fin 3, Db x i j ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (hDb i j).integrable_sq
  have hlhs : lpsRegGradEnergy ρ ε hε b hb 0 = ∑ i : Fin 3, ∫ x, ∑ j : Fin 3,
      spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, 0) i) j x ^ 2 := by
    unfold lpsRegGradEnergy
    refine Finset.sum_congr rfl fun i _ => ?_
    have hj (j : Fin 3) : Integrable (fun x => spatialDeriv
        (fun y => lpsRegU ρ ε hε b hb (y, 0) i) j x ^ 2) volume :=
      (lps_regR12_slice_memLp ρ ε hε b hb 0 le_rfl i [j]).integrable_sq
    rw [integral_finsetSum _ fun j _ => hj j]
  rw [hlhs, integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_le_sum fun i _ => hrowInt i

/-- The gradient energy of the regularized velocity, extended by its time-zero value to negative times, is continuous. -/
theorem lps_regR12_gradEnergy_continuous :
    Continuous (fun t : ℝ => lpsRegGradEnergy ρ ε hε b hb (max t 0)) := by
  unfold lpsRegGradEnergy
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    lps_regR12_word_sq_continuous ρ ε hε b hb i [j]

/-- The second-derivative energy of the regularized velocity, extended by its time-zero value to negative times, is continuous. -/
theorem lps_regR12_hessEnergy_continuous :
    Continuous (fun t : ℝ => lpsRegHessEnergy ρ ε hε b hb (max t 0)) := by
  unfold lpsRegHessEnergy
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => lps_regR12_word_sq_continuous ρ ε hε b hb i [j, k]

/-- The gradient energy is nonnegative. -/
theorem lps_regR12_gradEnergy_nonneg (t : ℝ) : 0 ≤ lpsRegGradEnergy ρ ε hε b hb t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

/-- The second-derivative energy is nonnegative. -/
theorem lps_regR12_hessEnergy_nonneg (t : ℝ) : 0 ≤ lpsRegHessEnergy ρ ε hε b hb t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => sq_nonneg _

/-- The gradient energy of the regularized velocity has the stated derivative at every positive time (`eq:lps-uniform-H1`). -/
theorem lps_regR12_gradEnergy_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => lpsRegGradEnergy ρ ε hε b hb (max s 0))
      (-2 * lpsRegHessEnergy ρ ε hε b hb t + 2 * lpsRegTransportPairing ρ ε hε b hb t) t := by
  have h := lps_regR12_gradient_energy_hasDerivAt ρ ε hε b hb ht
  rw [lps_regR12_gradient_energy_deriv_eq ρ ε hε b hb ht.le] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  simp only [max_eq_left hs.le]

/-- The cubic differential inequality `y' + ‖∇²U_ε‖₂² ≤ C y³` for the gradient energy of the regularized velocity, with an absolute constant (`eq:lps-uniform-H1`). -/
theorem lps_regR12_cubic_inequality {t : ℝ} (ht : 0 < t) :
    (-2 * lpsRegHessEnergy ρ ε hε b hb t + 2 * lpsRegTransportPairing ρ ε hε b hb t) +
      lpsRegHessEnergy ρ ε hε b hb t ≤
    4 * (9 * gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ)) ^ 4 *
      lpsRegGradEnergy ρ ε hε b hb t ^ 3 := by
  have hK := lps_regR12_transportPairing_le ρ ε hε b hb ht.le
  have hS0 : 0 ≤ gagliardoNirenbergSobolevConstant.toReal := ENNReal.toReal_nonneg
  refine lps_h1_cubic_differential_inequality (K := lpsRegTransportPairing ρ ε hε b hb t)
    (by positivity) (lps_regR12_gradEnergy_nonneg ρ ε hε b hb t)
    (lps_regR12_hessEnergy_nonneg ρ ε hε b hb t) (by ring) ?_
  have := (le_abs_self _).trans hK
  calc lpsRegTransportPairing ρ ε hε b hb t ≤ _ := this
    _ = _ := by simp only [Real.rpow_eq_pow]; ring

/-- Tonelli identity for a square-integrable function on a slab, in terms of the slice integrals. -/
theorem lps_slab_integral_eq_time_integral {f : Vec3 → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : MemLp (fun z : Vec3 × ℝ => f z.1 z.2) 2
      (volume.restrict (Set.univ ×ˢ Ioo 0 T))) :
    (∫ z in Set.univ ×ˢ Ioo 0 T, f z.1 z.2 ^ 2) = ∫ t in (0 : ℝ)..T, ∫ x : Vec3, f x t ^ 2 := by
  have hμ : (volume : Measure (Vec3 × ℝ)).restrict (Set.univ ×ˢ Ioo 0 T) =
      (volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hint : Integrable (fun z : Vec3 × ℝ => f z.1 z.2 ^ 2)
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [← hμ]; exact hf.integrable_sq
  rw [hμ, integral_prod_symm _ hint, intervalIntegral.integral_of_le hT,
    ← integral_Ioc_eq_integral_Ioo]
  simp [Measure.restrict_univ]

/-- The slab integral of the second derivatives of the regularized velocity is the time integral of their slice energies. -/
theorem lps_regR12_hess_slab {T : ℝ} (hT : 0 < T) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), ∑ i : Fin 3, ∑ j : Fin 3,
      vec3EuclideanNorm (fun k => spatialPartial (fun w => spatialPartial
        (fun v => lpsRegU ρ ε hε b hb v i) j w) k z) ^ (2 : ℕ)) =
      ∫ t in (0 : ℝ)..T, lpsRegHessEnergy ρ ε hε b hb (max t 0) := by
  have hmem (i j k : Fin 3) : MemLp (fun z : Vec3 × ℝ =>
      wordDeriv [j, k] (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, z.2) i) z.1) 2
      (volume.restrict (Set.univ ×ˢ Ioo 0 T)) :=
    lps_regR12Velocity_all_word_memLp_slab ρ ε hε b hb 0 T le_rfl hT i [j, k]
  have hpt (z : ParabolicPoint) (i j : Fin 3) :
      vec3EuclideanNorm (fun k => spatialPartial (fun w => spatialPartial
        (fun v => lpsRegU ρ ε hε b hb v i) j w) k z) ^ (2 : ℕ) =
      ∑ k : Fin 3, (wordDeriv [j, k] (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, z.2) i) z.1) ^ 2 :=
    CKN.Foundation.Heat.vec3EuclideanNorm_sq _
  simp only [hpt]
  have hint (i j k : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      (wordDeriv [j, k] (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, z.2) i) z.1) ^ 2)
      (volume.restrict (Set.univ ×ˢ Ioo 0 T)) := (hmem i j k).integrable_sq
  have hsl (i j k : Fin 3) := lps_slab_integral_eq_time_integral (T := T) hT.le
    (f := fun x t => wordDeriv [j, k] (fun y : Vec3 => lpsRegU ρ ε hε b hb (y, t) i) x) (hmem i j k)
  change (∫ z in Set.univ ×ˢ Ioo 0 T, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    (wordDeriv [j, k] (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, z.2) i) z.1) ^ 2) = _
  set Hf : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j k z =>
    (wordDeriv [j, k] (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, z.2) i) z.1) ^ 2 with hHf
  have e1 : (∫ z in Set.univ ×ˢ Ioo 0 T, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Hf i j k z) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in Set.univ ×ˢ Ioo 0 T, Hf i j k z := by
    rw [integral_finsetSum (f := fun i z => ∑ j : Fin 3, ∑ k : Fin 3, Hf i j k z) _
      (fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint i j k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum (f := fun j z => ∑ k : Fin 3, Hf i j k z) _
      (fun j _ => integrable_finsetSum _ fun k _ => hint i j k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_finsetSum (f := fun k z => Hf i j k z) _ (fun k _ => hint i j k)
  rw [e1]
  have hcont (i j k : Fin 3) : Continuous (fun t : ℝ => ∫ x : Vec3, spatialDeriv (spatialDeriv
      (fun y => lpsRegU ρ ε hε b hb (y, max t 0) i) j) k x ^ 2) :=
    lps_regR12_word_sq_continuous ρ ε hε b hb i [j, k]
  have e2 : (∫ t in (0 : ℝ)..T, lpsRegHessEnergy ρ ε hε b hb (max t 0)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ t in (0 : ℝ)..T, ∫ x : Vec3,
        spatialDeriv (spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, max t 0) i) j) k x ^ 2 := by
    unfold lpsRegHessEnergy
    rw [intervalIntegral.integral_finsetSum (fun i _ => (continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => hcont i j k).intervalIntegrable 0 T)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun j _ => (continuous_finsetSum _ fun k _ =>
      hcont i j k).intervalIntegrable 0 T)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact intervalIntegral.integral_finsetSum (fun k _ => (hcont i j k).intervalIntegrable 0 T)
  rw [e2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  refine (hsl i j k).trans ?_
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht0 : 0 ≤ t := by
    rcases Set.mem_uIcc.mp ht with h | h <;> linarith only [h.1, h.2, hT]
  simp only [max_eq_left ht0]
  rfl

/-- The gradient integrand of the regularized velocity is integrable on every nonnegative-time slice, with integral the gradient energy. -/
theorem lps_regR12_gradSq {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Vec3 => spatialGradientSq (lpsRegU ρ ε hε b hb)
      (fun z i j => spatialPartial (fun w => lpsRegU ρ ε hε b hb w i) j z) (x, t)) volume ∧
    (∫ x : Vec3, spatialGradientSq (lpsRegU ρ ε hε b hb)
      (fun z i j => spatialPartial (fun w => lpsRegU ρ ε hε b hb w i) j z) (x, t)) =
        lpsRegGradEnergy ρ ε hε b hb t := by
  have hj (i j : Fin 3) : Integrable (fun x : Vec3 => spatialDeriv
      (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2) volume :=
    (lps_regR12_slice_memLp ρ ε hε b hb t ht i [j]).integrable_sq
  have hfun : (fun x : Vec3 => spatialGradientSq (lpsRegU ρ ε hε b hb)
      (fun z i j => spatialPartial (fun w => lpsRegU ρ ε hε b hb w i) j z) (x, t)) =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3, spatialDeriv
        (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2 := rfl
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hj i j, ?_⟩
  rw [integral_finsetSum (f := fun i x => ∑ j : Fin 3, spatialDeriv
    (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2) _
    (fun i _ => integrable_finsetSum _ fun j _ => hj i j)]
  unfold lpsRegGradEnergy
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_finsetSum (f := fun j x => spatialDeriv
    (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2) _ (fun j _ => hj i j)

/-- The squared velocity of the regularized solution is integrable on every nonnegative-time slice. -/
theorem lps_regR12_kineticSq {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Vec3 => vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ)) volume ∧
    (∫ x : Vec3, vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ)) =
      ∫ x, ∑ i : Fin 3, lpsRegU ρ ε hε b hb (x, t) i ^ 2 := by
  have hfun : (fun x : Vec3 => vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ)) =
      fun x => ∑ i : Fin 3, lpsRegU ρ ε hε b hb (x, t) i ^ 2 :=
    funext fun x => CKN.Foundation.Heat.vec3EuclideanNorm_sq _
  rw [hfun]
  exact ⟨integrable_finsetSum _ fun i _ =>
    (lps_regR12_slice_memLp ρ ε hε b hb t ht i []).integrable_sq, rfl⟩

end



/-- Uniform `H¹`/`H²` bounds for the regularized solutions (`prop:lps-local-strong`). -/
theorem lps_regularised_uniform_h1_bounds :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ρ : CKN.Leray.RegMollifierProfile)
        (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3),
        (hb : ESS.IsLpsGoodTime
          (fun z : ParabolicPoint => b z.1)
          (fun z i => Db z.1 i) 0) →
        ∃ T M : ℝ, 0 < T ∧
          c * Real.rpow
            (1 + Real.sqrt (∫ x : Vec3,
              (∑ i : Fin 3, (b x i) ^ 2) +
                ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
            (-4 : ℝ) ≤ T ∧
          0 ≤ M ∧
          ∀ (ε : ℝ) (hε : 0 < ε),
            let Uε : ParabolicPoint → Vec3 :=
              CKN.Leray.regR12Velocity ρ ε hε b
                (by simpa using hb.2)
            let Dε : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
              spatialPartial (fun y => Uε y i) j z
            let D2ε : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
              fun z i j k =>
                spatialPartial
                  (fun y => spatialPartial (fun x => Uε x i) j y) k z
            (∀ t : ℝ, t ∈ Icc 0 T →
              ∫ x : Vec3,
                vec3EuclideanNorm (Uε (x, t)) ^ (2 : ℕ) +
                  spatialGradientSq Uε Dε (x, t) ≤ M) ∧
            ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              ∑ i : Fin 3, ∑ j : Fin 3,
                vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M := by
  set S : ℝ := gagliardoNirenbergSobolevConstant.toReal with hS
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  set C0 : ℝ := 9 * S ^ (3 / 2 : ℝ) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  set C : ℝ := 4 * C0 ^ 4 with hC
  have hC0' : 0 ≤ C := by positivity
  refine ⟨1 / (8 * (1 + C)), by positivity, ?_⟩
  intro ρ b Db hGood
  have hbJ : CKN.IsInJ b := by simpa using hGood.2
  let y : ℝ → ℝ → ℝ := fun e t =>
    if h : 0 < e then lpsRegGradEnergy ρ e h b hbJ (max t 0) else 0
  let d : ℝ → ℝ → ℝ := fun e t =>
    if h : 0 < e then lpsRegHessEnergy ρ e h b hbJ (max t 0) else 0
  let dy : ℝ → ℝ → ℝ := fun e t =>
    if h : 0 < e then -2 * lpsRegHessEnergy ρ e h b hbJ (max t 0) +
      2 * lpsRegTransportPairing ρ e h b hbJ (max t 0) else 0
  have hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x => b x i) ∧ h.grad = (fun x j => Db x i j) := hGood.1
  have hDb (i j : Fin 3) : MemLp (fun x : Vec3 => Db x i j) 2 volume := by
    rcases hH1 i with ⟨h, _hfun, hgrad⟩
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ,
      hgrad] using h.gradMemL2 j
  have hbi (i : Fin 3) : MemLp (fun x : Vec3 => b x i) 2 volume := (memLp_pi_iff.mp hbJ.1) i
  have hIb : Integrable (fun x : Vec3 => ∑ i : Fin 3, b x i ^ 2) volume :=
    integrable_finsetSum _ fun i _ => (hbi i).integrable_sq
  have hIDb : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, Db x i j ^ 2) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hDb i j).integrable_sq
  have hb0 : (∫ x : Vec3, ∑ i : Fin 3, b x i ^ 2) ≤
      ∫ x : Vec3, (∑ i : Fin 3, b x i ^ 2) + ∑ i : Fin 3, ∑ j : Fin 3, Db x i j ^ 2 :=
    integral_mono hIb (hIb.add hIDb) fun x => le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hDb0 : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, Db x i j ^ 2) ≤
      ∫ x : Vec3, (∑ i : Fin 3, b x i ^ 2) + ∑ i : Fin 3, ∑ j : Fin 3, Db x i j ^ 2 :=
    integral_mono hIDb (hIb.add hIDb) fun x => le_add_of_nonneg_left
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hE0 : 0 ≤ ∫ x : Vec3, (∑ i : Fin 3, b x i ^ 2) + ∑ i : Fin 3, ∑ j : Fin 3, Db x i j ^ 2 :=
    (lps_good_datum_h1_energy_integrable b Db hGood).2
  have hT0 : 0 < lpsH1ComparisonTime (∫ x : Vec3, (∑ i : Fin 3, b x i ^ 2) +
      ∑ i : Fin 3, ∑ j : Fin 3, Db x i j ^ 2) C := by
    unfold lpsH1ComparisonTime
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (by positivity)
  refine lps_regularised_uniform_h1_bounds_of_energy_estimates ρ b Db hGood C hC0' y dy d
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro e
    by_cases he : 0 < e
    · simp only [y, he, ↓reduceDIte]
      exact lps_regR12_gradEnergy_continuous ρ e he b hbJ
    · simp only [y, he, ↓reduceDIte]
      exact continuous_const
  · intro e
    by_cases he : 0 < e
    · simp only [d, he, ↓reduceDIte]
      exact lps_regR12_hessEnergy_continuous ρ e he b hbJ
    · simp only [d, he, ↓reduceDIte]
      exact continuous_const
  · intro e he t ht
    simp only [y, dy, he, ↓reduceDIte, max_eq_left ht.1.le]
    have := lps_regR12_gradEnergy_hasDerivAt ρ e he b hbJ ht.1
    exact this
  · intro e he t ht
    simp only [y, d, he, ↓reduceDIte]
    exact ⟨lps_regR12_gradEnergy_nonneg ρ e he b hbJ _, lps_regR12_hessEnergy_nonneg ρ e he b hbJ _⟩
  · intro e he t ht
    simp only [y, d, dy, he, ↓reduceDIte, max_eq_left ht.1.le]
    exact lps_regR12_cubic_inequality ρ e he b hbJ ht.1
  · intro e he
    simp only [y, he, ↓reduceDIte, max_self]
    exact (lps_regR12_initial_gradient_le ρ e he b hbJ Db hH1).trans hDb0
  · intro e he t ht
    rw [(lps_regR12_kineticSq ρ e he b hbJ ht.1).2]
    exact (lps_regR12_kinetic_le ρ e he b hbJ ht.1).trans hb0
  · intro e he t ht
    rw [(lps_regR12_gradSq ρ e he b hbJ ht.1).2]
    simp only [y, he, ↓reduceDIte, max_eq_left ht.1]
    exact le_rfl
  · intro e he t ht
    exact (lps_regR12_kineticSq ρ e he b hbJ ht.1).1
  · intro e he t ht
    exact (lps_regR12_gradSq ρ e he b hbJ ht.1).1
  · intro e he
    have h := (lps_regR12_hess_slab ρ e he b hbJ hT0).le
    simpa only [d, he, ↓reduceDIte] using h

end ESS.LPS
