/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegSlice
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongCompactness
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergySlab

/-!
# The uniform slab bound for the time derivative of the regularized velocity

The slice bound of the time derivative and the uniform `H¹`, `L²_tH²` bounds give a bound on the
slab `L²` norm of the time derivative of every regularized velocity that does not depend on the
regularization parameter (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A nonnegative slab function whose slice integrals are dominated by an integrable function of
time is integrable on the slab, with integral at most the time integral of the bound. -/
theorem lps_slab_integrable_of_slice_bound {a τ : ℝ} {F : Vec3 × ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (vlSlab a τ)))
    (hnn : ∀ z, 0 ≤ F z) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a τ) volume)
    (hslice : ∀ t ∈ Ioo a τ, Integrable (fun x => F (x, t)) volume ∧
      (∫ x, F (x, t)) ≤ g t) :
    Integrable F (volume.restrict (vlSlab a τ)) ∧
      (∫ z in vlSlab a τ, F z) ≤ ∫ t in Ioo a τ, g t := by
  have hmeas : AEStronglyMeasurable F ((volume : Measure Vec3).prod (volume.restrict (Ioo a τ)))
    := by
    rw [← vlSlab_measure]; exact hF
  have hint : Integrable F (volume.restrict (vlSlab a τ)) := by
    rw [vlSlab_measure]
    refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using (hslice t ht).1
    · have hm : AEStronglyMeasurable (fun t => ∫ x, ‖F (x, t)‖)
          (volume.restrict (Ioo a τ)) := hmeas.norm.prod_swap.integral_prod_right'
      refine Integrable.mono' hg hm ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have h0 : 0 ≤ ∫ x, ‖F (x, t)‖ := integral_nonneg fun x => norm_nonneg _
      rw [Real.norm_of_nonneg h0]
      have : (∫ x, ‖F (x, t)‖) = ∫ x, F (x, t) := by
        congr 1; funext x; exact Real.norm_of_nonneg (hnn _)
      rw [this]
      exact (hslice t ht).2
  refine ⟨hint, ?_⟩
  rw [vlSlab_integral_eq hint]
  have hi2 : Integrable (fun t => ∫ x, F (x, t)) (volume.restrict (Ioo a τ)) := by
    have := hint
    rw [vlSlab_measure] at this
    exact this.integral_prod_right
  exact integral_mono_ae hi2 hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using (hslice t ht).2)

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- The uniform bound of the regularized family controls the gradient energy of every slice
(`lem:lps-regularized-Hk-start`). -/
theorem lps_regR12_gradEnergy_le {t : ℝ} (ht : 0 ≤ t) {M : ℝ}
    (h : (∫ x : Vec3, vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ) +
      spatialGradientSq (lpsRegU ρ ε hε b hb)
        (fun z i j => spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j z) (x, t)) ≤ M) :
    lpsRegGradEnergy ρ ε hε b hb t ≤ M := by
  have hUw := lps_regR12_slice_memLp ρ ε hε b hb t ht
  have ha : ∀ x : Vec3, vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ) =
      ∑ i : Fin 3, lpsRegU ρ ε hε b hb (x, t) i ^ 2 := fun x =>
    lps_vec3EuclideanNorm_sq_eq_sum_sq _
  have hai : Integrable (fun x : Vec3 => vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ))
      volume := by
    simp only [ha]
    exact integrable_finsetSum _ fun i _ => (hUw i []).integrable_sq
  have hbi : Integrable (fun x : Vec3 => spatialGradientSq (lpsRegU ρ ε hε b hb)
      (fun z i j => spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j z) (x, t)) volume := by
    unfold spatialGradientSq
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact (hUw i [j]).integrable_sq
  rw [integral_add hai hbi] at h
  have h0 : 0 ≤ ∫ x : Vec3, vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ) :=
    integral_nonneg fun x => sq_nonneg _
  have hb2 : (∫ x : Vec3, spatialGradientSq (lpsRegU ρ ε hε b hb)
      (fun z i j => spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j z) (x, t)) =
      lpsRegGradEnergy ρ ε hε b hb t := by
    show (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
      spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2) = _
    unfold lpsRegGradEnergy
    have hsq : ∀ i j : Fin 3, Integrable (fun x : Vec3 =>
        spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2) volume :=
      fun i j => (hUw i [j]).integrable_sq
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hsq i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hsq i j)]
  linarith only [h, h0, hb2]

/-- The slab `L²` norm of the time derivative of the regularized velocity is bounded uniformly in
the regularization parameter by the uniform `H¹` and `L²_tH²` bounds (`prop:lps-local-strong`). -/
theorem lps_regR12_Q_slab {T M : ℝ} (hT : 0 < T)
    (hy : ∀ t ∈ Ioc 0 T, lpsRegGradEnergy ρ ε hε b hb t ≤ M)
    (hH : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (spatialPartial
        (fun y => spatialPartial (fun x => lpsRegU ρ ε hε b hb x i) j y) k z) ^ 2) ≤ M) :
    (∀ i : Fin 3, MemLp (fun z : ParabolicPoint => lpsRegQ ρ ε hε b hb z i) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) ∧
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ∑ i : Fin 3, (lpsRegQ ρ ε hε b hb z i) ^ 2) ≤
      (3 + 81 * (gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) * M ^ (3 / 2 : ℝ))) * M +
        81 * (gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) * M ^ (3 / 2 : ℝ)) * T := by
  set S := gagliardoNirenbergSobolevConstant.toReal with hS
  set κ : ℝ := 81 * (S ^ (3 : ℕ) * M ^ (3 / 2 : ℝ)) with hκ
  have hM0 : 0 ≤ M := by
    have := hy (T / 2) ⟨by linarith only [hT], by linarith only [hT]⟩
    refine le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      integral_nonneg fun x => sq_nonneg _) this
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hκ0 : 0 ≤ κ := by positivity
  -- the Hessian density
  let HD : Vec3 × ℝ → ℝ := fun z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (spatialPartial
    (fun y => spatialPartial (fun x => lpsRegU ρ ε hε b hb x i) j y) k
      ((z.1, z.2) : ParabolicPoint)) ^ 2
  have hHDint : Integrable HD (volume.restrict (vlSlab 0 T)) := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => ?_
    exact (lps_regR12_second_memLp_open_slab ρ ε hε b hb T hT i j k).integrable_sq
  have hHt : ∀ t : ℝ, 0 ≤ t → (∫ x : Vec3, HD (x, t)) = lpsRegHessEnergy ρ ε hε b hb t := by
    intro t ht
    have hsq : ∀ i j k : Fin 3, Integrable (fun x : Vec3 => spatialDeriv (spatialDeriv
        (fun y => lpsRegU ρ ε hε b hb (y, t) i) j) k x ^ 2) volume :=
      fun i j k => (lps_regR12_slice_memLp ρ ε hε b hb t ht i [j, k]).integrable_sq
    show (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, spatialDeriv (spatialDeriv
        (fun y => lpsRegU ρ ε hε b hb (y, t) i) j) k x ^ 2) = _
    unfold lpsRegHessEnergy
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => hsq i j k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hsq i j k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ (fun k _ => hsq i j k)]
  have hHtInt : Integrable (fun t : ℝ => ∫ x : Vec3, HD (x, t)) (volume.restrict (Ioo 0 T)) := by
    have := hHDint
    rw [vlSlab_measure] at this
    exact this.integral_prod_right
  have hHsum : (∫ t in Ioo 0 T, ∫ x : Vec3, HD (x, t)) ≤ M := by
    rw [← vlSlab_integral_eq hHDint]
    exact hH
  -- measurability of the time derivative
  obtain ⟨hQcont, -⟩ := lps_regR12_Q_facts ρ ε hε b hb
  have hslabSub : vlSlab 0 T ⊆ Set.univ ×ˢ Ioi 0 := fun z hz => ⟨hz.1, hz.2.1⟩
  have hQc : ∀ i : Fin 3, ContinuousOn (fun z : Vec3 × ℝ =>
      lpsRegQ ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) i) (vlSlab 0 T) := fun i =>
    (((hQcont i).comp parabolicHomeomorph.symm.continuous.continuousOn
      (fun _ hz => hz)).mono hslabSub)
  have hslabMeas : MeasurableSet (vlSlab 0 T) := MeasurableSet.univ.prod measurableSet_Ioo
  have hQm : ∀ i : Fin 3, AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      lpsRegQ ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) i) (volume.restrict (vlSlab 0 T)) :=
    fun i => (hQc i).aestronglyMeasurable hslabMeas
  let F : Vec3 × ℝ → ℝ := fun z => ∑ i : Fin 3,
    (lpsRegQ ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) i) ^ 2
  have hFm : AEStronglyMeasurable F (volume.restrict (vlSlab 0 T)) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hQm i).pow 2
  have hFnn : ∀ z, 0 ≤ F z := fun z => Finset.sum_nonneg fun i _ => sq_nonneg _
  -- slice bound
  have hsl : ∀ t ∈ Ioo 0 T, Integrable (fun x : Vec3 => F (x, t)) volume ∧
      (∫ x : Vec3, F (x, t)) ≤ (3 + κ) * (∫ x : Vec3, HD (x, t)) + κ := by
    intro t ht
    obtain ⟨hmem, hbound⟩ := lps_regR12_Q_slice ρ ε hε b hb ht.1
    have hi : ∀ i : Fin 3, Integrable (fun x : Vec3 =>
        lpsRegQ ρ ε hε b hb (x, t) i ^ 2) volume := fun i => (hmem i).integrable_sq
    refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
    show (∫ x : Vec3, ∑ i : Fin 3, lpsRegQ ρ ε hε b hb (x, t) i ^ 2) ≤ _
    rw [integral_finsetSum _ (fun i _ => hi i), hHt t ht.1.le]
    refine hbound.trans ?_
    set y := lpsRegGradEnergy ρ ε hε b hb t with hyt
    set H := lpsRegHessEnergy ρ ε hε b hb t with hHdef
    have hy0 : 0 ≤ y := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      integral_nonneg fun x => sq_nonneg _
    have hH0 : 0 ≤ H := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
    have h1 : y ^ (3 / 2 : ℝ) ≤ M ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hy0 (hy t ⟨ht.1, ht.2.le⟩) (by norm_num)
    have h2 : H ^ (1 / 2 : ℝ) ≤ (1 + H) / 2 := by
      rw [← Real.sqrt_eq_rpow]
      nlinarith only [Real.sq_sqrt hH0, sq_nonneg (Real.sqrt H - 1)]
    have h3 : S ^ (3 : ℕ) * y ^ (3 / 2 : ℝ) * H ^ (1 / 2 : ℝ) ≤
        S ^ (3 : ℕ) * M ^ (3 / 2 : ℝ) * ((1 + H) / 2) := by
      gcongr
    have h4 : 162 * (S ^ (3 : ℕ) * y ^ (3 / 2 : ℝ) * H ^ (1 / 2 : ℝ)) ≤ κ * (1 + H) := by
      rw [hκ]; nlinarith only [h3]
    nlinarith only [h4]
  have hgint : IntegrableOn (fun t : ℝ => (3 + κ) * (∫ x : Vec3, HD (x, t)) + κ) (Ioo 0 T)
      volume :=
    (hHtInt.const_mul _).add (integrableOn_const (by simp))
  obtain ⟨hFint, hFle⟩ := lps_slab_integrable_of_slice_bound hFm hFnn hgint hsl
  refine ⟨fun i => ?_, ?_⟩
  · refine (memLp_two_iff_integrable_sq (hQm i)).2 ?_
    refine Integrable.mono' hFint ((hQm i).pow 2) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun i : Fin 3 =>
      (lpsRegQ ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
  · refine hFle.trans ?_
    rw [integral_add (hHtInt.const_mul _) (integrableOn_const (by simp)), integral_const_mul,
      setIntegral_const]
    have : (volume.real (Ioo (0 : ℝ) T)) = T := by simp [Measure.real, hT.le]
    rw [this]
    simp only [smul_eq_mul]
    nlinarith only [hHsum, hκ0, mul_le_mul_of_nonneg_left hHsum (by positivity : 0 ≤ 3 + κ)]

end

end ESS.LPS

end
