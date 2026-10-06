/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyStaticPressure

/-!
# The mollifier limit of the energy pairing on one time slice

On one time slice the mollified energy pairing of one velocity component is a
sum of four pairings of mollified square-integrable fields. As the mollifier
radius tends to zero it converges to the corresponding pairing of the
unmollified fields, and it is bounded uniformly in the radius by products of
slice `L²` norms. This is the spatial limit in `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution Topology

noncomputable section

namespace CKN.Leray

/-- The Cauchy–Schwarz inequality for real square-integrable functions. -/
theorem abs_integral_mul_le_eLpNorm_two {f g : Vec3 → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  have hH := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (μ := volume) (f := f) (g := g) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    (r := (1 : ℝ≥0∞)) (b := fun a b : ℝ => a * b) (c := (1 : NNReal))
    (by exact continuous_mul) hf.aestronglyMeasurable hg.aestronglyMeasurable (by
      filter_upwards [] with x
      simp only [one_mul]
      simp [nnnorm_mul])
  have hH' : eLpNorm (fun x => f x * g x) 1 volume ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
    simpa using hH
  rw [← Real.norm_eq_abs, ← ENNReal.toReal_mul]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) ?_
  refine le_trans (le_of_eq ?_) hH'
  rw [eLpNorm_one_eq_lintegral_enorm]
  · simp_rw [ofReal_norm]
  · exact hf.aestronglyMeasurable.mul hg.aestronglyMeasurable

theorem toReal_eLpNorm_mul_le {X h : Vec3 → ℝ} (hX : MemLp X 2 volume)
    (hh : AEStronglyMeasurable h volume) {M : ℝ} (hM : ∀ x, |h x| ≤ M) :
    (eLpNorm (fun x => X x * h x) 2 volume).toReal ≤ M * (eLpNorm X 2 volume).toReal := by
  have hb : eLpNorm (fun x => X x * h x) 2 volume ≤ ENNReal.ofReal M * eLpNorm X 2 volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hX.aestronglyMeasurable.mul hh)
      (Eventually.of_forall fun x => by
        change ‖X x * h x‖ ≤ M * ‖X x‖
        rw [norm_mul, mul_comm, Real.norm_eq_abs (h x)]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)) 2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX.eLpNorm_ne_top) hb
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0] at h

theorem toReal_eLpNorm_leConv_leMol_le {g : Vec3 → ℝ} (hg : MemLp g 2 volume) (n : ℕ) :
    (eLpNorm (leConv (leMol n) g) 2 volume).toReal ≤ (eLpNorm g 2 volume).toReal :=
  ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_leConv_leMol_le hg n)

/-- The mollified energy pairing of one velocity component on one time slice. -/
@[expose]
def leDeltaRHS (n : ℕ) (uk : Vec3 → ℝ) (A : Fin 3 → Vec3 → ℝ) (q G F ψ : Vec3 → ℝ)
    (k : Fin 3) : ℝ :=
  -(∑ j : Fin 3, ∫ x, leConv (leMol n) (A j) x *
      (leConv (CKN.spatialDeriv (leMol n) j) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j))) -
    (∫ x, leConv (leMol n) q x *
      (leConv (CKN.spatialDeriv (leMol n) k) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec k))) +
    (∫ x, leConv (leMol n) uk x * ψ x * leConv (leMol n) G x) -
    ∫ x, leConv (leMol n) F x * (leConv (leMol n) uk x * ψ x)

/-- The limiting energy pairing of one velocity component on one time slice. -/
@[expose]
def leLimit (uk : Vec3 → ℝ) (Dk A : Fin 3 → Vec3 → ℝ) (q G F ψ : Vec3 → ℝ) (k : Fin 3) : ℝ :=
  -(∑ j : Fin 3, ∫ x, A j x * (Dk j x * ψ x + uk x * fderiv ℝ ψ x (CKN.basisVec j))) -
    (∫ x, q x * (Dk k x * ψ x + uk x * fderiv ℝ ψ x (CKN.basisVec k))) +
    (∫ x, G x * (uk x * ψ x)) - ∫ x, F x * (uk x * ψ x)

section Slice

variable {uk q G F ψ : Vec3 → ℝ} {Dk A : Fin 3 → Vec3 → ℝ} (hu : MemLp uk 2 volume)
  (hD : ∀ j, MemLp (Dk j) 2 volume) (hA : ∀ j, MemLp (A j) 2 volume) (hq : MemLp q 2 volume)
  (hG : MemLp G 2 volume) (hF : MemLp F 2 volume)
  (hweak : ∀ j, CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) j uk (Dk j))
  (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)

include hu hD hweak in
theorem leConv_productDeriv_eq (n : ℕ) (j : Fin 3) :
    (fun x => leConv (CKN.spatialDeriv (leMol n) j) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j)) =
      fun x => leConv (leMol n) (Dk j) x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j) := by
  funext x
  rw [leConv_spatialDeriv_leMol hu (hD j) (hweak j) n x]

include hu hD hweak hψ hψc in
theorem memLp_leConv_productDeriv (n : ℕ) (j : Fin 3) :
    MemLp (fun x => leConv (CKN.spatialDeriv (leMol n) j) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j)) 2 volume := by
  rw [leConv_productDeriv_eq hu hD hweak n j]
  exact (memLp_mul_compact (memLp_leConv_leMol (hD j) n) hψ.continuous hψc).add
    (memLp_mul_compact (memLp_leConv_leMol hu n)
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)))

include hu hD hψ hψc in
theorem memLp_productDeriv (j : Fin 3) :
    MemLp (fun x => Dk j x * ψ x + uk x * fderiv ℝ ψ x (CKN.basisVec j)) 2 volume :=
  (memLp_mul_compact (hD j) hψ.continuous hψc).add
    (memLp_mul_compact hu ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)))

include hu hD hA hq hG hF hweak hψ hψc in
/-- The mollifier limit of the energy pairing on one time slice. -/
theorem tendsto_leDeltaRHS (k : Fin 3) :
    Tendsto (fun n => leDeltaRHS n uk A q G F ψ k) atTop
      (𝓝 (leLimit uk Dk A q G F ψ k)) := by
  have hY := fun j => tendsto_mollified_productDeriv hu (hD j) (hweak j) hψ hψc
  have t1 := tendsto_finsetSum Finset.univ fun j _ => tendsto_integral_leConv_mul (hA j)
    (fun n => memLp_leConv_productDeriv hu hD hweak hψ hψc n j)
    (memLp_productDeriv hu hD hψ hψc j) (hY j)
  have t2 := tendsto_integral_leConv_mul hq
    (fun n => memLp_leConv_productDeriv hu hD hweak hψ hψc n k)
    (memLp_productDeriv hu hD hψ hψc k) (hY k)
  have t3 := tendsto_integral_leConv_mul hG
    (fun n => memLp_mul_compact (memLp_leConv_leMol hu n) hψ.continuous hψc)
    (memLp_mul_compact hu hψ.continuous hψc) (tendsto_mul_leConv_leMol hu hψ.continuous hψc)
  have t4 := tendsto_integral_leConv_mul hF
    (fun n => memLp_mul_compact (memLp_leConv_leMol hu n) hψ.continuous hψc)
    (memLp_mul_compact hu hψ.continuous hψc) (tendsto_mul_leConv_leMol hu hψ.continuous hψc)
  have e3 : ∀ n, ∫ x, leConv (leMol n) uk x * ψ x * leConv (leMol n) G x =
      ∫ x, leConv (leMol n) G x * (leConv (leMol n) uk x * ψ x) := fun n =>
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have h := ((t1.neg.sub t2).add t3).sub t4
  refine h.congr fun n => ?_
  unfold leDeltaRHS
  rw [e3 n]

include hu hD hA hq hG hF hweak hψ hψc in
/-- The uniform bound of the mollified energy pairing on one time slice. -/
theorem abs_leDeltaRHS_le {M : ℝ} (hMψ : ∀ x, |ψ x| ≤ M)
    (hMd : ∀ j x, |fderiv ℝ ψ x (CKN.basisVec j)| ≤ M) (n : ℕ) (k : Fin 3) :
    |leDeltaRHS n uk A q G F ψ k| ≤
      M * ((∑ j : Fin 3, (eLpNorm (A j) 2 volume).toReal + (eLpNorm q 2 volume).toReal) *
          (∑ j : Fin 3, (eLpNorm (Dk j) 2 volume).toReal + (eLpNorm uk 2 volume).toReal) +
        (eLpNorm uk 2 volume).toReal *
          ((eLpNorm G 2 volume).toReal + (eLpNorm F 2 volume).toReal)) := by
  set nu := (eLpNorm uk 2 volume).toReal
  set b := ∑ j : Fin 3, (eLpNorm (Dk j) 2 volume).toReal + nu with hb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMψ 0)
  have hdψ : ∀ j, AEStronglyMeasurable (fun x => fderiv ℝ ψ x (CKN.basisVec j)) volume :=
    fun j => ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  have hwψ : MemLp (fun x => leConv (leMol n) uk x * ψ x) 2 volume :=
    memLp_mul_compact (memLp_leConv_leMol hu n) hψ.continuous hψc
  have bwψ : (eLpNorm (fun x => leConv (leMol n) uk x * ψ x) 2 volume).toReal ≤ M * nu :=
    (toReal_eLpNorm_mul_le (memLp_leConv_leMol hu n) hψ.continuous.aestronglyMeasurable
      hMψ).trans (mul_le_mul_of_nonneg_left (toReal_eLpNorm_leConv_leMol_le hu n) hM0)
  have bY : ∀ j, (eLpNorm (fun x => leConv (CKN.spatialDeriv (leMol n) j) uk x * ψ x +
      leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j)) 2 volume).toReal ≤ M * b := by
    intro j
    rw [leConv_productDeriv_eq hu hD hweak n j]
    have m1 := memLp_mul_compact (memLp_leConv_leMol (hD j) n) hψ.continuous hψc
    have m2 : MemLp (fun x => leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j)) 2 volume :=
      memLp_mul_compact (memLp_leConv_leMol hu n)
        ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j))
    have hadd := eLpNorm_add_le (μ := volume) (f := fun x => leConv (leMol n) (Dk j) x * ψ x)
      (g := fun x => leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j)) (p := 2)
      (by norm_num)
    have hadd' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨m1.eLpNorm_ne_top,
      m2.eLpNorm_ne_top⟩) hadd
    rw [ENNReal.toReal_add m1.eLpNorm_ne_top m2.eLpNorm_ne_top] at hadd'
    have c1 := (toReal_eLpNorm_mul_le (memLp_leConv_leMol (hD j) n)
      hψ.continuous.aestronglyMeasurable hMψ).trans
      (mul_le_mul_of_nonneg_left (toReal_eLpNorm_leConv_leMol_le (hD j) n) hM0)
    have c2 := (toReal_eLpNorm_mul_le (memLp_leConv_leMol hu n) (hdψ j) (hMd j)).trans
      (mul_le_mul_of_nonneg_left (toReal_eLpNorm_leConv_leMol_le hu n) hM0)
    have hDj : (eLpNorm (Dk j) 2 volume).toReal ≤ ∑ i : Fin 3, (eLpNorm (Dk i) 2 volume).toReal :=
      Finset.single_le_sum (f := fun i => (eLpNorm (Dk i) 2 volume).toReal)
        (fun i _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
    have hfun : (fun x => leConv (leMol n) (Dk j) x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j)) =
        (fun x => leConv (leMol n) (Dk j) x * ψ x) +
          fun x => leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j) := rfl
    rw [hfun]
    have hMD := mul_le_mul_of_nonneg_left hDj hM0
    calc _ ≤ _ := hadd'
      _ ≤ M * (eLpNorm (Dk j) 2 volume).toReal + M * nu := add_le_add c1 c2
      _ ≤ M * b := by rw [hb, mul_add]; exact add_le_add hMD le_rfl
  have b1 : ∀ j, |∫ x, leConv (leMol n) (A j) x *
      (leConv (CKN.spatialDeriv (leMol n) j) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j))| ≤
      (eLpNorm (A j) 2 volume).toReal * (M * b) := fun j =>
    (abs_integral_mul_le_eLpNorm_two (memLp_leConv_leMol (hA j) n)
      (memLp_leConv_productDeriv hu hD hweak hψ hψc n j)).trans
      (mul_le_mul (toReal_eLpNorm_leConv_leMol_le (hA j) n) (bY j) ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg)
  have b2 : |∫ x, leConv (leMol n) q x *
      (leConv (CKN.spatialDeriv (leMol n) k) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec k))| ≤
      (eLpNorm q 2 volume).toReal * (M * b) :=
    (abs_integral_mul_le_eLpNorm_two (memLp_leConv_leMol hq n)
      (memLp_leConv_productDeriv hu hD hweak hψ hψc n k)).trans
      (mul_le_mul (toReal_eLpNorm_leConv_leMol_le hq n) (bY k) ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg)
  have b3 : |∫ x, leConv (leMol n) uk x * ψ x * leConv (leMol n) G x| ≤
      (eLpNorm G 2 volume).toReal * (M * nu) := by
    rw [show (∫ x, leConv (leMol n) uk x * ψ x * leConv (leMol n) G x) =
      ∫ x, leConv (leMol n) G x * (leConv (leMol n) uk x * ψ x) from
        integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)]
    exact (abs_integral_mul_le_eLpNorm_two (memLp_leConv_leMol hG n) hwψ).trans
      (mul_le_mul (toReal_eLpNorm_leConv_leMol_le hG n) bwψ ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg)
  have b4 : |∫ x, leConv (leMol n) F x * (leConv (leMol n) uk x * ψ x)| ≤
      (eLpNorm F 2 volume).toReal * (M * nu) :=
    (abs_integral_mul_le_eLpNorm_two (memLp_leConv_leMol hF n) hwψ).trans
      (mul_le_mul (toReal_eLpNorm_leConv_leMol_le hF n) bwψ ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg)
  have bs : |∑ j : Fin 3, ∫ x, leConv (leMol n) (A j) x *
      (leConv (CKN.spatialDeriv (leMol n) j) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j))| ≤
      (∑ j : Fin 3, (eLpNorm (A j) 2 volume).toReal) * (M * b) := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => b1 j)
  unfold leDeltaRHS
  set S1 := ∑ j : Fin 3, ∫ x, leConv (leMol n) (A j) x *
      (leConv (CKN.spatialDeriv (leMol n) j) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j))
  set S2 := ∫ x, leConv (leMol n) q x *
      (leConv (CKN.spatialDeriv (leMol n) k) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec k))
  set S3 := ∫ x, leConv (leMol n) uk x * ψ x * leConv (leMol n) G x
  set S4 := ∫ x, leConv (leMol n) F x * (leConv (leMol n) uk x * ψ x)
  have t1 := abs_sub (-S1 - S2 + S3) S4
  have t2 := abs_add_le (-S1 - S2) S3
  have t3 := abs_sub (-S1) S2
  have t4 := abs_neg S1
  set sA := ∑ j : Fin 3, (eLpNorm (A j) 2 volume).toReal
  set nq := (eLpNorm q 2 volume).toReal
  set nG := (eLpNorm G 2 volume).toReal
  set nF := (eLpNorm F 2 volume).toReal
  have : |-S1 - S2 + S3 - S4| ≤ sA * (M * b) + nq * (M * b) + nG * (M * nu) + nF * (M * nu) := by
    linarith only [t1, t2, t3, t4, bs, b2, b3, b4]
  refine this.trans (le_of_eq ?_)
  ring

end Slice

end CKN.Leray

end
