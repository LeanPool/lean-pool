/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsEstimates

/-!
# Slice estimates for regularized Leray tails

Almost every positive-time Sobolev slice has the interpolation and pressure
bounds needed for the quantitative flux estimate in `lem:reg-tails`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regTails_interpolate_four
    {μ : Measure Vec3} {g : Vec3 → ℝ}
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm g (ENNReal.ofReal (4 : ℝ)) μ ≤
      eLpNorm g 2 μ ^ (1 / 4 : ℝ) *
        eLpNorm g 6 μ ^ (3 / 4 : ℝ) := by
  let w : Vec3 → ℝ := fun x => ‖g x‖ ^ (1 / 4 : ℝ)
  let v : Vec3 → ℝ := fun x => ‖g x‖ ^ (3 / 4 : ℝ)
  have hw : AEStronglyMeasurable w μ := by
    simpa [w, Function.comp_def] using
      ((Real.continuous_rpow_const (q := (1 / 4 : ℝ)) (by norm_num)).aemeasurable.comp_aemeasurable
        hg.aemeasurable.norm).aestronglyMeasurable
  have hv : AEStronglyMeasurable v μ := by
    simpa [v, Function.comp_def] using
      ((Real.continuous_rpow_const (q := (3 / 4 : ℝ)) (by norm_num)).aemeasurable.comp_aemeasurable
        hg.aemeasurable.norm).aestronglyMeasurable
  have hholder : eLpNorm (fun x => w x * v x) (ENNReal.ofReal (4 : ℝ)) μ ≤
      eLpNorm w (ENNReal.ofReal (8 : ℝ)) μ *
        eLpNorm v (ENNReal.ofReal (8 : ℝ)) μ := by
    have htriple : ENNReal.HolderTriple (ENNReal.ofReal (8 : ℝ))
        (ENNReal.ofReal (8 : ℝ)) (ENNReal.ofReal (4 : ℝ)) := by
      refine ⟨?_⟩
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
        ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
    simpa [ENNReal.smul_def, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (μ := μ) (p := ENNReal.ofReal (8 : ℝ))
        (q := ENNReal.ofReal (8 : ℝ))
        (r := ENNReal.ofReal (4 : ℝ))
        (fun a b : ℝ => a * b) 1 continuous_mul hw hv
        (Filter.Eventually.of_forall fun x => by
          simp [Real.norm_eq_abs, one_mul]) (hpqr := htriple))
  have hprod : (fun x => w x * v x) = fun x => ‖g x‖ := by
    funext x
    by_cases hx : ‖g x‖ = 0
    · have hgx : g x = 0 := norm_eq_zero.mp hx
      simp [w, v, hgx]
    · change ‖g x‖ ^ (1 / 4 : ℝ) * ‖g x‖ ^ (3 / 4 : ℝ) = ‖g x‖
      rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx))]
      norm_num
  have hwp : eLpNorm w (ENNReal.ofReal (8 : ℝ)) μ =
      eLpNorm g 2 μ ^ (1 / 4 : ℝ) := by
    have hraw := eLpNorm_norm_rpow g hg (q := (1 / 4 : ℝ))
      (by norm_num) (p := ENNReal.ofReal (8 : ℝ))
    have hexp : ENNReal.ofReal (8 : ℝ) * ENNReal.ofReal (1 / 4 : ℝ) = 2 := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    rw [hexp] at hraw
    simpa [w] using hraw
  have hvp : eLpNorm v (ENNReal.ofReal (8 : ℝ)) μ =
      eLpNorm g 6 μ ^ (3 / 4 : ℝ) := by
    have hraw := eLpNorm_norm_rpow g hg (q := (3 / 4 : ℝ))
      (by norm_num) (p := ENNReal.ofReal (8 : ℝ))
    have hexp : ENNReal.ofReal (8 : ℝ) * ENNReal.ofReal (3 / 4 : ℝ) = 6 := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    rw [hexp] at hraw
    simpa [v] using hraw
  rw [hprod, hwp, hvp, eLpNorm_norm g hg] at hholder
  exact hholder

/-- Whole-space L⁴ control for an H¹ scalar component, obtained by interpolating
the global Sobolev L⁶ estimate with L². This is used in the quantitative error
bound in `lem:reg-tails`. -/
theorem regTails_h1_component_L4
    (v : CKN.H1Function (Set.univ : Set Vec3)) :
    eLpNorm v.toFun (ENNReal.ofReal (4 : ℝ)) volume ≤
      CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
        eLpNorm v.toFun 2 volume ^ (1 / 4 : ℝ) *
          eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume ^
            (3 / 4 : ℝ) := by
  have hv2 : MemLp v.toFun 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn] using v.memL2
  have hgradFun (i : Fin 3) : MemLp (fun x => v.grad x i) 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn] using v.grad_memL2 i
  have hgrad2 : MemLp v.grad 2 volume := (memLp_pi_iff).2 hgradFun
  have hgradNormLeEuclidean : eLpNorm v.grad 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
    rw [← eLpNorm_norm v.grad hgrad2.aestronglyMeasurable]
    apply eLpNorm_mono_ae_real (hgrad2.aestronglyMeasurable.norm)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm (v.grad x)
  have hv6 : eLpNorm v.toFun 6 volume ≤
      CKN.gagliardoNirenbergSobolevConstant *
        eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
    have hsup : eLpNorm v.toFun 6 volume ≤
        CKN.gagliardoNirenbergSobolevConstant * eLpNorm v.grad 2 volume := by
      simpa [CKN.gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
        CKN.weakGradientLpNormOn, Measure.restrict_univ] using
        (Classical.choose_spec CKN.sobolev_L6_global).2 v
    exact hsup.trans (mul_le_mul_of_nonneg_left hgradNormLeEuclidean
      (by positivity))
  calc
    eLpNorm v.toFun (ENNReal.ofReal (4 : ℝ)) volume ≤
        eLpNorm v.toFun 2 volume ^ (1 / 4 : ℝ) *
          eLpNorm v.toFun 6 volume ^ (3 / 4 : ℝ) :=
      regTails_interpolate_four hv2.aestronglyMeasurable
    _ ≤ eLpNorm v.toFun 2 volume ^ (1 / 4 : ℝ) *
          (CKN.gagliardoNirenbergSobolevConstant *
            eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume) ^
              (3 / 4 : ℝ) := by
      gcongr
    _ = CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
          eLpNorm v.toFun 2 volume ^ (1 / 4 : ℝ) *
            eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume ^
              (3 / 4 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      ac_rfl

private theorem regTails_component_gradient_norm_le
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (i : Fin 3) :
    vec3EuclideanNorm (D z i) ≤ Real.sqrt (spatialGradientSq u D z) := by
  change Real.sqrt (∑ j : Fin 3, (D z i j) ^ (2 : ℕ)) ≤
    Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3, (D z k j) ^ (2 : ℕ))
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg (D z k j))
    (Finset.mem_univ i)

/-- On almost every Sobolev slice, the global gradient norm used in the
time-integrated dissipation is the square-integrable size supplied by the
explicit weak gradient. -/
theorem regTails_gradient_slice_norm_eq_profile
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (t : ℝ) (ht : 0 < t)
    (hDcont : ∀ i j, ContinuousOn (fun z : ParabolicPoint => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))))
    (h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3))
    (hGradients : ∀ i x j, (h i).grad x j = D (x, t) i j) :
    (eLpNorm (fun x : Vec3 => Real.sqrt (spatialGradientSq u D (x, t)))
      2 volume).toReal =
      Real.sqrt ((∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq u D (x, t)) ∂volume).toReal) := by
  let G : Vec3 → ℝ := fun x => Real.sqrt (spatialGradientSq u D (x, t))
  have hDprod : ∀ i j, ContinuousOn (fun z : Vec3 × ℝ => D (z.1, z.2) i j)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) := by
    intro i j
    exact regUniform_continuousOn_pullback (hDcont i j)
      (fun z hz => ⟨Set.mem_univ _, hz.2⟩)
  have hDslice : ∀ i j, Continuous (fun x : Vec3 => D (x, t) i j) := by
    intro i j
    have hmap : MapsTo (fun x : Vec3 => (x, t)) Set.univ
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) := by
      intro x hx
      exact ⟨Set.mem_univ _, ht⟩
    have hcomp' : ContinuousOn (fun x : Vec3 => D (x, t) i j) Set.univ :=
      (hDprod i j).comp (continuous_id.prodMk continuous_const).continuousOn hmap
    exact (continuousOn_univ.mp hcomp')
  have hGcont : Continuous G := by
    have hSq : Continuous (fun x : Vec3 => spatialGradientSq u D (x, t)) := by
      unfold spatialGradientSq
      apply continuous_finsetSum
      intro i hi
      apply continuous_finsetSum
      intro j hj
      exact (hDslice i j).pow 2
    exact Real.continuous_sqrt.comp hSq
  have hGmeas : AEStronglyMeasurable G volume := hGcont.aestronglyMeasurable
  have hDmem (i j : Fin 3) : MemLp (fun x : Vec3 => D (x, t) i j) 2 volume := by
    simpa [CKN.GradMemLpOn, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
      Measure.restrict_univ, hGradients i _ j] using (h i).grad_memL2 j
  have hSqIntegrable : Integrable
      (fun x : Vec3 => spatialGradientSq u D (x, t)) volume := by
    have hsum : Integrable (fun x : Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (D (x, t) i j) ^ (2 : ℕ)) volume :=
      integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => (hDmem i j).integrable_sq
    exact hsum.congr (Eventually.of_forall fun x => rfl)
  have hGsqIntegrable : Integrable (fun x : Vec3 => G x ^ (2 : ℕ)) volume := by
    have hEq : (fun x : Vec3 => G x ^ (2 : ℕ)) =
        fun x => spatialGradientSq u D (x, t) := by
      funext x
      dsimp [G]
      rw [Real.sq_sqrt]
      unfold spatialGradientSq
      exact Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg (D (x, t) i j)
    exact hSqIntegrable.congr hEq.symm.eventuallyEq
  have hGmem : MemLp G 2 volume :=
    (memLp_two_iff_integrable_sq hGmeas).2 hGsqIntegrable
  have hLin : (∫ x : Vec3, G x ^ (2 : ℕ) ∂volume) =
      (∫⁻ x : Vec3, ENNReal.ofReal
        (spatialGradientSq u D (x, t)) ∂volume).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      apply lintegral_congr
      intro x
      congr 1
      have hEq : G x ^ (2 : ℕ) = spatialGradientSq u D (x, t) := by
        dsimp [G]
        rw [Real.sq_sqrt]
        unfold spatialGradientSq
        exact Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun j _ => sq_nonneg (D (x, t) i j)
      rw [hEq]
    · exact Filter.Eventually.of_forall fun x => sq_nonneg (G x)
    · have hEq : (fun x : Vec3 => G x ^ (2 : ℕ)) = G * G := by
        funext x
        simp [pow_two]
      rw [hEq]
      exact (hGcont.mul hGcont).aestronglyMeasurable
  have hLpFormula := hGmem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hNorm : (eLpNorm G 2 volume).toReal =
      Real.sqrt (∫ x : Vec3, G x ^ (2 : ℕ) ∂volume) := by
    rw [hLpFormula]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    rw [Real.sqrt_eq_rpow]
  rw [hNorm, hLin]

/-- Almost every regularized velocity slice satisfies the L⁴ Gagliardo–Nirenberg
bound needed for the convection and pressure terms in `lem:reg-tails`. -/
theorem regTails_vector_slice_L4
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (t : ℝ) (h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3))
    (hValues : ∀ i x, (h i).toFun x = u (x, t) i)
    (hGradients : ∀ i x j, (h i).grad x j = D (x, t) i j)
    (hU : MemLp (fun x : Vec3 => u (x, t)) 2 volume) :
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume ≤
      3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume ^
          (1 / 4 : ℝ) *
        eLpNorm (fun x : Vec3 => Real.sqrt (spatialGradientSq u D (x, t)))
          2 volume ^ (3 / 4 : ℝ) := by
  let V : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (u (x, t))
  have hV : MemLp V 2 volume := by
    exact hU.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hVmeas : AEStronglyMeasurable V volume := hV.aestronglyMeasurable
  have hVnorm : (fun x : Vec3 => ‖V x‖) =
      (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) := by
    funext x
    exact (vec3EuclideanNorm_eq_l2 (u (x, t))).symm
  have hcomponentTwo (i : Fin 3) :
      eLpNorm (fun x : Vec3 => u (x, t) i) 2 volume ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume := by
    have hcoord : AEStronglyMeasurable (fun x : Vec3 => u (x, t) i) volume :=
      (hU.eval i).aestronglyMeasurable
    apply eLpNorm_mono_ae_real hcoord
    filter_upwards [] with x
    exact abs_apply_le_vec3EuclideanNorm (u (x, t)) i
  have hgradientTwo (i : Fin 3) :
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (D (x, t) i)) 2 volume ≤
        eLpNorm (fun x : Vec3 => Real.sqrt
          (spatialGradientSq u D (x, t))) 2 volume := by
    have hgrad : MemLp (fun x : Vec3 => D (x, t) i) 2 volume := by
      apply memLp_pi_iff.mpr
      intro j
      simpa [CKN.GradMemLpOn, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
        Measure.restrict_univ, hGradients i _ j] using (h i).grad_memL2 j
    have hgradNorm : AEStronglyMeasurable
        (fun x : Vec3 => vec3EuclideanNorm (D (x, t) i)) volume :=
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        hgrad.aestronglyMeasurable
    apply eLpNorm_mono_ae_real hgradNorm
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using
      regTails_component_gradient_norm_le u D (x, t) i
  have hscalar (i : Fin 3) :
      eLpNorm (fun x : Vec3 => u (x, t) i) (ENNReal.ofReal (4 : ℝ)) volume ≤
        CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume ^
            (1 / 4 : ℝ) *
          eLpNorm (fun x : Vec3 => Real.sqrt (spatialGradientSq u D (x, t)))
            2 volume ^ (3 / 4 : ℝ) := by
    have hgn := regTails_h1_component_L4 (h i)
    have hvalue : eLpNorm (fun x : Vec3 => (h i).toFun x)
        (ENNReal.ofReal (4 : ℝ)) volume =
        eLpNorm (fun x : Vec3 => u (x, t) i)
          (ENNReal.ofReal (4 : ℝ)) volume := by
      apply eLpNorm_congr_ae
      filter_upwards [] with x
      exact hValues i x
    have hvalue2 : eLpNorm (h i).toFun 2 volume =
        eLpNorm (fun x : Vec3 => u (x, t) i) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [] with x
      exact hValues i x
    have hgradvalue : eLpNorm
        (fun x : Vec3 => vec3EuclideanNorm ((h i).grad x)) 2 volume =
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (D (x, t) i)) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [] with x
      congr 1
      funext j
      exact hGradients i x j
    rw [hvalue, hvalue2, hgradvalue] at hgn
    calc
      _ = eLpNorm (fun x : Vec3 => u (x, t) i)
          (ENNReal.ofReal (4 : ℝ)) volume := rfl
      _ ≤ CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
            eLpNorm (fun x : Vec3 => u (x, t) i) 2 volume ^ (1 / 4 : ℝ) *
            eLpNorm (fun x : Vec3 => vec3EuclideanNorm (D (x, t) i))
              2 volume ^ (3 / 4 : ℝ) := by
        exact hgn
      _ ≤ _ := by
        gcongr
        · exact hcomponentTwo i
        · exact hgradientTwo i
  have hsum : eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume ≤
      ∑ i : Fin 3, eLpNorm (fun x : Vec3 => u (x, t) i)
        (ENNReal.ofReal (4 : ℝ)) volume := by
    have hpoint : ∀ x : Vec3, ‖V x‖ ≤ ∑ i : Fin 3, |u (x, t) i| := by
      intro x
      calc
        ‖V x‖ = vec3EuclideanNorm (u (x, t)) := congrFun hVnorm x
        _ ≤ ∑ i : Fin 3, |u (x, t) i| :=
          vec3EuclideanNorm_le_sum_abs (u (x, t))
    calc
      eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume ≤
          eLpNorm (fun x => ∑ i : Fin 3, |u (x, t) i|)
            (ENNReal.ofReal (4 : ℝ)) volume := by
        apply eLpNorm_mono_ae_real hVmeas
        exact Filter.Eventually.of_forall hpoint
      _ ≤ ∑ i : Fin 3, eLpNorm (fun x : Vec3 => |u (x, t) i|)
            (ENNReal.ofReal (4 : ℝ)) volume :=
        eLpNorm_sum_le (p := ENNReal.ofReal (4 : ℝ))
          (s := (Finset.univ : Finset (Fin 3)))
          (f := fun i x => |u (x, t) i|)
          (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 : ℝ))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact eLpNorm_norm _ ((hU.eval i).aestronglyMeasurable)
  have hsumBound :
      (∑ i : Fin 3, eLpNorm (fun x : Vec3 => u (x, t) i)
        (ENNReal.ofReal (4 : ℝ)) volume) ≤
        ∑ _i : Fin 3,
          (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
            eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume ^
              (1 / 4 : ℝ) *
            eLpNorm (fun x : Vec3 => Real.sqrt (spatialGradientSq u D (x, t)))
              2 volume ^ (3 / 4 : ℝ)) :=
    Finset.sum_le_sum fun i _ => hscalar i
  have hleft : eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume =
      eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume := by
    rw [← eLpNorm_norm V hVmeas]
    exact congrArg (fun f => eLpNorm f (ENNReal.ofReal (4 : ℝ)) volume)
      hVnorm.symm
  rw [hleft]
  calc
    eLpNorm V (ENNReal.ofReal (4 : ℝ)) volume ≤
        ∑ i : Fin 3, eLpNorm (fun x : Vec3 => u (x, t) i)
          (ENNReal.ofReal (4 : ℝ)) volume := hsum
    _ ≤ ∑ _i : Fin 3,
          (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
            eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume ^
              (1 / 4 : ℝ) *
            eLpNorm (fun x : Vec3 => Real.sqrt (spatialGradientSq u D (x, t)))
              2 volume ^ (3 / 4 : ℝ)) := hsumBound
    _ = _ := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        mul_assoc, mul_left_comm, mul_comm]

/-- The Riesz pressure representative has a slice `L²` estimate controlled
by the fourth-power velocity norms. -/
theorem regTails_mollified_velocity_slice_L4
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hU2 : MemLp (regUniformVelocitySlice u t) 2 volume)
    (hU4 : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (4 : ℝ)) volume) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (4 : ℝ)) volume := by
  let f : Vec3 → Vec3 := fun x => u (x, t)
  let ψ := regMollifyVector ρ ε hε (regUniformSpatialField f)
  have hf₂ : MemLp (regUniformSpatialField f) 2 volume := by
    change MemLp (regUniformVelocitySlice u t) 2 volume
    exact hU2
  have hcontract := regMollifyVector_eLpNorm_le ρ ε hε hf₂
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 : ℝ))
    (by norm_num : ENNReal.ofReal (4 : ℝ) ≠ ⊤)
  have hψmeas : AEStronglyMeasurable ψ volume :=
    regMollifyVector_aestronglyMeasurable ρ ε hε hf₂
  have hψcomp := hψmeas.comp_measurePreserving vec3ToL2Vec3_measurePreserving
  have hinput : eLpNorm (regUniformL2VectorNormOnVec3
      (regUniformSpatialField f)) (ENNReal.ofReal (4 : ℝ)) volume =
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume := by
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp [regUniformL2VectorNormOnVec3, regUniformSpatialField, f,
      vec3EuclideanNorm_eq_l2]
  have hcoerce : (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t))) =
      fun x => ‖ψ (WithLp.toLp 2 x)‖ := by
    funext x
    change vec3EuclideanNorm
        (WithLp.ofLp (ψ (WithLp.toLp 2 x))) = ‖ψ (WithLp.toLp 2 x)‖
    rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_ofLp]
  have houtput : eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume = eLpNorm ψ
          (ENNReal.ofReal (4 : ℝ)) volume := by
    calc
      _ = eLpNorm (fun x : Vec3 => ‖ψ (WithLp.toLp 2 x)‖)
            (ENNReal.ofReal (4 : ℝ)) volume := by
        exact congrArg (fun g => eLpNorm g (ENNReal.ofReal (4 : ℝ)) volume) hcoerce
      _ = eLpNorm (fun x : Vec3 => ψ (WithLp.toLp 2 x))
            (ENNReal.ofReal (4 : ℝ)) volume := eLpNorm_norm _ hψcomp
      _ = eLpNorm ψ (ENNReal.ofReal (4 : ℝ)) volume :=
        eLpNorm_comp_measurePreserving hψmeas vec3ToL2Vec3_measurePreserving
  have hbound : eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume ≤
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (4 : ℝ)) volume := by
    rw [houtput]
    exact hcontract.trans_eq hinput
  refine ⟨?_, hbound⟩
  rw [memLp_iff]
  exact lt_of_le_of_lt hbound hU4.eLpNorm_lt_top

/-- Convolution does not increase the Euclidean slice `L²` norm of the
regularized velocity. -/
theorem regTails_mollified_velocity_slice_L2
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hU2 : MemLp (regUniformVelocitySlice u t) 2 volume) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t))) 2 volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t))) 2 volume ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume := by
  let f : Vec3 → Vec3 := fun x => u (x, t)
  let ψ := regMollifyVector ρ ε hε (regUniformSpatialField f)
  have hf₂ : MemLp (regUniformSpatialField f) 2 volume := by
    change MemLp (regUniformVelocitySlice u t) 2 volume
    exact hU2
  have hcontract := regMollifyVector_eLpNorm_two_le ρ ε hε hf₂
  have hψmeas : AEStronglyMeasurable ψ volume :=
    regMollifyVector_aestronglyMeasurable ρ ε hε hf₂
  have hψcomp := hψmeas.comp_measurePreserving vec3ToL2Vec3_measurePreserving
  have hfieldNorm : eLpNorm (regUniformSpatialField f) 2 volume =
      eLpNorm (regUniformL2VectorNormOnVec3
        (regUniformSpatialField f)) 2 volume := by
    calc
      _ = eLpNorm (fun x : L2Vec3 => ‖regUniformSpatialField f x‖) 2 volume :=
        (eLpNorm_norm (regUniformSpatialField f) hf₂.aestronglyMeasurable).symm
      _ = eLpNorm (regUniformL2VectorNormOnVec3
          (regUniformSpatialField f)) 2 volume := by
        exact (eLpNorm_comp_measurePreserving
          (hf₂.aestronglyMeasurable.norm) vec3ToL2Vec3_measurePreserving).symm
  have hinput : eLpNorm (regUniformL2VectorNormOnVec3
      (regUniformSpatialField f)) 2 volume =
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp [regUniformL2VectorNormOnVec3, regUniformSpatialField, f,
      vec3EuclideanNorm_eq_l2]
  have hcoerce : (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t))) =
      fun x => ‖ψ (WithLp.toLp 2 x)‖ := by
    funext x
    change vec3EuclideanNorm
        (WithLp.ofLp (ψ (WithLp.toLp 2 x))) = ‖ψ (WithLp.toLp 2 x)‖
    rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_ofLp]
  have houtput : eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t))) 2 volume =
      eLpNorm ψ 2 volume := by
    calc
      _ = eLpNorm (fun x => ‖ψ (WithLp.toLp 2 x)‖) 2 volume := by
        exact congrArg (fun g => eLpNorm g 2 volume) hcoerce
      _ = eLpNorm (fun x => ψ (WithLp.toLp 2 x)) 2 volume := eLpNorm_norm _ hψcomp
      _ = eLpNorm ψ 2 volume :=
        eLpNorm_comp_measurePreserving hψmeas vec3ToL2Vec3_measurePreserving
  have hbound : eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t))) 2 volume ≤
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume := by
    rw [houtput]
    exact hcontract.trans_eq (hfieldNorm.trans hinput)
  refine ⟨memLp_iff.mpr ?_, hbound⟩
  calc
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t))) 2 volume =
        eLpNorm ψ 2 volume := houtput
    _ ≤ eLpNorm (regUniformSpatialField f) 2 volume := hcontract
    _ < ⊤ := hU2.eLpNorm_lt_top

/-- The Riesz pressure representative has a slice `L²` estimate controlled
by the fourth-power velocity norms. -/
theorem regTails_pressure_slice_norm_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hU2 : ∀ t, 0 ≤ t → MemLp (regUniformVelocitySlice u t) 2 volume)
    (hUbound : ∀ t, 0 < t → ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec3,
      vec3EuclideanNorm (u (x, t)) ≤ B)
    (hR4 : ∀ t : ℝ, 0 < t → ∃ hF : ∀ i j : Fin 3,
      MemLp (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
        (ENNReal.ofReal (2 : ℝ)) volume,
      (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF i j).toLp (fun x : Vec3 =>
            regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j))) :
    ∀ t : ℝ, 0 < t →
      (eLpNorm (fun x : Vec3 => p (x, t))
          (ENNReal.ofReal (2 : ℝ)) volume).toReal ≤
        9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            (regUniformMollifiedVelocity ρ ε hε u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume).toReal *
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
            (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
  classical
  let P : ℝ → Lp ℝ (ENNReal.ofReal (2 : ℝ)) (volume : Measure Vec3) :=
    fun t => if ht : 0 < t then
      let hFt := Classical.choose (hR4 t ht)
      let Ft : PressureTensorLp (2 : ℝ) := fun i j =>
        (hFt i j).toLp (fun x : Vec3 =>
          regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
      rieszPressureSlice (2 : ℝ) (by norm_num) Ft
    else 0
  have hR4Class : ∀ t : ℝ, 0 < t → ∃ F : PressureTensorLp (2 : ℝ),
      (∀ i j, (F i j : Vec3 → ℝ) =ᵐ[volume]
        regPressureTensorSlice ρ ε hε u t i j) ∧
      P t = rieszPressureSlice (2 : ℝ) (by norm_num) F := by
    intro t ht
    let hFt := Classical.choose (hR4 t ht)
    let Ft : PressureTensorLp (2 : ℝ) := fun i j =>
      (hFt i j).toLp (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
    refine ⟨Ft, ?_, ?_⟩
    · intro i j
      exact (hFt i j).coeFn_toLp
    · simp [P, ht, Ft]
  have hBound := regPressure_slice_L2_bound ρ ε hε u P hU2 hUbound hR4Class
  intro t ht
  let hFt := Classical.choose (hR4 t ht)
  let Ft : PressureTensorLp (2 : ℝ) := fun i j =>
    (hFt i j).toLp (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
  have hPressure : (fun x : Vec3 => p (x, t)) =ᵐ[volume]
      rieszPressureSlice (2 : ℝ) (by norm_num) Ft := by
    have hSource := Classical.choose_spec (hR4 t ht)
    have hRepresentative := rieszPressureSliceRepresentative_ae_eq
      (2 : ℝ) (by norm_num) Ft
    exact hSource.trans hRepresentative.symm
  have hNorm :
      (eLpNorm (fun x : Vec3 => p (x, t))
        (ENNReal.ofReal (2 : ℝ)) volume).toReal = ‖P t‖ := by
    rw [eLpNorm_congr_ae hPressure]
    have hPteq : P t = rieszPressureSlice (2 : ℝ) (by norm_num) Ft := by
      simp [P, ht, Ft]
    rw [hPteq, MeasureTheory.toReal_eLpNorm, Lp.norm_def]
    rfl
  rw [hNorm]
  exact hBound t ht

end CKN.Leray

end
