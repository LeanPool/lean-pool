/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSlices

/-!
# Assoc Pressure Mixed Norm

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Finite square-integral and strong measurability give the `L²` energy
class used in the space-time cutoff limits for `thm:assoc-pressure`. -/
theorem associatedPressure_memLp_two_of_lintegral_lt_top
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ)
    (hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) < ⊤) :
    MemLp f 2 μ := by
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

private theorem associatedPressure_integrable_sq_of_lintegral_lt_top
    {E : Type} [NormedAddCommGroup E] {S : Set ParabolicPoint}
    {f : ParabolicPoint → E}
    (hf : AEStronglyMeasurable f (volume.restrict S))
    (hfin : (∫⁻ z in S, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖f z‖ : ℝ) ^ (2 : ℕ)) (volume.restrict S) := by
  have hmeas : AEStronglyMeasurable (fun z => (‖f z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict S) := hf.norm.pow 2
  have hfinite :
      (∫⁻ z in S, ENNReal.ofReal ((‖f z‖ : ℝ) ^ (2 : ℕ))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_)) hfin)
    filter_upwards [] with z
    calc
      ENNReal.ofReal ((‖f z‖ : ℝ) ^ (2 : ℕ))
          = ENNReal.ofReal ((‖f z‖ : ℝ) ^ (2 : ℝ)) := by
              norm_num [Real.rpow_natCast]
      _ = ENNReal.ofReal ‖f z‖ ^ (2 : ℝ) :=
        (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
      _ = ‖f z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hfinite

private theorem associatedPressure_memLp_four_of_memLp_two_six
    {α : Type} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf2 : MemLp f 2 μ) (hf6 : MemLp f (ENNReal.ofReal (6 : ℝ)) μ) :
    MemLp f (ENNReal.ofReal (4 : ℝ)) μ := by
  let g : α → ℝ := fun x => ‖f x‖ ^ (3 : ℝ)
  have hgmeas : AEStronglyMeasurable g μ := by
    simpa [g, Function.comp_def] using
      ((Real.continuous_rpow_const (q := (3 : ℝ)) (by norm_num)).aemeasurable.comp_aemeasurable
        hf2.aestronglyMeasurable.aemeasurable.norm).aestronglyMeasurable
  have hg2 : MemLp g 2 μ := by
    rw [memLp_iff]
    have hnorm := eLpNorm_norm_rpow f hf2.aestronglyMeasurable
      (q := (3 : ℝ)) (by norm_num) (p := (2 : ℝ≥0∞))
    have hexp : (2 : ℝ≥0∞) * ENNReal.ofReal (3 : ℝ) =
        ENNReal.ofReal (6 : ℝ) := by norm_num
    rw [hexp] at hnorm
    have hfin : eLpNorm f (ENNReal.ofReal (6 : ℝ)) μ < ⊤ := hf6.eLpNorm_lt_top
    have hpowfin : eLpNorm f (ENNReal.ofReal (6 : ℝ)) μ ^ (3 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
    change eLpNorm (fun x => ‖f x‖ ^ (3 : ℝ)) 2 μ < ⊤
    rw [hnorm]
    exact hpowfin
  have : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hprod : MemLp (fun x => f x * g x) 1 μ := hf2.mul hg2
  have hint : Integrable (fun x => f x * g x) μ :=
    memLp_one_iff_integrable.mp hprod
  have hpoint (x : α) : ‖f x * g x‖ = ‖f x‖ ^ (4 : ℝ) := by
    by_cases hx : ‖f x‖ = 0
    · have hfx : f x = 0 := norm_eq_zero.mp hx
      simp [g, hfx]
    · have hpos : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      rw [norm_mul]
      rw [show ‖g x‖ = ‖f x‖ ^ (3 : ℝ) by
        simp [g]]
      calc
        ‖f x‖ * ‖f x‖ ^ (3 : ℝ) = ‖f x‖ ^ (1 : ℝ) * ‖f x‖ ^ (3 : ℝ) := by
          rw [Real.rpow_one]
        _ = ‖f x‖ ^ ((1 : ℝ) + 3) := by rw [← Real.rpow_add hpos]
        _ = ‖f x‖ ^ (4 : ℝ) := by norm_num
  have hfour : Integrable (fun x => ‖f x‖ ^ (4 : ℝ)) μ := by
    apply hint.norm.congr
    filter_upwards [] with x
    exact hpoint x
  have h4 := (integrable_norm_rpow_iff hf2.aestronglyMeasurable
    (by norm_num : ENNReal.ofReal (4 : ℝ) ≠ 0)
    (by norm_num : ENNReal.ofReal (4 : ℝ) ≠ ⊤)).mp ?_
  · exact h4
  · simpa using hfour

private theorem associatedPressureTensor_slice_memLp_two
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∀ i j : Fin 3,
      MemLp (fun x : Vec3 => associatedPressureTensor T u i j (x, t)) 2 volume := by
  classical
  rcases hLH with ⟨hT, ha, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  let Q : Set ParabolicPoint := spaceTimeSet Set.univ (Ioo 0 T)
  have huProd : AEStronglyMeasurable u
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact huMeas
  have hDuProd : AEStronglyMeasurable Du
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact hDuMeas
  have hDuLT : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    exact lt_of_le_of_lt (lintegral_mono fun _ => le_add_left le_rfl) hJointTop
  have hDuSq : Integrable (fun z => (‖Du z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict Q) :=
    associatedPressure_integrable_sq_of_lintegral_lt_top hDuMeas hDuLT
  have hDuSqProd : Integrable (fun z => (‖Du z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact hDuSq
  have hDuSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => Du (x, t)) 2 volume := by
    filter_upwards [hDuProd.prodMk_right, hDuSqProd.prod_left_ae]
      with t hmeas hsquare
    have hmeasVolume : AEStronglyMeasurable (fun x : Vec3 => Du (x, t)) volume := by
      simpa only [Measure.restrict_univ] using hmeas
    have hsquareVolume : Integrable (fun x : Vec3 => (‖Du (x, t)‖ : ℝ) ^ (2 : ℕ)) volume := by
      simpa only [Measure.restrict_univ] using hsquare
    exact (memLp_two_iff_integrable_sq_norm hmeasVolume).2 hsquareVolume
  have huSliceMeas : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume :=
    by
      filter_upwards [huProd.prodMk_right] with t hmeas
      simpa only [Measure.restrict_univ] using hmeas
  have huSliceFinite : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ)) < ⊤ := by
    filter_upwards [ae_le_essSup (f :=
      fun t : ℝ => ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ))] with t ht
    exact lt_of_le_of_lt ht hSliceTop
  have huSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => u (x, t)) 2 volume := by
    filter_upwards [huSliceMeas, huSliceFinite] with t hmeas hfinite
    exact associatedPressure_memLp_two_of_lintegral_lt_top hmeas hfinite
  have hweakSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∀ i : Fin 3, HasWeakGradientOn Set.univ
        (fun x : Vec3 => u (x, t) i) (fun x : Vec3 => Du (x, t) i) := hWeakGrad
  filter_upwards [huSlice, hDuSlice, hweakSlice,
    ae_restrict_mem measurableSet_Ioo] with t hu2 hDu2 hweak ht
  intro i j
  have hui2 : MemLp (fun x : Vec3 => u (x, t) i) 2 volume :=
    (memLp_pi_iff.mp hu2) i
  have hDui2 : MemLp (fun x : Vec3 => Du (x, t) i) 2 volume :=
    (memLp_pi_iff.mp hDu2) i
  let hH1 : H1Function (Set.univ : Set Vec3) := by
    refine ⟨(fun x : Vec3 => u (x, t) i), (fun x : Vec3 => Du (x, t) i), ?_, ?_, hweak i⟩
    · simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hui2
    · intro k
      simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
        Measure.restrict_univ] using (memLp_pi_iff.mp hDui2) k
  have h6 : MemLp (fun x : Vec3 => u (x, t) i)
      (ENNReal.ofReal (6 : ℝ)) volume := by
    rw [memLp_iff]
    have hSob := (Classical.choose_spec CKN.sobolev_L6_global).2 hH1
    have hGrad : MemLp hH1.grad 2 volume := by
      apply memLp_pi_iff.mpr
      intro k
      simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
        Measure.restrict_univ] using hH1.gradMemL2 k
    have hBound : eLpNorm hH1.toFun (ENNReal.ofReal (6 : ℝ)) volume ≤
        gagliardoNirenbergSobolevConstant * eLpNorm hH1.grad 2 volume := by
      simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
        CKN.weakGradientLpNormOn, CKN.MemLpOn, CKN.volumeOn,
        Measure.restrict_univ] using hSob
    have hCtop : gagliardoNirenbergSobolevConstant < ⊤ := by
      dsimp [gagliardoNirenbergSobolevConstant]
      exact lt_top_iff_ne_top.mpr (Classical.choose_spec CKN.sobolev_L6_global).1
    have hBoundTop : eLpNorm hH1.toFun (ENNReal.ofReal (6 : ℝ)) volume < ⊤ :=
      lt_of_le_of_lt hBound (ENNReal.mul_lt_top hCtop hGrad.eLpNorm_lt_top)
    have hH1fun : hH1.toFun = fun x : Vec3 => u (x, t) i := rfl
    simpa only [hH1fun] using hBoundTop
  have hui4 := associatedPressure_memLp_four_of_memLp_two_six hui2 h6
  have huj2 : MemLp (fun x : Vec3 => u (x, t) j) 2 volume :=
    (memLp_pi_iff.mp hu2) j
  have hDuj2 : MemLp (fun x : Vec3 => Du (x, t) j) 2 volume :=
    (memLp_pi_iff.mp hDu2) j
  have huj6 : MemLp (fun x : Vec3 => u (x, t) j)
      (ENNReal.ofReal (6 : ℝ)) volume := by
    let hH1j : H1Function (Set.univ : Set Vec3) := by
      refine ⟨(fun x : Vec3 => u (x, t) j), (fun x : Vec3 => Du (x, t) j), ?_, ?_, hweak j⟩
      · simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using huj2
      · intro k
        simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using (memLp_pi_iff.mp hDuj2) k
    rw [memLp_iff]
    have hSob := (Classical.choose_spec CKN.sobolev_L6_global).2 hH1j
    have hGrad : MemLp hH1j.grad 2 volume := by
      apply memLp_pi_iff.mpr
      intro k
      simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
        Measure.restrict_univ] using hH1j.gradMemL2 k
    have hBound : eLpNorm hH1j.toFun (ENNReal.ofReal (6 : ℝ)) volume ≤
        gagliardoNirenbergSobolevConstant * eLpNorm hH1j.grad 2 volume := by
      simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
        CKN.weakGradientLpNormOn, CKN.MemLpOn, CKN.volumeOn,
        Measure.restrict_univ] using hSob
    have hCtop : gagliardoNirenbergSobolevConstant < ⊤ := by
      dsimp [gagliardoNirenbergSobolevConstant]
      exact lt_top_iff_ne_top.mpr (Classical.choose_spec CKN.sobolev_L6_global).1
    have hBoundTop : eLpNorm hH1j.toFun (ENNReal.ofReal (6 : ℝ)) volume < ⊤ :=
      lt_of_le_of_lt hBound (ENNReal.mul_lt_top hCtop hGrad.eLpNorm_lt_top)
    have hH1jfun : hH1j.toFun = fun x : Vec3 => u (x, t) j := rfl
    simpa only [hH1jfun] using hBoundTop
  have huj4 := associatedPressure_memLp_four_of_memLp_two_six huj2 huj6
  have : ENNReal.HolderTriple (ENNReal.ofReal (4 : ℝ))
      (ENNReal.ofReal (4 : ℝ)) (ENNReal.ofReal (2 : ℝ)) := by
    have h : Real.HolderTriple (4 : ℝ) 4 2 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    exact h.ennrealOfReal
  have hproduct : MemLp (fun x : Vec3 => u (x, t) i * u (x, t) j)
      (ENNReal.ofReal (2 : ℝ)) volume := hui4.mul huj4
  have hinput : (fun x : Vec3 => associatedPressureTensor T u i j (x, t)) =ᵐ[volume]
      fun x : Vec3 => u (x, t) i * u (x, t) j := by
    filter_upwards [] with x
    have hxmem : (x, t) ∈ parabolicHomeomorph.symm ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
      change (x, t) ∈ (Set.univ : Set Vec3) ×ˢ Ioo 0 T
      exact ⟨Set.mem_univ _, ht⟩
    simp [associatedPressureTensor, parabolicHomeomorph_symm_apply, hxmem]
  have hproduct' : MemLp (fun x : Vec3 => u (x, t) i * u (x, t) j) 2 volume := by
    simpa using hproduct
  exact (memLp_congr_ae hinput).2 hproduct'

private theorem associatedPressure_memLp_three_of_lintegral_lt_top
    {α : Type} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hfin : (∫⁻ x, ‖f x‖ₑ ^ (3 : ℝ) ∂μ) < ⊤) :
    MemLp f (ENNReal.ofReal (3 : ℝ)) μ := by
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3)]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

private theorem associatedPressureVelocity_slice_l3_bound
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {B : ℝ≥0∞}
    (hB : essSup
      (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) ≤ B)
    (hBtop : B < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (3 : ℝ)) volume ≤ B ^ (1 / 3 : ℝ) := by
  have huMeas : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    simpa using hLH.2.2.1
  have huProd : AEStronglyMeasurable u
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact huMeas
  have huSliceMeas : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume := by
    filter_upwards [huProd.prodMk_right] with t hmeas
    simpa only [Measure.restrict_univ] using hmeas
  have hBound : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ)) ≤ B := by
    filter_upwards [ae_le_essSup (f := fun t : ℝ =>
      ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))] with t ht
    exact ht.trans hB
  filter_upwards [huSliceMeas, hBound] with t humeas hbound
  let n : Vec3 → ℝ := fun x => vec3EuclideanNorm (u (x, t))
  have hnmeas : AEStronglyMeasurable n volume :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      humeas
  have hIntEq : (∫⁻ x : Vec3, ‖n x‖ₑ ^ (3 : ℝ)) =
      ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ) := by
    apply lintegral_congr_ae
    filter_upwards [] with x
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  have hIntBound : (∫⁻ x : Vec3, ‖n x‖ₑ ^ (3 : ℝ)) ≤ B := by
    calc
      _ = ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ) := hIntEq
      _ ≤ B := hbound
  have hIntTop : (∫⁻ x : Vec3, ‖n x‖ₑ ^ (3 : ℝ)) < ⊤ :=
    lt_of_le_of_lt hIntBound hBtop
  have hnmem := associatedPressure_memLp_three_of_lintegral_lt_top hnmeas hIntTop
  have hPower : eLpNorm n (ENNReal.ofReal (3 : ℝ)) volume ^ (3 : ℝ) =
      ∫⁻ x : Vec3, ‖n x‖ₑ ^ (3 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) ENNReal.ofReal_ne_top hnmeas,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3),
      ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), ENNReal.rpow_one]
  have hPowerBound : eLpNorm n (ENNReal.ofReal (3 : ℝ)) volume ^ (3 : ℝ) ≤ B := by
    rw [hPower, hIntEq]
    exact hbound
  change eLpNorm n (ENNReal.ofReal (3 : ℝ)) volume ≤ B ^ (1 / 3 : ℝ)
  simpa only [one_div] using
    (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 3)).2 hPowerBound

/-- The selected space-time pressure has the same almost-everywhere spatial
slice as its `L^{3/2}` realization, as required for `thm:assoc-pressure`. -/
theorem associatedPressure_riesz_pressure_slice_cross_exponent
    {T : ℝ} {F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hF5 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hF3 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hF2 : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∀ i j,
      MemLp (fun x : Vec3 => F i j (x, t)) 2 volume) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (fun x : Vec3 => rieszPressureSpaceTime (5 / 3 : ℝ)
        (by norm_num) F hF5 (x, t)) =ᵐ[volume]
      fun x : Vec3 => rieszPressureSpaceTime (3 / 2 : ℝ)
        (by norm_num) F hF3 (x, t) := by
  have hSlice5 := ae_restrict_of_ae (s := Ioo 0 T)
    (rieszPressureSpaceTime_slice_ae_eq
      (r := (5 / 3 : ℝ)) (by norm_num) F hF5)
  have hSlice3 := ae_restrict_of_ae (s := Ioo 0 T)
    (rieszPressureSpaceTime_slice_ae_eq
      (r := (3 / 2 : ℝ)) (by norm_num) F hF3)
  filter_upwards [hSlice5, hSlice3, hF2] with t ⟨hFt5, hP5⟩ ⟨hFt3, hP3⟩ hFt2
  let C5 : PressureTensorLp (5 / 3 : ℝ) := fun i j =>
    (hFt5 i j).toLp (fun x : Vec3 => F i j (x, t))
  let C3 : PressureTensorLp (3 / 2 : ℝ) := fun i j =>
    (hFt3 i j).toLp (fun x : Vec3 => F i j (x, t))
  have hOperatorEq (i j : Fin 3) :
      (fun x : Vec3 => rieszPressureOperator (5 / 3 : ℝ) (by norm_num)
        i j (C5 i j) x) =ᵐ[volume]
      fun x : Vec3 => rieszPressureOperator (3 / 2 : ℝ) (by norm_num)
        i j (C3 i j) x := by
    exact rieszPressureOperator_ae_eq_of_memLp_common
      (5 / 3 : ℝ) (by norm_num) (3 / 2 : ℝ) (by norm_num) i j
      (fun x : Vec3 => F i j (x, t)) (hFt5 i j) (hFt3 i j) (hFt2 i j)
  have hPressureSliceSum (r : ℝ) (hr : 1 < r)
      (C : PressureTensorLp r) :
      (fun x : Vec3 => rieszPressureSlice r hr C x) =ᵐ[volume]
        fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
          rieszPressureOperator r hr i j (C i j) x := by
    let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    let hOp (i j : Fin 3) := rieszPressureOperator r hr i j (C i j)
    have hOuter := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i : Fin 3 => ∑ j : Fin 3, hOp i j)
    have hInner (i : Fin 3) :=
      Lp.coeFn_finsetSum (Finset.univ : Finset (Fin 3)) (hOp i)
    filter_upwards [hOuter, ae_all_iff.2 hInner] with x houter hinner
    dsimp [rieszPressureSlice, hOp]
    have hOuter' :
        (∑ i : Fin 3, ∑ j : Fin 3, rieszPressureOperator r hr i j (C i j) :
          Lp ℝ (ENNReal.ofReal r) volume) x =
        ∑ i : Fin 3, (∑ j : Fin 3,
          rieszPressureOperator r hr i j (C i j) :
            Lp ℝ (ENNReal.ofReal r) volume) x := by
      simpa only [Finset.sum_apply] using houter
    calc
      (∑ i : Fin 3, ∑ j : Fin 3,
          rieszPressureOperator r hr i j (C i j) :
            Lp ℝ (ENNReal.ofReal r) volume) x =
          ∑ i : Fin 3, (∑ j : Fin 3,
            rieszPressureOperator r hr i j (C i j) :
              Lp ℝ (ENNReal.ofReal r) volume) x := hOuter'
      _ = ∑ i : Fin 3, ∑ j : Fin 3, rieszPressureOperator r hr i j (C i j) x := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hinner i
  have hSumEq :
      (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
        rieszPressureOperator (5 / 3 : ℝ) (by norm_num) i j (C5 i j) x) =ᵐ[volume]
      fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
        rieszPressureOperator (3 / 2 : ℝ) (by norm_num) i j (C3 i j) x := by
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hOperatorEq i j]
      with x hEq
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hEq i j
  have hC5 : (fun x : Vec3 => rieszPressureSlice (5 / 3 : ℝ)
      (by norm_num) C5 x) =ᵐ[volume]
      fun x : Vec3 => rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3 x :=
    (hPressureSliceSum (5 / 3 : ℝ) (by norm_num) C5).trans <|
      hSumEq.trans (hPressureSliceSum (3 / 2 : ℝ) (by norm_num) C3).symm
  exact hP5.trans (hC5.trans hP3.symm)

/-- The two space-time pressure exponents select the same function almost
everywhere for the Leray tensor, as required for the gradient-test cancellation
in `thm:assoc-pressure`. -/
theorem associatedPressureForSolution_rieszPressureThreeHalves_ae_eq
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    (fun z : Vec3 × ℝ => rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
      (associatedPressureTensor T u)
      (associatedPressureTensor_memLp_fiveThirds hLH) z) =ᵐ[volume]
    fun z : Vec3 × ℝ => rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (associatedPressureTensor T u)
      (associatedPressureTensor_memLp_threeHalves hLH) z := by
  let F := associatedPressureTensor T u
  have hF5 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    exact associatedPressureTensor_memLp_fiveThirds hLH i j
  have hF3 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    exact associatedPressureTensor_memLp_threeHalves hLH i j
  have hF2 := associatedPressureTensor_slice_memLp_two hLH
  have hCross := associatedPressure_riesz_pressure_slice_cross_exponent hF5 hF3 hF2
  have hCrossGlobal : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo 0 T →
      (fun x : Vec3 => rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        F hF5 (x, t)) =ᵐ[volume]
      fun x : Vec3 => rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        F hF3 (x, t) := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact hCross
  have hSlices5 := rieszPressureSpaceTime_slice_ae_eq
    (5 / 3 : ℝ) (by norm_num) F hF5
  have hSlices3 := rieszPressureSpaceTime_slice_ae_eq
    (3 / 2 : ℝ) (by norm_num) F hF3
  have hSectionEq : ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x : Vec3 => rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        F hF5 (x, t)) =ᵐ[volume]
      fun x : Vec3 => rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        F hF3 (x, t) := by
    filter_upwards [hCrossGlobal, hSlices5, hSlices3]
      with t hInside hSlice5 hSlice3
    by_cases ht : t ∈ Ioo 0 T
    · exact hInside ht
    · obtain ⟨hFt5, hP5⟩ := hSlice5
      obtain ⟨hFt3, hP3⟩ := hSlice3
      have hFzero (i j : Fin 3) :
          (fun x : Vec3 => F i j (x, t)) = fun _ => 0 := by
        funext x
        have hxnot : (x, t) ∉ parabolicHomeomorph.symm ⁻¹'
            spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
          change parabolicHomeomorph.symm (x, t) ∉
            spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
          intro hmem
          change parabolicHomeomorph.symm (x, t) ∈
            (Set.univ : Set Vec3) ×ˢ Ioo 0 T at hmem
          exact ht hmem.2
        simp [F, associatedPressureTensor, hxnot]
      let C5 : PressureTensorLp (5 / 3 : ℝ) := fun i j =>
        (hFt5 i j).toLp (fun x : Vec3 => F i j (x, t))
      let C3 : PressureTensorLp (3 / 2 : ℝ) := fun i j =>
        (hFt3 i j).toLp (fun x : Vec3 => F i j (x, t))
      have hC5zero (i j : Fin 3) : C5 i j = 0 := by
        apply Lp.ext
        filter_upwards [(hFt5 i j).coeFn_toLp] with x hx
        simpa [C5] using hx.trans (congrFun (hFzero i j) x)
      have hC3zero (i j : Fin 3) : C3 i j = 0 := by
        apply Lp.ext
        filter_upwards [(hFt3 i j).coeFn_toLp] with x hx
        simpa [C3] using hx.trans (congrFun (hFzero i j) x)
      have hSlice5zero : rieszPressureSlice (5 / 3 : ℝ) (by norm_num) C5 = 0 := by
        simp [rieszPressureSlice, hC5zero]
      have hSlice3zero : rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3 = 0 := by
        simp [rieszPressureSlice, hC3zero]
      have hOut5 : (fun x : Vec3 => rieszPressureSpaceTime (5 / 3 : ℝ)
          (by norm_num) F hF5 (x, t)) =ᵐ[volume] fun _ => 0 := by
        calc
          _ =ᵐ[volume] fun x : Vec3 => rieszPressureSlice (5 / 3 : ℝ)
              (by norm_num) C5 x := hP5
          _ =ᵐ[volume] fun _ => 0 := by
            simp [hSlice5zero]
      have hOut3 : (fun x : Vec3 => rieszPressureSpaceTime (3 / 2 : ℝ)
          (by norm_num) F hF3 (x, t)) =ᵐ[volume] fun _ => 0 := by
        calc
          _ =ᵐ[volume] fun x : Vec3 => rieszPressureSlice (3 / 2 : ℝ)
              (by norm_num) C3 x := hP3
          _ =ᵐ[volume] fun _ => 0 := by
            simp [hSlice3zero]
      exact hOut5.trans hOut3.symm
  apply ae_eq_of_ae_time_sections
    (rieszPressureSpaceTime_measurable (5 / 3 : ℝ) (by norm_num)
      (associatedPressureTensor T u) hF5)
    (rieszPressureSpaceTime_measurable (3 / 2 : ℝ) (by norm_num)
      (associatedPressureTensor T u) hF3)
    hSectionEq

private theorem associatedPressure_rieszPressure_l3_mixed_bound
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤) :
    essSup
      (fun t : ℝ => ∫⁻ x : Vec3,
        ‖rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
          (associatedPressureTensor T u)
          (associatedPressureTensor_memLp_fiveThirds hLH)
          (x, t)‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤ := by
  let S : ℝ≥0∞ := essSup
    (fun t : ℝ => ∫⁻ x : Vec3,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
    (volume.restrict (Ioo 0 T))
  have hStop : S < ⊤ := by simpa [S] using hL3
  let N : ℝ≥0∞ := S ^ (1 / 3 : ℝ)
  have hNtop : N < ⊤ := by
    dsimp [N]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hStop.ne
  have hF5 : ∀ i j, MemLp (associatedPressureTensor T u i j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    exact associatedPressureTensor_memLp_fiveThirds hLH i j
  have hF3 : ∀ i j, MemLp (associatedPressureTensor T u i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    exact associatedPressureTensor_memLp_threeHalves hLH i j
  have hTensor2 := associatedPressureTensor_slice_memLp_two hLH
  have hCross := associatedPressure_riesz_pressure_slice_cross_exponent
    hF5 hF3 hTensor2
  have hPressure3Slice := ae_restrict_of_ae (s := Ioo 0 T)
    (rieszPressureSpaceTime_slice_ae_eq
      (r := (3 / 2 : ℝ)) (by norm_num) (associatedPressureTensor T u) hF3)
  have hVelocity3 := associatedPressureVelocity_slice_l3_bound hLH
    (B := S) le_rfl hStop
  have huMeas : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    simpa using hLH.2.2.1
  have huProd : AEStronglyMeasurable u
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact huMeas
  have huSliceMeas : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume := by
    filter_upwards [huProd.prodMk_right] with t hmeas
    simpa only [Measure.restrict_univ] using hmeas
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)⟩
  let : ENNReal.HolderTriple (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have h : Real.HolderTriple (3 : ℝ) 3 (3 / 2 : ℝ) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    exact h.ennrealOfReal
  let K : ℝ≥0∞ :=
    (ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
      9 * N.toReal ^ 2)) ^ (3 / 2 : ℝ)
  have hKtop : K < ⊤ := by
    dsimp [K]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      ENNReal.ofReal_lt_top.ne
  have hIntegralBound : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫⁻ x : Vec3,
        ‖rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
          (associatedPressureTensor T u)
          (associatedPressureTensor_memLp_fiveThirds hLH)
          (x, t)‖ₑ ^ (3 / 2 : ℝ)) ≤ K := by
    filter_upwards [hCross, hPressure3Slice, hTensor2, hVelocity3,
      huSliceMeas, ae_restrict_mem measurableSet_Ioo]
      with t hCrossT ⟨hFt3, hP3⟩ hF2 hVel3 humeas ht
    let n : Vec3 → ℝ := fun x => vec3EuclideanNorm (u (x, t))
    have hNBound : eLpNorm n (ENNReal.ofReal (3 : ℝ)) volume ≤ N := by
      change eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (3 : ℝ)) volume ≤ N
      exact hVel3
    have hCoordMeas (i : Fin 3) :
        AEStronglyMeasurable (fun x : Vec3 => u (x, t) i) volume :=
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        humeas
    have hCoordBound (i : Fin 3) :
        eLpNorm (fun x : Vec3 => u (x, t) i)
          (ENNReal.ofReal (3 : ℝ)) volume ≤ N := by
      calc
        eLpNorm (fun x : Vec3 => u (x, t) i)
            (ENNReal.ofReal (3 : ℝ)) volume ≤
          eLpNorm n (ENNReal.ofReal (3 : ℝ)) volume := by
            apply eLpNorm_mono (hCoordMeas i)
            intro x
            rw [Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
            exact abs_apply_le_vec3EuclideanNorm (u (x, t)) i
        _ ≤ N := hNBound
    have hCoord3 (i : Fin 3) : MemLp (fun x : Vec3 => u (x, t) i)
        (ENNReal.ofReal (3 : ℝ)) volume := by
      rw [memLp_iff]
      exact lt_of_le_of_lt (hCoordBound i) hNtop
    have hInputEquality (i j : Fin 3) :
        (fun x : Vec3 => associatedPressureTensor T u i j (x, t)) =ᵐ[volume]
          fun x : Vec3 => u (x, t) i * u (x, t) j := by
      filter_upwards [] with x
      have hxmem : (x, t) ∈ parabolicHomeomorph.symm ⁻¹'
          spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
        change (x, t) ∈ (Set.univ : Set Vec3) ×ˢ Ioo 0 T
        exact ⟨Set.mem_univ _, ht⟩
      simp [associatedPressureTensor, parabolicHomeomorph_symm_apply, hxmem]
    have hProductBound (i j : Fin 3) :
        eLpNorm (fun x : Vec3 => u (x, t) i * u (x, t) j)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ N ^ (2 : ℕ) := by
      have hHolder :
          eLpNorm (fun x : Vec3 => u (x, t) i * u (x, t) j)
              (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
            eLpNorm (fun x : Vec3 => u (x, t) i)
                (ENNReal.ofReal (3 : ℝ)) volume *
              eLpNorm (fun x : Vec3 => u (x, t) j)
                (ENNReal.ofReal (3 : ℝ)) volume := by
        simpa only [ENNReal.coe_one, one_mul] using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
          (p := ENNReal.ofReal (3 : ℝ)) (q := ENNReal.ofReal (3 : ℝ))
          (r := ENNReal.ofReal (3 / 2 : ℝ))
          (fun v w : ℝ => v * w) 1 continuous_mul (hCoordMeas i) (hCoordMeas j)
          (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs]))
      calc
        _ ≤ eLpNorm (fun x : Vec3 => u (x, t) i)
              (ENNReal.ofReal (3 : ℝ)) volume *
            eLpNorm (fun x : Vec3 => u (x, t) j)
              (ENNReal.ofReal (3 : ℝ)) volume := by simpa using hHolder
        _ ≤ N * N := mul_le_mul (hCoordBound i) (hCoordBound j)
            (by positivity) (by positivity)
        _ = N ^ (2 : ℕ) := by rw [pow_two]
    let C3 : PressureTensorLp (3 / 2 : ℝ) := fun i j =>
      (hFt3 i j).toLp (fun x : Vec3 => associatedPressureTensor T u i j (x, t))
    have hC3norm (i j : Fin 3) : ‖C3 i j‖ ≤ N.toReal ^ 2 := by
      rw [Lp.norm_toLp]
      have hRawBound :
          eLpNorm (fun x : Vec3 => associatedPressureTensor T u i j (x, t))
              (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ N ^ (2 : ℕ) := by
        calc
          _ = eLpNorm (fun x : Vec3 => u (x, t) i * u (x, t) j)
                (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
              eLpNorm_congr_ae (hInputEquality i j)
          _ ≤ N ^ (2 : ℕ) := hProductBound i j
      have hN2top : N ^ (2 : ℕ) < ⊤ := by
        simpa [pow_two] using (ENNReal.mul_lt_top hNtop hNtop)
      calc
        _ ≤ (N ^ (2 : ℕ)).toReal := ENNReal.toReal_mono hN2top.ne hRawBound
        _ = N.toReal ^ 2 := by rw [ENNReal.toReal_pow]
    have hCnonneg : 0 ≤ rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) :=
      le_trans (norm_nonneg _) (rieszPressureOperator_norm_le
        (3 / 2 : ℝ) (by norm_num) 0 0)
    have hC3sum : ∑ i : Fin 3, ∑ j : Fin 3, ‖C3 i j‖ ≤
        9 * N.toReal ^ 2 := by
      calc
        _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, N.toReal ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hC3norm i j
        _ = 9 * N.toReal ^ 2 := by
          simp only [Finset.sum_const, Finset.card_fin]
          ring_nf
    have hPressureClassBound :
        ‖rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3‖ ≤
          rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
            (9 * N.toReal ^ 2) := by
      exact (rieszPressureSlice_norm_le
        (3 / 2 : ℝ) (by norm_num) C3).trans
        (mul_le_mul_of_nonneg_left hC3sum hCnonneg)
    let P3 : Vec3 → ℝ := rieszPressureSliceRepresentative
      (3 / 2 : ℝ) (by norm_num) C3
    have hP3rep : (rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3 :
        Vec3 → ℝ) =ᵐ[volume] P3 :=
      rieszPressureSliceRepresentative_ae_eq (3 / 2 : ℝ) (by norm_num) C3
    have hP3mem : MemLp P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      (memLp_congr_ae hP3rep).mp (Lp.memLp
        (rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3))
    have hP3class : hP3mem.toLp P3 = rieszPressureSlice
        (3 / 2 : ℝ) (by norm_num) C3 := by
      apply Lp.ext
      filter_upwards [hP3mem.coeFn_toLp, hP3rep] with x hto hclass
      exact hto.trans hclass.symm
    have hP3eLpNorm : eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
          (9 * N.toReal ^ 2)) := by
      calc
        eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume =
            ENNReal.ofReal ‖hP3mem.toLp P3‖ := by
          calc
            _ = ENNReal.ofReal (eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal :=
              (ENNReal.ofReal_toReal hP3mem.eLpNorm_lt_top.ne).symm
            _ = ENNReal.ofReal ‖hP3mem.toLp P3‖ :=
              congrArg ENNReal.ofReal (Lp.norm_toLp P3 hP3mem).symm
        _ = ENNReal.ofReal ‖rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3‖ :=
          congrArg (fun q : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ))
            (volume : Measure Vec3) => ENNReal.ofReal ‖q‖) hP3class
        _ ≤ ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
            (9 * N.toReal ^ 2)) := ENNReal.ofReal_le_ofReal hPressureClassBound
    have hP3integral :
        (∫⁻ x : Vec3, ‖P3 x‖ₑ ^ (3 / 2 : ℝ)) =
          eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume ^ (3 / 2 : ℝ) := by
      rw [eLpNorm_eq_eLpNorm'
        (by norm_num) ENNReal.ofReal_ne_top hP3mem.aestronglyMeasurable,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      exact lintegral_rpow_enorm_eq_rpow_eLpNorm'
        (f := P3) (μ := volume) (q := (3 / 2 : ℝ)) (by norm_num)
    have hP5toP3 :
        (fun x : Vec3 => rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
          (associatedPressureTensor T u)
          (associatedPressureTensor_memLp_fiveThirds hLH) (x, t)) =ᵐ[volume] P3 :=
      hCrossT.trans (hP3.trans hP3rep)
    calc
      (∫⁻ x : Vec3,
          ‖rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
            (associatedPressureTensor T u)
            (associatedPressureTensor_memLp_fiveThirds hLH) (x, t)‖ₑ ^ (3 / 2 : ℝ)) =
        ∫⁻ x : Vec3, ‖P3 x‖ₑ ^ (3 / 2 : ℝ) := by
          apply lintegral_congr_ae
          filter_upwards [hP5toP3] with x hx
          rw [hx]
      _ = eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume ^ (3 / 2 : ℝ) :=
        hP3integral
      _ ≤ (ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
          (9 * N.toReal ^ 2))) ^ (3 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hP3eLpNorm (by norm_num)
      _ = K := by simp [K, mul_assoc]
  exact lt_of_le_of_lt (essSup_le_of_ae_le K hIntegralBound) hKtop

/-- The selected associated pressure has the conditional mixed norm required
by `thm:assoc-pressure`. -/
theorem associatedPressureForSolution_memLp_mixedThreeHalves
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤) :
    essSup
      (fun t : ℝ => ∫⁻ x : Vec3,
        ‖associatedPressureForSolution hLH (x, t)‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤ := by
  have hpoint (x : Vec3) (t : ℝ) :
      associatedPressureForSolution hLH ((x, t) : ParabolicPoint) =
        rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
          (associatedPressureTensor T u)
          (associatedPressureTensor_memLp_fiveThirds hLH) (x, t) := by
    change (rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
      (associatedPressureTensor T u) (associatedPressureTensor_memLp_fiveThirds hLH)
      (parabolicHomeomorph ((x, t) : ParabolicPoint))) =
        (rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
          (associatedPressureTensor T u)
          (associatedPressureTensor_memLp_fiveThirds hLH) (x, t))
    rfl
  have hfun : (fun t : ℝ => ∫⁻ x : Vec3,
      ‖associatedPressureForSolution hLH (x, t)‖ₑ ^ (3 / 2 : ℝ)) =
    (fun t : ℝ => ∫⁻ x : Vec3,
      ‖rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_fiveThirds hLH) (x, t)‖ₑ ^ (3 / 2 : ℝ)) := by
    funext t
    apply lintegral_congr_ae
    filter_upwards [] with x
    rw [hpoint]
  rw [hfun]
  exact associatedPressure_rieszPressure_l3_mixed_bound hLH hL3

end CKN.Leray

end
