/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.TenThirds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Serrin Estimate

The weak derivative identity is stable under subtraction of `L²` fields.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


namespace ESS

/-- The weak derivative identity is stable under subtraction of `L²` fields. -/
theorem serrin_weakPartialDeriv_sub
    {f g df dg : Vec3 → ℝ} {i : Fin 3}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hdf : MemLp df 2 volume) (hdg : MemLp dg 2 volume)
    (hF : HasWeakPartialDerivOn (Set.univ : Set Vec3) i f df)
    (hG : HasWeakPartialDerivOn (Set.univ : Set Vec3) i g dg) :
    HasWeakPartialDerivOn (Set.univ : Set Vec3) i (f - g) (df - dg) := by
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ENNReal.HolderConjugate.instTwoTwo
  intro φ hφsmooth hφcompact hφsupport
  let ei : Vec3 := CKN.basisVec i
  let dφ : Vec3 → ℝ := fun x => (fderiv ℝ φ x) ei
  have hdφsmooth : ContDiff ℝ (⊤ : ℕ∞) dφ := by
    change ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv φ i)
    exact CKN.contDiff_spatialDeriv_smooth hφsmooth i
  have hdφcompact : HasCompactSupport dφ := by
    simpa [dφ, ei] using hφcompact.fderiv_apply (𝕜 := ℝ) ei
  have hdφLp : MemLp dφ 2 volume :=
    hdφsmooth.continuous.memLp_of_hasCompactSupport hdφcompact
  have hφLp : MemLp φ 2 volume := hφsmooth.continuous.memLp_of_hasCompactSupport hφcompact
  have hFint : Integrable (fun x => f x * dφ x) volume := hf.integrable_mul hdφLp
  have hGint : Integrable (fun x => g x * dφ x) volume := hg.integrable_mul hdφLp
  have hdfint : Integrable (fun x => df x * φ x) volume := hdf.integrable_mul hφLp
  have hdgint : Integrable (fun x => dg x * φ x) volume := hdg.integrable_mul hφLp
  have hFid := hF φ hφsmooth hφcompact hφsupport
  have hGid := hG φ hφsmooth hφcompact hφsupport
  have hFid' : ∫ x, f x * dφ x = -∫ x, df x * φ x := by
    simpa only [dφ, ei, MeasureTheory.setIntegral_univ] using hFid
  have hGid' : ∫ x, g x * dφ x = -∫ x, dg x * φ x := by
    simpa only [dφ, ei, MeasureTheory.setIntegral_univ] using hGid
  have hsub :
      ∫ x, (f x - g x) * dφ x = -∫ x, (df x - dg x) * φ x := by
    calc
      ∫ x, (f x - g x) * dφ x =
          (∫ x, f x * dφ x) - ∫ x, g x * dφ x := by
            rw [← integral_sub hFint hGint]
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = (-∫ x, df x * φ x) - (-∫ x, dg x * φ x) := by rw [hFid', hGid']
      _ = -∫ x, (df x - dg x) * φ x := by
            have hR : ∫ x, (df x - dg x) * φ x =
                (∫ x, df x * φ x) - ∫ x, dg x * φ x := by
              rw [← integral_sub hdfint hdgint]
              apply integral_congr_ae
              filter_upwards [] with x
              ring
            rw [hR]
            ring
  simpa [dφ, ei, MeasureTheory.setIntegral_univ] using hsub

private theorem serrin_memLp_two_of_lintegral_lt_top
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ)
    (hlt : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) < ⊤) :
    MemLp f 2 μ := by
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne

private theorem serrin_integrable_sq_of_lintegral_lt_top
    {E : Type} [NormedAddCommGroup E] {S : Set ParabolicPoint}
    {f : ParabolicPoint → E}
    (hf : AEStronglyMeasurable f (volume.restrict S))
    (hlt : (∫⁻ z in S, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖f z‖ : ℝ) ^ (2 : ℕ)) (volume.restrict S) := by
  have hfmeas : AEStronglyMeasurable (fun z => (‖f z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict S) := hf.norm.pow 2
  have hfintTop : (∫⁻ z in S,
      ENNReal.ofReal ((‖f z‖ : ℝ) ^ (2 : ℕ))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_)) hlt)
    filter_upwards [] with z
    calc
      ENNReal.ofReal ((‖f z‖ : ℝ) ^ (2 : ℕ)) =
          ENNReal.ofReal ((‖f z‖ : ℝ) ^ (2 : ℝ)) := by norm_num [Real.rpow_natCast]
      _ = ENNReal.ofReal ‖f z‖ ^ (2 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
      _ = ‖f z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
  exact (lintegral_ofReal_ne_top_iff_integrable hfmeas
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hfintTop

/-- Almost every time slice of a Leray–Hopf field and its weak gradient are
square-integrable. -/
theorem serrin_slice_memLp_two_ae
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      MemLp (fun x : Vec3 => u (x, s)) 2 volume ∧
      MemLp (fun x : Vec3 => Du (x, s)) 2 volume := by
  rcases hLH with ⟨_hT, _, huMeas, hDuMeas, _, hJoint, _, _, _, _, _, _⟩
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have huLT : (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    exact lt_of_le_of_lt (lintegral_mono fun _ => le_add_right le_rfl) hJoint
  have hDuLT : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    exact lt_of_le_of_lt (lintegral_mono fun _ => le_add_left le_rfl) hJoint
  have hu2 : MemLp u 2 (volume.restrict Q) :=
    serrin_memLp_two_of_lintegral_lt_top huMeas huLT
  have hDu2 : MemLp Du 2 (volume.restrict Q) :=
    serrin_memLp_two_of_lintegral_lt_top hDuMeas hDuLT
  have huSq : Integrable (fun z => (‖u z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact serrin_integrable_sq_of_lintegral_lt_top huMeas huLT
  have hDuSq : Integrable (fun z => (‖Du z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact serrin_integrable_sq_of_lintegral_lt_top hDuMeas hDuLT
  have huMeasProd : AEStronglyMeasurable u
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))]
    exact huMeas
  have hDuMeasProd : AEStronglyMeasurable Du
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))]
    exact hDuMeas
  filter_upwards [huMeasProd.prodMk_right, hDuMeasProd.prodMk_right,
    huSq.prod_left_ae, hDuSq.prod_left_ae] with s hus hDus husq hDusq
  exact ⟨by
      simpa [Measure.restrict_univ] using (memLp_two_iff_integrable_sq_norm hus).2 husq,
    by
      simpa [Measure.restrict_univ] using (memLp_two_iff_integrable_sq_norm hDus).2 hDusq⟩

/-- Young's inequality in the exponents used in the relative-energy estimate
for `lem:pv-serrin-uniqueness`. -/
theorem serrin_trilinear_young {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    A * B ^ (2 / 5 : ℝ) * C ^ (8 / 5 : ℝ) ≤
      (1 / 2 : ℝ) * C ^ 2 + (32 / 5 : ℝ) * A ^ 5 * B ^ 2 := by
  let x : ℝ := (1 / 2 : ℝ) * C ^ (8 / 5 : ℝ)
  let y : ℝ := 2 * A * B ^ (2 / 5 : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hpq : (5 / 4 : ℝ).HolderConjugate 5 := by
    refine ⟨?_, by norm_num, by norm_num⟩
    norm_num
  have hYoung := Real.young_inequality_of_nonneg hx hy hpq
  have hCmul : (C ^ (8 / 5 : ℝ)) ^ (5 / 4 : ℝ) = C ^ (2 : ℕ) := by
    calc
      (C ^ (8 / 5 : ℝ)) ^ (5 / 4 : ℝ) = C ^ (2 : ℝ) := by
        rw [← Real.rpow_mul hC (8 / 5 : ℝ) (5 / 4 : ℝ)]
        norm_num
      _ = C ^ (2 : ℕ) := Real.rpow_natCast C 2
  have hhalf : (1 / 2 : ℝ) ^ (5 / 4 : ℝ) ≤ 1 / 2 := by
    calc
      (1 / 2 : ℝ) ^ (5 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ = 1 / 2 := by rw [Real.rpow_one]
  have hfirst : x ^ (5 / 4 : ℝ) / (5 / 4 : ℝ) ≤ (1 / 2 : ℝ) * C ^ 2 := by
    have hcoef : (1 / 2 : ℝ) ^ (5 / 4 : ℝ) / (5 / 4 : ℝ) ≤ 1 / 2 := by
      calc
        (1 / 2 : ℝ) ^ (5 / 4 : ℝ) / (5 / 4 : ℝ) ≤
            (1 / 2 : ℝ) / (5 / 4 : ℝ) := by gcongr
        _ ≤ 1 / 2 := by norm_num
    calc
      x ^ (5 / 4 : ℝ) / (5 / 4 : ℝ) =
          ((1 / 2 : ℝ) ^ (5 / 4 : ℝ) / (5 / 4 : ℝ)) * C ^ 2 := by
        rw [show x = (1 / 2 : ℝ) * C ^ (8 / 5 : ℝ) by rfl,
          Real.mul_rpow (by norm_num) (Real.rpow_nonneg hC _), hCmul]
        ring_nf
      _ ≤ (1 / 2 : ℝ) * C ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg C)
  have hBmul : (B ^ (2 / 5 : ℝ)) ^ (5 : ℝ) = B ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hB (2 / 5 : ℝ) 5]
    norm_num
  have hsecond : y ^ (5 : ℝ) / 5 ≤ (32 / 5 : ℝ) * A ^ 5 * B ^ 2 := by
    rw [show y = 2 * A * B ^ (2 / 5 : ℝ) by rfl,
      Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) * A) (Real.rpow_nonneg hB _),
      Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hA, hBmul]
    norm_num
    ring_nf
    exact le_rfl
  calc
    A * B ^ (2 / 5 : ℝ) * C ^ (8 / 5 : ℝ) = x * y := by
      dsimp [x, y]
      ring
    _ ≤ x ^ (5 / 4 : ℝ) / (5 / 4 : ℝ) + y ^ (5 : ℝ) / 5 := hYoung
    _ ≤ (1 / 2 : ℝ) * C ^ 2 + (32 / 5 : ℝ) * A ^ 5 * B ^ 2 :=
      add_le_add hfirst hsecond

/-- The spatial interpolation bound and Young's inequality give the
integrable-coefficient estimate used in the zero-start comparison in
`lem:pv-serrin-uniqueness`. -/
theorem serrin_interpolation_young {K A B D N : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hN : N ≤ K * B ^ (2 / 5 : ℝ) * D ^ (3 / 5 : ℝ)) :
    A * N * D ≤ (1 / 2 : ℝ) * D ^ 2 +
      (32 / 5 : ℝ) * (K * A) ^ 5 * B ^ 2 := by
  have hscale : A * N * D ≤ (K * A) * B ^ (2 / 5 : ℝ) *
      D ^ (8 / 5 : ℝ) := by
    calc
      A * N * D = (A * N) * D := by ring
      _ ≤ (A * (K * B ^ (2 / 5 : ℝ) * D ^ (3 / 5 : ℝ))) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hA) hD
      _ = (K * A) * B ^ (2 / 5 : ℝ) * D ^ (8 / 5 : ℝ) := by
        by_cases hDpos : D = 0
        · simp [hDpos]
        · have hDgt : 0 < D := lt_of_le_of_ne hD (Ne.symm hDpos)
          have hrpow : D ^ (3 / 5 : ℝ) * D = D ^ (8 / 5 : ℝ) := by
            calc
              D ^ (3 / 5 : ℝ) * D =
                  D ^ (3 / 5 : ℝ) * D ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = D ^ ((3 / 5 : ℝ) + 1) := (Real.rpow_add hDgt _ _).symm
              _ = D ^ (8 / 5 : ℝ) := by norm_num
          calc
            A * (K * B ^ (2 / 5 : ℝ) * D ^ (3 / 5 : ℝ)) * D =
                (K * A) * B ^ (2 / 5 : ℝ) * (D ^ (3 / 5 : ℝ) * D) := by ring
            _ = (K * A) * B ^ (2 / 5 : ℝ) * D ^ (8 / 5 : ℝ) := by rw [hrpow]
  have hYoung := serrin_trilinear_young (mul_nonneg hK hA) hB hD
  exact hscale.trans hYoung

/-- Vector-valued spatial interpolation from componentwise `H¹` data. The
finite-dimensional constant is kept explicit for use in the cross-testing
estimate in `lem:pv-serrin-uniqueness`. -/
theorem serrin_vector_spatial_tenThirds
    {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (hw2 : MemLp w 2 volume)
    (hH1 : ∀ _i : Fin 3, H1Function (Set.univ : Set Vec3))
    (hFun : ∀ i : Fin 3, (hH1 i).toFun = fun x => w x i)
    (hGrad : ∀ i : Fin 3, (hH1 i).grad = fun x j => Dw x i j) :
    eLpNorm w (ENNReal.ofReal (10 / 3 : ℝ)) volume ≤
      3 * gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
        (2 : ℝ≥0∞) ^ (3 / 5 : ℝ) *
        eLpNorm w 2 volume ^ (2 / 5 : ℝ) *
          eLpNorm Dw 2 volume ^ (3 / 5 : ℝ) := by
  let p : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  let Wsum : Vec3 → ℝ := fun x => ∑ i : Fin 3, |w x i|
  have hWsumNonneg (x : Vec3) : 0 ≤ Wsum x := by
    dsimp [Wsum]
    positivity
  have hwBound (x : Vec3) : ‖w x‖ ≤ Wsum x := by
    apply (pi_norm_le_iff_of_nonneg (hWsumNonneg x)).2
    intro i
    dsimp [Wsum]
    calc
      ‖w x i‖ = |w x i| := Real.norm_eq_abs _
      _ ≤ ∑ j : Fin 3, |w x j| :=
        Finset.single_le_sum (fun j _hj => abs_nonneg (w x j)) (Finset.mem_univ i)
  have hvectorLe : eLpNorm w p volume ≤ eLpNorm Wsum p volume :=
    eLpNorm_mono_ae_real hw2.aestronglyMeasurable (Filter.Eventually.of_forall hwBound)
  have hsumLp : eLpNorm Wsum p volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => |w x i|) p volume := by
    have hsumEq : Wsum = ∑ i : Fin 3, (fun x : Vec3 => |w x i|) := by
      funext x
      rfl
    rw [hsumEq]
    exact eLpNorm_sum_le (μ := volume) (p := p) (f := fun i x => |w x i|)
      (s := Finset.univ) (by norm_num [p] : (1 : ℝ≥0∞) ≤ p)
  have hsumLp' : eLpNorm Wsum p volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => w x i) p volume := by
    refine hsumLp.trans ?_
    apply Finset.sum_le_sum
    intro i hi
    have hcoord : AEStronglyMeasurable (fun x => w x i) volume :=
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        hw2.aestronglyMeasurable
    have heq := eLpNorm_congr_norm_ae (p := p)
      (continuous_abs.comp_aestronglyMeasurable hcoord)
      hcoord
      (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
    exact le_of_eq heq
  have hrow2 (i : Fin 3) :
      eLpNorm (hH1 i).toFun 2 volume ≤ eLpNorm w 2 volume := by
    have hrow := eLpNorm_mono_ae ((hH1 i).memL2.aestronglyMeasurable)
      (μ := CKN.volumeOn (Set.univ : Set Vec3)) (p := (2 : ℝ≥0∞))
      (Filter.Eventually.of_forall fun x => by
        simpa only [hFun i] using norm_le_pi_norm (w x) i)
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hrow
  have hrowGrad (i : Fin 3) :
      eLpNorm (fun x => vec3EuclideanNorm ((hH1 i).grad x)) 2 volume ≤
        (2 : ℝ≥0∞) * eLpNorm Dw 2 volume := by
    have hrowGradLp : MemLp (hH1 i).grad 2 volume := by
      apply (memLp_pi_iff).2
      intro j
      simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
        (hH1 i).gradMemL2 j
    have hmeas : AEStronglyMeasurable
        (fun x => vec3EuclideanNorm ((hH1 i).grad x)) volume := by
      exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        hrowGradLp.aestronglyMeasurable
    have hpoint : ∀ᵐ (x : Vec3) ∂volume,
        ‖vec3EuclideanNorm ((hH1 i).grad x)‖ ≤ 2 * ‖Dw x‖ := by
      filter_upwards [] with x
      rw [hGrad i]
      have hrow : ‖(fun j => Dw x i j : Vec3)‖ ≤ ‖Dw x‖ :=
        norm_le_pi_norm (Dw x) i
      have hroot : Real.sqrt 3 ≤ 2 := by
        nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg 3]
      have hreal : vec3EuclideanNorm (fun j => Dw x i j) ≤ 2 * ‖Dw x‖ := by
        calc
          vec3EuclideanNorm (fun j => Dw x i j) ≤
              Real.sqrt 3 * ‖(fun j => Dw x i j : Vec3)‖ :=
            vec3EuclideanNorm_le_sqrt_three_mul_norm _
          _ ≤ Real.sqrt 3 * ‖Dw x‖ :=
            mul_le_mul_of_nonneg_left hrow (Real.sqrt_nonneg 3)
          _ ≤ 2 * ‖Dw x‖ :=
            mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact hreal
    have hmulRaw := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hpoint
      (2 : ℝ≥0∞)
    simpa using hmulRaw
  have hrowLp (i : Fin 3) :
      eLpNorm (fun x => w x i) p volume ≤
        gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
          eLpNorm w 2 volume ^ (2 / 5 : ℝ) *
            (2 * eLpNorm Dw 2 volume) ^
              (3 / 5 : ℝ) := by
    have hgn := h1_gagliardoNirenberg_tenThirds (hH1 i)
    calc
      eLpNorm (fun x => w x i) p volume =
          eLpNorm (hH1 i).toFun p volume := by rw [hFun i]
      _ ≤ gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
            eLpNorm (hH1 i).toFun 2 volume ^ (2 / 5 : ℝ) *
              eLpNorm (fun x => vec3EuclideanNorm ((hH1 i).grad x)) 2 volume ^
                (3 / 5 : ℝ) := by
          simpa [p] using hgn
      _ ≤ gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
            eLpNorm w 2 volume ^ (2 / 5 : ℝ) *
              (2 * eLpNorm Dw 2 volume) ^
                (3 / 5 : ℝ) := by
          gcongr
          · exact hrow2 i
          · exact hrowGrad i
  have hrowLp' (i : Fin 3) :
      eLpNorm (fun x => w x i) p volume ≤
        gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
          (2 : ℝ≥0∞) ^ (3 / 5 : ℝ) *
          eLpNorm w 2 volume ^ (2 / 5 : ℝ) *
            eLpNorm Dw 2 volume ^ (3 / 5 : ℝ) := by
    calc
      _ ≤ gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
            eLpNorm w 2 volume ^ (2 / 5 : ℝ) *
              (2 * eLpNorm Dw 2 volume) ^
                (3 / 5 : ℝ) := hrowLp i
      _ = gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
            (2 : ℝ≥0∞) ^ (3 / 5 : ℝ) *
            eLpNorm w 2 volume ^ (2 / 5 : ℝ) *
              eLpNorm Dw 2 volume ^ (3 / 5 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 5)]
        ac_rfl
  calc
    eLpNorm w p volume ≤ eLpNorm Wsum p volume := hvectorLe
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => w x i) p volume := hsumLp'
    _ ≤ ∑ _i : Fin 3,
          gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
            (2 : ℝ≥0∞) ^ (3 / 5 : ℝ) *
              eLpNorm w 2 volume ^ (2 / 5 : ℝ) *
                eLpNorm Dw 2 volume ^ (3 / 5 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hrowLp' i
    _ = 3 * gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
          (2 : ℝ≥0∞) ^ (3 / 5 : ℝ) *
          eLpNorm w 2 volume ^ (2 / 5 : ℝ) *
            eLpNorm Dw 2 volume ^ (3 / 5 : ℝ) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring

/-- The strong initial trace of a Leray--Hopf field gives convergence of its
spatial `L²` distance to the datum along almost every time. -/
theorem serrin_difference_initial_trace_l2_ae
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hU : IsLerayHopfSolution T a u Du) :
    Tendsto
      (fun t : ℝ => eLpNorm (fun x : Vec3 => u (x, t) - a x) 2 volume)
      (nhdsWithin 0 (Ioi 0) ⊓ ae (volume.restrict (Ioo 0 T))) (nhds 0) := by
  rcases hU with ⟨hT, hJ, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, hDiv, hWeakCont, hMomentum, hEnergy, hTrace⟩
  have hSlices := serrin_slice_memLp_two_ae
    (T := T) (a := a) (u := u) (Du := Du)
      ⟨hT, hJ, huMeas, hDuMeas, hSliceTop, hJointTop,
        hWeakGrad, hDiv, hWeakCont, hMomentum, hEnergy, hTrace⟩
  have hTrace' : Tendsto
      (fun t : ℝ => (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t) - a x)) ^ (2 : ℝ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    exact hTrace
  let l := nhdsWithin 0 (Ioi 0) ⊓ ae (volume.restrict (Ioo 0 T))
  have hTraceInf : Tendsto
      (fun t : ℝ => (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t) - a x)) ^ (2 : ℝ)))
      l (nhds 0) := hTrace'.mono_left inf_le_left
  have hRoot : Tendsto
      (fun t : ℝ => (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t) - a x)) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ)) l (nhds 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto
      (0 : ℝ≥0∞) |>.comp hTraceInf
    convert h using 1 <;> simp [Function.comp_def]
  have hBound : ∀ᶠ t in l,
      eLpNorm (fun x : Vec3 => u (x, t) - a x) 2 volume ≤
        (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t) - a x)) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) := by
    have hSliceMem : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
        MemLp (fun x : Vec3 => u (x, t) - a x) 2 volume := by
      filter_upwards [hSlices] with t ht
      have ha2 : MemLp a 2 volume := hJ.1
      exact ht.1.sub ha2
    have hSliceMemL : ∀ᶠ t in l,
        MemLp (fun x : Vec3 => u (x, t) - a x) 2 volume :=
      hSliceMem.filter_mono inf_le_right
    filter_upwards [hSliceMemL] with t ht
    let g : Vec3 → ℝ := fun x => vec3EuclideanNorm (u (x, t) - a x)
    have hg : AEStronglyMeasurable g volume :=
      continuous_vec3EuclideanNorm.comp_aestronglyMeasurable ht.aestronglyMeasurable
    have hNorm : eLpNorm (fun x : Vec3 => u (x, t) - a x) 2 volume ≤
        eLpNorm g 2 volume := by
      apply eLpNorm_mono_ae_real ht.aestronglyMeasurable
      filter_upwards [] with x
      exact norm_le_vec3EuclideanNorm (u (x, t) - a x)
    have hENorm : eLpNorm g 2 volume =
        (∫⁻ x : Vec3, ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) (by norm_num) hg]
      norm_num
    have hIntegrand : (fun x : Vec3 => ‖g x‖ₑ ^ (2 : ℝ)) =ᵐ[volume]
        (fun x => ENNReal.ofReal (vec3EuclideanNorm (u (x, t) - a x)) ^ (2 : ℝ)) := by
      filter_upwards [] with x
      change ‖vec3EuclideanNorm (u (x, t) - a x)‖ₑ ^ (2 : ℝ) = _
      rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
    calc
      _ ≤ eLpNorm g 2 volume := hNorm
      _ = (∫⁻ x : Vec3, ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hENorm
      _ = (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t) - a x)) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by rw [lintegral_congr_ae hIntegrand]
  have hnonneg : ∀ᶠ t in l,
      0 ≤ eLpNorm (fun x : Vec3 => u (x, t) - a x) 2 volume :=
    Filter.Eventually.of_forall fun _ => bot_le
  have hresult := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hRoot hnonneg hBound
  exact hresult

end ESS
