/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExtSobolevBallTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Setting.VectorNormAggregation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Energy interpolation for Leray--Hopf fields

The spatial and space-time interpolation estimates are the energy interpolation
used in `lem:u-ten-thirds` and `eq:gn-ten-thirds`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem memLp_two_of_lintegral_lt_top
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {v : α → E}
    (hv : AEStronglyMeasurable v μ)
    (hlt : (∫⁻ z, ‖v z‖ₑ ^ (2 : ℝ) ∂μ) < ⊤) :
    MemLp v 2 μ := by
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hv]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne

private theorem integrable_sq_of_lintegral_lt_top
    {E : Type} [NormedAddCommGroup E] {S : Set ParabolicPoint}
    {v : ParabolicPoint → E}
    (hv : AEStronglyMeasurable v (volume.restrict S))
    (hvlt : (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ)) (volume.restrict S) := by
  have hvmeas : AEStronglyMeasurable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict S) := hv.norm.pow 2
  have hvfin : (∫⁻ z in S, ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_)) hvlt)
    filter_upwards [] with z
    calc
      ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ))
          = ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℝ)) := by
              norm_num [Real.rpow_natCast]
      _ = ENNReal.ofReal ‖v z‖ ^ (2 : ℝ) :=
            (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
      _ = ‖v z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
  exact (lintegral_ofReal_ne_top_iff_integrable hvmeas
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hvfin

private theorem enorm_apply_le (v : Vec3) (i : Fin 3) :
    ‖v i‖ₑ ≤ ‖v‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm v i)

private theorem eLpNorm_two_sq_eq_lintegral
    {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (2 : ℝ≥0∞) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  norm_num

private theorem eLpNorm_tenThirds_pow_eq_lintegral
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (10 / 3 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (10 / 3 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : ENNReal.ofReal (10 / 3 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3),
    ← ENNReal.rpow_mul]
  norm_num

private theorem memLp_ofReal_of_lintegral_lt_top
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ} (hp : 0 < p) {f : α → E}
    (hf : AEStronglyMeasurable f μ)
    (hlt : (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) < ⊤) :
    MemLp f (ENNReal.ofReal p) μ := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hlt.ne

/-- The Sobolev constant chosen from the ball-time interpolation estimate. -/
@[expose]
noncomputable def energyInterpolationSobolevConstant : ℝ :=
  Classical.choose CKN.ball_time_sobolev

private theorem component_gradient_sq_le_spatialGradientSq
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (z : ParabolicPoint) (i : Fin 3) :
    vec3EuclideanNorm (Du z i) ^ (2 : ℕ) ≤ spatialGradientSq u Du z := by
  rw [vec3EuclideanNorm, Real.sq_sqrt
    (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (Du z i j)),
    spatialGradientSq]
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg (Du z k j))
    (Finset.mem_univ i)

private theorem spatialGradientSq_enorm_le
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (z : ParabolicPoint) :
    ENNReal.ofReal (spatialGradientSq u Du z) ≤
      9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hreal : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ (2 : ℕ) := by
    rw [spatialGradientSq]
    calc
      ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ) ≤
          ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((norm_le_pi_norm (Du z i) j).trans (norm_le_pi_norm (Du z) i)) 2
      _ = 9 * ‖Du z‖ ^ (2 : ℕ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  calc
    ENNReal.ofReal (spatialGradientSq u Du z) ≤
        ENNReal.ofReal (9 * ‖Du z‖ ^ (2 : ℕ)) := ENNReal.ofReal_le_ofReal hreal
    _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
        show ENNReal.ofReal (9 : ℝ) = 9 by norm_num,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      norm_num [ENNReal.rpow_natCast]

/-- The constant in the ball-time Sobolev interpolation estimate. -/
@[expose]
noncomputable def ballTimeSobolevConstant : ℝ :=
  energyInterpolationSobolevConstant

private theorem ballTimeSobolevConstant_pos : 0 < ballTimeSobolevConstant :=
  (Classical.choose_spec CKN.ball_time_sobolev).1

/-- The global energy interpolation constant for the `L^{10/3}` bound. -/
@[expose]
noncomputable def energyTenThirdsConstant : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (2 / 3 : ℝ)) * 3 *
    ENNReal.ofReal energyInterpolationSobolevConstant

private theorem ball_time_sobolev_apply :
    ∀ (x₀ : Vec3) (r : ℝ), 0 < r →
    ∀ J : Set ℝ, OrdConnected J →
    ∀ g : Vec3 × ℝ → ℝ, ∀ Dg : Vec3 × ℝ → Vec3,
    let U := vec3Ball x₀ r
    AEStronglyMeasurable g (volume.restrict (U ×ˢ J)) →
    AEStronglyMeasurable Dg (volume.restrict (U ×ˢ J)) →
    (∀ᵐ s ∂volume.restrict J, ∃ v : H1Function U,
      (fun x => g (x,s)) =ᵐ[volume.restrict U] v.toFun ∧
      (fun x => Dg (x,s)) =ᵐ[volume.restrict U] v.grad) →
    MemLp g 2 (volume.restrict (U ×ˢ J)) →
    MemLp Dg 2 (volume.restrict (U ×ˢ J)) →
    let A := essSup
      (fun s => eLpNorm (fun x => g (x,s)) 2 (volume.restrict U))
      (volume.restrict J)
    A < ⊤ →
    MemLp g (ENNReal.ofReal (10/3 : ℝ)) (volume.restrict (U ×ˢ J)) ∧
    eLpNorm g (ENNReal.ofReal (10/3 : ℝ))
        (volume.restrict (U ×ˢ J)) ^ (10/3 : ℝ) ≤
      ENNReal.ofReal ballTimeSobolevConstant *
        (A ^ (4/3 : ℝ) *
            eLpNorm (fun z => vec3EuclideanNorm (Dg z)) 2
              (volume.restrict (U ×ˢ J)) ^ (2 : ℝ) +
         ENNReal.ofReal (r ^ (-2 : ℝ)) *
            A ^ (10/3 : ℝ) * volume J) := by
  exact (Classical.choose_spec CKN.ball_time_sobolev).2

private theorem slice_memLp_two_ae_of_lerayHopf
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict (Set.univ : Set Vec3)) ∧
      MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict (Set.univ : Set Vec3)) := by
  rcases hLH with ⟨_hT, _, huMeas, hDuMeas, _, hJoint, _, _, _, _, _, _⟩
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have huLT : (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono fun _ => le_add_right le_rfl) hJoint
  have hDuLT : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono fun _ => le_add_left le_rfl) hJoint
  have hu2 : MemLp u 2 (volume.restrict Q) :=
    memLp_two_of_lintegral_lt_top huMeas huLT
  have hDu2 : MemLp Du 2 (volume.restrict Q) :=
    memLp_two_of_lintegral_lt_top hDuMeas hDuLT
  have huSq : Integrable (fun z => (‖u z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact integrable_sq_of_lintegral_lt_top huMeas huLT
  have hDuSq : Integrable (fun z => (‖Du z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact integrable_sq_of_lintegral_lt_top hDuMeas hDuLT
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
  exact ⟨(memLp_two_iff_integrable_sq_norm hus).2 husq,
    (memLp_two_iff_integrable_sq_norm hDus).2 hDusq⟩

private theorem lerayHopf_component_tenThirds_on_ball
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => u z i)
      (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball x₀ r) (Ioo 0 T))) ∧
    eLpNorm (fun z : ParabolicPoint => u z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (spaceTimeSet (vec3Ball x₀ r) (Ioo 0 T))) ^
        (10 / 3 : ℝ) ≤
      ENNReal.ofReal ballTimeSobolevConstant *
        ((essSup
            (fun s => eLpNorm (fun x => u (x, s) i) 2
              (volume.restrict (vec3Ball x₀ r)))
            (volume.restrict (Ioo 0 T))) ^ (4 / 3 : ℝ) *
          eLpNorm (fun z => vec3EuclideanNorm (Du z i)) 2
            (volume.restrict (spaceTimeSet (vec3Ball x₀ r) (Ioo 0 T))) ^ (2 : ℝ) +
          ENNReal.ofReal (r ^ (-2 : ℝ)) *
            (essSup
              (fun s => eLpNorm (fun x => u (x, s) i) 2
                (volume.restrict (vec3Ball x₀ r)))
            (volume.restrict (Ioo 0 T))) ^ (10 / 3 : ℝ) *
            volume (Ioo 0 T)) ∧
    essSup (fun s => eLpNorm (fun x => u (x, s) i) 2
        (volume.restrict (vec3Ball x₀ r))) (volume.restrict (Ioo 0 T)) ≤
      (essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo 0 T))) ^ (1 / 2 : ℝ) := by
  classical
  have hSlices := slice_memLp_two_ae_of_lerayHopf hLH
  rcases hLH with ⟨_hT, _, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, _, _, _, _, _⟩
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let U : Set Vec3 := vec3Ball x₀ r
  have hQmeas : AEStronglyMeasurable u (volume.restrict Q) := huMeas
  have hDumeas : AEStronglyMeasurable Du (volume.restrict Q) := hDuMeas
  have huLT : (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    exact lt_of_le_of_lt (lintegral_mono fun _ => le_add_right le_rfl) hJointTop
  have hDuLT : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    exact lt_of_le_of_lt (lintegral_mono fun _ => le_add_left le_rfl) hJointTop
  have hu2 : MemLp u 2 (volume.restrict Q) :=
    memLp_two_of_lintegral_lt_top hQmeas huLT
  have hDu2 : MemLp Du 2 (volume.restrict Q) :=
    memLp_two_of_lintegral_lt_top hDumeas hDuLT
  have hsub : spaceTimeSet U (Ioo 0 T) ⊆ Q := by
    exact Set.prod_mono (by intro x hx; exact Set.mem_univ x) le_rfl
  have hu2U : MemLp (fun z : ParabolicPoint => u z i) 2
      (volume.restrict (spaceTimeSet U (Ioo 0 T))) := by
    exact memLp_pi_iff.mp
      (hu2.mono_measure (Measure.restrict_mono hsub le_rfl)) i
  let Dg : ParabolicPoint → Vec3 := fun z => Du z i
  have hDg2U : MemLp Dg 2
      (volume.restrict (spaceTimeSet U (Ioo 0 T))) := by
    exact (memLp_pi_iff.mp (hDu2.mono_measure
      (Measure.restrict_mono hsub le_rfl)) i)
  have hgMeas : AEStronglyMeasurable (fun z : ParabolicPoint => u z i)
      (volume.restrict (spaceTimeSet U (Ioo 0 T))) :=
    hu2U.aestronglyMeasurable
  have hDgMeas : AEStronglyMeasurable Dg
      (volume.restrict (spaceTimeSet U (Ioo 0 T))) :=
    hDg2U.aestronglyMeasurable
  have hWeakGradSlice : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => u (x, s) i) (fun x => Du (x, s) i) := by
    filter_upwards [hWeakGrad] with s hs
    exact hs i
  have hSliceH1 : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      ∃ v : H1Function U,
        (fun x => u (x, s) i) =ᵐ[volume.restrict U] v.toFun ∧
        (fun x => Dg (x, s)) =ᵐ[volume.restrict U] v.grad := by
    filter_upwards [hSlices, hWeakGradSlice]
      with s hmem hgrad
    refine ⟨⟨(fun x => u (x, s) i), (fun x => Du (x, s) i), ?_, ?_, ?_⟩,
      Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
    · exact (memLp_pi_iff.mp hmem.1 i).mono_measure
        (Measure.restrict_mono (Set.subset_univ U) le_rfl)
    · intro j
      exact (memLp_pi_iff.mp (memLp_pi_iff.mp hmem.2 i) j).mono_measure
        (Measure.restrict_mono (Set.subset_univ U) le_rfl)
    · exact hgrad.restrict (isOpen_vec3Ball x₀ r)
        (Set.subset_univ U)
  let B : ℝ≥0∞ := essSup
    (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
    (volume.restrict (Ioo 0 T))
  have hBtop : B < ⊤ := hSliceTop
  have hABound : essSup
      (fun s => eLpNorm (fun x => u (x, s) i) 2 (volume.restrict U))
      (volume.restrict (Ioo 0 T)) ≤ B ^ (1 / 2 : ℝ) := by
    have hae : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
        eLpNorm (fun x => u (x, s) i) 2 (volume.restrict U) ≤ B ^ (1 / 2 : ℝ) := by
      filter_upwards [ENNReal.ae_le_essSup
        (μ := volume.restrict (Ioo 0 T))
        (fun s => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)),
        hSlices] with s hs hmem
      have hcomponentMeas : AEStronglyMeasurable
          (fun x : Vec3 => u (x, s) i) (volume.restrict U) := by
        exact (memLp_pi_iff.mp (hmem.1.mono_measure
          (Measure.restrict_mono (Set.subset_univ U) le_rfl)) i).aestronglyMeasurable
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) (by norm_num) hcomponentMeas]
      simp only [ENNReal.toReal_ofNat]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      calc
        (∫⁻ x in U, ‖u (x, s) i‖ₑ ^ (2 : ℝ))
            ≤ ∫⁻ x : Vec3, ‖u (x, s) i‖ₑ ^ (2 : ℝ) := by
              calc
                (∫⁻ x in U, ‖u (x, s) i‖ₑ ^ (2 : ℝ)) ≤
                    ∫⁻ x in (Set.univ : Set Vec3),
                      ‖u (x, s) i‖ₑ ^ (2 : ℝ) :=
                  lintegral_mono_set (μ := volume) (Set.subset_univ U)
                _ = ∫⁻ x : Vec3, ‖u (x, s) i‖ₑ ^ (2 : ℝ) := by
                  rw [Measure.restrict_univ]
        _ ≤ ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ) := by
              have hpoint (x : Vec3) :
                  ‖u (x, s) i‖ₑ ^ (2 : ℝ) ≤ ‖u (x, s)‖ₑ ^ (2 : ℝ) :=
                ENNReal.rpow_le_rpow (enorm_apply_le (u (x, s)) i)
                  (by norm_num : (0 : ℝ) ≤ 2)
              exact lintegral_mono hpoint
        _ ≤ B := hs
    exact essSup_le_of_ae_le _ hae
  have hA : essSup
      (fun s => eLpNorm (fun x => u (x, s) i) 2 (volume.restrict U))
      (volume.restrict (Ioo 0 T)) < ⊤ := by
    exact lt_of_le_of_lt hABound
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBtop.ne)
  have hmain := ball_time_sobolev_apply x₀ r hr (Ioo 0 T)
    ordConnected_Ioo (fun z => u z i) Dg
    hgMeas hDgMeas hSliceH1 hu2U hDg2U hA
  refine ⟨hmain.1, hmain.2, ?_⟩
  simpa [B, U] using hABound

private theorem radius_tendsto_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  refine ⟨N, ?_⟩
  intro n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.le_trans hn (Nat.le_succ n)
  exact le_of_lt (hN.trans_le hcast)

private theorem tenThirds_radius_bound_tendsto (T : ℝ) (B M : ℝ≥0∞)
    (hB : B < ⊤) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ballTimeSobolevConstant *
      (M + ENNReal.ofReal (((n : ℝ) + 1) ^ (-(2 : ℝ))) *
        B ^ (5 / 3 : ℝ) * volume (Ioo 0 T))) atTop
      (nhds (ENNReal.ofReal ballTimeSobolevConstant * M)) := by
  have hVolumeTop : volume (Ioo 0 T) < ⊤ := measure_Ioo_lt_top
  have hBpowTop : B ^ (5 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne
  have hErrFactorTop : B ^ (5 / 3 : ℝ) * volume (Ioo 0 T) < ⊤ :=
    ENNReal.mul_lt_top hBpowTop hVolumeTop
  have hradius : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def] using radius_tendsto_atTop
  have hradiusPow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(2 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (2 : ℝ))).comp hradius
  have herror : Tendsto
      (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1) ^ (-(2 : ℝ))) *
        B ^ (5 / 3 : ℝ) * volume (Ioo 0 T)) atTop (nhds 0) := by
    have hcoef : Tendsto (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1) ^ (-(2 : ℝ))))
        atTop (nhds (0 : ℝ≥0∞)) := by simpa using ENNReal.tendsto_ofReal hradiusPow
    have hmul := (ENNReal.continuous_mul_const hErrFactorTop.ne).tendsto 0
    simpa only [Function.comp_def, zero_mul, mul_assoc] using hmul.comp hcoef
  have hsum : Tendsto (fun n : ℕ => M +
      (ENNReal.ofReal (((n : ℝ) + 1) ^ (-(2 : ℝ))) *
        B ^ (5 / 3 : ℝ) * volume (Ioo 0 T))) atTop (nhds M) := by
    simpa only [add_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => M)
      atTop (nhds M)).add herror
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto M |>.comp hsum

private theorem lerayHopf_component_tenThirds_lintegral_bound
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) (i : Fin 3) :
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ‖u z i‖ₑ ^ (10 / 3 : ℝ)) ≤
      ENNReal.ofReal ballTimeSobolevConstant *
        ((essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
          (volume.restrict (Ioo 0 T))) ^ (2 / 3 : ℝ) *
          (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            ENNReal.ofReal (spatialGradientSq u Du z))) := by
  classical
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μ : Measure ParabolicPoint := volume.restrict Q
  let B : ℝ≥0∞ := essSup
    (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
    (volume.restrict (Ioo 0 T))
  let G : ℝ≥0∞ := ∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)
  let M : ℝ≥0∞ := B ^ (2 / 3 : ℝ) * G
  have hSliceTop : B < ⊤ := by
    rcases hLH with ⟨_, _, _, _, h, _, _, _, _, _, _, _⟩
    exact h
  let radius : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hmainTendsto : Tendsto
      (fun n => ENNReal.ofReal ballTimeSobolevConstant *
        (M + ENNReal.ofReal (radius n ^ (-(2 : ℝ))) *
          B ^ (5 / 3 : ℝ) * volume (Ioo 0 T)))
      atTop (nhds (ENNReal.ofReal ballTimeSobolevConstant * M)) := by
    simpa [radius] using tenThirds_radius_bound_tendsto T B M hSliceTop
  have hQmeas : AEStronglyMeasurable u μ := by
    rcases hLH with ⟨_, _, h, _, _, _, _, _, _, _, _, _⟩
    exact h
  have huComp : AEStronglyMeasurable (fun z : ParabolicPoint => u z i) μ := by
    exact (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
      hQmeas
  let f : ParabolicPoint → ℝ≥0∞ := fun z => ‖u z i‖ₑ ^ (10 / 3 : ℝ)
  have hf : AEMeasurable f μ := by
    exact huComp.enorm.pow_const (10 / 3 : ℝ)
  let S : ℕ → Set ParabolicPoint := fun n =>
    spaceTimeSet (vec3Ball 0 (radius n)) (Set.univ : Set ℝ)
  have hSmeas (n : ℕ) : MeasurableSet (S n) := by
    exact (isOpen_spaceTimeSet (vec3Ball 0 (radius n)) Set.univ
      (isOpen_vec3Ball 0 (radius n)) isOpen_univ).measurableSet
  have hpoint (z : ParabolicPoint) :
      Tendsto (fun n => (S n).indicator f z) atTop (nhds (f z)) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (vec3EuclideanNorm z.1)
    have hEventually : ∀ᶠ n : ℕ in atTop, z ∈ S n := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ radius n := by
        simpa [radius] using (show (N : ℝ) ≤ (n : ℝ) + 1 by
          exact_mod_cast Nat.le_trans hn (Nat.le_succ n))
      have hball : vec3EuclideanNorm z.1 < radius n := hN.trans_le hcast
      change z.1 ∈ vec3Ball 0 (radius n) ∧ z.2 ∈ Set.univ
      constructor
      · simpa [vec3Ball, sub_zero] using hball
      · trivial
    exact (tendsto_const_nhds (x := f z)).congr' <| hEventually.mono fun n hn => by
      simp [hn]
  have hgn (n : ℕ) : AEMeasurable ((S n).indicator f) μ :=
    hf.indicator (hSmeas n)
  have hFatou := lintegral_liminf_le' (μ := μ) (u := atTop) hgn
  have hliminf (z : ParabolicPoint) :
      Filter.liminf (fun n => (S n).indicator f z) atTop = f z :=
    (hpoint z).liminf_eq
  have hglobalLe :
      (∫⁻ z in Q, f z) ≤
        Filter.liminf (fun n => ∫⁻ z, (S n).indicator f z ∂μ) atTop := by
    calc
      (∫⁻ z in Q, f z) = ∫⁻ z, Filter.liminf
          (fun n => (S n).indicator f z) atTop ∂μ := by
            apply lintegral_congr_ae
            exact ae_of_all μ (fun z => (hliminf z).symm)
      _ ≤ Filter.liminf
          (fun n => ∫⁻ z, (S n).indicator f z ∂μ) atTop := hFatou
  have hlocalBound (n : ℕ) :
      (∫⁻ z in spaceTimeSet (vec3Ball 0 (radius n)) (Ioo 0 T), f z) ≤
        ENNReal.ofReal ballTimeSobolevConstant *
          (M + ENNReal.ofReal (radius n ^ (-(2 : ℝ))) *
            B ^ (5 / 3 : ℝ) * volume (Ioo 0 T)) := by
    have hpos : 0 < radius n := by
      dsimp [radius]
      positivity
    have hlocal := lerayHopf_component_tenThirds_on_ball
      (x₀ := 0) hLH hpos i
    let U := vec3Ball (0 : Vec3) (radius n)
    have hsub : spaceTimeSet U (Ioo 0 T) ⊆ Q :=
      Set.prod_mono (Set.subset_univ U) le_rfl
    have hDuMeas : AEStronglyMeasurable Du
        (volume.restrict (spaceTimeSet U (Ioo 0 T))) := by
      rcases hLH with ⟨_, _, _, h, _, _, _, _, _, _, _, _⟩
      exact h.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hrowMeas : AEStronglyMeasurable (fun z : ParabolicPoint => Du z i)
        (volume.restrict (spaceTimeSet U (Ioo 0 T))) := by
      exact (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        hDuMeas
    have hgradMeas : AEStronglyMeasurable
        (fun z : ParabolicPoint => vec3EuclideanNorm (Du z i))
        (volume.restrict (spaceTimeSet U (Ioo 0 T))) :=
      continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hrowMeas
    have hgradSq :
        eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Du z i))
            2 (volume.restrict (spaceTimeSet U (Ioo 0 T))) ^ (2 : ℝ) ≤ G := by
      rw [eLpNorm_two_sq_eq_lintegral hgradMeas]
      calc
        (∫⁻ z in spaceTimeSet U (Ioo 0 T),
          ‖vec3EuclideanNorm (Du z i)‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ z in spaceTimeSet U (Ioo 0 T),
            ENNReal.ofReal (spatialGradientSq u Du z) := by
              apply lintegral_mono
              intro z
              change ‖vec3EuclideanNorm (Du z i)‖ₑ ^ (2 : ℝ) ≤
                ENNReal.ofReal (spatialGradientSq u Du z)
              have hnorm :
                  ‖vec3EuclideanNorm (Du z i)‖ₑ ^ (2 : ℝ) =
                    ENNReal.ofReal (vec3EuclideanNorm (Du z i) ^ (2 : ℕ)) := by
                rw [← ofReal_norm, Real.norm_eq_abs,
                  abs_of_nonneg (vec3EuclideanNorm_nonneg (Du z i)),
                  ENNReal.ofReal_rpow_of_nonneg
                    (vec3EuclideanNorm_nonneg (Du z i)) (by norm_num)]
                norm_num [Real.rpow_natCast]
              rw [hnorm]
              exact ENNReal.ofReal_le_ofReal
                (component_gradient_sq_le_spatialGradientSq z i)
        _ ≤ G := by
          dsimp [G, Q]
          exact lintegral_mono_set hsub
    have hA := hlocal.2.2
    have hA43 :
        (essSup (fun s => eLpNorm (fun x => u (x, s) i) 2
          (volume.restrict U)) (volume.restrict (Ioo 0 T))) ^ (4 / 3 : ℝ) ≤
        B ^ (2 / 3 : ℝ) := by
      calc
        _ ≤ (B ^ (1 / 2 : ℝ)) ^ (4 / 3 : ℝ) :=
          ENNReal.rpow_le_rpow hA (by norm_num)
        _ = B ^ (2 / 3 : ℝ) := by
          rw [← ENNReal.rpow_mul]
          norm_num
    have hA53 :
        (essSup (fun s => eLpNorm (fun x => u (x, s) i) 2
          (volume.restrict U)) (volume.restrict (Ioo 0 T))) ^ (10 / 3 : ℝ) ≤
        B ^ (5 / 3 : ℝ) := by
      calc
        _ ≤ (B ^ (1 / 2 : ℝ)) ^ (10 / 3 : ℝ) :=
          ENNReal.rpow_le_rpow hA (by norm_num)
        _ = B ^ (5 / 3 : ℝ) := by
          rw [← ENNReal.rpow_mul]
          norm_num
    have hterms :
        (essSup (fun s => eLpNorm (fun x => u (x, s) i) 2
          (volume.restrict U)) (volume.restrict (Ioo 0 T))) ^ (4 / 3 : ℝ) *
          eLpNorm (fun z => vec3EuclideanNorm (Du z i)) 2
            (volume.restrict (spaceTimeSet U (Ioo 0 T))) ^ (2 : ℝ) +
          ENNReal.ofReal (radius n ^ (-(2 : ℝ))) *
            (essSup (fun s => eLpNorm (fun x => u (x, s) i) 2
              (volume.restrict U)) (volume.restrict (Ioo 0 T))) ^ (10 / 3 : ℝ) *
            volume (Ioo 0 T) ≤
          M + ENNReal.ofReal (radius n ^ (-(2 : ℝ))) *
            B ^ (5 / 3 : ℝ) * volume (Ioo 0 T) := by
      dsimp [M]
      apply add_le_add
      · exact mul_le_mul hA43 hgradSq (by positivity) (by positivity)
      · gcongr
    have hnormLocal := hlocal.2.1
    have hlocalPower :
        eLpNorm (fun z : ParabolicPoint => u z i)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (spaceTimeSet U (Ioo 0 T))) ^ (10 / 3 : ℝ) ≤
          ENNReal.ofReal ballTimeSobolevConstant *
            (M + ENNReal.ofReal (radius n ^ (-(2 : ℝ))) *
              B ^ (5 / 3 : ℝ) * volume (Ioo 0 T)) := by
      exact hnormLocal.trans (by gcongr)
    have hintLocal :
        (∫⁻ z in spaceTimeSet U (Ioo 0 T),
          ‖u z i‖ₑ ^ (10 / 3 : ℝ)) ≤
          ENNReal.ofReal ballTimeSobolevConstant *
            (M + ENNReal.ofReal (radius n ^ (-(2 : ℝ))) *
              B ^ (5 / 3 : ℝ) * volume (Ioo 0 T)) := by
      rw [← eLpNorm_tenThirds_pow_eq_lintegral hlocal.1.aestronglyMeasurable]
      exact hlocalPower
    exact hintLocal
  have hseqLe (n : ℕ) :
      (∫⁻ z, (S n).indicator f z ∂μ) ≤
        ENNReal.ofReal ballTimeSobolevConstant *
          (M + ENNReal.ofReal (radius n ^ (-(2 : ℝ))) *
            B ^ (5 / 3 : ℝ) * volume (Ioo 0 T)) := by
    have hset : S n ∩ Q =
        spaceTimeSet (vec3Ball 0 (radius n)) (Ioo 0 T) := by
      ext z
      rcases z with ⟨x, t⟩
      change ((x ∈ vec3Ball 0 (radius n) ∧ t ∈ Set.univ) ∧
        (x ∈ (Set.univ : Set Vec3) ∧ t ∈ Ioo 0 T)) ↔
        (x ∈ vec3Ball 0 (radius n) ∧ t ∈ Ioo 0 T)
      simp
    rw [lintegral_indicator (hSmeas n), Measure.restrict_restrict (hSmeas n), hset]
    exact hlocalBound n
  have hlimInfSeq :
      Filter.liminf (fun n => ∫⁻ z, (S n).indicator f z ∂μ) atTop ≤
        ENNReal.ofReal ballTimeSobolevConstant * M := by
    calc
      Filter.liminf (fun n => ∫⁻ z, (S n).indicator f z ∂μ) atTop ≤
          Filter.liminf
            (fun n => ENNReal.ofReal ballTimeSobolevConstant *
              (M + ENNReal.ofReal (radius n ^ (-(2 : ℝ))) *
                B ^ (5 / 3 : ℝ) * volume (Ioo 0 T))) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hseqLe)
      _ = ENNReal.ofReal ballTimeSobolevConstant * M := hmainTendsto.liminf_eq
  have hfinal := hglobalLe.trans hlimInfSeq
  simpa only [Q, f, M, G] using hfinal

/-- `lem:u-ten-thirds`, with its first quantitative bound and the resulting
space-time `L^{10/3}` membership. The vector constant includes the finite
dimensional aggregation from its three scalar components. -/
theorem lerayHopf_memLp_tenThirds
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp u (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)) ≤
        energyTenThirdsConstant *
          ((essSup (fun s : ℝ => ∫⁻ x : Vec3,
              ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ))
            (volume.restrict (Ioo 0 T))) ^ (2 / 3 : ℝ) *
            (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              ENNReal.ofReal (spatialGradientSq u Du z))) := by
  classical
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μ : Measure ParabolicPoint := volume.restrict Q
  let Bsup : ℝ≥0∞ := essSup
    (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
    (volume.restrict (Ioo 0 T))
  let B : ℝ≥0∞ := essSup
    (fun s : ℝ => ∫⁻ x : Vec3,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ))
    (volume.restrict (Ioo 0 T))
  let G : ℝ≥0∞ := ∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)
  have hSliceTop : Bsup < ⊤ := by
    rcases hLH with ⟨_, _, _, _, h, _, _, _, _, _, _, _⟩
    exact h
  have hJointTop :
      (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    rcases hLH with ⟨_, _, _, _, _, h, _, _, _, _, _, _⟩
    exact h
  have hBLeThreeBsup : B ≤ 3 * Bsup := by
    apply essSup_le_of_ae_le _
    filter_upwards [ae_le_essSup (f :=
      fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))] with s hs
    calc
      (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ)) ≤
          ∫⁻ x : Vec3, 3 * ‖u (x, s)‖ₑ ^ (2 : ℝ) := by
        apply lintegral_mono
        intro x
        exact vec3Euclidean_sq_le_three_enorm_sq (u (x, s))
      _ = 3 * ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const_mul' (3 : ℝ≥0∞) _ (by norm_num)]
      _ ≤ 3 * Bsup := mul_le_mul_of_nonneg_left hs (by norm_num)
  have hBtop : B < ⊤ :=
    lt_of_le_of_lt hBLeThreeBsup
      (ENNReal.mul_lt_top (by norm_num) hSliceTop)
  have hBsupLe : Bsup ≤ B := by
    apply essSup_le_of_ae_le _
    filter_upwards [ae_le_essSup (f :=
      fun s : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ))] with s hs
    calc
      (∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ) := by
        apply lintegral_mono
        intro x
        exact enorm_sq_le_vec3Euclidean_sq (u (x, s))
      _ ≤ B := hs
  have hDuJoint : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) ≤
      ∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) := by
    apply lintegral_mono
    intro z
    exact le_add_left le_rfl
  have hGle : G ≤ 9 * (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) := by
    dsimp [G]
    calc
      (∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)) ≤
          ∫⁻ z in Q, 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        apply lintegral_mono
        intro z
        exact spatialGradientSq_enorm_le z
      _ = 9 * (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) := by
        rw [lintegral_const_mul' (9 : ℝ≥0∞) _ (by norm_num)]
  have hGtop : G < ⊤ :=
    lt_of_le_of_lt hGle
      (ENNReal.mul_lt_top (by norm_num : (9 : ℝ≥0∞) < ⊤)
        (lt_of_le_of_lt hDuJoint hJointTop))
  have hBpowTop : B ^ (2 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBtop.ne
  have hMtop : B ^ (2 / 3 : ℝ) * G < ⊤ := ENNReal.mul_lt_top hBpowTop hGtop
  have hQmeas : AEStronglyMeasurable u μ := by
    rcases hLH with ⟨_, _, h, _, _, _, _, _, _, _, _, _⟩
    exact h
  have hcomponentMeas (i : Fin 3) :
      AEStronglyMeasurable (fun z : ParabolicPoint => u z i) μ :=
    (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hQmeas
  have hcomponentPowMeas (i : Fin 3) :
      AEMeasurable (fun z : ParabolicPoint => ‖u z i‖ₑ ^ (10 / 3 : ℝ)) μ :=
    (hcomponentMeas i).enorm.pow_const (10 / 3 : ℝ)
  have hmass :
      (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)) ≤
        energyTenThirdsConstant * (B ^ (2 / 3 : ℝ) * G) := by
    have hpoint (z : ParabolicPoint) :
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ) ≤
          ENNReal.ofReal ((3 : ℝ) ^ (2 / 3 : ℝ)) *
            ∑ i : Fin 3, ‖u z i‖ₑ ^ (10 / 3 : ℝ) := by
      have hagg := CKN.ofReal_vec3EuclideanNorm_rpow_le_sum (u := u z)
        (p := (10 / 3 : ℝ)) (by norm_num : 1 ≤ (10 / 3 : ℝ))
      have hmax : max 0 ((10 / 3 : ℝ) / 2 - 1) = 2 / 3 := by norm_num
      simpa [hmax] using hagg
    have hsumMeas : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        AEMeasurable (fun z : ParabolicPoint => ‖u z i‖ₑ ^ (10 / 3 : ℝ)) μ :=
      fun i _ => hcomponentPowMeas i
    have hcomponentSum :
        (∑ i : Fin 3, ∫⁻ z in Q, ‖u z i‖ₑ ^ (10 / 3 : ℝ)) ≤
          ∑ i : Fin 3, ENNReal.ofReal ballTimeSobolevConstant *
            (B ^ (2 / 3 : ℝ) * G) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        (∫⁻ z in Q, ‖u z i‖ₑ ^ (10 / 3 : ℝ)) ≤
            ENNReal.ofReal ballTimeSobolevConstant *
              (Bsup ^ (2 / 3 : ℝ) * G) := by
          simpa [Bsup, G, Q] using
            lerayHopf_component_tenThirds_lintegral_bound hLH i
        _ ≤ ENNReal.ofReal ballTimeSobolevConstant *
              (B ^ (2 / 3 : ℝ) * G) := by
          gcongr
    calc
      (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)) ≤
          ∫⁻ z in Q, ENNReal.ofReal ((3 : ℝ) ^ (2 / 3 : ℝ)) *
            ∑ i : Fin 3, ‖u z i‖ₑ ^ (10 / 3 : ℝ) := by
        apply lintegral_mono
        exact hpoint
      _ = ENNReal.ofReal ((3 : ℝ) ^ (2 / 3 : ℝ)) *
            ∑ i : Fin 3, ∫⁻ z in Q, ‖u z i‖ₑ ^ (10 / 3 : ℝ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ hsumMeas]
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (2 / 3 : ℝ)) *
            ∑ i : Fin 3, ENNReal.ofReal ballTimeSobolevConstant *
              (B ^ (2 / 3 : ℝ) * G) :=
        mul_le_mul_of_nonneg_left hcomponentSum (by positivity)
      _ = energyTenThirdsConstant * (B ^ (2 / 3 : ℝ) * G) := by
        simp [energyTenThirdsConstant, ballTimeSobolevConstant,
          Finset.sum_const, Fintype.card_fin]
        simp only [mul_assoc]
  have hconstTop : energyTenThirdsConstant < ⊤ := by
    unfold energyTenThirdsConstant
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num))
      ENNReal.ofReal_lt_top
  have hmassTop : (∫⁻ z in Q,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)) < ⊤ :=
    lt_of_le_of_lt hmass (ENNReal.mul_lt_top hconstTop hMtop)
  have hnormMassLe : (∫⁻ z in Q, ‖u z‖ₑ ^ (10 / 3 : ℝ)) ≤
      ∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ) := by
    apply lintegral_mono
    intro z
    calc
      ‖u z‖ₑ ^ (10 / 3 : ℝ) = ENNReal.ofReal (‖u z‖ ^ (10 / 3 : ℝ)) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      _ ≤ ENNReal.ofReal (vec3EuclideanNorm (u z) ^ (10 / 3 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _)
          (CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm (u z)) (by norm_num))
      _ = ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ) :=
        (ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
          (by norm_num)).symm
  have hnormMassTop : (∫⁻ z in Q, ‖u z‖ₑ ^ (10 / 3 : ℝ)) < ⊤ :=
    lt_of_le_of_lt hnormMassLe hmassTop
  have hmem : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) μ := by
    exact memLp_ofReal_of_lintegral_lt_top (by norm_num) hQmeas hnormMassTop
  refine ⟨?_, ?_⟩
  · simpa [Q, μ] using hmem
  · simpa [Q, B, G] using hmass


end CKN
