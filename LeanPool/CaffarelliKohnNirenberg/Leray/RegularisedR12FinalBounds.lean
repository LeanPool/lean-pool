/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalField
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedEnergyForm

/-!
# Square integrability of the space-time fields on slabs

Each spatial slice of a weighted field is the inverse Fourier transform of a
square-integrable frequency field, so its `L²` norm is bounded by the norm of
the frequency field. Integrating over time, a space-time field whose frequency
path is bounded on `[δ,T]` is square integrable on the slab `ℝ³ × (δ,T)`, as
required by `thm:regularised` (R2).
-/

public section

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

section Slice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem regR12Kernel_le_one (ξ : L2Vec3) : regR12Kernel ξ ≤ 1 := by
  unfold regR12Kernel
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith only [sq_nonneg ‖ξ‖])
    (by norm_num)

/-- The slice of a weighted field is square integrable, with norm at most
`C ‖G‖`. -/
theorem regR12WeightedField_slice_lintegral_le (M : L2Vec3 → ℂ) (hM : AEStronglyMeasurable M)
    (C : ℝ) (hC : 0 ≤ C) (hMC : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2))
    (G : Lp E 2 (volume : Measure L2Vec3)) :
    (∫⁻ x : Vec3, ‖regR12WeightedField M G (WithLp.toLp 2 x)‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal (C * ‖G‖) ^ (2 : ℝ) := by
  let h : L2Vec3 → E := fun ξ => M ξ • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
    (G : L2Vec3 → E) ξ
  have hpt : ∀ ξ, ‖h ξ‖ ≤ C * ‖(G : L2Vec3 → E) ξ‖ := by
    intro ξ
    have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
    have hw : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) := Real.rpow_nonneg hpos.le _
    have halg : (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) = regR12Kernel ξ := by
      unfold regR12Kernel
      rw [show (-1 : ℝ) = 1 + (-2) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    simp only [h]
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    calc ‖M ξ‖ * ((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) * ‖(G : L2Vec3 → E) ξ‖)
        ≤ C * (1 + ‖ξ‖ ^ 2) * ((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) * ‖(G : L2Vec3 → E) ξ‖) :=
          mul_le_mul_of_nonneg_right (hMC ξ) (by positivity)
      _ = C * ((1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) * ‖(G : L2Vec3 → E) ξ‖ := by ring
      _ = C * regR12Kernel ξ * ‖(G : L2Vec3 → E) ξ‖ := by rw [halg]
      _ ≤ C * 1 * ‖(G : L2Vec3 → E) ξ‖ := by
          gcongr
          exact regR12Kernel_le_one ξ
      _ = C * ‖(G : L2Vec3 → E) ξ‖ := by ring
  have hmeas : AEStronglyMeasurable h volume :=
    hM.smul (regR12Weight_continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable G))
  have hL2 : MemLp h 2 volume := by
    refine lt_of_le_of_lt (eLpNorm_mono_ae (g := fun ξ => C * ‖(G : L2Vec3 → E) ξ‖) hmeas
      (Filter.Eventually.of_forall fun ξ => ?_)) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt ξ
    · exact (((Lp.memLp G).norm).const_mul C)
  let H : Lp E 2 (volume : Measure L2Vec3) := (Lp.fourierTransformₗᵢ L2Vec3 E).symm (hL2.toLp h)
  have hH : ((Lp.fourierTransformₗᵢ L2Vec3 E H : Lp E 2 (volume : Measure L2Vec3)) :
      L2Vec3 → E) =ᵐ[volume] h := by
    simp only [H, LinearIsometryEquiv.apply_symm_apply]
    exact hL2.coeFn_toLp
  have hrep := regR12WeightedField_ae_eq M hM C hC hMC G H hH
  have hHnorm : ‖H‖ ≤ C * ‖G‖ := by
    simp only [H, LinearIsometryEquiv.norm_map]
    rw [Lp.norm_toLp, Lp.norm_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc eLpNorm h 2 volume ≤ eLpNorm (fun ξ => C * ‖(G : L2Vec3 → E) ξ‖) 2 volume :=
          eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall fun ξ => by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact hpt ξ)
      _ = ENNReal.ofReal C * eLpNorm (G : L2Vec3 → E) 2 volume := by
          rw [show (fun ξ => C * ‖(G : L2Vec3 → E) ξ‖) =
              C • (fun ξ => ‖(G : L2Vec3 → E) ξ‖) from rfl,
            eLpNorm_const_smul, Real.enorm_of_nonneg hC,
              eLpNorm_norm _ (Lp.aestronglyMeasurable G)]
      _ = ENNReal.ofReal (C * ‖G‖) := by
          rw [ENNReal.ofReal_mul hC, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top G)]
  have hchange : (∫⁻ x : Vec3, ‖regR12WeightedField M G (WithLp.toLp 2 x)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ y : L2Vec3, ‖regR12WeightedField M G y‖ₑ ^ (2 : ℝ) :=
    vec3ToL2Vec3_measurePreserving.lintegral_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
      (fun y : L2Vec3 => ‖regR12WeightedField M G y‖ₑ ^ (2 : ℝ))
  rw [hchange]
  calc (∫⁻ y : L2Vec3, ‖regR12WeightedField M G y‖ₑ ^ (2 : ℝ))
      = ∫⁻ y : L2Vec3, ‖(H : L2Vec3 → E) y‖ₑ ^ (2 : ℝ) := by
        apply lintegral_congr_ae
        filter_upwards [hrep] with y hy
        rw [hy]
    _ = eLpNorm (H : L2Vec3 → E) 2 volume ^ (2 : ℝ) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          (Lp.aestronglyMeasurable H), ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ ENNReal.ofReal (C * ‖G‖) ^ (2 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top H), ← Lp.norm_def]
        exact ENNReal.ofReal_le_ofReal hHnorm

/-- A space-time field whose frequency path is bounded on `(δ,T)` is square
integrable on the slab `ℝ³ × (δ,T)`. -/
theorem regR12SpaceTimeField_memLp_slab (c : E →L[ℝ] ℝ) (M : L2Vec3 → ℂ)
    (hM : AEStronglyMeasurable M) (C : ℝ) (hC : 0 ≤ C) (hMC : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2))
    (G : ℝ → Lp E 2 (volume : Measure L2Vec3)) (hG : Continuous G) (δ T B : ℝ)
    (hB : ∀ t ∈ Ioo δ T, ‖G t‖ ≤ B) :
    MemLp (regR12SpaceTimeField c M G) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
  let g : Vec3 × ℝ → ℝ := fun z => c (regR12WeightedField M (G z.2) (WithLp.toLp 2 z.1))
  have hgc : Continuous g := regR12SpaceTimeField_continuous c M hM C hC hMC G hG
  have hmeas : AEStronglyMeasurable (regR12SpaceTimeField c M G)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) :=
    hgc.aestronglyMeasurable
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hmeas,
    ENNReal.toReal_ofNat]
  let Φ : Vec3 × ℝ → ℝ≥0∞ := fun z => ‖g z‖ₑ ^ (2 : ℝ)
  have hΦ : Measurable Φ := (hgc.measurable.enorm).pow_const _
  have hslice : ∀ t ∈ Ioo δ T, (∫⁻ x, Φ (x, t)) ≤
      ENNReal.ofReal ‖c‖ ^ (2 : ℝ) * ENNReal.ofReal (C * B) ^ (2 : ℝ) := by
    intro t ht
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
    have hpt : ∀ x : Vec3, Φ (x, t) ≤ ENNReal.ofReal ‖c‖ ^ (2 : ℝ) *
        ‖regR12WeightedField M (G t) (WithLp.toLp 2 x)‖ₑ ^ (2 : ℝ) := by
      intro x
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      simp only [g]
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (c.le_opNorm _)
    calc (∫⁻ x, Φ (x, t)) ≤ ∫⁻ x, ENNReal.ofReal ‖c‖ ^ (2 : ℝ) *
          ‖regR12WeightedField M (G t) (WithLp.toLp 2 x)‖ₑ ^ (2 : ℝ) := lintegral_mono hpt
      _ = ENNReal.ofReal ‖c‖ ^ (2 : ℝ) *
          ∫⁻ x, ‖regR12WeightedField M (G t) (WithLp.toLp 2 x)‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ ENNReal.ofReal ‖c‖ ^ (2 : ℝ) * ENNReal.ofReal (C * ‖G t‖) ^ (2 : ℝ) := by
          gcongr
          exact regR12WeightedField_slice_lintegral_le M hM C hC hMC (G t)
      _ ≤ ENNReal.ofReal ‖c‖ ^ (2 : ℝ) * ENNReal.ofReal (C * B) ^ (2 : ℝ) := by
          gcongr
          exact hB t ht
  have heq : (∫⁻ z, ‖regR12SpaceTimeField c M G z‖ₑ ^ (2 : ℝ)
      ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) =
      ∫⁻ t in Ioo δ T, ∫⁻ x, Φ (x, t) := by
    change (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T), Φ z) = _
    rw [lintegral_slab_eq_prod Φ (Ioo δ T), lintegral_prod_symm' Φ hΦ]
  rw [heq]
  calc (∫⁻ t in Ioo δ T, ∫⁻ x, Φ (x, t))
      ≤ ∫⁻ _t in Ioo δ T, ENNReal.ofReal ‖c‖ ^ (2 : ℝ) * ENNReal.ofReal (C * B) ^ (2 : ℝ) :=
        setLIntegral_mono measurable_const hslice
    _ < ⊤ := by
        rw [setLIntegral_const, Real.volume_Ioo]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
          ENNReal.ofReal_lt_top

end Slice

end CKN.Leray
