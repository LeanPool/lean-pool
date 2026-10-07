/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatWeighted
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatLinear
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The kernel formula for rough tensors

For a tensor in `L²` vanishing at nonpositive times, the kernel integrals
defining the forced heat response converge absolutely at almost every point
of the slab `ℝ³ × (0,τ)`, the response is measurable, and responses of
approximating tensors converge to it in the weighted `L¹` sense and hence,
along a subsequence, almost everywhere on the slab. This identifies the rough
response of `lem:pv-stokes` with limits of smooth responses.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The kernel formula of the forced heat response for a tensor on `Vec3 × ℝ`. -/
@[expose] def kernelResponse (g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : Vec3 :=
  fun i => ∫ p : Vec3 × ℝ, ∑ j : Fin 3, heatKernelSpaceDerivative p.1 p.2 j * g i j (z - p)

/-- The forced heat response is the kernel formula of its tensor. -/
theorem forcedHeat_eq_kernelResponse (G : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (z : ParabolicPoint) :
    forcedHeat G z = kernelResponse (fun i j (p : Vec3 × ℝ) => G i j p) z := rfl

/-- The kernel response of a measurable tensor is measurable. -/
theorem kernelResponse_component_aestronglyMeasurable {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, AEStronglyMeasurable (g i j) volume) (i : Fin 3) :
    AEStronglyMeasurable (fun z : Vec3 × ℝ => kernelResponse g z i) volume := by
  let F : (Vec3 × ℝ) × (Vec3 × ℝ) → ℝ := fun q =>
    ∑ j : Fin 3, heatKernelSpaceDerivative q.2.1 q.2.2 j * g i j (q.1 - q.2)
  have hF : AEStronglyMeasurable F ((volume : Measure (Vec3 × ℝ)).prod volume) := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    exact ((heatKernelSpaceDerivative_vecTime_measurable j).comp
      measurable_snd).aestronglyMeasurable.mul
      ((hg i j).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  exact hF.integral_prod_right'

/-- For a source in `L²` vanishing at nonpositive times, the kernel integral is
absolutely convergent at almost every point of the slab. -/
theorem kernel_integrable_ae_slab {τ : ℝ} (hτ : 0 < τ) (j : Fin 3) {H : Vec3 × ℝ → ℝ}
    (hH : MemLp H 2 volume) (hsupp : ∀ z, H z ≠ 0 → 0 < z.2) :
    ∀ᵐ z ∂(volume.restrict ((univ : Set Vec3) ×ˢ Ioo 0 τ)),
      Integrable (fun p : Vec3 × ℝ => heatKernelSpaceDerivative p.1 p.2 j * H (z - p)) := by
  obtain ⟨C, _, hC⟩ := kernel_weighted_lintegral_le hτ j
  have hbound := hC H hH.aestronglyMeasurable hsupp
  have hfin : ∫⁻ z in (univ : Set Vec3) ×ˢ Ioo 0 τ, ENNReal.ofReal (forcedHeatWeight z.1) *
      ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H (z - p)‖ₑ ≠ ∞ :=
    (hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH.eLpNorm_lt_top)).ne
  have hjoint : AEMeasurable (fun q : (Vec3 × ℝ) × (Vec3 × ℝ) =>
      ‖heatKernelSpaceDerivative q.2.1 q.2.2 j * H (q.1 - q.2)‖ₑ)
      ((volume : Measure (Vec3 × ℝ)).prod volume) :=
    (((heatKernelSpaceDerivative_vecTime_measurable j).comp measurable_snd).aestronglyMeasurable.mul
      (hH.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))).enorm
  have hmeas : AEMeasurable (fun z : Vec3 × ℝ => ENNReal.ofReal (forcedHeatWeight z.1) *
      ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H (z - p)‖ₑ)
      (volume.restrict ((univ : Set Vec3) ×ˢ Ioo 0 τ)) :=
    ((ENNReal.measurable_ofReal.comp (forcedHeatWeight_continuous.measurable.comp
      measurable_fst)).aemeasurable.mul hjoint.lintegral_prod_right').restrict
  filter_upwards [ae_lt_top' hmeas hfin] with z hz
  have hw : ENNReal.ofReal (forcedHeatWeight z.1) ≠ 0 := by
    simpa using forcedHeatWeight_pos z.1
  have hlt : ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H (z - p)‖ₑ < ∞ := by
    by_contra hge
    rw [not_lt, top_le_iff] at hge
    rw [hge, ENNReal.mul_top hw] at hz
    exact lt_irrefl _ hz
  refine ⟨?_, hlt⟩
  exact ((heatKernelSpaceDerivative_vecTime_measurable j).aestronglyMeasurable.mul
    (hH.aestronglyMeasurable.comp_quasiMeasurePreserving
      ((volume : Measure (Vec3 × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving))

/-- The weighted kernel lintegral is measurable in the base point. -/
theorem kernel_weighted_aemeasurable (j : Fin 3) {H : Vec3 × ℝ → ℝ}
    (hH : AEStronglyMeasurable H volume) (μ : Measure (Vec3 × ℝ)) (hμ : μ ≪ volume) :
    AEMeasurable (fun z : Vec3 × ℝ => ENNReal.ofReal (forcedHeatWeight z.1) *
      ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H (z - p)‖ₑ) μ := by
  have hjoint : AEMeasurable (fun q : (Vec3 × ℝ) × (Vec3 × ℝ) =>
      ‖heatKernelSpaceDerivative q.2.1 q.2.2 j * H (q.1 - q.2)‖ₑ)
      ((volume : Measure (Vec3 × ℝ)).prod volume) :=
    (((heatKernelSpaceDerivative_vecTime_measurable j).comp measurable_snd).aestronglyMeasurable.mul
      (hH.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))).enorm
  exact (((ENNReal.measurable_ofReal.comp (forcedHeatWeight_continuous.measurable.comp
      measurable_fst)).aemeasurable.mul hjoint.lintegral_prod_right')).mono_ac hμ

/-- Responses of smooth tensors converging in `L²` to a rough tensor converge
to the rough response in the weighted `L¹` sense on the slab. -/
theorem kernelResponse_weighted_tendsto {τ : ℝ} (hτ : 0 < τ)
    {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {gn : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg2 : ∀ i j, MemLp (g i j) 2 volume)
    (hgsupp : ∀ i j z, g i j z ≠ 0 → 0 < z.2)
    (hgn : ∀ n i j, ContDiff ℝ (⊤ : ℕ∞) (gn n i j))
    (hgnc : ∀ n i j, HasCompactSupport (gn n i j))
    (hgnpos : ∀ n i j, tsupport (gn n i j) ⊆ {p | 0 < p.2})
    (hconv : ∀ i j, Tendsto (fun n => eLpNorm (gn n i j - g i j) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z in (univ : Set Vec3) ×ˢ Ioo 0 τ,
      ENNReal.ofReal (forcedHeatWeight z.1) * ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ)
      atTop (𝓝 0) := by
  set Q : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Ioo 0 τ
  choose C hC0 hC using fun j : Fin 3 => kernel_weighted_lintegral_le hτ j
  let H : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun n i j => gn n i j - g i j
  have hgnmem (n : ℕ) (i j : Fin 3) : MemLp (gn n i j) 2 volume :=
    (hgn n i j).continuous.memLp_of_hasCompactSupport (hgnc n i j)
  have hHm (n : ℕ) (i j : Fin 3) : AEStronglyMeasurable (H n i j) volume :=
    (hgnmem n i j).aestronglyMeasurable.sub (hg2 i j).aestronglyMeasurable
  have hHsupp (n : ℕ) (i j : Fin 3) (z : Vec3 × ℝ) (hz : H n i j z ≠ 0) : 0 < z.2 := by
    by_cases hgz : g i j z = 0
    · have hgnz : gn n i j z ≠ 0 := by
        intro h0
        apply hz
        simp [H, h0, hgz]
      exact hgnpos n i j (subset_tsupport _ hgnz)
    · exact hgsupp i j z hgz
  have hgint : ∀ᵐ (z : Vec3 × ℝ) ∂(volume.restrict Q), ∀ i j,
      Integrable (fun p : Vec3 × ℝ => heatKernelSpaceDerivative p.1 p.2 j * g i j (z - p)) := by
    have h := fun (ij : Fin 3 × Fin 3) => kernel_integrable_ae_slab hτ ij.2 (hg2 ij.1 ij.2)
      (hgsupp ij.1 ij.2)
    filter_upwards [ae_all_iff.2 h] with z hz i j
    exact hz (i, j)
  have hgnint (n : ℕ) (z : Vec3 × ℝ) (i j : Fin 3) :
      Integrable (fun p : Vec3 × ℝ => heatKernelSpaceDerivative p.1 p.2 j * gn n i j (z - p)) :=
    (heatKernelSpaceDerivative_locallyIntegrable j).integrable_smul_right_of_hasCompactSupport
      ((hgn n i j).continuous.comp (continuous_const.sub continuous_id))
      ((hgnc n i j).comp_homeomorph (Homeomorph.subLeft z))
  have hpoint (n : ℕ) : ∀ᵐ (z : Vec3 × ℝ) ∂(volume.restrict Q),
      ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H n i j (z - p)‖ₑ := by
    filter_upwards [hgint] with z hz
    have hcomp (i : Fin 3) : ‖kernelResponse (gn n) z i - kernelResponse g z i‖ₑ ≤
        ∑ j : Fin 3, ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H n i j (z - p)‖ₑ := by
      have hA : Integrable (fun p : Vec3 × ℝ => ∑ j : Fin 3,
          heatKernelSpaceDerivative p.1 p.2 j * gn n i j (z - p)) :=
        integrable_finsetSum _ fun j _ => hgnint n z i j
      have hB : Integrable (fun p : Vec3 × ℝ => ∑ j : Fin 3,
          heatKernelSpaceDerivative p.1 p.2 j * g i j (z - p)) :=
        integrable_finsetSum _ fun j _ => hz i j
      simp only [kernelResponse]
      rw [← integral_sub hA hB]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← lintegral_finsetSum' (f := fun j (p : Vec3 × ℝ) =>
        ‖heatKernelSpaceDerivative p.1 p.2 j * H n i j (z - p)‖ₑ) _ fun j _ =>
        ((heatKernelSpaceDerivative_vecTime_measurable j).aestronglyMeasurable.mul
          ((hHm n i j).comp_quasiMeasurePreserving
            ((volume : Measure (Vec3 × ℝ)).measurePreserving_sub_left
              z).quasiMeasurePreserving)).enorm]
      refine lintegral_mono fun p => ?_
      rw [← Finset.sum_sub_distrib]
      refine (enorm_sum_le _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simp only [H, Pi.sub_apply]
      ring
    calc
      ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ =
          ENNReal.ofReal ‖kernelResponse (gn n) z - kernelResponse g z‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∑ i : Fin 3, ‖kernelResponse (gn n) z i - kernelResponse g z i‖) := by
        refine ENNReal.ofReal_le_ofReal ((pi_norm_le_iff_of_nonneg
          (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun i => ?_)
        exact Finset.single_le_sum
          (f := fun k => ‖kernelResponse (gn n) z k - kernelResponse g z k‖)
          (fun k _ => norm_nonneg _) (Finset.mem_univ i)
      _ = ∑ i : Fin 3, ‖kernelResponse (gn n) z i - kernelResponse g z i‖ₑ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
        simp_rw [ofReal_norm]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hcomp i
  have hbound (n : ℕ) : ∫⁻ z in Q, ENNReal.ofReal (forcedHeatWeight z.1) *
      ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ENNReal.ofReal (C j) * eLpNorm (H n i j) 2 volume := by
    calc
      _ ≤ ∫⁻ z in Q, ∑ i : Fin 3, ∑ j : Fin 3, ENNReal.ofReal (forcedHeatWeight z.1) *
          ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H n i j (z - p)‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpoint n] with z hz
        refine (mul_le_mul_right hz _).trans (le_of_eq ?_)
        simp only [Finset.mul_sum]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫⁻ z in Q, ENNReal.ofReal (forcedHeatWeight z.1) *
          ∫⁻ p, ‖heatKernelSpaceDerivative p.1 p.2 j * H n i j (z - p)‖ₑ := by
        rw [lintegral_finsetSum' _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
          kernel_weighted_aemeasurable j (hHm n i j) _
            Measure.restrict_le_self.absolutelyContinuous]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact lintegral_finsetSum' _ fun j _ =>
          kernel_weighted_aemeasurable j (hHm n i j) _ Measure.restrict_le_self.absolutelyContinuous
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        hC j (H n i j) (hHm n i j) (hHsupp n i j)
  have hlim : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ENNReal.ofReal (C j) * eLpNorm (H n i j) 2 volume) atTop (𝓝 0) := by
    have h1 (i j : Fin 3) : Tendsto (fun n => ENNReal.ofReal (C j) * eLpNorm (H n i j) 2 volume)
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C j)) (hconv i j)
        (Or.inr ENNReal.ofReal_ne_top)
      simpa only [mul_zero] using h
    have h2 (i : Fin 3) : Tendsto (fun n => ∑ j : Fin 3,
        ENNReal.ofReal (C j) * eLpNorm (H n i j) 2 volume) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => h1 i j
      simpa only [Finset.sum_const_zero] using h
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ => h2 i
    simpa only [Finset.sum_const_zero] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => bot_le) hbound

/-- Along a subsequence, responses of smooth approximants converge almost
everywhere on the slab to the rough response. -/
theorem kernelResponse_ae_subseq {τ : ℝ} (hτ : 0 < τ)
    {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {gn : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg2 : ∀ i j, MemLp (g i j) 2 volume)
    (hgsupp : ∀ i j z, g i j z ≠ 0 → 0 < z.2)
    (hgn : ∀ n i j, ContDiff ℝ (⊤ : ℕ∞) (gn n i j))
    (hgnc : ∀ n i j, HasCompactSupport (gn n i j))
    (hgnpos : ∀ n i j, tsupport (gn n i j) ⊆ {p | 0 < p.2})
    (hconv : ∀ i j, Tendsto (fun n => eLpNorm (gn n i j - g i j) 2 volume) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ z ∂(volume.restrict ((univ : Set Vec3) ×ˢ Ioo 0 τ)),
      Tendsto (fun k => kernelResponse (gn (ns k)) z) atTop (𝓝 (kernelResponse g z)) := by
  have hw := kernelResponse_weighted_tendsto hτ hg2 hgsupp hgn hgnc hgnpos hconv
  let f : ℕ → Vec3 × ℝ → Vec3 := fun n z =>
    forcedHeatWeight z.1 • (kernelResponse (gn n) z - kernelResponse g z)
  have hf : Tendsto (fun n => eLpNorm (f n - fun _ => (0 : Vec3)) 1
      (volume.restrict ((univ : Set Vec3) ×ˢ Ioo 0 τ))) atTop (𝓝 0) := by
    refine hw.congr fun n => ?_
    have hZ (h : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (hh : ∀ i j, AEStronglyMeasurable (h i j) volume) :
        AEStronglyMeasurable (kernelResponse h) volume :=
      (aemeasurable_pi_iff.2 fun i =>
        (kernelResponse_component_aestronglyMeasurable hh i).aemeasurable).aestronglyMeasurable
    have hfm : AEStronglyMeasurable (f n - fun _ => (0 : Vec3))
        (volume.restrict ((univ : Set Vec3) ×ˢ Ioo 0 τ)) :=
      (((forcedHeatWeight_continuous.comp continuous_fst).aestronglyMeasurable.smul
        ((hZ _ fun i j => (hgn n i j).continuous.aestronglyMeasurable).sub
          (hZ _ fun i j => (hg2 i j).aestronglyMeasurable))).sub
        aestronglyMeasurable_const).restrict
    rw [eLpNorm_one_eq_lintegral_enorm hfm]
    apply lintegral_congr
    intro z
    simp only [f, Pi.sub_apply, sub_zero]
    rw [enorm_smul, Real.enorm_eq_ofReal (forcedHeatWeight_pos z.1).le]
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    hf).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae] with z hz
  have hwpos := forcedHeatWeight_pos z.1
  have hlim := (hz.const_smul (forcedHeatWeight z.1)⁻¹).add_const (kernelResponse g z)
  simp only [smul_zero, zero_add] at hlim
  refine hlim.congr fun k => ?_
  simp only [f, smul_smul, inv_mul_cancel₀ hwpos.ne', one_smul, sub_add_cancel]

end ESS

end
