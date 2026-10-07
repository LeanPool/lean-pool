/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughApprox
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatEstimates

/-!
# The critical and `L⁴` bounds for rough tensors

For a tensor in `L^{5/2} ∩ L²` supported in the slab `Q_τ`, the forced heat
response (the kernel formula) inherits the smooth-data bounds of
`forcedHeat_smooth_estimates` by Fatou's lemma along the almost everywhere
convergent smooth approximation: the `L⁵` and `L⁴` bounds on `Q_τ` and, for
almost every time, the `L³` and `L²` slice bounds. This is the rough-data form
of `eq:pv-stokes-l5` and `eq:pv-stokes-l4` in `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The `L^p` norm of a `3 × 3` tensor field is at most the sum of the norms of
its entries. -/
theorem eLpNorm_tensor_le_sum {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (T : α → Fin 3 → Fin 3 → ℝ)
    (hT : ∀ i j, AEStronglyMeasurable (fun a => T a i j) μ) :
    eLpNorm T p μ ≤ ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (fun a => T a i j) p μ := by
  have hpt (a : α) : ‖T a‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖T a i j‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => norm_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => norm_nonneg _)).2 fun j => ?_
    calc
      ‖T a i j‖ ≤ ∑ j' : Fin 3, ‖T a i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖T a i j'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, ‖T a i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖T a i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hTm : AEStronglyMeasurable T μ :=
    (aemeasurable_pi_iff.2 fun i => aemeasurable_pi_iff.2 fun j =>
      (hT i j).aemeasurable).aestronglyMeasurable
  refine (eLpNorm_mono_real hTm hpt).trans ?_
  have hsum : (fun a => ∑ i : Fin 3, ∑ j : Fin 3, ‖T a i j‖) =
      ∑ i : Fin 3, ∑ j : Fin 3, fun a => ‖T a i j‖ := by
    funext a
    simp only [Finset.sum_apply]
  rw [hsum]
  refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (eLpNorm_sum_le hp).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun j _ => eLpNorm_norm _ (hT i j)

private theorem liminf_le_of_le_tendsto {u v : ℕ → ℝ≥0∞} {a : ℝ≥0∞} (huv : ∀ n, u n ≤ v n)
    (hv : Tendsto v atTop (𝓝 a)) : atTop.liminf u ≤ a :=
  (liminf_le_liminf (Eventually.of_forall huv)).trans hv.liminf_eq.le

private theorem tendsto_const_mul_add {C A : ℝ≥0∞} (hC : C ≠ ∞) {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => C * (A + e n)) atTop (𝓝 (C * A)) := by
  have h := ENNReal.Tendsto.const_mul (a := C) (tendsto_const_nhds (x := A) |>.add he)
    (Or.inr hC)
  simpa only [add_zero] using h

/-- The rough-data critical and `L⁴` bounds for the forced heat response of a
tensor in `L^{5/2} ∩ L²` supported in `Q_τ`, with the absolute constant of
`forcedHeat_smooth_estimates`. -/
theorem forcedHeat_rough_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume) →
      (∀ i j, MemLp (G i j) 2 volume) →
      (∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) →
      eLpNorm (forcedHeat G) 5
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      eLpNorm (forcedHeat G) 4
          (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C *
          (eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) +
          eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) := by
  obtain ⟨C, hC, hsmooth⟩ := forcedHeat_smooth_estimates
  refine ⟨C, hC, fun τ hτ G hG52 hG2 hGsupp => ?_⟩
  obtain ⟨Gn, hGn, hGnc, hGnpos, h52, h2, hae⟩ := forcedHeat_rough_approx hτ hG52 hG2 hGsupp
  set Q : Set ParabolicPoint := CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  set μQ : Measure ParabolicPoint := volume.restrict Q
  set Gt : ParabolicPoint → Fin 3 → Fin 3 → ℝ := fun z i j => G i j z
  have hGm (i j : Fin 3) : AEStronglyMeasurable (fun z : ParabolicPoint => G i j z) volume :=
    (hG2 i j).aestronglyMeasurable
  have hGnm (n : ℕ) (i j : Fin 3) :
      AEStronglyMeasurable (fun z : ParabolicPoint => Gn n i j z) volume :=
    (hGn n i j).continuous.aestronglyMeasurable
  -- tensor norms of the approximants
  have htensor (p : ℝ≥0∞) (hp : 1 ≤ p) (n : ℕ) :
      eLpNorm (fun z => fun i j => Gn n i j z) p μQ ≤
        eLpNorm Gt p μQ + ∑ i : Fin 3, ∑ j : Fin 3,
          eLpNorm (fun q : Vec3 × ℝ => Gn n i j q - G i j q) p volume := by
    have hsplit : (fun z => fun i j => Gn n i j z) =
        Gt + fun z => fun i j => Gn n i j z - G i j z := by
      funext z i j
      simp [Gt]
    rw [hsplit]
    refine (eLpNorm_add_le hp).trans (add_le_add le_rfl ?_)
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    exact eLpNorm_tensor_le_sum hp _ fun i j => (hGnm n i j).sub (hGm i j)
  have he52 : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      eLpNorm (fun q : Vec3 × ℝ => Gn n i j q - G i j q) (ENNReal.ofReal (5 / 2)) volume)
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => h52 i j
    simpa only [Finset.sum_const_zero] using h
  have he2 : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      eLpNorm (fun q : Vec3 × ℝ => Gn n i j q - G i j q) 2 volume) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => h2 i j
    simpa only [Finset.sum_const_zero] using h
  have hp52 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (5 / 2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  -- measurability of the responses
  have hZm : AEStronglyMeasurable (forcedHeat G) (volume : Measure ParabolicPoint) :=
    (aemeasurable_pi_iff.2 fun i =>
      (kernelResponse_component_aestronglyMeasurable (g := fun i j (q : Vec3 × ℝ) => G i j q)
        hGm i).aemeasurable).aestronglyMeasurable
  have hZnc (n : ℕ) : Continuous (fun z : Vec3 × ℝ => forcedHeat (Gn n) z) :=
    continuous_pi fun i => (forcedHeat_contDiff (hGn n) (hGnc n) i).continuous
  have hZnm (n : ℕ) : AEStronglyMeasurable (forcedHeat (Gn n)) (volume : Measure ParabolicPoint) :=
    (hZnc n).aestronglyMeasurable
  have haeQ : ∀ᵐ z ∂μQ, Tendsto (fun n => forcedHeat (Gn n) z) atTop (𝓝 (forcedHeat G z)) :=
    hae
  have hC' : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
  -- slices
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 τ) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo 0 τ)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hae' : ∀ᵐ z ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 τ))),
      Tendsto (fun n => forcedHeat (Gn n) z) atTop (𝓝 (forcedHeat G z)) := by
    rw [← hprod]
    exact hae
  have hswap := (Measure.measurePreserving_swap (μ := volume.restrict (Ioo (0 : ℝ) τ))
    (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae hae'
  have hslices := Measure.ae_ae_of_ae_prod hswap
  have hslice (t : ℝ) (ht : t ∈ Ioo 0 τ)
      (hlim : ∀ᵐ x ∂(volume : Measure Vec3),
        Tendsto (fun n => forcedHeat (Gn n) (x, t)) atTop (𝓝 (forcedHeat G (x, t))))
      (p : ℝ≥0∞) (A : ℝ≥0∞) (e : ℕ → ℝ≥0∞) (he : Tendsto e atTop (𝓝 0))
      (hbound : ∀ n, eLpNorm (fun x : Vec3 => forcedHeat (Gn n) (x, t)) p volume ≤
        ENNReal.ofReal C * (A + e n)) :
      eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) p volume ≤ ENNReal.ofReal C * A := by
    have hfn (n : ℕ) : AEStronglyMeasurable (fun x : Vec3 => forcedHeat (Gn n) (x, t)) volume :=
      ((hZnc n).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    have hflim : AEStronglyMeasurable (fun x : Vec3 => forcedHeat G (x, t)) volume :=
      aestronglyMeasurable_of_tendsto_ae atTop hfn hlim
    exact (Lp.eLpNorm_lim_le_liminf_eLpNorm hfn _ hflim hlim).trans
      (liminf_le_of_le_tendsto hbound (tendsto_const_mul_add hC' he))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `L⁵`
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hZnm n).restrict) _ hZm.restrict
      haeQ).trans (liminf_le_of_le_tendsto (fun n => ?_)
        (tendsto_const_mul_add hC' he52))
    exact ((hsmooth (Gn n) (hGn n) (hGnc n) (hGnpos n) τ hτ).2.2.2.1).trans
      (mul_le_mul_right (htensor _ hp52 n) _)
  · -- `L⁴`
    have he := he52.add he2
    rw [add_zero] at he
    have hsum := tendsto_const_mul_add (A := eLpNorm Gt (ENNReal.ofReal (5 / 2)) μQ +
      eLpNorm Gt 2 μQ) hC' he
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hZnm n).restrict) _ hZm.restrict
      haeQ).trans (liminf_le_of_le_tendsto (v := fun n => ENNReal.ofReal C *
        ((eLpNorm Gt (ENNReal.ofReal (5 / 2)) μQ + eLpNorm Gt 2 μQ) +
          ((∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (fun q : Vec3 × ℝ => Gn n i j q - G i j q)
            (ENNReal.ofReal (5 / 2)) volume) +
          ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (fun q : Vec3 × ℝ => Gn n i j q - G i j q)
            2 volume))) (fun n => ?_) ?_)
    · exact ((hsmooth (Gn n) (hGn n) (hGnc n) (hGnpos n) τ hτ).2.2.2.2).trans
        (mul_le_mul_right (le_of_le_of_eq (add_le_add (htensor _ hp52 n)
          (htensor 2 (by norm_num) n)) (by ring)) _)
    · exact hsum
  · filter_upwards [hslices, ae_restrict_mem measurableSet_Ioo] with t hlim ht
    refine hslice t ht hlim 3 _ _ he52 fun n => ?_
    exact ((hsmooth (Gn n) (hGn n) (hGnc n) (hGnpos n) τ hτ).2.2.1 t ⟨ht.1.le, ht.2.le⟩).trans
      (mul_le_mul_right (htensor _ hp52 n) _)
  · filter_upwards [hslices, ae_restrict_mem measurableSet_Ioo] with t hlim ht
    refine hslice t ht hlim 2 _ _ he2 fun n => ?_
    exact ((hsmooth (Gn n) (hGn n) (hGnc n) (hGnpos n) τ hτ).1 t ⟨ht.1.le, ht.2.le⟩).trans
      (mul_le_mul_right (htensor 2 (by norm_num) n) _)

end ESS

end
