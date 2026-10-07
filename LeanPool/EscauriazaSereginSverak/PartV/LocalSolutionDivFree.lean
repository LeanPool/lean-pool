/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionDivFreePairing
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices

/-!
# The forced heat response of a double-divergence-free tensor is divergence free

Let `G ∈ L²` be a tensor supported in the slab `Q_τ = ℝ³ × (0, τ)` with
`∑_ij ∂_i ∂_j G_ij(·, s) = 0` in the sense of distributions for almost every
time `s`. Then the forced heat response `Z_i = ∑_j ∂_j W₊ ⋆ G_ij` is weakly
divergence free on almost every time slice of the slab. This is the
divergence-free clause of the local solution in `prop:pv-local-solution`,
where `G = -(F + p I)` with `p` the Riesz pressure of `F`.

The proof is by duality: at almost every time the kernel integrals converge
absolutely against the weight `forcedHeatWeight`
(`kernel_weighted_lintegral_le`), and `forcedHeat_divergence_pairing_eq_zero`
evaluates the pairing with `∂_i ψ` as zero. A general tensor is first replaced
by a measurable modification, which does not change the response.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- For a measurable square-integrable tensor supported in the slab, the weighted
kernel integrals defining its forced heat response are finite on almost every
time slice of the slab. -/
theorem forcedHeat_weighted_slice_lintegral_lt_top {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ} (hGm : ∀ i j, Measurable (G i j))
    (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), ∀ i j,
      ∫⁻ x : Vec3, ENNReal.ofReal (forcedHeatWeight x) *
        ∫⁻ p : Vec3 × ℝ, ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (x - p.1, t - p.2)‖ₑ
          < ∞ := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  have hsupp' : ∀ z : Vec3 × ℝ, G i j z ≠ 0 → 0 < z.2 := by
    intro z hz
    by_contra hneg
    exact hz (hsupp i j z fun hmem => hneg hmem.2.1)
  obtain ⟨C, _, hC⟩ := kernel_weighted_lintegral_le hτ j
  have hbound := hC (fun z : Vec3 × ℝ => G i j z) (hG2 i j).aestronglyMeasurable hsupp'
  set F : Vec3 × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (forcedHeatWeight z.1) *
    ∫⁻ p : Vec3 × ℝ, ‖heatKernelSpaceDerivative p.1 p.2 j * G i j (z - p : Vec3 × ℝ)‖ₑ with hF_def
  have hFm : Measurable F := by
    have hjoint : Measurable (fun q : (Vec3 × ℝ) × (Vec3 × ℝ) =>
        ‖heatKernelSpaceDerivative q.2.1 q.2.2 j * G i j (q.1 - q.2 : Vec3 × ℝ)‖ₑ) :=
      (((heatKernelSpaceDerivative_vecTime_measurable j).comp measurable_snd).mul
        ((hGm i j).comp (show Measurable (fun q : (Vec3 × ℝ) × (Vec3 × ℝ) =>
          (q.1 - q.2 : Vec3 × ℝ)) from measurable_fst.sub measurable_snd))).enorm
    exact (ENNReal.measurable_ofReal.comp (forcedHeatWeight_continuous.measurable.comp
      measurable_fst)).mul hjoint.lintegral_prod_right'
  have hmeas : volume.restrict ((univ : Set Vec3) ×ˢ Ioo 0 τ) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo 0 τ)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hfin : ∫⁻ z, F z ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 τ))) ≠ ∞ := by
    rw [← hmeas]
    exact (hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hG2 i j).eLpNorm_lt_top)).ne
  rw [lintegral_prod_symm _ hFm.aemeasurable] at hfin
  filter_upwards [ae_lt_top hFm.lintegral_prod_left' hfin] with t ht
  exact ht

/-- Almost every time slice of a square-integrable tensor supported in the slab
is square integrable. -/
theorem tensor_slice_memLp_two_ae {τ : ℝ} {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ i j, MemLp (fun y : Vec3 => G i j (y, s)) 2 volume := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  have h := serrin_slice_memLp_ae (T := τ) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    ENNReal.ofNat_ne_top ((hG2 i j).restrict _)
  rw [ae_restrict_iff' measurableSet_Ioo] at h
  filter_upwards [h] with s hs
  by_cases hsI : s ∈ Ioo 0 τ
  · exact hs hsI
  · have hzero : (fun y : Vec3 => G i j (y, s)) = 0 := by
      funext y
      exact hsupp i j (y, s) fun hmem => hsI hmem.2
    rw [hzero]
    exact MemLp.zero

/-- The divergence-free property of the forced heat response for a measurable
double-divergence-free tensor in `L²` supported in the slab. -/
theorem forcedHeat_divFree_of_measurable {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ} (hGm : ∀ i j, Measurable (G i j))
    (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    (hdd : ∀ᵐ s ∂(volume : Measure ℝ), ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, G i j (y, s) * CKN.mixedSecond φ i j y = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), ∀ ψ : CKN.WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, forcedHeat G (x, t) i * ψ.partialDeriv i x = 0 := by
  have hslice := (tensor_slice_memLp_two_ae hG2 hsupp).and hdd
  filter_upwards [forcedHeat_weighted_slice_lintegral_lt_top hτ hGm hG2 hsupp] with t ht ψ
  exact forcedHeat_divergence_pairing_eq_zero hGm ht hslice ψ

/-- The forced heat response of a double-divergence-free tensor is divergence
free: for `G ∈ L²` supported in `Q_τ` with `∑_ij ∂_i ∂_j G_ij(·, s) = 0` in the
sense of distributions for almost every `s`, almost every time slice of
`Z = forcedHeat G` in `(0, τ)` satisfies `∫ Z · ∇ψ = 0` for every test function
`ψ`. This is the divergence-free clause of `prop:pv-local-solution`. -/
theorem forcedHeat_divFree {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    (hdd : ∀ᵐ s ∂(volume : Measure ℝ), ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, G i j (y, s) * CKN.mixedSecond φ i j y = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), ∀ ψ : CKN.WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, forcedHeat G (x, t) i * ψ.partialDeriv i x = 0 := by
  set S : Set ParabolicPoint := CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) with hS_def
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioo
  set G' : Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun i j =>
    S.indicator ((hG2 i j).aestronglyMeasurable.mk (G i j)) with hG'_def
  have hG'm (i j : Fin 3) : Measurable (G' i j) :=
    (hG2 i j).aestronglyMeasurable.stronglyMeasurable_mk.measurable.indicator hS
  have hGG' (i j : Fin 3) : G i j =ᵐ[volume] G' i j := by
    have hind : S.indicator (G i j) = G i j := by
      funext z
      by_cases hz : z ∈ S
      · exact indicator_of_mem hz _
      · rw [indicator_of_notMem hz, hsupp i j z hz]
    exact (EventuallyEq.of_eq hind.symm).trans
      (hG2 i j).aestronglyMeasurable.ae_eq_mk.indicator
  have hG'2 (i j : Fin 3) : MemLp (G' i j) 2 volume := (hG2 i j).ae_eq (hGG' i j)
  have hG'supp : ∀ i j z, z ∉ S → G' i j z = 0 := fun i j z hz => indicator_of_notMem hz _
  have hG'dd : ∀ᵐ s ∂(volume : Measure ℝ), ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, G' i j (y, s) * CKN.mixedSecond φ i j y = 0 := by
    have hslices : ∀ᵐ s ∂(volume : Measure ℝ), ∀ i j,
        (fun y : Vec3 => G i j (y, s)) =ᵐ[volume] fun y => G' i j (y, s) := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      have h : ∀ᵐ q ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
          G i j q = G' i j q := hGG' i j
      have hswap := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae h
      exact Measure.ae_ae_of_ae_prod hswap
    filter_upwards [hdd, hslices] with s hs hsl φ hφ hφc
    rw [← hs φ hφ hφc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    apply integral_congr_ae
    filter_upwards [hsl i j] with y hy
    rw [hy]
  have hZ (z : Vec3 × ℝ) : forcedHeat G z = forcedHeat G' z := by
    funext i
    change (∫ p : Vec3 × ℝ, ∑ j : Fin 3,
        heatKernelSpaceDerivative p.1 p.2 j * G i j (z - p : Vec3 × ℝ)) =
      ∫ p : Vec3 × ℝ, ∑ j : Fin 3,
        heatKernelSpaceDerivative p.1 p.2 j * G' i j (z - p : Vec3 × ℝ)
    have hshift (j : Fin 3) : (fun p : Vec3 × ℝ => G i j (z - p : Vec3 × ℝ)) =ᵐ[volume]
        fun p : Vec3 × ℝ => G' i j (z - p : Vec3 × ℝ) :=
      ((volume : Measure (Vec3 × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving.ae_eq_comp
        (hGG' i j)
    apply integral_congr_ae
    filter_upwards [ae_all_iff.2 hshift] with p hp
    exact Finset.sum_congr rfl fun j _ => by rw [hp j]
  filter_upwards [forcedHeat_divFree_of_measurable hτ hG'm hG'2 hG'supp hG'dd] with t ht ψ
  simp only [hZ]
  exact ht ψ

end ESS

end
