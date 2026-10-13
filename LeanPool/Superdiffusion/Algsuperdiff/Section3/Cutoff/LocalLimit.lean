/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Locality
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit

/-!
# LocalLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Integral-local measurability of the genuine lower cutoff

This module promotes finite lower-cutoff locality to the genuine lower-infinite
cutoff.  The target is the manuscript/CoarseGraining integral-local sigma-field
`LocalSigmaR U`: compactly supported entry tests in `U` are limits of the
corresponding finite lower-cutoff tests.  The limit is taken on the public
`CutoffSample` carrier, where lower-tail convergence is genuine, while the
domain sigma-field is the explicit lower-shell completion.

This proves local *observability*.  Spatial independence and its exact range
remain separate consequences, and are not asserted here.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Topology
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The local information on the public cutoff carrier induced from the
completed lower-shell local sigma-field on the canonical shell sequence. -/
abbrev cutoffSampleLocalSigma (M : ABKModel d) (m : ℤ) (U : Set (Vec d)) :
    MeasurableSpace (CutoffSample d) :=
  (lowerShellLocalCompletion M m U).comap Subtype.val

private theorem measurable_subtype_val_cutoffSampleLocal
    (M : ABKModel d) (m : ℤ) (U : Set (Vec d)) :
    @Measurable (CutoffSample d) (ShellSeq d)
      (cutoffSampleLocalSigma M m U) (lowerShellLocalCompletion M m U)
      Subtype.val :=
  Measurable.of_comap_le le_rfl

private theorem measurable_entryTestR_from_LocalSigmaR (U : Set (Vec d))
    (i j : Fin d) {phi : Vec d → ℝ} (hphi : IsProbeR phi)
    (hphiSupport : Function.support phi ⊆ U) :
    @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) (borel ℝ)
      (entryTestR i j phi) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, j, phi, hphi, hphiSupport, t, ht, rfl⟩

private theorem measurable_finiteLowerCutoff_on_cutoffSample_local
    (M : ABKModel d) (m : ℤ) (q : ℕ) (U : Set (Vec d)) :
    @Measurable (CutoffSample d) (RegCoeffField d)
      (cutoffSampleLocalSigma M m U) (LocalSigmaR U)
      (fun omega => finiteLowerCutoff m q omega.1) := by
  have hfinite : @Measurable (ShellSeq d) (RegCoeffField d)
      (lowerShellLocalCompletion M m U) (LocalSigmaR U)
      (finiteLowerCutoff m q) :=
    (measurable_finiteLowerCutoff_local m q U).mono
      (lowerShellLocalSigma_le_completion M m U) le_rfl
  exact hfinite.comp (measurable_subtype_val_cutoffSampleLocal M m U)

private theorem exists_openOriginCube_of_isCompact {K : Set (Vec d)}
    (hK : IsCompact K) :
    ∃ ell : ℤ, K ⊆ openCubeSet (originCube d ell) := by
  let g : Vec d → ℝ := fun x => 2 * ∑ i : Fin d, |x i|
  have hg : Continuous g := by
    exact continuous_const.mul
      (continuous_finsetSum Finset.univ
        (fun i _ => (continuous_apply i).abs))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 3)
  refine ⟨(n : ℤ), ?_⟩
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ ∑ j : Fin d, |x j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have hgx : |g x| ≤ C := hC x hx
  have hsum_nn : 0 ≤ ∑ j : Fin d, |x j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg (x j)
  have hsum : 2 * ∑ j : Fin d, |x j| ≤ C := by
    simpa [g, abs_of_nonneg hsum_nn] using hgx
  have hpow : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := by simp
  rw [hpow]
  have hb : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by linarith
  rw [abs_lt] at hb
  exact ⟨by linarith [hb.1], hb.2⟩

private theorem tendsto_entryTestR_of_tendstoUniformlyOn
    (F : ℕ → RegCoeffField d) (f : RegCoeffField d) (i j : Fin d)
    (phi : Vec d → ℝ) (hphi : IsProbeR phi) (W : Set (Vec d))
    (hconv : TendstoUniformlyOn (fun n x => F n x i j)
      (fun x => f x i j) atTop W)
    (hcont : Continuous (fun x => f x i j))
    (hKW : tsupport phi ⊆ W) :
    Tendsto (fun n => entryTestR i j phi (F n)) atTop
      (𝓝 (entryTestR i j phi f)) := by
  set K := tsupport phi with hK
  have hKcompact : IsCompact K := by
    simpa [hK] using! hphi.hasCompactSupport
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  obtain ⟨C0, hC0⟩ := hKcompact.exists_bound_of_continuousOn hcont.continuousOn
  let C : ℝ := max C0 0
  have hC : ∀ x ∈ K, |f x i j| ≤ C := fun x hx =>
    (hC0 x hx).trans (le_max_left _ _)
  have hCnonneg : 0 ≤ C := le_max_right _ _
  obtain ⟨B, hB⟩ := hphi.bounded
  have hBnonneg : 0 ≤ B := (abs_nonneg (phi 0)).trans (hB 0)
  have hnear : ∀ᶠ n in atTop, ∀ x ∈ W,
      |f x i j - F n x i j| < 1 := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
      (Metric.tendstoUniformlyOn_iff.mp hconv 1 zero_lt_one)
  have hbound : ∀ᶠ n in atTop, ∀ᵐ x ∂volume,
      |F n x i j * phi x| ≤ K.indicator (fun _ => (C + 1) * B) x := by
    filter_upwards [hnear] with n hn
    filter_upwards with x
    by_cases hxK : x ∈ K
    · have hFx : |F n x i j| ≤ C + 1 := by
        have hd : |f x i j - F n x i j| < 1 := hn x (hKW (by simpa [hK] using hxK))
        calc
          |F n x i j| = |(F n x i j - f x i j) + f x i j| := by ring_nf
          _ ≤ |F n x i j - f x i j| + |f x i j| := abs_add_le _ _
          _ = |f x i j - F n x i j| + |f x i j| := by rw [abs_sub_comm]
          _ ≤ 1 + C := by linarith [hC x hxK]
          _ = C + 1 := by ring
      rw [Set.indicator_of_mem hxK, abs_mul]
      exact mul_le_mul hFx (hB x) (abs_nonneg _) (by linarith)
    · have hphiZero : phi x = 0 := by
        by_contra hzero
        apply hxK
        rw [hK]
        exact subset_closure hzero
      simp [Set.indicator_of_notMem hxK, hphiZero]
  have hDint : Integrable (K.indicator (fun _ => (C + 1) * B)) volume :=
    (integrable_indicator_iff hKmeas).mpr
      (integrableOn_const hKcompact.measure_lt_top.ne)
  have hlim : ∀ᵐ x ∂volume, Tendsto
      (fun n => F n x i j * phi x) atTop (𝓝 (f x i j * phi x)) := by
    filter_upwards with x
    by_cases hxK : x ∈ K
    · exact (hconv.tendsto_at (hKW (by simpa [hK] using hxK))).mul_const (phi x)
    · have hphiZero : phi x = 0 := by
        by_contra hzero
        apply hxK
        rw [hK]
        exact subset_closure hzero
      simp [hphiZero]
  have ht := tendsto_integral_filter_of_dominated_convergence
    (K.indicator (fun _ => (C + 1) * B))
    (Filter.Eventually.of_forall fun n =>
      (integrable_entry_mul_probe i j hphi (F n)).aestronglyMeasurable)
    hbound hDint hlim
  simpa only [entryTestR] using ht

private theorem tendsto_entryTestR_finiteLowerCutoff_cutoff (m : ℤ)
    (omega : CutoffSample d) (i j : Fin d) (phi : Vec d → ℝ)
    (hphi : IsProbeR phi) :
    Tendsto
      (fun q : ℕ => entryTestR i j phi (finiteLowerCutoff m q omega.1))
      atTop (𝓝 (entryTestR i j phi (cutoff m omega))) := by
  obtain ⟨ell, hell⟩ := exists_openOriginCube_of_isCompact (d := d) hphi.hasCompactSupport
  exact tendsto_entryTestR_of_tendstoUniformlyOn
    (fun q => finiteLowerCutoff m q omega.1) (cutoff m omega) i j phi hphi
    (openCubeSet (originCube d ell))
    (lowerTailGood_tendstoUniformlyOn_finiteLowerCutoff_entry omega.2 ell m i j)
    (continuous_cutoff_entry m omega i j) hell

/-- Every supported integral observation of the genuine lower-infinite cutoff
is measurable from the completed lower-shell local sigma-field. -/
theorem measurable_entryTestR_cutoff_local (M : ABKModel d) (m : ℤ)
    (U : Set (Vec d)) (i j : Fin d) {phi : Vec d → ℝ}
    (hphi : IsProbeR phi) (hphiSupport : Function.support phi ⊆ U) :
    @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) (borel ℝ)
      (fun omega => entryTestR i j phi (cutoff m omega)) := by
  let g : CutoffSample d → ℝ := fun omega => limsup
    (fun q : ℕ => entryTestR i j phi (finiteLowerCutoff m q omega.1)) atTop
  have hfinite : ∀ q : ℕ,
      @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) (borel ℝ)
        (fun omega => entryTestR i j phi (finiteLowerCutoff m q omega.1)) := by
    intro q
    exact (measurable_entryTestR_from_LocalSigmaR U i j hphi hphiSupport).comp
      (measurable_finiteLowerCutoff_on_cutoffSample_local M m q U)
  have hg : @Measurable (CutoffSample d) ℝ (cutoffSampleLocalSigma M m U) (borel ℝ) g :=
    Measurable.limsup hfinite
  have heq : (fun omega : CutoffSample d => entryTestR i j phi (cutoff m omega)) = g := by
    funext omega
    exact (tendsto_entryTestR_finiteLowerCutoff_cutoff m omega i j phi hphi).limsup_eq.symm
  rw [heq]
  exact hg

/-- The genuine cutoff is measurable into CoarseGraining's integral-local
sigma-field from the completed lower-shell information.  This is the local
observable A needed for the eventual range proof; it is not a pointwise
restriction claim. -/
theorem measurable_cutoff_local (M : ABKModel d) (m : ℤ) (U : Set (Vec d)) :
    @Measurable (CutoffSample d) (RegCoeffField d)
      (cutoffSampleLocalSigma M m U) (LocalSigmaR U) (cutoff m) := by
  change @Measurable (CutoffSample d) (RegCoeffField d)
    (cutoffSampleLocalSigma M m U)
    (MeasurableSpace.generateFrom
      {s | ∃ (i j : Fin d) (phi : Vec d → ℝ), IsProbeR phi ∧
        Function.support phi ⊆ U ∧ ∃ t : Set ℝ, MeasurableSet t ∧
          s = entryTestR i j phi ⁻¹' t})
    (cutoff m)
  refine @measurable_generateFrom (CutoffSample d) (RegCoeffField d)
    (cutoffSampleLocalSigma M m U) _ _ ?_
  rintro s ⟨i, j, phi, hphi, hphiSupport, t, ht, rfl⟩
  exact (measurable_entryTestR_cutoff_local M m U i j hphi hphiSupport) ht

end

end Algsuperdiff.Section3.Cutoff
