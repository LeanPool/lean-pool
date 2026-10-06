/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfSlab
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.WeakContL3Support
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformCutoffFamilySeparated

/-!
# Time increments of solenoidal pairings for the forced regularized solutions

The forced regularized solutions of `lem:regularised-forced` are only
continuous `L²` mild solutions, so the time regularity of a spatial pairing
comes from the weak momentum identity `eq:reg-momentum-forced`, as in
`lem:forced-equicontinuity`. For a smooth, compactly supported,
divergence-free spatial field `w`, testing the identity with `η(t) w(x)` shows
that `t ↦ ∫ u(t)·w` has the weak time derivative
`∫ ((J u)_j u_i ∂_j w_i - (Du)_{ij} ∂_j w_i + f·w)`: the pressure drops out.
Continuity of the pairing then identifies each increment from time `0` with
the space-time integral of this flux.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The flux density of the forced momentum identity against a spatial test
field `wc`: transport, viscous and force contributions. -/
@[expose]
def forcedHopfPairingFlux (J U f : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (wc : Fin 3 → Vec3 → ℝ)
    (z : ParabolicPoint) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, J z j * U z i * spatialDeriv (wc i) j z.1
    - ∑ i : Fin 3, ∑ j : Fin 3, D z i j * spatialDeriv (wc i) j z.1
    + ∑ i : Fin 3, f z i * wc i z.1

/-- The transport term of two `L³` fields against bounded coefficients is
integrable on a finite measure space. -/
theorem forcedHopf_transport_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {V W : α → Vec3} {φ : Fin 3 → Fin 3 → α → ℝ}
    (hV : MemLp V 3 μ) (hW : MemLp W 3 μ) (hφ : ∀ i j, MemLp (φ i j) ∞ μ) :
    Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3, V x j * W x i * φ i j x) μ := by
  have : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple 3 3 (3 / 2) := by
      exact ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
      hreal.ennrealOfReal
  have h32 : (1 : ℝ≥0∞) ≤ 3 / 2 := by
    rw [← CKN.ofReal_threeHalves]
    exact ENNReal.one_le_ofReal.mpr (by norm_num)
  refine integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ?_))
  have h : MemLp (fun x => V x j * W x i) (3 / 2 : ℝ≥0∞) μ := (hV.eval j).mul (hW.eval i)
  exact stability_integrable_mul_bounded_test μ h32 h (hφ i j)

/-- A continuous compactly supported spatial function is bounded on
space-time. -/
theorem forcedHopf_memLp_top_spatial {μ : Measure ParabolicPoint}
    {g : Vec3 → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    MemLp (fun z : ParabolicPoint => g z.1) ∞ μ := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  refine memLp_top_of_bound ?_ C (ae_of_all _ fun z => hC z.1)
  exact (hg.measurable.comp measurable_fst).aestronglyMeasurable

/-- The slab `K × (0,T)` over a compact spatial set has finite measure. -/
theorem forcedHopf_slab_isFiniteMeasure {K : Set Vec3} (hK : IsCompact K)
    (T : ℝ) :
    IsFiniteMeasure ((volume : Measure ParabolicPoint).restrict
      (spaceTimeSet K (Ioo 0 T))) := by
  refine isFiniteMeasure_restrict.mpr ?_
  change (volume : Measure (Vec3 × ℝ)) (K ×ˢ Ioo 0 T) ≠ ⊤
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top hK.measure_lt_top.ne measure_Ioo_lt_top.ne

/-- The spatial derivatives of a smooth compactly supported spatial function
are bounded on space-time. -/
theorem forcedHopf_spatialDeriv_memLp_top {μ : Measure ParabolicPoint}
    {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (j : Fin 3) :
    MemLp (fun z : ParabolicPoint => spatialDeriv g j z.1) ∞ μ :=
  forcedHopf_memLp_top_spatial ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hgc.fderiv_apply (𝕜 := ℝ) _)

/-- The flux density is integrable on the slab over a compact spatial set
carrying the test field. -/
theorem forcedHopf_pairingFlux_integrable
    {T : ℝ} {J U f : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {wc : Fin 3 → Vec3 → ℝ} (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i))
    {K : Set Vec3} (hK : IsCompact K) (hwK : ∀ i, tsupport (wc i) ⊆ K)
    (hJ : MemLp J 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hU : MemLp U 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hD : MemLp D 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hf : MemLp f 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    Integrable (forcedHopfPairingFlux J U f D wc)
      (volume.restrict (spaceTimeSet K (Ioo 0 T))) := by
  have hwc : ∀ i, HasCompactSupport (wc i) := fun i =>
    IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (hwK i)
  let νK : Measure ParabolicPoint := volume.restrict (spaceTimeSet K (Ioo 0 T))
  have : IsFiniteMeasure νK := forcedHopf_slab_isFiniteMeasure hK T
  have hνK : νK ≤ volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    Measure.restrict_mono_set volume (Set.prod_mono (subset_univ K) subset_rfl)
  have hUK : MemLp U 3 νK := hU.mono_measure hνK
  have hJK : MemLp J 3 νK := hJ.mono_measure hνK
  have hDK : MemLp D 2 νK := hD.mono_measure hνK
  have hfK : MemLp f 2 νK := hf.mono_measure hνK
  have hwtop : ∀ i, MemLp (fun z : ParabolicPoint => wc i z.1) ∞ νK := fun i =>
    forcedHopf_memLp_top_spatial (hw i).continuous (hwc i)
  have hdwtop : ∀ i j, MemLp (fun z : ParabolicPoint => spatialDeriv (wc i) j z.1) ∞ νK :=
    fun i j => forcedHopf_spatialDeriv_memLp_top (hw i) (hwc i) j
  exact ((forcedHopf_transport_integrable νK hJK hUK hdwtop).sub
    (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      stability_integrable_mul_bounded_test νK (by norm_num)
        ((hDK.eval i).eval j) (hdwtop i j))))).add
    (integrable_finsetSum _ (fun i _ =>
      stability_integrable_mul_bounded_test νK (by norm_num) (hfK.eval i) (hwtop i)))

/-- The increment of a solenoidal pairing of a forced regularized solution
from time `0` is the space-time integral of the flux, by the weak momentum
identity `eq:reg-momentum-forced` tested with `η(t) w(x)` and the
continuity of the pairing. -/
theorem forcedHopf_regPairing_sub_eq
    {T : ℝ} (hT : 0 < T)
    {U J f : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {P : ParabolicPoint → ℝ}
    {wc : Fin 3 → Vec3 → ℝ} (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i))
    {K : Set Vec3} (hK : IsCompact K) (hwK : ∀ i, tsupport (wc i) ⊆ K)
    (hdivw : ∀ x, ∑ i : Fin 3, spatialDeriv (wc i) i x = 0)
    (hU : MemLp U 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hJ : MemLp J 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hD : MemLp D 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hf : MemLp f 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hcont : ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, U (x, t) i * wc i x)
      (Ici 0))
    (hmom : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, U z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              J z j * U z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              D z i j * spatialPartial (fun y => φ y i) j z
          - P z * (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0) :
    ∀ t ∈ Ioo 0 T,
      (∫ x, ∑ i : Fin 3, U (x, t) i * wc i x) -
          ∫ x, ∑ i : Fin 3, U (x, 0) i * wc i x =
        ∫ z in spaceTimeSet K (Ioo 0 t), forcedHopfPairingFlux J U f D wc z := by
  -- vanishing of the test off `K`
  have hwc : ∀ i, HasCompactSupport (wc i) := fun i =>
    IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (hwK i)
  have hw0 : ∀ i x, x ∉ K → wc i x = 0 := fun i x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hwK i h))
  have hdw0 : ∀ i j x, x ∉ K → spatialDeriv (wc i) j x = 0 := by
    intro i j x hx
    have h : fderiv ℝ (wc i) x = 0 := by
      by_contra hne
      exact hx (hwK i (support_fderiv_subset ℝ (Function.mem_support.mpr hne)))
    simp only [spatialDeriv, h, zero_apply]
  -- the slab over `K`
  let νK : Measure ParabolicPoint := volume.restrict (spaceTimeSet K (Ioo 0 T))
  have : IsFiniteMeasure νK := forcedHopf_slab_isFiniteMeasure hK T
  have hνK : νK ≤ volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    Measure.restrict_mono_set volume (Set.prod_mono (subset_univ K) subset_rfl)
  have hUK : MemLp U 3 νK := hU.mono_measure hνK
  have hwtop : ∀ i, MemLp (fun z : ParabolicPoint => wc i z.1) ∞ νK := fun i =>
    forcedHopf_memLp_top_spatial (hw i).continuous (hwc i)
  let F : ParabolicPoint → ℝ := fun z => ∑ i : Fin 3, U z i * wc i z.1
  let G : ParabolicPoint → ℝ := forcedHopfPairingFlux J U f D wc
  have hFint : Integrable F νK := integrable_finsetSum _ (fun i _ =>
    stability_integrable_mul_bounded_test νK (by norm_num) (hUK.eval i) (hwtop i))
  have hGint : Integrable G νK :=
    forcedHopf_pairingFlux_integrable hw hK hwK hJ hU hD hf
  have hFprod : Integrable (fun q : Vec3 × ℝ => F q)
      ((volume.restrict K).prod (volume.restrict (Ioo 0 T))) := by
    rw [← forcedHopf_slab_measure_eq_prod]
    exact hFint
  have hGprod : Integrable (fun q : Vec3 × ℝ => G q)
      ((volume.restrict K).prod (volume.restrict (Ioo 0 T))) := by
    rw [← forcedHopf_slab_measure_eq_prod]
    exact hGint
  -- the product-test identity
  have hFoff : ∀ z : ParabolicPoint, z.1 ∉ K → F z = 0 := by
    intro z hz
    simp only [F, hw0 _ _ hz, mul_zero, Finset.sum_const_zero]
  have hGoff : ∀ z : ParabolicPoint, z.1 ∉ K → G z = 0 := by
    intro z hz
    simp only [G, forcedHopfPairingFlux, hw0 _ _ hz, hdw0 _ _ _ hz, mul_zero,
      Finset.sum_const_zero, sub_zero, add_zero]
  have hweak : ∀ η : ℝ → ℝ, IsIntervalTest (Ioo 0 T) η →
      (∫ q, -(F q * deriv η q.2) - G q * η q.2
        ∂((volume.restrict K).prod (volume.restrict (Ioo 0 T)))) = 0 := by
    intro η hη
    obtain ⟨hηs, hηc, hηsupp⟩ := hη
    let Φ : ParabolicPoint → Vec3 := fun z i => wc i z.1 * η z.2
    have hsupp : Function.support (show Vec3 × ℝ → Vec3 from Φ) ⊆ K ×ˢ tsupport η := by
      intro z hz
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (Function.mem_support.mp hz)
      have hi' : wc i z.1 * η z.2 ≠ 0 := hi
      exact ⟨hwK i (subset_tsupport _ (Function.mem_support.mpr (left_ne_zero_of_mul hi'))),
        subset_tsupport _ (Function.mem_support.mpr (right_ne_zero_of_mul hi'))⟩
    have hΦtest : Φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) := by
      refine ⟨?_, ?_, ?_⟩
      · exact contDiff_pi.2 (fun i => ((hw i).comp contDiff_fst).mul (hηs.comp contDiff_snd))
      · exact HasCompactSupport.of_support_subset_isCompact (hK.prod hηc) hsupp
      · refine (closure_minimal hsupp (hK.isClosed.prod (isClosed_tsupport η))).trans ?_
        exact Set.prod_mono (subset_univ K) (hηsupp.trans Ioo_subset_Ioi_self)
    have htime : ∀ i (z : ParabolicPoint),
        timePartial (fun y => Φ y i) z = wc i z.1 * deriv η z.2 := fun i z =>
      CKN.Core.Endgame.timePartial_separatedProduct (wc i) hηs z
    have hspace : ∀ i j (z : ParabolicPoint),
        spatialPartial (fun y => Φ y i) j z = spatialDeriv (wc i) j z.1 * η z.2 :=
      fun i j z => CKN.Core.Endgame.spatialPartial_separatedProduct η (hw i) j z
    have hpoint : ∀ z : ParabolicPoint,
        (-(∑ i : Fin 3, U z i * timePartial (fun y => Φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              J z j * U z i * spatialPartial (fun y => Φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              D z i j * spatialPartial (fun y => Φ y i) j z
          - P z * (∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z)
          - ∑ i : Fin 3, f z i * Φ z i =
        -(F z * deriv η z.2) - G z * η z.2 := by
      intro z
      have hdiv : ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z = 0 := by
        simp only [hspace, ← Finset.sum_mul, hdivw, zero_mul]
      rw [hdiv]
      simp only [htime, hspace, F, G, forcedHopfPairingFlux, Φ, Fin.sum_univ_three]
      ring
    have hid := hmom Φ hΦtest
    simp only [hpoint] at hid
    have hsub : spaceTimeSet K (Ioo 0 T) ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
      Set.prod_mono (subset_univ K) Ioo_subset_Ioi_self
    have hmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))) :=
      MeasurableSet.univ.prod measurableSet_Ioi
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub] at hid
    · change ∫ q, -(F q * deriv η q.2) - G q * η q.2 ∂((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet K (Ioo 0 T)) : Measure (Vec3 × ℝ)) = 0 at hid
      rw [forcedHopf_slab_measure_eq_prod] at hid
      exact hid
    · intro z hz
      by_cases hzK : z.1 ∈ K
      · have hzt : z.2 ∉ tsupport η := fun h => hz.2 ⟨hzK, hηsupp h⟩
        have hη0 : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hzt
        have hdη0 : deriv η z.2 = 0 := by
          by_contra hne
          exact hzt (support_deriv_subset (Function.mem_support.mpr hne))
        rw [hη0, hdη0]
        ring
      · rw [hFoff z hzK, hGoff z hzK]
        ring
  obtain ⟨hFloc, hGon, hderiv⟩ :=
    weakContL3_productWeakDeriv (volume.restrict K) hFprod hGprod hweak
  -- the pairing is the integral over `K`
  let g : ℝ → ℝ := fun t => ∫ x, ∑ i : Fin 3, U (x, t) i * wc i x
  let h : ℝ → ℝ := fun t => ∫ x in K, G (x, t)
  have hgK : (fun t => ∫ x in K, F (x, t)) = g := by
    funext t
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hFoff (x, t) hx)
  rw [hgK] at hFloc hderiv
  obtain ⟨C, hC⟩ := eq_const_add_intervalIntegral_of_continuous_weakDeriv hT
    (show T / 2 ∈ Ioo 0 T from ⟨by linarith only [hT], by linarith only [hT]⟩)
    hFloc hGon.locallyIntegrableOn hderiv (hcont.mono (fun x hx => (show x ∈ Ici (0 : ℝ) from hx.1.le)))
  let h' : ℝ → ℝ := (Ioo 0 T).indicator h
  have hh' : Integrable h' := forcedHopf_integrable_timeDensity K T G hGint
  have hint_eq : ∀ x ∈ Ioo 0 T, ∫ s in T / 2..x, h s = ∫ s in T / 2..x, h' s := by
    intro x hx
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hs' : s ∈ Ioo 0 T := by
      rcases Set.mem_uIcc.mp hs with h1 | h1
      · exact ⟨by linarith only [h1.1, hT], by linarith only [h1.2, hx.2]⟩
      · exact ⟨by linarith only [h1.1, hx.1], by linarith only [h1.2, hT]⟩
    exact (indicator_of_mem hs' h).symm
  let R : ℝ → ℝ := fun x => C + ∫ s in T / 2..x, h' s
  have hRc : Continuous R := continuous_const.add (hh'.continuous_primitive _)
  have hgR : ∀ x ∈ Ioo 0 T, g x = R x := fun x hx => by
    change g x = C + ∫ s in T / 2..x, h' s
    rw [← hint_eq x hx]
    exact hC x hx
  have hg0 : g 0 = R 0 := by
    have h1 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
      ((hcont 0 Set.self_mem_Ici).mono Ioi_subset_Ici_self).tendsto
    have h2 : Tendsto R (𝓝[>] 0) (𝓝 (R 0)) := hRc.continuousWithinAt.tendsto
    have heq : g =ᶠ[𝓝[>] 0] R := by
      filter_upwards [Ioo_mem_nhdsGT hT] with x hx using hgR x hx
    exact tendsto_nhds_unique (h1.congr' heq) h2
  intro t ht
  have hstep : g t - g 0 = ∫ s in (0 : ℝ)..t, h' s := by
    rw [hgR t ht, hg0]
    change (C + ∫ s in T / 2..t, h' s) - (C + ∫ s in T / 2..0, h' s) = _
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      hh'.intervalIntegrable hh'.intervalIntegrable]
  exact hstep.trans (forcedHopf_setIntegral_slab_eq_intervalIntegral K T G hGint t
    ⟨ht.1.le, ht.2.le⟩).symm

end CKN.Leray

end
