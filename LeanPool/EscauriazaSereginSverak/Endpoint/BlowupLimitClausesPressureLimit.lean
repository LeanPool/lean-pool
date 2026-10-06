/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyPressure
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureRemainder

/-!
# The pressure limit of the blow-up sequence, with its split

Clause (c) of `prop:blowup-limit` for the pressure: the limit pressure is the
assembled whole-space pressure `P[u ⊗ u]` of the limit velocity, the rescaled
Riesz parts `p₁^k` of the fixed split of `lem:pressure-split` converge to it,
the rescaled harmonic remainders `p₂^k` tend to zero, and the rescaled
pressures `p^k` converge to it, in `L^{3/2}` of every bounded past cylinder.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem blowupLimitClausesPressure_velocity_Lthree_of_slice_bounds
    {u : ParabolicPoint → Vec3} (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) (Mᵤ : ℝ≥0∞) (hMᵤ : Mᵤ < ⊤)
    (hsourceU : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ Mᵤ)
    (vm : Vec3 × ℝ → Vec3) (hvmM : Measurable vm)
    (hvm : (fun z : Vec3 × ℝ => blowupVelocity x₀ t₀ r u z) =ᵐ[volume] vm) :
    (∀ᵐ t ∂(volume : Measure ℝ),
      eLpNorm (fun x : Vec3 => vm (x,t)) 3 volume ≤ Mᵤ) ∧ MemLp vm 3 volume := by
  have hprod : ∀ᵐ z ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
      blowupVelocity x₀ t₀ r u z = vm z := by
    rw [← Measure.volume_eq_prod]
    exact hvm
  have hvmSlicesEq := blowupLimitAssembly_ae_ae_of_ae_prod_swap hprod
  have hvmSlice : ∀ᵐ t ∂(volume : Measure ℝ),
      eLpNorm (fun x : Vec3 => vm (x,t)) 3 volume ≤ Mᵤ := by
    filter_upwards [hvmSlicesEq, blowupLimitAssemblyPressure_velocity_slice_bound u Mᵤ
      hsourceU x₀ t₀ r hr] with t hte htb
    calc
      eLpNorm (fun x : Vec3 => vm (x,t)) 3 volume =
          eLpNorm (fun x : Vec3 => blowupVelocity x₀ t₀ r u (x,t)) 3 volume :=
        eLpNorm_congr_ae hte.symm
      _ ≤ eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            (blowupVelocity x₀ t₀ r u (x,t))) 3 volume := by
        apply blowupLimitAssemblyPressure_slice_le_norm
        exact (hvmM.comp measurable_prodMk_right).aestronglyMeasurable.congr hte.symm
      _ ≤ Mᵤ := htb
  let J : Set ℝ := CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0)
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hJsub : J ⊆ Icc ((-1 - t₀) / r ^ 2) ((-t₀) / r ^ 2) := by
    intro t ht
    have ht' : t₀ + r ^ 2 * t ∈ Ioo (-1 : ℝ) 0 := ht
    constructor
    · rw [div_le_iff₀ hr2]
      linarith only [ht'.1]
    · rw [le_div_iff₀ hr2]
      linarith only [ht'.2]
  have hJfin : volume J < ⊤ :=
    lt_of_le_of_lt (measure_mono hJsub) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hJm : MeasurableSet J := by
    have hmeas : Measurable (CKN.scalingTime r t₀) := by
      unfold CKN.scalingTime
      fun_prop
    exact measurableSet_Ioo.preimage hmeas
  have hSm : MeasurableSet ((Set.univ : Set Vec3) ×ˢ J) := MeasurableSet.univ.prod hJm
  have hzero : ∀ z : Vec3 × ℝ, z ∉ (Set.univ : Set Vec3) ×ˢ J →
      blowupVelocity x₀ t₀ r u z = 0 := by
    intro z hz
    let w : ParabolicPoint := (x₀ + r • z.1, t₀ + r ^ 2 * z.2)
    have hvw : blowupVelocity x₀ t₀ r u z = r • goodPointDomain.indicator u w := rfl
    have hnot : w ∉ goodPointDomain := fun hmem => hz ⟨mem_univ _, hmem.2⟩
    rw [hvw, indicator_of_notMem hnot, smul_zero]
  have hind : vm =ᵐ[volume] ((Set.univ : Set Vec3) ×ˢ J).indicator vm := by
    filter_upwards [hvm] with z hz
    by_cases hzS : z ∈ (Set.univ : Set Vec3) ×ˢ J
    · rw [indicator_of_mem hzS]
    · rw [indicator_of_notMem hzS, ← hz, hzero z hzS]
  have hsliceJ : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x : Vec3 => vm (x,t)) 3 volume := by
    filter_upwards [ae_restrict_of_ae hvmSlice] with t ht
    exact ht
  have hbound := blowupLimitAssemblyPressure_memLp_three_of_slices hvmM hsliceJ
    (Set.univ : Set Vec3)
  have hfin : (volume J * Mᵤ ^ (3 : ℝ)) ^ (1 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_lt_top hJfin (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        hMᵤ.ne)).ne
  have hres : MemLp vm 3 (volume.restrict ((Set.univ : Set Vec3) ×ˢ J)) :=
    memLp_iff.2 (hbound.trans_lt hfin)
  exact ⟨hvmSlice, ((memLp_indicator_iff_restrict hSm).2 hres).ae_eq hind.symm⟩

/-- The pressure-limit step of `prop:blowup-limit`, clause (c), for the
assembled whole-space pressure of the limit: the rescaled fixed Riesz
pressures `p₁^k` converge to it, the rescaled harmonic remainders `p₂^k`
tend to zero, and so do the differences `p^k - q`, strongly in `L^{3/2}` of
every bounded past cylinder. -/
theorem blowupLimitClauses_pressure_limit
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0))
    (U : ParabolicPoint → Vec3) (hU : Measurable U)
    (MU : ℝ≥0∞) (hMU : MU < ⊤)
    (hUslice : ∀ᵐ t ∂(volume.restrict (Iio (0 : ℝ))),
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (U (x, t))) 3 volume ≤ MU)
    (hconv : ∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
      Tendsto (fun k => eLpNorm (fun z => blowupVelocity x₀ t₀ (r k) u z - U z) 3
        (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0))) atTop (nhds 0))
    (hG : ∀ n i j, MemLp (blowupLimitAssemblyPressureWindowTensor U n i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) :
    let q : ParabolicPoint → ℝ := blowupLimitAssemblyPressureLimit U hG
    let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure (pressureSplitTensor u)
      (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)
    (∀ T : ℝ, 0 < T → MemLp q (3 / 2 : ℝ≥0∞)
        (volume.restrict (spaceTimeSet Set.univ (Ioo (-T) 0)))) ∧
      (∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
        Tendsto (fun k => eLpNorm (fun z => blowupRieszPressure x₀ t₀ (r k) p₁ z - q z)
          (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
          atTop (nhds 0)) ∧
      (∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
        Tendsto (fun k => eLpNorm (blowupPressureRemainder x₀ t₀ (r k) p p₁)
          (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
          atTop (nhds 0)) ∧
      (∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
        Tendsto (fun k => eLpNorm (fun z => blowupPressure x₀ t₀ (r k) p z - q z)
          (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
          atTop (nhds 0)) := by
  obtain ⟨_, hind, hp₁, ⟨Mᵤ, hMᵤ, hsourceU⟩, ⟨Mₚ, hMₚ, hsourceP⟩, hp₂, hharm⟩ :=
    blowupLimitAssembly_source_pressure_data hu hDu hp hL2 henergy hpLp hL3 hgrad
      hS2 hS3
  set hF := pressureSplitTensor_memLp hu hDu henergy hL3 hgrad with hFdef
  set p₁ := pressureSplitRieszPressure (pressureSplitTensor u) hF with hp₁def
  -- the limit velocity: slices and window tensors
  have hUsliceVec : ∀ a : ℝ, ∀ᵐ t ∂volume.restrict (Ioo a 0),
      eLpNorm (fun x : Vec3 => U (x,t)) 3 volume ≤ MU := by
    intro a
    have h := ae_restrict_of_ae_restrict_of_subset
      (fun t (ht : t ∈ Ioo a 0) => (ht.2 : t < 0)) hUslice
    filter_upwards [h] with t ht
    exact (blowupLimitAssemblyPressure_slice_le_norm
      (hU.comp measurable_prodMk_right).aestronglyMeasurable).trans ht
  have hwindowFin : ∀ n : ℕ,
      (volume (Ioo (-((n : ℝ) + 1)) (0 : ℝ)) * MU ^ (3 : ℝ)) ^ (1 / 3 : ℝ) < ⊤ := by
    intro n
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    apply (ENNReal.mul_lt_top _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      hMU.ne)).ne
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  set q : Vec3 × ℝ → ℝ := blowupLimitAssemblyPressureLimit U hG with hqdef
  intro q' p₁'
  have hP1 : ∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
      Tendsto (fun k => eLpNorm (fun z => blowupRieszPressure x₀ t₀ (r k) p₁ z - q z)
        (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
        atTop (nhds 0) := by
      intro R hR a ha
      set m : ℕ := ⌈-a⌉₊ with hmdef
      set a' : ℝ := -((m : ℝ) + 1) with ha'def
      have hma : -a ≤ (m : ℝ) := Nat.le_ceil _
      have ha'a : a' < a := by
        simp only [a']
        linarith only [hma]
      have ha' : a' < 0 := ha'a.trans ha
      -- measurable versions of the blow-up velocities
      have hvaesm : ∀ k, AEStronglyMeasurable (blowupVelocity x₀ t₀ (r k) u) volume :=
        fun k => blowupRescaledVelocity_aestronglyMeasurable
          (goodPointDomain.indicator u) hind x₀ t₀ (r k) (hr k)
      let vm : ℕ → Vec3 × ℝ → Vec3 := fun k => (hvaesm k).mk _
      have hvmM : ∀ k, Measurable (vm k) := fun k =>
        (hvaesm k).stronglyMeasurable_mk.measurable
      have hvm : ∀ k, (fun z : Vec3 × ℝ => blowupVelocity x₀ t₀ (r k) u z) =ᵐ[volume]
          vm k := fun k => (hvaesm k).ae_eq_mk
      have hvmData : ∀ k,
          (∀ᵐ t ∂(volume : Measure ℝ),
            eLpNorm (fun x : Vec3 => vm k (x,t)) 3 volume ≤ Mᵤ) ∧
          MemLp (vm k) 3 volume := fun k =>
        blowupLimitClausesPressure_velocity_Lthree_of_slice_bounds x₀ t₀ (r k)
          (hr k) Mᵤ hMᵤ hsourceU (vm k) (hvmM k) (hvm k)
      have hvmSlice := fun k => (hvmData k).1
      have hvmMem := fun k => (hvmData k).2
      have hFm : ∀ k i j, MemLp (fun z => vm k z i * vm k z j)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume := fun k =>
        blowup_velocity_tensor_memLp (vm k) (hvmMem k)
      have hFv : ∀ k i j, MemLp (fun z : Vec3 × ℝ =>
          blowupVelocity x₀ t₀ (r k) u z i * blowupVelocity x₀ t₀ (r k) u z j)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
        intro k i j
        refine (hFm k i j).ae_eq ?_
        filter_upwards [hvm k] with z hz
        rw [hz]
      have hFeq : ∀ k i j, (fun z : Vec3 × ℝ =>
          blowupVelocity x₀ t₀ (r k) u z i * blowupVelocity x₀ t₀ (r k) u z j) =ᵐ[volume]
          (fun z => vm k z i * vm k z j) := by
        intro k i j
        filter_upwards [hvm k] with z hz
        rw [hz]
      -- convergence of the whole-space pressures on the enlarged window
      set N : ℝ≥0∞ := max Mᵤ MU with hNdef
      have hN : N < ⊤ := max_lt hMᵤ hMU
      have hvmSlice' : ∀ k, ∀ᵐ t ∂volume.restrict (Ioo a' 0),
          eLpNorm (fun x : Vec3 => vm k (x,t)) 3 volume ≤ N := by
        intro k
        filter_upwards [ae_restrict_of_ae (hvmSlice k)] with t ht
        exact ht.trans (le_max_left _ _)
      have hUslice' : ∀ᵐ t ∂volume.restrict (Ioo a' 0),
          eLpNorm (fun x : Vec3 => U (x,t)) 3 volume ≤ N := by
        filter_upwards [hUsliceVec a'] with t ht
        exact ht.trans (le_max_right _ _)
      have hconv' : ∀ L : ℝ, 0 < L → Tendsto (fun k => eLpNorm (fun z => vm k z - U z) 3
          (volume.restrict (CKN.euclideanBall (0 : Vec3) L ×ˢ Ioo a' 0))) atTop (nhds 0) := by
        intro L hL
        rw [euclideanBall_eq_vec3Ball hL]
        refine (hconv L hL a' ha').congr fun k => ?_
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_of_ae (hvm k)] with z hz
        rw [hz]
      have hriesz := blowupLimitAssemblyPressure_riesz_tendsto vm hvmM U hU ha' hN
        hvmSlice' hUslice' hconv' hFm (hG m) hR
      -- transfer to the rescaled fixed pressure and to the limit pressure
      have hsub : vec3Ball (0 : Vec3) R ×ˢ Ioo a 0 ⊆
          CKN.euclideanBall (0 : Vec3) R ×ˢ Ioo a' 0 := by
        rw [euclideanBall_eq_vec3Ball hR]
        exact prod_mono subset_rfl (Ioo_subset_Ioo_left ha'a.le)
      have hqeq : q =ᵐ[volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)]
          CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
            (blowupLimitAssemblyPressureWindowTensor U m) (hG m) := by
        have h := blowupLimitAssemblyPressureLimit_ae_eq U hG (-a)
        rw [neg_neg] at h
        exact ae_restrict_of_ae_restrict_of_subset
          (prod_mono (subset_univ _) subset_rfl) h
      have h₁ : Tendsto (fun k => eLpNorm
          (fun z => blowupRieszPressure x₀ t₀ (r k) p₁ z - q z)
          (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
          atTop (nhds 0) := by
        rw [← CKN.ofReal_threeHalves]
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hriesz
          (fun k => zero_le) (fun k => ?_)
        have hid := blowupLimitAssemblyPressure_riesz_rescale u hF hp₁ Mₚ hMₚ hsourceP
          x₀ t₀ (r k) (hr k) (hFv k)
        have hcongr := blowupLimitAssemblyPressure_rieszPressure_congr_ae (hFv k) (hFm k)
          (hFeq k)
        calc
          eLpNorm (fun z => blowupRieszPressure x₀ t₀ (r k) p₁ z - q z)
              (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)) =
              eLpNorm (fun z =>
                CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
                  (fun i j z => vm k z i * vm k z j) (hFm k) z -
                CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
                  (blowupLimitAssemblyPressureWindowTensor U m) (hG m) z)
              (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)) := by
            apply eLpNorm_congr_ae
            filter_upwards [ae_restrict_of_ae hid, hqeq] with z hz hzq
            rw [hz, hzq, hcongr]
          _ ≤ _ := eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
      exact h₁
  refine ⟨?_, hP1, fun R hR a ha =>
    blowupPressureRemainder_eLpNorm_tendsto_zero_pastBox p p₁ hp₂ hharm x₀ t₀ r hx₀ hr hr0
      R a hR ha, fun R hR a ha =>
    blowupPressure_tendsto_of_riesz p p₁ hp₂ hharm x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha q
      (hP1 R hR a ha)⟩
  · -- integrability on every past slab
    intro T hT
    have hae := blowupLimitAssemblyPressureLimit_ae_eq U hG T
    have hmem : MemLp q (ENNReal.ofReal (3 / 2 : ℝ))
        ((volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo (-T) 0)) :=
      ((CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num) _
        (hG ⌈T⌉₊)).restrict _).ae_eq hae.symm
    rw [CKN.ofReal_threeHalves] at hmem
    exact hmem

end ESS

end
