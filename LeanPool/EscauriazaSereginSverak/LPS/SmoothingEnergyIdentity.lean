/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingEnergyIdentityTime
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingEnergyIdentitySlice
public import LeanPool.EscauriazaSereginSverak.PartV.PvLocalSolutionLerayHopfCore

/-!
# The energy identity for a linear Stokes-type system

Let `v` be a weak solution of `∂ₜv - Δv + div H + ∇q = 0` on `ℝ³ × (c, d)`, tested
against smooth compactly supported vector fields, with `div v = 0` and `v`, its first
and second spatial derivatives, `∂ₜv`, `H` and `q` square integrable. The kinetic
energy `E(t) = ∫ |v(x, t)|² dx` has weak derivative `-2 ∫ |∇v|² + 2 ∫ H : ∇v`; if
moreover `t ↦ v(·, t)` is continuous into `L²` on `[c, d]`, the energy identity holds
between any two times of `[c, d]` (`prop:lps-smoothing`). No regularity of `q`
or `H` beyond square integrability is used.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The weak energy identity: for a weak solution of `∂ₜv - Δv + div H + ∇q = 0` on
`ℝ³ × (c, d)` with `div v = 0`, the kinetic energy `∫ |v(x, t)|² dx` has weak time
derivative `-2 ∫ |∇v|² + 2 ∫ H : ∇v` on `(c, d)` (`prop:lps-smoothing`). -/
theorem lps_energy_hasWeakDerivOn {c d : ℝ}
    {v : ParabolicPoint → Vec3} {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtv : ParabolicPoint → Vec3}
    {H : ParabolicPoint → Fin 3 → Fin 3 → ℝ} {q : ParabolicPoint → ℝ}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d) v Dv D2v Dtv)
    (hv : MemLp v 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDv : MemLp Dv 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hD2v : MemLp D2v 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDtv : MemLp Dtv 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hH : ∀ i j, MemLp (fun z => H z i j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hq : MemLp q 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hdiv : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))),
      ∑ i, Dv z i i = 0)
    (heq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo c d) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo c d),
        (∑ i, Dtv z i * φ z i
          - ∑ i, ∑ j, H z i j * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, Dv z i j * spatialPartial (fun y => φ y i) j z
          - q z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0) :
    HasWeakDerivOn (Ioo c d) (fun t => ∫ x : Vec3, ∑ i, (v (x, t) i) ^ 2)
      (fun t => -2 * (∫ x : Vec3, ∑ i, ∑ j, (Dv (x, t) i j) ^ 2)
        + 2 * (∫ x : Vec3, ∑ i, ∑ j, H (x, t) i j * Dv (x, t) i j)) := by
  have hkin := lps_kineticEnergy_hasWeakDerivOn hderiv hv hDtv
  have hbal := lps_linearStokes_slice_balance_ae hderiv hv hDv hD2v hDtv hH hq hdiv heq
  intro φ hφ
  rw [hkin φ hφ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hbal] with t ht
  simp only [ht]

/-- The kinetic energy of an `L²`-continuous curve of square-integrable slices is
continuous. -/
private theorem lps_sliceEnergy_continuousOn {c d : ℝ} {v : ParabolicPoint → Vec3}
    (hslice : ∀ t ∈ Icc c d, MemLp (fun x : Vec3 => v (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc c d,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => v (x, s) - v (x, t)) 2 volume)
        (nhdsWithin t (Icc c d)) (nhds 0)) :
    ContinuousOn (fun t => ∫ x : Vec3, ∑ i, (v (x, t) i) ^ 2) (Icc c d) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  let N : ℝ → ℝ := fun s =>
    (eLpNorm (fun x : Vec3 => v (x, s) - v (x, t)) 2 volume).toReal
  have hN : Tendsto N (nhdsWithin t (Icc c d)) (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hlim : Tendsto (fun s =>
      3 * (N s * N s) +
        2 * (3 * (N s * (eLpNorm (fun x : Vec3 => v (x, t)) 2 volume).toReal)))
      (nhdsWithin t (Icc c d)) (nhds 0) := by
    have h := ((hN.mul hN).const_mul 3).add
      (((hN.mul_const (eLpNorm (fun x : Vec3 => v (x, t)) 2 volume).toReal).const_mul
        3).const_mul 2)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hdiff : MemLp (fun x : Vec3 => v (x, s) - v (x, t)) 2 volume :=
    (hslice s hs).sub (hslice t ht)
  have hpairInt (f g : Vec3 → Vec3) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
      Integrable (fun x => ∑ i : Fin 3, f x i * g x i) :=
    integrable_finsetSum _ fun i _ =>
      (memLp_pi_iff.1 hf i).integrable_mul (memLp_pi_iff.1 hg i)
  have hsq (f : Vec3 → Vec3) :
      (fun x => ∑ i : Fin 3, (f x i) ^ 2) = fun x => ∑ i : Fin 3, f x i * f x i := by
    funext x
    simp only [sq]
  have hsplit :
      (∫ x : Vec3, ∑ i : Fin 3, (v (x, s) i) ^ 2) -
          ∫ x : Vec3, ∑ i : Fin 3, (v (x, t) i) ^ 2 =
        (∫ x : Vec3, ∑ i : Fin 3,
          (v (x, s) - v (x, t)) i * (v (x, s) - v (x, t)) i) +
          2 * ∫ x : Vec3, ∑ i : Fin 3,
            (v (x, s) - v (x, t)) i * v (x, t) i := by
    rw [hsq (fun x => v (x, s)), hsq (fun x => v (x, t)),
      ← integral_sub (hpairInt _ _ (hslice s hs) (hslice s hs))
        (hpairInt _ _ (hslice t ht) (hslice t ht)),
      ← integral_const_mul, ← integral_add
        (hpairInt (fun x => v (x, s) - v (x, t)) (fun x => v (x, s) - v (x, t)) hdiff hdiff)
        ((hpairInt (fun x => v (x, s) - v (x, t)) (fun x => v (x, t)) hdiff
          (hslice t ht)).const_mul 2)]
    congr 1
    funext x
    simp only [Pi.sub_apply, Fin.sum_univ_three]
    ring
  rw [Real.norm_eq_abs, hsplit]
  refine (abs_add_le _ _).trans (add_le_add (pvLH_pair_le hdiff hdiff) ?_)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (pvLH_pair_le hdiff (hslice t ht)) (by norm_num)

/-- The energy identity between any two times: if moreover every slice `v(·, t)`,
`t ∈ [c, d]`, is square integrable and `t ↦ v(·, t)` is continuous into `L²` on
`[c, d]`, then `E(t) - E(s) = ∫ₛᵗ (-2 ∫ |∇v|² + 2 ∫ H : ∇v)` for `c ≤ s ≤ t ≤ d`
(`prop:lps-smoothing`). -/
theorem lps_energy_eq_intervalIntegral {c d : ℝ} (hcd : c < d)
    {v : ParabolicPoint → Vec3} {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtv : ParabolicPoint → Vec3}
    {H : ParabolicPoint → Fin 3 → Fin 3 → ℝ} {q : ParabolicPoint → ℝ}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d) v Dv D2v Dtv)
    (hv : MemLp v 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDv : MemLp Dv 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hD2v : MemLp D2v 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDtv : MemLp Dtv 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hH : ∀ i j, MemLp (fun z => H z i j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hq : MemLp q 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hdiv : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))),
      ∑ i, Dv z i i = 0)
    (heq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo c d) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo c d),
        (∑ i, Dtv z i * φ z i
          - ∑ i, ∑ j, H z i j * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, Dv z i j * spatialPartial (fun y => φ y i) j z
          - q z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0)
    (hslice : ∀ t ∈ Icc c d, MemLp (fun x : Vec3 => v (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc c d,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => v (x, s) - v (x, t)) 2 volume)
        (nhdsWithin t (Icc c d)) (nhds 0)) :
    ∀ s t : ℝ, c ≤ s → s ≤ t → t ≤ d →
      (∫ x : Vec3, ∑ i, (v (x, t) i) ^ 2) - (∫ x : Vec3, ∑ i, (v (x, s) i) ^ 2) =
        ∫ τ in s..t, (-2 * (∫ x : Vec3, ∑ i, ∑ j, (Dv (x, τ) i j) ^ 2)
          + 2 * (∫ x : Vec3, ∑ i, ∑ j, H (x, τ) i j * Dv (x, τ) i j)) := by
  set E : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i, (v (x, t) i) ^ 2 with hE
  set g : ℝ → ℝ := fun t => -2 * (∫ x : Vec3, ∑ i, ∑ j, (Dv (x, t) i j) ^ 2)
    + 2 * (∫ x : Vec3, ∑ i, ∑ j, H (x, t) i j * Dv (x, t) i j) with hg
  have hweak : HasWeakDerivOn (Ioo c d) E g :=
    lps_energy_hasWeakDerivOn hderiv hv hDv hD2v hDtv hH hq hdiv heq
  have hEcont : ContinuousOn E (Icc c d) := lps_sliceEnergy_continuousOn hslice hcont
  -- the derivative is integrable on the slab
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo c d))
    with hν
  have hDij (i j : Fin 3) :
      MemLp (fun y : Vec3 × ℝ => Dv (parabolicHomeomorph.symm y) i j) 2 ν :=
    (memLp_pi_iff.1 ((memLp_pi_iff.1 (lps_memLp_slab_to_prod hDv)) i)) j
  have hY : Integrable (fun y : Vec3 × ℝ =>
      ∑ i, ∑ j, (Dv (parabolicHomeomorph.symm y) i j) ^ 2) ν :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hDij i j).integrable_sq
  have hZ : Integrable (fun y : Vec3 × ℝ =>
      ∑ i, ∑ j, H (parabolicHomeomorph.symm y) i j * Dv (parabolicHomeomorph.symm y) i j) ν :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (lps_memLp_slab_to_prod (hH i j)).integrable_mul (hDij i j)
  have hgInt : IntegrableOn g (Ioo c d) := by
    have hYt : IntegrableOn (fun t => ∫ x : Vec3, ∑ i, ∑ j, (Dv (x, t) i j) ^ 2) (Ioo c d) :=
      hY.integral_prod_right
    have hZt : IntegrableOn
        (fun t => ∫ x : Vec3, ∑ i, ∑ j, H (x, t) i j * Dv (x, t) i j) (Ioo c d) :=
      hZ.integral_prod_right
    exact (hYt.const_mul (-2)).add (hZt.const_mul 2)
  have hgIcc : IntegrableOn g (Icc c d) := hgInt.congr_set_ae (Ioo_ae_eq_Icc (μ := volume)).symm
  -- the primitive representation on the open interval
  set t₀ : ℝ := (c + d) / 2 with ht₀
  have ht₀mem : t₀ ∈ Ioo c d := ⟨by linarith only [hcd, ht₀], by linarith only [hcd, ht₀]⟩
  have ht₀Icc : t₀ ∈ Icc c d := Ioo_subset_Icc_self ht₀mem
  obtain ⟨C, hC⟩ := eq_const_add_intervalIntegral_of_continuous_weakDeriv hcd ht₀mem
    ((hEcont.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo)
    (hgInt.locallyIntegrableOn) hweak (hEcont.mono Ioo_subset_Icc_self)
  have hII : ∀ a b, a ∈ Icc c d → b ∈ Icc c d → IntervalIntegrable g volume a b := by
    intro a b ha hb
    rw [intervalIntegrable_iff]
    refine hgIcc.mono_set ?_
    intro x hx
    rw [uIoc, mem_Ioc] at hx
    exact ⟨(le_min ha.1 hb.1).trans hx.1.le, hx.2.trans (max_le ha.2 hb.2)⟩
  have hprim : ContinuousOn (fun b => C + ∫ τ in t₀..b, g τ) (Icc c d) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (hII c d ⟨le_rfl, hcd.le⟩
      ⟨hcd.le, le_rfl⟩) (by rw [uIcc_of_le hcd.le]; exact ht₀Icc)
    rw [uIcc_of_le hcd.le] at h
    exact continuousOn_const.add h
  have hrep : EqOn E (fun b => C + ∫ τ in t₀..b, g τ) (Icc c d) :=
    Set.EqOn.of_subset_closure (fun x hx => hC x hx) hEcont hprim Ioo_subset_Icc_self
      (closure_Ioo hcd.ne).ge
  intro s t hcs hst htd
  have hsI : s ∈ Icc c d := ⟨hcs, hst.trans htd⟩
  have htI : t ∈ Icc c d := ⟨hcs.trans hst, htd⟩
  change E t - E s = ∫ τ in s..t, g τ
  rw [hrep htI, hrep hsI]
  simp only [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (hII t₀ t ht₀Icc htI) (hII t₀ s ht₀Icc hsI)

end ESS
