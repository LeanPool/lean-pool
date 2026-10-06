/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PvLocalSolutionLerayHopfCore

/-!
# A strongly `L²`-continuous weak solution in `L⁵` is Leray–Hopf

For `prop:pv-local-solution`: a finite-energy weak solution with pressure on
`ℝ³ × (0, T)`, in space-time `L⁵`, whose slices are square integrable and
continuous into `L²` on `[0, T]` with the datum as the slice at `t = 0`,
satisfies every clause of `def:leray-hopf`, with the energy equality at every
time.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The energy equality at every time, for a strongly `L²`-continuous weak
solution in space-time `L⁵`. -/
theorem pvLH_energy_equality {T : ℝ} (hT : 0 < T) {a : Vec3 → Vec3}
    {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hS : IsSerrinWeakSolution T a U DU p)
    (hU5 : MemLp U (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hmem : ∀ t ∈ Icc 0 T, MemLp (fun x : Vec3 => U (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc 0 T, Tendsto (fun s => eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) 2
      volume) (𝓝[Icc 0 T] t) (𝓝 0)) :
    ∀ t ∈ Icc 0 T, (∫ x : Vec3, ∑ k : Fin 3, U (x, t) k * U (x, t) k) =
      (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
        2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, DU q k j * DU q k j := by
  have hDU2 := serrinWeak_gradient_memLp_two hS
  have hf := pvLH_sq_continuousOn hmem hcont
  have hg : ContinuousOn (fun t : ℝ => (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
      2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ k : Fin 3, ∑ j : Fin 3, DU q k j * DU q k j) (Icc 0 T) :=
    continuousOn_const.sub ((pvLH_dissipation_continuousOn hT.le hDU2).const_smul (2 : ℝ))
  have hae := serrin_energy_equality hS hU5
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hae
  refine Measure.eqOn_Icc_of_ae_eq (μ := volume) hT.ne (hae.mono fun t ht => ?_) hf hg
  linarith only [ht]

/-- A finite-energy weak solution with pressure in space-time `L⁵` whose slices
are square integrable and continuous into `L²` on `[0, T]`, with the datum as its
slice at `t = 0`, is a Leray–Hopf solution (`def:leray-hopf`). -/
theorem pvLH_lerayHopf_of_strongL2 {T : ℝ} (hT : 0 < T) {a : Vec3 → Vec3} (ha : IsInJ a)
    {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hS : IsSerrinWeakSolution T a U DU p)
    (hU5 : MemLp U (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hmem : ∀ t ∈ Icc 0 T, MemLp (fun x : Vec3 => U (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc 0 T, Tendsto (fun s => eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) 2
      volume) (𝓝[Icc 0 T] t) (𝓝 0))
    (h0 : ∀ x : Vec3, U (x, 0) = a x) :
    IsLerayHopfSolution T a U DU := by
  have hDU2 := serrinWeak_gradient_memLp_two hS
  have hE := pvLH_energy_equality hT hS hU5 hmem hcont
  have hsq (w : Vec3 → Vec3) (hw : MemLp w 2 volume) :
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (w x)) ^ (2 : ℝ)) =
        ENNReal.ofReal (∫ x : Vec3, ∑ k : Fin 3, w x k * w x k) := by
    have hint : Integrable (fun x => ∑ k : Fin 3, w x k * w x k) volume :=
      integrable_finsetSum _ fun k _ =>
        (memLp_pi_iff.1 hw k).integrable_mul (memLp_pi_iff.1 hw k)
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
      Finset.sum_nonneg fun k _ => mul_self_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _) (by norm_num), Real.rpow_two,
      vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun k _ => sq (w x k))
  refine ⟨hT, ha, hS.meas_u, hS.meas_Du, hS.slice_bound, hS.energy, hS.weak_grad, hS.div_free,
    fun w hw => pvLH_pairing_continuousOn hmem hcont hw, ?_, ?_, ?_⟩
  · -- the momentum equation against divergence-free tests
    intro φ hφ hdiv
    have h := hS.momentum φ hφ
    have hpt : (fun z : ParabolicPoint =>
        (-(∑ i : Fin 3, U z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3, U z i * U z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3, DU z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) =
        fun z => (-(∑ i : Fin 3, U z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3, U z i * U z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3, DU z i j * spatialPartial (fun y => φ y i) j z := by
      funext z
      rw [hdiv z]
      simp
    rw [hpt] at h
    exact h
  · -- the energy inequality at every time
    intro t ht
    have hDt : MemLp DU 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
      hDU2.mono_measure (serrin_slab_restrict_le ht.2)
    have hDint : Integrable (fun q => ∑ k : Fin 3, ∑ j : Fin 3, DU q k j * DU q k j)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
        (memLp_pi_iff.1 (memLp_pi_iff.1 hDt k) j).integrable_mul
          (memLp_pi_iff.1 (memLp_pi_iff.1 hDt k) j)
    have hgrad : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ENNReal.ofReal (spatialGradientSq U DU z)) =
        ENNReal.ofReal (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, DU q k j * DU q k j) := by
      rw [ofReal_integral_eq_lintegral_ofReal hDint (Eventually.of_forall fun q =>
        Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _)]
      refine lintegral_congr fun q => ?_
      simp only [spatialGradientSq, pow_two]
    have hD0 : 0 ≤ ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ k : Fin 3, ∑ j : Fin 3, DU q k j * DU q k j :=
      integral_nonneg fun q => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
        mul_self_nonneg _
    have hU0 : 0 ≤ ∫ x : Vec3, ∑ k : Fin 3, U (x, t) k * U (x, t) k :=
      integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
    rw [hsq _ (hmem t ht), hsq _ ha.1, hgrad, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) hD0, ← ENNReal.ofReal_mul (by norm_num)]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    linarith only [hE t ht]
  · -- the strong initial trace
    have hnear : Icc 0 T ∈ 𝓝[>] (0 : ℝ) :=
      mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self
    have hN : Tendsto (fun s => (eLpNorm (fun x : Vec3 => U (x, s) - U (x, 0)) 2 volume).toReal)
        (𝓝[>] 0) (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        ((hcont 0 (left_mem_Icc.2 hT.le)).mono_left (nhdsWithin_le_of_mem hnear))
      rw [ENNReal.toReal_zero] at h
      exact h
    have hreal : Tendsto (fun s => ∫ x : Vec3, ∑ k : Fin 3,
        (U (x, s) - U (x, 0)) k * (U (x, s) - U (x, 0)) k) (𝓝[>] 0) (𝓝 0) := by
      have hlim : Tendsto (fun s => 3 * ((eLpNorm (fun x : Vec3 => U (x, s) - U (x, 0)) 2
          volume).toReal * (eLpNorm (fun x : Vec3 => U (x, s) - U (x, 0)) 2 volume).toReal))
          (𝓝[>] 0) (𝓝 0) := by
        simpa using (hN.mul hN).const_mul 3
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun s => integral_nonneg fun x =>
          Finset.sum_nonneg fun k _ => mul_self_nonneg _) ?_
      filter_upwards [hnear] with s hs
      exact (le_abs_self _).trans
        (pvLH_pair_le ((hmem s hs).sub (hmem 0 (left_mem_Icc.2 hT.le)))
          ((hmem s hs).sub (hmem 0 (left_mem_Icc.2 hT.le))))
    have h := ENNReal.tendsto_ofReal hreal
    rw [ENNReal.ofReal_zero] at h
    refine h.congr' ?_
    filter_upwards [hnear] with s hs
    have hd : MemLp (fun x : Vec3 => U (x, s) - a x) 2 volume := (hmem s hs).sub ha.1
    rw [hsq _ hd]
    simp only [h0]

end ESS

end
