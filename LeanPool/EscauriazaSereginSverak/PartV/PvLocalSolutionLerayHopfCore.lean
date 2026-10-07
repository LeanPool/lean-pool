/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEnergyEquality
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossIdentity
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossLimitTerms
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyNLimit

/-!
# Leray–Hopf clauses from strong `L²` continuity

The last step of `prop:pv-local-solution`: a finite-energy weak solution with
pressure in space-time `L⁵` on `ℝ³ × (0, T)` whose time slices are square
integrable and continuous into `L²` on `[0, T]`, with the datum as its slice at
`t = 0`, is a Leray–Hopf solution. The energy equality, which holds at almost
every time in the `L⁵` class, extends to every time by continuity of both sides;
it gives the energy inequality of `def:leray-hopf`, and the strong `L²`
continuity gives the weak continuity and the strong initial trace.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A component of a square-integrable vector field has at most its norm. -/
theorem pvLH_component_eLpNorm_le {f : Vec3 → Vec3} (hf : MemLp f 2 volume) (k : Fin 3) :
    eLpNorm (fun x => f x k) 2 volume ≤ eLpNorm f 2 volume :=
  eLpNorm_mono ((continuous_apply k).comp_aestronglyMeasurable hf.aestronglyMeasurable)
    fun x => norm_le_pi_norm (f x) k

/-- The `L²` pairing of vector fields is bounded by three times the product of
their (sup-norm) `L²` norms. -/
theorem pvLH_pair_le {f g : Vec3 → Vec3} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x, ∑ k : Fin 3, f x k * g x k| ≤
      3 * ((eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal) := by
  have hfk (k : Fin 3) : MemLp (fun x => f x k) 2 volume := memLp_pi_iff.1 hf k
  have hgk (k : Fin 3) : MemLp (fun x => g x k) 2 volume := memLp_pi_iff.1 hg k
  rw [integral_finsetSum (f := fun k x => f x k * g x k) _ fun k _ =>
    (hfk k).integrable_mul (hgk k)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hk (k : Fin 3) : |∫ x, f x k * g x k| ≤
      (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal :=
    (CKN.Leray.abs_integral_mul_le_eLpNorm_two (hfk k) (hgk k)).trans
      (mul_le_mul (ENNReal.toReal_mono hf.eLpNorm_ne_top (pvLH_component_eLpNorm_le hf k))
        (ENNReal.toReal_mono hg.eLpNorm_ne_top (pvLH_component_eLpNorm_le hg k))
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  calc
    ∑ k : Fin 3, |∫ x, f x k * g x k| ≤
        ∑ _k : Fin 3, (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal :=
      Finset.sum_le_sum fun k _ => hk k
    _ = 3 * ((eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num

section

variable {T : ℝ} {U : ParabolicPoint → Vec3}

/-- Strong `L²` continuity gives continuity of the pairing with every square
integrable field. -/
theorem pvLH_pairing_continuousOn
    (hmem : ∀ t ∈ Icc 0 T, MemLp (fun x : Vec3 => U (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc 0 T, Tendsto (fun s => eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) 2
      volume) (𝓝[Icc 0 T] t) (𝓝 0))
    {w : Vec3 → Vec3} (hw : MemLp w 2 volume) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, U (x, t) i * w x i) (Icc 0 T) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun s => 3 * ((eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) 2
      volume).toReal * (eLpNorm w 2 volume).toReal)) (𝓝[Icc 0 T] t) (𝓝 0) := by
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)).mul_const
      (eLpNorm w 2 volume).toReal
    simpa using h.const_mul 3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hd : MemLp (fun x : Vec3 => U (x, s) - U (x, t)) 2 volume := (hmem s hs).sub (hmem t ht)
  have hI (v : Vec3 → Vec3) (hv : MemLp v 2 volume) :
      Integrable (fun x => ∑ i : Fin 3, v x i * w x i) :=
    integrable_finsetSum _ fun i _ =>
      (memLp_pi_iff.1 hv i).integrable_mul (memLp_pi_iff.1 hw i)
  rw [Real.norm_eq_abs, ← integral_sub (hI _ (hmem s hs)) (hI _ (hmem t ht))]
  have hpt : (fun x : Vec3 => ∑ i : Fin 3, U (x, s) i * w x i - ∑ i : Fin 3, U (x, t) i * w x i) =
      fun x => ∑ i : Fin 3, (U (x, s) - U (x, t)) i * w x i := by
    funext x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.sub_apply]
    ring
  rw [hpt]
  exact pvLH_pair_le hd hw

/-- Strong `L²` continuity gives continuity of the squared `L²` norm. -/
theorem pvLH_sq_continuousOn
    (hmem : ∀ t ∈ Icc 0 T, MemLp (fun x : Vec3 => U (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc 0 T, Tendsto (fun s => eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) 2
      volume) (𝓝[Icc 0 T] t) (𝓝 0)) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, ∑ k : Fin 3, U (x, t) k * U (x, t) k) (Icc 0 T) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  set N : ℝ → ℝ := fun s => (eLpNorm (fun x : Vec3 => U (x, s) - U (x, t)) 2 volume).toReal
  have hN : Tendsto N (𝓝[Icc 0 T] t) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hlim : Tendsto (fun s => 3 * (N s * N s) + 2 * (3 * (N s *
      (eLpNorm (fun x : Vec3 => U (x, t)) 2 volume).toReal))) (𝓝[Icc 0 T] t) (𝓝 0) := by
    have h := ((hN.mul hN).const_mul 3).add (((hN.mul_const
      (eLpNorm (fun x : Vec3 => U (x, t)) 2 volume).toReal).const_mul 3).const_mul 2)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hd : MemLp (fun x : Vec3 => U (x, s) - U (x, t)) 2 volume := (hmem s hs).sub (hmem t ht)
  have hI (v v' : Vec3 → Vec3) (hv : MemLp v 2 volume) (hv' : MemLp v' 2 volume) :
      Integrable (fun x => ∑ k : Fin 3, v x k * v' x k) :=
    integrable_finsetSum _ fun k _ =>
      (memLp_pi_iff.1 hv k).integrable_mul (memLp_pi_iff.1 hv' k)
  have hsplit : (∫ x : Vec3, ∑ k : Fin 3, U (x, s) k * U (x, s) k) -
      ∫ x : Vec3, ∑ k : Fin 3, U (x, t) k * U (x, t) k =
      (∫ x : Vec3, ∑ k : Fin 3, (U (x, s) - U (x, t)) k * (U (x, s) - U (x, t)) k) +
        2 * ∫ x : Vec3, ∑ k : Fin 3, (U (x, s) - U (x, t)) k * U (x, t) k := by
    rw [← integral_sub (hI _ _ (hmem s hs) (hmem s hs)) (hI _ _ (hmem t ht) (hmem t ht)),
      ← integral_const_mul, ← integral_add (hI _ _ hd hd) ((hI _ _ hd (hmem t ht)).const_mul 2)]
    congr 1
    funext x
    simp only [Pi.sub_apply, Fin.sum_univ_three]
    ring
  rw [Real.norm_eq_abs, hsplit]
  refine (abs_add_le _ _).trans (add_le_add (pvLH_pair_le hd hd) ?_)
  rw [abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left (pvLH_pair_le hd (hmem t ht)) zero_le_two

/-- The dissipation integral over `ℝ³ × (0, t)` is continuous in `t ∈ [0, T]`. -/
theorem pvLH_dissipation_continuousOn {DU : ParabolicPoint → Fin 3 → Vec3} (hT : 0 ≤ T)
    (hDU : MemLp DU 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    ContinuousOn (fun t : ℝ => ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      ∑ k : Fin 3, ∑ j : Fin 3, DU q k j * DU q k j) (Icc 0 T) := by
  set F : ParabolicPoint → ℝ := fun q => ∑ k : Fin 3, ∑ j : Fin 3, DU q k j * DU q k j
  have hF : Integrable F (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      (memLp_pi_iff.1 (memLp_pi_iff.1 hDU k) j).integrable_mul
        (memLp_pi_iff.1 (memLp_pi_iff.1 hDU k) j)
  have hprim := intervalIntegral.continuousOn_primitive_interval'
    (serrin_intervalIntegrable_of_slab hT hF) (left_mem_uIcc (a := (0 : ℝ)) (b := T))
  rw [uIcc_of_le hT] at hprim
  refine hprim.congr fun t ht => ?_
  exact (serrin_intervalIntegral_eq_slab ht.1
    (hF.mono_measure (serrin_slab_restrict_le ht.2))).symm

end

end ESS

end
