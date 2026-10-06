/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedTransportField
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedDissipation
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMollified
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureLocalBound
public import Mathlib.Analysis.MeanInequalities

/-!
# The regularized transport field on space-time slabs

The transport velocity `J_ε u` of the forced regularized problem
(`lem:regularised-forced`) is, on every time slice, the convolution of the
velocity slice with the smooth compactly supported regularizing kernel. For a
jointly measurable velocity with square-integrable slices it is therefore
jointly measurable, and the slice contraction of the convolution in `L^p`
(`lem:reg-mollifier-bounds`) integrates in time to a space-time `L^p` bound on
every slab, as used in `lem:forced-energy-bounds`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- On each slice with square-integrable velocity, the regularized transport
velocity is the kernel convolution of the velocity components. -/
theorem forcedLerayLimit_transport_component_eq
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (u : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (hz : MemLp (fun x : Vec3 => u (x, z.2)) 2 volume) (i : Fin 3) :
    regUniformMollifiedVelocity ρ ε hε u z i =
      ∫ y : Vec3, forcedTransportKernel ρ ε hε y * u (z.1 - y, z.2) i := by
  have h := forcedTransport_component_eq (ρ := ρ) hε hz z.1 i
  rw [convolution_def] at h
  exact h

/-- The regularized transport velocity of a jointly measurable velocity with
square-integrable slices is jointly measurable. -/
theorem forcedLerayLimit_transport_measurable
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (u : ParabolicPoint → Vec3)
    (hu : StronglyMeasurable u)
    (hslice : ∀ t : ℝ, MemLp (fun x : Vec3 => u (x, t)) 2 volume) :
    Measurable (regUniformMollifiedVelocity ρ ε hε u) := by
  refine measurable_pi_iff.2 fun i => ?_
  have heq : (fun z : ParabolicPoint => regUniformMollifiedVelocity ρ ε hε u z i) =
      fun z => ∫ y : Vec3, forcedTransportKernel ρ ε hε y * u (z.1 - y, z.2) i := by
    funext z
    exact forcedLerayLimit_transport_component_eq ρ ε hε u z (hslice z.2) i
  rw [heq]
  have hk : Measurable (forcedTransportKernel ρ ε hε) :=
    (forcedTransportKernel_contDiff ρ ε hε).continuous.measurable
  have hshift : Measurable fun q : (Vec3 × ℝ) × Vec3 => ((q.1.1 - q.2, q.1.2) : Vec3 × ℝ) :=
    (measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd
  have hint : StronglyMeasurable (Function.uncurry fun (z : Vec3 × ℝ) (y : Vec3) =>
      forcedTransportKernel ρ ε hε y * u (z.1 - y, z.2) i) := by
    refine Measurable.stronglyMeasurable ?_
    exact (hk.comp measurable_snd).mul
      ((measurable_pi_apply i).comp (hu.measurable.comp hshift))
  exact (hint.integral_prod_right (ν := (volume : Measure Vec3))).measurable

/-- The `p`-th power of the space-time `L^p` norm on a product is the time
integral of the `p`-th powers of the slice norms. -/
private theorem forcedLerayLimit_eLpNorm_rpow_prod {ν : Measure ℝ} [SFinite ν]
    {g : Vec3 × ℝ → ℝ} (hg : StronglyMeasurable g) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hptop : p ≠ ⊤) :
    eLpNorm g p ((volume : Measure Vec3).prod ν) ^ p.toReal =
      ∫⁻ t, eLpNorm (fun x : Vec3 => g (x, t)) p volume ^ p.toReal ∂ν := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hslice (t : ℝ) : AEStronglyMeasurable (fun x : Vec3 => g (x, t)) volume :=
    (hg.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hpow (x : ℝ≥0∞) : (x ^ (1 / p.toReal)) ^ p.toReal = x := by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg.aestronglyMeasurable, hpow,
    lintegral_prod_symm' _ (hg.measurable.enorm.pow_const _)]
  refine lintegral_congr fun t => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hslice t), hpow]

/-- The space-time `L^p` bound of the regularized transport velocity on a
slab over a time set `I`: each component is controlled by the three velocity
components, uniformly in the regularization parameter. -/
theorem forcedLerayLimit_transport_eLpNorm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (u : ParabolicPoint → Vec3)
    (hu : StronglyMeasurable u)
    (hslice : ∀ t : ℝ, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤) (I : Set ℝ) (i : Fin 3) :
    eLpNorm (fun z : ParabolicPoint => regUniformMollifiedVelocity ρ ε hε u z i) p
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)) ^ p.toReal ≤
      3 ^ (p.toReal - 1) * ∑ j : Fin 3,
        eLpNorm (fun z : ParabolicPoint => u z j) p
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)) ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hptop hp
    simpa using this
  let J := regUniformMollifiedVelocity ρ ε hε u
  have hJm : StronglyMeasurable (fun z : Vec3 × ℝ => J z i) :=
    ((measurable_pi_apply i).comp
      (forcedLerayLimit_transport_measurable ρ ε hε u hu hslice)).stronglyMeasurable
  have hum (j : Fin 3) : StronglyMeasurable (fun z : Vec3 × ℝ => u z j) :=
    ((measurable_pi_apply j).comp hu.measurable).stronglyMeasurable
  have hμ := restrict_spaceTimeSet_eq_prod I
  rw [hμ]
  refine le_of_eq_of_le (forcedLerayLimit_eLpNorm_rpow_prod hJm hp0 hptop) ?_
  refine le_of_le_of_eq ?_ (congrArg (fun x => 3 ^ (p.toReal - 1) * x)
    (Finset.sum_congr rfl fun j _ =>
      (forcedLerayLimit_eLpNorm_rpow_prod (hum j) hp0 hptop).symm))
  have hslicebound (t : ℝ) : eLpNorm (fun x : Vec3 => J (x, t) i) p volume ≤
      ∑ j : Fin 3, eLpNorm (fun x : Vec3 => u (x, t) j) p volume := by
    by_cases h : ∀ j : Fin 3, MemLp (fun x : Vec3 => u (x, t) j) p volume
    · exact regMollifyVector_component_eLpNorm_le_sum ρ ε hε hp hptop (hslice t) h i
    · simp only [not_forall] at h
      obtain ⟨j, hj⟩ := h
      have hjtop : eLpNorm (fun x : Vec3 => u (x, t) j) p volume = ⊤ := by
        by_contra hne
        exact hj (lt_top_iff_ne_top.2 hne)
      have hsum : ∑ j : Fin 3, eLpNorm (fun x : Vec3 => u (x, t) j) p volume = ⊤ :=
        top_unique (hjtop ▸ Finset.single_le_sum (f := fun j : Fin 3 =>
          eLpNorm (fun x : Vec3 => u (x, t) j) p volume)
          (fun _ _ => bot_le) (Finset.mem_univ j))
      rw [hsum]
      exact le_top
  have hmeas (j : Fin 3) : Measurable fun t : ℝ =>
      eLpNorm (fun x : Vec3 => u (x, t) j) p volume ^ p.toReal :=
    (measurable_eLpNorm_slice (hum j) hp0 hptop volume).pow_const _
  calc ∫⁻ t, eLpNorm (fun x : Vec3 => J (x, t) i) p volume ^ p.toReal ∂volume.restrict I
      ≤ ∫⁻ t, 3 ^ (p.toReal - 1) * ∑ j : Fin 3,
          eLpNorm (fun x : Vec3 => u (x, t) j) p volume ^ p.toReal ∂volume.restrict I := by
        refine lintegral_mono fun t => ?_
        have h1 := ENNReal.rpow_le_rpow (hslicebound t) (by positivity : 0 ≤ p.toReal)
        have h2 := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := (Finset.univ : Finset (Fin 3)))
          (f := fun j => eLpNorm (fun x : Vec3 => u (x, t) j) p volume) hq1
        simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h2
        exact h1.trans h2
    _ = 3 ^ (p.toReal - 1) * ∑ j : Fin 3, ∫⁻ t,
          eLpNorm (fun x : Vec3 => u (x, t) j) p volume ^ p.toReal ∂volume.restrict I := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hmeas j),
          lintegral_finsetSum _ fun j _ => hmeas j]

end CKN.Leray

end
