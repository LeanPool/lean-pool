/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceTest
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingHilbertChain
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitAC
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Time increments of `L²`-continuous fields with an `L²` time derivative

`prop:lps-smoothing`: a field `u` on the slab `ℝ³ × (t₀, T)` that is continuous
into `L²` on `[t₀, T]` and whose weak time derivative `∂ₜu` is square integrable
on the slab satisfies, for every smooth compactly supported spatial test `ψ`,
the pairing identity `⟨u(t) - u(s), ψ⟩ = ∫ₛᵗ ⟨∂ₜu(τ), ψ⟩ dτ`, and the increment
bound `‖u(t) - u(s)‖² ≤ (t - s) ∫ₛᵗ ‖∂ₜu(τ)‖² dτ`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The pairing of a component of a square-integrable vector field with a
square-integrable function is bounded by the product of the `L²` norms. -/
private theorem lps_twj_abs_pairing_le {a : Vec3 → Vec3} (ha : MemLp a 2 volume)
    {ψ : Vec3 → ℝ} (hψ : MemLp ψ 2 volume) (i : Fin 3) :
    |∫ x, a x i * ψ x| ≤ (eLpNorm a 2 volume).toReal * (eLpNorm ψ 2 volume).toReal := by
  have hai : MemLp (fun x => a x i) 2 volume := ha.eval i
  have h1 := lps_abs_integral_pairing_le (fun x => a x i) ψ hai hψ
  rw [vl_integral_sq_eq hai, vl_integral_sq_eq hψ, Real.sqrt_sq ENNReal.toReal_nonneg,
    Real.sqrt_sq ENNReal.toReal_nonneg] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
  exact ENNReal.toReal_mono ha.eLpNorm_ne_top
    (eLpNorm_mono hai.aestronglyMeasurable fun x => norm_le_pi_norm (a x) i)

/-- The pairing of a square-integrable function with the difference of two tests is
bounded by the product of the `L²` norms. -/
private theorem lps_twj_abs_pairing_sub_le {f ψ φ : Vec3 → ℝ} (hf : MemLp f 2 volume)
    (hψ : MemLp ψ 2 volume) (hφ : MemLp φ 2 volume) :
    |(∫ x, f x * ψ x) - ∫ x, f x * φ x| ≤
      Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, (ψ x - φ x) ^ 2) := by
  have h1 : Integrable (fun x => f x * ψ x) volume := hf.integrable_mul hψ
  have h2 : Integrable (fun x => f x * φ x) volume := hf.integrable_mul hφ
  have e : (∫ x, (f x * ψ x - f x * φ x)) = ∫ x, f x * (ψ x - φ x) :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [← integral_sub h1 h2, e]
  exact lps_abs_integral_pairing_le f (fun x => ψ x - φ x) hf (hψ.sub hφ)

/-- Slices of a square-integrable slab field are square integrable for almost every
time of `(t₀, T]`. -/
private theorem lps_twj_ae_slice_memLp {t₀ T : ℝ} {F : ParabolicPoint → ℝ}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    ∀ᵐ τ ∂volume, τ ∈ Ioc t₀ T → MemLp (fun x : Vec3 => F (x, τ)) 2 volume := by
  have hspaceTime : MemLp (fun q : Vec3 × ℝ => F q) 2
      ((volume : Measure Vec3).prod (volume.restrict (Ioo t₀ T))) := by
    rw [← lps_measure_slab_eq_prod]
    exact hF
  have hsq : Integrable (fun q : Vec3 × ℝ => ‖F q‖ ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo t₀ T))) :=
    (memLp_two_iff_integrable_sq_norm hspaceTime.aestronglyMeasurable).1 hspaceTime
  have h : ∀ᵐ τ ∂(volume.restrict (Ioo t₀ T)),
      MemLp (fun x : Vec3 => F (x, τ)) 2 volume := by
    filter_upwards [hspaceTime.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae]
      with τ hmeas hint
    exact (memLp_two_iff_integrable_sq_norm hmeas).2 hint
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ae_restrict_iff' measurableSet_Ioc] at h
  exact h

/-- The squared spatial `L²` norm of the slices of a square-integrable slab field is
integrable in time. -/
private theorem lps_twj_sq_slice_integrableOn {t₀ T : ℝ} {F : ParabolicPoint → ℝ}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    IntegrableOn (fun τ => ∫ x : Vec3, F (x, τ) ^ 2) (Ioc t₀ T) volume := by
  have hFL : MemLp (fun q : Vec3 × ℝ => F q) 2
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ T)) := hF
  have h := hFL.integrable_sq
  rw [lps_measure_slab_eq_prod] at h
  exact (integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).2 h.integral_prod_right

/-- The spatial `L²` norm of the slices of a square-integrable slab field is
integrable on every subinterval of `(t₀, T]`. -/
private theorem lps_twj_sqrt_slice_integrableOn {t₀ T : ℝ} {F : ParabolicPoint → ℝ}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {a b : ℝ} (ha : t₀ ≤ a) (hb : b ≤ T) :
    IntegrableOn (fun τ => Real.sqrt (∫ x : Vec3, F (x, τ) ^ 2)) (Ioc a b) volume := by
  have hN : IntegrableOn (fun τ => ∫ x : Vec3, F (x, τ) ^ 2) (Ioc a b) volume :=
    (lps_twj_sq_slice_integrableOn hF).mono_set (Ioc_subset_Ioc ha hb)
  have hfin : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hm : AEStronglyMeasurable (fun τ => Real.sqrt (∫ x : Vec3, F (x, τ) ^ 2))
      (volume.restrict (Ioc a b)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hN.aestronglyMeasurable
  have hsq : Integrable (fun τ => Real.sqrt (∫ x : Vec3, F (x, τ) ^ 2) ^ 2)
      (volume.restrict (Ioc a b)) :=
    hN.congr (ae_of_all _ fun τ =>
      (Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (F (x, τ)))).symm)
  exact ((memLp_two_iff_integrable_sq hm).2 hsq).integrable (by norm_num)

/-- The spatial pairing of a square-integrable slab field with a square-integrable
function is integrable in time. -/
private theorem lps_twj_pairing_integrableOn {t₀ T : ℝ} {F : ParabolicPoint → ℝ}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {ψ : Vec3 → ℝ} (hψ : MemLp ψ 2 volume) :
    IntegrableOn (fun τ => ∫ x : Vec3, F (x, τ) * ψ x) (Ioc t₀ T) volume := by
  have hFL : MemLp (fun q : Vec3 × ℝ => F q) 2
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ T)) := hF
  exact (integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).2
    (lps_integrable_slice_pairing hFL hψ).integral_prod_right

/-- The time integrals of the pairings of a square-integrable slab field with two
tests differ by at most the `L²` distance of the tests times the time integral of
the spatial `L²` norm of the field. -/
private theorem lps_twj_integral_pairing_sub_le {t₀ T : ℝ} {F : ParabolicPoint → ℝ}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {ψ φ : Vec3 → ℝ} (hψ : MemLp ψ 2 volume) (hφ : MemLp φ 2 volume)
    {a b : ℝ} (ha : t₀ ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    |(∫ τ in a..b, ∫ x, F (x, τ) * ψ x) - ∫ τ in a..b, ∫ x, F (x, τ) * φ x| ≤
      Real.sqrt (∫ x, (ψ x - φ x) ^ 2) * ∫ τ in a..b, Real.sqrt (∫ x, F (x, τ) ^ 2) := by
  have hIψ : IntegrableOn (fun τ => ∫ x, F (x, τ) * ψ x) (Ioc a b) volume :=
    (lps_twj_pairing_integrableOn hF hψ).mono_set (Ioc_subset_Ioc ha hb)
  have hIφ : IntegrableOn (fun τ => ∫ x, F (x, τ) * φ x) (Ioc a b) volume :=
    (lps_twj_pairing_integrableOn hF hφ).mono_set (Ioc_subset_Ioc ha hb)
  have hR := lps_twj_sqrt_slice_integrableOn hF ha hb
  have hsl := lps_twj_ae_slice_memLp hF
  simp only [intervalIntegral.integral_of_le hab]
  rw [← integral_sub hIψ hIφ, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hR.const_mul _) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hsl] with τ hτ hτI
  rw [Real.norm_eq_abs, mul_comm]
  exact lps_twj_abs_pairing_sub_le (hτ ⟨ha.trans_lt hτI.1, hτI.2.trans hb⟩) hψ hφ

/-- A spatial pairing is continuous along a curve that is continuous into `L²`. -/
private theorem lps_twj_pairing_continuousOn {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    {ψ : Vec3 → ℝ} (hψ : MemLp ψ 2 volume) (i : Fin 3) :
    ContinuousOn (fun t => ∫ x, u (x, t) i * ψ x) (Icc t₀ T) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun s => (eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume).toReal *
      (eLpNorm ψ 2 volume).toReal) (𝓝[Icc t₀ T] t) (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)).mul_const
      (eLpNorm ψ 2 volume).toReal
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun s => dist_nonneg) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsub : MemLp (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume :=
    (hslice s hs).sub (hslice t ht)
  have heq : (∫ x, u (x, s) i * ψ x) - ∫ x, u (x, t) i * ψ x =
      ∫ x, (u (x, s) - u (x, t)) i * ψ x := by
    have h1 : Integrable (fun x => u (x, s) i * ψ x) volume :=
      ((hslice s hs).eval i).integrable_mul hψ
    have h2 : Integrable (fun x => u (x, t) i * ψ x) volume :=
      ((hslice t ht).eval i).integrable_mul hψ
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  rw [Real.dist_eq, heq]
  exact lps_twj_abs_pairing_le hsub hψ i

/-- The time clause of a space-time weak derivative identity, tested against
`χ(t) ψ(x)`, is the one-dimensional weak derivative identity of the spatial
pairing with `ψ`. -/
private theorem lps_twj_pairing_hasWeakDerivOn {t₀ T : ℝ} {u Dtu : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (i : Fin 3)
    (htime : ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    HasWeakDerivOn (Ioo t₀ T) (fun t => ∫ x, u (x, t) i * ψ x)
      (fun t => ∫ x, Dtu (x, t) i * ψ x) := by
  intro χ hχ
  obtain ⟨hχs, hχc, hχsupp⟩ := hχ
  have hφ := lps_separated_test_mem (a := t₀) (b := T) hχs hχc hχsupp hψ hψc
  have h := htime _ hφ
  have hdχ : Continuous (deriv χ) := hχs.continuous_deriv (by simp)
  have hbdχ' : ∃ C, ∀ t, ‖deriv χ t‖ ≤ C := hdχ.bounded_above_of_compact_support hχc.deriv
  have hbdχ : ∃ C, ∀ t, ‖χ t‖ ≤ C := hχs.continuous.bounded_above_of_compact_support hχc
  have huL : MemLp (fun q : Vec3 × ℝ => u q i) 2 (volume.restrict (vlSlab t₀ T)) := hu.eval i
  have hDL : MemLp (fun q : Vec3 × ℝ => Dtu q i) 2 (volume.restrict (vlSlab t₀ T)) :=
    hDt.eval i
  have hL := integral_slab_separated huL hψ.continuous hψc hdχ hbdχ'
  have hR := integral_slab_separated hDL hψ.continuous hψc hχs.continuous hbdχ
  have hTP : ∀ z : ParabolicPoint, timePartial (fun y : Vec3 × ℝ => χ y.2 * ψ y.1) z =
      deriv χ z.2 * ψ z.1 := fun z => lps_separated_timePartial hχs z
  simp only [hTP] at h
  have hL' : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
      u z i * (deriv χ z.2 * ψ z.1)) =
      ∫ t in Ioo t₀ T, deriv χ t * ∫ x, u (x, t) i * ψ x := by
    rw [← hL]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  have hR' : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
      Dtu z i * (χ z.2 * ψ z.1)) =
      ∫ t in Ioo t₀ T, χ t * ∫ x, Dtu (x, t) i * ψ x := by
    rw [← hR]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [hL', hR'] at h
  have e1 : (∫ t in Ioo t₀ T, (∫ x, u (x, t) i * ψ x) * deriv χ t) =
      ∫ t in Ioo t₀ T, deriv χ t * ∫ x, u (x, t) i * ψ x :=
    integral_congr_ae (ae_of_all _ fun t => mul_comm _ _)
  have e2 : (∫ t in Ioo t₀ T, (∫ x, Dtu (x, t) i * ψ x) * χ t) =
      ∫ t in Ioo t₀ T, χ t * ∫ x, Dtu (x, t) i * ψ x :=
    integral_congr_ae (ae_of_all _ fun t => mul_comm _ _)
  change (∫ t in Ioo t₀ T, (∫ x, u (x, t) i * ψ x) * deriv χ t) =
    -(∫ t in Ioo t₀ T, (∫ x, Dtu (x, t) i * ψ x) * χ t)
  rw [e1, e2, h]

/-- `prop:lps-smoothing`: for a field continuous into `L²` on `[t₀, T]` with a
square-integrable weak time derivative on the slab, the spatial pairing of each
component with a smooth compactly supported test changes between two times by the
time integral of the paired derivative. -/
theorem lps_slice_pairing_sub_eq_integral {t₀ T : ℝ} (hT : t₀ < T)
    {u Dtu : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (htime : ∀ i : Fin 3,
      ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z)
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (i : Fin 3)
    {s t : ℝ} (hs : t₀ ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (∫ x, u (x, t) i * ψ x) - ∫ x, u (x, s) i * ψ x =
      ∫ τ in s..t, ∫ x, Dtu (x, τ) i * ψ x := by
  set f : ℝ → ℝ := fun τ => ∫ x, u (x, τ) i * ψ x with hf
  set g : ℝ → ℝ := fun τ => ∫ x, Dtu (x, τ) i * ψ x with hg
  have hψL : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hfc : ContinuousOn f (Icc t₀ T) := lps_twj_pairing_continuousOn hslice hcont hψL i
  have hgIoc : IntegrableOn g (Ioc t₀ T) volume := lps_twj_pairing_integrableOn (hDt.eval i) hψL
  have hgI : IntegrableOn g (Ioo t₀ T) volume := hgIoc.mono_set Ioo_subset_Ioc_self
  have hweak : HasWeakDerivOn (Ioo t₀ T) f g :=
    lps_twj_pairing_hasWeakDerivOn hu hDt i (htime i) hψ hψc
  have hc : (t₀ + T) / 2 ∈ Ioo t₀ T :=
    ⟨by linarith only [hT], by linarith only [hT]⟩
  have hfIoo : ContinuousOn f (Ioo t₀ T) := hfc.mono Ioo_subset_Icc_self
  obtain ⟨C, hC⟩ := eq_const_add_intervalIntegral_of_continuous_weakDeriv hT hc
    (hfIoo.locallyIntegrableOn measurableSet_Ioo) hgI.locallyIntegrableOn hweak hfIoo
  have hgII : IntervalIntegrable g volume t₀ T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact hgIoc
  have hcI : (t₀ + T) / 2 ∈ uIcc t₀ T := by
    rw [uIcc_of_le hT.le]
    exact Ioo_subset_Icc_self hc
  have hprim : ContinuousOn (fun τ => ∫ σ in (t₀ + T) / 2..τ, g σ) (Icc t₀ T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hgII hcI
    rwa [uIcc_of_le hT.le] at this
  have hEq : EqOn f (fun τ => C + ∫ σ in (t₀ + T) / 2..τ, g σ) (Icc t₀ T) := by
    refine Set.EqOn.of_subset_closure (s := Ioo t₀ T) (fun τ hτ => hC τ hτ) hfc
      (continuousOn_const.add hprim) Ioo_subset_Icc_self ?_
    rw [closure_Ioo hT.ne]
  have hsI : s ∈ Icc t₀ T := ⟨hs, hst.trans ht⟩
  have htI : t ∈ Icc t₀ T := ⟨hs.trans hst, ht⟩
  have hint : ∀ τ ∈ Icc t₀ T, IntervalIntegrable g volume ((t₀ + T) / 2) τ := by
    intro τ hτ
    refine hgII.mono_set ?_
    rw [uIcc_of_le hT.le]
    exact uIcc_subset_Icc (Ioo_subset_Icc_self hc) hτ
  change f t - f s = ∫ τ in s..t, g τ
  rw [hEq htI, hEq hsI, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hint t htI) (hint s hsI)]

/-- Duality in `L²`: a square-integrable function whose pairings with smooth
compactly supported tests are bounded by `M` times the `L²` norm of the test has
squared `L²` norm at most `M²` (`prop:lps-smoothing`). -/
theorem lps_integral_sq_le_of_test_pairing_le {w : Vec3 → ℝ} (hw : MemLp w 2 volume)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      |∫ x, w x * ψ x| ≤ M * Real.sqrt (∫ x, ψ x ^ 2)) :
    ∫ x, w x ^ 2 ≤ M ^ 2 := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set W : Lp ℝ 2 (volume : Measure Vec3) := hw.toLp w with hWdef
  let S : Set (Lp ℝ 2 (volume : Measure Vec3)) := {f | |inner ℝ W f| ≤ M * ‖f‖}
  have hSclosed : IsClosed S :=
    isClosed_le (continuous_abs.comp (continuous_const.inner continuous_id))
      (continuous_const.mul continuous_norm)
  have hdense := Lp.dense_hasCompactSupport_contDiff (E := Vec3) (F := ℝ) (p := 2)
    (μ := (volume : Measure Vec3)) (by norm_num)
  have hsub : {f : Lp ℝ 2 (volume : Measure Vec3) | ∃ g : Vec3 → ℝ,
      f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} ⊆ S := by
    rintro f ⟨g, hfg, hgc, hgs⟩
    have hgL : MemLp g 2 volume := hgs.continuous.memLp_of_hasCompactSupport hgc
    have hf_eq : f = hgL.toLp g := by
      refine Lp.ext ?_
      filter_upwards [hfg, hgL.coeFn_toLp] with x h1 h2
      rw [h1, h2]
    change |inner ℝ W f| ≤ M * ‖f‖
    rw [hf_eq, hWdef, lps_scalar_l2_toLp_inner_integral hw hgL]
    have hn : ‖hgL.toLp g‖ = Real.sqrt (∫ x, g x ^ 2) := by
      rw [← lps_scalar_l2_toLp_norm_sq_integral hgL, Real.sqrt_sq (norm_nonneg _)]
    rw [hn]
    exact hbound g hgs hgc
  have hall : S = univ := by
    have h := closure_mono hsub
    rw [hdense.closure_eq, hSclosed.closure_eq] at h
    exact eq_univ_of_univ_subset h
  have hW : W ∈ S := hall ▸ mem_univ W
  have h1 : |inner ℝ W W| ≤ M * ‖W‖ := hW
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h1
  have h2 : ‖W‖ ≤ M := by
    rcases (norm_nonneg W).eq_or_lt with h | h
    · rw [← h]
      exact hM
    · nlinarith only [h1, h]
  rw [← lps_scalar_l2_toLp_norm_sq_integral hw]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-- One component of the increment bound. -/
private theorem lps_twj_increment_component_le {t₀ T : ℝ} (hT : t₀ < T)
    {u Dtu : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (htime : ∀ i : Fin 3,
      ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z)
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    (i : Fin 3) {s t : ℝ} (hs : t₀ ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∫ x, (u (x, t) i - u (x, s) i) ^ 2 ≤ (t - s) * ∫ τ in s..t, ∫ x, (Dtu (x, τ) i) ^ 2 := by
  set N : ℝ → ℝ := fun τ => ∫ x, (Dtu (x, τ) i) ^ 2 with hN
  have hsI : s ∈ Icc t₀ T := ⟨hs, hst.trans ht⟩
  have htI : t ∈ Icc t₀ T := ⟨hs.trans hst, ht⟩
  have hNst : IntegrableOn N (Ioc s t) volume :=
    (lps_twj_sq_slice_integrableOn (hDt.eval i)).mono_set (Ioc_subset_Ioc hs ht)
  have hN0 : ∀ τ, 0 ≤ N τ := fun τ => integral_nonneg fun x => sq_nonneg _
  have hfin : IsFiniteMeasure (volume.restrict (Ioc s t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hsq : Integrable (fun τ => Real.sqrt (N τ) ^ 2) (volume.restrict (Ioc s t)) :=
    hNst.congr (ae_of_all _ fun τ => (Real.sq_sqrt (hN0 τ)).symm)
  have hsqrtI : IntegrableOn (fun τ => Real.sqrt (N τ)) (Ioc s t) volume :=
    lps_twj_sqrt_slice_integrableOn (hDt.eval i) hs ht
  have hCS : (∫ τ in Ioc s t, Real.sqrt (N τ)) ^ 2 ≤ (t - s) * ∫ τ in Ioc s t, N τ := by
    have h := ESS.LPS.lps_sq_integral_le hsqrtI hsq
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hst] at h
    refine h.trans_eq ?_
    congr 1
    exact integral_congr_ae (ae_of_all _ fun τ => Real.sq_sqrt (hN0 τ))
  set M : ℝ := Real.sqrt ((t - s) * ∫ τ in Ioc s t, N τ) with hM
  have hsqrtM : (∫ τ in Ioc s t, Real.sqrt (N τ)) ≤ M :=
    (le_abs_self _).trans (Real.abs_le_sqrt hCS)
  have hslices := lps_twj_ae_slice_memLp (hDt.eval i)
  have hwL : MemLp (fun x => u (x, t) i - u (x, s) i) 2 volume :=
    ((hslice t htI).eval i).sub ((hslice s hsI).eval i)
  have hbound : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      |∫ x, (u (x, t) i - u (x, s) i) * ψ x| ≤ M * Real.sqrt (∫ x, ψ x ^ 2) := by
    intro ψ hψ hψc
    have hψL : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
    have h1 : Integrable (fun x => u (x, t) i * ψ x) volume :=
      ((hslice t htI).eval i).integrable_mul hψL
    have h2 : Integrable (fun x => u (x, s) i * ψ x) volume :=
      ((hslice s hsI).eval i).integrable_mul hψL
    have heq : (∫ x, (u (x, t) i - u (x, s) i) * ψ x) =
        ∫ τ in Ioc s t, ∫ x, Dtu (x, τ) i * ψ x := by
      rw [← intervalIntegral.integral_of_le hst,
        ← lps_slice_pairing_sub_eq_integral hT hu hDt htime hslice hcont hψ hψc i hs hst ht,
        ← integral_sub h1 h2]
      exact integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [heq]
    have hle : |∫ τ in Ioc s t, ∫ x, Dtu (x, τ) i * ψ x| ≤
        ∫ τ in Ioc s t, Real.sqrt (N τ) * Real.sqrt (∫ x, ψ x ^ 2) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (hsqrtI.mul_const _) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hslices] with τ hτ hτI
      have hτ' : τ ∈ Ioc t₀ T := ⟨hs.trans_lt hτI.1, hτI.2.trans ht⟩
      rw [Real.norm_eq_abs]
      exact lps_abs_integral_pairing_le _ _ (hτ hτ') hψL
    rw [integral_mul_const] at hle
    exact hle.trans (mul_le_mul_of_nonneg_right hsqrtM (Real.sqrt_nonneg _))
  have key := lps_integral_sq_le_of_test_pairing_le hwL (Real.sqrt_nonneg _) hbound
  rw [Real.sq_sqrt (mul_nonneg (sub_nonneg.2 hst)
    (setIntegral_nonneg measurableSet_Ioc fun τ _ => hN0 τ))] at key
  rw [intervalIntegral.integral_of_le hst]
  exact key

/-- `prop:lps-smoothing`: for a field continuous into `L²` on `[t₀, T]` with a
square-integrable weak time derivative on the slab, the squared `L²` norm of an
increment is at most the length of the time interval times the time integral of
the squared `L²` norm of the time derivative. -/
theorem lps_slice_increment_sq_le {t₀ T : ℝ} (hT : t₀ < T)
    {u Dtu : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (htime : ∀ i : Fin 3,
      ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z)
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    {s t : ℝ} (hs : t₀ ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∫ x, ∑ i : Fin 3, (u (x, t) i - u (x, s) i) ^ 2 ≤
      (t - s) * ∫ τ in s..t, ∫ x, ∑ i : Fin 3, (Dtu (x, τ) i) ^ 2 := by
  have hsI : s ∈ Icc t₀ T := ⟨hs, hst.trans ht⟩
  have htI : t ∈ Icc t₀ T := ⟨hs.trans hst, ht⟩
  have hwI : ∀ i : Fin 3, Integrable (fun x => (u (x, t) i - u (x, s) i) ^ 2) volume :=
    fun i => (((hslice t htI).eval i).sub ((hslice s hsI).eval i)).integrable_sq
  rw [integral_finsetSum _ fun i _ => hwI i]
  have hslices : ∀ i : Fin 3, ∀ᵐ τ ∂volume, τ ∈ Ioc t₀ T →
      MemLp (fun x : Vec3 => Dtu (x, τ) i) 2 volume :=
    fun i => lps_twj_ae_slice_memLp (hDt.eval i)
  have hNII : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      IntervalIntegrable (fun τ => ∫ x, (Dtu (x, τ) i) ^ 2) volume s t := by
    intro i _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact (lps_twj_sq_slice_integrableOn (hDt.eval i)).mono_set (Ioc_subset_Ioc hs ht)
  have hRHS : (∫ τ in s..t, ∫ x, ∑ i : Fin 3, (Dtu (x, τ) i) ^ 2) =
      ∑ i : Fin 3, ∫ τ in s..t, ∫ x, (Dtu (x, τ) i) ^ 2 := by
    rw [← intervalIntegral.integral_finsetSum hNII]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hslices] with τ hτ hτI
    rw [uIoc_of_le hst] at hτI
    have hτ' : τ ∈ Ioc t₀ T := ⟨hs.trans_lt hτI.1, hτI.2.trans ht⟩
    exact integral_finsetSum _ fun i _ => (hτ i hτ').integrable_sq
  rw [hRHS, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    lps_twj_increment_component_le hT hu hDt htime hslice hcont i hs hst ht

/-- At a point where the primitive of an integrable function is differentiable with
derivative the function value, the forward averages converge to that value. -/
private theorem lps_twj_average_tendsto {t₀ T t : ℝ} (ht : t ∈ Ioo t₀ T) {g : ℝ → ℝ}
    (hgI : IntervalIntegrable g volume t₀ T)
    (hd : HasDerivAt (fun τ => ∫ σ in t₀..τ, g σ) (g t) t) :
    Tendsto (fun h => (1 / h) * ∫ τ in t..t + h, g τ) (𝓝[>] 0) (𝓝 (g t)) := by
  refine Tendsto.congr' ?_ hd.tendsto_slope_zero_right
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.2)] with h hh
  have hsub : ∀ τ ∈ Icc t₀ T, IntervalIntegrable g volume t₀ τ := by
    intro τ hτ
    refine hgI.mono_set ?_
    rw [uIcc_of_le hτ.1, uIcc_of_le (ht.1.le.trans ht.2.le)]
    exact Icc_subset_Icc le_rfl hτ.2
  have h1 : t + h ∈ Icc t₀ T :=
    ⟨by linarith only [ht.1, hh.1], by linarith only [hh.2]⟩
  have h2 : t ∈ Icc t₀ T := Ioo_subset_Icc_self ht
  rw [smul_eq_mul, one_div, intervalIntegral.integral_interval_sub_left (hsub _ h1) (hsub _ h2)]

/-- `prop:lps-smoothing`: for a field continuous into `L²` on `[t₀, T]` with a
square-integrable weak time derivative on the slab, almost every time of `(t₀, T)`
is a Lebesgue point of every spatial pairing: the forward difference quotients of the
pairing of each component with any smooth compactly supported test converge to the
pairing of the time derivative. -/
theorem lps_slice_pairing_ae_tendsto_slope {t₀ T : ℝ} (hT : t₀ < T)
    {u Dtu : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDt : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (htime : ∀ i : Fin 3,
      ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z)
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0)) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → ∀ i : Fin 3,
        Tendsto (fun h : ℝ =>
            (1 / h) * ((∫ x, u (x, t + h) i * ψ x) - ∫ x, u (x, t) i * ψ x))
          (𝓝[>] 0) (𝓝 (∫ x, Dtu (x, t) i * ψ x)) := by
  classical
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  -- a countable family of tests, dense in `L²` among all tests
  let 𝒯 : Type := {ψ : Vec3 → ℝ // ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ}
  have hmem : ∀ ψ : 𝒯, MemLp ψ.1 2 volume := fun ψ =>
    ψ.2.1.continuous.memLp_of_hasCompactSupport ψ.2.2
  let ιL : 𝒯 → Lp ℝ 2 (volume : Measure Vec3) := fun ψ => (hmem ψ).toLp ψ.1
  have hR : TopologicalSpace.IsSeparable (Set.range ιL) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨C, hCR, hCcount, hCdense⟩ := hR.exists_countable_dense_subset
  choose ψc hψc using fun c : C => hCR c.2
  have : Countable C := hCcount.to_subtype
  -- time integrability of the paired derivative and of its spatial norm
  have hgpI : ∀ ψ : Vec3 → ℝ, MemLp ψ 2 volume → ∀ i : Fin 3,
      IntervalIntegrable (fun τ => ∫ x, Dtu (x, τ) i * ψ x) volume t₀ T := fun ψ hψ i =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2
      (lps_twj_pairing_integrableOn (hDt.eval i) hψ)
  have hRI : ∀ i : Fin 3,
      IntervalIntegrable (fun τ => Real.sqrt (∫ x, (Dtu (x, τ) i) ^ 2)) volume t₀ T :=
    fun i => (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2
      (lps_twj_sqrt_slice_integrableOn (hDt.eval i) le_rfl le_rfl)
  -- Lebesgue points
  have hLeb := fun (c : C) (i : Fin 3) =>
    (hgpI (ψc c).1 (hmem (ψc c)) i).ae_hasDerivAt_integral
  have hLebR := fun (i : Fin 3) => (hRI i).ae_hasDerivAt_integral
  have hsl : ∀ i : Fin 3, ∀ᵐ τ ∂volume, τ ∈ Ioc t₀ T →
      MemLp (fun x => Dtu (x, τ) i) 2 volume :=
    fun i => lps_twj_ae_slice_memLp (hDt.eval i)
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_all_iff.2 fun c : C => ae_all_iff.2 fun i => hLeb c i,
    ae_all_iff.2 hLebR, ae_all_iff.2 hsl] with t hLt hLRt hSt htI ψ hψ hψK i
  have htIcc : t ∈ uIcc t₀ T := by
    rw [uIcc_of_le hT.le]
    exact Ioo_subset_Icc_self htI
  have ht₀ : t₀ ∈ uIcc t₀ T := by
    rw [uIcc_of_le hT.le]
    exact left_mem_Icc.2 hT.le
  have hψL : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψK
  -- reduce to forward averages of the paired derivative
  refine Tendsto.congr' (f₁ := fun h : ℝ => (1 / h) * ∫ τ in t..t + h, ∫ x, Dtu (x, τ) i * ψ x)
    ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 htI.2)] with h hh
    rw [lps_slice_pairing_sub_eq_integral hT hu hDt htime hslice hcont hψ hψK i htI.1.le
      (by linarith only [hh.1]) (by linarith only [hh.2])]
  -- approximation by the countable family
  rw [Metric.tendsto_nhds]
  intro ε hε
  set A : ℝ := Real.sqrt (∫ x, (Dtu (x, t) i) ^ 2) with hAdef
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  set δ : ℝ := ε / (4 * (A + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδA : δ * (A + 1) = ε / 4 := by
    rw [hδdef]
    field_simp
  let ψT : 𝒯 := ⟨ψ, hψ, hψK⟩
  obtain ⟨c, hcC, hdist⟩ := Metric.mem_closure_iff.1 (hCdense ⟨ψT, rfl⟩) δ hδ
  set φ : Vec3 → ℝ := (ψc ⟨c, hcC⟩).1 with hφdef
  have hφL : MemLp φ 2 volume := hmem (ψc ⟨c, hcC⟩)
  have hD : Real.sqrt (∫ x, (ψ x - φ x) ^ 2) < δ := by
    have hm : MemLp (fun x => ψ x - φ x) 2 volume := hψL.sub hφL
    have e : ιL ψT - ιL (ψc ⟨c, hcC⟩) = hm.toLp (fun x => ψ x - φ x) := by
      simp only [ιL, ← MemLp.toLp_sub]
      refine MemLp.toLp_congr _ _ ?_
      exact Eventually.of_forall fun x => by simp [ψT, φ]
    rw [← lps_scalar_l2_toLp_norm_sq_integral hm, Real.sqrt_sq (norm_nonneg _), ← e,
      ← dist_eq_norm, hψc ⟨c, hcC⟩]
    exact hdist
  have hD0 : 0 ≤ Real.sqrt (∫ x, (ψ x - φ x) ^ 2) := Real.sqrt_nonneg _
  -- convergence of the averages for the member of the family and for the norm
  have hφavg := lps_twj_average_tendsto htI (hgpI φ hφL i) (hLt ⟨c, hcC⟩ i htIcc t₀ ht₀)
  have hRavg := lps_twj_average_tendsto htI (hRI i) (hLRt i htIcc t₀ ht₀)
  have hev2 : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (1 / h) * ∫ τ in t..t + h, Real.sqrt (∫ x, (Dtu (x, τ) i) ^ 2) < A + 1 :=
    hRavg.eventually (gt_mem_nhds (by linarith only : A < A + 1))
  have hev3 := Metric.tendsto_nhds.1 hφavg (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 htI.2), hev2, hev3] with h hh hRh hφh
  have hh0 : 0 < 1 / h := one_div_pos.2 hh.1
  -- the averages for `ψ` and for `φ` are close
  have hdiff := lps_twj_integral_pairing_sub_le (hDt.eval i) hψL hφL htI.1.le
    (by linarith only [hh.1] : t ≤ t + h) (by linarith only [hh.2] : t + h ≤ T)
  set P : ℝ := (1 / h) * ∫ τ in t..t + h, Real.sqrt (∫ x, (Dtu (x, τ) i) ^ 2) with hPdef
  set D : ℝ := Real.sqrt (∫ x, (ψ x - φ x) ^ 2) with hDdef
  have h1 : |(1 / h) * (∫ τ in t..t + h, ∫ x, Dtu (x, τ) i * ψ x) -
      (1 / h) * ∫ τ in t..t + h, ∫ x, Dtu (x, τ) i * φ x| ≤ D * P := by
    rw [← mul_sub, abs_mul, abs_of_pos hh0, hPdef]
    calc (1 / h) * |(∫ τ in t..t + h, ∫ x, Dtu (x, τ) i * ψ x) -
          ∫ τ in t..t + h, ∫ x, Dtu (x, τ) i * φ x|
        ≤ (1 / h) * (D * ∫ τ in t..t + h, Real.sqrt (∫ x, (Dtu (x, τ) i) ^ 2)) :=
          mul_le_mul_of_nonneg_left hdiff hh0.le
      _ = D * ((1 / h) * ∫ τ in t..t + h, Real.sqrt (∫ x, (Dtu (x, τ) i) ^ 2)) := by ring
  -- the pairings at time `t` are close
  have h2 : |(∫ x, Dtu (x, t) i * ψ x) - ∫ x, Dtu (x, t) i * φ x| ≤ A * D :=
    lps_twj_abs_pairing_sub_le (hSt i ⟨htI.1, htI.2.le⟩) hψL hφL
  rw [Real.dist_eq] at hφh ⊢
  have hDP : D * P < ε / 4 := by
    calc D * P ≤ D * (A + 1) := mul_le_mul_of_nonneg_left hRh.le hD0
      _ < δ * (A + 1) := mul_lt_mul_of_pos_right hD (by positivity)
      _ = ε / 4 := hδA
  have hAD : A * D ≤ ε / 4 := by
    calc A * D ≤ (A + 1) * δ := mul_le_mul (by linarith only) hD.le hD0 (by positivity)
      _ = ε / 4 := by rw [mul_comm]; exact hδA
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  have h3' := abs_lt.1 hφh
  rw [abs_lt]
  constructor
  · linarith only [h1'.1, h2'.2, h3'.1, hDP, hAD]
  · linarith only [h1'.2, h2'.1, h3'.2, hDP, hAD]

end ESS
