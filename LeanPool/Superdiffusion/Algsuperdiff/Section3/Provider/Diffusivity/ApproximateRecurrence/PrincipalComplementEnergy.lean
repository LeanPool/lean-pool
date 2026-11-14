/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DimensionFloor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BigLambdaSensitivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsCloseEighth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLegsHolder
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsCompose
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualPerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.BadEventFrozenApplication

/-!
# PrincipalComplementEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The complement-energy leg of the principal response, per grid cube

The good-event display bounds the grid average of `switchCubeEnergy` against
the complement indicator of the per-cube bad event
`principalBadEvent M Ccg R (m - h)`.  This module supplies the other half: the
same grid average against the bad event itself.

Nothing here is common to all cubes.  The envelope `B`, the load `V` and the
event all vary with the grid cube `R`, and the tail is the per-cube estimate of
`exists_badEventEstimate_perCube_dimFloor_ofFrozen` at the *same*
floor-normalized constant `Cbase` the good leg uses.  That estimate is derived
from the frozen `Algsuperdiff.Frozen.Section3.bad_event_estimate` through the
scale-shift bridge, and it carries the union-bound factor `2`, which is absorbed
here through the Hoelder power: `(2 s) ^ (3/8) = 2 ^ (3/8) . s ^ (3/8)`, and
`2 ^ (3/8)` folds into the exported envelope constant `C`, which is enlarged to
`2 ^ (3/8) . max C₀ Kgate`.  No binder and no public statement changes: the
enlargement only strengthens the premises the caller already supplies at `C`,
and the dimension-only gate `Kgate ≤ E⁻² gamma⁻¹` of the frozen application is
*derived* here from the window premise
`gamma / 2 + exp (-(C⁻¹ E⁻² gamma⁻¹)) ≤ gamma` together with
`gamma ≤ 1 / 1089`.

## Visibility

Exactly one declaration of this module is visible outside it, the grid-average
endpoint
`exists_const_descendantsAverage_integral_switchCubeEnergy_badEvent_le`.  Every
other declaration here stays private.

That endpoint returns the bad leg's per-cube integrability on the conclusion
side, alongside its estimate.  The integrability is not a new hypothesis and
nothing new is proved for it: the Hoelder split already establishes
`MemLp X (8/5)` for the cube energy, and on this finite measure that membership
read at exponent one is exactly the integrability, which then rides the
conclusion chain outward through the per-cube estimate.  A direct consumer needs
it to recombine the bad leg with the complement leg.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Elementary real bounds

The scale gap and the oscillation rate both need `t * logb 3 t⁻¹` to be small
for small `t`.  The crude `log y ≤ y - 1` is far too weak here (it only gives
`t * logb 3 t⁻¹ ≤ (log 3)⁻¹`, which the gap budget cannot absorb); applying it
at the square root instead gives a bound that vanishes with `t`.  This is stated
over abstract reals, away from any `rpow`-laden goal. -/

/-- `log y ≤ 2 √y` for `0 < y`, by applying `log y ≤ y - 1` at `√y`. -/
private theorem log_le_two_mul_sqrt {y : ℝ} (hy : 0 < y) :
    Real.log y ≤ 2 * Real.sqrt y := by
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hlog := Real.log_le_sub_one_of_pos hsqrt
  have hhalf : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy.le
  rw [hhalf] at hlog
  have : Real.sqrt y - 1 ≤ Real.sqrt y := by linarith
  linarith

/-- `t * logb 3 t⁻¹ ≤ 2 * √t / log 3` for `0 < t`.  The right-hand side tends to
zero with `t`, which is what the scale-gap budget needs. -/
private theorem mul_logb_inv_le_sqrt {t : ℝ} (ht : 0 < t) :
    t * Real.logb 3 t⁻¹ ≤ 2 * Real.sqrt t / Real.log 3 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htinv : 0 < t⁻¹ := inv_pos.2 ht
  have hle : Real.log t⁻¹ ≤ 2 * Real.sqrt t⁻¹ := log_le_two_mul_sqrt htinv
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsq : t * Real.sqrt t⁻¹ = Real.sqrt t := by
    rw [Real.sqrt_inv]
    field_simp
    exact (Real.sq_sqrt ht.le).symm
  have hmul : t * Real.log t⁻¹ ≤ 2 * Real.sqrt t := by
    calc t * Real.log t⁻¹ ≤ t * (2 * Real.sqrt t⁻¹) :=
          mul_le_mul_of_nonneg_left hle ht.le
      _ = 2 * (t * Real.sqrt t⁻¹) := by ring
      _ = 2 * Real.sqrt t := by rw [hsq]
  rw [Real.logb,
    show t * (Real.log t⁻¹ / Real.log 3) = t * Real.log t⁻¹ / Real.log 3 by ring]
  gcongr

/-- `t * logb 3 t⁻¹ ≤ 2 √t`, discharging the `log 3` denominator by `1 ≤ log 3`. -/
private theorem mul_logb_inv_le_two_sqrt {t : ℝ} (ht : 0 < t) :
    t * Real.logb 3 t⁻¹ ≤ 2 * Real.sqrt t := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact le_trans Real.exp_one_lt_d9.le (by norm_num)
  exact (mul_logb_inv_le_sqrt ht).trans
    (div_le_self (by positivity) hlog3)

/-- **The scale-gap weight, collapsed to a numeral.**  At the recurrence
mesoscale the exponent `2 gamma (m - n)` splits into the buffer part, bounded by
`18` from `h ≤ 6 cstar gamma⁻¹` and `cstar ≤ 3/2`, and the logarithmic part,
bounded through `mul_logb_inv_le_two_sqrt` once `gamma ≤ 1 / 1089`, i.e. once
`√gamma ≤ 1 / 33`. -/
private theorem multiscaleDescendantWeight_recurrenceMesoScale_le (M : ABKModel d)
    (m h : ℤ) {a : ℕ} (ha : a ≤ 32)
    (hh : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹)
    (hgamma : M.gamma ≤ 1 / 1089) :
    Ch02.multiscaleDescendantWeight (originCube d m)
        (recurrenceMesoScale a M.gamma m h) M.gamma ≤ (3 : ℝ) ^ (22 : ℝ) := by
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  rw [Algsuperdiff.Section3.Provider.ErrorComparison.multiscaleDescendantWeight_originCube]
  refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).2 ?_
  have hk : ((recurrenceMesoScale a M.gamma m h : ℤ) : ℝ) =
      (m : ℝ) - (h : ℝ) - ((recurrenceGap a M.gamma : ℕ) : ℝ) := by
    rw [recurrenceMesoScale]
    push_cast
    ring
  rw [hk]
  have hlogb0 : 0 ≤ Real.logb 3 M.gamma⁻¹ := by
    refine Real.logb_nonneg (by norm_num) ?_
    rw [le_inv_comm₀ (by norm_num) hgpos]
    linarith [hgamma]
  have hceil : ((Nat.ceil (Real.logb 3 M.gamma⁻¹) : ℕ) : ℝ) ≤
      Real.logb 3 M.gamma⁻¹ + 1 := (Nat.ceil_lt_add_one hlogb0).le
  have hgap : ((recurrenceGap a M.gamma : ℕ) : ℝ) ≤
      32 * (Real.logb 3 M.gamma⁻¹ + 1) := by
    rw [recurrenceGap, logThreeCeil]
    push_cast
    have ha' : ((a : ℕ) : ℝ) ≤ 32 := by exact_mod_cast ha
    have hc0 : (0 : ℝ) ≤ ((Nat.ceil (Real.logb 3 M.gamma⁻¹) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    nlinarith [hceil, hc0, ha']
  have hbuffer : 2 * M.gamma * (h : ℝ) ≤ 18 := by
    have h1 : 2 * M.gamma * (h : ℝ) ≤
        2 * M.gamma * (6 * Disorder.cstar M * M.gamma⁻¹) := by
      have : (0 : ℝ) ≤ 2 * M.gamma := by linarith
      exact mul_le_mul_of_nonneg_left hh this
    have h2 : 2 * M.gamma * (6 * Disorder.cstar M * M.gamma⁻¹) =
        12 * Disorder.cstar M := by
      field_simp
      ring
    rw [h2] at h1
    linarith
  have hsqrt : Real.sqrt M.gamma ≤ 1 / 33 := by
    have h1 : Real.sqrt M.gamma ≤ Real.sqrt (1 / 1089) := Real.sqrt_le_sqrt hgamma
    have h2 : Real.sqrt (1 / 1089 : ℝ) = 1 / 33 := by
      rw [show (1 / 1089 : ℝ) = (1 / 33) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    linarith [h1, h2.le, h2.ge]
  have hlogpart : 2 * M.gamma * (32 * (Real.logb 3 M.gamma⁻¹ + 1)) ≤
      64 * (2 * Real.sqrt M.gamma) + 64 * M.gamma := by
    have hcore := mul_logb_inv_le_two_sqrt hgpos
    nlinarith [hcore]
  have hgamma0 : M.gamma ≤ 1 / 1089 := hgamma
  nlinarith [hbuffer, hgap, hlogpart, hsqrt, hgamma0, hgpos.le,
    Real.sqrt_nonneg M.gamma]

/-! ## The moment leg -/

section AbstractMoment

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- **The moment leg.**  A nonnegative `f` dominated by `W * g`, with `g` in
`L^8` of eighth moment inside `A ^ 8`, has eighth moment inside `(W * A) ^ 8`.
The two `rpow` folds are `Real.mul_rpow`, used once pointwise to split
`(W * g x) ^ 8` and once at the end to recombine `W ^ 8 * A ^ 8`. -/
private theorem integral_rpow_eight_le_of_le_const_mul {f g : Omega → ℝ}
    {W A : ℝ} (hW0 : 0 ≤ W) (hA0 : 0 ≤ A)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hle : ∀ x, f x ≤ W * g x) (hgmem : MemLp g 8 mu)
    (hgmom : ∫ x, g x ^ (8 : ℝ) ∂mu ≤ A ^ (8 : ℝ)) :
    ∫ x, f x ^ (8 : ℝ) ∂mu ≤ (W * A) ^ (8 : ℝ) := by
  have hg8 : Integrable (fun x => g x ^ (8 : ℝ)) mu := by
    have h := (integrable_norm_rpow_iff hgmem.aestronglyMeasurable
      (by norm_num) (by norm_num)).mpr hgmem
    rw [show (8 : ℝ≥0∞).toReal = (8 : ℝ) by norm_num] at h
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    change ‖g x‖ ^ (8 : ℝ) = g x ^ (8 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
  have hpt : ∀ x, f x ^ (8 : ℝ) ≤ W ^ (8 : ℝ) * g x ^ (8 : ℝ) := by
    intro x
    have h1 : f x ^ (8 : ℝ) ≤ (W * g x) ^ (8 : ℝ) :=
      Real.rpow_le_rpow (hf0 x) (hle x) (by norm_num)
    rwa [Real.mul_rpow hW0 (hg0 x)] at h1
  have hmono : ∫ x, f x ^ (8 : ℝ) ∂mu ≤ ∫ x, W ^ (8 : ℝ) * g x ^ (8 : ℝ) ∂mu :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hf0 x) _)
      (hg8.const_mul _) (Filter.Eventually.of_forall hpt)
  have hW8 : (0 : ℝ) ≤ W ^ (8 : ℝ) := Real.rpow_nonneg hW0 _
  calc ∫ x, f x ^ (8 : ℝ) ∂mu
      ≤ ∫ x, W ^ (8 : ℝ) * g x ^ (8 : ℝ) ∂mu := hmono
    _ = W ^ (8 : ℝ) * ∫ x, g x ^ (8 : ℝ) ∂mu := integral_const_mul _ _
    _ ≤ W ^ (8 : ℝ) * A ^ (8 : ℝ) := mul_le_mul_of_nonneg_left hgmom hW8
    _ = (W * A) ^ (8 : ℝ) := (Real.mul_rpow hW0 hA0).symm

/-- Stated over an abstract carrier so that no definitional depth of the envelope
reaches the unifier: the caller instantiates `B` and `G` after the fact. -/
private theorem memLp_and_integral_of_le_two_mul {B G : Omega → ℝ} {W A : ℝ}
    (hW0 : 0 ≤ W) (hA0 : 0 ≤ A) (hB0 : ∀ x, 0 ≤ B x) (hG0 : ∀ x, 0 ≤ G x)
    (hBm : AEStronglyMeasurable B mu) (hle : ∀ x, B x ≤ W * (2 * G x))
    (hGmem : MemLp G 8 mu) (hGmom : ∫ x, G x ^ (8 : ℝ) ∂mu ≤ A ^ (8 : ℝ)) :
    MemLp B 8 mu ∧
      ∫ x, B x ^ (8 : ℝ) ∂mu ≤ (W * (2 * A)) ^ (8 : ℝ) := by
  have h2G0 : ∀ x, 0 ≤ 2 * G x := fun x => by linarith [hG0 x]
  have h2Gmem : MemLp (fun x => 2 * G x) 8 mu := hGmem.const_mul 2
  have h2Gmom : ∫ x, (2 * G x) ^ (8 : ℝ) ∂mu ≤ (2 * A) ^ (8 : ℝ) :=
    integral_rpow_eight_le_of_le_const_mul (by norm_num) hA0 h2G0 hG0
      (fun _ => le_rfl) hGmem hGmom
  refine ⟨?_, ?_⟩
  · refine MemLp.mono (h2Gmem.const_mul W) hBm
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hB0 x)]
    exact (hle x).trans (le_abs_self _)
  · exact integral_rpow_eight_le_of_le_const_mul hW0 (by positivity) hB0 h2G0
      hle h2Gmem h2Gmom

/-- **Step 2, load leg.**  The square root of a nonnegative `N` with integrable
square lies in `L^4`, since `‖√N‖ ^ 4 = N ^ 2` pointwise.  Abstract in `N`, so
the concrete load never reaches this statement. -/
private theorem memLp_sqrt_four_of_integrable_sq {N : Omega → ℝ}
    (hN0 : ∀ x, 0 ≤ N x)
    (hNm : AEStronglyMeasurable (fun x => Real.sqrt (N x)) mu)
    (hNsq : Integrable (fun x => N x ^ (2 : ℕ)) mu) :
    MemLp (fun x => Real.sqrt (N x)) 4 mu := by
  refine (integrable_norm_rpow_iff hNm (by norm_num) (by norm_num)).mp ?_
  refine hNsq.congr (Filter.Eventually.of_forall fun x => ?_)
  change N x ^ (2 : ℕ) = ‖Real.sqrt (N x)‖ ^ (4 : ℝ≥0∞).toReal
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    show (4 : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show Real.sqrt (N x) ^ (4 : ℕ) = (Real.sqrt (N x) ^ (2 : ℕ)) ^ (2 : ℕ) by ring,
    Real.sq_sqrt (hN0 x)]

/-- **Step 2, response leg.**  With `X` below `B * V ^ 2` and the two seminorm
bounds in hand, `eLpNorm_energy_le_of_moments` already places `X` inside a
finite `L^{8/5}` seminorm, so membership is that bound paired with the
measurability of `X`.  Abstract in `B`, `V`, `X`. -/
private theorem memLp_eightFifths_of_moments {B V X : Omega → ℝ}
    (hB0 : ∀ x, 0 ≤ B x) (hV0 : ∀ x, 0 ≤ V x) (hX0 : ∀ x, 0 ≤ X x)
    (hdom : ∀ x, X x ≤ B x * V x ^ (2 : ℕ))
    (hXm : AEStronglyMeasurable X mu) (hBm : AEStronglyMeasurable B mu)
    (hVm : AEStronglyMeasurable V mu) {Cb Cv : ℝ} (hCb0 : 0 ≤ Cb) (hCv0 : 0 ≤ Cv)
    (hBn : eLpNorm B 8 mu ≤ ENNReal.ofReal Cb)
    (hVn : eLpNorm V 4 mu ≤ ENNReal.ofReal Cv) :
    MemLp X (8 / 5 : ℝ≥0∞) mu :=
  (lt_of_le_of_lt
      (eLpNorm_energy_le_of_moments hB0 hV0 hX0 hdom hXm hBm hVm hCb0 hCv0 hBn hVn)
      ENNReal.ofReal_lt_top)

/-- `ENNReal.ofReal (8/5)` is the literal `8/5`. -/
private theorem ofReal_eightFifths'' :
    ENNReal.ofReal (8 / 5 : ℝ) = (8 / 5 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- **Step 3: the per-cube Hoelder split.**  The registered chain — energy
seminorm bound, descent to the real moment root, indicator split at tail power
`3/8` — assembled over abstract carriers.  The exponent pair is `(8/5, 8/3)`. -/
private theorem integral_mul_indicator_le_of_two_moments [IsFiniteMeasure mu]
    {B V X : Omega → ℝ} {Ebad : Set Omega} {Cb Cv tail : ℝ}
    (hB0 : ∀ x, 0 ≤ B x) (hV0 : ∀ x, 0 ≤ V x) (hX0 : ∀ x, 0 ≤ X x)
    (hdom : ∀ x, X x ≤ B x * V x ^ (2 : ℕ))
    (hXm : AEStronglyMeasurable X mu) (hBm : AEStronglyMeasurable B mu)
    (hVm : AEStronglyMeasurable V mu) (hCb0 : 0 ≤ Cb) (hCv0 : 0 ≤ Cv)
    (hBn : eLpNorm B 8 mu ≤ ENNReal.ofReal Cb)
    (hVn : eLpNorm V 4 mu ≤ ENNReal.ofReal Cv)
    (hE : MeasurableSet Ebad) (htail : mu.real Ebad ≤ tail) :
    Integrable (fun x => X x * Ebad.indicator (fun _ => (1 : ℝ)) x) mu ∧
      ∫ x, X x * Ebad.indicator (fun _ => (1 : ℝ)) x ∂mu ≤
        Cb * Cv ^ (2 : ℕ) * tail ^ ((3 : ℝ) / 8) := by
  have hmem : MemLp X (ENNReal.ofReal (8 / 5 : ℝ)) mu := by
    rw [ofReal_eightFifths'']
    exact memLp_eightFifths_of_moments hB0 hV0 hX0 hdom hXm hBm hVm hCb0 hCv0 hBn hVn
  -- the same membership, read at exponent one, gives the leg's integrability
  have hXint : Integrable X mu := by
    refine memLp_one_iff_integrable.mp (hmem.mono_exponent ?_)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hindint : Integrable (fun x => X x * Ebad.indicator (fun _ => (1 : ℝ)) x) mu := by
    refine Integrable.mono' hXint
      (hXm.mul (measurable_one.indicator hE).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have hi0 : (0 : ℝ) ≤ Ebad.indicator (fun _ => (1 : ℝ)) x :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have hi : Ebad.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
      by_cases hx : x ∈ Ebad
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [Real.norm_of_nonneg (mul_nonneg (hX0 x) hi0)]
    calc X x * Ebad.indicator (fun _ => (1 : ℝ)) x ≤ X x * 1 :=
          mul_le_mul_of_nonneg_left hi (hX0 x)
      _ = X x := mul_one _
  refine ⟨hindint, ?_⟩
  have hseminorm : eLpNorm X (ENNReal.ofReal (8 / 5 : ℝ)) mu ≤
      ENNReal.ofReal (Cb * Cv ^ (2 : ℕ)) := by
    rw [ofReal_eightFifths'']
    exact eLpNorm_energy_le_of_moments hB0 hV0 hX0 hdom hXm hBm hVm hCb0 hCv0 hBn hVn
  have hroot : (∫ x, X x ^ (8 / 5 : ℝ) ∂mu) ^ ((1 : ℝ) / (8 / 5 : ℝ)) ≤
      Cb * Cv ^ (2 : ℕ) :=
    integral_rpow_le_of_eLpNorm_le hX0 (by norm_num) hmem (by positivity) hseminorm
  have hroot' : (∫ x, X x ^ (8 / 5 : ℝ) ∂mu) ^ ((5 : ℝ) / 8) ≤ Cb * Cv ^ (2 : ℕ) := by
    rwa [show (1 : ℝ) / (8 / 5 : ℝ) = (5 : ℝ) / 8 by norm_num] at hroot
  exact integral_mul_indicator_le_of_moment
    (Filter.Eventually.of_forall hX0) hmem hE hroot' (by positivity) htail

end AbstractMoment

/-! ## The cube-independent operator envelope -/

/-- The **centred** operator envelope `B` at the centred cube of a given scale: `2
(sigma⁻¹ Lambda_{s,q} + sigma lambda⁻¹_{s,q})`. -/
def coarseEnvelopeCentred (M : ABKModel d) (cutoffScale : ℤ)
    (sigma : PositiveScalar) (k : ℤ) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    CutoffSample d → ℝ :=
  fun omega =>
    2 * ((sigma : ℝ)⁻¹ *
        Ch02.LambdaSq (originCube d k) s q
          (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) +
      (sigma : ℝ) *
        (Ch02.lambdaSq (originCube d k) s q
          (coefficientCutoffTriadicCoeffFamily M cutoffScale omega))⁻¹)

/-- **The per-cube energy dominated by the centred envelope.**

`switchCubeEnergy` unfolds to the left-hand side of
`blockVecDot_coarseBlockMatrix_le_operatorEnvelope`, whose envelope lives on the
cube `R`.  The two deterministic translation covariances move that envelope to
the centred cube of the same scale, evaluated at the translated sample, so the
majorant is `B ∘ translateCutoffSample (triadicCubeShift R)` with `B`
independent of `R`. -/
private theorem switchCubeEnergy_le_coarseEnvelopeCentred [NeZero d]
    (M : ABKModel d) (cutoffScale : ℤ) (sigma : PositiveScalar)
    (R : TriadicCube d) {s : ℝ} {q : Ch02.MultiscaleExponent}
    (hs : 0 < s) (hq : q.IsAdmissible) (Y : BlockVec d)
    (omega : CutoffSample d) :
    switchCubeEnergy M cutoffScale R Y omega ≤
      coarseEnvelopeCentred M cutoffScale sigma R.scale s q
          (translateCutoffSample (triadicCubeShift R) omega) *
        Real.sqrt (annealedSqrtNormSq sigma Y) ^ (2 : ℕ) := by
  have h := blockVecDot_coarseBlockMatrix_le_operatorEnvelope sigma R
    (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) hs hq Y
  have hL :=
    Algsuperdiff.Section3.Provider.Multiscale.LambdaSq_cutoff_translateCutoffSample
      M cutoffScale R s q omega
  have hl :=
    Algsuperdiff.Section3.Provider.BadEvents.lambdaSq_cutoff_translateCutoffSample
      M cutoffScale R s q omega
  refine le_trans h (le_of_eq ?_)
  simp only [coarseEnvelopeCentred, ← hL, ← hl]

/-! ## The two endpoint identifications, at independent domain and cutoff scales -/

/-- The centred upper endpoint, at domain scale `k` and cutoff scale `L`.  This
is `Tail.cutoffUpperEllipticityLiteral_eq` with the two scales kept apart; the
domain and the cutoff enter the definition independently. -/
private theorem lambdaSqUpper_eq_cutoffUpperEllipticity (M : ABKModel d) (k L : ℤ)
    {s : ℝ} (hs : 0 < s) (q : CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    Ch02.LambdaSq (originCube d k) s q.1
        (coefficientCutoffTriadicCoeffFamily M L omega) =
      Observable.cutoffUpperEllipticity M k L s hs q omega := by
  let : NeZero d := Algsuperdiff.Section3.Provider.BadEvents.neZeroOfModel M
  rw [congrFun (Observable.cutoffUpperEllipticity_eq_literal M k L s hs q) omega]
  change _ = Ch04.LambdaSqCoeffField (originCube d k) s q.1
      (Cutoff.coefficientCutoff M.nu L omega)
  rw [Ch04.LambdaSqCoeffField]
  simp only [dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)]
  exact Ch02.LambdaSq_eq_ofAEEq
    (Algsuperdiff.Section3.Provider.Tail.coefficientCutoffFamily_aeeq M L omega)
    (originCube d k) s q.1

/-- The centred inverse lower endpoint, at domain scale `k` and cutoff scale
`L`. -/
private theorem lambdaSqLower_inv_eq_cutoffLowerEllipticityInv (M : ABKModel d)
    (k L : ℤ) {s : ℝ} (hs : 0 < s) (q : CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    (Ch02.lambdaSq (originCube d k) s q.1
        (coefficientCutoffTriadicCoeffFamily M L omega))⁻¹ =
      Observable.cutoffLowerEllipticityInv M k L s hs q omega := by
  rw [congrFun (Observable.cutoffLowerEllipticityInv_eq_literal M k L s hs q) omega,
    ← congrFun
      (Algsuperdiff.Section3.Provider.BadEvents.cubeLowerEllipticityInvLiteral_originCube
        M k L s q) omega,
    ← Algsuperdiff.Section3.Provider.BadEvents.cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq
        M (originCube d k) L s q omega,
    inv_inv]

/-- The centred envelope written at the carrier of
`integral_coarseEllipticityGauge_rpow_eight_le`: twice the gauged sum of the
two multiscale endpoints. -/
private theorem coarseEnvelopeCentred_eq_gauge (M : ABKModel d) (k L : ℤ)
    {s : ℝ} (hs : 0 < s) (q : CoarseEllipticityExponent)
    (sigma : PositiveScalar) (omega : CutoffSample d) :
    coarseEnvelopeCentred M L sigma k s q.1 omega =
      2 * (Observable.cutoffUpperEllipticity M k L s hs q omega * (sigma : ℝ)⁻¹ +
        Observable.cutoffLowerEllipticityInv M k L s hs q omega * (sigma : ℝ)) := by
  rw [coarseEnvelopeCentred,
    lambdaSqUpper_eq_cutoffUpperEllipticity M k L hs q omega,
    lambdaSqLower_inv_eq_cutoffLowerEllipticityInv M k L hs q omega]
  ring

/-- The centred envelope is measurable, through its gauge form. -/
private theorem measurable_coarseEnvelopeCentred (M : ABKModel d) (k L : ℤ)
    {s : ℝ} (hs : 0 < s) (q : CoarseEllipticityExponent)
    (sigma : PositiveScalar) :
    Measurable (coarseEnvelopeCentred M L sigma k s q.1) := by
  have hfun : coarseEnvelopeCentred M L sigma k s q.1 =
      fun omega =>
        2 * (Observable.cutoffUpperEllipticity M k L s hs q omega * (sigma : ℝ)⁻¹ +
          Observable.cutoffLowerEllipticityInv M k L s hs q omega * (sigma : ℝ)) := by
    funext omega
    exact coarseEnvelopeCentred_eq_gauge M k L hs q sigma omega
  rw [hfun]
  exact
    (((Observable.measurable_cutoffUpperEllipticity M k L s hs q).mul_const _).add
      ((Observable.measurable_cutoffLowerEllipticityInv M k L s hs q).mul_const _)).const_mul 2

/-- The centred envelope is nonnegative, through its gauge form. -/
private theorem coarseEnvelopeCentred_nonneg (M : ABKModel d) (k L : ℤ)
    {s : ℝ} (hs : 0 < s) (q : CoarseEllipticityExponent)
    (sigma : PositiveScalar) (omega : CutoffSample d) :
    0 ≤ coarseEnvelopeCentred M L sigma k s q.1 omega := by
  rw [coarseEnvelopeCentred_eq_gauge M k L hs q sigma omega]
  have hu : 0 ≤ Observable.cutoffUpperEllipticity M k L s hs q omega :=
    Observable.cutoffUpperEllipticity_nonneg M k L s hs q omega
  have hl : 0 ≤ Observable.cutoffLowerEllipticityInv M k L s hs q omega :=
    Observable.cutoffLowerEllipticityInv_nonneg M k L s hs q omega
  have hs0 : (0 : ℝ) ≤ (sigma : ℝ) := sigma.2.le
  have hsi : (0 : ℝ) ≤ ((sigma : ℝ))⁻¹ := (inv_pos.2 sigma.2).le
  have h1 : 0 ≤ Observable.cutoffUpperEllipticity M k L s hs q omega * (sigma : ℝ)⁻¹ :=
    mul_nonneg hu hsi
  have h2 : 0 ≤ Observable.cutoffLowerEllipticityInv M k L s hs q omega * (sigma : ℝ) :=
    mul_nonneg hl hs0
  linarith

/-! ## Promotion from the cube scale to the field scale -/

/-- **The descendant promotion.**  The centred envelope at the cube scale `k` is
below `multiscaleDescendantWeight` times the centred envelope at the field scale
`m`.  Both legs of the sum carry the *same* weight, so it factors out of the
whole envelope. -/
private theorem coarseEnvelopeCentred_le_weight_mul [NeZero d] (M : ABKModel d)
    (cutoffScale : ℤ) (sigma : PositiveScalar) {k m : ℤ} (hkm : k ≤ m)
    {s : ℝ} {q : Ch02.MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible)
    (omega : CutoffSample d) :
    coarseEnvelopeCentred M cutoffScale sigma k s q omega ≤
      Ch02.multiscaleDescendantWeight (originCube d m) k s *
        coarseEnvelopeCentred M cutoffScale sigma m s q omega := by
  have hmem :=
    Algsuperdiff.Section3.Provider.ErrorComparison.originCube_mem_descendantsAtScale
      (d := d) hkm
  have hUp := Ch02.descendant_LambdaSq_le
    (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) hmem hs hq
  have hLo := Ch02.descendant_lambdaSq_inv_le
    (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) hmem hs hq
  have hsiginv0 : (0 : ℝ) ≤ ((sigma : ℝ))⁻¹ := (inv_pos.2 sigma.2).le
  have hsig0 : (0 : ℝ) ≤ (sigma : ℝ) := sigma.2.le
  have h1 := mul_le_mul_of_nonneg_left hUp hsiginv0
  have h2 := mul_le_mul_of_nonneg_left hLo hsig0
  simp only [coarseEnvelopeCentred]
  have hstep :
      2 * ((sigma : ℝ)⁻¹ *
            Ch02.LambdaSq (originCube d k) s q
              (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) +
          (sigma : ℝ) *
            (Ch02.lambdaSq (originCube d k) s q
              (coefficientCutoffTriadicCoeffFamily M cutoffScale omega))⁻¹) ≤
        2 * ((sigma : ℝ)⁻¹ *
              (Ch02.multiscaleDescendantWeight (originCube d m) k s *
                Ch02.LambdaSq (originCube d m) s q
                  (coefficientCutoffTriadicCoeffFamily M cutoffScale omega)) +
            (sigma : ℝ) *
              (Ch02.multiscaleDescendantWeight (originCube d m) k s *
                (Ch02.lambdaSq (originCube d m) s q
                  (coefficientCutoffTriadicCoeffFamily M cutoffScale omega))⁻¹)) := by
    linarith
  exact hstep.trans (le_of_eq (by ring))

/-- No cube, no translation and no weight appear here; the gauge endpoint is taken
at `L = m`, and the event cutoff plays no role. -/
private theorem memLp_and_integral_envelope_field (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma →
          MemLp
              (coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) m M.gamma
                coarseExponentOne.1)
              8 (Cutoff.cutoffSampleLaw M).toMeasure ∧
            ∫ omega,
                (coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) m M.gamma
                  coarseExponentOne.1 omega) ^ (8 : ℝ)
                ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
              (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) ^ (8 : ℝ) := by
  obtain ⟨C, hC0, hgauge⟩ := integral_coarseEllipticityGauge_rpow_eight_le d
  refine ⟨C, hC0, ?_⟩
  intro M m E hstate hE hEupper hgap
  have hcstar0 : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  obtain ⟨hmemG, hmomG⟩ := hgauge M m E hstate hE hEupper hgap m (by omega)
  have hgauge_eq : ∀ omega : CutoffSample d,
      coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) m M.gamma
          coarseExponentOne.1 omega =
        2 * (Observable.cutoffUpperEllipticity M m m M.gamma
                M.shellPrefix.gamma_pos coarseExponentOne omega *
              (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ +
            Observable.cutoffLowerEllipticityInv M m m M.gamma
                M.shellPrefix.gamma_pos coarseExponentOne omega *
              (Annealed.sigmaBar M (m - 1) : ℝ)) := fun omega =>
    coarseEnvelopeCentred_eq_gauge M m m M.shellPrefix.gamma_pos coarseExponentOne
      (Annealed.sigmaBar M (m - 1)) omega
  have hres := memLp_and_integral_of_le_two_mul
    (B := coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) m M.gamma
      coarseExponentOne.1)
    (G := fun omega =>
      Observable.cutoffUpperEllipticity M m m M.gamma M.shellPrefix.gamma_pos
          coarseExponentOne omega * (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ +
        Observable.cutoffLowerEllipticityInv M m m M.gamma M.shellPrefix.gamma_pos
          coarseExponentOne omega * (Annealed.sigmaBar M (m - 1) : ℝ))
    (W := 1) (A := C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)
    (by norm_num) (by positivity)
    (fun omega =>
      coarseEnvelopeCentred_nonneg M m m M.shellPrefix.gamma_pos coarseExponentOne
        (Annealed.sigmaBar M (m - 1)) omega)
    (fun omega => by
      have h := coarseEnvelopeCentred_nonneg M m m M.shellPrefix.gamma_pos
        coarseExponentOne (Annealed.sigmaBar M (m - 1)) omega
      rw [hgauge_eq omega] at h
      linarith)
    (measurable_coarseEnvelopeCentred M m m M.shellPrefix.gamma_pos
      coarseExponentOne (Annealed.sigmaBar M (m - 1))).aestronglyMeasurable
    (fun omega => le_of_eq (by rw [hgauge_eq omega]; ring))
    hmemG hmomG
  refine ⟨hres.1, ?_⟩
  have h := hres.2
  rwa [one_mul] at h

/-! ## Transport along the base-point translation -/

/-- The cutoff sample law is invariant under the base-point translation, so the
translated envelope has the same law as the centred one. -/
private theorem measurePreserving_translateCutoffSample (M : ABKModel d)
    (z : Vec d) :
    MeasurePreserving (translateCutoffSample (d := d) z)
      (cutoffSampleLaw M).toMeasure (cutoffSampleLaw M).toMeasure :=
  ⟨measurable_translateCutoffSample z, map_translateCutoffSample_cutoffSampleLaw M z⟩

/-- Integrals against the cutoff sample law are unchanged by the base-point
translation. -/
private theorem integral_comp_translateCutoffSample (M : ABKModel d) (z : Vec d)
    {f : CutoffSample d → ℝ}
    (hf : AEStronglyMeasurable f (cutoffSampleLaw M).toMeasure) :
    ∫ omega, f (translateCutoffSample z omega) ∂(cutoffSampleLaw M).toMeasure =
      ∫ omega, f omega ∂(cutoffSampleLaw M).toMeasure := by
  have hmap := map_translateCutoffSample_cutoffSampleLaw M z
  have hf' : AEStronglyMeasurable f
      (Measure.map (translateCutoffSample (d := d) z)
        (cutoffSampleLaw M).toMeasure) := by
    rw [hmap]
    exact hf
  have h := integral_map (measurable_translateCutoffSample z).aemeasurable hf'
  rw [hmap] at h
  exact h.symm

/-- `MemLp` transports along the base-point translation. -/
private theorem memLp_comp_translateCutoffSample (M : ABKModel d) (z : Vec d)
    {f : CutoffSample d → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (cutoffSampleLaw M).toMeasure) :
    MemLp (fun omega => f (translateCutoffSample z omega)) p
      (cutoffSampleLaw M).toMeasure :=
  hf.comp_measurePreserving (measurePreserving_translateCutoffSample M z)

/-! ## The per-cube complement energy -/

private theorem principalComplementEnergy_comparisonBounds1 :
    ∀ (d : ℕ) (C : ℝ) (M : ABKModel d) (m h : ℤ) (a : ℕ) (R : TriadicCube d) (_ : a ≤ (32 : ℕ))
      (_ : R.scale = recurrenceMesoScale a M.gamma m h) (_ : M.gamma ≤ (1 / 1089 : ℝ))
      (_ : (↑h : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹),
      let _ : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩;
      ∀ (_ : (0 : ℝ) < M.gamma) (_ : (0 : ℝ) ≤ (2 : ℝ) * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹))
        (_ : (0 : ℝ) < (3 : ℝ) ^ (22 : ℝ)) (_ : R.scale ≤ m)
        (_ :
          MemLp
            (coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - (1 : ℤ))) m M.gamma
              coarseExponentOne.1)
            (8 : ℝ≥0∞) (↑(cutoffSampleLaw M) : Measure (CutoffSample d)))
        (_ :
          ∫ (omega : CutoffSample d),
              coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - (1 : ℤ))) m M.gamma
                  coarseExponentOne.1 omega ^
                (8 : ℝ) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)) ≤
            ((2 : ℝ) * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) ^ (8 : ℝ))
        (_ :
          ∀ (omega : CutoffSample d),
            (0 : ℝ) ≤
              coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - (1 : ℤ))) m M.gamma
                coarseExponentOne.1 omega),
        (∀ (omega : CutoffSample d),
            (0 : ℝ) ≤
              coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - (1 : ℤ))) R.scale M.gamma
                coarseExponentOne.1 omega) ∧
          MemLp
              (fun (omega : CutoffSample d) =>
                coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - (1 : ℤ))) R.scale M.gamma
                  coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega))
              (8 : ℝ≥0∞) (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) ∧
            AEStronglyMeasurable
                (fun (omega : CutoffSample d) =>
                  coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - (1 : ℤ))) R.scale M.gamma
                    coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega))
                (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) ∧
              ∫ (omega : CutoffSample d),
                  coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - (1 : ℤ))) R.scale M.gamma
                      coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega) ^
                    (8 : ℝ) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)) ≤
                ((3 : ℝ) ^ (22 : ℝ) * ((2 : ℝ) * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹))) ^ (8 :
                  ℝ) := by
  intro d C M m h _ R ha hRscale hgamma hh _ hgpos hA0 hW0 hRm hGmem hGmom hG0
  have hF0 : ∀ omega : CutoffSample d,
      0 ≤ coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
        coarseExponentOne.1 omega := fun omega =>
    coarseEnvelopeCentred_nonneg M R.scale m hgpos coarseExponentOne
      (Annealed.sigmaBar M (m - 1)) omega
  have hFm : Measurable
      (coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
        coarseExponentOne.1) :=
    measurable_coarseEnvelopeCentred M R.scale m hgpos coarseExponentOne
      (Annealed.sigmaBar M (m - 1))
  -- the descendant promotion, at the numeral of the recurrence mesoscale
  have hweight : Ch02.multiscaleDescendantWeight (originCube d m) R.scale M.gamma ≤
      (3 : ℝ) ^ (22 : ℝ) := by
    rw [hRscale]
    exact multiscaleDescendantWeight_recurrenceMesoScale_le M m h ha hh hgamma
  have hFle : ∀ omega : CutoffSample d,
      coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
          coarseExponentOne.1 omega ≤
        (3 : ℝ) ^ (22 : ℝ) *
          coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) m M.gamma
            coarseExponentOne.1 omega := by
    intro omega
    exact (coarseEnvelopeCentred_le_weight_mul M m (Annealed.sigmaBar M (m - 1)) hRm
      hgpos coarseExponentOne.2 omega).trans
      (mul_le_mul_of_nonneg_right hweight (hG0 omega))
  have hFmem : MemLp
      (coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
        coarseExponentOne.1) 8 (cutoffSampleLaw M).toMeasure := by
    refine MemLp.mono (hGmem.const_mul ((3 : ℝ) ^ (22 : ℝ))) hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hF0 omega)]
    exact (hFle omega).trans (le_abs_self _)
  have hFmom : ∫ omega : CutoffSample d,
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
            coarseExponentOne.1 omega ^ (8 : ℝ) ∂(cutoffSampleLaw M).toMeasure ≤
      ((3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹))) ^ (8 : ℝ) :=
    integral_rpow_eight_le_of_le_const_mul hW0.le hA0 hF0 hG0 hFle hGmem hGmom
  -- the same two facts at the cube's base point
  have hBmem : MemLp
      (fun omega : CutoffSample d =>
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
          coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega))
      8 (cutoffSampleLaw M).toMeasure :=
    memLp_comp_translateCutoffSample M (triadicCubeShift R) hFmem
  have hBm : AEStronglyMeasurable
      (fun omega : CutoffSample d =>
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
          coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega))
      (cutoffSampleLaw M).toMeasure :=
    (hFm.comp (measurable_translateCutoffSample (triadicCubeShift R))).aestronglyMeasurable
  have hBmom : ∫ omega : CutoffSample d,
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
            coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega) ^ (8 : ℝ)
        ∂(cutoffSampleLaw M).toMeasure ≤
      ((3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹))) ^ (8 : ℝ) := by
    have hpow : AEStronglyMeasurable
        (fun omega : CutoffSample d =>
          coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
            coarseExponentOne.1 omega ^ (8 : ℝ)) (cutoffSampleLaw M).toMeasure :=
      (((Real.continuous_rpow_const
        (by norm_num : (0 : ℝ) ≤ 8)).measurable).comp hFm).aestronglyMeasurable
    rw [integral_comp_translateCutoffSample M (triadicCubeShift R) hpow]
    exact hFmom
  exact ⟨hF0, hBmem, hBm, hBmom⟩

private theorem principalComplementEnergy_comparisonBounds2 :
    ∀ (d : ℕ) (Kgate C : ℝ) (_ : (0 : ℝ) < C),
      let Cout : ℝ := (2 : ℝ) ^ (3 / 8 : ℝ) * max C Kgate;
      ∀ (_ : (0 : ℝ) < Cout) (_ : C ≤ Cout) (_ : Kgate ≤ Cout) (M : ABKModel d)
        (E : { E : ℝ // (1 : ℝ) ≤ E }) (m h : ℤ) (a : ℕ) (R : TriadicCube d) (_ : (0 : ℤ) < h)
        (_ : R.scale = recurrenceMesoScale a M.gamma m h)
        (_ : max (Real.exp ((2 : ℝ) * Cout)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
        (_ : M.gamma / (2 : ℝ) + Real.exp (-(Cout⁻¹ * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) ≤ M.gamma)
        (_ : M.gamma ≤ (1 / 1089 : ℝ)),
        (0 : ℝ) < M.gamma ∧
          (0 : ℝ) < Disorder.cstar M ∧
            (0 : ℝ) < M.gamma⁻¹ ∧
              M.gamma / (2 : ℝ) + Real.exp (-(C⁻¹ * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) ≤ M.gamma ∧
                max (Real.exp ((2 : ℝ) * C)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ) ∧
                  Kgate ≤ (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹ ∧
                    (0 : ℝ) ≤ (2 : ℝ) * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) ∧
                      (0 : ℝ) < (3 : ℝ) ^ (22 : ℝ) ∧
                        (0 : ℝ) ≤ (3 : ℝ) ^ (22 : ℝ) * ((2 : ℝ) * (C * (Disorder.cstar M)⁻¹ *
                          M.gamma⁻¹)) ∧
                          R.scale ≤ m ∧ R.scale ≤ m - h := by
  intro _ Kgate C hC0 Cout hCout0 hCleCout hKleCout M E m h a R _ hRscale hEexp hwindow hgamma
  have hgpos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  -- the enlarged exported constant, read back at the envelope constant
  have hginv0 : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgpos
  have hinvCC : Cout⁻¹ ≤ C⁻¹ := by
    rw [inv_le_inv₀ hCout0 hC0]
    exact hCleCout
  have hmonoWin : Cout⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ ≤
      C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hinvCC (sq_nonneg _)) hginv0.le
  have hwindowC : M.gamma / 2 +
      Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma := by
    have h := Real.exp_le_exp.2 (neg_le_neg hmonoWin)
    linarith [hwindow]
  have hEexpC : max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    max_le (le_trans (Real.exp_le_exp.2 (by linarith)) ((le_max_left _ _).trans hEexp))
      ((le_max_right _ _).trans hEexp)
  -- the dimension-only gate of the frozen application, from the window premise
  have hKgateE : Kgate ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by
    have hw : Real.exp (-(Cout⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma / 2 := by
      linarith [hwindow]
    have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hinv : (1 : ℝ) / 2178 ≤ 1 / Real.exp 1 :=
      one_div_le_one_div_of_le hpos (by linarith)
    have hsmall : M.gamma / 2 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      linarith [hgamma, hinv]
    have hle1 : (1 : ℝ) ≤ Cout⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by
      have h := Real.exp_le_exp.1 (le_trans hw hsmall)
      linarith
    have heq : Cout * (Cout⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) =
        ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by
      field_simp
    calc Kgate ≤ Cout := hKleCout
      _ = Cout * 1 := (mul_one _).symm
      _ ≤ Cout * (Cout⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) :=
          mul_le_mul_of_nonneg_left hle1 hCout0.le
      _ = ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := heq
  have hA0 : (0 : ℝ) ≤ 2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) := by
    have h1 : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar0
    have h2 : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgpos
    have h3 : (0 : ℝ) < C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ :=
      mul_pos (mul_pos hC0 h1) h2
    linarith
  have hW0 : (0 : ℝ) < (3 : ℝ) ^ (22 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hCb0 : (0 : ℝ) ≤ (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) :=
    mul_nonneg hW0.le hA0
  -- the two scale comparisons carried by the mesoscale identity
  have hRm : R.scale ≤ m := by
    rw [hRscale]
    simp only [recurrenceMesoScale]
    omega
  have hRn : R.scale ≤ m - h := by
    rw [hRscale]
    simp only [recurrenceMesoScale]
    omega
  exact ⟨hgpos, hcstar0, hginv0, hwindowC, hEexpC, hKgateE, hA0, hW0, hCb0, hRm, hRn⟩

/-- **The per-cube complement-energy estimate.**

At a triadic cube `R` whose scale is the recurrence mesoscale `n - a *
ceil|log_3 cgamma|`, the expectation of the cube energy against the indicator
of the per-cube bad event `principalBadEvent M (2 Cbase) R (m - h)` is inside

```
  3^22 . ( 2 C cstar^{-1} cgamma^{-1} ) . sqrt( E[ |bfAhom^{1/2} P|^4 ] ) . P[bad]^{3/8} .
```

The three factors are the three inputs of the Hoelder split: the eighth moment
of the operator envelope, promoted from the cube scale to the field scale by
`multiscaleDescendantWeight` and moved to the cube's base point by the
translation invariance of the cutoff sample law; the fourth moment of the load,
left as a moment so that the grid average can supply it; and the bad-event
probability at the floor-normalized constant.

The load family `P` is arbitrary: neither the envelope nor the event depends on
it, and only its two well-definedness binders are used.  The `3^22` is the
numeral of `multiscaleDescendantWeight_recurrenceMesoScale_le`, available once
`a <= 32`, `h <= 6 cstar cgamma^{-1}` and `cgamma <= 1 / 1089`.

The tail power is `3/8`; the second summand of the envelope carries
the inverse.

: this statement holds only under the propositions supplied by its binders. -/
private theorem exists_const_integral_switchCubeEnergy_mul_principalBadEvent_indicator_le
    (d : ℕ) :
    ∃ Cbase c C : ℝ, 1 ≤ Cbase ∧ (d : ℝ) ^ 6 ≤ Cbase ∧ 0 < c ∧ 0 < C ∧
      ∀ (M : ABKModel d) (E : {E : ℝ // 1 ≤ E}) (m h : ℤ) (a : ℕ)
        (R : TriadicCube d) (P : CutoffSample d → BlockVec d),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        0 < h →
        a ≤ 32 →
        R.scale = recurrenceMesoScale a M.gamma m h →
        max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        c⁻¹ * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma →
        M.gamma ≤ 1 / 1089 →
        (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
        AEStronglyMeasurable
            (fun omega : CutoffSample d => switchCubeEnergy M m R (P omega) omega)
            (cutoffSampleLaw M).toMeasure →
        AEStronglyMeasurable
            (fun omega : CutoffSample d =>
              Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)))
            (cutoffSampleLaw M).toMeasure →
        Integrable
            (fun omega : CutoffSample d =>
              annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega) ^ (2 : ℕ))
            (cutoffSampleLaw M).toMeasure →
          Integrable
              (fun omega : CutoffSample d =>
                switchCubeEnergy M m R (P omega) omega *
                  (principalBadEvent M (2 * Cbase) R (m - h)).indicator
                    (fun _ => (1 : ℝ)) omega)
              (cutoffSampleLaw M).toMeasure ∧
          ∫ omega : CutoffSample d,
              switchCubeEnergy M m R (P omega) omega *
                (principalBadEvent M (2 * Cbase) R (m - h)).indicator
                  (fun _ => (1 : ℝ)) omega
              ∂(cutoffSampleLaw M).toMeasure ≤
            (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) *
                Real.sqrt
                  (∫ omega : CutoffSample d,
                    annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega) ^ (2 : ℕ)
                    ∂(cutoffSampleLaw M).toMeasure) *
              (Real.exp
                  (-(c * Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (-5 * Provider.BadEvents.scaleGapPos (m - h) R.scale) *
                    (3 : ℝ) ^ Provider.BadEvents.scaleGapPos R.scale (m - h))) +
                Real.exp (-Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ^
                ((3 : ℝ) / 8) := by
  classical
  obtain ⟨Cbase, c, Kgate, hCbase, hCbased, hc, hKgate0, hbad⟩ :=
    exists_badEventEstimate_perCube_dimFloor_ofFrozen d
  obtain ⟨C, hC0, henv⟩ := memLp_and_integral_envelope_field d
  have hroot2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 8) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 8)
    simpa using h
  have hroot20 : (0 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 8) := by linarith
  set Cout : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 8) * max C Kgate with hCoutDef
  have hCmax0 : (0 : ℝ) < max C Kgate := lt_of_lt_of_le hC0 (le_max_left _ _)
  have hCout0 : (0 : ℝ) < Cout := by
    rw [hCoutDef]
    exact mul_pos (by linarith) hCmax0
  have hCr : C * (2 : ℝ) ^ ((3 : ℝ) / 8) ≤ Cout := by
    rw [hCoutDef]
    have := mul_le_mul_of_nonneg_left (le_max_left C Kgate) hroot20
    linarith [this]
  have hCleCout : C ≤ Cout := by nlinarith [hCr, hroot2, hC0]
  have hKleCout : Kgate ≤ Cout := by
    rw [hCoutDef]
    have := mul_le_mul_of_nonneg_left (le_max_right C Kgate) hroot20
    nlinarith [this, hroot2, hKgate0]
  refine ⟨Cbase, c, Cout, hCbase, hCbased, hc, hCout0, ?_⟩
  intro M E m h a R P hstate hh0 ha hRscale hEexp hEadm hEgamma hwindow hgamma hh
    hXm hVm hVint
  let : NeZero d := Algsuperdiff.Section3.Provider.BadEvents.neZeroOfModel M
  obtain ⟨hgpos, hcstar0, hginv0, hwindowC, hEexpC, hKgateE, hA0, hW0, hCb0, hRm, hRn⟩ :=
    (show ((0 : ℝ) < M.gamma) ∧ ((0 : ℝ) < Disorder.cstar M) ∧ ((0 : ℝ) < M.gamma⁻¹) ∧ (M.gamma /
      2 +
      Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma) ∧ (max (Real.exp (2 * C))
        (Disorder.cstar M)⁻¹ ≤ (E : ℝ)) ∧ (Kgate ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) ∧ ((0 : ℝ) ≤ 2 *
          (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) ∧ ((0 : ℝ) < (3 : ℝ) ^ (22 : ℝ)) ∧ ((0 : ℝ) ≤ (3
            : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹))) ∧ (R.scale ≤ m) ∧
              (R.scale ≤ m - h) from
      @principalComplementEnergy_comparisonBounds2 (d) (Kgate) (C) (hC0) (hCout0) (hCleCout)
        (hKleCout) (M) (E) (m) (h) (a) (R) (hh0) (hRscale) (hEexp) (hwindow) (hgamma))
  -- the field-scale envelope, its membership and its eighth moment
  obtain ⟨hGmem, hGmom⟩ := henv M m E hstate hEexpC hEgamma hwindowC
  have hG0 : ∀ omega : CutoffSample d,
      0 ≤ coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) m M.gamma
        coarseExponentOne.1 omega := fun omega =>
    coarseEnvelopeCentred_nonneg M m m hgpos coarseExponentOne
      (Annealed.sigmaBar M (m - 1)) omega
  obtain ⟨hF0, hBmem, hBm, hBmom⟩ :=
    (show (∀ omega : CutoffSample d,
      0 ≤ coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
        coarseExponentOne.1 omega) ∧ (MemLp
      (fun omega : CutoffSample d =>
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
          coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega))
      8 (cutoffSampleLaw M).toMeasure) ∧ (AEStronglyMeasurable
      (fun omega : CutoffSample d =>
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
          coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega))
      (cutoffSampleLaw M).toMeasure) ∧ (∫ omega : CutoffSample d,
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
            coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega) ^ (8 : ℝ)
        ∂(cutoffSampleLaw M).toMeasure ≤
      ((3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹))) ^ (8 : ℝ)) from
      @principalComplementEnergy_comparisonBounds1 (d) (C) (M) (m) (h) (a) (R) (ha) (hRscale)
        (hgamma) (hh) (hgpos) (hA0) (hW0) (hRm) (hGmem) (hGmom) (hG0))
  have hBn : eLpNorm
      (fun omega : CutoffSample d =>
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
          coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega))
      8 (cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹))) :=
    eLpNorm_eight_le_ofReal_of_moment (fun omega => hF0 _) hBmem hCb0 hBmom
  -- the load leg
  have hN0 : ∀ omega : CutoffSample d,
      0 ≤ annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega) := fun omega =>
    annealedSqrtNormSq_nonneg _ _
  have hVmem : MemLp
      (fun omega : CutoffSample d =>
        Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)))
      4 (cutoffSampleLaw M).toMeasure :=
    memLp_sqrt_four_of_integrable_sq hN0 hVm hVint
  set m4 : ℝ := ∫ omega : CutoffSample d,
    annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega) ^ (2 : ℕ)
    ∂(cutoffSampleLaw M).toMeasure with hm4
  have hm40 : 0 ≤ m4 := by
    rw [hm4]
    exact integral_nonneg fun omega => pow_nonneg (hN0 omega) 2
  have hCv0 : (0 : ℝ) ≤ m4 ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hm40 _
  have hV4 : ∀ omega : CutoffSample d,
      Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)) ^ (4 : ℝ) =
        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega) ^ (2 : ℕ) := by
    intro omega
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)) ^ (4 : ℕ) =
          (Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)) ^ (2 : ℕ)) ^
            (2 : ℕ) by ring,
      Real.sq_sqrt (hN0 omega)]
  have hVmom : ∫ omega : CutoffSample d,
        Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)) ^ (4 : ℝ)
        ∂(cutoffSampleLaw M).toMeasure ≤ (m4 ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) := by
    have hroot : (m4 ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) = m4 := by
      rw [← Real.rpow_mul hm40]
      norm_num
    rw [hroot, integral_congr_ae (Filter.Eventually.of_forall hV4), ← hm4]
  have hVn : eLpNorm
      (fun omega : CutoffSample d =>
        Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)))
      4 (cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (m4 ^ ((1 : ℝ) / 4)) :=
    eLpNorm_four_le_ofReal_of_moment (fun omega => Real.sqrt_nonneg _) hVmem hCv0 hVmom
  -- the pointwise domination, the nonnegativity and the event
  have hdom : ∀ omega : CutoffSample d,
      switchCubeEnergy M m R (P omega) omega ≤
        coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
            coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega) *
          Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)) ^ (2 : ℕ) :=
    fun omega =>
      switchCubeEnergy_le_coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R
        hgpos coarseExponentOne.2 (P omega) omega
  have hX0 : ∀ omega : CutoffSample d, 0 ≤ switchCubeEnergy M m R (P omega) omega :=
    fun _ => blockVecDot_coarseBlockMatrix_nonneg _ _ _
  have hE : MeasurableSet (principalBadEvent M (2 * Cbase) R (m - h)) :=
    measurableSet_principalBadEvent M (2 * Cbase) R (m - h)
  set t : ℝ :=
    Real.exp
        (-(c * Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (-5 * Provider.BadEvents.scaleGapPos (m - h) R.scale) *
          (3 : ℝ) ^ Provider.BadEvents.scaleGapPos R.scale (m - h))) +
      Real.exp (-Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) with htdef
  have ht0 : (0 : ℝ) ≤ t := by
    rw [htdef]
    positivity
  have htail : (cutoffSampleLaw M).toMeasure.real
      (principalBadEvent M (2 * Cbase) R (m - h)) ≤ 2 * t :=
    hbad M m E hstate hEadm hEgamma hKgateE R (m - h) (by omega) hRn
  obtain ⟨hint, hmain⟩ := integral_mul_indicator_le_of_two_moments
    (mu := (cutoffSampleLaw M).toMeasure)
    (B := fun omega : CutoffSample d =>
      coarseEnvelopeCentred M m (Annealed.sigmaBar M (m - 1)) R.scale M.gamma
        coarseExponentOne.1 (translateCutoffSample (triadicCubeShift R) omega))
    (V := fun omega : CutoffSample d =>
      Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P omega)))
    (X := fun omega : CutoffSample d => switchCubeEnergy M m R (P omega) omega)
    (Ebad := principalBadEvent M (2 * Cbase) R (m - h))
    (fun omega => hF0 _) (fun _ => Real.sqrt_nonneg _) hX0 hdom hXm hBm hVm hCb0
    hCv0 hBn hVn hE htail
  have hsq : (m4 ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) = Real.sqrt m4 := by
    rw [← Real.rpow_natCast (m4 ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hm40,
      Real.sqrt_eq_rpow]
    norm_num
  rw [hsq] at hmain
  refine ⟨hint, le_trans hmain ?_⟩
  -- the union-bound factor `2`, absorbed by the Hoelder power into the envelope
  have hmulrpow : ((2 : ℝ) * t) ^ ((3 : ℝ) / 8) =
      (2 : ℝ) ^ ((3 : ℝ) / 8) * t ^ ((3 : ℝ) / 8) := Real.mul_rpow (by norm_num) ht0
  have ht38 : (0 : ℝ) ≤ t ^ ((3 : ℝ) / 8) := Real.rpow_nonneg ht0 _
  have hS0 : (0 : ℝ) ≤ Real.sqrt m4 := Real.sqrt_nonneg _
  have hab : (0 : ℝ) ≤ (3 : ℝ) ^ (22 : ℝ) * 2 * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hW0.le (by norm_num))
      (inv_pos.2 hcstar0).le) hginv0.le
  have hconst : (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) *
        (2 : ℝ) ^ ((3 : ℝ) / 8) ≤
      (3 : ℝ) ^ (22 : ℝ) * (2 * (Cout * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) := by
    calc (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) *
          (2 : ℝ) ^ ((3 : ℝ) / 8)
        = ((3 : ℝ) ^ (22 : ℝ) * 2 * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) *
            (C * (2 : ℝ) ^ ((3 : ℝ) / 8)) := by ring
      _ ≤ ((3 : ℝ) ^ (22 : ℝ) * 2 * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) * Cout :=
          mul_le_mul_of_nonneg_left hCr hab
      _ = (3 : ℝ) ^ (22 : ℝ) * (2 * (Cout * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) := by ring
  calc (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) *
        Real.sqrt m4 * ((2 : ℝ) * t) ^ ((3 : ℝ) / 8)
      = ((3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) *
          (2 : ℝ) ^ ((3 : ℝ) / 8)) * Real.sqrt m4 * t ^ ((3 : ℝ) / 8) := by
        rw [hmulrpow]
        ring
    _ ≤ ((3 : ℝ) ^ (22 : ℝ) * (2 * (Cout * (Disorder.cstar M)⁻¹ * M.gamma⁻¹))) *
          Real.sqrt m4 * t ^ ((3 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hS0) ht38

/-! ## The grid average of the complement energy -/

/-- **The bad-event leg at the grid average.**

On a grid of depth-`j` triadic descendants of `Q` whose common scale `Q.scale -
j` is the recurrence mesoscale, the discrete Cauchy--Schwarz step of
`gridAverage_badEventEnergy_le` turns the per-cube square roots of the previous
estimate into the square root of the grid average, which is the left-hand side
of the fourth-moment display.  The tail is the same for every cube of the grid,
since every cube of the grid has the same scale.

`Cv` enters as the fourth root of the grid average of the load moment, a named
binder: nothing here estimates that average.  The three well-definedness binders
are the per-cube ones of the previous estimate.

: this statement holds only under the propositions supplied by its binders. -/
theorem exists_const_descendantsAverage_integral_switchCubeEnergy_badEvent_le
    (d : ℕ) :
    ∃ Cbase c C : ℝ, 1 ≤ Cbase ∧ (d : ℝ) ^ 6 ≤ Cbase ∧ 0 < c ∧ 0 < C ∧
      ∀ (M : ABKModel d) (E : {E : ℝ // 1 ≤ E}) (m h : ℤ) (a : ℕ) (Q : TriadicCube d)
        (j : ℕ) (P : TriadicCube d → CutoffSample d → BlockVec d) (Cv : ℝ),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        0 < h →
        a ≤ 32 →
        Q.scale - (j : ℤ) = recurrenceMesoScale a M.gamma m h →
        max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        c⁻¹ * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma →
        M.gamma ≤ 1 / 1089 →
        (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
        0 ≤ Cv →
        (∀ R ∈ descendantsAtDepth Q j,
          AEStronglyMeasurable
            (fun omega : CutoffSample d => switchCubeEnergy M m R (P R omega) omega)
            (cutoffSampleLaw M).toMeasure) →
        (∀ R ∈ descendantsAtDepth Q j,
          AEStronglyMeasurable
            (fun omega : CutoffSample d =>
              Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P R omega)))
            (cutoffSampleLaw M).toMeasure) →
        (∀ R ∈ descendantsAtDepth Q j,
          Integrable
            (fun omega : CutoffSample d =>
              annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P R omega) ^ (2 : ℕ))
            (cutoffSampleLaw M).toMeasure) →
        descendantsAverage Q j
            (fun R => ∫ omega : CutoffSample d,
              annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P R omega) ^ (2 : ℕ)
              ∂(cutoffSampleLaw M).toMeasure) ≤ Cv ^ (4 : ℕ) →
          (∀ R ∈ descendantsAtDepth Q j,
            Integrable
              (fun omega : CutoffSample d =>
                switchCubeEnergy M m R (P R omega) omega *
                  (principalBadEvent M (2 * Cbase) R (m - h)).indicator
                    (fun _ => (1 : ℝ)) omega)
              (cutoffSampleLaw M).toMeasure) ∧
          descendantsAverage Q j
              (fun R => ∫ omega : CutoffSample d,
                switchCubeEnergy M m R (P R omega) omega *
                  (principalBadEvent M (2 * Cbase) R (m - h)).indicator
                    (fun _ => (1 : ℝ)) omega
                ∂(cutoffSampleLaw M).toMeasure) ≤
            (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) *
                Cv ^ (2 : ℕ) *
              (Real.exp
                  (-(c * Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (-5 * Provider.BadEvents.scaleGapPos (m - h)
                      (recurrenceMesoScale a M.gamma m h)) *
                    (3 : ℝ) ^ Provider.BadEvents.scaleGapPos
                      (recurrenceMesoScale a M.gamma m h) (m - h))) +
                Real.exp (-Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ^
                ((3 : ℝ) / 8) := by
  classical
  obtain ⟨Cbase, c, C, hCbase, hCbased, hc, hC0, hcube⟩ :=
    exists_const_integral_switchCubeEnergy_mul_principalBadEvent_indicator_le d
  refine ⟨Cbase, c, C, hCbase, hCbased, hc, hC0, ?_⟩
  intro M E m h a Q j P Cv hstate hh0 ha hscale hEexp hEadm hEgamma hwindow hgamma hh
    hCv0 hXm hVm hVint havg
  have hgpos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hA0 : (0 : ℝ) ≤ 2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹) := by
    have h1 : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar0
    have h2 : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgpos
    have h3 : (0 : ℝ) < C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ :=
      mul_pos (mul_pos hC0 h1) h2
    linarith
  have hCb0 : (0 : ℝ) ≤ (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) :=
    mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le hA0
  set t : ℝ :=
    (Real.exp
        (-(c * Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (-5 * Provider.BadEvents.scaleGapPos (m - h)
            (recurrenceMesoScale a M.gamma m h)) *
          (3 : ℝ) ^ Provider.BadEvents.scaleGapPos
            (recurrenceMesoScale a M.gamma m h) (m - h))) +
      Real.exp (-Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ^ ((3 : ℝ) / 8) with ht
  have ht0 : (0 : ℝ) ≤ t := by
    rw [ht]
    positivity
  -- every cube of the grid sits at the recurrence mesoscale
  have hRscale : ∀ R ∈ descendantsAtDepth Q j,
      R.scale = recurrenceMesoScale a M.gamma m h := by
    intro R hR
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hscale]
  have hm40 : ∀ R : TriadicCube d,
      0 ≤ ∫ omega : CutoffSample d,
        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P R omega) ^ (2 : ℕ)
        ∂(cutoffSampleLaw M).toMeasure := fun R =>
    integral_nonneg fun omega => pow_nonneg (annealedSqrtNormSq_nonneg _ _) 2
  have hpint : ∀ R ∈ descendantsAtDepth Q j,
      Integrable
        (fun omega : CutoffSample d =>
          switchCubeEnergy M m R (P R omega) omega *
            (principalBadEvent M (2 * Cbase) R (m - h)).indicator
              (fun _ => (1 : ℝ)) omega)
        (cutoffSampleLaw M).toMeasure := fun R hR =>
    (hcube M E m h a R (P R) hstate hh0 ha (hRscale R hR) hEexp hEadm
      hEgamma hwindow hgamma hh (hXm R hR) (hVm R hR) (hVint R hR)).1
  refine ⟨hpint, ?_⟩
  have hpbad : ∀ R ∈ descendantsAtDepth Q j,
      (∫ omega : CutoffSample d,
          switchCubeEnergy M m R (P R omega) omega *
            (principalBadEvent M (2 * Cbase) R (m - h)).indicator
              (fun _ => (1 : ℝ)) omega
          ∂(cutoffSampleLaw M).toMeasure) ≤
        (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) *
            Real.sqrt
              (∫ omega : CutoffSample d,
                annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P R omega) ^ (2 : ℕ)
                ∂(cutoffSampleLaw M).toMeasure) * t := by
    intro R hR
    have hres := (hcube M E m h a R (P R) hstate hh0 ha (hRscale R hR) hEexp hEadm
      hEgamma hwindow hgamma hh (hXm R hR) (hVm R hR) (hVint R hR)).2
    rw [hRscale R hR] at hres
    rw [ht]
    exact hres
  have hexp : ∀ G : TriadicCube d → ℝ, descendantsAverage Q j G =
      (∑ R ∈ descendantsAtDepth Q j, G R) / ((descendantsAtDepth Q j).card : ℝ) := by
    intro G
    change ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, G R = _
    rw [div_eq_inv_mul]
  rcases Finset.eq_empty_or_nonempty (descendantsAtDepth Q j) with hempty | hne
  · rw [hexp, hempty]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero]
    exact mul_nonneg (mul_nonneg hCb0 (pow_nonneg hCv0 2)) ht0
  · rw [hexp] at havg ⊢
    exact gridAverage_badEventEnergy_le hne _ _ (fun R _ => hm40 R) hCb0 ht0 hpbad havg

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
