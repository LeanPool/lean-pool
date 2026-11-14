/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepPartialReflectionCompose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryOdd

/-!
# OneStepOddClassCornerMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Affine box-moment comparisons, and the full-met-set fold

Two `L²` transfer tools for the corner pricing.

1. **The controlled box comparison**
   (`normalizedL2On_coordBox_affineEval_le_of_controlled`): for an affine
   function and two nondegenerate boxes, if in every coordinate carrying a
   nonzero slope the first box's edge and centre offset are within `κ` edges of
   the second box, then the first seminorm is at most `√((24d+1)κ² + 2)` times
   the second.  Proof: the proved sharp moment identity
   `normalizedL2On_coordBox_affineEval_sq` on both boxes, the centre shift by
   `affineEval_eq_center_add`, and Cauchy–Schwarz
   (`sq_sum_le_card_mul_sum_sq`).  This generalizes the proved reverse
   Chebyshev (`normalizedL2On_coordBox_affineEval_half_le`) to boxes that are
   neither concentric nor nested, which is what the window-hugging corner slabs
   need.

2. **The full-met-set fold**
   (`normalizedL2On_reflectedWindow_le_of_faceOdd_forall`): a competitor odd
   under *every* met-face reflection has doubled-window seminorm at most `2^d`
   times its window seminorm — 's operator reconciliation composed with the
   proved cellwise `L²` cost of the odd extension.  The companion
   `normalizedL2On_reflectedWindow_affineEval_le` prices an arbitrary affine
   function on the doubled window against the window (instance of 1 at `κ = 2`:
   each reflected edge is at most doubled and each centre moves by at most half
   an edge).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `L²` data of an affine function on a box -/

/-- An affine function is square integrable on every coordinate box. -/
theorem memLp_affineEval_coordBox (lo hi : Fin d → ℝ) (c : ℝ) (g : Vec d) :
    MemLp (affineEval c g) 2 (volume.restrict (coordBox lo hi)) := by
  rw [memLp_two_iff_integrable_sq (continuous_affineEval c g).aestronglyMeasurable]
  exact integrableOn_coordBox_of_continuous ((continuous_affineEval c g).pow 2) lo hi

/-! ## 2. The controlled box comparison -/

/-- **The controlled box comparison for affine functions.**  If every
nonzero-slope coordinate of `B₁` has edge and centre offset within `κ` edges
of `B₂`, then `‖ℓ‖_{L²(B₁)} ≤ √((24d+1)κ²+2) ‖ℓ‖_{L²(B₂)}`. -/
theorem normalizedL2On_coordBox_affineEval_le_of_controlled
    {lo₁ hi₁ lo₂ hi₂ : Fin d → ℝ} (hlt₁ : ∀ l, lo₁ l < hi₁ l)
    (hlt₂ : ∀ l, lo₂ l < hi₂ l) {κ : ℝ} {c : ℝ} {g : Vec d}
    (hctrl : ∀ l, g l = 0 ∨ ((hi₁ l - lo₁ l ≤ κ * (hi₂ l - lo₂ l)) ∧
      |boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l| ≤ κ * (hi₂ l - lo₂ l))) :
    normalizedL2On (coordBox lo₁ hi₁) (affineEval c g)
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * κ ^ 2 + 2)
          * normalizedL2On (coordBox lo₂ hi₂) (affineEval c g) := by
  classical
  set C2 : ℝ := (24 * (d : ℝ) + 1) * κ ^ 2 + 2 with hC2def
  have hC2two : (2 : ℝ) ≤ C2 := by
    rw [hC2def]
    have h1 : (0 : ℝ) ≤ (24 * (d : ℝ) + 1) * κ ^ 2 := by positivity
    linarith only [h1]
  set A : ℝ := affineEval c g (boxCenter lo₂ hi₂) with hAdef
  set S : ℝ := ∑ l, g l * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l) with hSdef
  set Sig2 : ℝ := ∑ l, g l ^ 2 * ((hi₂ l - lo₂ l) ^ 2 / 12) with hSig2def
  have hSig20 : 0 ≤ Sig2 := by
    rw [hSig2def]
    refine Finset.sum_nonneg fun l _ => ?_
    positivity
  -- the centre shift
  have hshift : affineEval c g (boxCenter lo₁ hi₁) = A + S := by
    rw [hAdef, hSdef]
    exact affineEval_eq_center_add c g (boxCenter lo₂ hi₂) (boxCenter lo₁ hi₁)
  -- Cauchy–Schwarz on the shift
  have hCS : S ^ 2 ≤ (d : ℝ) * κ ^ 2 * (12 * Sig2) := by
    have h1 : S ^ 2 ≤ (d : ℝ)
        * ∑ l, (g l * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l)) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun l => g l * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l))
      rw [Finset.card_univ, Fintype.card_fin] at h
      rw [hSdef]
      exact_mod_cast h
    have h2 : ∀ l : Fin d, (g l * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l)) ^ 2
        ≤ κ ^ 2 * (g l ^ 2 * (hi₂ l - lo₂ l) ^ 2) := by
      intro l
      rcases hctrl l with hg | ⟨_, hcen⟩
      · rw [hg]
        have : (0 : ℝ) ≤ κ ^ 2 * (0 ^ 2 * (hi₂ l - lo₂ l) ^ 2) := by positivity
        calc ((0 : ℝ) * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l)) ^ 2
            = 0 := by ring
          _ ≤ κ ^ 2 * (0 ^ 2 * (hi₂ l - lo₂ l) ^ 2) := this
      · have habs : |boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l| ^ 2
            ≤ (κ * (hi₂ l - lo₂ l)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hcen 2
        rw [sq_abs] at habs
        calc (g l * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l)) ^ 2
            = g l ^ 2 * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l) ^ 2 := by ring
          _ ≤ g l ^ 2 * (κ * (hi₂ l - lo₂ l)) ^ 2 :=
              mul_le_mul_of_nonneg_left habs (sq_nonneg _)
          _ = κ ^ 2 * (g l ^ 2 * (hi₂ l - lo₂ l) ^ 2) := by ring
    have h3 : ∑ l, (g l * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l)) ^ 2
        ≤ κ ^ 2 * ∑ l, g l ^ 2 * (hi₂ l - lo₂ l) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => h2 l
    have h4 : (∑ l, g l ^ 2 * (hi₂ l - lo₂ l) ^ 2) = 12 * Sig2 := by
      rw [hSig2def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have h5 : (d : ℝ) * (κ ^ 2 * ∑ l, g l ^ 2 * (hi₂ l - lo₂ l) ^ 2)
        = (d : ℝ) * κ ^ 2 * (12 * Sig2) := by
      rw [h4]
      ring
    calc S ^ 2 ≤ (d : ℝ)
          * ∑ l, (g l * (boxCenter lo₁ hi₁ l - boxCenter lo₂ hi₂ l)) ^ 2 := h1
      _ ≤ (d : ℝ) * (κ ^ 2 * ∑ l, g l ^ 2 * (hi₂ l - lo₂ l) ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)
      _ = (d : ℝ) * κ ^ 2 * (12 * Sig2) := h5
  -- the edge comparison
  have hedges : ∑ l, g l ^ 2 * ((hi₁ l - lo₁ l) ^ 2 / 12) ≤ κ ^ 2 * Sig2 := by
    rw [hSig2def, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rcases hctrl l with hg | ⟨hedge, _⟩
    · rw [hg]
      have h0 : (0 : ℝ) ≤ κ ^ 2 * ((0:ℝ) ^ 2 * ((hi₂ l - lo₂ l) ^ 2 / 12)) := by
        positivity
      calc ((0:ℝ)) ^ 2 * ((hi₁ l - lo₁ l) ^ 2 / 12) = 0 := by ring
        _ ≤ κ ^ 2 * ((0:ℝ) ^ 2 * ((hi₂ l - lo₂ l) ^ 2 / 12)) := h0
    · have h1 : (0 : ℝ) ≤ hi₁ l - lo₁ l := by linarith only [hlt₁ l]
      have hsq : (hi₁ l - lo₁ l) ^ 2 ≤ (κ * (hi₂ l - lo₂ l)) ^ 2 :=
        pow_le_pow_left₀ h1 hedge 2
      calc g l ^ 2 * ((hi₁ l - lo₁ l) ^ 2 / 12)
          ≤ g l ^ 2 * ((κ * (hi₂ l - lo₂ l)) ^ 2 / 12) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            linarith only [hsq]
        _ = κ ^ 2 * (g l ^ 2 * ((hi₂ l - lo₂ l) ^ 2 / 12)) := by ring
  -- the squared comparison
  have hsq₁ := normalizedL2On_coordBox_affineEval_sq hlt₁ c g
  have hsq₂ := normalizedL2On_coordBox_affineEval_sq hlt₂ c g
  have hB2 : affineEval c g (boxCenter lo₁ hi₁) ^ 2 ≤ 2 * A ^ 2 + 2 * S ^ 2 := by
    rw [hshift]
    calc (A + S) ^ 2 = 2 * A ^ 2 + 2 * S ^ 2 - (A - S) ^ 2 := by ring
      _ ≤ 2 * A ^ 2 + 2 * S ^ 2 := by linarith only [sq_nonneg (A - S)]
  have hN12 : normalizedL2On (coordBox lo₁ hi₁) (affineEval c g) ^ 2
      ≤ C2 * normalizedL2On (coordBox lo₂ hi₂) (affineEval c g) ^ 2 := by
    rw [hsq₁, hsq₂, ← hAdef]
    have hA0 : 0 ≤ A ^ 2 := sq_nonneg A
    have h24 : 2 * S ^ 2 ≤ 24 * (d : ℝ) * κ ^ 2 * Sig2 := by
      have h := hCS
      linarith only [h]
    rw [hC2def]
    have hSigterm := hedges
    have hgoal : affineEval c g (boxCenter lo₁ hi₁) ^ 2
          + ∑ l, g l ^ 2 * ((hi₁ l - lo₁ l) ^ 2 / 12)
        ≤ 2 * A ^ 2 + 24 * (d : ℝ) * κ ^ 2 * Sig2 + κ ^ 2 * Sig2 := by
      linarith only [hB2, h24, hSigterm]
    calc affineEval c g (boxCenter lo₁ hi₁) ^ 2
          + ∑ l, g l ^ 2 * ((hi₁ l - lo₁ l) ^ 2 / 12)
        ≤ 2 * A ^ 2 + 24 * (d : ℝ) * κ ^ 2 * Sig2 + κ ^ 2 * Sig2 := hgoal
      _ ≤ ((24 * (d : ℝ) + 1) * κ ^ 2 + 2) * (A ^ 2 + Sig2) := by
          have hk2 : (0 : ℝ) ≤ κ ^ 2 := sq_nonneg κ
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          have h1 : (0 : ℝ) ≤ (24 * (d : ℝ) + 1) * κ ^ 2 * A ^ 2 := by positivity
          have h2 : (0 : ℝ) ≤ 2 * Sig2 := by linarith only [hSig20]
          have hexp : ((24 * (d : ℝ) + 1) * κ ^ 2 + 2) * (A ^ 2 + Sig2)
              = 2 * A ^ 2 + 24 * (d : ℝ) * κ ^ 2 * Sig2 + κ ^ 2 * Sig2
                + ((24 * (d : ℝ) + 1) * κ ^ 2 * A ^ 2 + 2 * Sig2) := by
            ring
          rw [hexp]
          linarith only [h1, h2]
  -- take square roots
  have hN10 : 0 ≤ normalizedL2On (coordBox lo₁ hi₁) (affineEval c g) :=
    normalizedL2On_nonneg _ _
  have hN20 : 0 ≤ normalizedL2On (coordBox lo₂ hi₂) (affineEval c g) :=
    normalizedL2On_nonneg _ _
  have hC20 : (0 : ℝ) ≤ C2 := by linarith only [hC2two]
  have h := Real.sqrt_le_sqrt hN12
  rwa [Real.sqrt_sq hN10, Real.sqrt_mul hC20, Real.sqrt_sq hN20, hC2def] at h

/-! ## 3. The doubled window against the window, for affine functions -/

/-- **An affine function's doubled-window seminorm is controlled by its window
seminorm**: the instance of the controlled comparison at `κ = 2`. -/
theorem normalizedL2On_reflectedWindow_affineEval_le {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (c : ℝ) (g : Vec d) :
    normalizedL2On (reflectedWindow x m k) (affineEval c g)
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 2 ^ 2 + 2)
          * normalizedL2On (truncatedWindow x m k) (affineEval c g) := by
  have hltW : ∀ l, windowLo x m k l < windowHi x m k l :=
    windowLo_lt_windowHi_of_mem hx hkm
  have hltR : ∀ l, reflectedLo x m k l < reflectedHi x m k l := fun l =>
    lt_of_le_of_lt (reflectedLo_le_windowLo hx hkm l)
      (lt_of_lt_of_le (hltW l) (windowHi_le_reflectedHi hx hkm l))
  have hctrl : ∀ l, g l = 0 ∨
      ((reflectedHi x m k l - reflectedLo x m k l
          ≤ 2 * (windowHi x m k l - windowLo x m k l)) ∧
        |boxCenter (reflectedLo x m k) (reflectedHi x m k) l
            - boxCenter (windowLo x m k) (windowHi x m k) l|
          ≤ 2 * (windowHi x m k l - windowLo x m k l)) := by
    intro l
    refine Or.inr ?_
    have hedge := hltW l
    by_cases hup : MeetsUpperFace x m k l
    · have hlow := not_meetsLowerFace_of_meetsUpperFace hkm hup
      have hRlo := reflectedLo_of_not_meetsLowerFace hlow
      have hRhi := reflectedHi_of_meetsUpperFace hup
      have hWhi := windowHi_of_meetsUpperFace hup
      have h3m : (3 : ℝ) ^ m
          = (1 / 2 : ℝ) * (3 : ℝ) ^ m + (1 / 2 : ℝ) * (3 : ℝ) ^ m := by ring
      constructor
      · rw [hRlo, hRhi, hWhi]
        linarith only [h3m]
      · rw [boxCenter_apply, boxCenter_apply, hRlo, hRhi, hWhi]
        rw [abs_le]
        constructor
        · rw [hWhi] at hedge
          linarith only [h3m, hedge]
        · rw [hWhi] at hedge
          linarith only [h3m, hedge]
    · by_cases hlow : MeetsLowerFace x m k l
      · have hRlo := reflectedLo_of_meetsLowerFace hlow
        have hRhi := reflectedHi_of_not_meetsUpperFace hup
        have hWlo := windowLo_of_meetsLowerFace hlow
        have h3m : (3 : ℝ) ^ m
            = (1 / 2 : ℝ) * (3 : ℝ) ^ m + (1 / 2 : ℝ) * (3 : ℝ) ^ m := by ring
        constructor
        · rw [hRlo, hRhi, hWlo]
          linarith only [h3m]
        · rw [boxCenter_apply, boxCenter_apply, hRlo, hRhi, hWlo]
          rw [abs_le]
          constructor
          · rw [hWlo] at hedge
            linarith only [h3m, hedge]
          · rw [hWlo] at hedge
            linarith only [h3m, hedge]
      · have hRlo := reflectedLo_of_not_meetsLowerFace hlow
        have hRhi := reflectedHi_of_not_meetsUpperFace hup
        constructor
        · rw [hRlo, hRhi]
          linarith only [hedge]
        · rw [boxCenter_apply, boxCenter_apply, hRlo, hRhi]
          rw [sub_self, abs_zero]
          linarith only [hedge]
  have h := normalizedL2On_coordBox_affineEval_le_of_controlled hltR hltW
    (κ := 2) (c := c) (g := g) hctrl
  rwa [show coordBox (windowLo x m k) (windowHi x m k) = truncatedWindow x m k from
    (truncatedWindow_eq_coordBox x m k).symm] at h

/-! ## 4. The full-met-set fold -/

/-- **The fold**: a competitor odd under every met-face reflection has
doubled-window seminorm at most `2^d` times its window seminorm. -/
theorem normalizedL2On_reflectedWindow_le_of_faceOdd_forall {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) {V : Vec d → ℝ}
    (hupV : ∀ l, MeetsUpperFace x m k l → ∀ z : Vec d,
      V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z)
    (hlowV : ∀ l, MeetsLowerFace x m k l → ∀ z : Vec d,
      V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z)
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m k))) :
    normalizedL2On (reflectedWindow x m k) V
      ≤ 2 ^ d * normalizedL2On (truncatedWindow x m k) V := by
  have hae : oddExtend x m k V =ᵐ[volume] V :=
    oddExtend_ae_eq_self_of_faceOdd_forall hkm hupV hlowV
  have haeR : oddExtend x m k V =ᵐ[volume.restrict (reflectedWindow x m k)] V :=
    MeasureTheory.ae_restrict_of_ae hae
  have hoddR : MemLp (oddExtend x m k V) 2 (volume.restrict (reflectedWindow x m k)) :=
    hVR.ae_eq haeR.symm
  have hVU : MemLp V 2 (volume.restrict (truncatedWindow x m k)) :=
    hVR.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m k) le_rfl)
  have hRpos : 0 < (volume (reflectedWindow x m k)).toReal :=
    volume_toReal_reflectedWindow_pos x hx (by omega)
  have hUpos : 0 < (volume (truncatedWindow x m k)).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have h := normalizedL2On_oddExtend_le x hkm V hRpos hUpos hoddR hVU
  rwa [normalizedL2On_congr_ae haeR] at h

/-! ## 5. A seminorm triangle for differences -/

/-- `‖f − g‖_{L²(W)} ≤ ‖f‖_{L²(W)} + ‖g‖_{L²(W)}`. -/
theorem normalizedL2On_sub_le {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) (hg : MemLp g 2 (volume.restrict W)) :
    normalizedL2On W (fun y => f y - g y)
      ≤ normalizedL2On W f + normalizedL2On W g := by
  have hgneg : MemLp (fun y => (-1 : ℝ) * g y) 2 (volume.restrict W) := by
    have h := hg.neg
    have hfun : (fun y => (-1 : ℝ) * g y) = fun y => -(g y) := by
      funext y
      ring
    rw [hfun]
    exact h
  have h := normalizedL2On_add_le hf hgneg
  have hfun : (fun y => f y + (-1 : ℝ) * g y) = fun y => f y - g y := by
    funext y
    ring
  rw [hfun] at h
  rw [normalizedL2On_const_mul] at h
  have habs : |(-1 : ℝ)| = 1 := by norm_num
  rw [habs, one_mul] at h
  exact h

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
