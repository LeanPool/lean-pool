/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Data.EReal.Inv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.QuasiPshSingularities

/-!
# Absolute differences of extended-real potentials

The expression `|a - b|` is undefined in the usual extended-real arithmetic
when both values are negative infinity.  For integration against a measure
which does not charge the common pole locus, one may choose a finite value on
that locus.  Outside it, Mathlib's `EReal.abs` preserves both infinite values
by returning `top : ENNReal`.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- The absolute extended-real difference, with a prescribed finite value on
the common negative-infinity locus.  No other infinite value is truncated. -/
def poleModifiedERealAbsDiff (c : NNReal) (a b : EReal) : ENNReal :=
  if a = ⊥ ∧ b = ⊥ then (c : ENNReal) else (a - b).abs

/-- The canonical representative used below chooses zero on the common pole
locus and retains `top` at every one-sided infinite difference. -/
def canonicalERealAbsDiff (a b : EReal) : ENNReal :=
  poleModifiedERealAbsDiff 0 a b

/-- The signed real difference of two extended-real values, with a prescribed
finite value on their common negative-infinity locus.  At a point where both
values are finite this is the ordinary real difference.  The separate
one-sided infinite cases are retained by `EReal` until the final `toReal`; in
applications below they are excluded by the common-pole and no-`top`
hypotheses. -/
def poleModifiedERealDiffToReal (c : ℝ) (a b : EReal) : ℝ :=
  if a = ⊥ ∧ b = ⊥ then c else (a - b).toReal

/-- The canonical signed difference chooses zero on the common pole locus. -/
def canonicalERealDiffToReal (a b : EReal) : ℝ :=
  poleModifiedERealDiffToReal 0 a b

@[simp] theorem poleModifiedERealAbsDiff_bot_bot (c : NNReal) :
    poleModifiedERealAbsDiff c ⊥ ⊥ = c := by
  simp [poleModifiedERealAbsDiff]

@[simp] theorem canonicalERealAbsDiff_bot_bot :
    canonicalERealAbsDiff ⊥ ⊥ = 0 := by
  simp [canonicalERealAbsDiff]

@[simp] theorem poleModifiedERealDiffToReal_bot_bot (c : ℝ) :
    poleModifiedERealDiffToReal c ⊥ ⊥ = c := by
  simp [poleModifiedERealDiffToReal]

theorem canonicalERealDiffToReal_bot_bot :
    canonicalERealDiffToReal ⊥ ⊥ = 0 := by
  simp [canonicalERealDiffToReal]

@[simp] theorem poleModifiedERealAbsDiff_coe_coe
    (c : NNReal) (a b : ℝ) :
    poleModifiedERealAbsDiff c (a : EReal) (b : EReal) =
      ENNReal.ofReal |a - b| := by
  simp [poleModifiedERealAbsDiff, ← EReal.coe_sub, EReal.abs_def]

@[simp] theorem canonicalERealAbsDiff_coe_coe (a b : ℝ) :
    canonicalERealAbsDiff (a : EReal) (b : EReal) =
      ENNReal.ofReal |a - b| := by
  simp [canonicalERealAbsDiff]

/-- The canonical extended absolute difference is Borel measurable on the
whole square, including all four combinations of infinite values. -/
theorem measurable_canonicalERealAbsDiff :
    Measurable (fun p : EReal × EReal =>
      canonicalERealAbsDiff p.1 p.2) := by
  apply EReal.measurable_of_real_real
  · have hdiff : Measurable (fun p : ℝ × ℝ => p.1 - p.2) :=
      measurable_fst.sub measurable_snd
    simpa only [canonicalERealAbsDiff_coe_coe, Real.norm_eq_abs] using
      hdiff.norm.ennreal_ofReal
  · simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  · simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  · simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  · simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]

theorem Measurable.canonicalERealAbsDiff {X : Type*} [MeasurableSpace X]
    {u v : X → EReal} (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun x => canonicalERealAbsDiff (u x) (v x)) :=
  measurable_canonicalERealAbsDiff.comp (hu.prodMk hv)

@[simp] theorem poleModifiedERealDiffToReal_coe_coe
    (c a b : ℝ) :
    poleModifiedERealDiffToReal c (a : EReal) (b : EReal) = a - b := by
  simp [poleModifiedERealDiffToReal, ← EReal.coe_sub]

@[simp] theorem canonicalERealDiffToReal_coe_coe (a b : ℝ) :
    canonicalERealDiffToReal (a : EReal) (b : EReal) = a - b := by
  simp [canonicalERealDiffToReal]

@[simp] theorem poleModifiedERealAbsDiff_bot_left
    (c : NNReal) {b : EReal} (hb : b ≠ ⊥) :
    poleModifiedERealAbsDiff c ⊥ b = ⊤ := by
  simp [poleModifiedERealAbsDiff, hb]

@[simp] theorem canonicalERealAbsDiff_bot_left
    {b : EReal} (hb : b ≠ ⊥) :
    canonicalERealAbsDiff ⊥ b = ⊤ := by
  simp [canonicalERealAbsDiff, hb]

@[simp] theorem poleModifiedERealAbsDiff_bot_right
    (c : NNReal) {a : EReal} (ha : a ≠ ⊥) :
    poleModifiedERealAbsDiff c a ⊥ = ⊤ := by
  simp [poleModifiedERealAbsDiff, ha, EReal.sub_bot]

@[simp] theorem canonicalERealAbsDiff_bot_right
    {a : EReal} (ha : a ≠ ⊥) :
    canonicalERealAbsDiff a ⊥ = ⊤ := by
  simp [canonicalERealAbsDiff, ha]

@[simp] theorem poleModifiedERealDiffToReal_bot_left
    (c : ℝ) {b : EReal} (hb : b ≠ ⊥) :
    poleModifiedERealDiffToReal c ⊥ b = 0 := by
  simp [poleModifiedERealDiffToReal, hb]

@[simp] theorem canonicalERealDiffToReal_bot_left
    {b : EReal} (hb : b ≠ ⊥) :
    canonicalERealDiffToReal ⊥ b = 0 := by
  simp [canonicalERealDiffToReal, hb]

@[simp] theorem poleModifiedERealDiffToReal_bot_right
    (c : ℝ) {a : EReal} (ha : a ≠ ⊥) :
    poleModifiedERealDiffToReal c a ⊥ = 0 := by
  simp [poleModifiedERealDiffToReal, ha, EReal.sub_bot]

@[simp] theorem canonicalERealDiffToReal_bot_right
    {a : EReal} (ha : a ≠ ⊥) :
    canonicalERealDiffToReal a ⊥ = 0 := by
  simp [canonicalERealDiffToReal, ha]

@[simp] theorem canonicalERealDiffToReal_self (a : EReal) :
    canonicalERealDiffToReal a a = 0 := by
  cases a <;> simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal]

theorem poleModifiedERealDiffToReal_swap (c : ℝ) (a b : EReal) :
    poleModifiedERealDiffToReal c a b =
      -poleModifiedERealDiffToReal (-c) b a := by
  cases a <;> cases b <;>
    simp [poleModifiedERealDiffToReal, ← EReal.coe_sub]

theorem canonicalERealDiffToReal_swap (a b : EReal) :
    canonicalERealDiffToReal a b = -canonicalERealDiffToReal b a := by
  simpa [canonicalERealDiffToReal] using
    poleModifiedERealDiffToReal_swap 0 a b

/-- Away from `top`, a common-pole equivalence is exactly what is needed to
recover the absolute difference from the canonical signed difference. -/
theorem canonicalERealAbsDiff_eq_ofReal_abs_diff
    {a b : EReal} (ha_top : a ≠ ⊤) (hb_top : b ≠ ⊤)
    (hpole : a = ⊥ ↔ b = ⊥) :
    canonicalERealAbsDiff a b =
      ENNReal.ofReal |canonicalERealDiffToReal a b| := by
  cases a <;> cases b <;>
    simp_all [canonicalERealAbsDiff, poleModifiedERealAbsDiff,
      canonicalERealDiffToReal, poleModifiedERealDiffToReal,
      EReal.abs_def, ← EReal.coe_sub]

/-- Potentials of the same singularity type have precisely the same pole at
every point of the comparison set. -/
theorem sameSingularityTypeOn_eq_bot_iff {X : Type*} {u v : X → EReal}
    {U : Set X} (h : SameSingularityTypeOn u v U) {x : X} (hx : x ∈ U) :
    u x = ⊥ ↔ v x = ⊥ := by
  constructor
  · exact h.2.eq_bot_of_eq_bot hx
  · exact h.1.eq_bot_of_eq_bot hx

/-- Global equality of singularity type gives equality of pole loci. -/
theorem sameSingularityTypeOn_univ_poleSet_eq {X : Type*}
    {u v : X → EReal} (h : SameSingularityTypeOn u v Set.univ) :
    {x | u x = ⊥} = {x | v x = ⊥} := by
  ext x
  exact sameSingularityTypeOn_eq_bot_iff h (Set.mem_univ x)

/-- The two comparison constants for a common singularity type bound the
canonical signed difference at every non-`top`, non-pole point.  Only one
non-pole hypothesis is required because the preceding theorem supplies the
other one. -/
theorem sameSingularityTypeOn_canonicalDiff_bounded {X : Type*}
    {u v : X → EReal} {U : Set X}
    (h : SameSingularityTypeOn u v U) :
    ∃ C D : ℝ, ∀ x ∈ U,
      u x ≠ ⊤ → v x ≠ ⊤ → u x ≠ ⊥ →
        -D ≤ canonicalERealDiffToReal (u x) (v x) ∧
          canonicalERealDiffToReal (u x) (v x) ≤ C := by
  obtain ⟨C, hC⟩ := h.1
  obtain ⟨D, hD⟩ := h.2
  refine ⟨C, D, fun x hx hu_top hv_top hu_bot => ?_⟩
  have hv_bot : v x ≠ ⊥ := by
    intro hv
    exact hu_bot ((sameSingularityTypeOn_eq_bot_iff h hx).2 hv)
  have hu_coe : (((u x).toReal : ℝ) : EReal) = u x :=
    EReal.coe_toReal hu_top hu_bot
  have hv_coe : (((v x).toReal : ℝ) : EReal) = v x :=
    EReal.coe_toReal hv_top hv_bot
  have hC' := hC x hx
  have hD' := hD x hx
  rw [← hu_coe, ← hv_coe, ← EReal.coe_add] at hC' hD'
  have hC_real : (u x).toReal ≤ (v x).toReal + C :=
    EReal.coe_le_coe_iff.mp hC'
  have hD_real : (v x).toReal ≤ (u x).toReal + D :=
    EReal.coe_le_coe_iff.mp hD'
  rw [canonicalERealDiffToReal, poleModifiedERealDiffToReal,
    ite_eq_right (not_and_of_not_left _ hu_bot),
    EReal.toReal_sub hu_top hu_bot hv_top hv_bot]
  constructor <;> linarith

end

end SGPT.Foundations.Analysis.FirstPass
