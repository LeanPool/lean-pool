/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module

public import LeanPool.VenNullClockRoundRates.RoundAreaBridge
public import LeanPool.VenNullClockRoundRates.Lower
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# Admissible round-area profile classes and their observation gap
-/

@[expose] public section
noncomputable section

open MeasureTheory Set VenMask VenRate
open scoped ContDiff

namespace VenRateUpper

/-- The absolute discrepancy of the layer at downstream control `s`. -/
def layerDiscrepancy (μ : Measure UnitSphere) (w₀ w₁ : UnitSphere → ℝ)
    (θ s x : ℝ) : ℝ :=
  |layer μ w₁ (secondEnergy θ) s x - layer μ w₀ firstEnergy s x|

/-- Supremum absolute layer discrepancy over the closed read interval. -/
def layerSup (μ : Measure UnitSphere) (w₀ w₁ : UnitSphere → ℝ)
    (θ s a : ℝ) : ℝ :=
  sSup (layerDiscrepancy μ w₀ w₁ θ s '' Icc 0 a)

/-- The two-layer distance of Eq. (4), the maximum of the absolute suprema
of the separate unnormalized layer discrepancies on the full read interval. -/
def dataDistance (μ : Measure UnitSphere) (w₀ w₁ : UnitSphere → ℝ) (θ b a : ℝ) : ℝ :=
  max (layerSup μ w₀ w₁ θ 0 a) (layerSup μ w₀ w₁ θ b a)

private theorem abs_layer_le {μ : Measure UnitSphere} {w G : UnitSphere → ℝ}
    {s x a : ℝ} (hw : Integrable w μ) (hc : Continuous G) (hG : ∀ y, G y ≤ 1)
    (hs : 0 ≤ s) (hx : x ∈ Icc 0 a) :
    |layer μ w G s x| ≤ (∫ y, |w y| ∂μ) * Real.exp (a + s) := by
  have hi := weighted_integrable (int_tilt hw hs hc hG) x
  unfold layer
  calc
    _ ≤ ∫ y, |tilt w G s y * Real.exp (x * firstEnergy y)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y, |w y| * Real.exp (a + s) ∂μ := by
      apply integral_mono hi.abs (hw.abs.mul_const _)
      intro y
      have hSG : s * G y ≤ s := by
        simpa using mul_le_mul_of_nonneg_left (hG y) hs
      have hXF : x * firstEnergy y ≤ a := by
        exact (show x * firstEnergy y ≤ x by
          simpa using mul_le_mul_of_nonneg_left (en_bounds 0 y).1.2 hx.1).trans hx.2
      change |tilt w G s y * Real.exp (x * firstEnergy y)| ≤ |w y| * Real.exp (a + s)
      simp only [tilt, abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [mul_assoc, ← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg _)
    _ = _ := integral_mul_const _ _

private theorem layerDiscrepancy_bddAbove {μ : Measure UnitSphere}
    {w₀ w₁ : UnitSphere → ℝ} {θ s a : ℝ}
    (hw₀ : Integrable w₀ μ) (hw₁ : Integrable w₁ μ) (hs : 0 ≤ s) :
    BddAbove (layerDiscrepancy μ w₀ w₁ θ s '' Icc 0 a) := by
  refine ⟨(∫ y, |w₁ y| ∂μ) * Real.exp (a + s) +
    (∫ y, |w₀ y| ∂μ) * Real.exp (a + s), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  unfold layerDiscrepancy
  exact (abs_sub _ _).trans (add_le_add
    (abs_layer_le hw₁ (second_cont θ) (fun y => (en_bounds θ y).2.2) hs hx)
    (abs_layer_le hw₀ first_cont (fun y => (en_bounds θ y).1.2) hs hx))

/-- An envelope holds exactly when it bounds the actual two-layer distance. -/
theorem dataDistance_le_iff_dataClose {μ : Measure UnitSphere}
    {w₀ w₁ : UnitSphere → ℝ} {θ b a ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw₀ : Integrable w₀ μ) (hw₁ : Integrable w₁ μ) :
    dataDistance μ w₀ w₁ θ b a ≤ ε ↔ DataClose μ w₀ w₁ θ b a ε := by
  have hControl : (Icc (0 : ℝ) a).Nonempty := ⟨0, le_rfl, ha⟩
  unfold dataDistance layerSup
  constructor
  · intro h x hx
    refine ⟨?_, ?_⟩
    · exact (le_csSup (layerDiscrepancy_bddAbove hw₀ hw₁ (θ := θ) (a := a) le_rfl)
        ⟨x, hx, rfl⟩).trans ((le_max_left _ _).trans h)
    · exact (le_csSup (layerDiscrepancy_bddAbove hw₀ hw₁ (θ := θ) (a := a) hb)
        ⟨x, hx, rfl⟩).trans ((le_max_right _ _).trans h)
  · intro h
    apply max_le
    · refine csSup_le (hControl.image _) ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (h x hx).1
    · refine csSup_le (hControl.image _) ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (h x hx).2

private theorem dataDistance_nonneg {μ : Measure UnitSphere}
    {w₀ w₁ : UnitSphere → ℝ} {θ b a : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw₀ : Integrable w₀ μ) (hw₁ : Integrable w₁ μ) :
    0 ≤ dataDistance μ w₀ w₁ θ b a := by
  have hc := (dataDistance_le_iff_dataClose ha hb hw₀ hw₁ (θ := θ)).1 le_rfl
  exact (abs_nonneg _).trans (hc 0 ⟨le_rfl, ha⟩).1

/-- The three profile conditions in Eq. (2) under normalized round area. -/
def RoundAdmissible (M : ℝ) (w : UnitSphere → ℝ) : Prop :=
  Integrable w roundArea ∧ (∀ᵐ y ∂roundArea, 1 ≤ w y) ∧ (∫ y, w y ∂roundArea) ≤ M

/-- A smooth sphere profile represented by the restriction of a smooth
function on the ambient Cartesian space. -/
def AmbientSmooth (w : UnitSphere → ℝ) : Prop :=
  ∃ W : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ W ∧ ∀ y, w y = W y.val

private theorem ambientSmooth_one : AmbientSmooth (fun _ => 1) :=
  ⟨fun _ => 1, contDiff_const, fun _ => rfl⟩

/-- All data distances achievable by the stated round-area nuisance class. -/
def roundClassDistances (a b d M : ℝ) (Q : (UnitSphere → ℝ) → Prop) : Set ℝ :=
  {r | ∃ (θ : ℝ) (w₀ w₁ : UnitSphere → ℝ), d ≤ 1 - Real.cos θ ^ 2 ∧
    RoundAdmissible M w₀ ∧ RoundAdmissible M w₁ ∧ Q w₀ ∧ Q w₁ ∧
    r = dataDistance roundArea w₀ w₁ θ b a}

/-- The Eq. (33) infimum over separate nuisance profiles, with a common bound
on the two individual integrals, and all admissible alternative angles.
`Q := fun _ => True` gives the broad class. `Q := AmbientSmooth` gives the
smooth subclass in the ambient restriction representation. -/
def roundClassGap (a b d M : ℝ) (Q : (UnitSphere → ℝ) → Prop) : ℝ :=
  sInf (roundClassDistances a b d M Q)

private theorem roundClassDistances_bddBelow {a b d M : ℝ} {Q : (UnitSphere → ℝ) → Prop}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : BddBelow (roundClassDistances a b d M Q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨θ, w₀, w₁, _, hw₀, hw₁, _, _, rfl⟩
  exact dataDistance_nonneg ha hb hw₀.1 hw₁.1

private theorem roundAdmissible_one {M : ℝ} (hM : 1 ≤ M) :
    RoundAdmissible M (fun _ => 1) := by
  refine ⟨integrable_const _, ae_of_all _ fun _ => le_rfl, ?_⟩
  simpa using hM

private theorem roundClassDistances_nonempty {a b d M : ℝ} {Q : (UnitSphere → ℝ) → Prop}
    (hM : 1 ≤ M) (hd : d ≤ 1) (hQ : Q (fun _ => 1)) :
    (roundClassDistances a b d M Q).Nonempty := by
  have hSep : d ≤ 1 - Real.cos (Real.pi / 2) ^ 2 := by
    simpa [Real.cos_pi_div_two] using hd
  exact ⟨_, Real.pi / 2, (fun _ => 1), (fun _ => 1), hSep,
    roundAdmissible_one hM, roundAdmissible_one hM, hQ, hQ, rfl⟩

/-- The broad lower bound and ambient-smooth upper bound also apply to each
intermediate subclass, including an intrinsic smooth class that admits every
ambient smooth restriction. -/
theorem round_class_gap_between_broad_and_ambient {a b d M : ℝ}
    {Q : (UnitSphere → ℝ) → Prop} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : d ≤ 1) (hM : 1 ≤ M) (hQ : ∀ w, AmbientSmooth w → Q w) :
    roundClassGap a b d M (fun _ => True) ≤ roundClassGap a b d M Q ∧
      roundClassGap a b d M Q ≤ roundClassGap a b d M AmbientSmooth := by
  unfold roundClassGap
  constructor
  · refine csInf_le_csInf (roundClassDistances_bddBelow ha hb)
      (roundClassDistances_nonempty hM hd (hQ _ ambientSmooth_one)) ?_
    rintro _ ⟨θ, w₀, w₁, hSep, hw₀, hw₁, _, _, rfl⟩
    exact ⟨θ, w₀, w₁, hSep, hw₀, hw₁, trivial, trivial, rfl⟩
  · refine csInf_le_csInf (roundClassDistances_bddBelow ha hb)
      (roundClassDistances_nonempty hM hd ambientSmooth_one) ?_
    rintro _ ⟨θ, w₀, w₁, hSep, hw₀, hw₁, h₀, h₁, rfl⟩
    exact ⟨θ, w₀, w₁, hSep, hw₀, hw₁, hQ w₀ h₀, hQ w₁ h₁, rfl⟩

/-- The accepted lower masking rate bounds the actual class infimum uniformly.
The extra class predicate may retain only smooth profiles. The constant one
belongs to both printed classes and witnesses nonemptiness at large budgets. -/
theorem eventual_round_class_gap_lower {a b d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    ∃ C M₀ : ℝ, 0 < C ∧ 1 < M₀ ∧ ∀ M ≥ M₀,
      ∀ Q : (UnitSphere → ℝ) → Prop, Q (fun _ => 1) →
        Real.exp (-C * Real.log M * Real.log (Real.log M)) ≤ roundClassGap a b d M Q := by
  obtain ⟨C, M₀, hC, hM₀, hLower⟩ := lower_masking_rate roundArea hd hd1 ha hb
  refine ⟨C, M₀, hC, hM₀, ?_⟩
  intro M hM Q hQ
  unfold roundClassGap
  apply le_csInf (roundClassDistances_nonempty (hM₀.le.trans hM) hd1 hQ)
  rintro _ ⟨θ, w₀, w₁, hSep, hw₀, hw₁, _, _, rfl⟩
  exact hLower hM hSep hw₀.1 hw₁.1 hw₀.2.1 hw₁.2.1 hw₀.2.2 hw₁.2.2
    ((dataDistance_le_iff_dataClose ha.le hb.le hw₀.1 hw₁.1).1 le_rfl)

/-- One admissible common profile gives an upper bound for any of the printed
class infima whose defining class predicate accepts that profile. -/
theorem round_class_gap_le_of_common_witness {a b d M θ ε : ℝ}
    {Q : (UnitSphere → ℝ) → Prop} {w : UnitSphere → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSep : d ≤ 1 - Real.cos θ ^ 2) (hw : RoundAdmissible M w) (hQ : Q w)
    (hClose : DataClose roundArea w w θ b a ε) : roundClassGap a b d M Q ≤ ε := by
  have hMem : dataDistance roundArea w w θ b a ∈ roundClassDistances a b d M Q :=
    ⟨θ, w, w, hSep, hw, hw, hQ, hQ, rfl⟩
  exact (csInf_le (roundClassDistances_bddBelow ha hb) hMem).trans
    ((dataDistance_le_iff_dataClose ha hb hw.1 hw.1).2 hClose)

private theorem roundAdmissible_of_ambient {M : ℝ} {W : ℝ × ℝ × ℝ → ℝ}
    (hW : ContDiff ℝ ∞ W) (hRange : ∀ y : UnitSphere, 2 ≤ W y.val ∧ W y.val ≤ M) :
    RoundAdmissible M (fun y => W y.val) := by
  have hc : Continuous (fun y : UnitSphere => W y.val) :=
    hW.continuous.comp continuous_subtype_val
  have hi : Integrable (fun y : UnitSphere => W y.val) roundArea := by
    apply Integrable.of_bound hc.aestronglyMeasurable M
    exact ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hRange y).1])]
      exact (hRange y).2
  refine ⟨hi, ae_of_all _ (fun y => by linarith [(hRange y).1]), ?_⟩
  calc
    _ ≤ ∫ _ : UnitSphere, M ∂roundArea :=
      integral_mono hi (integrable_const _) (fun y => (hRange y).2)
    _ = M := by simp

/-- Eq. (34) follows for both classes from the accepted lower theorem and a
smooth common-profile upper witness at any one fixed admissible angle. This
join takes the full witness family of Proposition 5 as its premise. -/
theorem matching_round_class_rates_of_smooth_witness {a b d θ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hd1 : d ≤ 1)
    (hSep : d ≤ 1 - Real.cos θ ^ 2)
    (hUpper : ∃ c M₁ : ℝ, 0 < c ∧ 1 < M₁ ∧ ∀ M ≥ M₁,
      ∃ W : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ W ∧
        (∀ y : UnitSphere, 2 ≤ W y.val ∧ W y.val ≤ M) ∧
        DataClose roundArea (fun y => W y.val) (fun y => W y.val) θ b a
          (Real.exp (-c * Real.log M * Real.log (Real.log M)))) :
    ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 1 < M₀ ∧ ∀ M ≥ M₀,
      let lower := Real.exp (-C * Real.log M * Real.log (Real.log M))
      let upper := Real.exp (-c * Real.log M * Real.log (Real.log M))
      lower ≤ roundClassGap a b d M (fun _ => True) ∧
      roundClassGap a b d M (fun _ => True) ≤ upper ∧
      lower ≤ roundClassGap a b d M AmbientSmooth ∧
      roundClassGap a b d M AmbientSmooth ≤ upper := by
  obtain ⟨C, L, hC, hL, hLower⟩ := eventual_round_class_gap_lower hd hd1 ha hb
  obtain ⟨c, U, hc, _, hUpper⟩ := hUpper
  refine ⟨C, c, max L U, hC, hc, hL.trans_le (le_max_left _ _), ?_⟩
  intro M hM
  have hML : L ≤ M := (le_max_left _ _).trans hM
  have hMU : U ≤ M := (le_max_right _ _).trans hM
  obtain ⟨W, hW, hRange, hClose⟩ := hUpper M hMU
  have hw := roundAdmissible_of_ambient hW hRange
  have hs : AmbientSmooth (fun y => W y.val) := ⟨W, hW, fun _ => rfl⟩
  exact ⟨hLower M hML (fun _ => True) trivial,
    round_class_gap_le_of_common_witness ha.le hb.le hSep hw trivial hClose,
    hLower M hML AmbientSmooth ambientSmooth_one,
    round_class_gap_le_of_common_witness ha.le hb.le hSep hw hs hClose⟩

end VenRateUpper
end
