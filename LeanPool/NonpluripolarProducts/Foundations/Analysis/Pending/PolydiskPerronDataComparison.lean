/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PolydiskPerronEnvelope

/-!
# The Perron--Bremermann envelope as a function of its boundary data

`Pending.PolydiskPerronSemiconcave` discharges Blocki's `C^{1,1}` estimate on
the `C²` stratum, and its module docstring names the two ingredients that the
passage from `C²` data to the bounded upper semicontinuous data of Xia's Lemma
2.4.3 still costs:

1. monotonicity of `perronEnvelope` in the data, and the identification of the
   decreasing limit of the envelopes;
2. stability of `Pending.BedfordTaylor.IsBTLimit` along a decreasing sequence
   of locally bounded plurisubharmonic functions.

**This module proves the monotonicity half of ingredient 1, and the sup-norm
stability it yields:**

* `IsPerronCompetitor.mono_boundary` -- the competitor class only sees the
  boundary values, and grows with them;
* `IsPerronData.perronEnvelope_mono` -- hence the envelope is monotone in the
  data;
* `IsPerronData.perronEnvelope_add_const` -- the envelope commutes with a
  constant shift of the data;
* `IsPerronData.abs_perronEnvelope_sub_le` -- therefore the envelope is
  `1`-Lipschitz for the sup norm on the boundary, and
  `forall_abs_perronEnvelope_sub_le_of_uniform` -- uniformly convergent data
  have uniformly convergent envelopes.

**What is not proved here, and must not be read into the above.**  The other
half of ingredient 1 is the *identification of the decreasing limit* of the
envelopes; it is not in this module, for the reason spelled out next.  Dini's
theorem
(`Pending.ThetaCapacityDecreasingConvergence.exists_forall_lt_add_of_antitone_of_continuousOn`)
does make a decreasing sequence of data converge uniformly on the compact
`PBar`, and then the last theorem below makes the envelopes converge uniformly
-- but Dini needs the *limit* to be continuous too, and the limit of a
decreasing sequence of continuous functions is in general only upper
semicontinuous.  A merely usc limit cannot even be stated here: `IsPerronData`
requires `ContinuousOn v`, so the competitor class for usc data, which is what
Blocki's mollification argument identifies the limit envelope against, is not
expressible in this file.  What the statements below do cover is a decreasing
sequence of data whose pointwise limit is again continuous.

Ingredient 2 -- the Bedford--Taylor convergence theorem for a decreasing
sequence of locally bounded plurisubharmonic functions -- is no longer
untouched: it is proved in `Pending.BedfordTaylorDecreasingLimit`
(`tendsto_integral_of_antitone_isBTLimit`, `eq_zero_of_antitone_of_isBTLimit`),
and `Pending.PolydiskBalayageDecreasingData` performs the passage to decreasing
data on the measure side.  The identification of the limit envelope with the
envelope of the limiting data — the statement about `perronEnvelope` that this
module could not express — is
`Pending.PolydiskPerronDecreasingLimit.perronEnvelope_iInf_eq_of_antitone`: it
works with the competitor class of the usc datum directly, so no `IsPerronData`
hypothesis on the limit is needed.  Both ingredients of Błocki's passage are
therefore in place, and what remains between here and Xia's Lemma 2.4.3 is the
*existence* of the approximation — that a bounded usc datum on the distinguished
boundary is the decreasing limit of `C²` Perron data.

One general fact is proved on the way and stated in the root namespace, since
it is missing from `SGPT.Foundations.Analysis.Plurisubharmonic`: a
plurisubharmonic function stays plurisubharmonic after adding a real constant.
The `On`-form of "a constant is plurisubharmonic" is recorded next to it, but
it is only a wrapper: the content is
`SGPT.Foundations.Analysis.plurisubharmonicAt_const`.

Source: Z. Blocki, *The complex Monge--Ampere operator in pluripotential
theory*, lecture notes, Section 2.3; Bedford--Taylor, Invent. Math. 37 (1976).
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

/-! ## Constants are plurisubharmonic -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `On`-form of `plurisubharmonicAt_const`: a real constant is
plurisubharmonic on any set. -/
theorem plurisubharmonicOn_const (c : ℝ) (U : Set E) :
    PlurisubharmonicOn (fun _ : E => (c : EReal)) U :=
  fun x _ => plurisubharmonicAt_const (c : EReal) (EReal.coe_ne_top c) x

/-- Adding a real constant preserves plurisubharmonicity. -/
theorem PlurisubharmonicOn.add_const {u : E → EReal} {U : Set E}
    (hu : PlurisubharmonicOn u U) (c : ℝ) :
    PlurisubharmonicOn (fun y => u y + (c : EReal)) U :=
  hu.add (plurisubharmonicOn_const c U)

end SGPT.Foundations.Analysis

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass

variable {n : ℕ}

/-! ## The competitor class only sees the boundary values -/

/-- A competitor for smaller boundary data is a competitor for larger boundary
data.  Only the values on `PBar \ P` are used. -/
theorem IsPerronCompetitor.mono_boundary {v v' w : ComplexModel n → ℝ}
    (hw : IsPerronCompetitor v w)
    (hle : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, v ζ ≤ v' ζ) :
    IsPerronCompetitor v' w := by
  refine ⟨hw.1, fun ζ hζ ε hε => ?_⟩
  filter_upwards [hw.2 ζ hζ ε hε] with z hz
  have := hle ζ hζ
  linarith

/-- Shifting a competitor and its data by the same real constant. -/
theorem IsPerronCompetitor.add_const {v w : ComplexModel n → ℝ}
    (hw : IsPerronCompetitor v w) (c : ℝ) :
    IsPerronCompetitor (fun x => v x + c) (fun x => w x + c) := by
  refine ⟨?_, fun ζ hζ ε hε => ?_⟩
  · have hpsh := hw.1.add_const c
    have hfun : (fun z : ComplexModel n => ((w z + c : ℝ) : EReal)) =
        fun z : ComplexModel n => (w z : EReal) + (c : EReal) := by
      funext z
      exact EReal.coe_add _ _
    rw [hfun]
    exact hpsh
  · filter_upwards [hw.2 ζ hζ ε hε] with z hz
    linarith

/-- Shifting admissible data by a real constant. -/
theorem IsPerronData.add_const {v : ComplexModel n → ℝ} (hv : IsPerronData v)
    (c : ℝ) : IsPerronData (fun x => v x + c) := by
  refine ⟨hv.pos, hv.continuousOn.add continuousOn_const, ?_⟩
  have hpsh := hv.psh.add_const c
  have hfun : (fun z : ComplexModel n => ((v z + c : ℝ) : EReal)) =
      fun z : ComplexModel n => (v z : EReal) + (c : EReal) := by
    funext z
    exact EReal.coe_add _ _
  rw [hfun]
  exact hpsh

/-! ## Monotonicity, shift and the sup-norm estimate -/

/-- **The envelope is monotone in its boundary data.** -/
theorem IsPerronData.perronEnvelope_mono {v v' : ComplexModel n → ℝ}
    (hv : IsPerronData v) (hv' : IsPerronData v')
    (hle : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, v ζ ≤ v' ζ)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    perronEnvelope v z ≤ perronEnvelope v' z := by
  have : Nonempty {w : ComplexModel n → ℝ // IsPerronCompetitor v w} :=
    ⟨⟨v, hv.isPerronCompetitor_self⟩⟩
  exact ciSup_le fun w => hv'.le_perronEnvelope (w.2.mono_boundary hle) hz

/-- **The envelope commutes with a constant shift of the data.** -/
theorem IsPerronData.perronEnvelope_add_const {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) (c : ℝ) {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    perronEnvelope (fun x => v x + c) z = perronEnvelope v z + c := by
  have hvc : IsPerronData (fun x => v x + c) := hv.add_const c
  refine le_antisymm ?_ ?_
  · have : Nonempty {w : ComplexModel n → ℝ //
        IsPerronCompetitor (fun x => v x + c) w} :=
      ⟨⟨fun x => v x + c, hvc.isPerronCompetitor_self⟩⟩
    refine ciSup_le fun w => ?_
    have hshift := w.2.add_const (-c)
    have hcomp : IsPerronCompetitor v (fun x => w.1 x + -c) :=
      hshift.mono_boundary (fun ζ _ => le_of_eq (by ring))
    have := hv.le_perronEnvelope hcomp hz
    linarith
  · have : Nonempty {w : ComplexModel n → ℝ // IsPerronCompetitor v w} :=
      ⟨⟨v, hv.isPerronCompetitor_self⟩⟩
    have hbound : ∀ w : {w : ComplexModel n → ℝ // IsPerronCompetitor v w},
        w.1 z ≤ perronEnvelope (fun x => v x + c) z - c := by
      intro w
      have := hvc.le_perronEnvelope (w.2.add_const c) hz
      linarith
    have hsup : perronEnvelope v z ≤ perronEnvelope (fun x => v x + c) z - c :=
      ciSup_le hbound
    linarith

/-- **The envelope is `1`-Lipschitz for the sup norm of the data on the
boundary.** -/
theorem IsPerronData.perronEnvelope_le_add_of_le_add {v v' : ComplexModel n → ℝ}
    (hv : IsPerronData v) (hv' : IsPerronData v') {c : ℝ}
    (hle : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, v ζ ≤ v' ζ + c)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    perronEnvelope v z ≤ perronEnvelope v' z + c := by
  have h1 : perronEnvelope v z ≤ perronEnvelope (fun x => v' x + c) z :=
    hv.perronEnvelope_mono (hv'.add_const c) hle hz
  rwa [hv'.perronEnvelope_add_const c hz] at h1

/-- The two-sided form. -/
theorem IsPerronData.abs_perronEnvelope_sub_le {v v' : ComplexModel n → ℝ}
    (hv : IsPerronData v) (hv' : IsPerronData v') {c : ℝ}
    (hle : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, |v ζ - v' ζ| ≤ c)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    |perronEnvelope v z - perronEnvelope v' z| ≤ c := by
  have h1 : perronEnvelope v z ≤ perronEnvelope v' z + c :=
    hv.perronEnvelope_le_add_of_le_add hv' (fun ζ hζ => by
      have := (abs_le.mp (hle ζ hζ)).2; linarith) hz
  have h2 : perronEnvelope v' z ≤ perronEnvelope v z + c :=
    hv'.perronEnvelope_le_add_of_le_add hv (fun ζ hζ => by
      have := (abs_le.mp (hle ζ hζ)).1; linarith) hz
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Uniformly convergent data have uniformly convergent envelopes.**
Together with Dini's theorem this covers every decreasing sequence of data
continuous on the compact `PBar`. -/
theorem forall_abs_perronEnvelope_sub_le_of_uniform
    {v : ℕ → ComplexModel n → ℝ} {vlim : ComplexModel n → ℝ}
    (hv : ∀ j, IsPerronData (v j)) (hvlim : IsPerronData vlim)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, |v j ζ - vlim ζ| ≤ eps)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ z ∈ unitPolydisk n,
      |perronEnvelope (v j) z - perronEnvelope vlim z| ≤ eps := by
  obtain ⟨N, hN⟩ := hunif eps heps
  exact ⟨N, fun j hj z hz => (hv j).abs_perronEnvelope_sub_le hvlim (hN j hj) hz⟩

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
