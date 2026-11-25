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

Perron–Bremermann competitors are compared using the full polydisk boundary
`closedUnitPolydisk n \ unitPolydisk n`. Monotonicity of the competitor class
gives monotonicity of the envelope. Constant shifts then give the sup-norm
estimate and uniform stability with respect to the boundary data.

Błocki uses decreasing `C^{1,1}` data on the full boundary in the
[proof of Theorem 2.3.1](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=52).
The Lean comparison applies to continuous data, including the smooth data
that occur in such an approximation. It gives uniform envelope convergence
when the boundary data converge uniformly.
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
