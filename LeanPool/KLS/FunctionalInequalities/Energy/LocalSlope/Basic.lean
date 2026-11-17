/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Squared local metric slope and its finite-energy test class -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Energy.LocalSlope

section Metric

variable {X : Type*} [MetricSpace X]

/-- Pointwise local metric slope as the infimum of punctured-ball secant suprema.
The real quotient at `y = x` is zero, so including the center does not change the supremum.
At an isolated point the slope is zero. This is not the two-moving-point Lipschitz constant. -/
def apply (f : X → ℝ) (x : X) : ENNReal :=
  ⨅ (r : ℝ) (_ : 0 < r), ⨆ (y : X) (_ : dist y x < r),
    ENNReal.ofReal (dist (f y) (f x) / dist y x)

@[simp] theorem apply_const (c : ℝ) (x : X) :
    apply (fun _ : X ↦ c) x = 0 := by
  unfold apply
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le (1 : ℝ) (iInf_le_of_le zero_lt_one (by simp))

/-- The local-slope definition handles a one-point carrier without a nontriviality premise. -/
theorem apply_eq_zero_of_subsingleton [Subsingleton X] (f : X → ℝ) (x : X) :
    apply f x = 0 := by
  have hf : f = fun _ ↦ f x := funext fun y ↦ congrArg f (Subsingleton.elim y x)
  rw [hf, apply_const]

/-- The secant supremum over the punctured ball of radius `r`. -/
private def secantSup (f : X → ℝ) (x : X) (r : ℝ) : ENNReal :=
  ⨆ (y : X) (_ : dist y x < r), ENNReal.ofReal (dist (f y) (f x) / dist y x)

private theorem secantSup_mono (f : X → ℝ) (x : X) {r r' : ℝ} (h : r ≤ r') :
    secantSup f x r ≤ secantSup f x r' :=
  iSup₂_le fun y hy ↦ le_iSup₂ (f := fun y (_ : dist y x < r') ↦
    ENNReal.ofReal (dist (f y) (f x) / dist y x)) y (hy.trans_le h)

private theorem apply_eq_iInf_secantSup (f : X → ℝ) (x : X) :
    apply f x = ⨅ r : {r : ℝ // 0 < r}, secantSup f x r := by
  rw [apply, iInf_subtype']
  rfl

/-- Local slopes are subadditive under a local secant bound: if near `x` every secant of `g`
is bounded by the sum of the secants of `a` and `b`, then the slope of `g` at `x` is at most
the sum of their slopes. -/
theorem apply_le_add {g a b : X → ℝ} {x : X} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ y, dist y x < r₀ → dist (g y) (g x) ≤ dist (a y) (a x) + dist (b y) (b x)) :
    apply g x ≤ apply a x + apply b x := by
  have hsup (r : ℝ) (hr : r ≤ r₀) :
      secantSup g x r ≤ secantSup a x r + secantSup b x r := by
    refine iSup₂_le fun y hy ↦ ?_
    calc ENNReal.ofReal (dist (g y) (g x) / dist y x)
        ≤ ENNReal.ofReal ((dist (a y) (a x) + dist (b y) (b x)) / dist y x) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (h y (hy.trans_le hr))
            dist_nonneg)
      _ ≤ ENNReal.ofReal (dist (a y) (a x) / dist y x) +
            ENNReal.ofReal (dist (b y) (b x) / dist y x) := by
          rw [add_div]
          exact ENNReal.ofReal_add_le
      _ ≤ secantSup a x r + secantSup b x r :=
          add_le_add (le_iSup₂ (f := fun y (_ : dist y x < r) ↦
              ENNReal.ofReal (dist (a y) (a x) / dist y x)) y hy)
            (le_iSup₂ (f := fun y (_ : dist y x < r) ↦
              ENNReal.ofReal (dist (b y) (b x) / dist y x)) y hy)
  rw [apply_eq_iInf_secantSup a, apply_eq_iInf_secantSup b, ENNReal.iInf_add_iInf]
  · refine le_iInf fun r ↦ ?_
    have hmin : 0 < min (r : ℝ) r₀ := lt_min r.2 hr₀
    calc apply g x ≤ secantSup g x (min (r : ℝ) r₀) := by
          rw [apply_eq_iInf_secantSup]
          exact iInf_le (fun r : {r : ℝ // 0 < r} ↦ secantSup g x r) ⟨_, hmin⟩
      _ ≤ secantSup a x (min (r : ℝ) r₀) + secantSup b x (min (r : ℝ) r₀) :=
          hsup _ (min_le_right _ _)
      _ ≤ secantSup a x r + secantSup b x r :=
          add_le_add (secantSup_mono a x (min_le_left _ _))
            (secantSup_mono b x (min_le_left _ _))
  · intro i j
    refine ⟨⟨min (i : ℝ) j, lt_min i.2 j.2⟩, add_le_add ?_ ?_⟩
    · exact secantSup_mono a x (min_le_left _ _)
    · exact secantSup_mono b x (min_le_right _ _)

/-- A local secant bound by one function bounds the slope. -/
theorem apply_le_of_dist_le {g a : X → ℝ} {x : X} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ y, dist y x < r₀ → dist (g y) (g x) ≤ dist (a y) (a x)) :
    apply g x ≤ apply a x := by
  have := apply_le_add (b := fun _ ↦ (0 : ℝ)) hr₀ fun y hy ↦ by simpa using h y hy
  simpa using this

/-- The slope of a `K`-Lipschitz function is at most `K`. -/
theorem apply_le_of_lipschitzWith {f : X → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (x : X) : apply f x ≤ K := by
  refine iInf₂_le_of_le 1 zero_lt_one (iSup₂_le fun y _ ↦ ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases (dist_nonneg (x := y) (y := x)).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact K.2
  · rw [div_le_iff₀ hpos]
    exact hf.dist_le_mul y x

/-- A function that is constant near `x` has zero slope at `x`. -/
theorem apply_eq_zero_of_eqOn_ball {f : X → ℝ} {x : X} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ y, dist y x < r₀ → f y = f x) : apply f x = 0 := by
  have := apply_le_of_dist_le (g := f) (a := fun _ ↦ (0 : ℝ)) hr₀ fun y hy ↦ by
    rw [h y hy, dist_self, dist_self]
  exact le_antisymm (by simpa using this) bot_le

/-- Restriction along an isometric embedding does not increase the local slope: each secant of
`f ∘ e` near `y` is a secant of `f` near `e y` at the same distance. -/
theorem apply_comp_le_of_isometry {Y : Type*} [MetricSpace Y] {e : Y → X} (he : Isometry e)
    (f : X → ℝ) (y : Y) : apply (f ∘ e) y ≤ apply f (e y) := by
  unfold apply
  refine iInf₂_mono fun r _ => iSup₂_le fun z hz => ?_
  have hz' : dist (e z) (e y) < r := by rwa [he.dist_eq]
  have h := le_iSup₂ (f := fun (w : X) (_ : dist w (e y) < r) =>
    ENNReal.ofReal (dist (f w) (f (e y)) / dist w (e y))) (e z) hz'
  simpa only [Function.comp_apply, he.dist_eq] using h

/-- Composition with a nonexpansive map does not increase the local slope: a secant of `g ∘ r`
at `x` vanishes when `r` collapses the two points, and is otherwise at most the secant of `g` at
`r x` over the shorter distance `dist (r x') (r x) ≤ dist x' x`. -/
theorem apply_comp_le_of_lipschitzWith_one {Y : Type*} [MetricSpace Y] {r : X → Y}
    (hr : LipschitzWith 1 r) (g : Y → ℝ) (x : X) : apply (g ∘ r) x ≤ apply g (r x) := by
  unfold apply
  refine iInf₂_mono fun ρ _ => iSup₂_le fun x' hx' => ?_
  have hd : dist (r x') (r x) ≤ dist x' x := by simpa using hr.dist_le_mul x' x
  rcases (dist_nonneg (x := r x') (y := r x)).eq_or_lt with h0 | hpos
  · have hrr : r x' = r x := dist_eq_zero.1 h0.symm
    simp [Function.comp_apply, hrr]
  · refine le_trans ?_ (le_iSup₂ (f := fun (w : Y) (_ : dist w (r x) < ρ) =>
      ENNReal.ofReal (dist (g w) (g (r x)) / dist w (r x))) (r x') (hd.trans_lt hx'))
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Function.comp_apply]
    exact div_le_div_of_nonneg_left dist_nonneg hpos hd

end Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The squared local-slope integral for the displayed coordinate law `ν`, with no factor `1/2`.
It takes values in `ENNReal` and may be infinite. No change to intrinsic coordinates is made here.
-/
def energy (ν : ProbabilityMeasure E) (f : E → ℝ) : ENNReal :=
  ∫⁻ x, apply f x ^ 2 ∂(ν : Measure E)

/-- Locally Lipschitz tests with finite second moment and finite squared local-slope energy.
The domain is independent of the candidate Poincaré constant; smoothness and compact support are
not required. -/
structure Admissible (ν : ProbabilityMeasure E) (f : E → ℝ) : Prop where
  locallyLipschitz : LocallyLipschitz f
  memLp_two : MemLp f 2 (ν : Measure E)
  finite_energy : energy ν f ≠ ⊤


end FunctionalInequalities.Energy.LocalSlope
