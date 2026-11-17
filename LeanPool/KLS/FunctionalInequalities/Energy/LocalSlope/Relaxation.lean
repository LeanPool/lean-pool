/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.LocalSlope.Gradient
public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance

/-!
# The asymptotic Lipschitz constant and the `L²` relaxation of the local-slope energy

Read `AsymptoticLipschitz.apply`, `AsymptoticLipschitz.energy`, `AsymptoticLipschitz.Admissible`,
then `LocalSlope.preEnergy`, `LocalSlope.relaxation` and the two relaxation conventions.

The metric Cheeger energy can relax the squared *local slope*
`|∇f|(x) = limsup_{y → x} |f y − f x| / d(y, x)` (one moving point, `Energy.LocalSlope.apply`) or
the squared *asymptotic Lipschitz constant* `Lip_a f (x) = inf_{r > 0} Lip(f, B(x, r))` (two
moving points, `AsymptoticLipschitz.apply`).  This module builds both pre-energies on the
existing literature test domain `Energy.LocalSlope.Admissible` and their sequential `L²(ν)`
relaxations, and proves the unconditional comparison
`LocalSlope.relaxation ν ≤ AsymptoticLipschitz.relaxation ν`.

"Lower-semicontinuous relaxation" is the project's sequential relaxation, which in the metric
space `L²(ν)` is lower semicontinuous and is the largest lower-semicontinuous functional below
the raw energy on tests (`LocalSlope.lowerSemicontinuous_relaxation`,
`LocalSlope.le_relaxation_of_lowerSemicontinuous`).

The equality `LocalSlope.relaxation ν = AsymptoticLipschitz.relaxation ν` is proved downstream
for every Borel probability law on a finite-dimensional inner-product space in
`Energy/Cheeger/Identification.lean` (`LocalSlope.relaxation_eq_asymptoticLipschitz`). This
foundational module does not use that equality. The identification concerns relaxed energies,
not agreement on individual tests, a finiteness assertion, or a Poincaré inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy

universe u

/-! ### Asymptotic Lipschitz constant -/

namespace AsymptoticLipschitz

section Metric

variable {X : Type*} [MetricSpace X]

/-- Pointwise asymptotic Lipschitz constant `Lip_a f (x) = inf_{r > 0} Lip(f, B(x, r))`, the
infimum over radii of the two-moving-point secant supremum on the open ball.  The real quotient
at `y = z` is zero, so coincident pairs do not change the supremum.  This is not the one-moving-
point local slope `Energy.LocalSlope.apply`, which it dominates pointwise. -/
def apply (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (_ : 0 < r), ⨆ (y : X) (_ : dist y x < r) (z : X) (_ : dist z x < r),
    ENNReal.ofReal (dist (f y) (f z) / dist y z)

/-- Constants have zero asymptotic Lipschitz constant. -/
@[simp] theorem apply_const (c : ℝ) (x : X) :
    apply (fun _ : X ↦ c) x = 0 := by
  unfold apply
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le (1 : ℝ) (iInf_le_of_le zero_lt_one (by simp))

/-- On a one-point carrier every function is constant. -/
theorem apply_eq_zero_of_subsingleton [Subsingleton X] (f : X → ℝ) (x : X) :
    apply f x = 0 := by
  have hf : f = fun _ ↦ f x := funext fun y ↦ congrArg f (Subsingleton.elim y x)
  rw [hf, apply_const]

/-- A globally Lipschitz function has asymptotic Lipschitz constant at most its constant. -/
theorem apply_le_of_lipschitzWith {K : ℝ≥0} {f : X → ℝ} (hf : LipschitzWith K f) (x : X) :
    apply f x ≤ K := by
  unfold apply
  refine iInf_le_of_le 1 (iInf_le_of_le zero_lt_one ?_)
  refine iSup_le fun y ↦ iSup_le fun _ ↦ iSup_le fun z ↦ iSup_le fun _ ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rcases eq_or_ne (dist y z) 0 with h0 | h0
  · rw [h0, div_zero]
    exact K.coe_nonneg
  · exact (div_le_iff₀ (dist_nonneg.lt_of_ne (Ne.symm h0))).2 (hf.dist_le_mul y z)

end Metric

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The unnormalized squared asymptotic-Lipschitz integral in a coordinate space. -/
def energy (ν : ProbabilityMeasure V) (f : V → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, apply f x ^ 2 ∂(ν : Measure V)

/-- The asymptotic-Lipschitz test domain: locally Lipschitz `L²(ν)` functions of finite
asymptotic-Lipschitz energy.  It mirrors `Energy.LocalSlope.Admissible`. -/
structure Admissible (ν : ProbabilityMeasure V) (f : V → ℝ) : Prop where
  locallyLipschitz : LocallyLipschitz f
  memLp_two : MemLp f 2 (ν : Measure V)
  finite_energy : energy ν f ≠ ⊤

end AsymptoticLipschitz

namespace LocalSlope

section Metric

variable {X : Type*} [MetricSpace X]

/-- The one-moving-point local slope is dominated by the asymptotic Lipschitz constant. -/
theorem apply_le_asymptoticLipschitz (f : X → ℝ) (x : X) :
    apply f x ≤ AsymptoticLipschitz.apply f x := by
  unfold apply AsymptoticLipschitz.apply
  refine iInf_mono fun r ↦ iInf_mono fun hr ↦ iSup_mono fun y ↦ iSup_mono fun hy ↦ ?_
  exact le_iSup₂_of_le x (by simpa using hr) le_rfl

end Metric

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The squared local-slope energy is at most the squared asymptotic-Lipschitz energy. -/
theorem energy_le_asymptoticLipschitz (ν : ProbabilityMeasure V) (f : V → ℝ) :
    energy ν f ≤ AsymptoticLipschitz.energy ν f := by
  unfold energy AsymptoticLipschitz.energy
  refine lintegral_mono fun x ↦ ?_
  exact ENNReal.pow_le_pow_left (apply_le_asymptoticLipschitz f x)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Every asymptotic-Lipschitz test is a local-slope test. -/
theorem Admissible.of_asymptoticLipschitz {ν : ProbabilityMeasure V} {f : V → ℝ}
    (hf : AsymptoticLipschitz.Admissible ν f) : Admissible ν f :=
  { locallyLipschitz := hf.locallyLipschitz
    memLp_two := hf.memLp_two
    finite_energy := ne_top_of_le_ne_top hf.finite_energy (energy_le_asymptoticLipschitz ν f) }

/-! ### The local-slope pre-energy and its `L²` relaxation -/

/-- The finite squared local-slope pre-energy on the literature test domain, realized in real
`L²(ν)`.  The energy is finite on tests by `Admissible.finite_energy`, so `ENNReal.toNNReal`
loses nothing. -/
def preEnergy (ν : ProbabilityMeasure V) : PreEnergy (Lp ℝ 2 (ν : Measure V)) where
  Test := {f : V → ℝ // Admissible ν f}
  toAmbient f := f.2.memLp_two.toLp f.1
  energy f := (energy ν f.1).toNNReal

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The ambient realization of a local-slope test is its `L²(ν)` class. -/
@[simp]
theorem preEnergy_toAmbient (ν : ProbabilityMeasure V) (f : {f : V → ℝ // Admissible ν f}) :
    (preEnergy ν).toAmbient f = f.2.memLp_two.toLp f.1 :=
  rfl

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The pre-energy of a local-slope test is its squared local-slope integral. -/
theorem coe_preEnergy_energy (ν : ProbabilityMeasure V) (f : {f : V → ℝ // Admissible ν f}) :
    ((preEnergy ν).energy f : ℝ≥0∞) = energy ν f.1 :=
  ENNReal.coe_toNNReal f.2.finite_energy

/-- The sequential `L²(ν)` relaxation of the squared local-slope energy over locally Lipschitz
tests.  Twice the metric Cheeger energy in the Blueprint normalization; see `Cheeger.energy`. -/
def relaxation (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  (preEnergy ν).sequentialRelaxation

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Unfolding the local-slope relaxation exposes the generic sequential relaxation. -/
theorem relaxation_apply (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f = (preEnergy ν).sequentialRelaxation f :=
  rfl

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The relaxation is lower semicontinuous on `L²(ν)`: it is a lower-semicontinuous
relaxation in the sense of the Blueprint. -/
theorem lowerSemicontinuous_relaxation (ν : ProbabilityMeasure V) :
    LowerSemicontinuous (fun f : Lp ℝ 2 (ν : Measure V) ↦ relaxation ν f) :=
  (preEnergy ν).lowerSemicontinuous_sequentialRelaxation

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Relaxation does not increase the raw slope energy of an admissible test. -/
theorem relaxation_toLp_le (ν : ProbabilityMeasure V) {f : V → ℝ} (hf : Admissible ν f) :
    relaxation ν (hf.memLp_two.toLp f) ≤ energy ν f := by
  have h := (preEnergy ν).sequentialRelaxation_toAmbient_le
    (⟨f, hf⟩ : {f : V → ℝ // Admissible ν f})
  rwa [coe_preEnergy_energy] at h

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The relaxation is the largest lower-semicontinuous functional below the raw slope energy
on admissible tests: together with `lowerSemicontinuous_relaxation` and `relaxation_toLp_le`
this characterizes it as the lower-semicontinuous envelope. -/
theorem le_relaxation_of_lowerSemicontinuous (ν : ProbabilityMeasure V)
    (Q : Functional (Lp ℝ 2 (ν : Measure V)))
    (hlsc : LowerSemicontinuous (fun f ↦ Q f))
    (hQ : ∀ (f : V → ℝ) (hf : Admissible ν f), Q (hf.memLp_two.toLp f) ≤ energy ν f)
    (g : Lp ℝ 2 (ν : Measure V)) :
    Q g ≤ relaxation ν g := by
  apply (preEnergy ν).le_sequentialRelaxation_of_lowerSemicontinuous Q hlsc
  rintro ⟨f, hf⟩
  rw [coe_preEnergy_energy]
  exact hQ f hf

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Dimension zero: on a one-point coordinate space every relaxed slope energy vanishes. -/
theorem relaxation_eq_zero_of_subsingleton [Subsingleton V] (ν : ProbabilityMeasure V)
    (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f = 0 := by
  obtain ⟨c, hf⟩ := L2.exists_eq_const_of_subsingleton ν f
  have hconst : MemLp (fun _ : V ↦ c) 2 (ν : Measure V) := memLp_const c
  have henergy : energy ν (fun _ : V ↦ c) = 0 := by
    unfold energy
    simp
  have hadm : Admissible ν (fun _ : V ↦ c) :=
    ⟨(LipschitzWith.const c).locallyLipschitz, hconst, by
      rw [henergy]; exact ENNReal.zero_ne_top⟩
  have hle := relaxation_toLp_le ν hadm
  rw [henergy] at hle
  rw [hf]
  exact le_antisymm hle bot_le

end LocalSlope

namespace AsymptoticLipschitz

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The finite squared asymptotic-Lipschitz pre-energy, realized in real `L²(ν)`. -/
def preEnergy (ν : ProbabilityMeasure V) : PreEnergy (Lp ℝ 2 (ν : Measure V)) where
  Test := {f : V → ℝ // Admissible ν f}
  toAmbient f := f.2.memLp_two.toLp f.1
  energy f := (energy ν f.1).toNNReal

/-- The sequential `L²(ν)` relaxation of the squared asymptotic-Lipschitz energy.  This is the
alternative Cheeger convention; it is not the selected one. -/
def relaxation (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  (preEnergy ν).sequentialRelaxation

end AsymptoticLipschitz

namespace LocalSlope

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The easy comparison of the two Cheeger conventions: relaxing the smaller slope over the
larger test class gives the smaller relaxed energy. -/
theorem relaxation_le_asymptoticLipschitz (ν : ProbabilityMeasure V)
    (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f ≤ AsymptoticLipschitz.relaxation ν f := by
  have h := (AsymptoticLipschitz.preEnergy ν).sequentialRelaxation_comp_le
    (preEnergy ν) id continuous_id
    (fun f' ↦ ⟨⟨f'.1, Admissible.of_asymptoticLipschitz f'.2⟩, rfl,
      ENNReal.toNNReal_mono f'.2.finite_energy (energy_le_asymptoticLipschitz ν f'.1)⟩) f
  exact h


end LocalSlope

end FunctionalInequalities.Energy
