/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltCanonicalMap.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianJointEvaluation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousNoisePath

/-!
# Ginibre Brownian integral tilt canonical map

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreFiniteNoise_extension_canonical_prefix`,
`ginibreFiniteNoise_canonical_evaluation_identDistrib`,
`ginibreFiniteNoise_canonical_whole_path_identDistrib`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance finiteNoiseMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance finiteNoiseBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance fullNoiseMeasurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance fullNoiseBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

/-- Continuous zero-initial extension of a literal finite driving path. -/
def ginibreFiniteNoiseExtension (n : ℕ) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) (T : ℝ), Configuration n)) : GinibreContinuousNoise n :=
  ⟨⟨fun s => f (projIcc (0 : ℝ) (T : ℝ) T.property s) - f ⟨0, ⟨le_rfl, T.property⟩⟩,
      (f.continuous.comp (continuous_projIcc :
        Continuous (projIcc (0 : ℝ) (T : ℝ) T.property))).sub continuous_const⟩,
    sub_eq_zero.mpr (congrArg f (projIcc_left _))⟩

theorem ginibreFiniteNoiseExtension_measurable (n : ℕ) (T : ℝ≥0) :
    @Measurable _ _ (borel C(Icc (0 : ℝ) (T : ℝ), Configuration n)) _ (ginibreFiniteNoiseExtension n
        T) := by
  let : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  let : MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
  let : BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
  have hclosed : IsClosed {f : C(ℝ, Configuration n) | f 0=0} :=
    isClosed_eq (continuous_eval_const 0) continuous_const
  have hec : Topology.IsClosedEmbedding (fun f : GinibreContinuousNoise n => f.val) :=
    hclosed.isClosedEmbedding_subtypeVal
  apply hec.measurableEmbedding.measurable_comp_iff.mp
  apply ginibre_measurable_continuousMap_of_evaluations
  intro s
  exact (continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable

@[simp] theorem ginibreFiniteNoiseExtension_apply (n : ℕ) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) (T : ℝ), Configuration n)) (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
    (ginibreFiniteNoiseExtension n T f).val s=f ⟨s, hs⟩-f ⟨0, ⟨le_rfl, T.property⟩⟩ := by
  change f (projIcc (0 : ℝ) (T : ℝ) T.property s)-f ⟨0, ⟨le_rfl, T.property⟩⟩ = _
  have he : projIcc (0 : ℝ) (T : ℝ) T.property s=⟨s, hs⟩ := projIcc_of_mem T.property hs
  rw [he]

/-- Restricting and continuously extending an actual driver preserves its
canonical solution on every closed prefix on which that solution is alive. -/
theorem ginibreFiniteNoise_extension_canonical_prefix {n : ℕ} (α : ℝ)
    (z : Configuration n) (T S : ℝ≥0) (hST : S ≤ T)
    (f : C(Icc (0 : ℝ) (T : ℝ), Configuration n)) (N : ℝ → Configuration n)
    (hN0 : N 0 = 0) (hf : ∀ s (hs : s ∈ Icc 0 (T : ℝ)), f ⟨s, hs⟩ = N s)
    (hAlive : (S : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    ∀ t≤S, ginibreDrivenMaximalValue n α (ginibreFiniteNoiseExtension n T f).val z t=
      ginibreDrivenMaximalValue n α N z t := by
  let E := (ginibreFiniteNoiseExtension n T f).val
  have heq : EqOn E N (Icc 0 (T : ℝ)) := by
    intro s hs
    simp only [E, ginibreFiniteNoiseExtension_apply n T f s hs, hf s hs, hf 0 ⟨le_rfl, T.property⟩,
        hN0, sub_zero]
  have hSeg := ginibreDrivenMaximalPath_segment S hAlive
  have hSegE : GinibreDrivenSegment n α E z S (ginibreDrivenMaximalPath n α N z) := by
    refine ⟨hSeg.1, hSeg.2.1,?_⟩
    intro s hs
    refine ⟨(hSeg.2.2 s hs).1, (hSeg.2.2 s hs).2.1,?_⟩
    rw [heq ⟨hs.1, hs.2.trans (by exact_mod_cast hST)⟩]
    exact (hSeg.2.2 s hs).2.2
  have hAliveE := hSegE.horizon_lt_lifetime
    (ginibreFiniteNoiseExtension n T f).val.continuous (ginibreFiniteNoiseExtension n T f).property
  intro t ht
  have hh := ginibreDrivenMaximalValue_eq_segment hSegE t ht
    ((ENNReal.coe_le_coe.mpr ht).trans_lt hAliveE)
  simpa only [E, ginibreDrivenMaximalPath, Real.toNNReal_coe] using hh

/-- Genuine measurable canonical original evaluation as a functional of the
finite continuous driving path. This is a mapping lemma, not a stochastic law
assumption or a substitute for the original SDE. -/
theorem ginibreFiniteNoise_canonical_evaluation_measurable {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) (T t : ℝ≥0) :
    @Measurable _ _ (borel C(Icc (0 : ℝ) (T : ℝ), Configuration n)) _
      (fun f => ginibreDrivenMaximalValue n α (ginibreFiniteNoiseExtension n T f).val z t) := by
  have hm := (ginibreDrivenMaximalValue_joint_measurable hn α t).comp
    ((measurable_const (a := (⟨z, hz⟩ : {z : Configuration n // CollisionFree z}))).prodMk
        (ginibreFiniteNoiseExtension_measurable n T))
  exact hm

/-- Actual equality of continuous finite-noise laws passes to the genuine
canonical original SDE evaluations, including their defined killed values. -/
theorem ginibreFiniteNoise_canonical_evaluation_identDistrib {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) (T t : ℝ≥0)
    (P : Measure Ω) (Q : Measure Ω')
    (X : Ω → C(Icc (0 : ℝ) (T : ℝ), Configuration n))
    (Y : Ω' → C(Icc (0 : ℝ) (T : ℝ), Configuration n))
    (hX : @Measurable _ _ _ (borel C(Icc (0 : ℝ) (T : ℝ), Configuration n)) X)
    (hY : @Measurable _ _ _ (borel C(Icc (0 : ℝ) (T : ℝ), Configuration n)) Y)
    (hLaw : P.map X = Q.map Y) :
    IdentDistrib (fun ω => ginibreDrivenMaximalValue n α (ginibreFiniteNoiseExtension n T (X ω)).val
        z t)
      (fun ω => ginibreDrivenMaximalValue n α (ginibreFiniteNoiseExtension n T (Y ω)).val z t) P Q
          := by
  let : MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
  let : BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
  exact (show IdentDistrib X Y P Q from ⟨hX.aemeasurable, hY.aemeasurable, hLaw⟩).comp
    (ginibreFiniteNoise_canonical_evaluation_measurable hn α z hz T t)

/-- Every canonical evaluation at once is a measurable functional of the
finite continuous driver. Equal driver laws therefore identify the entire
raw canonical path, including the defined values beyond its maximal lifetime. -/
theorem ginibreFiniteNoise_canonical_whole_path_identDistrib {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) (T : ℝ≥0)
    (P : Measure Ω) (Q : Measure Ω')
    (X : Ω → C(Icc (0 : ℝ) (T : ℝ), Configuration n))
    (Y : Ω' → C(Icc (0 : ℝ) (T : ℝ), Configuration n))
    (hX : @Measurable _ _ _ (borel C(Icc (0 : ℝ) (T : ℝ), Configuration n)) X)
    (hY : @Measurable _ _ _ (borel C(Icc (0 : ℝ) (T : ℝ), Configuration n)) Y)
    (hLaw : P.map X = Q.map Y) :
    IdentDistrib
      (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (ginibreFiniteNoiseExtension n T
          (X ω)).val z t.val)
      (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (ginibreFiniteNoiseExtension n T
          (Y ω)).val z t.val) P Q := by
  let : MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
  let : BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
  have hm : Measurable (fun f (t : Icc (0 : ℝ≥0) T) =>
      ginibreDrivenMaximalValue n α (ginibreFiniteNoiseExtension n T f).val z t.val) := by
    apply Measurable.of_eval
    intro t
    exact ginibreFiniteNoise_canonical_evaluation_measurable hn α z hz T t.val
  exact (show IdentDistrib X Y P Q from ⟨hX.aemeasurable, hY.aemeasurable, hLaw⟩).comp hm

end
end GinibrePoincare
