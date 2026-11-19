/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathContinuousLocalFlow.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathUniformLocalExistence
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathLocalStability

/-! A genuine continuous local solution map on bounded continuous-noise path space. -/

@[expose] public section
open MeasureTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Continuous paths `[-1, 1] → E` vanishing at `0` and bounded in norm by `M`. -/
abbrev drivenBoundedNoiseSpace (M : ℝ) :=
  {N : C(Icc (-1 : ℝ) 1, E) | N ⟨0, by norm_num⟩ = 0 ∧ ∀ s, ‖N s‖ ≤ M}

/-- Extends a bounded noise path on `[-1, 1]` to `ℝ` by precomposing with the projection
`Set.projIcc` onto `[-1, 1]`, so it is constant outside that interval. -/
def drivenBoundedNoiseExtension {M : ℝ} (N : drivenBoundedNoiseSpace E M) : ℝ → E :=
  fun t => N.val (Set.projIcc (-1 : ℝ) 1 (by norm_num) t)

variable {E}
omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem drivenBoundedNoiseExtension_continuous {M : ℝ} (N : drivenBoundedNoiseSpace E M) :
    Continuous (drivenBoundedNoiseExtension E N) := N.val.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem drivenBoundedNoiseExtension_zero {M : ℝ} (N : drivenBoundedNoiseSpace E M) :
    drivenBoundedNoiseExtension E N 0 = 0 := by
  unfold drivenBoundedNoiseExtension
  rw [Set.projIcc_of_mem (by norm_num) (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)]
  exact N.property.1

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem drivenBoundedNoiseExtension_norm_le {M : ℝ} (N : drivenBoundedNoiseSpace E M) (t : ℝ) :
    ‖drivenBoundedNoiseExtension E N t‖ ≤ M := N.property.2 _

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem drivenBoundedNoiseExtension_sub_norm_le {M : ℝ} (N Q : drivenBoundedNoiseSpace E M) (t : ℝ)
    :
    ‖drivenBoundedNoiseExtension E N t-drivenBoundedNoiseExtension E Q t‖ ≤ ‖N.val-Q.val‖ :=
  (N.val-Q.val).norm_coe_le_norm _

theorem drivenContinuousNoise_continuous_local_flow
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b) (z : E) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ε : ℝ, ∃ hε : ε > 0, ∃ Φ : drivenBoundedNoiseSpace E M → C(Icc 0 ε, E),
      LipschitzWith ⟨Real.exp ((K : ℝ)*ε), (Real.exp_pos _).le⟩ Φ ∧
      (∀ N, Φ N ⟨0, ⟨le_rfl, hε.le⟩⟩ = z) ∧
      ∀ N (t : Icc 0 ε), Φ N t = z+drivenBoundedNoiseExtension E N t+
        ∫ s in (0 : ℝ)..t, b (Φ N (Set.projIcc 0 ε hε.le s)) := by
  obtain ⟨ε, hε, hExist⟩ := drivenContinuousNoise_lipschitz_uniform_local b K hb z M hM
  have hAll (N : drivenBoundedNoiseSpace E M) : ∃ X : ℝ → E,
      ContinuousOn X (Icc 0 ε) ∧ X 0 = z ∧ ∀ t ∈ Icc 0 ε,
        X t = z+drivenBoundedNoiseExtension E N t+∫ s in (0 : ℝ)..t, b (X s) :=
    hExist _ (drivenBoundedNoiseExtension_continuous N) (drivenBoundedNoiseExtension_zero N)
      (fun t ht => drivenBoundedNoiseExtension_norm_le N t)
  choose X hX hX0 hXEq using hAll
  let Φ : drivenBoundedNoiseSpace E M → C(Icc 0 ε, E) := fun N =>
    { toFun := fun t => X N t
      continuous_toFun := (hX N).comp_continuous continuous_subtype_val (fun t => t.property) }
  refine ⟨ε, hε, Φ,?_,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro N Q
    rw [dist_eq_norm]
    apply (ContinuousMap.norm_le (Φ N-Φ Q) (mul_nonneg (Real.exp_pos _).le (dist_nonneg))).mpr
    intro t
    have h := drivenVolterra_lipschitz_stability_on b K hb z
      (drivenBoundedNoiseExtension E N) (drivenBoundedNoiseExtension E Q)
      (X N) (X Q) ε ‖N.val-Q.val‖ hε.le (norm_nonneg _) (hX N) (hX Q)
      (hXEq N) (hXEq Q) (fun s hs => drivenBoundedNoiseExtension_sub_norm_le N Q s) t t.property
    change ‖X N t-X Q t‖ ≤ _
    simpa [Subtype.dist_eq, dist_eq_norm, mul_comm] using h
  · intro N
    exact hX0 N
  · intro N t
    change X N t = _
    rw [hXEq N t t.property]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    dsimp only [Φ]
    rw [Set.projIcc_of_mem hε.le (show s ∈ Icc 0 ε from ⟨hs.1, hs.2.trans t.property.2⟩)]
    rfl

theorem drivenContinuousNoise_local_flow_causal
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b) (z : E)
    (M ε : ℝ) (hε : 0 ≤ ε)
    (Φ : drivenBoundedNoiseSpace E M → C(Icc 0 ε, E))
    (hEq : ∀ N (t : Icc 0 ε), Φ N t = z + drivenBoundedNoiseExtension E N t +
      ∫ s in (0 : ℝ)..t, b (Φ N (Set.projIcc 0 ε hε s)))
    (N Q : drivenBoundedNoiseSpace E M) (t : Icc 0 ε)
    (hPast : ∀ s ∈ Icc 0 (t : ℝ), drivenBoundedNoiseExtension E N s =
      drivenBoundedNoiseExtension E Q s) : Φ N t = Φ Q t := by
  let X : ℝ → E := fun s => Φ N (Set.projIcc 0 ε hε s)
  let Y : ℝ → E := fun s => Φ Q (Set.projIcc 0 ε hε s)
  have hX : Continuous X := (Φ N).continuous.comp continuous_projIcc
  have hY : Continuous Y := (Φ Q).continuous.comp continuous_projIcc
  have hEqX (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      X s = z+drivenBoundedNoiseExtension E N s+∫ u in (0 : ℝ)..s, b (X u) := by
    have hse : s ∈ Icc 0 ε := ⟨hs.1, hs.2.trans t.property.2⟩
    simpa only [X, Set.projIcc_of_mem hε hse] using hEq N ⟨s, hse⟩
  have hEqY (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      Y s = z+drivenBoundedNoiseExtension E Q s+∫ u in (0 : ℝ)..s, b (Y u) := by
    have hse : s ∈ Icc 0 ε := ⟨hs.1, hs.2.trans t.property.2⟩
    simpa only [Y, Set.projIcc_of_mem hε hse] using hEq Q ⟨s, hse⟩
  have h := drivenVolterra_lipschitz_stability_on b K hb z
    (drivenBoundedNoiseExtension E N) (drivenBoundedNoiseExtension E Q) X Y
    t 0 t.property.1 le_rfl hX.continuousOn hY.continuousOn hEqX hEqY
    (fun s hs => by rw [hPast s hs, sub_self, norm_zero]) t ⟨t.property.1, le_rfl⟩
  have hz : X t = Y t := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using h)
      (norm_nonneg _)))
  simpa only [X, Y, Set.projIcc_of_mem hε t.property] using hz

theorem drivenContinuousNoise_measurable_local_flow
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b) (z : E) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ε : ℝ, ∃ hε : ε > 0, ∃ Φ : drivenBoundedNoiseSpace E M → C(Icc 0 ε, E),
      @Measurable _ _ (borel (drivenBoundedNoiseSpace E M)) (borel C(Icc 0 ε, E)) Φ ∧
      (∀ N, Φ N ⟨0, ⟨le_rfl, hε.le⟩⟩ = z) ∧
      (∀ N (t : Icc 0 ε), Φ N t = z+drivenBoundedNoiseExtension E N t+
        ∫ s in (0 : ℝ)..t, b (Φ N (Set.projIcc 0 ε hε.le s))) ∧
      ∀ N Q (t : Icc 0 ε),
        (∀ s ∈ Icc 0 (t : ℝ), drivenBoundedNoiseExtension E N s =
          drivenBoundedNoiseExtension E Q s) → Φ N t = Φ Q t := by
  obtain ⟨ε, hε, Φ, hLip, hZero, hEq⟩ := drivenContinuousNoise_continuous_local_flow b K hb z M hM
  exact ⟨ε, hε, Φ, hLip.continuous.borel_measurable, hZero, hEq,
    fun N Q t hPast => drivenContinuousNoise_local_flow_causal b K hb z M ε hε.le Φ hEq N Q t hPast⟩

end
end GinibrePoincare
