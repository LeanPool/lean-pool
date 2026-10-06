/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Form
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.AmnrDirectional
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The coarse-coefficient interface for the shared directional calculus. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4.IterateCalculus

/-! The mixed calculus below keeps spatial and material operations ordered. -/

/-- Scalar material operator. This calculus does not depend on a corrector tensor. -/
def amnrMaterial (b : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  _root_.AVenhance.Infra.Section4.amnrMaterial b f t x

/-- Space-time coordinate carrier used only to express the differential operators. -/
abbrev AmnrSpace :=
  _root_.AVenhance.Infra.Section4.AmnrSpace

/-- `none` is the material direction; `some i` is the i-th spatial direction. -/
def amnrDirection (b : AmnrSpace → Vec 2) (d : Option (Fin 2)) (z : AmnrSpace) : AmnrSpace :=
  _root_.AVenhance.Infra.Section4.amnrDirection b d z

/-- A directional differential operator on the actual space-time function. -/
def amnrOp (b : AmnrSpace → Vec 2) (d : Option (Fin 2))
    (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ :=
  _root_.AVenhance.Infra.Section4.amnrOp b d f z

/-- Ordered differential words, with the outermost operator at the head. -/
def amnrWord (b : AmnrSpace → Vec 2) : List (Option (Fin 2)) →
    (AmnrSpace → ℝ) → AmnrSpace → ℝ :=
  _root_.AVenhance.Infra.Section4.amnrWord b

theorem DirectionalCalculus.amnrDirection_contDiffOn {b : AmnrSpace → Vec 2} {U : Set AmnrSpace}
    {n : ℕ} (hb : ContDiffOn ℝ n b U) (d : Option (Fin 2)) :
    ContDiffOn ℝ n (amnrDirection b d) U := by
  exact _root_.AVenhance.Infra.Section4.Calculus.amnrDirection_contDiffOn hb d

/-- Every word consumes exactly one ordinary derivative per letter. -/
theorem amnrWord_contDiffOn {b : AmnrSpace → Vec 2} {U : Set AmnrSpace}
    (hU : IsOpen U) {N : ℕ} (hb : ContDiffOn ℝ N b U)
    {f : AmnrSpace → ℝ} (hf : ContDiffOn ℝ N f U)
    (w : List (Option (Fin 2))) {n : ℕ} (hn : n + w.length ≤ N) :
    ContDiffOn ℝ n (amnrWord b w f) U := by
  exact _root_.AVenhance.Infra.Section4.amnrWord_contDiffOn hU hb hf w hn

/-- Directional Leibniz rule, with no quantitative hypothesis. -/
theorem amnrOp_mul {b : AmnrSpace → Vec 2} (d : Option (Fin 2))
    {f g : AmnrSpace → ℝ} {z : AmnrSpace}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    amnrOp b d (f * g) z = amnrOp b d f z * g z + f z * amnrOp b d g z := by
  exact _root_.AVenhance.Infra.Section4.amnrOp_mul d hf hg

/-- Directional differentiation commutes with finite sums of differentiable functions. -/
theorem amnrOp_sum {ι : Type*} (S : Finset ι) {b : AmnrSpace → Vec 2}
    (d : Option (Fin 2)) (f : ι → AmnrSpace → ℝ) (z : AmnrSpace)
    (hf : ∀ i ∈ S, DifferentiableAt ℝ (f i) z) :
    amnrOp b d (∑ i ∈ S, f i) z = ∑ i ∈ S, amnrOp b d (f i) z := by
  exact _root_.AVenhance.Infra.Section4.amnrOp_sum S d f z hf

theorem amnrOp_material {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    {z : AmnrSpace} (hf : DifferentiableAt ℝ f z) :
    amnrOp b none f z = amnrMaterial (fun t x => b (t, x))
      (fun t x => f (t, x)) z.1 z.2 := by
  exact _root_.AVenhance.Infra.Section4.amnrOp_material hf

end AVenhance.Infra.Section4.IterateCalculus
