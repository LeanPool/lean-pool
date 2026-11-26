/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Homotopy.Path
import LeanPool.GraphMinor.GM12.Section2PathHomotopy

/-!
# Paths on real parameter intervals

For the trace comparison in the representativity step of XII (7.3),
page 261, turn a real-parameter curve segment into a path on the unit
interval. Splitting its real interval gives the same path up to a
homotopy fixing the ends. This allows the homotopies for successive
region visits to be concatenated.
-/

public section

namespace GraphMinor.GM12

open Set Topology

/-- Restrict a continuous real-parameter curve to an interval and
rescale it to a path. -/
@[expose] noncomputable def realIntervalPath
    {S : Type*} [TopologicalSpace S] (f : ℝ → S) (hf : Continuous f) (a b : ℝ) :
    Path (f a) (f b) where
  toFun := fun t => f (a + t.val * (b - a))
  continuous_toFun := hf.comp (by fun_prop)
  source' := by change f (a + (0 : ℝ) * (b - a)) = f a; simp
  target' := by
    change f (a + (1 : ℝ) * (b - a)) = f b
    congr 1
    ring

/-- A real interval of length zero gives the constant path. -/
theorem realIntervalPath_self
    {S : Type*} [TopologicalSpace S] (f : ℝ → S) (hf : Continuous f) (a : ℝ) :
    realIntervalPath f hf a a = Path.refl (f a) := by
  ext t
  change f (a + t.val * (a - a)) = f a
  simp

/-- The paths on two successive real intervals concatenate to the
path on their union up to homotopy with fixed ends. This is the
partition step for traces in XII (7.3), page 261. -/
theorem realIntervalPath_split
    {S : Type*} [TopologicalSpace S] (f : ℝ → S) (hf : Continuous f)
    {a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    ((realIntervalPath f hf a c).trans (realIntervalPath f hf c b)).Homotopic
      (realIntervalPath f hf a b) := by
  let s : unitInterval := ⟨(c - a) / (b - a),
    div_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hab.le),
    (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hcb a)⟩
  have hs : a + s.val * (b - a) = c := by
    change a + ((c - a) / (b - a)) * (b - a) = c
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
    ring
  let P := realIntervalPath f hf a b
  have hmid : P s = f c := congrArg f hs
  let α : Path (f a) (P s) := (realIntervalPath f hf a c).cast rfl hmid
  let β : Path (P s) (f b) := (realIntervalPath f hf c b).cast hmid rfl
  have hα : ∀ t, α t = (P.subpath 0 s) t := by
    intro t
    change f (a + t.val * (c - a)) = f (a + ((1 - t.val) * 0 + t.val * s.val) * (b - a))
    apply congrArg f
    rw [← hs]
    ring
  have hβ : ∀ t, β t = (P.subpath s 1) t := by
    intro t
    change f (c + t.val * (b - c)) = f (a + ((1 - t.val) * s.val + t.val * 1) * (b - a))
    apply congrArg f
    rw [← hs]
    ring
  have hsplit := split_path_homotopic P s α β hα hβ
  exact hsplit

end GraphMinor.GM12
