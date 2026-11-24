/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import Mathlib.Topology.Subpath
import LeanPool.GraphMinor.GM12.Section2EntryPaths
import LeanPool.GraphMinor.GM12.Section2PathHomotopy

/-!
# Normalizing the approach in an entry curve

The two entry curves compared in XII, page 243, may start at different
points of the same approach. Put that approach on the unit interval.
Splitting each entry curve at its joining time gives its terminal spoke
and a subpath of the common approach. Concatenation changes only the
parametrization, up to a homotopy fixing the endpoints.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Split an entry curve into a subpath of a fixed approach and its
terminal spoke. The approach's earlier starting time is explicit, so
this lemma applies when two entry curves start at different points. -/
theorem normalize_entry_approach {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    (j : X → S) (hj : Function.Injective j) {a b w : X} (F : Path a b)
    {f : ℝ → S} {h₀ h c : ℝ} {s : unitInterval}
    (hF : ∀ t, j (F t) = f (h₀ + t.val * (c - h₀)))
    (hstart : h = h₀ + s.val * (c - h₀))
    (P : Path (F s) w) (ξ : Curve S) (hP : ∀ t, j (P t) = ξ t)
    {τ : unitInterval} (hτ : 0 < τ)
    (hfirst : ∀ t : unitInterval, t ≤ τ → ξ t = f (h + t.val / τ.val * (c - h))) :
    ∃ β : Path (F 1) w,
      (∀ t, j (β t) = ξ (Icc.convexComb τ 1 t)) ∧
      ((F.subpath s 1).trans β).Homotopic P := by
  have hjoin : P τ = F 1 := by
    apply hj
    rw [hP, hfirst τ le_rfl, hF]
    have hτ' : τ.val ≠ 0 := ne_of_gt hτ
    simp only [div_self hτ', one_mul, Icc.coe_one]
    congr 1
    ring
  let β₀ : Path (P τ) w := (P.subpath τ 1).cast rfl P.target.symm
  let β : Path (F 1) w := β₀.cast hjoin.symm rfl
  let α : Path (F s) (P τ) := (F.subpath s 1).cast rfl hjoin
  have hα : ∀ t, α t = (P.subpath 0 τ) t := by
    intro t
    apply hj
    change j ((F.subpath s 1) t) = j ((P.subpath 0 τ) t)
    rw [entry_subpath_prefix j P ξ hP hτ hfirst]
    change j (F (Icc.convexComb s 1 t)) = _
    rw [hF]
    congr 1
    simp only [Icc.coe_convexComb, Icc.coe_one]
    rw [hstart]
    ring
  have hβ₀ : ∀ t, β₀ t = (P.subpath τ 1) t := fun _ => rfl
  have hsplit := split_path_homotopic P τ α β₀ hα hβ₀
  refine ⟨β, ?_, ?_⟩
  · intro t
    change j (P (Icc.convexComb τ 1 t)) = _
    exact hP _
  · have heq : (F.subpath s 1).trans β = α.trans β₀ := by
      ext t
      simp only [Path.trans_apply]
      split_ifs <;> rfl
    rw [heq]
    exact hsplit

end GraphMinor.GM12
