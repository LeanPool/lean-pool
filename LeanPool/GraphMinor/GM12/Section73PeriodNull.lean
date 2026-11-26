/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73RealPath
public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section2PeriodicHits
import LeanPool.GraphMinor.GM11.FlatCover

/-!
# Null-homotopy of a closed curve from one real period

In the representativity step of XII (7.3), page 261, a trace
deforms one real period of the normal circle to a null-homotopic
walk. Reading this path homotopy on the cylinder gives a homotopy
of the original closed curve to a constant curve.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A null-homotopy fixing the endpoints of one period makes the
original closed curve null-homotopic. This closes the trace-path
comparison used for representativity in XII (7.3), page 261. -/
theorem closedCurve_null_of_period_path
    {S : Type*} [TopologicalSpace S] (φ : C(Circle, S)) (a : ℝ)
    {x : S} (ha : periodicCurve φ a = x) (hb : periodicCurve φ (a + 1) = x)
    (hnull : ((realIntervalPath (periodicCurve φ) (periodicCurve_continuous φ) a (a + 1)).cast
      ha.symm hb.symm).Homotopic (Path.refl x)) :
    ClosedCurveIsNullHomotopicIn univ φ := by
  let p := (realIntervalPath (periodicCurve φ) (periodicCurve_continuous φ) a (a + 1)).cast
    ha.symm hb.symm
  let x' : (univ : Set S) := ⟨x, mem_univ x⟩
  let p' : Path x' x' := p.map toUniv.continuous
  have hp : ∀ t, (p' t).1 = φ (arcParam (Circle.exp (2 * Real.pi * a)) t) := by
    intro t
    change φ (Circle.exp (2 * Real.pi * (a + t.val * (a + 1 - a)))) = _
    rw [arcParam_apply, ← Circle.exp_add]
    congr 2
    ring
  have hh : p'.Homotopic (Path.refl x') := hnull.map toUniv
  exact ⟨x, mem_univ x, closedCurvesHomotopicIn_of_path
    (Circle.exp (2 * Real.pi * a)) φ (ContinuousMap.const Circle x)
    p' (Path.refl x') hp (fun _ => rfl) hh⟩

end GraphMinor.GM12
