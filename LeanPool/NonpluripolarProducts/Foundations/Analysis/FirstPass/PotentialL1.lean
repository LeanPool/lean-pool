/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ExtendedDifference
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Local L¹ convergence of extended-real potentials

The ordinary `L¹` topology on quasi-plurisubharmonic potentials is expressed
intrinsically through holomorphic charts.  On every compact subset of a chart
target we integrate the actual extended-real absolute difference against the
standard Lebesgue measure on `ComplexModel n`.  The canonical difference is
zero at a common pole and remains infinite at a one-sided pole, so no arbitrary
`EReal.toReal` truncation enters the definition.

For a compact manifold, convergence for all chartwise compact subsets is the
usual local `L¹` convergence, hence the usual global `L¹` topology after taking
a finite atlas.  That equivalence is a separate compactness theorem and is not
built into the definition below.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- The extended `L¹` distance between two potentials on a measurable chart
set.  It is meaningful without an a priori integrability hypothesis: its value
may be `⊤`. -/
def chartL1EDistance (u v : M → EReal) (e : ComplexChart n M)
    (K : Set (ComplexModel n)) : ENNReal :=
  ∫⁻ z in K,
    canonicalERealAbsDiff (chartFunction u e z) (chartFunction v e z) ∂volume

@[simp] theorem chartL1EDistance_empty (u v : M → EReal)
    (e : ComplexChart n M) :
    chartL1EDistance u v e ∅ = 0 := by
  simp [chartL1EDistance]

theorem chartL1EDistance_mono_set (u v : M → EReal)
    (e : ComplexChart n M) {K L : Set (ComplexModel n)} (hKL : K ⊆ L) :
    chartL1EDistance u v e K ≤ chartL1EDistance u v e L := by
  exact lintegral_mono_set hKL

/-- Away from `⊤`, the canonical absolute difference of a value from itself is
zero, including at the common pole `⊥`. -/
theorem canonicalERealAbsDiff_self_of_ne_top {a : EReal} (ha : a ≠ ⊤) :
    canonicalERealAbsDiff a a = 0 := by
  cases a <;> simp_all [canonicalERealAbsDiff, poleModifiedERealAbsDiff]

@[simp] theorem chartL1EDistance_self_of_ne_top (u : M → EReal)
    (hu : ∀ x, u x ≠ ⊤) (e : ComplexChart n M) (K : Set (ComplexModel n)) :
    chartL1EDistance u u e K = 0 := by
  rw [chartL1EDistance, show
    (fun z => canonicalERealAbsDiff (chartFunction u e z) (chartFunction u e z)) =
      (fun _ => 0) from funext fun z =>
        canonicalERealAbsDiff_self_of_ne_top (hu (e.val.symm z))]
  simp

/-- Chart-local `L¹` convergence: the extended `L¹` distances tend to zero on
every compact subset of every holomorphic chart target. -/
def ManifoldL1LocallyTendsto {α : Type*} (u : α → M → EReal)
    (l : Filter α) (v : M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (K : Set (ComplexModel n)),
    IsCompact K → K ⊆ e.val.target →
      Tendsto (fun i => chartL1EDistance (u i) v e K) l (𝓝 0)

theorem manifoldL1LocallyTendsto_const (u : M → EReal)
    (hu : ∀ x, u x ≠ ⊤) {α : Type*} (l : Filter α) :
    ManifoldL1LocallyTendsto (n := n) (fun _ : α => u) l u := by
  intro e K _ _
  rw [show (fun _ : α => chartL1EDistance u u e K) = fun _ => 0 by
    funext i
    exact chartL1EDistance_self_of_ne_top u hu e K]
  exact tendsto_const_nhds

theorem ManifoldL1LocallyTendsto.congr {α : Type*}
    {u w : α → M → EReal} {l : Filter α} {v : M → EReal}
    (huw : ∀ i, u i = w i)
    (hu : ManifoldL1LocallyTendsto (n := n) u l v) :
    ManifoldL1LocallyTendsto (n := n) w l v := by
  have h : u = w := funext huw
  rw [← h]
  exact hu

/-- Eventual equality along the indexing filter is enough to identify two
chart-local `L¹` convergent families. -/
theorem ManifoldL1LocallyTendsto.congr' {α : Type*}
    {u w : α → M → EReal} {l : Filter α} {v : M → EReal}
    (huw : u =ᶠ[l] w)
    (hu : ManifoldL1LocallyTendsto (n := n) u l v) :
    ManifoldL1LocallyTendsto (n := n) w l v := by
  intro e K hK hKe
  apply (hu e K hK hKe).congr'
  filter_upwards [huw] with i hi
  rw [hi]

/-- Chart-local `L¹` convergence is stable under a filter reindexing. -/
theorem ManifoldL1LocallyTendsto.comp {α β : Type*}
    {u : α → M → EReal} {l : Filter α} {v : M → EReal}
    (hu : ManifoldL1LocallyTendsto (n := n) u l v)
    {g : β → α} {k : Filter β} (hg : Tendsto g k l) :
    ManifoldL1LocallyTendsto (n := n) (fun i => u (g i)) k v := by
  intro e K hK hKe
  exact (hu e K hK hKe).comp hg

/-- Passing to a finer indexing filter preserves chart-local `L¹`
convergence. -/
theorem ManifoldL1LocallyTendsto.mono_left {α : Type*}
    {u : α → M → EReal} {l k : Filter α} {v : M → EReal}
    (hu : ManifoldL1LocallyTendsto (n := n) u l v) (hkl : k ≤ l) :
    ManifoldL1LocallyTendsto (n := n) u k v := by
  intro e K hK hKe
  exact (hu e K hK hKe).mono_left hkl

end

end SGPT.Foundations.Analysis.FirstPass
