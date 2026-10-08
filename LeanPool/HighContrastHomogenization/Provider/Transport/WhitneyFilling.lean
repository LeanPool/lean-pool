/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyCells

/-!
# High-contrast homogenization: Provider.Transport.WhitneyFilling

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The maximal filling of a target by the cells of a second grid

The filling family `𝒱_a(W;q)` of `l.two.grid.whitney`(i): among the
aligned `q`-cells of scale `a ≤ n`, the *selected* ones are those contained in the
target `W` whose aligned parent of scale `a+1` is not, together with all the
scale-`n` cells contained in `W`.  This is the family the cross-grid rows
`e.two.grid.whitney.volumes` and the finite cross-grid exhaustion are indexed
by, and the one the transport reads as `𝒱_r(W;q)` in
`e.two.grid.whitney.average`.

Three structural facts are proved here, all of them for an arbitrary target set.
The selected cells are pairwise disjoint *across all scales*: a finer selected
cell inside a coarser one would have its parent inside the coarser one too, hence
inside `W`, which the selection rule forbids.  Each is contained in `W` by
definition -- this is the containment convention the window hypothesis relies on,
and it is a property of the construction rather than an arithmetic fact about
triadic ratios.  And each scale carries only finitely many selected cells,
because a selected cell contains its own center, the centers of one scale form a
lattice, and the target is bounded.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The maximal filling `𝒱_a(W;q)`** of `l.two.grid.whitney`(i),
as the set of indices of the selected cells: an aligned `q`-cell of scale `a ≤ n`
is selected when it is contained in the target `W` and either `a = n` or its
aligned parent of scale `a+1` is not contained in `W`. -/
@[expose]
def fillingIndex (q : Mat d) (n : ℤ) (W : Set (Vec d)) (a : ℤ) : Set (Fin d → ℤ) :=
  {w | a ≤ n ∧ adaptedCellAt q a w ⊆ W ∧
    (a = n ∨ ¬ adaptedCellAt q (a + 1) (gridParent w) ⊆ W)}

/-- A selected cell is contained in the target. -/
theorem adaptedCellAt_subset_of_mem_fillingIndex {q : Mat d} {n a : ℤ} {W : Set (Vec d)}
    {w : Fin d → ℤ} (hw : w ∈ fillingIndex q n W a) : adaptedCellAt q a w ⊆ W :=
  hw.2.1

/-- A selected cell has a scale at most the starting scale of the filling. -/
theorem le_of_mem_fillingIndex {q : Mat d} {n a : ℤ} {W : Set (Vec d)}
    {w : Fin d → ℤ} (hw : w ∈ fillingIndex q n W a) : a ≤ n :=
  hw.1

/-! ## The selected cells are pairwise disjoint -/

private theorem disjoint_of_lt₀ {q : Mat d} (hq : q.PosDef) {W : Set (Vec d)} {n a b : ℤ}
    (hab : a < b) {w v : Fin d → ℤ} (hw : w ∈ fillingIndex q n W a)
    (hv : v ∈ fillingIndex q n W b) :
    Disjoint (adaptedCellAt q a w) (adaptedCellAt q b v) := by
  by_contra hcon
  obtain ⟨x, hx1, hx2⟩ := Set.not_disjoint_iff.mp hcon
  have hane : a ≠ n := by
    have := le_of_mem_fillingIndex hv
    omega
  have hpar : ¬ adaptedCellAt q (a + 1) (gridParent w) ⊆ W :=
    hw.2.2.resolve_left hane
  refine hpar ?_
  have hxpar : x ∈ adaptedCellAt q (a + 1) (gridParent w) :=
    adaptedCellAt_subset_parent q a w hx1
  exact (adaptedCellAt_subset_of_mem_of_mem hq (by omega) hxpar hx2).trans
    (adaptedCellAt_subset_of_mem_fillingIndex hv)

/-- **The selected cells of the maximal filling are pairwise disjoint**, across
all scales: this is the disjointness clause of
`l.two.grid.whitney`(i). -/
theorem disjoint_of_mem_fillingIndex {q : Mat d} (hq : q.PosDef) {W : Set (Vec d)}
    {n a b : ℤ} {w v : Fin d → ℤ} (hw : w ∈ fillingIndex q n W a)
    (hv : v ∈ fillingIndex q n W b) (hne : (a, w) ≠ (b, v)) :
    Disjoint (adaptedCellAt q a w) (adaptedCellAt q b v) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact disjoint_of_lt₀ hq hab hw hv
  · subst hab
    refine Recurrence.disjoint_adaptedCellAt hq a fun hwv => hne ?_
    rw [hwv]
  · exact (disjoint_of_lt₀ hq hab hv hw).symm

/-! ## Each scale carries finitely many selected cells -/

/-- **A scale of the maximal filling is finite.**  A selected cell contains its
own center, so the selected indices of one scale are lattice points of a bounded
region. -/
theorem finite_fillingIndex {q : Mat d} (hq : q.PosDef) {W : Set (Vec d)}
    (hW : IsBoundedDomain W) (n a : ℤ) : (fillingIndex q n W a).Finite := by
  classical
  obtain ⟨R, hR, hRW⟩ := hW
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  set B : ℝ := ‖q⁻¹‖ * (Real.sqrt d * R) * (3 : ℝ) ^ (-a) with hB
  refine Set.Finite.subset (Finset.finite_toSet
    (Fintype.piFinset fun _ : Fin d => Finset.Icc (-⌈B⌉) ⌈B⌉)) ?_
  intro w hw
  have hcen : adaptedCellCenter q a w ∈ W := by
    refine adaptedCellAt_subset_of_mem_fillingIndex hw ?_
    rw [Recurrence.adaptedCellAt_eq_image, Recurrence.adaptedCellCenter_eq]
    exact ⟨standardCellCenter a w, Recurrence.standardCellCenter_mem_standardCell a w, rfl⟩
  have hpull : matVecMul q⁻¹ (adaptedCellCenter q a w) = standardCellCenter a w := by
    rw [Recurrence.adaptedCellCenter_eq]
    change q⁻¹ *ᵥ q *ᵥ standardCellCenter a w = standardCellCenter a w
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hbound : ∀ i, |standardCellCenter a w i| ≤ ‖q⁻¹‖ * (Real.sqrt d * R) := by
    intro i
    rw [← hpull]
    exact abs_matVecMul_le_of_abs_le q⁻¹ (fun k => hRW _ hcen k) i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
  have hentry : standardCellCenter a w i = (3 : ℝ) ^ a * (w i : ℝ) := rfl
  have hi := hbound i
  rw [hentry, abs_mul, abs_of_pos h3] at hi
  have hwi : |(w i : ℝ)| ≤ B := by
    rw [hB, zpow_neg, ← div_eq_mul_inv, le_div_iff₀ h3]
    linarith only [hi]
  have hceil : |((w i : ℤ) : ℝ)| ≤ ((⌈B⌉ : ℤ) : ℝ) := hwi.trans (Int.le_ceil B)
  rw [← Int.cast_abs] at hceil
  have habs : |w i| ≤ ⌈B⌉ := by exact_mod_cast hceil
  exact abs_le.mp habs

/-! ## The selected ancestor of a cell contained in the target -/

/-- **A cell contained in the target has a selected ancestor.**  Taking the
coarsest ancestor still contained in `W`, within the scale range of the filling,
produces a selected cell containing the given one: either that ancestor sits at
the starting scale `n`, or its own parent escapes `W`.  This is the step
"let `b` be the largest scale in `{J,…,n}` such that `C^{(b)} ⊆ W`" of
`l.two.grid.whitney`(i). -/
theorem exists_mem_fillingIndex_of_subset {q : Mat d} {W : Set (Vec d)} {n J : ℤ}
    (hJn : J ≤ n) {w : Fin d → ℤ} (hw : adaptedCellAt q J w ⊆ W) :
    ∃ b : ℕ, J + (b : ℤ) ≤ n ∧ gridParent^[b] w ∈ fillingIndex q n W (J + (b : ℤ)) ∧
      adaptedCellAt q J w ⊆ adaptedCellAt q (J + (b : ℤ)) (gridParent^[b] w) := by
  classical
  set S : Finset ℕ := (Finset.range ((n - J).toNat + 1)).filter
    fun k => adaptedCellAt q (J + (k : ℤ)) (gridParent^[k] w) ⊆ W with hS
  have h0 : 0 ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    simpa using hw
  have hne : S.Nonempty := ⟨0, h0⟩
  have hbS := S.max'_mem hne
  set b : ℕ := S.max' hne with hb
  rw [hS, Finset.mem_filter, Finset.mem_range] at hbS
  have hbn : J + (b : ℤ) ≤ n := by omega
  refine ⟨b, hbn, ⟨hbn, hbS.2, ?_⟩, adaptedCellAt_subset_ancestor q J w b⟩
  rcases eq_or_lt_of_le hbn with heq | hlt
  · exact Or.inl heq
  · refine Or.inr fun hcon => ?_
    have hmem : b + 1 ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [Function.iterate_succ_apply' gridParent b w]
      have hscale : J + ((b : ℕ) + 1 : ℕ) = J + (b : ℤ) + 1 := by push_cast; ring
      rw [hscale]
      exact hcon
    have hle := S.le_max' (b + 1) hmem
    omega

end

end Transport
end HighContrast
end HCPolySupport
