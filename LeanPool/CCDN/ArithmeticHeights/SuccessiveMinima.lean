/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# The successive minima of a symmetric convex body

For a lattice `L` in a finite-dimensional real normed space `E` and a symmetric convex body `B`,
the `i`-th successive minimum is the least dilation of `B` that contains `i + 1` linearly
independent points of `L`. This file defines it, proves it positive, monotone and homogeneous of
degree `-1` in the body, and proves Cassels' Lemma 1: the minima are attained, by one family of
independent lattice vectors realizing all of them at once.

## Main definitions

* `ZLattice.successiveMinimum`: the `i`-th successive minimum, as the infimum of the admissible
  dilations. For `i ≥ finrank ℝ E` there are none and the value is `sInf ∅ = 0`, so every
  statement below carries `i < finrank ℝ E`.

## Main results

* `gauge_le_iff_mem_smul`: the dictionary between Cassels' distance functions and the convex-body
  form pinned by the roadmap. Membership in `t • B` is having gauge at most `t`, for a **closed**
  body; `mem_smul_of_gauge_lt` is the half that needs no closedness.
* `ZLattice.successiveMinimum_pos`: the minima are positive, which is where boundedness of the
  body is used, and `ZLattice.successiveMinimum_eq_zero_of_le`: they vanish above the dimension.
* `ZLattice.successiveMinimum_le_of_le` and `ZLattice.successiveMinimum_smul`: monotone in the
  index, homogeneous of degree `-1` in the body.
* `ZLattice.exists_linearIndependent_gauge_eq_successiveMinimum`: **Cassels' Lemma 1**. There is
  one linearly independent family of lattice vectors whose gauges are the successive minima. This
  is what every later proof consumes; its body form is
  `ZLattice.exists_linearIndependent_mem_smul_successiveMinimum`, which is where closedness of
  the body is used.
* `Finset.prod_pow_le_prod_range`: the regrouping that turns a bound on the product of all `d * k`
  minima into a bound on a product of `k` `d`-th powers — what Layers 5.3 and 5.4 spend to pass
  from the minima of the lattice of a `k`-dimensional `K`-subspace to `k` heights.
* `ZLattice.successiveMinimum_zero_eq`: the zeroth minimum is the least dilation containing a
  nonzero lattice point — the quantity Minkowski's convex-body theorem bounds — and
  `ZLattice.successiveMinimum_zero_le_one` is that theorem read as the case `i = 0`.

## Implementation notes

The body is carried as four separate hypotheses — convex, symmetric, with nonempty interior,
bounded — plus closedness where it is needed, rather than as one bundled structure, so that each
statement says which of them it uses. Cassels indexes the minima by a distance function `F` and
dilates `{x | F x ≤ 1}`; the convex-body form is the pinned one, and `gauge_le_iff_mem_smul` is
the translation, proved once here.

⚠ **Attainment does not need the body to be closed; only its body form does.** The family of
`ZLattice.exists_linearIndependent_gauge_eq_successiveMinimum` realizes the minima as *gauges*
for any bounded symmetric convex body with nonempty interior, and that statement is the one the
proof produces. Turning `gauge B (v j) = λ j` into `v j ∈ λ j • B` is exactly the dictionary, and
exactly what fails for an open body: for the open unit ball no lattice vector lies in `λ 0 • B`
at all, since anything inside that dilation would already have shown a smaller dilation
admissible. The two statements are therefore kept apart, and only the second carries `IsClosed B`.

⚠ **The minima are not monotone in the index without `i < finrank ℝ E`.** Above the dimension
there is no independent family at all, the set of admissible dilations is empty, and the value is
`sInf ∅ = 0`. So `Monotone (successiveMinimum L B)` is false whenever `E` is nontrivial, and a
statement of Minkowski's second theorem that ranged over all of `ℕ` would multiply by zero.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter VIII §1:
the definition, Lemma 1 (attainment) and the elementary properties proved here. E. Bombieri and
W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006), Appendix C.2.
Minkowski's first theorem is Mathlib's
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`.

This is Layer 4.1 of the `ArithmeticHeights` roadmap.
-/

public section

open Metric Module MeasureTheory Set

open scoped Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}

/-! ### The body and its gauge

Three facts about a symmetric convex body, none of them about lattices: it is a neighbourhood of
the origin, and its dilations are the sublevel sets of its gauge — from below always, and exactly
when the body is closed. -/

/-- A symmetric convex set with nonempty interior is a neighbourhood of `0`: the midpoint of an
interior point and its negative is an interior point. This is what makes the body absorbent, and
it is the only use of the symmetry hypothesis in the elementary theory. -/
theorem Convex.mem_nhds_zero_of_symmetric (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) : B ∈ 𝓝 (0 : E) := by
  obtain ⟨x, hx⟩ := hB₂
  have hneg : -x ∈ B := hB₁ x (interior_subset hx)
  have h0 : (0 : E) ∈ interior B := by
    have := hB₀.combo_interior_self_mem_interior hx hneg (a := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    simpa using this
  exact mem_interior_iff_mem_nhds.1 h0

/-- Half of the gauge dictionary, and the half that costs nothing: a point of gauge strictly less
than `t` lies in `t • B`. No closedness is needed, and this is what the existence statements below
use to exhibit an admissible dilation. -/
theorem mem_smul_of_gauge_lt (hB₀ : Convex ℝ B) (h₀ : B ∈ 𝓝 (0 : E)) {t : ℝ} {x : E}
    (h : gauge B x < t) : x ∈ t • B := by
  have hx : x ∈ {y : E | gauge B y ≤ gauge B x} := by simp
  rw [setOfPred_gauge_le_eq hB₀ (mem_of_mem_nhds h₀) (absorbent_nhds_zero h₀)
    (gauge_nonneg x)] at hx
  exact mem_iInter₂.1 hx t h

/-- **The gauge dictionary.** For a closed convex body with `0` in its interior, lying in the
dilation `t • B` is the same as having gauge at most `t`. This is the translation between Cassels'
distance functions and the convex-body form of the successive minima, and closedness is exactly
what it costs: for an open body the two sides differ on the boundary. -/
theorem gauge_le_iff_mem_smul (hB₀ : Convex ℝ B) (hB₄ : IsClosed B) (h₀ : B ∈ 𝓝 (0 : E)) {t : ℝ}
    (ht : 0 < t) {x : E} : gauge B x ≤ t ↔ x ∈ t • B := by
  refine ⟨fun h ↦ ?_, gauge_le_of_mem ht.le⟩
  have h1 : gauge B (t⁻¹ • x) ≤ 1 := by
    rw [gauge_smul_of_nonneg (inv_nonneg.2 ht.le), smul_eq_mul, inv_mul_le_iff₀ ht, mul_one]
    exact h
  have h2 : t⁻¹ • x ∈ B := by
    rw [← hB₄.closure_eq]
    exact (gauge_le_one_iff_mem_closure hB₀ h₀).1 h1
  rwa [mem_smul_set_iff_inv_smul_mem₀ ht.ne']

namespace ZLattice

variable {i : ℕ}

/-- The `i`-th **successive minimum** of a set `B` with respect to a lattice `L`: the least
dilation of `B` containing `i + 1` linearly independent points of `L`. The case `i = 0` is the
quantity bounded by Minkowski's convex-body theorem. For `i ≥ finrank ℝ E` there is no such
family and the value is `sInf ∅ = 0`, so every statement about the minima carries
`i < finrank ℝ E`. -/
noncomputable def successiveMinimum (L : Submodule ℤ E) (B : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ v : Fin (i + 1) → E,
    (∀ j, v j ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ v}

variable {L : Submodule ℤ E}

/-- An admissible dilation bounds the minimum from above. This and `le_successiveMinimum` are the
only two ways the infimum is used below. -/
theorem successiveMinimum_le {t : ℝ} (ht : 0 < t) {v : Fin (i + 1) → E}
    (hv : ∀ j, v j ∈ (t • B) ∩ (L : Set E)) (hind : LinearIndependent ℝ v) :
    successiveMinimum L B i ≤ t :=
  csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩ ⟨ht, v, hv, hind⟩

/-- The minima are homogeneous of degree `-1` in the body: dilating the body by `c` divides every
minimum by `c`. -/
theorem successiveMinimum_smul (L : Submodule ℤ E) (B : Set E) (i : ℕ) {c : ℝ} (hc : 0 < c) :
    successiveMinimum L (c • B) i = c⁻¹ * successiveMinimum L B i := by
  rw [successiveMinimum, successiveMinimum, ← smul_eq_mul,
    ← Real.sInf_smul_of_nonneg (inv_nonneg.2 hc.le)]
  congr 1
  ext t
  simp only [mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨ht, v, hv, hind⟩
    refine ⟨t * c, ⟨by positivity, v, fun j ↦ ⟨?_, (hv j).2⟩, hind⟩, by field_simp⟩
    have := (hv j).1
    rwa [smul_smul] at this
  · rintro ⟨s, ⟨hs, v, hv, hind⟩, rfl⟩
    have heq : c⁻¹ * s * c = s := by field_simp
    refine ⟨by positivity, v, fun j ↦ ⟨?_, (hv j).2⟩, hind⟩
    rw [smul_smul, heq]
    exact (hv j).1

variable [FiniteDimensional ℝ E]

section Elementary

variable [DiscreteTopology L] [IsZLattice ℝ L]

/-- A `ℤ`-basis of a lattice of `E`, read as an `ℝ`-basis of `E` indexed by `Fin (finrank ℝ E)`.
Every basis vector is a lattice point, which is what makes the set of admissible dilations
nonempty. -/
private theorem exists_basis_mem (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, ∀ j, b j ∈ L := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  refine ⟨((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).reindex
    (Fintype.equivFinOfCardEq hcard), fun j ↦ ?_⟩
  simp only [Basis.reindex_apply, Basis.ofZLatticeBasis_apply]
  exact SetLike.coe_mem _

/-- Below the dimension there is an admissible dilation: a basis of `E` made of lattice vectors
is independent, and the body absorbs its finitely many members. -/
private theorem exists_mem_minimumSet (hi : i < finrank ℝ E) (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) :
    ∃ t : ℝ, 0 < t ∧ ∃ v : Fin (i + 1) → E,
      (∀ j, v j ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ v := by
  have h₀ : B ∈ 𝓝 (0 : E) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  obtain ⟨b, hb⟩ := exists_basis_mem L
  set v : Fin (i + 1) → E := fun j ↦ b (j.castLE hi)
  set t : ℝ := 1 + ∑ j, gauge B (v j)
  have hlt : ∀ j, gauge B (v j) < t := fun j ↦ by
    have : gauge B (v j) ≤ ∑ k, gauge B (v k) :=
      Finset.single_le_sum (fun k _ ↦ gauge_nonneg (v k)) (Finset.mem_univ j)
    linarith
  refine ⟨t, ?_, v, fun j ↦ ⟨mem_smul_of_gauge_lt hB₀ h₀ (hlt j), ?_⟩, ?_⟩
  · have : (0 : ℝ) ≤ ∑ j, gauge B (v j) :=
      Finset.sum_nonneg fun j _ ↦ gauge_nonneg (v j)
    linarith
  · exact hb _
  · exact b.linearIndependent.comp _ fun a c h ↦ Fin.castLE_injective hi h

/-- Below the dimension, a lower bound for every admissible dilation is a lower bound for the
minimum. -/
theorem le_successiveMinimum (hi : i < finrank ℝ E) (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) {c : ℝ}
    (H : ∀ t : ℝ, 0 < t → ∀ v : Fin (i + 1) → E, (∀ j, v j ∈ (t • B) ∩ (L : Set E)) →
      LinearIndependent ℝ v → c ≤ t) :
    c ≤ successiveMinimum L B i :=
  le_csInf (exists_mem_minimumSet hi hB₀ hB₁ hB₂) fun _ ht ↦ H _ ht.1 _ ht.2.choose_spec.1
    ht.2.choose_spec.2

end Elementary

/-- Above the dimension the minima vanish: there is no independent family of `i + 1` vectors at
all, so the set of admissible dilations is empty and its infimum is the junk value `0`. Together
with `successiveMinimum_pos` this is why every statement about the minima is restricted to
`i < finrank ℝ E`. -/
theorem successiveMinimum_eq_zero_of_le (L : Submodule ℤ E) (B : Set E) (hi : finrank ℝ E ≤ i) :
    successiveMinimum L B i = 0 := by
  have hempty : {t : ℝ | 0 < t ∧ ∃ v : Fin (i + 1) → E,
      (∀ j, v j ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ v} = ∅ := by
    ext t
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    rintro -
    rintro ⟨v, -, hind⟩
    have := hind.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  rw [successiveMinimum, hempty, Real.sInf_empty]

/-- The minima are monotone in the index below the dimension: an independent family of `j + 1`
vectors contains one of `i + 1` vectors, so every dilation admissible at `j` is admissible at
`i`. The hypothesis `j < finrank ℝ E` is not removable — see `successiveMinimum_eq_zero_of_le`. -/
theorem successiveMinimum_le_of_le [DiscreteTopology L] [IsZLattice ℝ L] {j : ℕ} (hij : i ≤ j)
    (hj : j < finrank ℝ E) (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) :
    successiveMinimum L B i ≤ successiveMinimum L B j := by
  refine le_csInf (exists_mem_minimumSet hj hB₀ hB₁ hB₂) ?_
  rintro t ⟨ht, v, hv, hind⟩
  have hle : i + 1 ≤ j + 1 := by omega
  refine successiveMinimum_le ht (v := fun k ↦ v (k.castLE hle)) (fun k ↦ hv _) ?_
  exact hind.comp _ fun a c h ↦ Fin.castLE_injective hle h

section Discrete

variable [DiscreteTopology L]

/-- A bounded gauge slice meets the lattice in a finite set: the slice is bounded because the body
is, and the lattice is discrete and closed. This is the one place discreteness of the lattice is
used, and every attainment statement below rests on it. -/
private theorem finite_gauge_le_inter (L : Submodule ℤ E) [DiscreteTopology L]
    (h₀ : B ∈ 𝓝 (0 : E)) (hB₃ : Bornology.IsBounded B) (t : ℝ) :
    ({x : E | gauge B x ≤ t} ∩ (L : Set E)).Finite := by
  obtain ⟨R, hR, hRB⟩ := hB₃.subset_closedBall_lt 0 0
  refine Metric.finite_isBounded_inter_isClosed ?_ ?_ ?_
  · exact DiscreteTopology.isDiscrete
  · refine (Metric.isBounded_closedBall (x := (0 : E)) (r := R * t)).subset fun x hx ↦ ?_
    have hx' : ‖x‖ / R ≤ t :=
      le_trans (le_gauge_of_subset_closedBall (absorbent_nhds_zero h₀) hR.le hRB) hx
    rw [mem_closedBall_zero_iff]
    rw [div_le_iff₀ hR] at hx'
    linarith [hx', mul_comm t R]
  · have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_discreteTopology

/-- The gauge attains its minimum on any nonempty set of lattice points: the points of gauge at
most that of a chosen member form a finite set. -/
private theorem exists_gauge_min (L : Submodule ℤ E) [DiscreteTopology L] (h₀ : B ∈ 𝓝 (0 : E))
    (hB₃ : Bornology.IsBounded B) {S : Set E} (hS : S ⊆ (L : Set E)) (hne : S.Nonempty) :
    ∃ w ∈ S, ∀ y ∈ S, gauge B w ≤ gauge B y := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hfin : (S ∩ {x : E | gauge B x ≤ gauge B x₀}).Finite := by
    refine (finite_gauge_le_inter L h₀ hB₃ (gauge B x₀)).subset fun x hx ↦ ⟨hx.2, hS hx.1⟩
  obtain ⟨w, hw, hmin⟩ := Set.exists_min_image _ (gauge B) hfin ⟨x₀, hx₀, by simp⟩
  refine ⟨w, hw.1, fun y hy ↦ ?_⟩
  by_cases hy' : gauge B y ≤ gauge B x₀
  · exact hmin y ⟨hy, hy'⟩
  · exact le_trans (hmin x₀ ⟨hx₀, by simp⟩) (not_le.1 hy').le

variable [IsZLattice ℝ L]

/-- Nonzero lattice points have gauge bounded away from zero. This is where boundedness of the
body is used: the body is inside a ball, so a point of small gauge is a point of small norm, and
the lattice has none but `0`. -/
private theorem exists_pos_le_gauge (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (h₀ : B ∈ 𝓝 (0 : E)) (hB₃ : Bornology.IsBounded B) (hE : 0 < finrank ℝ E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ (L : Set E), x ≠ 0 → δ ≤ gauge B x := by
  obtain ⟨b, hb⟩ := exists_basis_mem L
  have hne : {x : E | x ∈ (L : Set E) ∧ x ≠ 0}.Nonempty :=
    ⟨b ⟨0, hE⟩, hb _, b.ne_zero _⟩
  obtain ⟨w, hw, hwmin⟩ := exists_gauge_min L h₀ hB₃ (fun y hy ↦ hy.1) hne
  refine ⟨gauge B w, ?_, fun x hx hx0 ↦ hwmin x ⟨hx, hx0⟩⟩
  rw [gauge_pos (absorbent_nhds_zero h₀) ((NormedSpace.isVonNBounded_iff ℝ).2 hB₃)]
  exact hw.2

/-- **The minima are positive.** A nonzero lattice point has gauge bounded away from zero, so no
small dilation of a bounded body can contain one. -/
theorem successiveMinimum_pos (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    (hB₃ : Bornology.IsBounded B) (hi : i < finrank ℝ E) : 0 < successiveMinimum L B i := by
  have h₀ : B ∈ 𝓝 (0 : E) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  obtain ⟨δ, hδ, hlow⟩ := exists_pos_le_gauge L h₀ hB₃ (by omega)
  refine lt_of_lt_of_le hδ (le_successiveMinimum hi hB₀ hB₁ hB₂ fun t ht v hv hind ↦ ?_)
  exact (hlow (v 0) (hv 0).2 (hind.ne_zero 0)).trans (gauge_le_of_mem ht.le (hv 0).1)

end Discrete

section Attainment

variable [DiscreteTopology L] [IsZLattice ℝ L]

/-- The inductive step of Cassels' Lemma 1, carrying the minimality of the family over the
complement of its own span: that clause is what makes the gauges increase along the family, and
it is the reason the construction is greedy rather than a choice for each index separately. -/
private theorem exists_gauge_eq_aux (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    (hB₃ : Bornology.IsBounded B) :
    ∀ m : ℕ, m ≤ finrank ℝ E → ∃ v : Fin m → E, (∀ j, v j ∈ (L : Set E)) ∧
      LinearIndependent ℝ v ∧ (∀ j : Fin m, gauge B (v j) = successiveMinimum L B j) ∧
      ∀ y ∈ (L : Set E), y ∉ Submodule.span ℝ (Set.range v) → ∀ j, gauge B (v j) ≤ gauge B y := by
  have h₀ : B ∈ 𝓝 (0 : E) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  intro m
  induction m with
  | zero =>
    exact fun _ ↦ ⟨Fin.elim0, fun j ↦ j.elim0, linearIndependent_empty_type, fun j ↦ j.elim0,
      fun _ _ _ j ↦ j.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨v, hvL, hvind, hvmin, hvlow⟩ := ih (by omega)
    have hrank : finrank ℝ (Submodule.span ℝ (Set.range v)) = m := by
      rw [finrank_span_eq_card hvind, Fintype.card_fin]
    have hWlt : Submodule.span ℝ (Set.range v) < ⊤ :=
      Submodule.lt_top_of_finrank_lt_finrank (by rw [hrank]; omega)
    have hne : {y : E | y ∈ (L : Set E) ∧ y ∉ Submodule.span ℝ (Set.range v)}.Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty, eq_empty_iff_forall_notMem] at hcon
      refine hWlt.ne (top_le_iff.1 ?_)
      rw [← (IsZLattice.span_top (K := ℝ) (L := L) : Submodule.span ℝ (L : Set E) = ⊤)]
      refine Submodule.span_le.2 fun y hy ↦ ?_
      by_contra hyW
      exact hcon y ⟨hy, hyW⟩
    obtain ⟨w, hw, hwmin⟩ := exists_gauge_min L h₀ hB₃ (fun y hy ↦ hy.1) hne
    obtain ⟨hwL, hwW⟩ := hw
    have hgle : ∀ j : Fin (m + 1), gauge B ((Fin.snoc v w : Fin (m + 1) → E) j) ≤ gauge B w := by
      refine Fin.lastCases ?_ fun k ↦ ?_
      · simp
      · simpa using hvlow w hwL hwW k
    have hv'ind : LinearIndependent ℝ (Fin.snoc v w : Fin (m + 1) → E) := hvind.finSnoc hwW
    have hv'L : ∀ j : Fin (m + 1), (Fin.snoc v w : Fin (m + 1) → E) j ∈ (L : Set E) := by
      refine Fin.lastCases ?_ fun k ↦ ?_
      · simpa using hwL
      · simpa using hvL k
    have hgw : gauge B w = successiveMinimum L B m := by
      refine le_antisymm ?_ ?_
      · refine le_successiveMinimum (by omega) hB₀ hB₁ hB₂ fun t ht u hu huind ↦ ?_
        have hex : ∃ k, u k ∉ Submodule.span ℝ (Set.range v) := by
          by_contra hcon
          rw [not_exists] at hcon
          have hle : Submodule.span ℝ (Set.range u) ≤ Submodule.span ℝ (Set.range v) := by
            refine Submodule.span_le.2 ?_
            rintro _ ⟨k, rfl⟩
            exact not_not.1 (hcon k)
          have := Submodule.finrank_mono hle
          rw [finrank_span_eq_card huind, Fintype.card_fin, hrank] at this
          omega
        obtain ⟨k, hk⟩ := hex
        exact (hwmin (u k) ⟨(hu k).2, hk⟩).trans (gauge_le_of_mem ht.le (hu k).1)
      · refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
        refine successiveMinimum_le (lt_of_le_of_lt (gauge_nonneg w) ht)
          (v := Fin.snoc v w) (fun j ↦ ⟨?_, hv'L j⟩) hv'ind
        exact mem_smul_of_gauge_lt hB₀ h₀ (lt_of_le_of_lt (hgle j) ht)
    refine ⟨Fin.snoc v w, hv'L, hv'ind, ?_, ?_⟩
    · refine Fin.lastCases ?_ fun k ↦ ?_
      · simpa using hgw
      · simpa using hvmin k
    · intro y hy hyW
      have hsub : Set.range v ⊆ Set.range (Fin.snoc v w : Fin (m + 1) → E) := by
        rw [Set.range_subset_iff]
        exact fun k ↦ ⟨k.castSucc, by simp⟩
      have hyW' : y ∉ Submodule.span ℝ (Set.range v) := fun h ↦
        hyW (Submodule.span_mono hsub h)
      refine Fin.lastCases ?_ fun k ↦ ?_
      · simpa using hwmin y ⟨hy, hyW'⟩
      · simpa using hvlow y hy hyW' k

/-- **Cassels' Lemma 1: the successive minima are attained.** There is a single family of
`finrank ℝ E` linearly independent lattice vectors whose gauges are the successive minima — not
one family for each index. This is the statement every later proof consumes.

⚠ No closedness of the body is needed here; see
`exists_linearIndependent_mem_smul_successiveMinimum` for the body form, which does need it. -/
theorem exists_linearIndependent_gauge_eq_successiveMinimum (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    ∃ v : Fin (finrank ℝ E) → E, (∀ j, v j ∈ (L : Set E)) ∧ LinearIndependent ℝ v ∧
      ∀ j : Fin (finrank ℝ E), gauge B (v j) = successiveMinimum L B j :=
  let ⟨v, hvL, hvind, hvmin, _⟩ := exists_gauge_eq_aux L hB₀ hB₁ hB₂ hB₃ (finrank ℝ E) le_rfl
  ⟨v, hvL, hvind, hvmin⟩

/-- The body form of Cassels' Lemma 1: the independent lattice vectors realizing the minima lie in
the corresponding dilations of the body. This is the form Minkowski's second theorem and the basis
lemma of Layer 4.6 consume, and `IsClosed B` is exactly what it costs over the gauge form. -/
theorem exists_linearIndependent_mem_smul_successiveMinimum (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) (hB₄ : IsClosed B) :
    ∃ v : Fin (finrank ℝ E) → E, (∀ j, v j ∈ (L : Set E)) ∧ LinearIndependent ℝ v ∧
      ∀ j : Fin (finrank ℝ E), v j ∈ (successiveMinimum L B j) • B := by
  obtain ⟨v, hvL, hvind, hvg⟩ :=
    exists_linearIndependent_gauge_eq_successiveMinimum L hB₀ hB₁ hB₂ hB₃
  refine ⟨v, hvL, hvind, fun j ↦ ?_⟩
  have hpos : 0 < successiveMinimum L B j :=
    successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ j.isLt
  rw [← gauge_le_iff_mem_smul hB₀ hB₄ (hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂) hpos, hvg j]

/-- **The dependence half of Cassels' Lemma 1.** Outside the span of the first `j` members of a
family realizing the minima there is nothing of gauge below the `j`-th minimum. The point would
extend those `j` members to an independent family of `j + 1` lattice points, which bounds the
`j`-th minimum by the largest gauge in the family; the induction on `j` is what identifies that
largest gauge as the gauge of the new point, since without it the bound is only by the maximum of
the new gauge and the `(j - 1)`-st minimum, and those can be equal. -/
theorem successiveMinimum_le_gauge_of_notMem_span (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    {v : Fin (finrank ℝ E) → E} (hvL : ∀ i, v i ∈ (L : Set E)) (hvind : LinearIndependent ℝ v)
    (hvg : ∀ i, gauge B (v i) = successiveMinimum L B i) :
    ∀ j : ℕ, j ≤ finrank ℝ E → ∀ y ∈ (L : Set E),
      y ∉ Submodule.span ℝ (v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j}) →
        successiveMinimum L B j ≤ gauge B y := by
  have h₀ : B ∈ 𝓝 (0 : E) := hB₀.mem_nhds_zero_of_symmetric hB₁ hB₂
  intro j
  induction j with
  | zero =>
    intro _ y hy hspan
    refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
    have htpos : 0 < t := lt_of_le_of_lt (gauge_nonneg _) ht
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    refine successiveMinimum_le htpos (v := fun _ : Fin (0 + 1) ↦ y)
      (fun _ ↦ ⟨mem_smul_of_gauge_lt hB₀ h₀ ht, hy⟩) ?_
    refine (linearIndependent_subsingleton_index_iff _).2 fun _ ↦ ?_
    intro hy0
    rw [hy0] at hspan
    exact hspan (Submodule.zero_mem _)
  | succ j ih =>
    intro hj y hy hspan
    have hjn : j < finrank ℝ E := hj
    have hprev : successiveMinimum L B j ≤ gauge B y :=
      ih hjn.le y hy fun h ↦
        hspan (Submodule.span_mono (Set.image_mono fun i hi ↦ Nat.lt_succ_of_lt hi) h)
    have hrange : Set.range (v ∘ Fin.castLE hj)
        = v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j + 1} := by
      rw [Set.range_comp, Fin.range_castLE]
    refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
    have htpos : 0 < t := lt_of_le_of_lt (gauge_nonneg _) ht
    refine successiveMinimum_le (i := j + 1) htpos (v := Fin.snoc (v ∘ Fin.castLE hj) y) ?_ ?_
    · refine Fin.lastCases ?_ (fun k ↦ ?_)
      · rw [Fin.snoc_last]
        exact ⟨mem_smul_of_gauge_lt hB₀ h₀ ht, hy⟩
      · rw [Fin.snoc_castSucc]
        refine ⟨mem_smul_of_gauge_lt hB₀ h₀ ?_, hvL _⟩
        calc gauge B ((v ∘ Fin.castLE hj) k) = successiveMinimum L B (k.castLE hj) := hvg _
          _ ≤ successiveMinimum L B j :=
              successiveMinimum_le_of_le (by simpa using Fin.is_le k) hjn hB₀ hB₁ hB₂
          _ ≤ gauge B y := hprev
          _ < t := ht
    · rw [linearIndependent_finSnoc]
      exact ⟨hvind.comp _ fun _ _ h ↦ Fin.castLE_injective hj h, fun hmem ↦ hspan (hrange ▸ hmem)⟩

/-- **Cassels' Lemma 1, completed.** A lattice point of gauge below the `j`-th minimum lies in the
span of the first `j` members of a family realizing the minima. No hypothesis on `j` is needed:
above the dimension the minima vanish and no gauge is negative. This is the input to Cassels'
Lemma 2, `ZLattice.exists_basis_mem_span_int_of_gauge_lt`. -/
theorem mem_span_of_gauge_lt_successiveMinimum (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    {v : Fin (finrank ℝ E) → E} (hvL : ∀ i, v i ∈ (L : Set E)) (hvind : LinearIndependent ℝ v)
    (hvg : ∀ i, gauge B (v i) = successiveMinimum L B i) {y : E} (hy : y ∈ (L : Set E)) {j : ℕ}
    (hgy : gauge B y < successiveMinimum L B j) :
    y ∈ Submodule.span ℝ (v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j}) := by
  by_contra hspan
  rcases le_or_gt (finrank ℝ E) j with hj | hj
  · rw [successiveMinimum_eq_zero_of_le L B hj] at hgy
    exact absurd hgy (not_lt.2 (gauge_nonneg _))
  · exact absurd (successiveMinimum_le_gauge_of_notMem_span L hB₀ hB₁ hB₂ hvL hvind hvg j hj.le y
      hy hspan) (not_le.2 hgy)

end Attainment

/-! ### Minkowski's first theorem as the case `i = 0`

The zeroth minimum is the least dilation of the body containing a nonzero lattice point, which is
the quantity Minkowski's convex-body theorem bounds. The identity is measure-free; the bound is
the only statement in this file that mentions a measure. -/

omit [FiniteDimensional ℝ E] in
/-- The zeroth minimum asks only for a nonzero lattice point: a one-element family is linearly
independent exactly when its member is nonzero. -/
theorem successiveMinimum_zero_eq (L : Submodule ℤ E) (B : Set E) :
    successiveMinimum L B 0 = sInf {t : ℝ | 0 < t ∧ ∃ x ∈ (t • B) ∩ (L : Set E), x ≠ 0} := by
  have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  rw [successiveMinimum]
  congr 1
  ext t
  simp only [mem_ofPred_eq, and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨v, hv, hind⟩
    exact ⟨v 0, hv 0, hind.ne_zero 0⟩
  · rintro ⟨x, hx, hx0⟩
    exact ⟨fun _ ↦ x, fun _ ↦ hx, (linearIndependent_subsingleton_index_iff _).2 fun _ ↦ hx0⟩

/-- **Minkowski's convex-body theorem is the case `i = 0`.** A symmetric convex compact body whose
volume is at least `2 ^ n` times the covolume of the lattice has zeroth minimum at most one. -/
theorem successiveMinimum_zero_le_one [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E)
    [μ.IsAddHaarMeasure] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₅ : IsCompact B)
    (h : 2 ^ finrank ℝ E * covolume L μ ≤ (μ B).toReal) :
    successiveMinimum L B 0 ≤ 1 := by
  classical
  have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  have hcount : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  have hdisc : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  set b := Module.Free.chooseBasis ℤ L
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have fund : IsAddFundamentalDomain L.toAddSubgroup F μ := ZLattice.isAddFundamentalDomain b μ
  have hFfin : μ F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hcov : covolume L μ = (μ F).toReal :=
    covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)
  have key : μ F * 2 ^ finrank ℝ E ≤ μ B := by
    rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hFfin (by finiteness)) hB₅.measure_lt_top.ne,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    rw [hcov] at h
    linarith [h]
  obtain ⟨x, hx0, hxB⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure fund hB₁ hB₀ hB₅ key
  refine successiveMinimum_le one_pos (v := fun _ ↦ (x : E)) (fun _ ↦ ⟨?_, ?_⟩)
    ((linearIndependent_subsingleton_index_iff _).2 fun _ hx ↦ hx0 (Subtype.ext hx))
  · rwa [one_smul]
  · exact x.2

end ZLattice

/-! ### Regrouping a product of minima -/

section Regrouping

/-- **Every `d`-th term, to the power `d`, against the whole product.** For a nonnegative sequence
that is monotone below `N`, the product of `f (d * j) ^ d` over `j < k` is at most the product of
`f i` over `i < d * k`. This is what turns Minkowski's second theorem — a bound on the product of
all `d * k` successive minima — into a bound on a product of `k` heights, each of which costs a
`d`-th power. -/
theorem Finset.prod_pow_le_prod_range {f : ℕ → ℝ} {N : ℕ} (hf0 : ∀ i, 0 ≤ f i)
    (hmono : ∀ i j, i ≤ j → j < N → f i ≤ f j) (d : ℕ) :
    ∀ k, d * k ≤ N → ∏ j ∈ Finset.range k, f (d * j) ^ d ≤ ∏ i ∈ Finset.range (d * k), f i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hle
    have hk : d * k ≤ N := le_trans (Nat.mul_le_mul_left d (Nat.le_succ k)) hle
    have hsplit : d * (k + 1) = d * k + d := by ring
    rw [Finset.prod_range_succ, hsplit, Finset.prod_range_add]
    refine mul_le_mul (ih hk) ?_ (pow_nonneg (hf0 _) _)
      (Finset.prod_nonneg fun i _ ↦ hf0 i)
    calc f (d * k) ^ d = ∏ _i ∈ Finset.range d, f (d * k) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range d, f (d * k + i) := by
          refine Finset.prod_le_prod₀ (fun i _ ↦ hf0 _) fun i hi ↦ ?_
          rw [Finset.mem_range] at hi
          exact hmono _ _ (Nat.le_add_right _ _) (by omega)

end Regrouping

/-! ### Worked examples -/

section Examples

open ZLattice

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E}

/-- The minima are **not** a monotone function of the index: above the dimension the value is the
junk `sInf ∅ = 0`, while below it the value is positive. Any statement about the minima that
ranged over all of `ℕ` — Minkowski's second theorem over `Finset.range` of anything larger than
the dimension, say — is refuted here. -/
example [DiscreteTopology L] [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) (hE : 0 < finrank ℝ E) :
    ¬ Monotone (successiveMinimum L B) := by
  intro hmono
  have h0 : 0 < successiveMinimum L B 0 := successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ hE
  have hn : successiveMinimum L B (finrank ℝ E) = 0 :=
    successiveMinimum_eq_zero_of_le L B le_rfl
  have := hmono (Nat.zero_le (finrank ℝ E))
  rw [hn] at this
  linarith

/-- **The body form of attainment fails for an open body.** For the open unit ball no lattice
vector lies in `λ 0 • B`: anything inside that dilation is inside a strictly smaller one, which
contradicts the definition of the infimum. So `IsClosed B` in
`exists_linearIndependent_mem_smul_successiveMinimum` is not a convenience, and the gauge form of
attainment is the sharp statement. -/
example [Nontrivial E] [DiscreteTopology L] [IsZLattice ℝ L] :
    ¬ ∃ v : Fin (finrank ℝ E) → E, (∀ j, v j ∈ (L : Set E)) ∧ LinearIndependent ℝ v ∧
      ∀ j : Fin (finrank ℝ E), v j ∈ (successiveMinimum L (ball 0 1) j) • ball (0 : E) 1 := by
  have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  have hE : 0 < finrank ℝ E := finrank_pos
  have hB₀ : Convex ℝ (ball (0 : E) 1) := convex_ball 0 1
  have hB₁ : ∀ x ∈ ball (0 : E) 1, -x ∈ ball (0 : E) 1 := by
    intro x hx
    rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
  have hB₂ : (interior (ball (0 : E) 1)).Nonempty := by
    rw [isOpen_ball.interior_eq]
    exact ⟨0, by simp⟩
  have hB₃ : Bornology.IsBounded (ball (0 : E) 1) := Metric.isBounded_ball
  set lam := successiveMinimum L (ball (0 : E) 1) 0 with hlam
  have hpos : 0 < lam := successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ hE
  rintro ⟨v, hvL, hvind, hvmem⟩
  set j : Fin (finrank ℝ E) := ⟨0, hE⟩
  have hx0 : v j ≠ 0 := hvind.ne_zero j
  have hmem : v j ∈ lam • ball (0 : E) 1 := hvmem j
  rw [mem_smul_set_iff_inv_smul_mem₀ hpos.ne', mem_ball_zero_iff, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos hpos, inv_mul_lt_one₀ hpos] at hmem
  set t := (‖v j‖ + lam) / 2 with ht
  have ht0 : 0 < t := by positivity
  have htlt : t < lam := by rw [ht]; linarith
  have hlow : lam ≤ t := by
    refine successiveMinimum_le ht0 (v := fun _ ↦ v j) (fun _ ↦ ⟨?_, ?_⟩)
      ((linearIndependent_subsingleton_index_iff _).2 fun _ ↦ hx0)
    · rw [mem_smul_set_iff_inv_smul_mem₀ ht0.ne', mem_ball_zero_iff, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos ht0, inv_mul_lt_one₀ ht0]
      rw [ht]; linarith
    · exact hvL j
  linarith

end Examples
