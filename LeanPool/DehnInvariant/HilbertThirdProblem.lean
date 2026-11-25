/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.EuclideanSpace
public import LeanPool.DehnInvariant.RationalAngles
public import LeanPool.DehnInvariant.Simplex
public import LeanPool.DehnInvariant.Volume
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Lean study 10 of the shape-language canon (DICTO, 19 Nov 2026), part AE: Hilbert's third problem
as Hilbert
asked it.

Hilbert (1900), problem 3 (on the volumes of two tetrahedra of equal bases and equal altitudes),
asks for
"two tetrahedra of equal bases and equal altitudes which can in no way be split up into congruent
tetrahedra,
and which cannot be combined with congruent tetrahedra to form two polyhedra which themselves
could be split
up into congruent tetrahedra" (D. Hilbert, Mathematische Probleme, Nachr. Ges. Wiss. Göttingen
(1900) 253–297;
English by M. W. Newson, Bull. Amer. Math. Soc. 8 (1902) 437–479). Dehn (Math. Ann. 55 (1901)
465–478) gave
such pairs.

The pair used here is the pair of Aigner and Ziegler, Proofs from THE BOOK, chapter "Hilbert's
third problem:
decomposing polyhedra" (their Examples 2 and 3, the tetrahedra T₁ and T₂, with edge length u = 1),
placed on
one and the same base triangle:
* base `A = (0,0,0)`, `B = (1,0,0)`, `C = (0,1,0)` (in the plane z = 0);
* `cornerTet`, apex `D = (0,0,1)`: three mutually perpendicular edges of length 1 at `A`;
* `orthoTet`, apex `D' = (0,1,1)`: the orthoscheme with the three mutually perpendicular edges
  `B A`, `A C`, `C D'` in a row (one sixth of a unit cube).
Both apexes are at distance 1 from the plane of the base.

* `cornerTet_eq_convexHull`, `orthoTet_eq_convexHull`: the two solids are the convex hulls of
  their corners.
* `hil_height_corner`, `hil_height_ortho`: both altitudes over the common base are 1.
* `volume_cornerTet`, `volume_orthoTet`: both volumes are 1/6.
* `dehnSet_cornerTet`: the Dehn invariant of `cornerTet` is 3√2 ⊗ arccos(1/√3) (three edges of
  length 1 at
  π/2, three edges of length √2 at arccos(1/√3)); `dehnSet_cornerTet_ne_zero`.
* `dehnSet_orthoTet`: the Dehn invariant of `orthoTet` is 0 (its angles are π/2, π/2, π/2, π/4,
  π/4, π/3).
* `EquiComplementable`, `dehnSet_eq_of_equiComplementable`: the second half of Hilbert's wording
  (adding congruent pieces to both solids) also keeps the Dehn invariant.
* `hilbert_third_problem`: **the statement in Hilbert's words.**

The pieces are convex polytopes (tetrahedra are among them) and are moved by isometries,
reflections included;
both make the statement stronger than Hilbert's.

Credits: Dehn (1901); the pair and its angles: Aigner–Ziegler; Mathlib `niven` (through study 1's
`tetDihedral_not_ratPi`: 2 arccos(1/√3) = π − arccos(1/3)), `Real.cos_two_mul`, `Real.arccos_cos`,
`Real.arccos_neg`, `MeasureTheory.volume_sum_rpow_le` (through study 9's `vol_l1_le`),
`Measure.addHaar_preimage_linearMap`, `LinearMap.det_toLin'`, `Matrix.det_fin_three`,
`PiLp.volume_preserving_ofLp`, `Metric.le_infDist`, `Metric.infDist_le_dist_of_mem`,
`affineSpan_le`,
`PiLp.norm_apply_le`, `Set.iUnion_option`, `Fintype.sum_option`; study 2's `dehnSum_eq_of_scissors`,
`dehnSet_image`, `dehn_bridge_R3`; study 4's `IsTetraData.dehnSet_eq`, `IsTetraData.eq_convexHull`,
`theta_pair_of_gram`, `dehnSet_sol_eq_zero_of_rational`, `angle_mem_ratPi_of_gram`; study 9's
`vol_half`,
`vol_eq_of_sub_null`, `plane_null`.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace Real Pointwise
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-! ### Equicomplementable solids -/

section complement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `P` and `Q` are equicomplementable: finitely many convex polytopes `c k` can be added to `P`,
and
congruent copies `g k '' c k` of the same pieces to `Q` (interiors disjoint from each other and
from `P`,
from `Q`), so that the two enlarged solids are scissors congruent. -/
def EquiComplementable (P Q : Set E) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (c : κ → Set E) (g : κ → E ≃ᵃⁱ[ℝ] E),
    (∀ k, IsPoly (c k)) ∧
    (∀ k, Disjoint (interior P) (interior (c k))) ∧
    (Pairwise fun i j => Disjoint (interior (c i)) (interior (c j))) ∧
    (∀ k, Disjoint (interior Q) (interior (g k '' c k))) ∧
    (Pairwise fun i j => Disjoint (interior (g i '' c i)) (interior (g j '' c j))) ∧
    ScissorsCongruent (P ∪ ⋃ k, c k) (Q ∪ ⋃ k, g k '' c k)

/-- **Equicomplementable convex polytopes have the same Dehn invariant.** -/
theorem dehnSet_eq_of_equiComplementable [Fact (finrank ℝ E = 3)] {P Q : Set E} (hP : IsPoly P)
    (hQ : IsPoly Q) (h : EquiComplementable P Q) : dehnSet P = dehnSet Q := by
  obtain ⟨κ, _, c, g, hc, hPc, hcc, hQc, hgg, κ', _, q, f, hq, hU, hdq, hU', hdf⟩ := h
  let p₁ : Option κ → Set E := fun o => o.elim P c
  let p₂ : Option κ → Set E := fun o => o.elim Q (fun k => g k '' c k)
  have hp₁ : ∀ o, IsPoly (p₁ o) := by
    intro o; cases o with
    | none => exact hP
    | some k => exact hc k
  have hp₂ : ∀ o, IsPoly (p₂ o) := by
    intro o; cases o with
    | none => exact hQ
    | some k => exact (hc k).image (g k)
  have hd₁ : Pairwise fun i j => Disjoint (interior (p₁ i)) (interior (p₁ j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact absurd rfl hij
      | some k => exact hPc k
    | some k =>
      cases j with
      | none => exact (hPc k).symm
      | some l => exact hcc (fun hkl => hij (congrArg some hkl))
  have hd₂ : Pairwise fun i j => Disjoint (interior (p₂ i)) (interior (p₂ j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact absurd rfl hij
      | some k => exact hQc k
    | some k =>
      cases j with
      | none => exact (hQc k).symm
      | some l => exact hgg (fun hkl => hij (congrArg some hkl))
  have hU₁ : (⋃ o, p₁ o) = ⋃ k, q k := by rw [Set.iUnion_option, hU]; rfl
  have hU₂ : (⋃ o, p₂ o) = ⋃ k, f k '' q k := by rw [Set.iUnion_option, hU']; rfl
  have hsum := dehnSum_eq_of_scissors hq hdq hdf hp₁ hd₁ hU₁ hp₂ hd₂ hU₂
  rw [Fintype.sum_option, Fintype.sum_option] at hsum
  have h2 : ∑ k, dehnSet (p₂ (some k)) = ∑ k, dehnSet (p₁ (some k)) :=
    Finset.sum_congr rfl fun k _ => dehnSet_image (g k) (c k)
  rw [h2] at hsum
  exact add_right_cancel hsum

end complement

/-! ### The two tetrahedra -/

/-- Corners of the first tetrahedron: the base `A`, `B`, `C` and the apex `D = (0,0,1)`. -/
def hil1P : Fin 4 → R3 := ![!₂[0, 0, 0], !₂[1, 0, 0], !₂[0, 1, 0], !₂[0, 0, 1]]

/-- Corners of the second tetrahedron: the same base and the apex `D' = (0,1,1)`. -/
def hil2P : Fin 4 → R3 := ![!₂[0, 0, 0], !₂[1, 0, 0], !₂[0, 1, 0], !₂[0, 1, 1]]

/-- Outward face normals of the first tetrahedron (face `m` is opposite the corner `m`). -/
def hil1N : Fin 4 → R3 := ![!₂[1, 1, 1], !₂[-1, 0, 0], !₂[0, -1, 0], !₂[0, 0, -1]]

/-- Outward face normals of the second tetrahedron (face `m` is opposite the corner `m`). -/
def hil2N : Fin 4 → R3 := ![!₂[1, 1, 0], !₂[-1, 0, 0], !₂[0, -1, 1], !₂[0, 0, -1]]

/-- Offsets of the faces, the same for both. -/
def hilB : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The first tetrahedron: x, y, z ≥ 0, x + y + z ≤ 1. -/
noncomputable def cornerTet : Set R3 := sol hil1N hilB

/-- The second tetrahedron (an orthoscheme): x ≥ 0, 0 ≤ z ≤ y, x + y ≤ 1. -/
noncomputable def orthoTet : Set R3 := sol hil2N hilB

theorem hil1_isTetraData : IsTetraData hil1N hil1P hilB (fun _ => 1) where
  w_pos := fun _ => one_pos
  delta := by
    intro m k
    fin_cases m <;> fin_cases k <;> simp [hilB, hil1N, hil1P, inner3]
  sum_one := by
    intro x
    simp [Fin.sum_univ_four, hilB, hil1N, inner3]
    ring
  rebuild := by
    intro x
    ext i
    fin_cases i <;> simp [Fin.sum_univ_four, hilB, hil1N, hil1P, inner3]

theorem hil2_isTetraData : IsTetraData hil2N hil2P hilB (fun _ => 1) where
  w_pos := fun _ => one_pos
  delta := by
    intro m k
    fin_cases m <;> fin_cases k <;> simp [hilB, hil2N, hil2P, inner3]
  sum_one := by
    intro x
    simp [Fin.sum_univ_four, hilB, hil2N, inner3]
  rebuild := by
    intro x
    ext i
    fin_cases i <;> simp [Fin.sum_univ_four, hilB, hil2N, hil2P, inner3]

theorem isPoly_cornerTet : IsPoly cornerTet := hil1_isTetraData.isPoly

theorem isPoly_orthoTet : IsPoly orthoTet := hil2_isTetraData.isPoly

lemma range_four {α : Type*} (a b c d : α) : Set.range ![a, b, c, d] = {a, b, c, d} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h | h | ⟨i, -⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr h.symm))
    · exact i.elim0
  · rintro (h | h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))

/-- The first tetrahedron is the convex hull of `A`, `B`, `C`, `D`. -/
theorem cornerTet_eq_convexHull :
    cornerTet = convexHull ℝ {hil1P 0, hil1P 1, hil1P 2, hil1P 3} := by
  rw [← range_four]
  have h : ![hil1P 0, hil1P 1, hil1P 2, hil1P 3] = hil1P := by
    funext i; fin_cases i <;> rfl
  rw [h]
  exact hil1_isTetraData.eq_convexHull

/-- The second tetrahedron is the convex hull of `A`, `B`, `C`, `D'`. -/
theorem orthoTet_eq_convexHull :
    orthoTet = convexHull ℝ {hil1P 0, hil1P 1, hil1P 2, hil2P 3} := by
  rw [← range_four]
  have h : ![hil1P 0, hil1P 1, hil1P 2, hil2P 3] = hil2P := by
    funext i; fin_cases i <;> rfl
  rw [h]
  exact hil2_isTetraData.eq_convexHull

/-! ### Equal altitudes over the common base -/

/-- Every point of the plane through the base `A`, `B`, `C` has third coordinate 0. -/
lemma hil_base_plane {y : R3} (hy : y ∈ affineSpan ℝ ({hil1P 0, hil1P 1, hil1P 2} : Set R3)) :
    y 2 = 0 := by
  let Q : AffineSubspace ℝ R3 := ((ℝ ∙ (!₂[0, 0, 1] : R3))ᗮ).toAffineSubspace
  have hmem : ∀ z : R3, z ∈ Q ↔ z 2 = 0 := by
    intro z
    change z ∈ ((ℝ ∙ (!₂[0, 0, 1] : R3))ᗮ) ↔ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner3]
    simp
  have hsub : ({hil1P 0, hil1P 1, hil1P 2} : Set R3) ⊆ Q := by
    rintro z (rfl | rfl | rfl) <;> exact (hmem _).2 (by simp [hil1P])
  exact (hmem y).1 (affineSpan_le.2 hsub hy)

lemma one_le_dist_of_coord {x y : R3} (hx : x 2 = 1) (hy : y 2 = 0) : 1 ≤ dist x y := by
  rw [dist_eq_norm]
  have h := PiLp.norm_apply_le (x - y) 2
  have h2 : (x - y) 2 = 1 := by
    change x 2 - y 2 = 1
    rw [hx, hy, sub_zero]
  rw [h2, norm_one] at h
  exact h

/-- **The altitude of the first tetrahedron** over the base `A B C` is 1. -/
theorem hil_height_corner :
    Metric.infDist (hil1P 3) (affineSpan ℝ ({hil1P 0, hil1P 1, hil1P 2} : Set R3) : Set R3)
        = 1 := by
  have hA : hil1P 0 ∈ (affineSpan ℝ ({hil1P 0, hil1P 1, hil1P 2} : Set R3) : Set R3) :=
    subset_affineSpan ℝ _ (mem_insert _ _)
  apply le_antisymm
  · refine (Metric.infDist_le_dist_of_mem hA).trans (le_of_eq ?_)
    apply dist3 _ _ zero_le_one
    simp [hil1P]
  · exact (Metric.le_infDist ⟨_, hA⟩).2 fun y hy =>
      one_le_dist_of_coord (by simp [hil1P]) (hil_base_plane hy)

/-- **The altitude of the second tetrahedron** over the same base `A B C` is 1. -/
theorem hil_height_ortho :
    Metric.infDist (hil2P 3) (affineSpan ℝ ({hil1P 0, hil1P 1, hil1P 2} : Set R3) : Set R3)
        = 1 := by
  have hA : hil1P 0 ∈ (affineSpan ℝ ({hil1P 0, hil1P 1, hil1P 2} : Set R3) : Set R3) :=
    subset_affineSpan ℝ _ (mem_insert _ _)
  have hC : hil1P 2 ∈ (affineSpan ℝ ({hil1P 0, hil1P 1, hil1P 2} : Set R3) : Set R3) :=
    subset_affineSpan ℝ _ (mem_insert_of_mem _ (mem_insert_of_mem _ rfl))
  apply le_antisymm
  · refine (Metric.infDist_le_dist_of_mem hC).trans (le_of_eq ?_)
    apply dist3 _ _ zero_le_one
    simp [hil1P, hil2P]
  · exact (Metric.le_infDist ⟨_, hA⟩).2 fun y hy =>
      one_le_dist_of_coord (by simp [hil2P]) (hil_base_plane hy)

/-! ### Equal volumes -/

/-- The first tetrahedron in coordinates. -/
def hilCornerF : Set (Fin 3 → ℝ) := {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ 0 ≤ u 2 ∧ u 0 + u 1 + u 2 ≤ 1}

/-- The second tetrahedron in coordinates. -/
def hilOrthoF : Set (Fin 3 → ℝ) := {u | 0 ≤ u 0 ∧ 0 ≤ u 2 ∧ u 2 ≤ u 1 ∧ u 0 + u 1 ≤ 1}

lemma cornerTet_eq : cornerTet = WithLp.ofLp ⁻¹' hilCornerF := by
  ext x
  constructor
  · intro hx
    have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
    norm_num [hil1N, hilB, inner3] at h0 h1 h2 h3
    exact ⟨h1, h2, h3, h0⟩
  · rintro ⟨h1, h2, h3, h0⟩
    have h1' : 0 ≤ x 0 := h1
    have h2' : 0 ≤ x 1 := h2
    have h3' : 0 ≤ x 2 := h3
    have h0' : x 0 + x 1 + x 2 ≤ 1 := h0
    intro m
    fin_cases m <;> simp [hil1N, hilB, inner3] <;> linarith

lemma orthoTet_eq : orthoTet = WithLp.ofLp ⁻¹' hilOrthoF := by
  ext x
  constructor
  · intro hx
    have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
    norm_num [hil2N, hilB, inner3] at h0 h1 h2 h3
    exact ⟨h1, h3, by linarith, h0⟩
  · rintro ⟨h1, h3, h2, h0⟩
    have h1' : 0 ≤ x 0 := h1
    have h3' : 0 ≤ x 2 := h3
    have h2' : x 2 ≤ x 1 := h2
    have h0' : x 0 + x 1 ≤ 1 := h0
    intro m
    fin_cases m <;> simp [hil2N, hilB, inner3] <;> linarith

/-- The corner simplex {u ≥ 0, u₀ + u₁ + u₂ ≤ 1} has volume 1/6 (study 9's method: three halvings
of the
ball of the sum norm). -/
lemma volume_hilCornerF : volume hilCornerF = ENNReal.ofReal (1 / 6) := by
  set S0 := {y : Fin 3 → ℝ | l1 y ≤ 1}
  set S1 := S0 ∩ {y | 0 < y 0}
  set S2 := S1 ∩ {y | 0 < y 1}
  set S3 := S2 ∩ {y | 0 < y 2}
  have m0 : MeasurableSet S0 := measurableSet_le continuous_l1.measurable measurable_const
  have mi : ∀ i : Fin 3, MeasurableSet {y : Fin 3 → ℝ | 0 < y i} := fun i =>
    measurableSet_lt measurable_const (measurable_pi_apply i)
  have m1 : MeasurableSet S1 := m0.inter (mi 0)
  have m2 : MeasurableSet S2 := m1.inter (mi 1)
  have e1 := vol_half 0 m0 (fun y => by simp [S0, l1_refl])
  have e2 := vol_half 1 m1 (fun y => by
    simp only [S1, S0, mem_inter_iff, mem_ofPred_eq, l1_refl, refl_apply_ne (by decide : (0 : Fin
        3) ≠ 1)])
  have e3 := vol_half 2 m2 (fun y => by
    simp only [S2, S1, S0, mem_inter_iff, mem_ofPred_eq, l1_refl,
      refl_apply_ne (by decide : (0 : Fin 3) ≠ 2), refl_apply_ne (by decide : (1 : Fin 3) ≠ 2)])
  have hS0 : volume S0 = ENNReal.ofReal (4 / 3) := by
    rw [vol_l1_le zero_le_one]; norm_num
  have h3 : volume S3 = ENNReal.ofReal (1 / 6) := by
    rw [hS0] at e1
    have v1 := ennreal_half (show 2 * volume S1 = ENNReal.ofReal (2 * (2 / 3)) by
      rw [e1]; norm_num)
    rw [v1] at e2
    have v2 := ennreal_half (show 2 * volume S2 = ENNReal.ofReal (2 * (1 / 3)) by
      rw [e2]; norm_num)
    rw [v2] at e3
    exact ennreal_half (show 2 * volume S3 = ENNReal.ofReal (2 * (1 / 6)) by
      rw [e3]; norm_num)
  rw [← h3]
  symm
  apply vol_eq_of_sub_null (z := {y | y 0 = 0} ∪ {y | y 1 = 0} ∪ {y | y 2 = 0})
  · rintro y ⟨⟨⟨h0, ha⟩, hb⟩, hc⟩
    simp only [S0, l1, mem_ofPred_eq] at h0 ha hb hc
    rw [abs_of_pos ha, abs_of_pos hb, abs_of_pos hc] at h0
    exact ⟨ha.le, hb.le, hc.le, h0⟩
  · rintro y ⟨ha, hb, hc, hs⟩
    by_cases h0 : y 0 = 0
    · exact Or.inr (Or.inl (Or.inl h0))
    by_cases h1 : y 1 = 0
    · exact Or.inr (Or.inl (Or.inr h1))
    by_cases h2 : y 2 = 0
    · exact Or.inr (Or.inr h2)
    have ha' := lt_of_le_of_ne ha (Ne.symm h0)
    have hb' := lt_of_le_of_ne hb (Ne.symm h1)
    have hc' := lt_of_le_of_ne hc (Ne.symm h2)
    refine Or.inl ⟨⟨⟨?_, ha'⟩, hb'⟩, hc'⟩
    simp only [S0, l1, mem_ofPred_eq]
    rw [abs_of_pos ha', abs_of_pos hb', abs_of_pos hc']; exact hs
  · exact measure_union_null (measure_union_null (plane_null 0 0) (plane_null 1 0)) (plane_null 2 0)

/-- The shear (u₀, u₁, u₂) ↦ (u₀, u₁ + u₂, u₂), as a matrix of determinant 1. -/
def shearM : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

/-- The shear carries the first tetrahedron onto the second and keeps volume (Cavalieri's
principle in this
one case). -/
lemma volume_hilOrthoF : volume hilOrthoF = ENNReal.ofReal (1 / 6) := by
  have hdet : LinearMap.det (Matrix.toLin' shearM) = 1 := by
    rw [LinearMap.det_toLin', shearM, Matrix.det_fin_three]; simp
  have hpre : (Matrix.toLin' shearM) ⁻¹' hilOrthoF = hilCornerF := by
    ext u
    have e0 : (Matrix.toLin' shearM u) 0 = u 0 := by
      simp [shearM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have e1 : (Matrix.toLin' shearM u) 1 = u 1 + u 2 := by
      simp [shearM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have e2 : (Matrix.toLin' shearM u) 2 = u 2 := by
      simp [shearM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    change (0 ≤ (Matrix.toLin' shearM u) 0 ∧ 0 ≤ (Matrix.toLin' shearM u) 2 ∧
      (Matrix.toLin' shearM u) 2 ≤ (Matrix.toLin' shearM u) 1 ∧
      (Matrix.toLin' shearM u) 0 + (Matrix.toLin' shearM u) 1 ≤ 1) ↔
      (0 ≤ u 0 ∧ 0 ≤ u 1 ∧ 0 ≤ u 2 ∧ u 0 + u 1 + u 2 ≤ 1)
    rw [e0, e1, e2]
    constructor
    · rintro ⟨a, b, c, d⟩; exact ⟨a, by linarith, b, by linarith⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨a, c, by linarith, by linarith⟩
  have h := Measure.addHaar_preimage_linearMap (volume : Measure (Fin 3 → ℝ))
    (f := Matrix.toLin' shearM) (by rw [hdet]; exact one_ne_zero) hilOrthoF
  rw [hpre, hdet, inv_one, abs_one, ENNReal.ofReal_one, one_mul, volume_hilCornerF] at h
  exact h.symm

lemma measurableSet_hilCornerF : MeasurableSet hilCornerF :=
  (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    ((measurableSet_le measurable_const (measurable_pi_apply 1)).inter
      ((measurableSet_le measurable_const (measurable_pi_apply 2)).inter
        (measurableSet_le (((measurable_pi_apply 0).add (measurable_pi_apply 1)).add
          (measurable_pi_apply 2)) measurable_const)))

lemma measurableSet_hilOrthoF : MeasurableSet hilOrthoF :=
  (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    ((measurableSet_le measurable_const (measurable_pi_apply 2)).inter
      ((measurableSet_le (measurable_pi_apply 2) (measurable_pi_apply 1)).inter
        (measurableSet_le ((measurable_pi_apply 0).add (measurable_pi_apply 1)) measurable_const)))

/-- **The first tetrahedron has volume 1/6.** -/
theorem volume_cornerTet : volume cornerTet = ENNReal.ofReal (1 / 6) := by
  rw [cornerTet_eq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    measurableSet_hilCornerF.nullMeasurableSet, volume_hilCornerF]

/-- **The second tetrahedron has volume 1/6.** -/
theorem volume_orthoTet : volume orthoTet = ENNReal.ofReal (1 / 6) := by
  rw [orthoTet_eq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    measurableSet_hilOrthoF.nullMeasurableSet, volume_hilOrthoF]

/-! ### The Dehn invariant of the first tetrahedron -/

lemma hil1N_inner_side (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) :
    ⟪hil1N i, hil1N j⟫ = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hil1N, inner3, norm3_sq] at hi hj ⊢

lemma hil1N_inner_base (i : Fin 4) (hi : i ≠ 0) :
    ⟪hil1N 0, hil1N 0⟫ = 3 ∧ ⟪hil1N 0, hil1N i⟫ = -1 := by
  fin_cases i <;> simp [hil1N, inner3, norm3_sq] at hi ⊢ <;> norm_num

/-- Where two of the three coordinate faces meet, the angle is π/2: class 0. -/
lemma hil1_theta_right {A : Set (Fin 4)} {i j : Fin 4} (hA : A = {i, j}) (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i ≠ j) : theta (cone hil1N A) = 0 := by
  rw [theta_pair_of_gram hil1N hA one_pos (Y := 1) (d := 0)
    (by rw [hil1N_inner_side i i hi hi, ite_eq_left rfl])
    (by rw [hil1N_inner_side j j hj hj, ite_eq_left rfl])
    (by rw [hil1N_inner_side i j hi hj, ite_eq_right hij, neg_zero]) (by norm_num),
    zero_div, Real.arccos_zero, Submodule.Quotient.mk_eq_zero, mem_ratPi_iff]
  exact ⟨1 / 2, by push_cast; ring⟩

/-- Where the slanted face meets a coordinate face, the angle is arccos(1/√3). -/
lemma hil1_theta_slant {A : Set (Fin 4)} {i : Fin 4} (hA : A = {0, i}) (hi : i ≠ 0) :
    theta (cone hil1N A) = (Submodule.Quotient.mk (Real.arccos (1 / √3)) : Angle) := by
  rw [theta_pair_of_gram hil1N hA (by norm_num : (0 : ℝ) < 3) (hil1N_inner_base i hi).1
    (by rw [hil1N_inner_side i i hi hi, ite_eq_left rfl]) (hil1N_inner_base i hi).2 (by norm_num),
        mul_one]

lemma hil1_dist (k l : Fin 4) (hk : k ≠ 0) (hl : l ≠ 0) (hkl : k ≠ l) :
    dist (hil1P k) (hil1P l) = √2 := by
  apply dist3 _ _ (Real.sqrt_nonneg 2)
  rw [Real.sq_sqrt (by norm_num)]
  fin_cases k <;> fin_cases l <;> simp [hil1P] at hk hl hkl ⊢ <;> norm_num

/-- **The Dehn invariant of the first tetrahedron**: 3√2 ⊗ arccos(1/√3). The three edges at the
right-angled
corner carry π/2 and drop out; the three edges of the slanted face have length √2 and angle
arccos(1/√3). -/
theorem dehnSet_cornerTet : dehnSet cornerTet = edgeTerm (3 * √2) (Real.arccos (1 / √3)) := by
  unfold cornerTet
  rw [hil1_isTetraData.dehnSet_eq, sum_tetPairs]
  simp only []
  rw [hil1_theta_right (i := 2) (j := 3) (compl_pair_eq (by decide)) (by decide) (by decide)
      (by decide),
    hil1_theta_right (i := 1) (j := 3) (compl_pair_eq (by decide)) (by decide) (by decide)
        (by decide),
    hil1_theta_right (i := 1) (j := 2) (compl_pair_eq (by decide)) (by decide) (by decide)
        (by decide),
    hil1_theta_slant (i := 3) (compl_pair_eq (by decide)) (by decide),
    hil1_theta_slant (i := 2) (compl_pair_eq (by decide)) (by decide),
    hil1_theta_slant (i := 1) (compl_pair_eq (by decide)) (by decide),
    hil1_dist 1 2 (by decide) (by decide) (by decide),
    hil1_dist 1 3 (by decide) (by decide) (by decide),
    hil1_dist 2 3 (by decide) (by decide) (by decide)]
  simp only [TensorProduct.tmul_zero, zero_add]
  unfold edgeTerm
  rw [show (3 : ℝ) * √2 = √2 + √2 + √2 by ring, TensorProduct.add_tmul, TensorProduct.add_tmul]

/-- 2 arccos(1/√3) = π − arccos(1/3): the angle of the corner tetrahedron and the angle of the
regular
tetrahedron. -/
lemma arccos_inv_sqrt_three : Real.arccos (1 / √3) = (π - tetDihedral) / 2 := by
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  have hle : (1 : ℝ) / √3 ≤ 1 := by rw [div_le_one hpos]; nlinarith
  have hge : (0 : ℝ) ≤ 1 / √3 := by positivity
  have hc : Real.cos (Real.arccos (1 / √3)) = 1 / √3 := Real.cos_arccos (by linarith) hle
  have h0 : 0 ≤ Real.arccos (1 / √3) := Real.arccos_nonneg _
  have h1 : Real.arccos (1 / √3) ≤ π / 2 := Real.arccos_le_pi_div_two.2 hge
  have h2 : Real.cos (2 * Real.arccos (1 / √3)) = -(1 / 3) := by
    rw [Real.cos_two_mul, hc, div_pow, h3]; norm_num
  have h4 : Real.arccos (Real.cos (2 * Real.arccos (1 / √3))) = 2 * Real.arccos (1 / √3) :=
    Real.arccos_cos (by linarith) (by linarith)
  rw [h2, Real.arccos_neg] at h4
  unfold tetDihedral
  linarith

/-- **arccos(1/√3) is not a rational multiple of π** (Niven's theorem, through the regular
tetrahedron's
angle). -/
theorem arccos_inv_sqrt_three_not_ratPi : Real.arccos (1 / √3) ∉ ratPi := by
  intro h
  apply tetDihedral_not_ratPi
  have e : tetDihedral = π - (2 : ℚ) • Real.arccos (1 / √3) := by
    rw [arccos_inv_sqrt_three, Rat.smul_def]; push_cast; ring
  rw [e]
  exact ratPi.sub_mem pi_mem_ratPi (ratPi.smul_mem 2 h)

/-- **The first tetrahedron has a nonzero Dehn invariant.** -/
theorem dehnSet_cornerTet_ne_zero : dehnSet cornerTet ≠ 0 := by
  rw [dehnSet_cornerTet]
  refine edgeTerm_ne_zero ?_ arccos_inv_sqrt_three_not_ratPi
  have : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  positivity

/-! ### The Dehn invariant of the second tetrahedron -/

/-- The Gram numbers of the four normals of the second tetrahedron. -/
def hil2G : Fin 4 → Fin 4 → ℤ := ![![2, -1, -1, 0], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![0, 0, -1, 1]]

lemma hil2N_inner (i j : Fin 4) : ⟪hil2N i, hil2N j⟫ = (hil2G i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [hil2N, hil2G, inner3, norm3_sq] <;> norm_num

lemma hil2G_table : ∀ i j : Fin 4, ∃ k : Fin 5, 4 * hil2G i j ^ 2 = (k : ℤ)
    * (hil2G i i * hil2G j j) := by
  decide

lemma hil2N_ne_zero (i : Fin 4) : hil2N i ≠ 0 := by
  intro h
  have h1 := hil2N_inner i i
  rw [h, inner_zero_left] at h1
  have h2 : hil2G i i ≠ 0 := by fin_cases i <;> decide
  exact h2 (by exact_mod_cast h1.symm)

/-- Any two of the four normals make an angle that is a rational multiple of π (the six interior
angles are
π/2, π/2, π/2, π/4, π/4, π/3). -/
lemma hil2N_angle (i j : Fin 4) : InnerProductGeometry.angle (hil2N i) (hil2N j) ∈ ratPi := by
  obtain ⟨k, hk⟩ := hil2G_table i j
  apply angle_mem_ratPi_of_gram (hil2N_ne_zero i) (hil2N_ne_zero j) (k := (k : ℕ)) (by omega)
  rw [hil2N_inner, hil2N_inner, hil2N_inner]
  exact_mod_cast hk

/-- **The second tetrahedron has Dehn invariant zero.** -/
theorem dehnSet_orthoTet : dehnSet orthoTet = 0 :=
  dehnSet_sol_eq_zero_of_rational hil2N hilB hil2N_ne_zero hil2N_angle

/-! ### Hilbert's statement -/

/-- The two tetrahedra are not scissors congruent. -/
theorem cornerTet_not_scissorsCongruent_orthoTet : ¬ ScissorsCongruent cornerTet orthoTet := by
  intro h
  apply dehnSet_cornerTet_ne_zero
  rw [dehn_bridge_R3 isPoly_cornerTet isPoly_orthoTet h, dehnSet_orthoTet]

/-- The two tetrahedra are not equicomplementable. -/
theorem cornerTet_not_equiComplementable_orthoTet : ¬ EquiComplementable cornerTet orthoTet := by
  intro h
  apply dehnSet_cornerTet_ne_zero
  rw [dehnSet_eq_of_equiComplementable isPoly_cornerTet isPoly_orthoTet h, dehnSet_orthoTet]

/-- **Hilbert's third problem, in Hilbert's words.** "Two tetrahedra of equal bases and equal
altitudes which
can in no way be split up into congruent tetrahedra, and which cannot be combined with congruent
tetrahedra to
form two polyhedra which themselves could be split up into congruent tetrahedra" (Hilbert 1900,
problem 3;
English by Newson 1902). Solved by Dehn (1901).

There are two tetrahedra `A B C D` and `A B C D'` on one and the same base triangle `A B C`, with
the same
altitude 1 over it (hence the same volume, 1/6), which are not scissors congruent and not
equicomplementable.
Here the pieces may be any convex polytopes, and they are moved by any isometries.
The pair: `A = (0,0,0)`, `B = (1,0,0)`, `C = (0,1,0)`, `D = (0,0,1)`, `D' = (0,1,1)`
(Aigner–Ziegler,
Proofs from THE BOOK, the tetrahedra T₁ and T₂ of the chapter on Hilbert's third problem). -/
theorem hilbert_third_problem :
    ∃ A B C D D' : R3,
      Metric.infDist D (affineSpan ℝ ({A, B, C} : Set R3) : Set R3) = 1 ∧
      Metric.infDist D' (affineSpan ℝ ({A, B, C} : Set R3) : Set R3) = 1 ∧
      volume (convexHull ℝ ({A, B, C, D} : Set R3)) = ENNReal.ofReal (1 / 6) ∧
      volume (convexHull ℝ ({A, B, C, D'} : Set R3)) = ENNReal.ofReal (1 / 6) ∧
      ¬ ScissorsCongruent (convexHull ℝ ({A, B, C, D} : Set R3)) (convexHull ℝ ({A, B, C,
          D'} : Set R3)) ∧
      ¬ EquiComplementable (convexHull ℝ ({A, B, C, D} : Set R3))
        (convexHull ℝ ({A, B, C, D'} : Set R3)) := by
  refine ⟨hil1P 0, hil1P 1, hil1P 2, hil1P 3, hil2P 3, hil_height_corner, hil_height_ortho, ?_,
      ?_, ?_, ?_⟩
  · rw [← cornerTet_eq_convexHull]; exact volume_cornerTet
  · rw [← orthoTet_eq_convexHull]; exact volume_orthoTet
  · rw [← cornerTet_eq_convexHull, ← orthoTet_eq_convexHull]
    exact cornerTet_not_scissorsCongruent_orthoTet
  · rw [← cornerTet_eq_convexHull, ← orthoTet_eq_convexHull]
    exact cornerTet_not_equiComplementable_orthoTet

end DehnCanon.Library
