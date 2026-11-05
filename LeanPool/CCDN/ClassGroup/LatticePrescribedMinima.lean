/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Module.ZLattice.Basic
import LeanPool.CCDN.ForMathlib.ZLattice

/-! A lattice basis with a prescribed nonzero first vector. Every later
vector is shortest outside the previous span. A given global
lower bound replaces the first vector's norm in the monotone thresholds. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A prescribed greedy lattice family: linearly independent vectors `v` of the lattice `L` with
first vector `v 0 = w`, each later vector `v i` being a shortest vector of `L` outside the real
span of the preceding vectors. -/
def IsPrescribedGreedyLatticeFamily (L : Submodule ℤ E) (w : E)
    {k : ℕ} (v : Fin (k + 1) → E) : Prop :=
  LinearIndependent ℝ v ∧ v 0 = w ∧ (∀ i, v i ∈ L) ∧
    ∀ i, i ≠ 0 → ∀ x, x ∈ L → x ∉ span ℝ (v '' Set.Iio i) → ‖v i‖ ≤ ‖x‖

section Projections

omit [FiniteDimensional ℝ E]

variable {L : Submodule ℤ E} {w : E} {k : ℕ} {v : Fin (k + 1) → E}

/-- The vectors of a prescribed greedy family are linearly independent. -/
private theorem IsPrescribedGreedyLatticeFamily.linearIndependent
    (hv : IsPrescribedGreedyLatticeFamily L w v) : LinearIndependent ℝ v := hv.1

/-- The first vector of a prescribed greedy family is the prescribed vector. -/
theorem IsPrescribedGreedyLatticeFamily.first_eq
    (hv : IsPrescribedGreedyLatticeFamily L w v) : v 0 = w := hv.2.1

/-- The vectors of a prescribed greedy family lie in the lattice. -/
theorem IsPrescribedGreedyLatticeFamily.mem
    (hv : IsPrescribedGreedyLatticeFamily L w v) (i : Fin (k + 1)) : v i ∈ L := hv.2.2.1 i

/-- Every later vector of a prescribed greedy family is a shortest lattice vector outside the
span of the preceding ones. -/
theorem IsPrescribedGreedyLatticeFamily.norm_le
    (hv : IsPrescribedGreedyLatticeFamily L w v) {i : Fin (k + 1)} (hi : i ≠ 0) {x : E}
    (hx : x ∈ L) (hxU : x ∉ span ℝ (v '' Set.Iio i)) : ‖v i‖ ≤ ‖x‖ :=
  hv.2.2.2 i hi x hx hxU

end Projections

omit [FiniteDimensional ℝ E] in
private theorem IsPrescribedGreedyLatticeFamily.snoc
    {L : Submodule ℤ E} {w : E} {k : ℕ} {v : Fin (k + 1) → E}
    (hv : IsPrescribedGreedyLatticeFamily L w v) {x : E} (hx : x ∈ L)
    (hxU : x ∉ span ℝ (Set.range v))
    (hmin : ∀ y, y ∈ L → y ∉ span ℝ (Set.range v) → ‖x‖ ≤ ‖y‖) :
    IsPrescribedGreedyLatticeFamily L w (Fin.snoc v x) := by
  refine ⟨hv.linearIndependent.finSnoc hxU, ?_, ?_, ?_⟩
  · simpa using hv.first_eq
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa using hv.mem j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro _
      simpa only [Fin.snoc_last, Fin.snoc_image_Iio_last] using hmin
    · intro hj
      have hj0 : j ≠ 0 := by intro hz; apply hj; simp [hz]
      simpa only [Fin.snoc_castSucc, Fin.snoc_image_Iio_castSucc] using
        fun x hx hxU => hv.norm_le hj0 hx hxU

/-- Prescribed-first greedy independent lattice vectors of every possible
length. -/
private theorem exists_prescribed_greedy_lattice_family
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : E) (hw : w ∈ L) (hw0 : w ≠ 0)
    (k : ℕ) (hk : k + 1 ≤ Module.finrank ℝ E) :
    ∃ v : Fin (k + 1) → E, IsPrescribedGreedyLatticeFamily L w v := by
  induction k with
  | zero =>
    let : Subsingleton (Fin (0 + 1)) := Fin.subsingleton_iff_le_one.mpr (by omega)
    refine ⟨fun _ => w, (linearIndependent_subsingleton_index_iff _).mpr (fun _ => hw0), rfl,
      fun _ => hw, ?_⟩
    intro i hi
    exact False.elim (hi (Subsingleton.elim _ _))
  | succ k ih =>
    obtain ⟨v, hv⟩ := ih (by omega)
    have hU : span ℝ (Set.range v) ≠ ⊤ := by
      intro he
      have hdim := finrank_span_eq_card hv.linearIndependent
      rw [he, finrank_top, Fintype.card_fin] at hdim
      omega
    obtain ⟨x, hx, hxU, hmin⟩ := ZLattice.exists_shortest_vector_notMem L _ hU
    exact ⟨Fin.snoc v x, hv.snoc hx hxU hmin⟩

/-- Every nonzero vector `w` of a full lattice `L` in a real space of dimension `n + 1` is the first
vector of a basis `b` of lattice vectors that forms a prescribed greedy lattice family. -/
theorem exists_prescribed_greedy_lattice_basis
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : E) (hw : w ∈ L) (hw0 : w ≠ 0)
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1) :
    ∃ b : Basis (Fin (n + 1)) ℝ E, IsPrescribedGreedyLatticeFamily L w b := by
  obtain ⟨v, hv⟩ := exists_prescribed_greedy_lattice_family L w hw hw0 n (by omega)
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv.linearIndependent (by simpa using hn.symm)
  exact ⟨b, by simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv⟩

omit [FiniteDimensional ℝ E] in
/-- The successive thresholds of a prescribed greedy family `v`: the first is the given lower bound
`δ`, and the `i`-th for `i ≠ 0` is the norm `‖v i‖`. -/
def prescribedLatticeMinima {n : ℕ} (v : Fin (n + 1) → E) (δ : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then δ else ‖v i‖

omit [FiniteDimensional ℝ E] in
/-- For a positive lower bound `δ`, all thresholds `prescribedLatticeMinima v δ` of a prescribed
greedy lattice family are positive. -/
theorem IsPrescribedGreedyLatticeFamily.minima_pos
    {L : Submodule ℤ E} {w : E} {n : ℕ} {v : Fin (n + 1) → E}
    (hv : IsPrescribedGreedyLatticeFamily L w v) {δ : ℝ} (hδ : 0 < δ) :
    ∀ i, 0 < prescribedLatticeMinima v δ i := by
  intro i
  unfold prescribedLatticeMinima
  split_ifs
  · exact hδ
  · exact norm_pos_iff.mpr (hv.linearIndependent.ne_zero i)

omit [FiniteDimensional ℝ E] in
/-- If `δ` is a lower bound for the norms of nonzero lattice vectors, then the thresholds
`prescribedLatticeMinima v δ` of a prescribed greedy lattice family are monotone. -/
theorem IsPrescribedGreedyLatticeFamily.minima_mono
    {L : Submodule ℤ E} {w : E} {n : ℕ} {v : Fin (n + 1) → E}
    (hv : IsPrescribedGreedyLatticeFamily L w v) {δ : ℝ}
    (hlower : ∀ x, x ∈ L → x ≠ 0 → δ ≤ ‖x‖) :
    Monotone (prescribedLatticeMinima v δ) := by
  intro i j hij
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · simp [prescribedLatticeMinima, hi, hj]
    · simpa [prescribedLatticeMinima, hi, hj] using
        hlower (v j) (hv.mem j) (hv.linearIndependent.ne_zero j)
  · have hj : j ≠ 0 := by intro hz; apply hi; exact le_antisymm (hz ▸ hij) (Fin.zero_le i)
    simp only [prescribedLatticeMinima, ite_eq_right hi, ite_eq_right hj]
    exact hv.norm_le hi (hv.mem j) (hv.linearIndependent.notMem_span_image (not_lt_of_ge hij))

omit [FiniteDimensional ℝ E] in
/-- If `δ` is a lower bound for the norms of nonzero lattice vectors, then every lattice vector
outside the span of the vectors of index `< i` of a prescribed greedy lattice family has norm at
least the `i`-th threshold `prescribedLatticeMinima v δ i`. -/
theorem IsPrescribedGreedyLatticeFamily.minima_outside
    {L : Submodule ℤ E} {w : E} {n : ℕ} {v : Fin (n + 1) → E}
    (hv : IsPrescribedGreedyLatticeFamily L w v) {δ : ℝ}
    (hlower : ∀ x, x ∈ L → x ≠ 0 → δ ≤ ‖x‖) :
    ∀ i x, x ∈ L → x ∉ span ℝ (v '' Set.Iio i) → prescribedLatticeMinima v δ i ≤ ‖x‖ := by
  intro i x hx hxU
  by_cases hi : i = 0
  · rw [prescribedLatticeMinima, ite_eq_left hi]
    apply hlower x hx
    intro hz
    exact hxU (hz ▸ Submodule.zero_mem _)
  · rw [prescribedLatticeMinima, ite_eq_right hi]
    exact hv.norm_le hi hx hxU

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
/-- The product of the norms `‖v i‖` equals `‖w‖ / δ` times the product of the thresholds
`prescribedLatticeMinima v δ i`, where `v 0 = w` and `δ ≠ 0`. -/
theorem prescribedLatticeMinima_prod {n : ℕ} (v : Fin (n + 1) → E)
    {w : E} (hw : v 0 = w) {δ : ℝ} (hδ : δ ≠ 0) :
    (∏ i, ‖v i‖) = (‖w‖ / δ) * ∏ i, prescribedLatticeMinima v δ i := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [prescribedLatticeMinima, Fin.succ_ne_zero, ↓reduceIte, hw]
  rw [← mul_assoc, div_mul_cancel₀ _ hδ]

end
end CCDN
