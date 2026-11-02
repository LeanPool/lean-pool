/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Countably many classes of unit vectors (Proposition C)

The unit vectors of a real Hilbert space fall into countably many classes such that any
two vectors `x, y` of one class satisfy `1 + ⟪x, y⟫ ≥ η > 0` for a constant `η` of the
class. Choose a Hilbert basis. For rationals `0 < b < a`, a unit vector whose coordinates
of magnitude at least `a` form a nonempty set `S`, all others having magnitude at most
`b`, is classified by `(a, b)` and the sign of its coordinate at an element of `S` chosen
by `Classical.epsilon`, a choice that depends only on `S`. Two vectors of one class differ
in their supports, giving `‖x + y‖ ≥ a - b`, or share the sign of a coordinate of
magnitude at least `a`, giving `‖x + y‖ ≥ 2a`.

Applied to the signs `±1` of a law in `L²`, this gives countably many classes of vertices
within which any two signs agree with probability bounded below.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace Erdos111

/-- A vector whose coordinates in a Hilbert basis all vanish is zero. -/
theorem eq_zero_of_forall_inner_hilbertBasis_eq_zero {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : HilbertBasis ι ℝ E) {x : E}
    (h : ∀ i, ⟪b i, x⟫ = 0) : x = 0 := by
  have hx := b.hasSum_repr x
  simp only [b.repr_apply_apply, h, zero_smul] at hx
  exact hx.unique hasSum_zero

/-- Only finitely many coordinates of a vector in a Hilbert basis have magnitude at least a
positive `t`. -/
theorem finite_setOf_le_abs_inner {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : HilbertBasis ι ℝ E) (x : E) {t : ℝ} (ht : 0 < t) :
    {i | t ≤ |⟪b i, x⟫|}.Finite := by
  have h := (b.orthonormal.inner_products_summable (x := x)).tendsto_cofinite_zero.eventually
    (gt_mem_nhds (pow_pos ht 2))
  refine (Filter.eventually_cofinite.1 h).subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, not_lt] at hi ⊢
  exact pow_le_pow_left₀ ht.le hi 2

/-- A real family with a nonzero member, only finitely many of whose members exceed any
positive magnitude, has rationals `0 < b < a` such that some member has magnitude at least
`a` and every member of magnitude below `a` has magnitude at most `b`. -/
theorem exists_rat_gap {ι : Type*} (f : ι → ℝ) (hfin : ∀ t, 0 < t → {i | t ≤ |f i|}.Finite)
    {i₀ : ι} (hi₀ : f i₀ ≠ 0) :
    ∃ q : ℚ × ℚ, 0 < q.2 ∧ q.2 < q.1 ∧ (∃ i, (q.1 : ℝ) ≤ |f i|) ∧
      ∀ i, |f i| < q.1 → |f i| ≤ q.2 := by
  set m := |f i₀|
  have hm : 0 < m := abs_pos.2 hi₀
  have hT : {i | m / 2 ≤ |f i| ∧ |f i| < m}.Finite :=
    (hfin (m / 2) (half_pos hm)).subset fun i hi => hi.1
  obtain ⟨L, hL0, hLm, hL⟩ : ∃ L, 0 < L ∧ L < m ∧ ∀ i, |f i| < m → |f i| ≤ L := by
    rcases Set.eq_empty_or_nonempty {i | m / 2 ≤ |f i| ∧ |f i| < m} with hT' | hT'
    · refine ⟨m / 2, half_pos hm, half_lt_self hm, fun i hi => ?_⟩
      by_contra hc
      have hi' : i ∈ {i | m / 2 ≤ |f i| ∧ |f i| < m} := ⟨(not_le.1 hc).le, hi⟩
      rw [hT'] at hi'
      exact hi'
    · obtain ⟨a, ha, hmax⟩ := Set.exists_max_image _ (fun i => |f i|) hT hT'
      refine ⟨max (m / 2) |f a|, lt_max_of_lt_left (half_pos hm),
        max_lt (half_lt_self hm) ha.2, fun i hi => ?_⟩
      by_cases hi' : m / 2 ≤ |f i|
      · exact le_max_of_le_right (hmax i ⟨hi', hi⟩)
      · exact le_max_of_le_left (not_le.1 hi').le
  obtain ⟨q₂, hq₂L, hq₂m⟩ := exists_rat_btwn hLm
  obtain ⟨q₁, hq₁₂, hq₁m⟩ := exists_rat_btwn hq₂m
  refine ⟨(q₁, q₂), by exact_mod_cast hL0.trans hq₂L, by exact_mod_cast hq₁₂, ⟨i₀, hq₁m.le⟩,
    fun i hi => (hL i (hi.trans hq₁m)).trans hq₂L.le⟩

/-- Proposition C. -/
theorem exists_unitVector_classes (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    ∃ (cls : E → ℕ) (η : ℕ → ℝ), (∀ n, 0 < η n) ∧
      ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → cls x = cls y → η (cls x) ≤ 1 + ⟪x, y⟫ := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ E
  rcases isEmpty_or_nonempty w with hw | hw
  · refine ⟨fun _ => 0, fun _ => 1, fun _ => one_pos, fun x y hx _ _ => ?_⟩
    rw [eq_zero_of_forall_inner_hilbertBasis_eq_zero (x := x) b fun i => (IsEmpty.false i).elim,
      norm_zero] at hx
    exact (zero_ne_one hx).elim
  have hgood : ∀ x : E, ∃ q : ℚ × ℚ, ‖x‖ = 1 → 0 < q.2 ∧ q.2 < q.1 ∧
      (∃ i, (q.1 : ℝ) ≤ |⟪b i, x⟫|) ∧ ∀ i, |⟪b i, x⟫| < q.1 → |⟪b i, x⟫| ≤ q.2 := by
    intro x
    by_cases hx : ‖x‖ = 1
    · obtain ⟨i₀, hi₀⟩ : ∃ i, ⟪b i, x⟫ ≠ 0 := by
        by_contra! h
        rw [eq_zero_of_forall_inner_hilbertBasis_eq_zero b h, norm_zero] at hx
        exact zero_ne_one hx
      obtain ⟨q, hq⟩ := exists_rat_gap (fun i => ⟪b i, x⟫)
        (fun t ht => finite_setOf_le_abs_inner b x ht) hi₀
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose q hq using hgood
  let g : (ℚ × ℚ) × Bool → ℝ := fun k =>
    if k.1.2 < k.1.1 then ((k.1.1 : ℝ) - k.1.2) ^ 2 / 2 else 1
  refine ⟨fun x => Encodable.encode
      (q x, decide (0 < ⟪b (Classical.epsilon fun i => ((q x).1 : ℝ) ≤ |⟪b i, x⟫|), x⟫)),
    fun n => (Encodable.decode n).elim 1 g, fun n => ?_, fun x y hx hy hxy => ?_⟩
  · change 0 < (Encodable.decode n).elim 1 g
    rcases Encodable.decode n with _ | k
    · exact one_pos
    · simp only [Option.elim, g]
      split_ifs with h
      · have : (k.1.2 : ℝ) < k.1.1 := by exact_mod_cast h
        have : (0 : ℝ) < (k.1.1 : ℝ) - k.1.2 := by linarith
        positivity
      · exact one_pos
  obtain ⟨hqxy, hsign⟩ := Prod.mk.inj (Encodable.encode_injective hxy)
  have hqy := hq y hy
  rw [← hqxy] at hqy hsign
  obtain ⟨h0, h12, ⟨i₁, hi₁⟩, hgap⟩ := hq x hx
  obtain ⟨-, -, -, hgapy⟩ := hqy
  simp only [Encodable.encodek, Option.elim, g, h12, ↓reduceIte]
  set p := q x
  have hp12 : (p.2 : ℝ) < p.1 := by exact_mod_cast h12
  have hp2 : (0 : ℝ) < p.2 := by exact_mod_cast h0
  -- some coordinate of `x + y` has magnitude at least `a - b`
  obtain ⟨i, hi⟩ : ∃ i, (p.1 : ℝ) - p.2 ≤ |⟪b i, x⟫ + ⟪b i, y⟫| := by
    by_cases hS : ∀ i, (p.1 : ℝ) ≤ |⟪b i, x⟫| ↔ (p.1 : ℝ) ≤ |⟪b i, y⟫|
    · have he : (fun i => (p.1 : ℝ) ≤ |⟪b i, x⟫|) = fun i => (p.1 : ℝ) ≤ |⟪b i, y⟫| :=
        funext fun i => propext (hS i)
      rw [← he] at hsign
      set i₀ := Classical.epsilon fun i => (p.1 : ℝ) ≤ |⟪b i, x⟫|
      have hx0 : (p.1 : ℝ) ≤ |⟪b i₀, x⟫| :=
        Classical.epsilon_spec (p := fun i => (p.1 : ℝ) ≤ |⟪b i, x⟫|) ⟨i₁, hi₁⟩
      have hy0 := (hS i₀).1 hx0
      refine ⟨i₀, ?_⟩
      by_cases hpos : 0 < ⟪b i₀, x⟫
      · have hpos' : 0 < ⟪b i₀, y⟫ := by simpa [hpos] using hsign
        rw [abs_of_pos hpos] at hx0
        rw [abs_of_pos hpos'] at hy0
        rw [abs_of_pos (by linarith)]
        linarith
      · have hpos' : ¬0 < ⟪b i₀, y⟫ := by simpa [hpos] using hsign
        rw [not_lt] at hpos hpos'
        rw [abs_of_nonpos hpos] at hx0
        rw [abs_of_nonpos hpos'] at hy0
        rw [abs_of_nonpos (by linarith)]
        linarith
    · obtain ⟨i, hi⟩ := not_forall.1 hS
      refine ⟨i, ?_⟩
      have tri₁ : |⟪b i, x⟫| - |⟪b i, y⟫| ≤ |⟪b i, x⟫ + ⟪b i, y⟫| := by
        have := abs_sub_abs_le_abs_sub ⟪b i, x⟫ (-⟪b i, y⟫)
        rwa [abs_neg, sub_neg_eq_add] at this
      have tri₂ : |⟪b i, y⟫| - |⟪b i, x⟫| ≤ |⟪b i, x⟫ + ⟪b i, y⟫| := by
        have := abs_sub_abs_le_abs_sub ⟪b i, y⟫ (-⟪b i, x⟫)
        rwa [abs_neg, sub_neg_eq_add, add_comm] at this
      by_cases hA : (p.1 : ℝ) ≤ |⟪b i, x⟫|
      · have hB : |⟪b i, y⟫| < p.1 := not_le.1 fun h => hi ⟨fun _ => h, fun _ => hA⟩
        have := hgapy i hB
        linarith
      · have hB : (p.1 : ℝ) ≤ |⟪b i, y⟫| := by
          by_contra h
          exact hi ⟨fun h' => (hA h').elim, fun h' => (h h').elim⟩
        have := hgap i (not_le.1 hA)
        linarith
  -- a single coordinate is bounded by the norm
  have hcoord : |⟪b i, x + y⟫| ≤ ‖x + y‖ := by
    have := abs_real_inner_le_norm (b i) (x + y)
    rwa [b.orthonormal.1 i, one_mul] at this
  rw [inner_add_right] at hcoord
  have hsq := pow_le_pow_left₀ (by linarith) (hi.trans hcoord) 2
  rw [norm_add_sq_real, hx, hy] at hsq
  linarith

/-- The vertices fall into countably many classes within which any two signs agree with
probability at least a positive constant of the class. -/
theorem exists_sign_classes {V : Type*} (ν : Measure (V → Bool)) [IsProbabilityMeasure ν] :
    ∃ (cls : V → ℕ) (η : ℕ → ℝ≥0), (∀ n, 0 < η n) ∧
      ∀ u v, cls u = cls v → (η (cls u) : ℝ≥0∞) ≤ ν {ω | ω u = ω v} := by
  obtain ⟨cls, η, hη, hcls⟩ := exists_unitVector_classes (Lp ℝ 2 ν)
  -- the sign `±1` of vertex `u`
  let f : V → (V → Bool) → ℝ := fun u ω => if ω u then 1 else -1
  have hfm : ∀ u, Measurable (f u) := fun u =>
    (measurable_of_countable (fun c : Bool => if c then (1 : ℝ) else -1)).comp
      (measurable_pi_apply u)
  have hfL : ∀ u, MemLp (f u) 2 ν := fun u =>
    MemLp.of_bound (hfm u).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      simp only [f]
      split_ifs <;> simp)
  let g : V → Lp ℝ 2 ν := fun u => (hfL u).toLp (f u)
  have hinner : ∀ u v,
      1 + ⟪g u, g v⟫ = 2 * ν.real {ω | ω u = ω v} := by
    intro u v
    have hA : MeasurableSet {ω : V → Bool | ω u = ω v} :=
      measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply v)
    have he : (fun ω => ⟪g u ω, g v ω⟫) =ᵐ[ν]
        fun ω => {ω | ω u = ω v}.indicator (fun _ => (2 : ℝ)) ω - 1 := by
      filter_upwards [(hfL u).coeFn_toLp, (hfL v).coeFn_toLp] with ω hu hv
      rw [hu, hv]
      simp only [f, Set.indicator, Set.mem_ofPred_eq]
      cases ω u <;> cases ω v <;> norm_num
    rw [L2.inner_def, integral_congr_ae he,
      integral_sub ((integrable_const 2).indicator hA) (integrable_const 1),
      integral_indicator_const _ hA, integral_const]
    simp only [probReal_univ, smul_eq_mul]
    ring
  have hunit : ∀ u, ‖g u‖ = 1 := by
    intro u
    have h := hinner u u
    simp only [real_inner_self_eq_norm_sq, Set.ofPred_true, probReal_univ] at h
    have h2 : ‖g u‖ ^ 2 = 1 := by linarith
    nlinarith [norm_nonneg (g u)]
  refine ⟨fun u => cls (g u), fun n => (η n / 2).toNNReal,
    fun n => Real.toNNReal_pos.2 (half_pos (hη n)), fun u v huv => ?_⟩
  have h := hcls _ _ (hunit u) (hunit v) huv
  rw [hinner] at h
  change ENNReal.ofReal (η _ / 2) ≤ _
  rw [← ofReal_measureReal (measure_ne_top ν _)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Erdos111
