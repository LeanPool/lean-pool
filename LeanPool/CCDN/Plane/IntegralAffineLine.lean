/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.ProjectiveBox

/-! Integer points on rational affine lines. Primitive integer
directions make the line parameter integral, giving a spacing bound. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The rational affine line `{a + t • v | t ∈ ℚ}` through `a` with direction `v`. -/
def rationalAffineLine {n : ℕ} (a v : RatPoint n) : Set (RatPoint n) :=
  {x | ∃ t : ℚ, x = a + t • v}

/-- The height `max_j |v j|` of an integer vector `v`. -/
def integerDirectionHeight {n : ℕ} (v : IntPoint n) : ℕ :=
  Finset.univ.sup (fun j => (v j).natAbs)

/-- Scaling the direction by a nonzero rational does not change the affine line. -/
lemma rationalAffineLine_smul_direction {n : ℕ} (a v : RatPoint n) {c : ℚ} (hc : c ≠ 0) :
    rationalAffineLine a (c • v) = rationalAffineLine a v := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t * c, by simpa only [smul_smul] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t / c, ?_⟩
    simpa only [smul_smul, div_mul_cancel₀ t hc] using ht

/-- Moving the base point along the direction does not change the affine line. -/
lemma rationalAffineLine_shift_base {n : ℕ} (a v : RatPoint n) (s : ℚ) :
    rationalAffineLine (a + s • v) v = rationalAffineLine a v := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨s + t, by simpa only [add_smul, add_assoc] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ht.trans ?_⟩
    funext j
    dsimp
    ring

/-- Any two distinct points determine the entire parameterized rational line. -/
private lemma rationalAffineLine_eq_of_distinct_points {n : ℕ} {a v x y : RatPoint n}
    (hx : x ∈ rationalAffineLine a v) (hy : y ∈ rationalAffineLine a v) (hxy : x ≠ y) :
    rationalAffineLine x (y - x) = rationalAffineLine a v := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hts : t - s ≠ 0 := by
    intro he
    have he' : t = s := sub_eq_zero.mp he
    exact hxy (by rw [he'])
  have he : (a + t • v) - (a + s • v) = (t - s) • v := by
    funext j
    dsimp
    ring
  rw [he, rationalAffineLine_smul_direction _ _ hts, rationalAffineLine_shift_base]

/-- A nonzero integer vector has positive height. -/
lemma integerDirectionHeight_pos {n : ℕ} {v : IntPoint n} (hv : v ≠ 0) :
    0 < integerDirectionHeight v := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  exact (Int.natAbs_pos.mpr hj).trans_le
    (Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ j))

private lemma exists_coordinate_integerDirectionHeight {n : ℕ} {v : IntPoint n} (hv : v ≠ 0) :
    ∃ j, |(v j : ℝ)| = integerDirectionHeight v := by
  obtain ⟨j, _⟩ := Function.ne_iff.mp hv
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n))
    ⟨j, Finset.mem_univ j⟩ (fun j => (v j).natAbs)
  refine ⟨k, ?_⟩
  have hh : ((v k).natAbs : ℝ) = integerDirectionHeight v := by exact_mod_cast hk.symm
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hh

/-- Bezout's identity for a primitive direction forces a rational integral
multiple of that direction to have an integer multiplier. -/
private theorem rational_scalar_integral_of_primitive {n : ℕ} (v : IntPoint n)
    (hprim : Finset.univ.gcd v = 1) {t : ℚ} (w : IntPoint n)
    (hw : ∀ j, (w j : ℚ) = t * v j) :
    ∃ k : ℤ, (k : ℚ) = t := by
  obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul Finset.univ v
  have hcQ : (∑ j, (v j : ℚ) * c j) = 1 := by exact_mod_cast (hc.symm.trans hprim)
  refine ⟨∑ j, w j * c j, ?_⟩
  push_cast
  simp_rw [hw]
  rw [show (∑ j, t * (v j : ℚ) * c j) = t * ∑ j, (v j : ℚ) * c j by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring, hcQ, mul_one]

private theorem integer_mem_rationalAffineLine_iff {n : ℕ} (a v x : IntPoint n)
    (hprim : Finset.univ.gcd v = 1) :
    rationalPoint x ∈ rationalAffineLine (rationalPoint a) (rationalPoint v) ↔
      ∃ k : ℤ, ∀ j, x j = a j + k * v j := by
  constructor
  · rintro ⟨t, ht⟩
    have hw (j) : ((x - a) j : ℚ) = t * v j := by
      have hh := congrFun ht j
      change (x j : ℚ) = (a j : ℚ) + t * v j at hh
      change ((x j - a j : ℤ) : ℚ) = _
      push_cast
      linarith
    obtain ⟨k, hk⟩ := rational_scalar_integral_of_primitive v hprim (x - a) hw
    refine ⟨k, fun j => ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hk]
    exact congrFun ht j
  · rintro ⟨k, hk⟩
    refine ⟨(k : ℚ), ?_⟩
    funext j
    change (x j : ℚ) = (a j : ℚ) + (k : ℚ) * v j
    exact_mod_cast hk j

private lemma int_finset_card_le_span (T : Finset ℤ) (hT : T.Nonempty) :
    (T.card : ℝ) ≤ (T.max' hT : ℝ) - (T.min' hT : ℝ) + 1 := by
  have hsub : T ⊆ Finset.Icc (T.min' hT) (T.max' hT) := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨T.min'_le k hk, T.le_max' k hk⟩
  have hle := Finset.card_le_card hsub
  rw [Int.card_Icc] at hle
  have hnonneg : 0 ≤ T.max' hT - T.min' hT + 1 := by
    have hh := T.min'_le (T.max' hT) (T.max'_mem hT)
    omega
  have hh : (T.card : ℤ) ≤ T.max' hT - T.min' hT + 1 := by
    have hh : (T.card : ℤ) ≤ ((T.max' hT + 1 - T.min' hT).toNat : ℤ) := by exact_mod_cast hle
    rw [Int.toNat_of_nonneg (by omega)] at hh
    omega
  exact_mod_cast hh

/-- Integer points on a primitive line are spaced by its largest direction
coordinate. This counts the line's intersection with the integer box. -/
private theorem integral_rationalAffineLine_count {n : ℕ} (a v : IntPoint n)
    (hv : v ≠ 0) (hprim : Finset.univ.gcd v = 1) {B : ℝ} (hB : 0 ≤ B) :
    (count (rationalAffineLine (rationalPoint a) (rationalPoint v)) B : ℝ) ≤
      1 + 2 * B / integerDirectionHeight v := by
  classical
  let S := integralPoints (rationalAffineLine (rationalPoint a) (rationalPoint v)) B
  have hrep (x : S) : ∃ k : ℤ, ∀ j, x.val j = a j + k * v j :=
    (integer_mem_rationalAffineLine_iff a v x.val hprim).mp (mem_integralPoints.mp x.property).2
  choose k hk using hrep
  have hkinj : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    funext j
    rw [hk x j, hk y j, h]
  let T : Finset ℤ := Finset.univ.image k
  have hcard : T.card = S.card := by
    rw [Finset.card_image_of_injective _ hkinj]
    simp only [Finset.card_univ, Fintype.card_coe]
  by_cases hT : T.Nonempty
  · have hTmem (t : ℤ) (ht : t ∈ T) : ∃ x : S, k x = t := by
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp ht
      exact ⟨x, hx⟩
    obtain ⟨xlo, hxlo⟩ := hTmem (T.min' hT) (T.min'_mem hT)
    obtain ⟨xhi, hxhi⟩ := hTmem (T.max' hT) (T.max'_mem hT)
    obtain ⟨j, hj⟩ := exists_coordinate_integerDirectionHeight hv
    have hlo := (mem_integralPoints.mp xlo.property).1 j
    have hhi := (mem_integralPoints.mp xhi.property).1 j
    have hspan : ((T.max' hT : ℝ) - (T.min' hT : ℝ)) * integerDirectionHeight v ≤ 2 * B := by
      have he : (xhi.val j : ℝ) - (xlo.val j : ℝ) =
          ((T.max' hT : ℝ) - (T.min' hT : ℝ)) * (v j : ℝ) := by
        rw [hk xhi j, hk xlo j, hxhi, hxlo]
        push_cast
        ring
      have habs := (abs_sub (xhi.val j : ℝ) (xlo.val j : ℝ)).trans (add_le_add hhi hlo)
      rw [he, abs_mul, hj, abs_of_nonneg (by
        have hh := T.min'_le (T.max' hT) (T.max'_mem hT)
        exact sub_nonneg.mpr (by exact_mod_cast hh))] at habs
      linarith
    have hheight : (0 : ℝ) < integerDirectionHeight v := by
      exact_mod_cast integerDirectionHeight_pos hv
    have hdif := (le_div_iff₀ hheight).mpr hspan
    have hcnt := int_finset_card_le_span T hT
    rw [hcard] at hcnt
    change (S.card : ℝ) ≤ _
    linarith
  · have hz : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hS : S.card = 0 := by simpa only [hz, Finset.card_empty] using hcard.symm
    change (S.card : ℝ) ≤ _
    rw [hS, Nat.cast_zero]
    positivity

/-- Divide an integer direction by the gcd of its coordinates. This gives
a primitive direction of no greater height on the same rational line. -/
private theorem exists_primitive_integer_direction {n : ℕ} (w : IntPoint n) (hw : w ≠ 0) :
    ∃ v : IntPoint n, v ≠ 0 ∧ Finset.univ.gcd v = 1 ∧
      (∀ j, |(v j : ℝ)| ≤ |(w j : ℝ)|) ∧
      ∀ a : RatPoint n, rationalAffineLine a (rationalPoint w) =
        rationalAffineLine a (rationalPoint v) := by
  classical
  obtain ⟨j, _⟩ := Function.ne_iff.mp hw
  obtain ⟨v, hv, hprim⟩ := Finset.extract_gcd w
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨j, Finset.mem_univ j⟩)
  let c := Finset.univ.gcd w
  have hvc (i) : w i = c * v i := hv i (Finset.mem_univ i)
  have hc : c ≠ 0 := by
    intro he
    apply hw
    funext i
    simpa only [he, zero_mul, Pi.zero_apply] using hvc i
  have hv0 : v ≠ 0 := by
    intro he
    apply hw
    funext i
    simpa only [he, Pi.zero_apply, mul_zero] using hvc i
  have hQ : rationalPoint w = (c : ℚ) • rationalPoint v := by
    funext i
    change (w i : ℚ) = (c : ℚ) * v i
    exact_mod_cast hvc i
  refine ⟨v, hv0, hprim, ?_, fun a => ?_⟩
  · intro i
    have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc
    rw [hvc i, Int.cast_mul, abs_mul]
    nlinarith [abs_nonneg (v i : ℝ)]
  · rw [hQ]
    exact rationalAffineLine_smul_direction _ _ (by exact_mod_cast hc)

/-- Two bounded integer points give a primitive integer direction of
height at most twice the box radius, representing their full rational line. -/
private theorem exists_primitive_direction_of_two_integer_points {n : ℕ}
    (a b : IntPoint n) (hab : a ≠ b) {B : ℝ}
    (ha : InBox a B) (hb : InBox b B) :
    ∃ v : IntPoint n, v ≠ 0 ∧ Finset.univ.gcd v = 1 ∧
      (integerDirectionHeight v : ℝ) ≤ 2 * B ∧
      rationalAffineLine (rationalPoint a) (rationalPoint b - rationalPoint a) =
        rationalAffineLine (rationalPoint a) (rationalPoint v) := by
  have hw : b - a ≠ 0 := fun h => hab (sub_eq_zero.mp h).symm
  obtain ⟨v, hv, hprim, hle, he⟩ := exists_primitive_integer_direction (b - a) hw
  refine ⟨v, hv, hprim, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := exists_coordinate_integerDirectionHeight hv
    rw [← hj]
    apply (hle j).trans
    change |((b j - a j : ℤ) : ℝ)| ≤ _
    rw [Int.cast_sub]
    have hh := (abs_sub (b j : ℝ) (a j : ℝ)).trans (add_le_add (hb j) (ha j))
    linarith
  · have hcast : rationalPoint (b - a) = rationalPoint b - rationalPoint a := by
      funext j
      exact Int.cast_sub _ _
    simpa only [hcast] using he (rationalPoint a)

/-- For a nonzero primitive integer vector `v`, the multiplicative height of the projective point
`[v]` equals `max_j |v j|`. -/
theorem projective_direction_height {n : ℕ} (v : IntPoint (n + 1))
    (hv : v ≠ 0) (hprim : Finset.univ.gcd v = 1) :
    (Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv)).mulHeight =
      (integerDirectionHeight v : ℝ) := by
  rw [projective_height_primitive v hv hprim]
  have hsup : (⨆ j, |v j| : ℤ) = (integerDirectionHeight v : ℤ) := by
    apply le_antisymm
    · apply ciSup_le
      intro j
      have hh : (v j).natAbs ≤ integerDirectionHeight v :=
        Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ j)
      have hh' : ((v j).natAbs : ℤ) ≤ (integerDirectionHeight v : ℤ) := by exact_mod_cast hh
      simpa only [Int.natCast_natAbs] using hh'
    · obtain ⟨j, hj⟩ := exists_coordinate_integerDirectionHeight hv
      have hjZ : |v j| = (integerDirectionHeight v : ℤ) := by exact_mod_cast hj
      rw [← hjZ]
      exact le_ciSup (Finite.bddAbove_range (fun j => |v j|)) j
  rw [hsup, Int.cast_natCast]

/-- Any rational affine line containing two bounded integer points has an
integer base point and primitive integer direction, with the exact spacing
estimate and the direction-height cutoff needed for summing line contributions. -/
theorem rationalAffineLine_integer_rep_and_count {n : ℕ}
    (a v : RatPoint n) {B : ℝ} (hB : 0 ≤ B)
    (hcount : 1 < count (rationalAffineLine a v) B) :
    ∃ (z w : IntPoint n), w ≠ 0 ∧ Finset.univ.gcd w = 1 ∧
      InBox z B ∧ (integerDirectionHeight w : ℝ) ≤ 2 * B ∧
      rationalAffineLine a v = rationalAffineLine (rationalPoint z) (rationalPoint w) ∧
      (count (rationalAffineLine a v) B : ℝ) ≤ 1 + 2 * B / integerDirectionHeight w := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcount
  obtain ⟨hxB, hxline⟩ := mem_integralPoints.mp hx
  obtain ⟨hyB, hyline⟩ := mem_integralPoints.mp hy
  obtain ⟨w, hw, hprim, hheight, he⟩ :=
    exists_primitive_direction_of_two_integer_points x y hxy hxB hyB
  have hxyQ : rationalPoint x ≠ rationalPoint y := by
    intro h
    apply hxy
    funext j
    exact Int.cast_injective (congrFun h j)
  have hline : rationalAffineLine a v =
      rationalAffineLine (rationalPoint x) (rationalPoint w) :=
    (rationalAffineLine_eq_of_distinct_points hxline hyline hxyQ).symm.trans he
  refine ⟨x, w, hw, hprim, hxB, hheight, hline, ?_⟩
  rw [hline]
  exact integral_rationalAffineLine_count x w hw hprim hB

end
end CCDN
