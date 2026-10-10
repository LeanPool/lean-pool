/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.LinearInequalities.Separation
public import LeanPool.ScottMeasurement.LinearInequalities.Rationalization
public import LeanPool.ScottMeasurement.LinearInequalities.Sequences

/-!
# Scott 1964, Theorems 1.1–1.4

Finite convex-separation forms of the general method in §1.
-/

@[expose] public section

open Set

namespace Scott1964.MeasurementStructures.LinearInequalities

section Algebraic

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- The sequence formulation may be used with any nonempty finite index type. -/
theorem WeightedSequenceCancellation.fintype {X N : Set L}
    (h : WeightedSequenceCancellation X N) {I : Type*} [Fintype I] [Nonempty I]
    (x : I → L) (c : I → ℝ) (hx : ∀ i, x i ∈ X)
    (hN : ∀ i, x i ∈ N) (hc : ∀ i, 0 < c i)
    (hsum : ∑ i, c i • x i = 0) : ∀ i, -x i ∈ N := by
  let n := Fintype.card I - 1
  have hcard : Fintype.card I = n + 1 := by
    dsimp [n]
    have := Fintype.card_pos (α := I)
    omega
  let e : Fin (n + 1) ≃ I :=
    Fintype.equivOfCardEq (by simpa using hcard.symm)
  have he := h n (x ∘ e) (c ∘ e) (fun i ↦ hx (e i))
    (fun i ↦ hN (e i)) (fun i ↦ hc (e i))
    (by
      rw [← hsum]
      exact e.sum_comp (fun i ↦ c i • x i))
  intro i
  simpa using he (e.symm i)

/-- Scott's positive-weight sequence condition is
equivalent to the geometric cancellation condition. -/
theorem weightedCancellation_of_sequence {X N : Set L}
    (hsym : Symmetric X)
    (hseq : WeightedSequenceCancellation X N) :
    WeightedCancellation X N := by
  rw [WeightedCancellation, Set.disjoint_left]
  intro z hzconv hzspan
  obtain ⟨ι, instι, w, a, hw, hwone, ha, hwa⟩ :=
    mem_convexHull_iff_exists_fintype.mp hzconv
  obtain ⟨d, t, ht, hdsupp, hdt⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp hzspan
  let I₁ := {i : ι // w i ≠ 0}
  let I₂ := {y : ↥t // d y ≠ 0}
  let I := I₁ ⊕ I₂
  let v : I → L
    | Sum.inl i => a i
    | Sum.inr y => if 0 < d y.1.1 then -y.1.1 else y.1.1
  let c : I → ℝ
    | Sum.inl i => w i
    | Sum.inr y => |d y.1.1|
  have hI : Nonempty I := by
    have hwne : ∃ i, w i ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hwone
    exact ⟨Sum.inl ⟨hwne.choose, hwne.choose_spec⟩⟩
  let : Nonempty I := hI
  have hvX : ∀ i, v i ∈ X := by
    rintro (i | y)
    · exact (ha i).1
    · rcases ht y.1.2 with ⟨hyX, hyN, hnyN⟩
      dsimp [v]
      split_ifs
      · exact hsym hyX
      · exact hyX
  have hvN : ∀ i, v i ∈ N := by
    rintro (i | y)
    · exact (ha i).2.1
    · rcases ht y.1.2 with ⟨hyX, hyN, hnyN⟩
      dsimp [v]
      split_ifs
      · exact hnyN
      · exact hyN
  have hc : ∀ i, 0 < c i := by
    rintro (i | y)
    · exact lt_of_le_of_ne (hw i) i.property.symm
    · exact abs_pos.mpr y.property
  have hsum : ∑ i, c i • v i = 0 := by
    rw [Fintype.sum_sum_type]
    have hleft : ∑ i : I₁, c (.inl i) • v (.inl i) = z := by
      rw [← hwa]
      rw [show (∑ i : I₁, c (.inl i) • v (.inl i)) =
          (∑ i ∈ Finset.univ.filter (fun i ↦ w i ≠ 0), w i • a i) by
        simpa [I₁, c, v] using
          (Finset.sum_subtype (Finset.univ.filter fun i ↦ w i ≠ 0)
            (by simp) (fun i ↦ w i • a i)).symm]
      exact Finset.sum_filter_of_ne fun i hi hterm hwi ↦
        hterm (by simp [hwi])
    have hright : ∑ y : I₂, c (.inr y) • v (.inr y) = -z := by
      rw [← hdt]
      have hsub :
          ∑ y : I₂, c (.inr y) • v (.inr y) =
            -∑ y ∈ t, d y • y := by
        rw [← Finset.sum_neg_distrib]
        rw [show (∑ y : I₂, c (.inr y) • v (.inr y)) =
            (∑ y : {y : ↥t // d y.1 ≠ 0}, -(d y.1.1 • y.1.1)) by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [I₂, c, v]
          split_ifs with hdy
          · rw [abs_of_pos hdy, smul_neg]
          · have hdyneg : d y.1.1 < 0 := lt_of_le_of_ne (le_of_not_gt hdy) y.2
            rw [abs_of_neg hdyneg, neg_smul]]
        calc
          ∑ y : {y : ↥t // d y.1 ≠ 0}, -(d y.1.1 • y.1.1) =
              ∑ y ∈ Finset.univ.filter (fun y : ↥t ↦ d y.1 ≠ 0),
                -(d y.1 • y.1) := by
                  exact (Finset.sum_subtype
                    (Finset.univ.filter fun y : ↥t ↦ d y.1 ≠ 0)
                    (by simp) (fun y : ↥t ↦ -(d y.1 • y.1))).symm
          _ = ∑ y : ↥t, -(d y.1 • y.1) := by
                exact Finset.sum_filter_of_ne fun y hy hterm hdy ↦
                  hterm (by simp [hdy])
          _ = ∑ y ∈ t, -(d y • y) := by
                change (t.attach.sum fun y ↦ -(d y.1 • y.1)) = _
                exact Finset.sum_attach t (fun y ↦ -(d y • y))
      exact hsub
    rw [hleft, hright]
    exact add_neg_cancel z
  have hall := hseq.fintype v c hvX hvN hc hsum
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hwone
  have hnot := (ha i).2.2
  exact hnot (by
    simpa [v] using hall (Sum.inl (show I₁ from ⟨i, hi⟩)))

/-- A realizing functional supplies Scott's strictly monotonic extension to
the additive closure. This is the forward half of Theorem 1.4. -/
theorem scott_theorem_1_4_forward {Y : Set L} {R : L → L → Prop}
    (hreal : RelationRealizable Y R) :
    ∃ Rplus : L → L → Prop,
      ExtendsOn Y (additiveClosure Y) R Rplus ∧
        StrictlyMonotonic (additiveClosure Y) Rplus := by
  obtain ⟨φ, hφ⟩ := hreal
  let Rplus : L → L → Prop := fun x y ↦ φ y ≤ φ x
  refine ⟨Rplus, ⟨AddSubmonoid.subset_closure, ?_⟩, ?_⟩
  · intro x hx y hy
    exact (hφ x hx y hy).symm
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy
      exact le_total (φ y) (φ x)
    · intro x₀ y₀ x₁ y₁ hx₀ hy₀ hx₁ hy₁ h₀ h₁
      dsimp [Rplus] at h₀ h₁ ⊢
      simp only [map_add]
      linarith
    · intro x₀ y₀ x₁ y₁ hx₀ hy₀ hx₁ hy₁ heq h₁
      dsimp [Rplus] at h₁ ⊢
      have hsum : φ x₀ + φ x₁ = φ y₀ + φ y₁ := by
        simpa only [map_add] using congrArg φ heq
      linarith

end Algebraic

section Additive

variable {L : Type*} [AddCommGroup L]

/-- A strictly monotonic extension implies Scott's literal condition (6). -/
theorem StrictlyMonotonic.relationSequenceCancellation
    {Y : Set L} {R Rplus : L → L → Prop}
    (hext : ExtendsOn Y (additiveClosure Y) R Rplus)
    (hmono : StrictlyMonotonic (additiveClosure Y) Rplus) :
    RelationSequenceCancellation Y R := by
  intro n x y hx hy hR hsum
  have hsumRel :
      ∀ s : Finset (Fin (n + 1)),
        Rplus (∑ i ∈ s, x i) (∑ i ∈ s, y i) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa using (hmono.complete
          (show (0 : L) ∈ additiveClosure Y from AddSubmonoid.zero_mem _)
          (show (0 : L) ∈ additiveClosure Y from AddSubmonoid.zero_mem _)).elim id id
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        apply hmono.add (hext.1 (hx i)) (hext.1 (hy i))
          (AddSubmonoid.sum_mem _ fun j hj ↦ hext.1 (hx j))
          (AddSubmonoid.sum_mem _ fun j hj ↦ hext.1 (hy j))
          ((hext.2 (hx i) (hy i)).mpr (hR i)) ih
  intro j
  let t : Finset (Fin (n + 1)) := Finset.univ.erase j
  have htail := hsumRel t
  apply (hext.2 (hy j) (hx j)).mp
  apply hmono.cancel (hext.1 (hx j)) (hext.1 (hy j))
    (AddSubmonoid.sum_mem _ fun i hi ↦ hext.1 (hx i))
    (AddSubmonoid.sum_mem _ fun i hi ↦ hext.1 (hy i))
    ?_ htail
  have hxsplit : x j + ∑ i ∈ t, x i = ∑ i, x i := by
    rw [add_comm, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hysplit : y j + ∑ i ∈ t, y i = ∑ i, y i := by
    rw [add_comm, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  rw [hxsplit, hysplit, hsum]

end Additive

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L]

/-- Scott (1964), Theorem 1.1. -/
theorem scott_theorem_1_1 {X N : Set L} (hX : X.Finite) (hsym : Symmetric X) :
    Realizable X N ↔ SignComplete X N ∧ WeightedSequenceCancellation X N := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases h : 0 ≤ φ x
      · exact Or.inl ((hφ x hx).mpr h)
      · right
        have hnx := hsym hx
        apply (hφ (-x) hnx).mpr
        simpa using le_of_not_ge h
    · exact Realizable.weightedSequenceCancellation ⟨φ, hφ⟩ hsym
  · rintro ⟨htotal, hseq⟩
    have hcancel := weightedCancellation_of_sequence hsym hseq
    obtain ⟨φ, hstrict, hneutral⟩ :=
      (finite_strict_separation
        (hX.subset fun _ hx ↦ hx.1)).mp hcancel
    refine ⟨φ, fun x hx ↦ ?_⟩
    constructor
    · intro hN
      by_cases hnN : -x ∈ N
      · exact le_of_eq (hneutral x ⟨hx, hN, hnN⟩).symm
      · exact (hstrict x ⟨hx, hN, hnN⟩).le
    · intro hφ
      rcases htotal hx with hN | hnN
      · exact hN
      · by_contra hxN
        have hneg := hstrict (-x) ⟨hsym hx, hnN, by simpa using hxN⟩
        simp only [map_neg] at hneg
        linarith

/-- Scott (1964), Theorem 1.2, for rational coordinate vectors.

Rationality is used to replace a positive real dependence by a positive
rational dependence, clear denominators, and reduce to repeated unweighted
summands.
-/
theorem scott_theorem_1_2 {S : Type*} [Finite S] {X N : Set (S → ℝ)}
    (hX : X.Finite) (hrat : IsRationalSet X) (hsym : Symmetric X) :
    Realizable X N ↔ SignComplete X N ∧ UnweightedSequenceCancellation X N := by
  let := Fintype.ofFinite S
  constructor
  · intro hreal
    have h := (scott_theorem_1_1 hX hsym).mp hreal
    exact ⟨h.1, h.2.unweighted⟩
  · rintro ⟨hcomplete, hunweighted⟩
    apply (scott_theorem_1_1 hX hsym).mpr
    exact ⟨hcomplete, hunweighted.rationalWeighted hrat⟩

/-- Geometric intermediate form used in the proof of Theorem 1.3. -/
theorem scott_theorem_1_3_geometric {Y : Set L} {R : L → L → Prop} (hY : Y.Finite) :
    RelationRealizable Y R ↔ RelationComplete Y R ∧ RelationCancellation Y R := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      exact le_total (φ y) (φ x) |>.imp (fun h ↦ (hφ x hx y hy).mpr h)
        (fun h ↦ (hφ y hy x hx).mpr h)
    · have hstrictFinite : (strictDifferences Y R).Finite := by
        apply ((hY.prod hY).image fun p : L × L ↦ p.1 - p.2).subset
        rintro z ⟨x, hx, y, hy, -, -, rfl⟩
        exact ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      apply (finite_strict_separation hstrictFinite).mpr
      refine ⟨φ, ?_, ?_⟩
      · rintro z ⟨x, hx, y, hy, hxy, hyx, rfl⟩
        have hle := (hφ x hx y hy).mp hxy
        have hnle : ¬φ x ≤ φ y := by
          intro h
          exact hyx ((hφ y hy x hx).mpr h)
        simp only [map_sub]
        linarith
      · rintro z ⟨x, hx, y, hy, hxy, hyx, rfl⟩
        have h₁ := (hφ x hx y hy).mp hxy
        have h₂ := (hφ y hy x hx).mp hyx
        simp only [map_sub]
        linarith
  · rintro ⟨hcomplete, hcancel⟩
    have hstrictFinite : (strictDifferences Y R).Finite := by
      apply ((hY.prod hY).image fun p : L × L ↦ p.1 - p.2).subset
      rintro z ⟨x, hx, y, hy, -, -, rfl⟩
      exact ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    obtain ⟨φ, hstrict, hneutral⟩ :=
      (finite_strict_separation hstrictFinite).mp hcancel
    refine ⟨φ, fun x hx y hy ↦ ?_⟩
    constructor
    · intro hxy
      by_cases hyx : R y x
      · have hz := hneutral (x - y) ⟨x, hx, y, hy, hxy, hyx, rfl⟩
        have heq : φ x = φ y := by
          simp only [map_sub] at hz
          linarith
        exact heq.ge
      · have hz := hstrict (x - y) ⟨x, hx, y, hy, hxy, hyx, rfl⟩
        simpa [map_sub, sub_pos] using hz.le
    · intro hle
      rcases hcomplete hx hy with hxy | hyx
      · exact hxy
      · by_contra hnxy
        have hz := hstrict (y - x) ⟨y, hy, x, hx, hyx, hnxy, rfl⟩
        simp only [map_sub, sub_pos] at hz
        linarith

/-- Scott (1964), Theorem 1.3, with the literal paired equal-sums
cancellation condition (6). -/
theorem scott_theorem_1_3 {S : Type*} [Finite S]
    {Y : Set (S → ℝ)} {R : (S → ℝ) → (S → ℝ) → Prop}
    (hY : Y.Finite) (hYrat : IsRationalSet Y) :
    RelationRealizable Y R ↔
      RelationComplete Y R ∧ RelationSequenceCancellation Y R := by
  let := Fintype.ofFinite S
  constructor
  · intro hreal
    obtain ⟨φ, hφ⟩ := hreal
    refine ⟨?_, RelationRealizable.sequenceCancellation ⟨φ, hφ⟩⟩
    intro x hx y hy
    exact le_total (φ y) (φ x) |>.imp
      (fun h ↦ (hφ x hx y hy).mpr h) (fun h ↦ (hφ y hy x hx).mpr h)
  · rintro ⟨hcomplete, hcancel⟩
    let X : Set (S → ℝ) := {z | ∃ x ∈ Y, ∃ y ∈ Y, z = x - y}
    let N : Set (S → ℝ) := {z | ∃ x ∈ Y, ∃ y ∈ Y, R x y ∧ z = x - y}
    have hXfinite : X.Finite := by
      apply ((hY.prod hY).image fun p : (S → ℝ) × (S → ℝ) ↦ p.1 - p.2).subset
      rintro z ⟨x, hx, y, hy, rfl⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    have hXrat : IsRationalSet X := rational_difference_set hYrat
    have hXsym : Symmetric X := by
      rintro z ⟨x, hx, y, hy, rfl⟩
      exact ⟨y, hy, x, hx, by simp [sub_eq_add_neg]⟩
    have hsign : SignComplete X N := by
      rintro z ⟨x, hx, y, hy, rfl⟩
      rcases hcomplete hx hy with hxy | hyx
      · left
        exact ⟨x, hx, y, hy, hxy, rfl⟩
      · right
        exact ⟨y, hy, x, hx, hyx, by simp [sub_eq_add_neg]⟩
    have hunweighted : UnweightedSequenceCancellation X N := by
      intro n z hzX hzN hsum
      choose x hx y hy hR hxy using hzN
      have hsumeq : ∑ i, x i = ∑ i, y i := by
        have hzero : ∑ i, x i - ∑ i, y i = 0 := by
          rw [← Finset.sum_sub_distrib]
          simpa only [hxy] using hsum
        exact sub_eq_zero.mp hzero
      have hrev := hcancel n x y hx hy hR hsumeq
      intro i
      exact ⟨y i, hy i, x i, hx i, hrev i, by
        rw [hxy i]
        simp [sub_eq_add_neg]⟩
    obtain ⟨φ, hφ⟩ :=
      (scott_theorem_1_2 hXfinite hXrat hXsym).mpr ⟨hsign, hunweighted⟩
    refine ⟨φ, fun x hx y hy ↦ ?_⟩
    constructor
    · intro hxy
      have hN : x - y ∈ N := ⟨x, hx, y, hy, hxy, rfl⟩
      have hnonneg := (hφ (x - y) ⟨x, hx, y, hy, rfl⟩).mp hN
      simpa [map_sub, sub_nonneg] using hnonneg
    · intro hle
      have hnonneg : 0 ≤ φ (x - y) := by simpa [map_sub, sub_nonneg] using hle
      obtain ⟨x', hx', y', hy', hx'y', heq⟩ :=
        (hφ (x - y) ⟨x, hx, y, hy, rfl⟩).mpr hnonneg
      by_contra hnxy
      have hyx := (hcomplete hx hy).resolve_left hnxy
      let xs : Fin 2 → S → ℝ := ![x', y]
      let ys : Fin 2 → S → ℝ := ![y', x]
      have hsum2 : ∑ i, xs i = ∑ i, ys i := by
        rw [Fin.sum_univ_two, Fin.sum_univ_two]
        dsimp [xs, ys]
        ext s
        have hs := congrFun heq s
        dsimp at hs ⊢
        linarith
      have hback := hcancel 1 xs ys (by simp [xs, hx', hy])
        (by simp [ys, hy', hx]) (by
          intro i
          fin_cases i <;> simp [xs, ys, hx'y', hyx]) hsum2
      exact hnxy (by simpa [xs, ys] using hback (1 : Fin 2))

/-- Scott (1964), Theorem 1.4: realizability is equivalent to extendability
to a strictly monotonic relation on the additive closure. -/
theorem scott_theorem_1_4 {S : Type*} [Finite S]
    {Y : Set (S → ℝ)} {R : (S → ℝ) → (S → ℝ) → Prop}
    (hY : Y.Finite) (hYrat : IsRationalSet Y) :
    RelationRealizable Y R ↔
      ∃ Rplus : (S → ℝ) → (S → ℝ) → Prop,
        ExtendsOn Y (additiveClosure Y) R Rplus ∧
        StrictlyMonotonic (additiveClosure Y) Rplus := by
  let := Fintype.ofFinite S
  constructor
  · intro h
    exact scott_theorem_1_4_forward h
  · rintro ⟨Rplus, hext, hmono⟩
    apply (scott_theorem_1_3 hY hYrat).mpr
    refine ⟨?_, hmono.relationSequenceCancellation hext⟩
    intro x hx y hy
    exact (hmono.complete (hext.1 hx) (hext.1 hy)).imp
      (fun h ↦ hext.2 hx hy |>.mp h) (fun h ↦ hext.2 hy hx |>.mp h)

end Scott1964.MeasurementStructures.LinearInequalities
