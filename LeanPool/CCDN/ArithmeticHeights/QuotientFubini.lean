/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# A Fubini decomposition of the quotient measure over a subspace

For a lattice `Λ` in a real vector space `V` with fundamental domain `F`, and a second space `W`,
the slab `F ×ˢ univ` is a fundamental domain in `V × W` for the sublattice `Λ × 0`, so that for a
`Λ × 0`-invariant set `S` the number `(μV.prod μW) ((F ×ˢ univ) ∩ S)` *is* the measure of the image
of `S` in the quotient `(V × W) ⧸ (Λ × 0)`. The main result decomposes that number as an integral
over `W` of the quotient measures in `V ⧸ Λ` of the slices of `S`.

This is the identity (10) in Cassels' proof of his Chapter VIII, Theorem IV, which is the kernel of
Weyl's proof of the upper bound in Minkowski's second theorem. Two further results carry the rest
of that proof: the descent `ZLattice.measure_inter_add_eq_of_separated`, which says that for a set
whose points are congruent modulo the big lattice `L` only when they are congruent modulo the small
one `Λ`, the quotient measures over `L` and over `Λ` agree; and the scaling estimate
`ZLattice.measure_inter_add_prod_smul_le`, which says that dilating a convex set by `s ≥ 1`
multiplies its quotient measure over `Λ × 0` by at least `s ^ dim W`.

## Main results

* `ZLattice.measure_inter_add_prod_eq_lintegral`: the Fubini decomposition, Cassels' (10).
* `ZLattice.isAddFundamentalDomain_prod_univ`: the slab `F ×ˢ univ` is a fundamental domain for
  `Λ × 0`, which is what makes the left-hand side of the decomposition a quotient measure.
* `ZLattice.measure_inter_add_prod_smul_le`: the scaling estimate, Cassels' (12) and (14).
* `ZLattice.exists_isAddFundamentalDomain_measure_smul_le`: the scaling estimate for a lattice of
  arbitrary rank in a single space, with the slab produced rather than assumed.
* `ZLattice.measure_inter_add_eq_of_separated`: the descent from `L` to `Λ`.
* `ZLattice.pow_mul_measure_inter_add_le`: the two combined — Cassels' Theorem IV in one step, the
  form Minkowski's second theorem chains over the successive minima.
* `ZLattice.countable_of_discreteTopology`: a discrete `ℤ`-submodule of a finite-dimensional real
  normed space is countable. Mathlib has this only for a lattice of full rank.

## Implementation notes

⚠ **The scaling estimate is not a statement about one set being a packing.** Its proof translates
each slice of the body by a *different* vector — `(s - 1) • y₀` for some `y₀` in that slice — and
what makes that legitimate is exactly that the quotient measure of a slice is unchanged by
translation. There is no single map of `V × W` doing this, which is why the Fubini decomposition,
and not a change of variables, is the tool.

⚠ **The descent needs the covolume to be finite, and that is the only place any finiteness enters.**
The proof exhibits `(FΛ ∩ (A + Λ)) ∪ (FL \ (A + L))` as a fundamental domain for `L`, so it has
the measure of `FL`; cancelling the second piece off both sides is what needs `μ FL ≠ ⊤`. No
compactness, closedness or boundedness of the body is used anywhere in this file.

⚠ **`IsZLattice` is not a hypothesis of the product results, and `Countable` is all they want.**
A fundamental domain is passed in as the hypothesis `∀ x, ∃! v : Λ, ↑v + x ∈ F` rather than
constructed, so the product statements are about an arbitrary countable `ℤ`-submodule. Only
`ZLattice.exists_isAddFundamentalDomain_measure_smul_le`, which builds the slab, needs the
submodule to be discrete — and there it is a `ZLattice` in its own span, not in the ambient space.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter VIII §4.2,
Theorem IV, and the displays (10), (12) and (14) of its proof. Cassels normalizes the lattice to
`ℤ ^ n` by a linear transformation first; the `V × W` form here is that normalization made
coordinate-free, and `ZLattice.exists_isAddFundamentalDomain_measure_smul_le` performs it.

⚠ What is *not* here is the chaining of Theorem IV over the successive minima, which is Minkowski's
second theorem itself. Beside the chain it wants three pieces of gauge bookkeeping, all specific to
the body rather than to the quotient measure: that `L ∩ span (v 0, …, v (J - 1))` has rank `J`,
that Cassels' Lemma 2 (`ZLattice.exists_basis_mem_span_int_of_gauge_lt`) supplies the separation
hypothesis for `t • B` when `2 t` is below the `J`-th minimum, and that a dilate of the body has
the expected measure.

This is infrastructure for Layer 4.2 of the `ArithmeticHeights` roadmap.
-/

public section

open MeasureTheory Measure Module Set

open scoped ENNReal Pointwise

namespace ZLattice

section Lattice

variable {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]

/-- A set enlarged by a countable lattice is a countable union of its translates, hence
measurable. -/
private theorem measurableSet_add_lattice (M : Submodule ℤ G) [Countable M] {A : Set G}
    (hA : MeasurableSet A) : MeasurableSet (A + (M : Set G)) := by
  have h : A + (M : Set G) = ⋃ l : M, (fun x ↦ x - (l : G)) ⁻¹' A := by
    ext x
    simp only [Set.mem_add, Set.mem_iUnion, Set.mem_preimage]
    exact ⟨fun ⟨a, ha, l, hl, he⟩ ↦ ⟨⟨l, hl⟩, by simp only [← he]; simpa using ha⟩,
      fun ⟨l, hx⟩ ↦ ⟨x - (l : G), hx, l, l.2, by abel⟩⟩
  rw [h]
  exact MeasurableSet.iUnion fun l ↦ hA.preimage (measurable_id.sub_const _)

omit [MeasurableSpace G] [BorelSpace G] in
/-- A set enlarged by a lattice is invariant under that lattice. -/
private theorem preimage_vadd_add_lattice (M : Submodule ℤ G) {Y : Set G} (g : M) :
    (fun x ↦ g +ᵥ x) ⁻¹' (Y + (M : Set G)) = Y + (M : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, l, hl, he⟩
    have he' : a + l = (g : G) + x := he
    refine ⟨a, ha, l - (g : G), Submodule.sub_mem _ hl g.2, ?_⟩
    change a + (l - (g : G)) = x
    linear_combination (norm := abel) he'
  · rintro ⟨a, ha, l, hl, rfl⟩
    refine ⟨a, ha, (g : G) + l, Submodule.add_mem _ g.2 hl, ?_⟩
    change a + ((g : G) + l) = (g : G) + (a + l)
    abel

omit [MeasurableSpace G] [BorelSpace G] in
/-- Membership in a set enlarged by a lattice is unchanged by a lattice translation. -/
private theorem mem_add_lattice_iff (M : Submodule ℤ G) {A : Set G} {v : G} (hv : v ∈ M) (x : G) :
    v + x ∈ A + (M : Set G) ↔ x ∈ A + (M : Set G) := by
  constructor
  · rintro ⟨a, ha, l, hl, h⟩
    refine ⟨a, ha, l - v, Submodule.sub_mem _ hl hv, ?_⟩
    simp only at h ⊢
    linear_combination (norm := abel) h
  · rintro ⟨a, ha, l, hl, rfl⟩
    exact ⟨a, ha, v + l, Submodule.add_mem _ hv hl, by simp; abel⟩

omit [MeasurableSpace G] [BorelSpace G] in
/-- Transporting the defining property of a fundamental domain along an equality of lattices. -/
private theorem existsUnique_of_eq {M N : Submodule ℤ G} (h : M = N) {F : Set G} {x : G}
    (hM : ∃! v : M, (v : G) + x ∈ F) : ∃! v : N, (v : G) + x ∈ F := by
  obtain ⟨u, hu, huq⟩ := hM
  refine ⟨⟨(u : G), h ▸ u.2⟩, hu, fun w hw ↦ ?_⟩
  have hwm : (w : G) ∈ M := h ▸ w.2
  have hwu : (⟨(w : G), hwm⟩ : M) = u := huq _ hw
  exact Subtype.ext (congrArg (fun z : M ↦ (z : G)) hwu)

end Lattice

section Descent

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- **The descent from a lattice to a sublattice** (the equivalence of (6) with (7) and (8) in
Cassels' proof of his Chapter VIII, Theorem IV). If two points of `A` are congruent modulo `L` only
when they are congruent modulo the sublattice `Λ`, then the measure of the image of `A` in `E ⧸ L`
equals the measure of its image in `E ⧸ Λ`: the covering `E ⧸ Λ → E ⧸ L` is injective there.

Both measures are read off against fundamental domains — `FΛ` for `Λ`, `FL` for `L`, each given by
its exact form `∀ x, ∃! v, ↑v + x ∈ ·` — and the proof exhibits `(FΛ ∩ (A + Λ)) ∪ (FL \ (A + L))`
as a third fundamental domain, for `L`. ⚠ This is where `μ FL ≠ ⊤` is used, and it is the only
finiteness hypothesis in the file. -/
theorem measure_inter_add_eq_of_separated (μ : Measure E) [μ.IsAddLeftInvariant]
    {Λ L : Submodule ℤ E} [Countable Λ] [Countable L] (hΛL : Λ ≤ L) {FΛ FL : Set E}
    (hΛ : ∀ x : E, ∃! v : Λ, (v : E) + x ∈ FΛ) (hL : ∀ x : E, ∃! v : L, (v : E) + x ∈ FL)
    (hmΛ : MeasurableSet FΛ) (hmL : MeasurableSet FL) (hfin : μ FL ≠ ⊤) {A : Set E}
    (hA : MeasurableSet A) (hsep : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ L → x - y ∈ Λ) :
    μ (FΛ ∩ (A + (Λ : Set E))) = μ (FL ∩ (A + (L : Set E))) := by
  have : VAddInvariantMeasure L E μ := inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E μ)
  set SΛ : Set E := A + (Λ : Set E) with hSΛ
  set SL : Set E := A + (L : Set E) with hSL
  have hsub : SΛ ⊆ SL := Set.add_subset_add_left fun l hl ↦ hΛL hl
  have hmSΛ : MeasurableSet SΛ := measurableSet_add_lattice Λ hA
  have hmSL : MeasurableSet SL := measurableSet_add_lattice L hA
  set D : Set E := (FΛ ∩ SΛ) ∪ (FL \ SL) with hD
  have hfd : IsAddFundamentalDomain L D μ := by
    refine IsAddFundamentalDomain.mk' ((hmΛ.inter hmSΛ).union (hmL.diff hmSL)).nullMeasurableSet
      fun x ↦ ?_
    by_cases hx : x ∈ SL
    · have hmemL : ∀ v : L, (v : E) + x ∈ SL := fun v ↦ (mem_add_lattice_iff L v.2 x).2 hx
      have hiff : ∀ y : E, y ∈ SL → (y ∈ D ↔ y ∈ FΛ ∩ SΛ) := fun y hy ↦ by
        simp only [hD, Set.mem_union, Set.mem_sdiff, hy, not_true_eq_false, and_false, or_false]
      have huniq2 : ∀ v v' : L, (v : E) + x ∈ FΛ ∩ SΛ → (v' : E) + x ∈ FΛ ∩ SΛ → v = v' := by
        intro v v' h1 h2
        obtain ⟨a₁, ha₁, c₁, hc₁, he₁⟩ := h1.2
        obtain ⟨a₂, ha₂, c₂, hc₂, he₂⟩ := h2.2
        have he₁' : a₁ + c₁ = (v : E) + x := he₁
        have he₂' : a₂ + c₂ = (v' : E) + x := he₂
        have hd1 : a₁ - a₂ = ((v : E) - (v' : E)) - (c₁ - c₂) := by
          linear_combination (norm := abel) he₁' - he₂'
        have hdiff : a₁ - a₂ ∈ L := by
          rw [hd1]
          exact Submodule.sub_mem _ (Submodule.sub_mem _ v.2 v'.2)
            (hΛL (Submodule.sub_mem _ hc₁ hc₂))
        have hs := hsep a₁ ha₁ a₂ ha₂ hdiff
        have hw : (v : E) - (v' : E) ∈ Λ := by
          have hd2 : (v : E) - (v' : E) = (a₁ - a₂) + (c₁ - c₂) := by
            linear_combination (norm := abel) he₂' - he₁'
          rw [hd2]
          exact Submodule.add_mem _ hs (Submodule.sub_mem _ hc₁ hc₂)
        obtain ⟨u', -, huq⟩ := hΛ ((v' : E) + x)
        have e1 : (⟨(v : E) - (v' : E), hw⟩ : Λ) = u' := by
          refine huq _ ?_
          change ((v : E) - (v' : E)) + ((v' : E) + x) ∈ FΛ
          rw [show ((v : E) - (v' : E)) + ((v' : E) + x) = (v : E) + x from by abel]
          exact h1.1
        have e2 : (0 : Λ) = u' := by
          refine huq _ ?_
          change ((0 : Λ) : E) + ((v' : E) + x) ∈ FΛ
          simpa using h2.1
        have h4 : (v : E) - (v' : E) = 0 := by
          have h5 := congrArg (fun z : Λ ↦ (z : E)) (e1.trans e2.symm)
          simpa using h5
        exact Subtype.ext (sub_eq_zero.1 h4)
      obtain ⟨a, ha, l, hl, hx'⟩ := hx
      have hx'' : a + l = x := hx'
      obtain ⟨u, hu, -⟩ := hΛ a
      have hex : ∃ v : L, (v : E) + x ∈ FΛ ∩ SΛ := by
        refine ⟨⟨(u : E) - l, Submodule.sub_mem _ (hΛL u.2) hl⟩, ?_⟩
        change ((u : E) - l) + x ∈ FΛ ∩ SΛ
        rw [show ((u : E) - l) + x = (u : E) + a from by rw [← hx'']; abel]
        exact ⟨hu, ⟨a, ha, (u : E), u.2, add_comm _ _⟩⟩
      obtain ⟨v₀, hv₀⟩ := hex
      exact ⟨v₀, (hiff _ (hmemL _)).2 hv₀, fun v hv ↦ huniq2 v v₀ ((hiff _ (hmemL v)).1 hv) hv₀⟩
    · have hmemL : ∀ v : L, (v : E) + x ∉ SL := fun v h ↦ hx ((mem_add_lattice_iff L v.2 x).1 h)
      have hiff : ∀ v : L, ((v : E) + x ∈ D ↔ (v : E) + x ∈ FL) := by
        intro v
        have h1 : (v : E) + x ∉ SΛ := fun h ↦ hmemL v (hsub h)
        rw [hD]
        simp only [Set.mem_union, Set.mem_sdiff]
        constructor
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h h1
          · exact h
        · exact fun h ↦ Or.inr ⟨h, hmemL v⟩
      obtain ⟨u, hu, huniq⟩ := hL x
      exact ⟨u, (hiff u).2 hu, fun v hv ↦ huniq v ((hiff v).1 hv)⟩
  have hdisj : Disjoint (FΛ ∩ SΛ) (FL \ SL) :=
    Set.disjoint_left.2 fun y hy hy' ↦ hy'.2 (hsub hy.2)
  have hunion : μ D = μ (FΛ ∩ SΛ) + μ (FL \ SL) := measure_union hdisj (hmL.diff hmSL)
  have hFL : μ FL = μ (FL ∩ SL) + μ (FL \ SL) := (measure_inter_add_sdiff FL hmSL).symm
  have hDeq : μ D = μ FL :=
    hfd.measure_eq (IsAddFundamentalDomain.mk' hmL.nullMeasurableSet hL)
  have hlt : μ (FL \ SL) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.sdiff_subset)
  rw [hunion, hFL] at hDeq
  exact (ENNReal.add_left_inj hlt).mp hDeq

end Descent

section Product

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W]

/-- A lattice in `V` sits in `V × W` as the sublattice `Λ × 0`, and it is countable there. -/
private instance countable_prod_bot (Λ : Submodule ℤ V) [Countable Λ] :
    Countable (Λ.prod (⊥ : Submodule ℤ W)) := by
  refine Function.Injective.countable
    (f := fun p : Λ.prod (⊥ : Submodule ℤ W) ↦ (⟨p.1.1, p.2.1⟩ : Λ)) ?_
  intro p q hpq
  have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hpq
  have h2 : p.1.2 = 0 := p.2.2
  have h3 : q.1.2 = 0 := q.2.2
  exact Subtype.ext (Prod.ext h1 (h2.trans h3.symm))

omit [NormedSpace ℝ V] [BorelSpace V] [FiniteDimensional ℝ V] [NormedSpace ℝ W] [BorelSpace W]
  [FiniteDimensional ℝ W] in
/-- **The slab is a fundamental domain.** If `F` is a fundamental domain for `Λ` in `V`, then
`F ×ˢ univ` is one for `Λ × 0` in `V × W`. This is what makes the left-hand side of
`ZLattice.measure_inter_add_prod_eq_lintegral` the measure of an image in the quotient. -/
theorem isAddFundamentalDomain_prod_univ (μV : Measure V) (μW : Measure W) (Λ : Submodule ℤ V)
    {F : Set V} (hF : ∀ x : V, ∃! v : Λ, (v : V) + x ∈ F) (hFm : MeasurableSet F) :
    IsAddFundamentalDomain (Λ.prod (⊥ : Submodule ℤ W)) (F ×ˢ (univ : Set W)) (μV.prod μW) := by
  refine IsAddFundamentalDomain.mk' (hFm.prod MeasurableSet.univ).nullMeasurableSet fun x ↦ ?_
  obtain ⟨v, hv, hu⟩ := hF x.1
  refine ⟨⟨((v : V), 0), ⟨v.2, Submodule.zero_mem _⟩⟩, ⟨hv, mem_univ _⟩, ?_⟩
  rintro ⟨⟨w₁, w₂⟩, hw⟩ hmem
  have hw₂ : w₂ = 0 := by simpa using hw.2
  subst hw₂
  have hvw := hu ⟨w₁, hw.1⟩ hmem.1
  exact Subtype.ext (Prod.ext (congrArg (fun z : Λ ↦ (z : V)) hvw) rfl)

omit [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] in
/-- The slice of a slab enlarged by `Λ × 0` is the corresponding slice enlarged by `Λ`. -/
private theorem preimage_prodMk_inter (Λ : Submodule ℤ V) (X : Set (V × W)) (z : W) {F : Set V} :
    (fun y ↦ (y, z)) ⁻¹' ((F ×ˢ (univ : Set W)) ∩
        (X + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W))))
      = F ∩ ({y | (y, z) ∈ X} + (Λ : Set V)) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true,
    Set.mem_add, Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_prod, Submodule.mem_bot]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨p, hp, l, ⟨hl₁, hl₂⟩, he⟩
    refine ⟨p.1, ?_, l.1, hl₁, ?_⟩
    · have hz : p.2 = z := by
        have := congrArg Prod.snd he
        simpa [hl₂] using this
      rwa [← hz]
    · have := congrArg Prod.fst he
      simpa using this
  · rintro ⟨a, ha, l, hl, he⟩
    exact ⟨(a, z), ha, (l, 0), ⟨hl, rfl⟩, by simp [he]⟩

/-- **The Fubini decomposition of the quotient measure** (Cassels, Chapter VIII, §4.2, the display
(10) in the proof of Theorem IV). The measure of the image of `X` in `(V × W) ⧸ (Λ × 0)` is the
integral over `W` of the measures of the images of the slices of `X` in `V ⧸ Λ`.

Both sides are quotient measures read off against fundamental domains: the slab `F ×ˢ univ` on the
left, by `ZLattice.isAddFundamentalDomain_prod_univ`, and `F` itself on the right. -/
theorem measure_inter_add_prod_eq_lintegral (μV : Measure V) [μV.IsAddHaarMeasure] (μW : Measure W)
    [μW.IsAddHaarMeasure] (Λ : Submodule ℤ V) [Countable Λ] {F : Set V} (hFm : MeasurableSet F)
    {X : Set (V × W)} (hX : MeasurableSet X) :
    (μV.prod μW) ((F ×ˢ (univ : Set W)) ∩ (X + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W))))
      = ∫⁻ z, μV (F ∩ ({y | (y, z) ∈ X} + (Λ : Set V))) ∂μW := by
  rw [Measure.prod_apply_symm ((hFm.prod MeasurableSet.univ).inter
    (measurableSet_add_lattice _ hX))]
  exact lintegral_congr fun z ↦ by rw [preimage_prodMk_inter Λ X z]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Translation invariance and monotonicity of the quotient measure, in one step: if every point of
`X` lands in `Y` after a translation by the *fixed* vector `c`, the quotient measure of `X` is at
most that of `Y`. -/
private theorem measure_inter_add_le (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : Submodule ℤ V)
    [Countable Λ] {F : Set V} (hF : ∀ x : V, ∃! v : Λ, (v : V) + x ∈ F) (hFm : MeasurableSet F)
    {X Y : Set V} (hY : MeasurableSet Y) {c : V} (hsub : ∀ y ∈ X, y + c ∈ Y) :
    μ (F ∩ (X + (Λ : Set V))) ≤ μ (F ∩ (Y + (Λ : Set V))) := by
  have : VAddInvariantMeasure Λ V μ := inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup V μ)
  set Fc : Set V := (fun y ↦ y + (-c)) ⁻¹' F with hFc
  have hFcm : MeasurableSet Fc := hFm.preimage (measurable_id.add_const _)
  have hFcfd : ∀ x : V, ∃! v : Λ, (v : V) + x ∈ Fc := by
    intro x
    obtain ⟨u, hu, huq⟩ := hF (x + (-c))
    refine ⟨u, ?_, fun w hw ↦ huq w ?_⟩
    · change ((u : V) + x) + (-c) ∈ F
      rw [show ((u : V) + x) + (-c) = (u : V) + (x + (-c)) from by abel]
      exact hu
    · change (w : V) + (x + (-c)) ∈ F
      rw [show (w : V) + (x + (-c)) = ((w : V) + x) + (-c) from by abel]
      exact hw
  have hstep : μ (F ∩ (X + (Λ : Set V)))
      = μ (Fc ∩ ((fun y ↦ y + (-c)) ⁻¹' (X + (Λ : Set V)))) := by
    rw [hFc, ← Set.preimage_inter]
    exact (measure_preimage_add_right μ (-c) _).symm
  rw [hstep]
  have hsub' : (fun y ↦ y + (-c)) ⁻¹' (X + (Λ : Set V)) ⊆ Y + (Λ : Set V) := by
    rintro y ⟨a, ha, l, hl, he⟩
    refine ⟨a + c, hsub a ha, l, hl, ?_⟩
    simp only at he ⊢
    linear_combination (norm := abel) he
  refine le_trans (measure_mono (Set.inter_subset_inter_right _ hsub')) (le_of_eq ?_)
  have h1 : IsAddFundamentalDomain Λ F μ := IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
  have h2 : IsAddFundamentalDomain Λ Fc μ :=
    IsAddFundamentalDomain.mk' hFcm.nullMeasurableSet hFcfd
  rw [Set.inter_comm Fc, Set.inter_comm F]
  exact h2.measure_set_eq h1 (measurableSet_add_lattice Λ hY) (preimage_vadd_add_lattice Λ)

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [MeasurableSpace W] [BorelSpace W]
  [FiniteDimensional ℝ W] in
/-- Dilating a set dilates its slices, the slice being taken at the dilated point. -/
private theorem slice_smul (A : Set (V × W)) {s : ℝ} (hs : s ≠ 0) (z : W) :
    {y | (y, s • z) ∈ s • A} = s • {y | (y, z) ∈ A} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_smul_set]
  constructor
  · rintro ⟨p, hp, he⟩
    have h₂ : s • p.2 = s • z := congrArg Prod.snd he
    have h₂' : p.2 = z := smul_right_injective W hs h₂
    exact ⟨p.1, by rwa [← h₂'], congrArg Prod.fst he⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x, z), hx, rfl⟩

/-- **The scaling estimate** (Cassels, Chapter VIII, §4.2, the displays (12) and (14) in the proof
of Theorem IV). For a convex set `A` and `s ≥ 1`, the quotient measure of `s • A` over `Λ × 0` is at
least `s ^ dim W` times that of `A`.

The factor is `s ^ dim W` and not `s ^ dim (V × W)` because the Fubini decomposition scales only
the `W`-direction: on each slice the dilation is replaced by a translation, which the quotient
measure over `Λ` does not see. ⚠ The translating vector depends on the slice, so no map of `V × W`
realizes this comparison; see the implementation notes. -/
theorem measure_inter_add_prod_smul_le (μV : Measure V) [μV.IsAddHaarMeasure] (μW : Measure W)
    [μW.IsAddHaarMeasure] (Λ : Submodule ℤ V) [Countable Λ] {F : Set V}
    (hF : ∀ x : V, ∃! v : Λ, (v : V) + x ∈ F) (hFm : MeasurableSet F) {A : Set (V × W)}
    (hAm : MeasurableSet A) (hAc : Convex ℝ A) {s : ℝ} (hs : 1 ≤ s) :
    ENNReal.ofReal (s ^ finrank ℝ W) * (μV.prod μW)
        ((F ×ˢ (univ : Set W)) ∩ (A + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W)))) ≤
      (μV.prod μW) ((F ×ˢ (univ : Set W)) ∩
        ((s • A) + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W)))) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hsAm : MeasurableSet (s • A) := hAm.const_smul₀ s
  rw [measure_inter_add_prod_eq_lintegral μV μW Λ hFm hAm,
    measure_inter_add_prod_eq_lintegral μV μW Λ hFm hsAm]
  set f : W → ℝ≥0∞ := fun z ↦ μV (F ∩ ({y | (y, z) ∈ s • A} + (Λ : Set V))) with hf
  have hsubst : ∫⁻ z, f z ∂μW = ENNReal.ofReal (s ^ finrank ℝ W) * ∫⁻ z, f (s • z) ∂μW := by
    have hne : s ≠ 0 := hs0.ne'
    have hmap : μW.map (fun z : W ↦ s • z) = ENNReal.ofReal |(s ^ finrank ℝ W)⁻¹| • μW :=
      map_addHaar_smul μW hne
    have h1 : ∫⁻ z, f z ∂(μW.map (fun z : W ↦ s • z)) = ∫⁻ z, f (s • z) ∂μW := by
      simpa using lintegral_map_equiv (μ := μW) f (MeasurableEquiv.smul₀ s hne)
    rw [hmap, lintegral_smul_measure,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s ^ finrank ℝ W)⁻¹)] at h1
    rw [← h1, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      mul_inv_cancel₀ (by positivity)]
    simp
  rw [hsubst]
  refine mul_le_mul_right (lintegral_mono fun z ↦ ?_) _
  set X : Set V := {y | (y, z) ∈ A} with hX
  have hXm : MeasurableSet X := hAm.preimage measurable_prodMk_right
  have hXc : Convex ℝ X := by
    intro y₁ h₁ y₂ h₂ a b ha hb hab
    change (a • y₁ + b • y₂, z) ∈ A
    rw [show (a • y₁ + b • y₂, z) = a • (y₁, z) + b • (y₂, z) from
      Prod.ext rfl (show z = a • z + b • z by rw [← add_smul, hab, one_smul])]
    exact hAc h₁ h₂ ha hb hab
  have hfz : f (s • z) = μV (F ∩ ((s • X) + (Λ : Set V))) := by
    rw [hf]
    simp only
    rw [slice_smul A hs0.ne' z, ← hX]
  rw [hfz]
  rcases Set.eq_empty_or_nonempty X with hemp | ⟨y₀, hy₀⟩
  · rw [hemp, Set.empty_add, Set.smul_set_empty, Set.empty_add]
  · refine measure_inter_add_le μV Λ hF hFm (hXm.const_smul₀ s) (c := (s - 1) • y₀) ?_
    intro y hy
    rw [show y + (s - 1) • y₀ = s • (s⁻¹ • y + (1 - s⁻¹) • y₀) from by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, smul_smul,
        show s * (1 - s⁻¹) = s - 1 from by field_simp]]
    refine Set.smul_mem_smul_set (hXc hy hy₀ (by positivity) ?_ (by ring))
    simp only [sub_nonneg]
    rw [inv_le_one₀ hs0]
    exact hs

end Product

section Space

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A lattice lies in its own `ℝ`-span. -/
private theorem le_restrictScalars_span (Λ : Submodule ℤ E) :
    Λ ≤ (Submodule.span ℝ (Λ : Set E)).restrictScalars ℤ := fun _ hx ↦ Submodule.subset_span hx

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A `ℤ`-submodule spans its own `ℝ`-span: the `span_top` half of being a lattice there. -/
private theorem span_comap_span_eq_top (Λ : Submodule ℤ E) :
    Submodule.span ℝ ((ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :
      Set ↥(Submodule.span ℝ (Λ : Set E))) = ⊤ := by
  set V : Submodule ℝ E := Submodule.span ℝ (Λ : Set E) with hV
  have himg : V.subtype '' ((ZLattice.comap ℝ Λ V.subtype) : Set ↥V) = (Λ : Set E) := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ hy, fun hx ↦ ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩⟩
  have hmap : Submodule.map V.subtype
      (Submodule.span ℝ ((ZLattice.comap ℝ Λ V.subtype) : Set ↥V)) = V := by
    rw [Submodule.map_span, himg, ← hV]
  exact Submodule.map_injective_of_injective V.subtype_injective
    (hmap.trans (Submodule.map_subtype_top V).symm)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The lattice and its copy inside its own span are `ℤ`-linearly equivalent. -/
private def comapSpanEquiv (Λ : Submodule ℤ E) :
    (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) ≃ₗ[ℤ] Λ :=
  Submodule.comapSubtypeEquivOfLe (le_restrictScalars_span Λ)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A discrete `ℤ`-submodule of a finite-dimensional real normed space is countable.** Mathlib
has this for a `ZLattice`; a discrete submodule of smaller rank is a `ZLattice` in its own span. -/
theorem countable_of_discreteTopology (Λ : Submodule ℤ E) [DiscreteTopology Λ] : Countable Λ := by
  have hdisc : DiscreteTopology (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
    ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective
  have hzl : IsZLattice ℝ (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
    ⟨span_comap_span_eq_top Λ⟩
  exact Countable.of_equiv _ (comapSpanEquiv Λ).toEquiv

/-- **The scaling estimate for a lattice of arbitrary rank in a single space**, with the slab
produced rather than assumed: some measurable set `F` is a fundamental domain for `Λ` and, for
every convex `A` and every `s ≥ 1`, the quotient measure of `s • A` modulo `Λ` is at least
`s ^ (n - rank Λ)` times that of `A`.

This is Cassels' normalization of his Chapter VIII, Theorem IV made intrinsic: he transforms the
lattice to `ℤ ^ n` linearly, and the transformation is here the choice of a complement `W` of the
span of `Λ`, along which the fundamental parallelepiped of `Λ` in that span is extended to the
slab `F`. The exponent is `dim W`. -/
theorem exists_isAddFundamentalDomain_measure_smul_le (μ : Measure E) [μ.IsAddHaarMeasure]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] :
    ∃ F : Set E, MeasurableSet F ∧ (∀ x : E, ∃! v : Λ, (v : E) + x ∈ F) ∧
      ∀ A : Set E, MeasurableSet A → Convex ℝ A → ∀ s : ℝ, 1 ≤ s →
        ENNReal.ofReal (s ^ (finrank ℝ E - finrank ℤ Λ)) * μ (F ∩ (A + (Λ : Set E))) ≤
          μ (F ∩ ((s • A) + (Λ : Set E))) := by
  have hcount : Countable Λ := countable_of_discreteTopology Λ
  set V : Submodule ℝ E := Submodule.span ℝ (Λ : Set E) with hV
  obtain ⟨W, hcompl⟩ := V.exists_isCompl
  set e : (↥V × ↥W) ≃L[ℝ] E :=
    (Submodule.prodEquivOfIsCompl V W hcompl).toContinuousLinearEquiv with he
  have hea : ∀ p : ↥V × ↥W, e p = (p.1 : E) + (p.2 : E) := fun _ ↦ rfl
  set Λ' : Submodule ℤ ↥V := ZLattice.comap ℝ Λ V.subtype with hΛ'
  have hmemΛ' : ∀ y : ↥V, y ∈ Λ' ↔ (y : E) ∈ Λ := fun _ ↦ Iff.rfl
  have hΛV : ∀ v : E, v ∈ Λ → v ∈ V := fun _ hv ↦ Submodule.subset_span hv
  have hdisc : DiscreteTopology Λ' :=
    ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective
  have hzl : IsZLattice ℝ Λ' := ⟨span_comap_span_eq_top Λ⟩
  have hcount' : Countable Λ' := inferInstance
  -- the fundamental parallelepiped of `Λ` inside its span
  have hmodfin : Module.Finite ℤ Λ' := ZLattice.module_finite ℝ Λ'
  have hfree : Module.Free ℤ Λ' := ZLattice.module_free ℝ Λ'
  set bZ : Basis (Module.Free.ChooseBasisIndex ℤ Λ') ℤ Λ' := Module.Free.chooseBasis ℤ Λ' with hbZ
  set bR : Basis (Module.Free.ChooseBasisIndex ℤ Λ') ℝ ↥V := bZ.ofZLatticeBasis ℝ Λ' with hbR
  set FV : Set ↥V := ZSpan.fundamentalDomain bR with hFVdef
  have hFVm : MeasurableSet FV := ZSpan.fundamentalDomain_measurableSet bR
  have hFVfd : ∀ y : ↥V, ∃! v : Λ', (v : ↥V) + y ∈ FV := fun y ↦
    existsUnique_of_eq (bZ.ofZLatticeBasis_span ℝ)
      (ZSpan.exist_unique_vadd_mem_fundamentalDomain bR y)
  -- the slab in `E`
  set F : Set E := e '' (FV ×ˢ (univ : Set ↥W)) with hFdef
  have hmemF : ∀ y : E, y ∈ F ↔ (e.symm y).1 ∈ FV := by
    intro y
    rw [hFdef]
    exact ⟨fun ⟨p, hp, hpy⟩ ↦ by simpa [← hpy] using hp.1,
      fun hy ↦ ⟨e.symm y, ⟨hy, Set.mem_univ _⟩, by simp⟩⟩
  have hFm : MeasurableSet F := by
    rw [show F = (e.symm : E → ↥V × ↥W) ⁻¹' (FV ×ˢ (univ : Set ↥W)) from by
      ext y; rw [hmemF y]; simp]
    exact (hFVm.prod MeasurableSet.univ).preimage e.symm.continuous.measurable
  have hπ : ∀ (v : Λ) (x : E),
      (e.symm ((v : E) + x)).1 = (⟨(v : E), hΛV _ v.2⟩ : ↥V) + (e.symm x).1 := by
    intro v x
    have hev : e.symm (v : E) = ((⟨(v : E), hΛV _ v.2⟩ : ↥V), (0 : ↥W)) := by
      refine e.injective ?_
      rw [ContinuousLinearEquiv.apply_symm_apply, hea]
      simp
    rw [map_add, hev]
    rfl
  have hFfd : ∀ x : E, ∃! v : Λ, (v : E) + x ∈ F := by
    intro x
    obtain ⟨u, hu, huq⟩ := hFVfd (e.symm x).1
    have huΛ : ((u : ↥V) : E) ∈ Λ := u.2
    refine ⟨⟨((u : ↥V) : E), huΛ⟩, ?_, ?_⟩
    · change ((u : ↥V) : E) + x ∈ F
      rw [hmemF, hπ ⟨((u : ↥V) : E), huΛ⟩ x,
        show (⟨((u : ↥V) : E), hΛV _ huΛ⟩ : ↥V) = (u : ↥V) from Subtype.ext rfl]
      exact hu
    · intro w hw
      have hw2 : (w : E) + x ∈ F := hw
      rw [hmemF, hπ w x] at hw2
      have hw' : (⟨⟨(w : E), hΛV _ w.2⟩, w.2⟩ : Λ') = u := huq _ hw2
      exact Subtype.ext (congrArg (fun z : Λ' ↦ ((z : ↥V) : E)) hw')
  refine ⟨F, hFm, hFfd, ?_⟩
  intro A hAm hAc s hs
  -- the transport of the Haar measure to the product
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ∀ S : Set E, MeasurableSet S →
      μ S = c * ((addHaar : Measure ↥V).prod (addHaar : Measure ↥W)) (e ⁻¹' S) := by
    set ν : Measure (↥V × ↥W) := μ.map e.symm with hν
    have hνHaar : ν.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
    obtain ⟨c, hcν⟩ : ∃ c : ℝ≥0∞, ν = c • ((addHaar : Measure ↥V).prod (addHaar : Measure ↥W)) :=
      ⟨addHaarScalarFactor ν ((addHaar : Measure ↥V).prod (addHaar : Measure ↥W)),
        isAddLeftInvariant_eq_smul _ _⟩
    refine ⟨c, fun S hS ↦ ?_⟩
    have h1 : ν (e ⁻¹' S) = μ S := by
      rw [hν, Measure.map_apply e.symm.continuous.measurable
        (hS.preimage e.continuous.measurable)]
      congr 1
      ext y
      simp
    rw [← h1, hcν]
    simp
  -- the transport of the sets
  have hpreadd : ∀ X Y : Set E, e ⁻¹' (X + Y) = (e ⁻¹' X) + (e ⁻¹' Y) := by
    intro X Y
    ext p
    simp only [Set.mem_preimage, Set.mem_add]
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      refine ⟨e.symm x, by simpa using hx, e.symm y, by simpa using hy, ?_⟩
      rw [← map_add, hxy]
      exact e.symm_apply_apply p
    · rintro ⟨p₁, h₁, p₂, h₂, rfl⟩
      exact ⟨e p₁, h₁, e p₂, h₂, (map_add e p₁ p₂).symm⟩
  have hpresmul : ∀ (t : ℝ) (X : Set E), e ⁻¹' (t • X) = t • (e ⁻¹' X) := by
    intro t X
    ext p
    simp only [Set.mem_preimage, Set.mem_smul_set]
    constructor
    · rintro ⟨a, ha, hae⟩
      refine ⟨e.symm a, by simpa using ha, ?_⟩
      rw [← map_smul, hae]
      exact e.symm_apply_apply p
    · rintro ⟨q, hq, rfl⟩
      exact ⟨e q, hq, (map_smul e t q).symm⟩
  have hpreΛ : e ⁻¹' (Λ : Set E) = ((Λ'.prod (⊥ : Submodule ℤ ↥W)) : Set (↥V × ↥W)) := by
    ext p
    simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.mem_prod, Submodule.mem_bot, hea]
    constructor
    · intro hp
      have hpV : (p.1 : E) + (p.2 : E) ∈ V := hΛV _ hp
      have h2 : (p.2 : E) ∈ V := by
        rw [show (p.2 : E) = ((p.1 : E) + (p.2 : E)) - (p.1 : E) from by abel]
        exact Submodule.sub_mem _ hpV p.1.2
      have h3 : p.2 = 0 := by
        have hmem : (p.2 : E) ∈ V ⊓ W := ⟨h2, p.2.2⟩
        rw [hcompl.inf_eq_bot] at hmem
        exact Subtype.ext (by simpa using hmem)
      refine ⟨(hmemΛ' p.1).2 ?_, h3⟩
      rw [show ((p.1 : ↥V) : E) = (p.1 : E) + (p.2 : E) from by
        rw [show (p.2 : E) = 0 from by rw [h3]; simp]; abel]
      exact hp
    · rintro ⟨h1, h2⟩
      rw [show (p.2 : E) = 0 from by rw [h2]; simp, add_zero]
      exact (hmemΛ' p.1).1 h1
  have hpreF : e ⁻¹' F = FV ×ˢ (univ : Set ↥W) := by
    ext p
    rw [Set.mem_preimage, hmemF]
    simp
  -- the rank bookkeeping
  have hr1 : finrank ℤ Λ = finrank ℝ ↥V := by
    rw [← ZLattice.rank ℝ Λ']
    exact ((comapSpanEquiv Λ).finrank_eq).symm
  have hr2 : finrank ℝ ↥V + finrank ℝ ↥W = finrank ℝ E :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  have hrank : finrank ℝ E - finrank ℤ Λ = finrank ℝ ↥W := by omega
  -- the comparison, transported
  have hsAm : MeasurableSet (s • A) := hAm.const_smul₀ s
  rw [hc _ (hFm.inter (measurableSet_add_lattice Λ hAm)),
    hc _ (hFm.inter (measurableSet_add_lattice Λ hsAm)), Set.preimage_inter, Set.preimage_inter,
    hpreF, hpreadd, hpreΛ, hpreadd, hpreΛ, hpresmul, hrank, mul_left_comm]
  exact mul_le_mul_right (measure_inter_add_prod_smul_le _ _ Λ' hFVfd hFVm
    (hAm.preimage e.continuous.measurable) (hAc.linear_preimage e.toLinearEquiv.toLinearMap) hs) c

/-- **Cassels' Chapter VIII, Theorem IV, in one step** (the display (14) of his proof). For a
convex set `A` on which congruence modulo the lattice `L` is congruence modulo the sublattice `Λ`,
dilating by `s ≥ 1` multiplies the measure of the image in `E ⧸ L` by at least
`s ^ (n - rank Λ)`.

This is the inductive step of Weyl's proof of the upper bound in Minkowski's second theorem: the
separation hypotheses are Cassels' Lemma 2 applied to `A = t • B`, and the exponent decreases by
one each time `t` passes a successive minimum. -/
theorem pow_mul_measure_inter_add_le (μ : Measure E) [μ.IsAddHaarMeasure] {Λ L : Submodule ℤ E}
    [DiscreteTopology Λ] [DiscreteTopology L] (hΛL : Λ ≤ L) {FL : Set E}
    (hL : ∀ x : E, ∃! v : L, (v : E) + x ∈ FL) (hmL : MeasurableSet FL) (hfin : μ FL ≠ ⊤)
    {A : Set E} (hAm : MeasurableSet A) (hAc : Convex ℝ A) {s : ℝ} (hs : 1 ≤ s)
    (hsepA : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ L → x - y ∈ Λ)
    (hsepB : ∀ x ∈ s • A, ∀ y ∈ s • A, x - y ∈ L → x - y ∈ Λ) :
    ENNReal.ofReal (s ^ (finrank ℝ E - finrank ℤ Λ)) * μ (FL ∩ (A + (L : Set E))) ≤
      μ (FL ∩ ((s • A) + (L : Set E))) := by
  have hcΛ : Countable Λ := countable_of_discreteTopology Λ
  have hcL : Countable L := countable_of_discreteTopology L
  obtain ⟨F, hFm, hFfd, hscale⟩ := exists_isAddFundamentalDomain_measure_smul_le μ Λ
  have hsAm : MeasurableSet (s • A) := hAm.const_smul₀ s
  rw [← measure_inter_add_eq_of_separated μ hΛL hFfd hL hFm hmL hfin hAm hsepA,
    ← measure_inter_add_eq_of_separated μ hΛL hFfd hL hFm hmL hfin hsAm hsepB]
  exact hscale A hAm hAc s hs

end Space

end ZLattice
