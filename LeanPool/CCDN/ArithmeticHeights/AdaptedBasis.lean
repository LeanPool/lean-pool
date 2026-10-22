/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# A lattice basis adapted to a flag

Let `L` be a discrete `ℤ`-submodule of a finite-dimensional real normed space `E`, and let
`v 0, …, v (n - 1)` be `ℝ`-linearly independent vectors of `L`, with `n = finrank ℝ E`. This file
builds a `ℤ`-basis `b 0, …, b (n - 1)` of `L` adapted to the flag the `v i` span: for every `j`,
the first `j` members of `b` are a `ℤ`-basis of `L ∩ span ℝ (v 0, …, v (j - 1))`.

## Main definitions

* `ZLattice.flagPart`: the `j`-th step `L ∩ span ℝ (v 0, …, v (j - 1))` of the flag, as a
  `ℤ`-submodule. The construction below is an induction along it, and so is the basis from the
  successive minima of Layer 4.6.

## Main results

* `ZLattice.exists_basis_adapted`: the adapted basis, stated both integrally — the `ℤ`-span of the
  first `j` basis vectors is exactly the part of `L` in the span of the first `j` of the `v i` —
  and in the weaker `ℝ`-form, that the two flags of subspaces coincide.
* `ZLattice.exists_basis_mem_span_int_of_mem_span_real`: the consequence the geometry of numbers
  uses, that a lattice point in the span of the first `j` of the `v i` is an *integer* combination
  of the first `j` basis vectors.
* `ZLattice.exists_extending`: the induction step in isolation — across a saturated step of rank
  one, a single vector `y` generates the quotient, in the form `Basis.mkFinSnocOfLE` consumes.
* `ZLattice.extending_congr`: that generating vector is determined only modulo the smaller
  module, which is the freedom Layer 4.6 spends on making the new basis vector short.
* `ZLattice.discreteTopology_of_le` and `ZLattice.finrank_int_eq_finrank_real`: the two facts about
  a submodule of a discrete lattice that the construction rests on, stated at arbitrary rank — it
  is discrete, and its `ℤ`-rank is the `ℝ`-dimension of its span. Minkowski's second theorem needs
  both for the sublattices cut out by the flag.

## Implementation notes

The construction is the modern one and not Cassels': the part `flagPart L v j` of `L` in the
`j`-th subspace of the flag is saturated in `flagPart L v (j + 1)` — no nonzero multiple of a
lattice point lies in it unless the point does, because the subspaces are `ℝ`-subspaces — so the
quotient is finitely generated and torsion-free, hence free, and its rank is `1` by the
rank-nullity theorem. A generator of that quotient extends a basis of `flagPart L v j` to a basis
of `flagPart L v (j + 1)` through Mathlib's `Basis.mkFinSnocOfLE`, and `n` steps reach `L` itself.

⚠ **All the analysis is in one rank computation.** Discreteness is used twice: to know that the
parts of `L` are finitely generated over `ℤ`, which is Mathlib's
`instModuleFinite_of_discrete_submodule`, and — indispensably — for
`finrank ℤ (flagPart L v j) = finrank ℝ (span ℝ (flagPart L v j))`, which is Mathlib's
`Real.finrank_eq_int_finrank_of_discrete`. A non-discrete subgroup such as `ℤ + ℤ √2 ⊆ ℝ` is
finitely generated but has `ℤ`-rank larger than the dimension of its span, and then the quotients
above are free of rank `> 1` and no single vector extends the basis. The induction step is
therefore stated with no topology at all: it asks for the rank as a hypothesis.

⚠ **`IsZLattice ℝ L` is not needed.** The independent family already spans `E` over `ℝ`, so a
lattice that contains it spans `E`; asking for the instance would be asking for a consequence of
the hypotheses.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter I,
Theorem I: for a sublattice `Λ` of a lattice `M` and a basis `a 1, …, a n` of `Λ`, a basis
`b 1, …, b n` of `M` with `a i = ∑_{j ≤ i} v i j • b j` and `v i i ≠ 0` (part B; part A is the
converse, the Hermite normal form of a sublattice). That triangular shape is the `ℝ`-form below,
and the integral form follows from it because the `b i` are a basis of `M`.

This is the lattice content of Chapter VIII, Lemma 2 — the basis such that `F x < λ i` forces `x`
to be an integer combination of `b 1, …, b (i - 1)` — which is Cassels' Theorem I of Chapter I
applied to the family of Lemma 1, the family realizing the successive minima.

This is infrastructure for Layers 4.2 and 4.6 of the `ArithmeticHeights` roadmap.
-/

public section

open Module Set Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ZLattice

/-! ### Discreteness and rank -/

omit [NormedSpace ℝ E] in
/-- A `ℤ`-submodule of a discrete one is discrete: the inclusion is a continuous injection. This
is stated for a submodule of arbitrary rank, which is what the sublattices cut out by a flag of
subspaces need; Mathlib's instances for lattices assume full rank. -/
theorem discreteTopology_of_le {L N : Submodule ℤ E} [DiscreteTopology L] (h : N ≤ L) :
    DiscreteTopology N := by
  refine DiscreteTopology.of_continuous_injective (f := fun x : N ↦ (⟨(x : E), h x.2⟩ : L))
    (continuous_subtype_val.subtype_mk _) fun x y hxy ↦ ?_
  have hxy' : (x : E) = (y : E) := congrArg (fun z : L ↦ (z : E)) hxy
  exact Subtype.ext hxy'

/-- The `ℤ`-rank of a submodule of a discrete lattice is the `ℝ`-dimension of its span. This is
the step discreteness is indispensable for: `ℤ + ℤ √2` has `ℤ`-rank two inside a line. -/
theorem finrank_int_eq_finrank_real [FiniteDimensional ℝ E] {L N : Submodule ℤ E}
    [DiscreteTopology L] (h : N ≤ L) : finrank ℤ N = finrank ℝ (span ℝ (N : Set E)) := by
  have hdisc : DiscreteTopology (span ℤ (N : Set E)) := by
    rw [Submodule.span_eq]
    exact discreteTopology_of_le h
  have h2 := Real.finrank_eq_int_finrank_of_discrete hdisc
  rw [Set.finrank, Set.finrank, Submodule.span_eq] at h2
  exact h2.symm

/-! ### The flag of an independent family -/

/-- The part of a lattice `L` inside the `ℝ`-span of the first `j` members of a family `v`: the
`j`-th step of the flag along which an adapted basis is built. -/
@[expose] def flagPart {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E) (j : ℕ) : Submodule ℤ E :=
  L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < j})).restrictScalars ℤ

theorem mem_flagPart {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E) (j : ℕ) {x : E} :
    x ∈ flagPart L v j ↔ x ∈ L ∧ x ∈ span ℝ (v '' {i : Fin n | (i : ℕ) < j}) :=
  Iff.rfl

theorem flagPart_le {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E) (j : ℕ) : flagPart L v j ≤ L :=
  inf_le_left

theorem flagPart_zero {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E) : flagPart L v 0 = ⊥ := by
  have hempty : {i : Fin n | (i : ℕ) < 0} = (∅ : Set (Fin n)) := by ext i; simp
  rw [flagPart, hempty]
  simp

theorem flagPart_mono {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E) {j k : ℕ} (hjk : j ≤ k) :
    flagPart L v j ≤ flagPart L v k := by
  rintro x ⟨hxL, hxW⟩
  exact ⟨hxL, span_mono (Set.image_mono fun i hi ↦ lt_of_lt_of_le hi hjk) hxW⟩

theorem mem_flagPart_of_lt {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E) (hvL : ∀ i, v i ∈ L)
    {i : Fin n} {j : ℕ} (hij : (i : ℕ) < j) : v i ∈ flagPart L v j :=
  ⟨hvL i, subset_span ⟨i, hij, rfl⟩⟩

/-- The steps of the flag span the subspaces they were cut out of: no `ℝ`-dimension is lost by
intersecting with the lattice, because the lattice already contains a spanning family. -/
theorem span_flagPart {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E) (hvL : ∀ i, v i ∈ L) (j : ℕ) :
    span ℝ ((flagPart L v j : Submodule ℤ E) : Set E) = span ℝ (v '' {i : Fin n | (i : ℕ) < j}) :=
  le_antisymm (span_le.2 fun _ hx ↦ hx.2) (span_le.2 (by
    rintro _ ⟨i, hi, rfl⟩
    exact subset_span (mem_flagPart_of_lt L v hvL hi)))

/-- **The steps of the flag are saturated.** A lattice point a nonzero multiple of which lies in
`flagPart L v j` lies there itself: the `j`-th subspace is an `ℝ`-subspace, so it is closed under
dividing by a nonzero integer. -/
theorem flagPart_saturated {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E) {c : ℤ} (hc : c ≠ 0)
    {j : ℕ} {z : E} (hz : z ∈ L) (hcz : c • z ∈ flagPart L v j) : z ∈ flagPart L v j := by
  rw [mem_flagPart]
  refine ⟨hz, ?_⟩
  have h1 : (c : ℝ) • z ∈ span ℝ (v '' {i : Fin n | (i : ℕ) < j}) := by
    rw [Int.cast_smul_eq_zsmul]
    exact ((mem_flagPart L v j).1 hcz).2
  have hz' : z = ((c : ℝ))⁻¹ • ((c : ℝ) • z) := by
    rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul]
  rw [hz']
  exact Submodule.smul_mem _ _ h1

/-- The `j`-th step of the flag has `ℤ`-rank `j`. This is where discreteness enters. -/
theorem finrank_flagPart [FiniteDimensional ℝ E] {n : ℕ} (L : Submodule ℤ E) [DiscreteTopology L]
    (v : Fin n → E) (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L) {j : ℕ} (hj : j ≤ n) :
    finrank ℤ (flagPart L v j) = j := by
  have hset : v '' {i : Fin n | (i : ℕ) < j} = Set.range (v ∘ Fin.castLE hj) := by
    rw [Set.range_comp, Fin.range_castLE]
  rw [finrank_int_eq_finrank_real (flagPart_le L v j), span_flagPart L v hvL j, hset,
    finrank_span_eq_card (hv.comp _ (Fin.castLE_injective hj)), Fintype.card_fin]

/-- The last step of the flag is the whole lattice. -/
theorem flagPart_eq_self [FiniteDimensional ℝ E] {n : ℕ} (L : Submodule ℤ E) (v : Fin n → E)
    (hn : n = finrank ℝ E) (hv : LinearIndependent ℝ v) : flagPart L v n = L := by
  have huniv : {i : Fin n | (i : ℕ) < n} = (Set.univ : Set (Fin n)) := by ext i; simp
  have hWn : span ℝ (v '' {i : Fin n | (i : ℕ) < n}) = ⊤ := by
    rw [huniv, Set.image_univ]
    exact hv.span_eq_top_of_card_eq_finrank' (by simp [hn])
  rw [flagPart, hWn, Submodule.restrictScalars_top, inf_top_eq]

/-! ### The induction step -/

omit [NormedSpace ℝ E] in
/-- **A generator of a saturated rank-one step.** If `N ≤ N'` are `ℤ`-submodules, `N'` has rank
one more than `N`, and `N` is saturated in `N'` — a point of `N'` a nonzero multiple of which lies
in `N` lies in `N` itself — then a single vector `y` of `N'` generates the quotient, in exactly
the two clauses `Basis.mkFinSnocOfLE` asks for.

No topology enters: the geometric situation supplies the rank and the saturation, and the rest is
that a finitely generated torsion-free `ℤ`-module of rank `1` is `ℤ`. -/
theorem exists_extending {N N' : Submodule ℤ E} (hle : N ≤ N') [Module.Finite ℤ N']
    (hsat : ∀ c : ℤ, c ≠ 0 → ∀ z ∈ N', c • z ∈ N → z ∈ N)
    (hrank : finrank ℤ N' = finrank ℤ N + 1) :
    ∃ y ∈ N', (∀ c : ℤ, ∀ x ∈ N, c • y + x = 0 → c = 0) ∧
      ∀ z ∈ N', ∃ c : ℤ, z + c • y ∈ N := by
  classical
  set P : Submodule ℤ N' := Submodule.comap N'.subtype N with hP
  have hPrank : finrank ℤ P = finrank ℤ N := by
    rw [hP, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq]
  have hQrank : finrank ℤ (N' ⧸ P) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank (R := ℤ) P
    omega
  have htf : Module.IsTorsionFree ℤ (N' ⧸ P) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c q hq ↦ ?_
    rcases eq_or_ne c 0 with rfl | hc
    · exact Or.inl rfl
    refine Or.inr ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hP,
      Submodule.mem_comap] at hq
    rw [Submodule.Quotient.mk_eq_zero, hP, Submodule.mem_comap]
    exact hsat c hc z z.2 (by simpa using hq)
  have hfree : Module.Free ℤ (N' ⧸ P) := Module.free_iff_isTorsionFree.2 htf
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (N' ⧸ P)) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hQrank]
  set e : Basis (Fin 1) ℤ (N' ⧸ P) :=
    (Module.Free.chooseBasis ℤ (N' ⧸ P)).reindex (Fintype.equivFinOfCardEq hcard) with he
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective P (e 0)
  have hyN : (y : E) ∉ N := by
    intro hmem
    have : Submodule.Quotient.mk y = (0 : N' ⧸ P) :=
      (Submodule.Quotient.mk_eq_zero P).2 (by rw [hP, Submodule.mem_comap]; exact hmem)
    rw [hy] at this
    exact e.ne_zero 0 this
  have hli : ∀ c : ℤ, ∀ x ∈ N, c • (y : E) + x = 0 → c = 0 := by
    intro c x hx hcx
    by_contra hc
    refine hyN (hsat c hc _ y.2 ?_)
    rw [eq_neg_of_add_eq_zero_left hcx]
    exact neg_mem hx
  have hsp : ∀ z ∈ N', ∃ c : ℤ, z + c • (y : E) ∈ N := by
    intro z hz
    refine ⟨-(e.repr (Submodule.Quotient.mk (⟨z, hz⟩ : N')) 0), ?_⟩
    have hz' : Submodule.Quotient.mk (⟨z, hz⟩ : N')
        = e.repr (Submodule.Quotient.mk (⟨z, hz⟩ : N')) 0 • e 0 := by
      conv_lhs => rw [← e.sum_repr (Submodule.Quotient.mk (⟨z, hz⟩ : N'))]
      simp
    have hzero : Submodule.Quotient.mk
        ((⟨z, hz⟩ : N') + (-(e.repr (Submodule.Quotient.mk (⟨z, hz⟩ : N')) 0)) • y)
          = (0 : N' ⧸ P) := by
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, hy, neg_smul, ← hz']
      simp
    simpa [hP] using (Submodule.Quotient.mk_eq_zero P).1 hzero
  exact ⟨(y : E), y.2, hli, hsp⟩

omit [NormedSpace ℝ E] in
/-- **The generator is determined only modulo the smaller module.** Moving `y` by an element of
`N` preserves both clauses of `ZLattice.exists_extending`, so the basis vector added at each step
may be shortened before it is added. This is the whole freedom Layer 4.6 has. -/
theorem extending_congr {N N' : Submodule ℤ E} {y y' : E} (hyy' : y' - y ∈ N)
    (hli : ∀ c : ℤ, ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ N', ∃ c : ℤ, z + c • y ∈ N) :
    (∀ c : ℤ, ∀ x ∈ N, c • y' + x = 0 → c = 0) ∧ ∀ z ∈ N', ∃ c : ℤ, z + c • y' ∈ N := by
  constructor
  · intro c x hx hcx
    refine hli c (c • (y' - y) + x) (N.add_mem (N.smul_mem c hyy') hx) ?_
    rw [← hcx, smul_sub]
    abel
  · intro z hz
    obtain ⟨c, hc⟩ := hsp z hz
    refine ⟨c, ?_⟩
    have heq : z + c • y' = z + c • y + c • (y' - y) := by
      rw [smul_sub]
      abel
    rw [heq]
    exact N.add_mem hc (N.smul_mem c hyy')

/-! ### The adapted basis -/

/-- **A `ℤ`-basis adapted to the flag of an independent family.** For `ℝ`-linearly independent
lattice vectors `v 0, …, v (n - 1)` spanning `E`, some `ℤ`-basis `b` of `L` has, for every `j`, its
first `j` members a `ℤ`-basis of the part of `L` in the span of `v 0, …, v (j - 1)`; in particular
the two flags of subspaces coincide.

This is Cassels' Chapter I, Theorem I, part B, in the form Chapter VIII, Lemma 2 uses it. Only
discreteness of `L` is assumed: `IsZLattice ℝ L` follows from the hypotheses on `v`. -/
theorem exists_basis_adapted [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {n : ℕ} (hn : n = finrank ℝ E) {v : Fin n → E} (hvL : ∀ i, v i ∈ L)
    (hv : LinearIndependent ℝ v) :
    ∃ b : Basis (Fin n) ℤ L,
      (∀ j : ℕ, span ℤ ((fun i ↦ ((b i : L) : E)) '' {i : Fin n | (i : ℕ) < j}) =
          L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < j})).restrictScalars ℤ) ∧
      ∀ j : ℕ, span ℝ ((fun i ↦ ((b i : L) : E)) '' {i : Fin n | (i : ℕ) < j}) =
          span ℝ (v '' {i : Fin n | (i : ℕ) < j}) := by
  classical
  have key : ∀ j, j ≤ n → ∃ b : Basis (Fin j) ℤ (flagPart L v j), ∀ k, k ≤ j →
      span ℤ ((fun i ↦ ((b i : flagPart L v j) : E)) '' {i : Fin j | (i : ℕ) < k})
        = flagPart L v k := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : flagPart L v 0 = ⊥ := flagPart_zero L v
      have : Subsingleton (flagPart L v 0) := by rw [h0]; infer_instance
      refine ⟨Basis.empty _, fun k hk ↦ ?_⟩
      obtain rfl : k = 0 := Nat.le_zero.1 hk
      rw [show {i : Fin 0 | (i : ℕ) < 0} = (∅ : Set (Fin 0)) from Set.eq_empty_of_isEmpty _,
        Set.image_empty, Submodule.span_empty, h0]
    | succ j ih =>
      intro hj
      obtain ⟨b, hb⟩ := ih (Nat.le_of_succ_le hj)
      have hdisc : DiscreteTopology (flagPart L v (j + 1)) :=
        discreteTopology_of_le (flagPart_le L v (j + 1))
      have hmono : flagPart L v j ≤ flagPart L v (j + 1) := flagPart_mono L v (Nat.le_succ j)
      obtain ⟨y, hyN, hli, hsp⟩ := exists_extending hmono
        (fun c hc z hz hcz ↦ flagPart_saturated L v hc (flagPart_le L v (j + 1) hz) hcz)
        (by rw [finrank_flagPart L v hv hvL hj,
              finrank_flagPart L v hv hvL (Nat.le_of_succ_le hj)])
      refine ⟨Basis.mkFinSnocOfLE b hmono y hyN hli hsp, fun k hk ↦ ?_⟩
      have hcs : ∀ i : Fin j,
          ((Basis.mkFinSnocOfLE b hmono y hyN hli hsp (Fin.castSucc i) :
              flagPart L v (j + 1)) : E) = ((b i : flagPart L v j) : E) := by
        intro i
        simp
      rcases eq_or_lt_of_le hk with rfl | hk'
      · have huniv : {i : Fin (j + 1) | (i : ℕ) < j + 1} = (Set.univ : Set (Fin (j + 1))) := by
          ext i; simpa using i.isLt
        rw [huniv, Set.image_univ,
          show (fun i ↦ ((Basis.mkFinSnocOfLE b hmono y hyN hli hsp i :
              flagPart L v (j + 1)) : E))
            = (flagPart L v (j + 1)).subtype ∘ Basis.mkFinSnocOfLE b hmono y hyN hli hsp from rfl,
          Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_subtype_top]
      · have hkj : k ≤ j := Nat.lt_succ_iff.1 hk'
        have hset : {i : Fin (j + 1) | (i : ℕ) < k}
            = Fin.castSucc '' {i : Fin j | (i : ℕ) < k} := by
          ext i
          simp only [Set.mem_ofPred_eq, Set.mem_image]
          constructor
          · intro hi
            exact ⟨⟨i, lt_of_lt_of_le hi hkj⟩, hi, by ext; rfl⟩
          · rintro ⟨i', hi', rfl⟩
            simpa using hi'
        rw [hset, ← Set.image_comp,
          show ((fun i ↦ ((Basis.mkFinSnocOfLE b hmono y hyN hli hsp i :
              flagPart L v (j + 1)) : E)) ∘ Fin.castSucc)
            = fun i ↦ ((b i : flagPart L v j) : E) from funext hcs]
        exact hb k hkj
  obtain ⟨b, hb⟩ := key n le_rfl
  have hmin : ∀ j : ℕ, {i : Fin n | (i : ℕ) < j} = {i : Fin n | (i : ℕ) < min j n} := by
    intro j
    ext i
    simp only [Set.mem_ofPred_eq, lt_min_iff, and_iff_left i.isLt]
  have hLn : flagPart L v n = L := flagPart_eq_self L v hn hv
  have hcoe : (fun i ↦ (((b.map (LinearEquiv.ofEq _ _ hLn)) i : L) : E))
      = fun i ↦ ((b i : flagPart L v n) : E) := by
    funext i
    simp
  refine ⟨b.map (LinearEquiv.ofEq _ _ hLn), fun j ↦ ?_, fun j ↦ ?_⟩
  · rw [hcoe, hmin j]
    exact hb _ (min_le_right j n)
  · rw [hcoe, hmin j, ← Submodule.span_span_of_tower (R := ℤ) (S := ℝ),
      hb _ (min_le_right j n)]
    exact span_flagPart L v hvL _

/-- **The integral form.** With the basis of `ZLattice.exists_basis_adapted`, a lattice point in
the `ℝ`-span of `v 0, …, v (j - 1)` is an *integer* combination of `b 0, …, b (j - 1)`. This is the
shape of Cassels' Chapter VIII, Lemma 2, and it is the shape the second theorem consumes. -/
theorem exists_basis_mem_span_int_of_mem_span_real [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] {n : ℕ} (hn : n = finrank ℝ E) {v : Fin n → E} (hvL : ∀ i, v i ∈ L)
    (hv : LinearIndependent ℝ v) :
    ∃ b : Basis (Fin n) ℤ L, ∀ (j : ℕ) (x : E), x ∈ L →
      x ∈ span ℝ (v '' {i : Fin n | (i : ℕ) < j}) →
        x ∈ span ℤ ((fun i ↦ ((b i : L) : E)) '' {i : Fin n | (i : ℕ) < j}) := by
  obtain ⟨b, hb, -⟩ := exists_basis_adapted L hn hvL hv
  exact ⟨b, fun j x hxL hxs ↦ (hb j).ge (Submodule.mem_inf.2
    ⟨hxL, (Submodule.restrictScalars_mem ℤ _ x).2 hxs⟩)⟩

end ZLattice
