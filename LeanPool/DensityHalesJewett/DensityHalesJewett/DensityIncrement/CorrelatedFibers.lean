/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.Parameters
public import LeanPool.DensityHalesJewett.DensityHalesJewett.GrahamRothschild
public import LeanPool.DensityHalesJewett.DensityHalesJewett.UniformFibers
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Correlated fibers and many parameter lines

Uniformization and line canonization produce a subspace whose parameter-cube lines all have dense
common fibers; averaging over fixed suffixes then yields either an immediate density increment or a
suffix with many complete restricted-alphabet lines.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- A finite word family contains no complete combinatorial line. -/
def IsLineFree {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ∃ a, l a ∉ A

/-- Pull a word family back to the parameter cube of a subspace. -/
noncomputable def pullback {η α ι : Type*} [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι → α)) : Finset (η → α) :=
  parameterPreimage V A

/-- Pullback density agrees with the subspace-relative density. -/
lemma dens_pullback {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    (pullback V A).dens = Subspace.relativeDensity V A := by
  unfold pullback parameterPreimage Subspace.relativeDensity
  congr 1
  ext x
  simp only [mem_filter]

variable {N : ℕ}

/-- Graham--Rothschild applied to a subspace with uniformly dense fibers: a subspace of it on which
either every restricted-alphabet line has common-suffix density at least `θ`, or every one has
common-suffix density below `θ`. -/
lemma exists_uniform_fibers_and_homogeneous_lines {k M L : ℕ} {δ : ℝ} {ι κ : Type*}
    [Fintype (κ → Fin (k + 1))] [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L) {A : Finset (ι ⊕ κ → Fin (k + 1))}
    {U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι}
    (hU : ∀ x, δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
      ((∀ l : Combinatorics.Line (Fin k) (Fin M),
          Parameters.θ k N δ ≤
            ((univ.filter fun y ↦
              ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
        (∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((univ.filter fun y ↦
            ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k N δ)) := by
  classical
  let := Subspace.lineFintype (k + 1) L
  obtain ⟨R, hR⟩ := GrahamRothschild.exists_mapLine_mem_or_notMem (by simpa using hGR)
    (univ.filter fun l : Combinatorics.Line (Fin (k + 1)) (Fin L) ↦ Parameters.θ k N δ ≤
      ((univ.filter fun y ↦ ∀ a : Fin k, Sum.elim (U (l a.castSucc)) y ∈ A).dens : ℝ))
  refine ⟨Subspace.compose U R, ?_, ?_⟩
  · intro x
    simpa using hU (R x)
  · refine hR.imp ?_ ?_
    · intro h l
      simpa [Combinatorics.Line.map_apply] using h (l.map Fin.castSucc)
    · intro h l
      simpa [Combinatorics.Line.map_apply] using h (l.map Fin.castSucc)

/-- Restricting the parameter directions of a good correlated-fibers subspace preserves its
uniform fiber and common-line-fiber estimates. -/
lemma restrict_correlated_fibers_subspace {k m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M)
    {δ : ℝ} {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    {A : Finset (ι ⊕ κ → Fin (k + 1))}
    {W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι}
    (hfibers : ∀ x,
      δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k N δ ≤
        ((univ.filter fun y ↦
          ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k N δ ≤
          ((univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  let R := Subspace.repeatInitial (Fin (k + 1)) hm hmM
  let V := Subspace.compose W R
  refine ⟨V, ?_, ?_⟩
  · intro x
    simpa [V, Subspace.compose_apply] using hfibers (R x)
  · intro l
    let Rk := Subspace.repeatInitial (Fin k) hm hmM
    simpa [V, R, Rk, Subspace.compose_apply, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using
        hlines (Subspace.composeLine Rk l)

/-- Uniformly dense fibers force a positive-density set of suffixes whose restricted parameter
slice has density at least `δ / 4`. -/
lemma dense_suffixes_of_uniform_fibers {k M : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    {A : Finset (ι ⊕ κ → Fin (k + 1))}
    {W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι}
    (hfibers : ∀ x,
      δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    δ / 4 ≤
      ((univ.filter fun y : κ → Fin (k + 1) ↦
        δ / 4 ≤
          ((univ.filter fun x : Fin M → Fin k ↦
            Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hη₀ := Parameters.η_pos k N hδ₀
  have hηδ := Parameters.η_le_δ_div_six k N δ
  refine le_trans ?_ (density_ge_threshold (fun y ↦ by exact_mod_cast dens_le_one)
    (by nlinarith : δ / 4 < δ - Parameters.η k N δ ^ 2 / 2)
    ((le_expect univ_nonempty fun x _ ↦ hfibers (Fin.castSucc ∘ x)).trans_eq
      (Subspace.average_restrictedParameterSlice A W).symm))
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Density Hales--Jewett in every dense suffix slice, followed by pigeonhole on lines, produces
one parameter line shared by a set of suffixes of density at least `θ`. -/
lemma exists_popular_line_of_dense_suffixes {k M : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hN : IsDHJDimension k (δ / 4) (N + 1)) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hM : N + 1 ≤ M)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    {A : Finset (ι ⊕ κ → Fin (k + 1))}
    {W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι}
    (hfibers : ∀ x,
      δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k N δ ≤
        ((univ.filter fun y ↦
          ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  let R := Subspace.repeatInitial (Fin (k + 1)) (Nat.le_add_left 1 N) hM
  let Rk := Subspace.repeatInitial (Fin k) (Nat.le_add_left 1 N) hM
  obtain ⟨l, hl⟩ := Subspace.exists_line_forall_mem_slices (by omega) hN
    (fun y ↦ univ.filter fun x ↦ Sum.elim (Subspace.compose W R (Fin.castSucc ∘ x)) y ∈ A)
    (by positivity) (dense_suffixes_of_uniform_fibers hk hδ₀ hδ₁ (W := Subspace.compose W R)
      fun x ↦ by simpa using hfibers (R x))
    fun y hy ↦ (mem_filter.1 hy).2
  refine ⟨Subspace.composeLine Rk l, hl.trans (mod_cast dens_le_dens ?_)⟩
  intro y
  simp [Subspace.compose_apply, Subspace.composeLine_apply, Subspace.repeatInitial_map, R, Rk]

/-- Every parameter-cube line in a suitable subspace has a dense common fiber.

Graham--Rothschild makes the lines of a subspace of dimension `M` all dense or all sparse, and
`exists_popular_line_of_dense_suffixes` rules out the second case. The subspace is then restricted
to `m` parameters. -/
lemma exists_subspace_correlated_fibers {k M L : ℕ} (hk : 2 ≤ k)
    {m : ℕ} (hm : 1 ≤ m)
    {δ : ℝ} (hN : IsDHJDimension k (δ / 4) (N + 1)) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))] [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hmM : m ≤ M) (hNM : N + 1 ≤ M)
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L)
    {A : Finset (ι ⊕ κ → Fin (k + 1))} {U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι}
    (hU : ∀ x, δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k N δ ≤
          ((univ.filter fun y ↦ ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  obtain ⟨W, hW, hgood | hsparse⟩ := exists_uniform_fibers_and_homogeneous_lines hGR hU
  · exact restrict_correlated_fibers_subspace hm hmM hW hgood
  · obtain ⟨l, hl⟩ := exists_popular_line_of_dense_suffixes hk hN hδ₀ hδ₁ hNM hW
    exact absurd hl (hsparse l).not_ge

/-- The pullback of a word family to a subspace after fixing the suffix coordinates. -/
def suffixPullback {α η ι κ : Type*} [Fintype (η → α)]
    [DecidableEq (ι ⊕ κ → α)] (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι ⊕ κ → α)) (y : κ → α) : Finset (η → α) :=
  univ.filter fun x ↦ Sum.elim (V x) y ∈ A

/-- The parameter lines whose first-`k` points belong to a word family at a fixed suffix. -/
def suffixLines {k m : ℕ} {ι κ : Type*}
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (y : κ → Fin (k + 1)) :
    Finset (Combinatorics.Line (Fin k) (Fin m)) :=
  univ.filter fun l ↦ ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A

/-- Pointwise fiber lower bounds imply the corresponding average lower bound for fixed-suffix
pullbacks, by double counting. -/
lemma average_suffixPullback_lower {α η ι κ : Type*} [Nonempty α] [Fintype (η → α)]
    [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {V : Combinatorics.Subspace η α ι} {A : Finset (ι ⊕ κ → α)} {r : ℝ}
    (hV : ∀ x, r ≤ ((fiber A (V x)).dens : ℝ)) :
    r ≤ 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) :=
  (le_expect univ_nonempty fun x _ ↦ hV x).trans_eq
    (Subspace.expect_dens_filter_comm fun x y ↦ Sum.elim (V x) y ∈ A)

/-- If a function has average at least `δ - η²/2` but never reaches `δ + η²/2`, then it is at
least `δ - 2η` on all but an `η`-fraction of its domain. -/
lemma density_near_average {X : Type*} [Fintype X] [Nonempty X]
    {f : X → ℝ} {δ η : ℝ} (hη₀ : 0 < η)
    (havg : δ - η ^ 2 / 2 ≤ 𝔼 x : X, f x)
    (hupper : ∀ x, f x < δ + η ^ 2 / 2) :
    1 - η ≤ ((univ.filter fun x ↦ δ - 2 * η ≤ f x).dens : ℝ) := by
  set H := univ.filter fun x ↦ δ - 2 * η ≤ f x
  have hf (x : X) : f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * Set.indicator H 1 x := by
    by_cases hx : x ∈ H
    · rw [Set.indicator_of_mem (by simpa using hx), Pi.one_apply, mul_one]
      linarith [hupper x]
    · rw [Set.indicator_of_notMem (by simpa using hx), mul_zero, add_zero]
      exact (not_le.1 (by simpa [H] using hx)).le
  have hexpect : 𝔼 x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * (H.dens : ℝ) := by
    refine (expect_le_expect fun x _ ↦ hf x).trans_eq ?_
    rw [expect_add_distrib, expect_const univ_nonempty, ← mul_expect, expect_indicator_one]
  by_contra! hH
  nlinarith [mul_le_mul_of_nonneg_left hH.le (by positivity : (0 : ℝ) ≤ η ^ 2 / 2 + 2 * η)]

/-- Dense common suffix fibers for every line give the same lower bound for the average
fixed-suffix line density, by double counting. -/
lemma average_suffixLines_lower {k m : ℕ} {ι κ : Type*}
    [Fintype (κ → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    {V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι}
    {A : Finset (ι ⊕ κ → Fin (k + 1))} {θ : ℝ}
    (hV : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      θ ≤ ((univ.filter fun y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    θ ≤ 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
  refine (le_expect univ_nonempty fun l _ ↦ hV l).trans_eq ?_
  unfold suffixLines
  exact Subspace.expect_dens_filter_comm _

/-- A function bounded above by one with average at least `θ` exceeds `θ/2` on a set of
density at least `θ/2`. -/
lemma density_half_threshold {X : Type*} [Fintype X] [Nonempty X]
    {f : X → ℝ} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hf₁ : ∀ x, f x ≤ 1) (havg : θ ≤ 𝔼 x : X, f x) :
    θ / 2 ≤ ((univ.filter fun x ↦ θ / 2 ≤ f x).dens : ℝ) := by
  refine le_trans ?_
    (density_ge_threshold hf₁ (by linarith) havg)
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - θ / 2)]
  nlinarith [sq_nonneg (θ / 2)]

/-- Two subsets of densities at least `1-η` and `θ/2` intersect when `η < θ/2`. -/
lemma exists_mem_inter_of_large_density {X : Type*} [Fintype X]
    {S T : Finset X} {η θ : ℝ}
    (hS : 1 - η ≤ (S.dens : ℝ)) (hT : θ / 2 ≤ (T.dens : ℝ))
    (hηθ : η < θ / 2) : ∃ x, x ∈ S ∧ x ∈ T := by
  classical
  by_contra! h
  have hunion : ((S ∪ T).dens : ℝ) = (S.dens : ℝ) + (T.dens : ℝ) := by
    exact_mod_cast dens_union_of_disjoint (disjoint_left.mpr h)
  linarith [(by exact_mod_cast dens_le_one : ((S ∪ T).dens : ℝ) ≤ 1)]

/-- Correlated fibers yield either a dense fixed suffix or a fixed suffix supporting many
complete parameter lines.

If no suffix pullback reaches density `δ + η²/2`, then all but an `η`-fraction of the suffixes
have pullback density at least `δ - 2η`, a `θ/2`-fraction support a `θ/2`-fraction of the lines,
and `η < θ/2` makes the two sets meet. -/
lemma exists_suffix_many_lines {k m : ℕ}
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (Fin m → Fin (k + 1))]
    [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    {A : Finset (ι ⊕ κ → Fin (k + 1))}
    {V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι}
    (hfiber : ∀ x, δ - Parameters.η k N δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      Parameters.θ k N δ ≤
        ((univ.filter fun y ↦
          ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    (∃ y, δ + Parameters.η k N δ ^ 2 / 2 ≤
      ((suffixPullback V A y).dens : ℝ)) ∨
    ∃ y, δ - 2 * Parameters.η k N δ ≤ ((suffixPullback V A y).dens : ℝ) ∧
      Parameters.θ k N δ / 2 ≤ ((suffixLines V A y).dens : ℝ) := by
  rw [or_iff_not_imp_left]
  intro hinc
  push Not at hinc
  obtain ⟨y, hy, hylines⟩ := exists_mem_inter_of_large_density
    (density_near_average (Parameters.η_pos k N hδ₀) (average_suffixPullback_lower hfiber) hinc)
    (density_half_threshold (Parameters.θ_pos k N hδ₀) (Parameters.θ_le_one k N hδ₁)
      (fun y ↦ by exact_mod_cast dens_le_one) (average_suffixLines_lower hlines))
    (Parameters.η_lt_θ_div_two k N hδ₀)
  exact ⟨y, (mem_filter.1 hy).2, (mem_filter.1 hylines).2⟩

/-- Fixing a suffix and transporting the coordinates turns the relative density into the density
of the suffix pullback. -/
lemma Subspace.relativeDensity_fixSuffixReindex {k m p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin (k + 1))) (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin p))
    (y : Fin q → Fin (k + 1)) :
    Subspace.relativeDensity (Subspace.fixSuffixReindex e V y) A =
      (suffixPullback V (Subspace.splitWords e A) y).dens := by
  rw [Subspace.relativeDensity, suffixPullback]
  congr 1
  ext x
  simp

/-- Fixing a suffix and transporting the coordinates turns the complete lines into the suffix
lines. -/
lemma Subspace.filter_fixSuffixReindex_eq_suffixLines {k m p q n : ℕ}
    [Fintype (Combinatorics.Line (Fin k) (Fin m))] (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin (k + 1))) (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin p))
    (y : Fin q → Fin (k + 1)) :
    (univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
      ∀ a, Subspace.fixSuffixReindex e V y (Fin.castSucc ∘ l a) ∈ A) =
      suffixLines V (Subspace.splitWords e A) y := by
  ext l
  simp [suffixLines]

/-- The ambient dimension required by the many-lines lemma `exists_subspace_many_lines`: large
enough to make the fibers uniform above a subspace on which Graham--Rothschild canonizes the lines
of a parameter cube of dimension `max m (N + 1)`. -/
noncomputable def manyLinesBound (k N m : ℕ) (δ : ℝ) : ℕ :=
  Subspace.variableCutFibersBound (k + 1)
    (max 1 (GrahamRothschild.bound (k + 1) 2 (max m (N + 1)))) (Parameters.η k N δ ^ 2 / 2)

/-- Either density has already increased on an `m`-subspace, or a dense slice contains a positive
proportion of all parameter-cube lines. -/
lemma exists_subspace_many_lines {k : ℕ} (hk : 2 ≤ k)
    {m : ℕ} [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (hm : 1 ≤ m) {δ : ℝ} (hN : IsDHJDimension k (δ / 4) (N + 1)) (hδ₀ : 0 < δ)
    (hδ₁ : δ ≤ 1)
    {n : ℕ} (hn : manyLinesBound k N m δ ≤ n)
    {A : Finset (Fin n → Fin (k + 1))} (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k N δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)) ∨
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ - 2 * Parameters.η k N δ ≤ (Subspace.relativeDensity V A : ℝ) ∧
      Parameters.θ k N δ / 2 ≤
        ((univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
          ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) := by
  classical
  obtain ⟨p, q, e, -, U, hU⟩ := Subspace.variableCutFibersSufficient_of_le (le_max_left _ _)
    (by positivity [Parameters.η_pos k N hδ₀]) hn A
  obtain ⟨W, hWfiber, hWlines⟩ := exists_subspace_correlated_fibers hk hm hN hδ₀ hδ₁
    (M := max m (N + 1)) (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
    (A := Subspace.splitWords e A) (U := U) fun x ↦ by linarith [hU x]
  obtain ⟨y, hy⟩ | ⟨y, hy, hylines⟩ := exists_suffix_many_lines hδ₀ hδ₁ hWfiber hWlines
  · exact .inl ⟨Subspace.fixSuffixReindex e W y, by
      rwa [Subspace.relativeDensity_fixSuffixReindex]⟩
  · exact .inr ⟨Subspace.fixSuffixReindex e W y, by
      rwa [Subspace.relativeDensity_fixSuffixReindex], by
      rwa [Subspace.filter_fixSuffixReindex_eq_suffixLines]⟩

end DensityHalesJewett
