/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Cone-separation roots for the convex-duality unification

The shared geometric kernel of mathematical finance's convex-duality pillar: finite-dimensional
separation of a closed convex **cone** `C ⊆ (ι → ℝ)` produces a positive pricing/representing
functional. Two faces of the same Hahn–Banach principle live here:

* `exists_pos_separating_of_cone_disjoint_simplex` — a cone disjoint from the whole standard simplex
  admits a **strictly** positive functional `q` (`> 0` at every coordinate) that is `≤ 0` on the
  cone. This is the FTAP separating functional: the attainable-gains cone misses the simplex (no
  arbitrage) ⟹ the equivalent martingale measure. It generalizes the subspace kernel
  `exists_pos_dual_of_disjoint_stdSimplex` (two-sided `= 0`) to a cone (one-sided `≤ 0`).
* `exists_separating_of_not_mem_cone` — a single point outside a closed convex cone is separated by
  a functional `p` that is `≤ 0` on the cone and `> 0` at the point. This is the coherent-risk
  representing density: a rejected position separated from the acceptance cone.

Both rest on two shared atoms — `functional_eq_sum_single` (basis expansion of a functional) and
`functional_nonneg_on_cone` (a functional bounded below on a cone is `≥ 0` on it; the cone's
nonnegative-scaling homogeneity is what turns a separation bound into a sign). The separations
themselves are Mathlib's `geometric_hahn_banach_compact_closed` and
`geometric_hahn_banach_point_closed`.

## API at this pin

The cone is a `C : Set (ι → ℝ)` carrying `Convex ℝ C`, `IsClosed C`, and homogeneity
`∀ x ∈ C, ∀ c ≥ 0, c • x ∈ C`. There is no `ConvexCone.dual` constant at this pin, but
`ProperCone`/`PointedCone` *are* live, and Mathlib's `ProperCone.hyperplane_separation`
(`Analysis/Convex/Cone/Dual.lean`) is the separation theorem the results below re-derive
from `geometric_hahn_banach_compact_closed`. Consuming it — packaging `C` as a
`ProperCone ℝ (ι → ℝ)` and keeping only the `Pi.single` coordinate glue — is an open
upgrade; the explicit `Set` representation is a historical choice, not a forced one.

## Main results

* `MathFin.exists_pos_separating_of_cone_disjoint_simplex`: for a convex, closed cone `C` in
  `ι → ℝ` (`ι` finite) that contains no point of the standard simplex, there exists `q` with
  every coordinate positive and `∑ q i * v i ≤ 0` for all `v ∈ C`.
* `MathFin.exists_separating_of_not_mem_cone`: for a convex, closed cone `C` containing `0` and a
  point `x₀ ∉ C`, there exists `p` with `∑ p i * v i ≤ 0` on `C` and `0 < ∑ p i * x₀ i`.

## Tags

Hahn–Banach separation, convex cone, no arbitrage, coherent risk measure, pricing functional,
separating hyperplane, MSC 90C25, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin


/-- A continuous linear functional on `ι → ℝ` equals its `∑ wᵢ · f(eᵢ)` expansion on the
standard basis. Shared atom of the two cone-separation theorems below. -/
lemma functional_eq_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : StrongDual ℝ (ι → ℝ)) (w : ι → ℝ) :
    f w = ∑ i, w i * f (Pi.single i 1) := by
  have hwsum : w = ∑ i, w i • Pi.single i (1 : ℝ) := by
    funext j; rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb; rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  conv_lhs => rw [hwsum]
  rw [map_sum]; exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]

/-- A functional bounded below by a negative `u` on a cone `C` is nonnegative on `C`: a ray
`c ∈ C` with `f c < 0` is unbounded below on `C` (scale by `(u-1)/f c ≥ 0`), contradicting the
bound. Shared atom of the two cone-separation theorems below. -/
lemma functional_nonneg_on_cone {ι : Type*} {C : Set (ι → ℝ)}
    (hCcone : ∀ ⦃x⦄, x ∈ C → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • x ∈ C)
    {f : StrongDual ℝ (ι → ℝ)} {u : ℝ} (hu : u < 0) (hlb : ∀ y ∈ C, u < f y) :
    ∀ c ∈ C, 0 ≤ f c := by
  intro c hc
  by_contra hlt
  rw [not_le] at hlt
  have hfcne : f c ≠ 0 := ne_of_lt hlt
  have ht : 0 ≤ (u - 1) / f c := by
    rw [div_nonneg_iff]; right; exact ⟨by linarith, le_of_lt hlt⟩
  have hmem : ((u - 1) / f c) • c ∈ C := hCcone hc ht
  have hval : f (((u - 1) / f c) • c) = u - 1 := by rw [map_smul, smul_eq_mul]; field_simp
  have hlt2 := hlb _ hmem; rw [hval] at hlt2; linarith

/-- **Cone separation root.** A closed convex cone `C ⊆ (ι → ℝ)` containing no probability vector
(no nonnegative `v` with `∑ i, v i = 1`, i.e. disjoint from the standard simplex) admits a
strictly-positive functional `q` that is `≤ 0` on `C` (a separating supporting functional).
The geometric heart shared by the FTAP (gains cone), the coherent-risk representation (acceptance
cone), and superhedging (super-replication cone). Generalizes
`exists_pos_dual_of_disjoint_stdSimplex` (subspace ⇒ two-sided `= 0`) to a cone (one-sided `≤ 0`).
-/
theorem exists_pos_separating_of_cone_disjoint_simplex
    {ι : Type*} [Fintype ι]
    (C : Set (ι → ℝ)) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hCcone : ∀ ⦃x⦄, x ∈ C → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • x ∈ C)
    (hdisj : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → ∑ i, v i = 1 → v ∉ C) :
    ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∀ v ∈ C, ∑ i, q i * v i ≤ 0 := by
  classical
  rcases C.eq_empty_or_nonempty with hCempty | hCne
  · exact ⟨fun _ ↦ 1, fun _ ↦ one_pos, fun w hw ↦ by rw [hCempty] at hw; simp at hw⟩
  obtain ⟨x₀, hx₀⟩ := hCne
  have h0C : (0 : ι → ℝ) ∈ C := by simpa using hCcone hx₀ (le_refl (0 : ℝ))
  set Δ : Set (ι → ℝ) := Set.range fun w : Convexity.StdSimplex ℝ ι ↦ ⇑w.weights
  have hconvΔ : Convex ℝ Δ := by
    rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩ a b ha hb hab
    exact ⟨Convexity.convexCombPair a b ha hb hab w₁ w₂, by simp⟩
  have hcompΔ : IsCompact Δ :=
    isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed hconvΔ hcompΔ hCconv
    hCclosed (Set.disjoint_left.2 (by
      rintro _ ⟨w, rfl⟩; exact hdisj _ w.weights_nonneg w.total_of_fintype))
  have hv_neg : v < 0 := by have h0 := hfv 0 h0C; rwa [map_zero] at h0
  have hfC_nonneg : ∀ c ∈ C, 0 ≤ f c := functional_nonneg_on_cone hCcone hv_neg hfv
  have hsingle_mem (i : ι) : (Pi.single i (1 : ℝ)) ∈ Δ :=
    ⟨.single i, by simp [Finsupp.single_eq_pi_single]⟩
  have hsingle_neg : ∀ i, f (Pi.single i (1 : ℝ)) < 0 := fun i ↦ by
    have := hfu _ (hsingle_mem i); linarith
  refine ⟨fun i ↦ - f (Pi.single i 1), fun i ↦ by have := hsingle_neg i; linarith, fun w hw ↦ ?_⟩
  calc ∑ i, (- f (Pi.single i (1 : ℝ))) * w i
      = - ∑ i, w i * f (Pi.single i 1) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = - f w := by rw [← functional_eq_sum_single f w]
    _ ≤ 0 := by have := hfC_nonneg w hw; linarith

/-- **Cone point-separation.** A point `x₀` outside a closed convex cone `C ⊆ (ι → ℝ)` is
separated by a functional `p` that is `≤ 0` on `C` and `> 0` at `x₀`. The companion to
`exists_pos_separating_of_cone_disjoint_simplex`: that separates a cone from the whole simplex
(strictly positive `q`); this separates a single exterior point from the cone (a representing
density direction). The coherent-risk representation applies it to a rejected position and the
acceptance cone. -/
theorem exists_separating_of_not_mem_cone
    {ι : Type*} [Fintype ι] (C : Set (ι → ℝ))
    (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hCcone : ∀ ⦃x⦄, x ∈ C → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • x ∈ C)
    (h0 : (0 : ι → ℝ) ∈ C) {x₀ : ι → ℝ} (hx₀ : x₀ ∉ C) :
    ∃ p : ι → ℝ, (∀ v ∈ C, ∑ i, p i * v i ≤ 0) ∧ 0 < ∑ i, p i * x₀ i := by
  classical
  obtain ⟨f, u, hfx₀, hfC⟩ := geometric_hahn_banach_point_closed hCconv hCclosed hx₀
  have hu_neg : u < 0 := by have h0' := hfC 0 h0; rwa [map_zero] at h0'
  have hfC_nonneg : ∀ c ∈ C, 0 ≤ f c := functional_nonneg_on_cone hCcone hu_neg hfC
  refine ⟨fun i ↦ - f (Pi.single i 1), fun v hv ↦ ?_, ?_⟩
  · have hsum : ∑ i, (- f (Pi.single i (1 : ℝ))) * v i = - f v := by
      rw [functional_eq_sum_single f v, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum]; have := hfC_nonneg v hv; linarith
  · have hsum : ∑ i, (- f (Pi.single i (1 : ℝ))) * x₀ i = - f x₀ := by
      rw [functional_eq_sum_single f x₀, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum]; linarith

end MathFin
