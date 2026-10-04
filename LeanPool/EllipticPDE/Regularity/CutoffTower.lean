/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Sobolev.Basic
public import LeanPool.EllipticPDE.Regularity.DifferenceQuotient
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.MetricSpace.Thickening


/-!
# Smooth cutoff tower for the interior `H²` estimate

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) localises the
difference-quotient method with a nested family of smooth cutoffs: an innermost cutoff `ζ` equal
to `1` on the region of interest `V`, a middle cutoff `ξ` equal to `1` on the support of `ζ`,
and an outermost cutoff `θ` equal to `1` on the support of `ξ`, all three compactly supported
inside the ambient domain `Ω`. The outermost support has a positive margin `δ`: every point of
`tsupport θ` stays inside `Ω` after a coordinate shift `h eₖ` of size `|h| < δ`, which is
exactly what lets the discrete difference quotient act inside `Ω` without losing mass.

This file provides:

* `exists_isTestFn_one_nhdsSet_of_isCompact`: the underlying smooth Urysohn-type cutoff lemma:
  for `K` compact inside an open `U`, a test function on `U` valued in `[0,1]` and equal to `1`
  on a neighbourhood of `K`. This specialises the classical smooth-partition-of-unity
  construction (`Mathlib.Geometry.Manifold.PartitionOfUnity`) to the trivial self-chart manifold
  structure that `EuclideanSpace ℝ (Fin d)` has as a finite-dimensional normed space, bridged
  back to plain `ContDiff` via `contMDiff_iff_contDiff`.
* `exists_margin_of_isCompact_subset_isOpen`: the positive-margin fact for a compact-in-open
  pair, from `IsCompact.exists_cthickening_subset_open`.
* `CutoffTower`: the bundle of the three nested cutoffs and the margin.
* `cutoffTowerOfIsCompactSubsetIsOpen`: existence of a `CutoffTower` for every compact `V`
  inside an open `Ω`, built by three applications of the Urysohn-type cutoff lemma followed by
  one application of the margin lemma.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Urysohn-type smooth cutoff on a compact-in-open pair -/

/-- **Smooth Urysohn cutoff.** For `K` compact contained in an open `U`, a test function on `U`
(`EllipticPdes.Sobolev.IsTestFn`), valued in `[0,1]`, equal to `1` on a neighbourhood of `K`.
This is the smooth cutoff-function device used throughout interior regularity theory (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1), obtained here from the manifold
smooth-partition-of-unity Urysohn lemma specialised to the self-chart manifold structure
`EuclideanSpace ℝ (Fin d)` has as a finite-dimensional normed space. -/
theorem exists_isTestFn_one_nhdsSet_of_isCompact {K U : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ζ : EuclideanSpace ℝ (Fin d) → ℝ,
      IsTestFn U ζ ∧ (∀ᶠ x in 𝓝ˢ K, ζ x = 1) ∧ ∀ x, ζ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨δ, δpos, hδ⟩ := hK.exists_cthickening_subset_open hU hKU
  have ht_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
  have ht_closure_compact : IsCompact (closure (Metric.thickening δ K)) :=
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure
      (Metric.closure_thickening_subset_cthickening δ K)
  have ht_closure_subset : closure (Metric.thickening δ K) ⊆ U :=
    (Metric.closure_thickening_subset_cthickening δ K).trans hδ
  obtain ⟨f, hf1, hf0, hfIcc⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d))) (n := (⊤ : ℕ∞)) hK.isClosed
    (t := Metric.thickening δ K)
    (by rw [ht_open.interior_eq]; exact Metric.self_subset_thickening δpos K)
  have hsupp : Function.support (f : EuclideanSpace ℝ (Fin d) → ℝ)
      ⊆ Metric.thickening δ K := by
    intro x hx
    by_contra hxt
    exact hx (hf0 x hxt)
  refine ⟨(f : EuclideanSpace ℝ (Fin d) → ℝ), ⟨?_, ?_, ?_⟩, hf1, hfIcc⟩
  · exact contMDiff_iff_contDiff.mp f.contMDiff
  · exact ht_closure_compact.of_isClosed_subset isClosed_closure (closure_mono hsupp)
  · exact (closure_mono hsupp).trans ht_closure_subset

/-! ### Positive shift margin on a compact-in-open pair -/

/-- **Positive margin.** For `K` compact inside an open `Ω`, there is `δ > 0` such that every
point of `K` stays inside `Ω` after any coordinate shift `h eₖ` with `|h| < δ`. This is the
finite-margin fact that lets the interior difference-quotient method translate a cutoff's
support without leaving the domain (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8). -/
theorem exists_margin_of_isCompact_subset_isOpen {K Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : Fin d) (h : ℝ), |h| < δ → ∀ x ∈ K, x + hshift k h ∈ Ω := by
  obtain ⟨δ, δpos, hδ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  refine ⟨δ, δpos, fun k h hh x hx => hδ (Metric.thickening_subset_cthickening δ K ?_)⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨x, hx, ?_⟩
  rw [dist_eq_norm, show x + hshift k h - x = hshift k h from by abel]
  calc ‖hshift k h‖ = |h| := by simp [hshift, norm_smul]
    _ < δ := hh

/-! ### Nested cutoff tower -/

/-- **Nested cutoff tower.** Three test functions on `Ω`: `ζ` equal to `1` on the base
compact set `V`, `ξ` equal to `1` on the support of `ζ`, `θ` equal to `1` on the support of
`ξ`, together with a positive coordinate-shift margin valid on the support of `θ`. This is
exactly the tower `ζ`, `ξ`, `θ` nested in that support-inclusion order, localising the
difference-quotient method of the interior `H²` estimate (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8). -/
structure CutoffTower (Ω V : Set (EuclideanSpace ℝ (Fin d))) where
  /-- The innermost cutoff, equal to `1` on `V`. -/
  ζ : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The middle cutoff, equal to `1` on `tsupport ζ`. -/
  ξ : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The outermost cutoff, equal to `1` on `tsupport ξ`. -/
  θ : EuclideanSpace ℝ (Fin d) → ℝ
  /-- `ζ` is a test function on `Ω`. -/
  hζ : IsTestFn Ω ζ
  /-- `ξ` is a test function on `Ω`. -/
  hξ : IsTestFn Ω ξ
  /-- `θ` is a test function on `Ω`. -/
  hθ : IsTestFn Ω θ
  /-- `ζ` is valued in `[0,1]`. -/
  hζ_Icc : ∀ x, ζ x ∈ Set.Icc (0 : ℝ) 1
  /-- `ξ` is valued in `[0,1]`. -/
  hξ_Icc : ∀ x, ξ x ∈ Set.Icc (0 : ℝ) 1
  /-- `θ` is valued in `[0,1]`. -/
  hθ_Icc : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1
  /-- `ζ ≡ 1` on a neighbourhood of `V`. -/
  hζ_one : ∀ᶠ x in 𝓝ˢ V, ζ x = 1
  /-- `ξ ≡ 1` on a neighbourhood of `tsupport ζ`. -/
  hξ_one : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ξ x = 1
  /-- `θ ≡ 1` on a neighbourhood of `tsupport ξ`. -/
  hθ_one : ∀ᶠ x in 𝓝ˢ (tsupport ξ), θ x = 1
  /-- The positive coordinate-shift margin on `tsupport θ`. -/
  margin : ℝ
  /-- The margin is positive. -/
  hmargin_pos : 0 < margin
  /-- Below the margin, every point of `tsupport θ` stays inside `Ω` after a coordinate
  shift. -/
  hmargin : ∀ (k : Fin d) (h : ℝ), |h| < margin → ∀ x ∈ tsupport θ, x + hshift k h ∈ Ω

namespace CutoffTower

variable {Ω V : Set (EuclideanSpace ℝ (Fin d))}

/-- The innermost cutoff is equal to `1` at every point of `V`, rather than on a neighbourhood
of it. -/
theorem zeta_eqOn_one (T : CutoffTower Ω V) : Set.EqOn T.ζ 1 V :=
  fun x hx => T.hζ_one.self_of_nhdsSet x hx

/-- The middle cutoff is equal to `1` at every point of `tsupport ζ`. -/
theorem xi_eqOn_one (T : CutoffTower Ω V) : Set.EqOn T.ξ 1 (tsupport T.ζ) :=
  fun x hx => T.hξ_one.self_of_nhdsSet x hx

/-- The outermost cutoff is equal to `1` at every point of `tsupport ξ`. -/
theorem theta_eqOn_one (T : CutoffTower Ω V) : Set.EqOn T.θ 1 (tsupport T.ξ) :=
  fun x hx => T.hθ_one.self_of_nhdsSet x hx

end CutoffTower

/-- **Existence of the cutoff tower.** For any compact `V` inside an open `Ω`, a cutoff tower
based at `V` exists: three applications of `exists_isTestFn_one_nhdsSet_of_isCompact` build
`ζ`, `ξ`, `θ` in turn (each new cutoff's compact set is the topological support of the
previous one, which stays inside `Ω`), and `exists_margin_of_isCompact_subset_isOpen` supplies
the final margin on `tsupport θ`. -/
noncomputable def cutoffTowerOfIsCompactSubsetIsOpen {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (hV : IsCompact V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω) : CutoffTower Ω V := by
  choose ζ hζ hζ_one hζ_Icc using
    exists_isTestFn_one_nhdsSet_of_isCompact hV hΩ hVΩ
  choose ξ hξ hξ_one hξ_Icc using
    exists_isTestFn_one_nhdsSet_of_isCompact hζ.2.1 hΩ hζ.2.2
  choose θ hθ hθ_one hθ_Icc using
    exists_isTestFn_one_nhdsSet_of_isCompact hξ.2.1 hΩ hξ.2.2
  choose δ hδ_pos hδ using
    exists_margin_of_isCompact_subset_isOpen hθ.2.1 hΩ hθ.2.2
  exact
    { ζ := ζ
      ξ := ξ
      θ := θ
      hζ := hζ
      hξ := hξ
      hθ := hθ
      hζ_Icc := hζ_Icc
      hξ_Icc := hξ_Icc
      hθ_Icc := hθ_Icc
      hζ_one := hζ_one
      hξ_one := hξ_one
      hθ_one := hθ_one
      margin := δ
      hmargin_pos := hδ_pos
      hmargin := hδ }

end EllipticPdes.Regularity
