/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

module

public import LeanPool.TetrahedronPacking.PeriodicSeparation
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Robust separation of periodic convex motifs

Keep a nominal separating plane fixed. A perturbation loses at most the
operator norm of its functional times the displacement of each side. The
finite shift search must use coordinate bounds valid for the perturbed
vertices. These two checks control independent sources of uncertainty.
-/

namespace TetrahedronPacking

open Set

/-- A separating plane with a displacement budget on each side still
separates the interiors after perturbation. Equality allows boundary contact. -/
theorem disjoint_interiors_of_perturbed_plane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} {v v' : ι → E} {w w' : κ → E}
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) {a b εv εw : ℝ}
    (hv : ∀ i, f (v i) ≤ a) (hw : ∀ j, b ≤ f (w j))
    (hδv : ∀ i, ‖v' i - v i‖ ≤ εv)
    (hδw : ∀ j, ‖w' j - w j‖ ≤ εw)
    (hgap : a + ‖f‖ * εv ≤ b - ‖f‖ * εw) :
    Disjoint (interior (convexHull ℝ (range v'))) (interior (convexHull ℝ (range w'))) := by
  apply disjoint_interiors_of_separating_plane f hf (a + ‖f‖ * εv)
  · intro i
    have h := (f.le_opNorm (v' i - v i)).trans
      (mul_le_mul_of_nonneg_left (hδv i) (norm_nonneg f))
    rw [map_sub, Real.norm_eq_abs] at h
    linarith [le_abs_self (f (v' i) - f (v i)), hv i]
  · intro j
    have h := (f.le_opNorm (w' j - w j)).trans
      (mul_le_mul_of_nonneg_left (hδw j) (norm_nonneg f))
    rw [map_sub, Real.norm_eq_abs] at h
    linarith [neg_le_abs (f (w' j) - f (w j)), hw j]

/-- A robust periodic certificate may compare two lattices. The search box
is computed in the perturbed chart, and the bound on shift displacement is
only needed for the shifts in that box. -/
theorem disjoint_interiors_of_perturbed_shift_certificates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ α : Type*} (C C' : E ≃ₗ[ℝ] (α → ℝ))
    (v v' : ι → E) (w w' : κ → E) (required : (α → ℤ) → Prop)
    (loV hiV loW hiW : α → ℝ) {εv εw : ℝ} (εshift : (α → ℤ) → ℝ)
    (hv' : ∀ i j, loV j ≤ C' (v' i) j ∧ C' (v' i) j ≤ hiV j)
    (hw' : ∀ i j, loW j ≤ C' (w' i) j ∧ C' (w' i) j ≤ hiW j)
    (hδv : ∀ i, ‖v' i - v i‖ ≤ εv)
    (hδw : ∀ j, ‖w' j - w j‖ ≤ εw)
    (certificate : ∀ k : α → ℤ, required k →
      (∀ j, loV j - hiW j ≤ (k j : ℝ) ∧ (k j : ℝ) ≤ hiV j - loW j) →
      ‖C'.symm (fun j => (k j : ℝ)) - C.symm (fun j => (k j : ℝ))‖ ≤ εshift k ∧
      ∃ (f : E →L[ℝ] ℝ) (a b : ℝ), f ≠ 0 ∧
        (∀ i, f (v i) ≤ a) ∧ (∀ j, b ≤ f (w j + C.symm (fun i => (k i : ℝ)))) ∧
        a + ‖f‖ * εv ≤ b - ‖f‖ * (εw + εshift k)) :
    ∀ k : α → ℤ, required k →
      Disjoint (interior (convexHull ℝ (range v')))
        (interior (convexHull ℝ (range (fun j => w' j + C'.symm (fun i => (k i : ℝ)))))) := by
  intro k hk
  by_contra h
  obtain ⟨x, hx, hy⟩ := Set.not_disjoint_iff.mp h
  have hb := shift_bounds_of_hulls_intersect C' v' w' k loV hiV loW hiW hv' hw'
    (interior_subset hx) (interior_subset hy)
  obtain ⟨hδshift, f, a, b, hf, hfv, hfw, hgap⟩ := certificate k hk hb
  have hδ (j : κ) :
      ‖(w' j + C'.symm (fun i => (k i : ℝ))) -
        (w j + C.symm (fun i => (k i : ℝ)))‖ ≤ εw + εshift k := by
    rw [add_sub_add_comm]
    exact (norm_add_le _ _).trans (add_le_add (hδw j) hδshift)
  exact Set.disjoint_left.mp
    (disjoint_interiors_of_perturbed_plane f hf hfv hfw hδv hδ hgap) hx hy

/-- Fractional coordinates remove cell-basis errors from the shift itself.
The same bounds therefore apply to all invertible realizations of a cell
provided their fractional vertices satisfy the given error budget. -/
theorem disjoint_interiors_of_fractional_clearance
    {ι κ α : Type*} [Fintype α]
    (C : (α → ℝ) ≃ₗ[ℝ] (α → ℝ))
    (v v' : ι → α → ℝ) (w w' : κ → α → ℝ)
    (required : (α → ℤ) → Prop) (loV hiV loW hiW : α → ℝ)
    {εv εw : ℝ} (hεv : 0 ≤ εv) (hεw : 0 ≤ εw)
    (hv : ∀ i j, loV j ≤ v i j ∧ v i j ≤ hiV j)
    (hw : ∀ i j, loW j ≤ w i j ∧ w i j ≤ hiW j)
    (hδv : ∀ i j, |v' i j - v i j| ≤ εv)
    (hδw : ∀ i j, |w' i j - w i j| ≤ εw)
    (certificate : ∀ k : α → ℤ, required k →
      (∀ j, loV j - hiW j - (εv + εw) ≤ (k j : ℝ) ∧
        (k j : ℝ) ≤ hiV j - loW j + (εv + εw)) →
      ∃ (f : (α → ℝ) →L[ℝ] ℝ) (a b : ℝ), f ≠ 0 ∧
        (∀ i, f (v i) ≤ a) ∧ (∀ j, b ≤ f (w j + fun i => (k i : ℝ))) ∧
        a + ‖f‖ * εv ≤ b - ‖f‖ * εw) :
    ∀ k : α → ℤ, required k →
      Disjoint (interior (convexHull ℝ (range (fun i => C.symm (v' i)))))
        (interior (convexHull ℝ (range (fun j => C.symm (w' j) +
          C.symm (fun i => (k i : ℝ)))))) := by
  classical
  have hnormV (i : ι) : ‖v' i - v i‖ ≤ εv := by
    rw [pi_norm_le_iff_of_nonneg hεv]
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hδv i
  have hnormW (i : κ) : ‖w' i - w i‖ ≤ εw := by
    rw [pi_norm_le_iff_of_nonneg hεw]
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hδw i
  have hboundsV (i : ι) (j : α) : loV j - εv ≤ v' i j ∧ v' i j ≤ hiV j + εv := by
    have h := abs_le.mp (hδv i j)
    obtain ⟨hl, hh⟩ := hv i j
    constructor <;> linarith
  have hboundsW (i : κ) (j : α) : loW j - εw ≤ w' i j ∧ w' i j ≤ hiW j + εw := by
    have h := abs_le.mp (hδw i j)
    obtain ⟨hl, hh⟩ := hw i j
    constructor <;> linarith
  let I : (α → ℝ) ≃ₗ[ℝ] (α → ℝ) := LinearEquiv.refl ℝ _
  have hI (x : α → ℝ) : I.symm x = x := rfl
  intro k hk
  have h := disjoint_interiors_of_perturbed_shift_certificates I I v v' w w' required
    (fun j => loV j - εv) (fun j => hiV j + εv)
    (fun j => loW j - εw) (fun j => hiW j + εw) (fun _ => 0)
    hboundsV hboundsW hnormV hnormW (by
      intro s hs hb
      refine ⟨by simp, ?_⟩
      obtain ⟨f, a, b, hf, hfv, hfw, hgap⟩ := certificate s hs (fun j => by
        obtain ⟨hl, hh⟩ := hb j
        change loV j - εv - (hiW j + εw) ≤ (s j : ℝ) at hl
        change (s j : ℝ) ≤ hiV j + εv - (loW j - εw) at hh
        constructor <;> linarith)
      exact ⟨f, a, b, hf, hfv, hfw, by simpa only [add_zero] using hgap⟩) k hk
  let H := C.symm.toContinuousLinearEquiv.toHomeomorph
  have imageHull (s : Set (α → ℝ)) :
      H '' interior (convexHull ℝ s) =
        interior (convexHull ℝ (C.symm '' s)) := by
    rw [H.image_interior]
    exact congrArg interior (C.symm.toLinearMap.image_convexHull s)
  have hi := Set.disjoint_image_of_injective H.injective h
  rw [imageHull, imageHull, ← Set.range_comp, ← Set.range_comp] at hi
  change Disjoint (interior (convexHull ℝ (range (fun i => C.symm (v' i)))))
    (interior (convexHull ℝ (range (fun j =>
      C.symm (w' j + I.symm (fun i => (k i : ℝ))))))) at hi
  simpa only [hI, map_add] using hi

/-- A separation certificate for each relative displacement also gives
pairwise disjoint interiors for copies at arbitrary lattice indices. -/
theorem pairwise_disjoint_of_relative_shift
    {μ ι α : Type*} [Fintype α]
    (C : (α → ℝ) ≃ₗ[ℝ] (α → ℝ)) (v : μ → ι → α → ℝ)
    (separated : ∀ (i j : μ) (k : α → ℤ), i ≠ j ∨ k ≠ 0 →
      Disjoint (interior (convexHull ℝ (range (v i))))
        (interior (convexHull ℝ (range (fun a =>
          v j a + C.symm (fun r => (k r : ℝ))))))) :
    let piece (p : μ × (α → ℤ)) :=
      convexHull ℝ (range (fun a => v p.1 a + C.symm (fun r => (p.2 r : ℝ))))
    Pairwise fun p q => Disjoint (interior (piece p)) (interior (piece q)) := by
  dsimp only
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have hne : i ≠ j ∨ l - k ≠ 0 := by
    by_cases hij : i = j
    · right
      intro hkl
      exact h (Prod.ext hij (sub_eq_zero.mp hkl).symm)
    · exact Or.inl hij
  let shift := Homeomorph.addRight (C.symm (fun r => (k r : ℝ)))
  have hd := disjoint_image_of_injective shift.injective (separated i j (l - k) hne)
  simp only [shift.image_interior] at hd
  have imageHull (u : ι → α → ℝ) :
      shift '' convexHull ℝ (range u) =
        convexHull ℝ (range (fun a => u a + C.symm (fun r => (k r : ℝ)))) := by
    simpa [shift, ← range_comp, Function.comp_def, add_comm] using
      AffineMap.image_convexHull
        (AffineEquiv.vaddConst ℝ (C.symm (fun r => (k r : ℝ)))).toAffineMap (range u)
  rw [imageHull, imageHull] at hd
  have shift_eq : (fun r : α => (↑((l - k) r) : ℝ)) =
      (fun r => (l r : ℝ)) - (fun r => (k r : ℝ)) := by
    ext r
    exact Int.cast_sub _ _
  simpa only [shift_eq, map_sub, add_assoc, sub_add_cancel] using hd


end TetrahedronPacking
