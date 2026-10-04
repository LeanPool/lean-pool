/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.WeakDerivOnSymm
public import LeanPool.EllipticPDE.Regularity.IteratedRestrict


/-!
# Identifications on the collar

The inductive hypothesis of Guo, *Partial Differential Equations I and II* (Course Lecture
Notes), Theorem VIII.3.2 (p. 65) hands over a family of iterated weak derivatives on a compact
set, and says of its first entries only that they are weak derivatives of the solution. The
ambient element has its own first derivatives, in its gradient coordinates. The two agree, but
only almost everywhere, and only where a cutoff is invisible.

`EllipticPdes.Regularity.mulTest_weakDerivOn_unique` gives the agreement after a cutoff. On an
open collar where the outer cutoff of the tower is identically `1`, the cutoff drops out and the
two families become equal as `L²` classes on the collar. Running the induction step there rather
than on the compact set is what lets a single family supply every derivative the datum needs.

## Main declarations

* `restrictL2_extendL2_trans`: restricting twice is restricting once.
* `restrictL2_extendL2_eq_of_mulTest_eq`: an identification after a cutoff becomes an equality
  on the collar.
* `restrictL2_extendL2_congr_of_weakDerivOn`: two weak derivatives of one class are equal on the
  collar.
* `exists_restrictFamily`, `exists_collarFamily`: a family and its bound, moved in one step.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Restricting twice is restricting once.** For `N ⊆ W`, cutting an `L²(Ω)` class down to
`W` and then to `N` is cutting it down to `N`. The two sets need no relation to `Ω`, since the
whole-space extension is what both restrictions read. -/
theorem restrictL2_extendL2_trans {Ω W N : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (hNm : MeasurableSet N)
    (hNW : N ⊆ W) (g : L2D Ω) :
    restrictL2 (Ω := N) (extendL2 hWm (restrictL2 (Ω := W) (extendL2 hΩm g)))
      = restrictL2 (Ω := N) (extendL2 hΩm g) := by
  refine Lp.ext ?_
  have hrW : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ W →
      (restrictL2 (Ω := W) (extendL2 hΩm g) x : ℝ) = (extendL2 hΩm g x : ℝ) :=
    (ae_restrict_iff' hWm).mp (coeFn_restrictL2 (Ω := W) (extendL2 hΩm g))
  filter_upwards [coeFn_restrictL2 (Ω := N)
      (extendL2 hWm (restrictL2 (Ω := W) (extendL2 hΩm g))),
    coeFn_restrictL2 (Ω := N) (extendL2 hΩm g),
    ae_restrict_of_ae (coeFn_extendL2 hWm (restrictL2 (Ω := W) (extendL2 hΩm g))),
    ae_restrict_of_ae hrW, ae_restrict_mem hNm] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, Set.indicator_of_mem (hNW h5), h4 (hNW h5)]

/-- **Identification after a cutoff as an equality on the collar.** Where `θ` is identically
`1` on `N ⊆ W`, two classes with `θ·X = θ·Y` restrict to the same class on `N`. -/
theorem restrictL2_extendL2_eq_of_mulTest_eq {W N : Set (EuclideanSpace ℝ (Fin d))}
    (hWm : MeasurableSet W) (hNm : MeasurableSet N) (hNW : N ⊆ W)
    {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθW : IsTestFn W θ) (hθN : Set.EqOn θ 1 N)
    {X Y : L2D W} (h : mulTest hθW X = mulTest hθW Y) :
    restrictL2 (Ω := N) (extendL2 hWm X) = restrictL2 (Ω := N) (extendL2 hWm Y) := by
  refine Lp.ext ?_
  have hXY : ∀ᵐ x ∂(volume.restrict W), θ x * (X x : ℝ) = θ x * (Y x : ℝ) := by
    filter_upwards [mulTest_coeFn hθW X, mulTest_coeFn hθW Y] with x h1 h2
    rw [← h1, ← h2, h]
  have hXYN : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ W →
      θ x * (X x : ℝ) = θ x * (Y x : ℝ) := (ae_restrict_iff' hWm).mp hXY
  filter_upwards [coeFn_restrictL2 (Ω := N) (extendL2 hWm X),
    coeFn_restrictL2 (Ω := N) (extendL2 hWm Y),
    ae_restrict_of_ae (coeFn_extendL2 hWm X), ae_restrict_of_ae (coeFn_extendL2 hWm Y),
    ae_restrict_of_ae hXYN, ae_restrict_mem hNm] with x h1 h2 h3 h4 h5 h6
  have hone : θ x = 1 := hθN h6
  have hkey := h5 (hNW h6)
  rw [hone, one_mul, one_mul] at hkey
  rw [h1, h2, h3, h4, Set.indicator_of_mem (hNW h6), Set.indicator_of_mem (hNW h6), hkey]

/-- **Two weak derivatives of one class are equal on the collar.** The inductive family's first
entries and the ambient element's gradient coordinates are both weak derivatives of the
solution, so they agree there. -/
theorem restrictL2_extendL2_congr_of_weakDerivOn {W N : Set (EuclideanSpace ℝ (Fin d))}
    (hWm : MeasurableSet W) (hNm : MeasurableSet N) (hNW : N ⊆ W)
    {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθW : IsTestFn W θ) (hθN : Set.EqOn θ 1 N)
    {i : Fin d} {g X Y : L2D W} (hX : HasWeakDerivOn W i g X) (hY : HasWeakDerivOn W i g Y) :
    restrictL2 (Ω := N) (extendL2 hWm X) = restrictL2 (Ω := N) (extendL2 hWm Y) :=
  restrictL2_extendL2_eq_of_mulTest_eq hWm hNm hNW hθW hθN
    (mulTest_weakDerivOn_unique hWm hθW hX hY)

/-- **Family and its bound moved to a subregion.** Both halves of the restriction, packaged
so the elaborator does the unification once. Applied inline in the induction step, where the
context has the tower and the datum, the same two lines take minutes. -/
theorem exists_restrictFamily {Ω N : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) {g : L2D Ω} {k : ℕ} {C : ℝ}
    (H : HasIteratedWeakDerivOn Ω k g) (hC : IteratedL2Bound H C) :
    ∃ HN : HasIteratedWeakDerivOn N k (restrictL2 (Ω := N) (extendL2 hΩm g)),
      IteratedL2Bound HN C :=
  ⟨H.restrict hΩm hNm hNΩ, IteratedL2Bound.restrict hC⟩

/-- **Inductive family moved to the collar.** A family on `W` for the whole-space
extension of `g`, restricted to `N`, is a family there for the same class, with the same bound,
and its first entries are the given weak derivatives of `g`.

The three conclusions travel together because the induction step needs all three and each is a
unification the elaborator should do once. Doing them inline takes minutes, since the step's
context has the tower, its collar, four cutoffs and the datum by the time it needs them. -/
theorem exists_collarFamily {Ω W N : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (hNm : MeasurableSet N) (hNW : N ⊆ W)
    {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθW : IsTestFn W θ) (hθN : Set.EqOn θ 1 N)
    {g : L2D Ω} {Dg : Fin d → L2D Ω}
    (hDgw : ∀ i, HasWeakDeriv i (extendL2 hΩm g) (extendL2 hΩm (Dg i))) {m : ℕ} {C : ℝ}
    (HuW : HasIteratedWeakDerivOn W (m + 1) (restrictL2 (Ω := W) (extendL2 hΩm g)))
    (hHuW : IteratedL2Bound HuW C) :
    ∃ HuN : HasIteratedWeakDerivOn N (m + 1) (restrictL2 (Ω := N) (extendL2 hΩm g)),
      IteratedL2Bound HuN C ∧
      ∀ i : Fin d, HuN.D [i] = restrictL2 (Ω := N) (extendL2 hΩm (Dg i)) := by
  refine ⟨(HuW.restrict hWm hNm hNW).congr (restrictL2_extendL2_trans hΩm hWm hNm hNW g),
    IteratedL2Bound.congr (h := restrictL2_extendL2_trans hΩm hWm hNm hNW g)
      (IteratedL2Bound.restrict (hWm := hWm) (hVm := hNm) (hVW := hNW) hHuW), fun i => ?_⟩
  have h1 : HasWeakDerivOn W i (restrictL2 (Ω := W) (extendL2 hΩm g)) (HuW.D [i]) := by
    have h := HuW.D_step i [] (Nat.succ_pos m)
    rwa [HuW.D_nil] at h
  have h2 : HasWeakDerivOn W i (restrictL2 (Ω := W) (extendL2 hΩm g))
      (restrictL2 (Ω := W) (extendL2 hΩm (Dg i))) :=
    hasWeakDerivOn_of_hasWeakDeriv i (hDgw i)
  change restrictL2 (Ω := N) (extendL2 hWm (HuW.D [i])) = _
  rw [restrictL2_extendL2_congr_of_weakDerivOn hWm hNm hNW hθW hθN h1 h2,
    restrictL2_extendL2_trans hΩm hWm hNm hNW]

end EllipticPdes.Regularity
