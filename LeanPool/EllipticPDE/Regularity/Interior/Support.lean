/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.RestrictedDiffQuotientMem
public import LeanPool.EllipticPDE.Regularity.CoeffC1
public import LeanPool.EllipticPDE.Regularity.CutoffTower


/-!
# Internal support lemmas for the interior estimate

Shared scaffolding for the modules under `EllipticPdes.Regularity.Interior`. These declarations
are internal: they are exposed only because Lean's `private` modifier is file-scoped and
the interior estimate spans several modules. Each lemma here is stated and proved once but
consumed in more than one of them, so no single module can keep it private.

Consumers should use `interior_H2_estimate` and its siblings from
`EllipticPdes.Regularity.Interior`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- A cutoff-multiplied class vanishes a.e. off the topological support of the cutoff. -/
lemma mulTest_ae_eq_zero_off_tsupport {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω η) (g : L2D Ω) :
    ∀ᵐ x ∂(volume.restrict Ω),
      x ∉ tsupport η → (mulTest hη g x : ℝ) = 0 := by
  filter_upwards [mulTest_coeFn hη g] with x hx hxns
  rw [hx, image_eq_zero_of_notMem_tsupport hxns, zero_mul]

/-- If a class `g` vanishes a.e. (on `Ω`) off a set `S`, then its extension by zero to the
whole space is a.e. supported in `S`. -/
lemma extendL2_supp_of_ae_restrict (hΩm : MeasurableSet Ω) (g : L2D Ω)
    {S : Set (EuclideanSpace ℝ (Fin d))}
    (hg : ∀ᵐ x ∂(volume.restrict Ω), x ∉ S → (g x : ℝ) = 0) :
    ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S := by
  filter_upwards [coeFn_extendL2 hΩm g, ae_imp_of_ae_restrict hg] with x hx himp
  rw [hx]; intro hne
  by_cases hxΩ : x ∈ Ω
  · by_contra hxS
    rw [Set.indicator_of_mem hxΩ] at hne
    exact hne (himp hxΩ hxS)
  · rw [Set.indicator_of_notMem hxΩ] at hne; exact absurd rfl hne

/-- Restriction to `Ω` is non-expansive on `L²`: `‖restrictL2 w‖ ≤ ‖w‖`. -/
lemma norm_restrictL2_le (w : EucL2 d) :
    ‖restrictL2 (Ω := Ω) w‖ ≤ ‖w‖ :=
  norm_Lp_toLp_restrict_le Ω w

/-- Abstract single-term ≤ sum over `Fin d` for a nonnegative real family, isolated so its
application only beta-reduces (avoiding a `Finset.single_le_sum` isDefEq loop on `L²` norm
summands). -/
lemma single_le_sum_fin {m : ℕ} (g : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) (k : Fin m) :
    g k ≤ ∑ i : Fin m, g i :=
  Finset.single_le_sum (f := g) (fun i _ => hg i) (Finset.mem_univ k)

end EllipticPdes.Regularity
