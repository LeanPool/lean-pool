/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# High-contrast homogenization: Consistency.ConvexDilation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Dilation of a convex domain, and global smooth realization

This module checks the defining predicate `MemH1a` of `H¹_a(V)` of
`s.introduction`, and its zero-trace variant `MemH1a0`.  It checks the requirement in those
classes that a member be approximated in the
`H¹_a` norm by functions smooth on all of `ℝ^d`, where the paper's
coefficient-weighted spaces are completions of `C^∞(U)`, the functions smooth
*on* `U`: a function smooth on `U` is carried, by dilation and a cutoff, to a
globally smooth function agreeing with its dilate exactly on `closure U`, and
exact agreement on an open set makes the two share their coordinate gradients.

Were that check to fail — were the homothety of `closure U` not to land in
`interior U`, or the dilate not to have a globally smooth representative
agreeing with it exactly on `closure U` with the same coordinate gradients —
then the printed completions could not be represented by the globally smooth
approximants that `MemH1a` demands; the predicate would encode a class smaller
than the space the paper prints, and every statement that assumes a member of
`MemH1a`, among them the estimates for weak solutions, would be vacuous
precisely where the paper means it to apply.  This module is a consistency
check of that definition and is not a result of the paper.

The classical route between the two dilates the domain and then mollifies the
function.  This module supplies the dilation step and removes the need for the
mollification.

The first section is the geometric core: for a convex `U` carrying an interior
ball around `c`, the homothety `x ↦ c + lam • (x - c)` of ratio `lam < 1` maps
`closure U` into `interior U`, so a function smooth on `U` becomes, after
dilation, smooth on an *open* set containing `closure U`.  Neither boundedness
nor openness of `U` is used; the interior ball is the only nondegeneracy input.

The second section replaces mollification.  Because the dilate is smooth on an
open neighbourhood of `closure U`, a smooth Urysohn cutoff turns it into a
genuinely globally smooth function agreeing with it *exactly* on `closure U`,
not merely approximately, and exact agreement on an open set transfers to the
coordinate gradients.

One classical, coefficient-free statement is not settled here: that dilation is
continuous at `lam = 1` in `L¹(U) × L²(U)`.  Until it is available the membership
classes used here are not known to agree with the printed completions, in either
direction.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The convex dilation lemma

For a convex `U` carrying an interior ball around `c`, the homothety
`x ↦ c + lam • (x - c)` of ratio `lam < 1` centred at `c` pulls the whole closure
strictly inside: its image lands in `interior U`.  No boundedness of `U` and no
openness of `U` is used; the interior ball is the only nondegeneracy input. -/

/-- The homothety of ratio `lam` centred at `c` is smooth. -/
theorem contDiff_dilate (c : Vec d) (lam : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => c + lam • (x - c)) := by
  refine ContDiff.add contDiff_const ?_
  exact ContDiff.const_smul lam (contDiff_id.sub contDiff_const)

/-- **The convex dilation lemma.**  If `U` is convex and contains the ball of
radius `ρ > 0` about `c`, then for every ratio `lam ∈ [0, 1)` the homothety
`x ↦ c + lam • (x - c)` maps `closure U` into `interior U`. -/
theorem dilate_closure_subset_interior_of_convex {U : Set (Vec d)}
    (hconv : Convex ℝ U) {c : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball c ρ ⊆ U) {lam : ℝ} (hlam : lam ∈ Set.Ico (0 : ℝ) 1) :
    (fun x => c + lam • (x - c)) '' closure U ⊆ interior U := by
  have hc : c ∈ interior U :=
    interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hρ)
  rintro _ ⟨x, hx, rfl⟩
  have hkey : (1 - lam) • c + lam • x ∈ interior U :=
    hconv.combo_interior_closure_mem_interior hc hx (sub_pos.mpr hlam.2) hlam.1
      (by ring)
  show c + lam • (x - c) ∈ interior U
  have heq : c + lam • (x - c) = (1 - lam) • c + lam • x := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [heq]
  exact hkey

/-- The dilated closure lands in `U` itself. -/
theorem smul_closure_subset_of_convex {U : Set (Vec d)} (hconv : Convex ℝ U)
    {c : Vec d} {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.ball c ρ ⊆ U)
    {lam : ℝ} (hlam : lam ∈ Set.Ico (0 : ℝ) 1) :
    (fun x => c + lam • (x - c)) '' closure U ⊆ U :=
  (dilate_closure_subset_interior_of_convex hconv hρ hball hlam).trans
    interior_subset

/-- The open set on which the dilated function inherits smoothness: the
homothety preimage of `interior U`. -/
@[expose]
def dilationDomain (c : Vec d) (lam : ℝ) (U : Set (Vec d)) : Set (Vec d) :=
  (fun x => c + lam • (x - c)) ⁻¹' interior U

theorem isOpen_dilationDomain (c : Vec d) (lam : ℝ) (U : Set (Vec d)) :
    IsOpen (dilationDomain c lam U) :=
  isOpen_interior.preimage (contDiff_dilate c lam).continuous

/-- The dilation domain is a *neighbourhood of the closure*: this is the
dilation lemma read as an inclusion of sets. -/
theorem closure_subset_dilationDomain {U : Set (Vec d)} (hconv : Convex ℝ U)
    {c : Vec d} {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.ball c ρ ⊆ U)
    {lam : ℝ} (hlam : lam ∈ Set.Ico (0 : ℝ) 1) :
    closure U ⊆ dilationDomain c lam U := fun _ hx =>
  dilate_closure_subset_interior_of_convex hconv hρ hball hlam ⟨_, hx, rfl⟩

/-- **Smoothness of the dilate on a neighbourhood of the closure.**  A function
smooth on `U` only becomes, after dilation, smooth on the *open* set
`dilationDomain c lam U`, which by `closure_subset_dilationDomain` contains
`closure U`. -/
theorem contDiffOn_comp_dilate {U : Set (Vec d)} {c : Vec d} {lam : ℝ}
    {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => v (c + lam • (x - c)))
      (dilationDomain c lam U) := by
  have hmaps : Set.MapsTo (fun x : Vec d => c + lam • (x - c))
      (dilationDomain c lam U) U := by
    intro x hx
    exact interior_subset hx
  exact hv.comp (contDiff_dilate c lam).contDiffOn hmaps

/-- The conclusion of this section: from smoothness on `U` alone one gets a genuine
open neighbourhood of `closure U` on which the dilate is smooth. -/
theorem exists_isOpen_contDiffOn_comp_dilate {U : Set (Vec d)}
    (hconv : Convex ℝ U) {c : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball c ρ ⊆ U) {lam : ℝ} (hlam : lam ∈ Set.Ico (0 : ℝ) 1)
    {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    ∃ S : Set (Vec d), IsOpen S ∧ closure U ⊆ S ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => v (c + lam • (x - c))) S :=
  ⟨dilationDomain c lam U, isOpen_dilationDomain c lam U,
    closure_subset_dilationDomain hconv hρ hball hlam, contDiffOn_comp_dilate hv⟩

/-! ## The mollification step is unnecessary

The classical route to the density converse dilates and then *mollifies*, and
mollification in `L²` is the expensive part: the ambient library carries no
`Lp`-convergence statement for mollifiers.  It is not needed here.  Because the
previous section delivers smoothness on an *open* set containing `closure U`, a smooth Urysohn
cutoff turns the dilate into a genuinely globally smooth function that agrees
with it *exactly* on `closure U`, not merely approximately.  The cutoff is
`exists_contMDiffMap_zero_one_nhds_of_isClosed` read through `contMDiff_iff_contDiff`
for the model `modelWithCornersSelf ℝ (Vec d)`. -/

/-- **Global smooth realization.**  A function smooth on an open `S` is realized
*exactly* on any closed `K ⊆ S` by a function smooth on all of `ℝ^d`.  This is
the step that replaces mollification. -/
theorem exists_contDiff_eqOn_of_contDiffOn_isOpen {S : Set (Vec d)} (hS : IsOpen S)
    {K : Set (Vec d)} (hK : IsClosed K) (hKS : K ⊆ S) {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w S) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ Set.EqOn g w K := by
  classical
  obtain ⟨χ, h0, h1, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed
      (I := modelWithCornersSelf ℝ (Vec d)) (n := ⊤) (isClosed_compl_iff.2 hS) hK
      (Set.disjoint_left.mpr fun a ha hb => ha (hKS hb))
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : Vec d → ℝ) :=
    contMDiff_iff_contDiff.1 χ.contMDiff
  refine ⟨fun x => if x ∈ S then χ x * w x else 0, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ S
    · have hmem : S ∈ nhds x := hS.mem_nhds hx
      have hsmooth : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => χ y * w y) x :=
        hχ.contDiffAt.mul (hw.contDiffAt hmem)
      refine hsmooth.congr_of_eventuallyEq ?_
      filter_upwards [hmem] with y hy
      simp only [ite_eq_left hy]
    · have hxc : x ∈ Sᶜ := hx
      have hev : ∀ᶠ y in nhds x, χ y = 0 :=
        h0.filter_mono (nhds_le_nhdsSet hxc)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      by_cases hyS : y ∈ S
      · simp only [ite_eq_left hyS, hy, zero_mul]
      · simp only [ite_eq_right hyS]
  · intro x hx
    have hxS : x ∈ S := hKS hx
    have hone : χ x = 1 := h1.self_of_nhdsSet x hx
    simp only [ite_eq_left hxS, hone, one_mul]

/-- **The two sections combined.**  On a convex `U` with an interior ball, a function
smooth on `U` alone has a dilate that is realized on all of `closure U` by a
globally smooth function.  No mollification, no `Lp` convergence, no
approximation: the agreement is exact. -/
theorem exists_contDiff_eqOn_dilate_of_convex {U : Set (Vec d)} (hconv : Convex ℝ U)
    {c : Vec d} {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.ball c ρ ⊆ U)
    {lam : ℝ} (hlam : lam ∈ Set.Ico (0 : ℝ) 1) {v : Vec d → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      Set.EqOn g (fun x => v (c + lam • (x - c))) (closure U) :=
  exists_contDiff_eqOn_of_contDiffOn_isOpen (isOpen_dilationDomain c lam U)
    isClosed_closure (closure_subset_dilationDomain hconv hρ hball hlam)
    (contDiffOn_comp_dilate hv)

/-- Exact agreement on an open set transfers to the coordinate gradients, so the
realization of the previous theorem has the *same* `smoothGrad` as the dilate
throughout `U`.  Both summands of `h1sNormSqOn` therefore see the globally
smooth `g` and the dilate `v ∘ T` as the same object on `U`. -/
theorem smoothGrad_congr_of_eqOn_isOpen {S : Set (Vec d)} (hS : IsOpen S)
    {f g : Vec d → ℝ} (h : Set.EqOn f g S) {x : Vec d} (hx : x ∈ S) :
    smoothGrad f x = smoothGrad g x := by
  have hev : f =ᶠ[nhds x] g := Filter.eventuallyEq_of_mem (hS.mem_nhds hx) h
  have hfd : fderiv ℝ f x = fderiv ℝ g x := hev.fderiv_eq
  show (fun i => fderiv ℝ f x (basisVec i)) = fun i => fderiv ℝ g x (basisVec i)
  rw [hfd]

end

end HighContrast
end HCPolySupport
