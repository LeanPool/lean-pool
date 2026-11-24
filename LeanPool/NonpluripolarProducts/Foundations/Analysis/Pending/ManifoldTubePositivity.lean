/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalTubeFunction
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerPerturbation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothDDCForm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateDensityGeometry

/-!
# Step 6 of `prop:principalization` on the manifold

Source: Copy-4, step 6 of the proof of `prop:principalization`:

> For `B ≫ 1`, there is a relatively compact neighborhood `U` of `W` on a
> neighborhood of whose closure
> `Ω_U := θ_Y - Θ_D - ½δ₀ π^*ω + ddᶜ(fTilde + B r_W²) > 0`:
> indeed, along `W` the restriction of `Ω_U` to `T_W` is `A_W`, while the Levi
> form of `r_W²` is positive semidefinite with kernel exactly `T_W`.

`Pending.GlobalTubeFunction` builds `r_W²` and its Levi properties;
`Pending.UniformTubePositivity` and `Pending.PlaneTubePositivity` carry the
pointwise and uniform linear algebra.  This file does the manifold bookkeeping:

* `ddcClosedForm`: `ddᶜψ` of a chart-smooth function as a genuine
  `ClosedRealOneOneForm`, so that `β + B • ddᶜψ` is a form and chart-independence
  of strict positivity (`Pending.KahlerPerturbation`) applies to it.  The type
  `(1,1)` field is `FirstPass.MongeAmpere.smoothDDC_isOneOne`, the closedness
  field is `d² = 0`.
* `exists_pos_forall_strictPosAt_add_smul_ddc`: the sentence above, with `r_W²`
  abstracted to any chart-smooth `ρ` whose Levi form along the compact `W` is
  semipositive and on whose null directions `β` is positive.  ONE constant `B`
  and ONE open `U ⊇ W`, which is the manuscript's quantifier order.
* `exists_tube_forall_strictPosAt`: the two combined — for a compact submanifold
  `W` and a form `β` positive on the tangent directions of `W`, the tube function
  and the constant exist together.

The constant cannot be taken monotonically large uniformly on a neighbourhood:
the patched tube is only semipositive *along* `W` (the partition-of-unity cross
terms change sign off `W`), so the finite subcover argument has to close at the
points of `W` and use openness of strict positivity afterwards.  That is the
shape of `Pending.UniformTubePositivity.
exists_isStrictlyPositive_add_smul_of_pos_on_null_atCompact`, reproduced here on
the manifold because `StrictPosAt` is not a statement about a fixed chart.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

open FirstPass FirstPass.PositiveClasses PositivityPerturbation
  PlaneTubePositivity UniformTubePositivity KahlerPerturbation
  SmoothDDCForm GlobalTubeFunction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### `ddᶜψ` as a closed real `(1,1)`-form -/

/-- **`ddᶜψ` of a chart-smooth function as a closed real `(1,1)`-form.**
`Pending.SmoothDDCForm.ddcForm` already bundles the overlap law; the two
remaining fields are `d² = 0` and the `J`-invariance of `smoothDDC`. -/
def ddcClosedForm (ψ : M → ℝ) (hψ : ChartSmooth (n := n) ψ) :
    ClosedRealOneOneForm n M :=
  ⟨ddcForm ψ hψ, SmoothRealForm.exteriorDerivative_isClosed _, by
    intro e z hz u v
    rw [ddcForm_coeff]
    exact MongeAmpere.smoothDDC_isOneOne
      (((hψ e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) u v⟩

@[simp] theorem ddcClosedForm_coeff (ψ : M → ℝ) (hψ : ChartSmooth (n := n) ψ)
    (e : ComplexChart n M) :
    (ddcClosedForm ψ hψ).val.coeff e = smoothDDC fun z => ψ (e.val.symm z) := rfl

/-- The quadratic form of `ddᶜψ` in a chart is the Levi form of the chart
representation, divided by `π`. -/
theorem quad_ddcClosedForm_coeff {ψ : M → ℝ} (hψ : ChartSmooth (n := n) ψ)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (v : ComplexModel n) :
    quad ((ddcClosedForm ψ hψ).val.coeff e z) v =
      leviForm (fun w => ψ (e.val.symm w)) z v / Real.pi := by
  rw [ddcClosedForm_coeff]
  exact smoothDDC_complexDiagonal_eq_leviForm
    (((hψ e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v

/-! ### Strict positivity of `β + B ddᶜρ` near a compact set -/

theorem isOpen_setOf_strictPosAt (α : SmoothRealForm n M 2) :
    IsOpen {y : M | StrictPosAt α y} :=
  isOpen_iff_mem_nhds.2 fun _ hy => hy.eventually

/-- **Step 6's positivity sentence, on the manifold.**  If the Levi form of the
chart-smooth `ρ` is semipositive at every point of the compact `W`, and `β` is
strictly positive on its null directions there, then one constant `B` and one
open `U ⊇ W` make `β + B ddᶜρ` strictly positive on all of `U`.

Only the preferred chart at each point of `W` appears in the hypotheses;
`Pending.KahlerPerturbation.StrictPosAt.isStrictlyPositive` turns the conclusion
into strict positivity in every chart. -/
theorem exists_pos_forall_strictPosAt_add_smul_ddc
    {W : Set M} (hW : IsCompact W) (β : ClosedRealOneOneForm n M)
    {ρ : M → ℝ} (hρ : ChartSmooth (n := n) ρ)
    (hsemi : ∀ w ∈ W, ∀ v : ComplexModel n,
      0 ≤ leviForm (fun z => ρ ((complexChartAt (n := n) w).val.symm z))
        ((complexChartAt (n := n) w).val w) v)
    (hpos : ∀ w ∈ W, ∀ v : ComplexModel n, v ≠ 0 →
      leviForm (fun z => ρ ((complexChartAt (n := n) w).val.symm z))
        ((complexChartAt (n := n) w).val w) v = 0 →
      0 < quad (β.val.coeff (complexChartAt (n := n) w)
        ((complexChartAt (n := n) w).val w)) v) :
    ∃ B : ℝ, 0 < B ∧ ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧
      ∀ y ∈ U, StrictPosAt (β + B • ddcClosedForm ρ hρ).val y := by
  classical
  set γ : ClosedRealOneOneForm n M := ddcClosedForm ρ hρ with hγ
  -- the two pointwise hypotheses, in the `quad` language of the linear algebra
  have hmem : ∀ w : M, (complexChartAt (n := n) w).val w ∈
      (complexChartAt (n := n) w).val.target :=
    fun w => (complexChartAt (n := n) w).val.map_source (mem_complexChartAt_source w)
  have hb : ∀ w ∈ W, ∀ v : ComplexModel n,
      0 ≤ quad (γ.val.coeff (complexChartAt (n := n) w)
        ((complexChartAt (n := n) w).val w)) v := by
    intro w hw v
    rw [hγ, quad_ddcClosedForm_coeff hρ _ (hmem w) v]
    exact div_nonneg (hsemi w hw v) Real.pi_nonneg
  have ha : ∀ w ∈ W, ∀ v : ComplexModel n, v ≠ 0 →
      quad (γ.val.coeff (complexChartAt (n := n) w)
        ((complexChartAt (n := n) w).val w)) v = 0 →
      0 < quad (β.val.coeff (complexChartAt (n := n) w)
        ((complexChartAt (n := n) w).val w)) v := by
    intro w hw v hv hnull
    rw [hγ, quad_ddcClosedForm_coeff hρ _ (hmem w) v, div_eq_zero_iff] at hnull
    rcases hnull with h | h
    · exact hpos w hw v hv h
    · exact absurd h Real.pi_ne_zero
  -- the coefficient of the perturbed form
  have hcoeff : ∀ (B : ℝ) (e : ComplexChart n M) (z : ComplexModel n),
      (β + B • γ).val.coeff e z = β.val.coeff e z + B • γ.val.coeff e z := by
    intro B e z
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
  set N : ℝ → Set M := fun B => {y : M | StrictPosAt (β + B • γ).val y} with hN
  have hNopen : ∀ B : ℝ, IsOpen (N B) := fun B => isOpen_setOf_strictPosAt _
  have hcover : W ⊆ ⋃ j : ℕ, N ((j : ℝ) + 1) := by
    intro w hw
    obtain ⟨B₁, hB₁, hB₁pos⟩ :=
      exists_isStrictlyPositive_add_smul_of_pos_on_null (hb w hw) (ha w hw)
    obtain ⟨j, hj⟩ := exists_nat_ge B₁
    refine mem_iUnion.2 ⟨j, ?_⟩
    change StrictPosAt (β + ((j : ℝ) + 1) • γ).val w
    rw [StrictPosAt, hcoeff]
    exact hB₁pos _ (le_trans hj (by linarith))
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun j : ℕ => N ((j : ℝ) + 1))
    (fun j => hNopen _) hcover
  set B₀ : ℝ := ((t.sup id : ℕ) : ℝ) + 1 with hB₀
  have hWsub : W ⊆ N B₀ := by
    intro w hw
    obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.mp (ht hw)
    have hjs : (j : ℕ) ≤ t.sup id := Finset.le_sup (f := id) hj
    have hle : (j : ℝ) + 1 ≤ B₀ := by
      have : (j : ℝ) ≤ ((t.sup id : ℕ) : ℝ) := Nat.cast_le.mpr hjs
      rw [hB₀]; linarith
    have hwj' : IsStrictlyPositive
        (β.val.coeff (complexChartAt (n := n) w) ((complexChartAt (n := n) w).val w)
          + ((j : ℝ) + 1) • γ.val.coeff (complexChartAt (n := n) w)
            ((complexChartAt (n := n) w).val w)) := by
      have h : StrictPosAt (β + ((j : ℝ) + 1) • γ).val w := hwj
      rw [StrictPosAt, hcoeff] at h
      exact h
    change StrictPosAt (β + B₀ • γ).val w
    rw [StrictPosAt, hcoeff]
    exact isStrictlyPositive_add_smul_mono (hb w hw) hle hwj'
  exact ⟨B₀, by rw [hB₀]; positivity, N B₀, hNopen _, hWsub, fun _ hy => hy⟩

/-! ### The tube and the constant, together -/

/-- **Step 6 of `prop:principalization`.**  On a compact complex manifold, let `W`
be a closed set all of whose points are regular of dimension `k`, and let `β` be a
closed real `(1,1)`-form which is strictly positive along the tangent directions
of `W` — i.e. on the kernel of the differential of every NONDEGENERATE holomorphic
flattening of `W` in every ambient chart.  Then there are a chart-smooth `r ≥ 0`
vanishing on `W`, a constant `B > 0` and an open `U ⊇ W` with `β + B ddᶜr` strictly
positive on `U`.

The injectivity clause in `hβ` is not decoration: without it, replacing
the last `n - k` coordinates of a flattening by their squares produces another
admissible `F` whose differential vanishes on the normal directions, and `hβ`
would collapse to strict positivity of `β` in ALL directions along `W` — which
Copy-4 does not have, and which would make the tube redundant.

Discharging a hypothesis quantified over ALL nondegenerate flattenings still needs
the independence of `(dF)⁻¹(ℂᵏ × 0)` from `F`, which is not in the tree.  A
consumer that does not want to prove it should use the two-step route instead:
`Pending.GlobalTubeFunction.exists_chartSmooth_tube` hands back one concrete
flattening per point, and `exists_pos_forall_strictPosAt_add_smul_ddc` above
consumes the Levi form of the tube directly, with no flattening in its
statement. -/
theorem exists_tube_forall_strictPosAt [CompactSpace M] {W : Set M} {k : ℕ}
    (hWclosed : IsClosed W) (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (β : ClosedRealOneOneForm n M)
    (hβ : ∀ (f : ComplexChart n M) (w : M), w ∈ W → w ∈ f.val.source →
      ∀ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
        IsOpen D → f.val w ∈ D → D ⊆ f.val.target → ContDiffOn ℂ ∞ F D →
        Function.Injective (fderiv ℝ F (f.val w)) →
        (∀ z ∈ D, (f.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) →
        ∀ v : ComplexModel n, v ≠ 0 →
          fderiv ℝ F (f.val w) v ∈ complexCoordinatePlane n k →
          0 < quad (β.val.coeff f (f.val w)) v) :
    ∃ (r : M → ℝ) (hr : ChartSmooth (n := n) r) (B : ℝ), 0 < B ∧
      (∀ y, 0 ≤ r y) ∧ (∀ w ∈ W, r w = 0) ∧
      ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧
        ∀ y ∈ U, StrictPosAt (β + B • ddcClosedForm r hr).val y := by
  obtain ⟨r, hr, hrnn, hrW, hlevi⟩ := exists_chartSmooth_tube hWclosed hWreg
  have hsemi : ∀ w ∈ W, ∀ v : ComplexModel n,
      0 ≤ leviForm (fun z => r ((complexChartAt (n := n) w).val.symm z))
        ((complexChartAt (n := n) w).val w) v := fun w hw v =>
    (hlevi (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)).1 v
  have hpos : ∀ w ∈ W, ∀ v : ComplexModel n, v ≠ 0 →
      leviForm (fun z => r ((complexChartAt (n := n) w).val.symm z))
        ((complexChartAt (n := n) w).val w) v = 0 →
      0 < quad (β.val.coeff (complexChartAt (n := n) w)
        ((complexChartAt (n := n) w).val w)) v := by
    intro w hw v hv hnull
    obtain ⟨-, F, D, hDopen, hzD, hDsub, hFholo, hFinj, hFflat, hker⟩ :=
      hlevi (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)
    exact hβ (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)
      F D hDopen hzD hDsub hFholo hFinj hFflat v hv (hker v hnull)
  obtain ⟨B, hB, U, hU, hWU, hposU⟩ :=
    exists_pos_forall_strictPosAt_add_smul_ddc hWclosed.isCompact β hr hsemi hpos
  exact ⟨r, hr, B, hB, hrnn, hrW, U, hU, hWU, hposU⟩

end

end SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
