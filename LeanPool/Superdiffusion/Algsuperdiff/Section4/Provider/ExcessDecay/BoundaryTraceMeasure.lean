/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionGlue

/-!
# BoundaryTraceMeasure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The trace measure of the boundary window: the zero extension and the slab

The unit needs two things beyond the analytic core of `BoundaryPoincareCore`:

1. **the trace carrier** — an `H¹₀(□_m)` datum, read on a cube `A` that pokes
   out of `□_m`, is an `H¹(A)` function that *vanishes identically* on the part
   of `A` outside `□_m`.  That part is the development's stand-in for the trace
   measure: the zero-trace hypothesis is converted into a **volume** statement,
   which is the only form the carriers support (no surface measure exists in
   CoarseGraining or Mathlib).  `zeroExtendH1` builds the `H¹(A)` function and
   `eLpNorm_zeroExtend_eq` / `eLpNorm_zeroExtendGrad_eq` say that its norms are
   the datum's own norms on `A ∩ □_m`.
2. **the slab bound** — a quantitative lower bound on the volume of that part.
   `volume_le_three_mul_slab` is the sharp form we need: if a set is a "box in
   the direction `e`" whose `g`-range `(lo, hi)` reaches at least a third of the
   way past a level `a`, then the whole set is at most three times the slab
   `{a ≤ g}`.  The proof is a *covering by three translates* of the slab — no
   product-measure computation, only translation invariance and subadditivity.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The zero extension as an `H¹` function on an arbitrary set -/

/-- Off its topological support a function has vanishing derivative. -/
theorem fderiv_apply_eq_zero_of_notMem_tsupport {φ : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport φ) (i : Fin d) : (fderiv ℝ φ x) (basisVec i) = 0 := by
  have hzero : φ =ᶠ[nhds x] 0 :=
    ((isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx).mono
      fun z hz => image_eq_zero_of_notMem_tsupport hz
  rw [hzero.fderiv_eq]
  simp only [fderiv_zero, Pi.zero_apply, zero_apply]

/-- A global weak-gradient graph restricts to every set: the test functions of
the smaller set are test functions of the ambient space, and both integrands
vanish off their support. -/
theorem hasWeakGradientOn_of_univ {V : Set (Vec d)} {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (h : HasWeakGradientOn Set.univ u Du) :
    HasWeakGradientOn V u Du := by
  intro i φ hφ hφc hφV
  have h1 := h i φ hφ hφc (by simp)
  rw [Measure.restrict_univ] at h1
  have hzero1 : ∀ x ∉ V, u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun hmem => hx (hφV hmem)) i,
      mul_zero]
  have hzero2 : ∀ x ∉ V, Du x i * φ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hφV hmem)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  exact h1

/-- **The zero extension of an `H¹₀(V)` datum, read on an arbitrary set `A`.**

The value and the gradient are the literal zero extensions of `OddReflectionGlue`;
the weak-gradient identity is its global one, restricted. -/
def zeroExtendH1 {V : Set (Vec d)} (hV : MeasurableSet V) (u : H10Function V)
    (A : Set (Vec d)) : H1Function A where
  toFun := zeroExtend V u.toFun
  grad := zeroExtendGrad V u.grad
  memL2 := (memL2_zeroExtend hV u).restrict A
  gradMemL2 := by
    intro i
    have h := gradMemL2_zeroExtendGrad hV u i
    rw [MemLpOn, Measure.restrict_univ] at h
    exact h.restrict A
  hasWeakGradient := hasWeakGradientOn_of_univ (hasWeakGradientOn_univ_zeroExtend hV u)

@[simp] theorem zeroExtendH1_toFun {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) (A : Set (Vec d)) :
    (zeroExtendH1 hV u A).toFun = zeroExtend V u.toFun := rfl

@[simp] theorem zeroExtendH1_grad {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) (A : Set (Vec d)) :
    (zeroExtendH1 hV u A).grad = zeroExtendGrad V u.grad := rfl

/-- The zero extension vanishes off `V`. -/
theorem zeroExtendH1_eq_zero_of_notMem {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) (A : Set (Vec d)) {y : Vec d} (hy : y ∉ V) :
    (zeroExtendH1 hV u A).toFun y = 0 :=
  zeroExtend_of_notMem _ hy

/-- The `L²` norm of the zero extension over `A` is the datum's own norm over
`A ∩ V`. -/
theorem eLpNorm_zeroExtend_eq {V : Set (Vec d)} (hV : MeasurableSet V)
    (f : Vec d → ℝ) (A : Set (Vec d)) :
    eLpNorm (zeroExtend V f) 2 (volume.restrict A) =
      eLpNorm f 2 (volume.restrict (A ∩ V)) := by
  rw [zeroExtend, eLpNorm_indicator_eq_eLpNorm_restrict hV,
    Measure.restrict_restrict hV, Set.inter_comm V A]

/-- The `L²` norm of a coordinate of the zero-extended gradient over `A` is the
datum's own norm over `A ∩ V`. -/
theorem eLpNorm_zeroExtendGrad_eq {V : Set (Vec d)} (hV : MeasurableSet V)
    (G : Vec d → Vec d) (A : Set (Vec d)) (i : Fin d) :
    eLpNorm (fun y => zeroExtendGrad V G y i) 2 (volume.restrict A) =
      eLpNorm (fun y => G y i) 2 (volume.restrict (A ∩ V)) := by
  rw [zeroExtendGrad_apply_coord, eLpNorm_indicator_eq_eLpNorm_restrict hV,
    Measure.restrict_restrict hV, Set.inter_comm V A]

/-! ## 2. The slab: three translates cover the box -/

/-- **The slab covering bound.**

If `A` is a box in the direction `e` — every point has `g`-value in `(lo, hi)`,
and shifting a point along `e` keeps it in `A` as long as the `g`-value stays in
`(lo, hi)` — and the level `a` sits within `hi` of the top and at least a third
of the `g`-range from the bottom (`a - 2(hi - a) ≤ lo`), then `A` is covered by
three translates of the slab `A ∩ {a ≤ g}`.

No measurability is required: the proof is `measure_mono` plus subadditivity
plus translation invariance. -/
theorem volume_le_three_mul_slab {A : Set (Vec d)} {g : Vec d → ℝ} {e : Vec d}
    {lo hi a : ℝ} (hg : ∀ (y : Vec d) (s : ℝ), g (y + s • e) = g y + s)
    (hrange : ∀ y ∈ A, lo < g y ∧ g y < hi)
    (hshift : ∀ y ∈ A, ∀ s : ℝ, lo < g y + s → g y + s < hi → y + s • e ∈ A)
    (hah : a < hi) (halo : a - 2 * (hi - a) ≤ lo) :
    volume A ≤ 3 * volume (A ∩ {y | a ≤ g y}) := by
  classical
  set S : Set (Vec d) := A ∩ {y | a ≤ g y} with hSdef
  set t : ℝ := hi - a with htdef
  have ht : 0 < t := by simp only [htdef]; linarith only [hah]
  -- the three translates
  have hcover : A ⊆ ((fun y : Vec d => y + (0 : ℝ) • e) ⁻¹' S) ∪
      ((fun y : Vec d => y + t • e) ⁻¹' S) ∪
      ((fun y : Vec d => y + (2 * t) • e) ⁻¹' S) := by
    intro y hy
    obtain ⟨hlo, hhi⟩ := hrange y hy
    by_cases h0 : a ≤ g y
    · refine Or.inl (Or.inl ?_)
      simp only [Set.mem_preimage, hSdef, Set.mem_inter_iff, Set.mem_ofPred_eq,
        zero_smul, add_zero]
      exact ⟨hy, h0⟩
    · push Not at h0
      by_cases h1 : a - t ≤ g y
      · refine Or.inl (Or.inr ?_)
        have hmemA : y + t • e ∈ A := by
          refine hshift y hy t ?_ ?_
          · linarith only [hlo, ht]
          · simp only [htdef]; linarith only [h0]
        simp only [Set.mem_preimage, hSdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨hmemA, by rw [hg y t]; linarith only [h1]⟩
      · push Not at h1
        refine Or.inr ?_
        have hmemA : y + (2 * t) • e ∈ A := by
          refine hshift y hy (2 * t) ?_ ?_
          · linarith only [hlo, ht]
          · simp only [htdef]; linarith only [h1]
        simp only [Set.mem_preimage, hSdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
        refine ⟨hmemA, ?_⟩
        rw [hg y (2 * t)]
        have : a - 2 * t ≤ lo := by simp only [htdef]; linarith only [halo]
        linarith only [hlo, this]
  have htrans : ∀ c : ℝ, volume ((fun y : Vec d => y + c • e) ⁻¹' S) = volume S :=
    fun c => measure_preimage_add_right volume (c • e) S
  calc volume A
      ≤ volume (((fun y : Vec d => y + (0 : ℝ) • e) ⁻¹' S) ∪
          ((fun y : Vec d => y + t • e) ⁻¹' S) ∪
          ((fun y : Vec d => y + (2 * t) • e) ⁻¹' S)) := measure_mono hcover
    _ ≤ volume (((fun y : Vec d => y + (0 : ℝ) • e) ⁻¹' S) ∪
            ((fun y : Vec d => y + t • e) ⁻¹' S)) +
          volume ((fun y : Vec d => y + (2 * t) • e) ⁻¹' S) := measure_union_le _ _
    _ ≤ (volume ((fun y : Vec d => y + (0 : ℝ) • e) ⁻¹' S) +
            volume ((fun y : Vec d => y + t • e) ⁻¹' S)) +
          volume ((fun y : Vec d => y + (2 * t) • e) ⁻¹' S) :=
        add_le_add (measure_union_le _ _) le_rfl
    _ = 3 * volume S := by
        rw [htrans 0, htrans t, htrans (2 * t)]
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
