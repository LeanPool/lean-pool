/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorResolvent.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorWeakSpace
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Ginibre Full Generator Resolvent
-/


@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped Topology

abbrev GinibreFullFormAmbient (n : ℕ) := WithLp 2 (GinibreFullValueL2 n × GinibreFullGradientL2 n)

/-- Convert the Hilbert graph coordinate to the physical weak gradient. -/
def ginibreFullFormCoordinates (n : ℕ) :
    GinibreFullFormAmbient n →L[ℝ] (GinibreFullValueL2 n × GinibreFullGradientL2 n) :=
  (WithLp.fstL 2 ℝ (GinibreFullValueL2 n) (GinibreFullGradientL2 n)).prod
    (Real.sqrt (n : ℝ) • WithLp.sndL 2 ℝ (GinibreFullValueL2 n) (GinibreFullGradientL2 n))

/-- The full symmetric H¹ graph in the Hilbert normalization
`‖u‖² + (1/n) ‖grad u‖²`. -/
def ginibreFullFormSpace (n : ℕ) (hn : 0 < n) : Submodule ℝ (GinibreFullFormAmbient n) :=
  (ginibreFullWeakSpace n hn).comap (ginibreFullFormCoordinates n).toLinearMap

theorem ginibreFullFormSpace_isClosed (n : ℕ) (hn : 0 < n) :
    IsClosed (ginibreFullFormSpace n hn : Set (GinibreFullFormAmbient n)) :=
  (ginibreFullWeakSpace_isClosed n hn).preimage (ginibreFullFormCoordinates n).continuous

instance ginibreFullFormSpace_complete (n : ℕ) (hn : 0 < n) :
    CompleteSpace (ginibreFullFormSpace n hn) :=
  (ginibreFullFormSpace_isClosed n hn).completeSpace_coe

/-- Value projection from the full Hilbert graph. -/
def ginibreFullFormValue (n : ℕ) (hn : 0 < n) :
    ginibreFullFormSpace n hn →L[ℝ] GinibreFullValueL2 n :=
  (WithLp.fstL 2 ℝ (GinibreFullValueL2 n) (GinibreFullGradientL2 n)).comp
    (ginibreFullFormSpace n hn).subtypeL

/-- Physical gradient projection from the full Hilbert graph. -/
def ginibreFullFormGradient (n : ℕ) (hn : 0 < n) :
    ginibreFullFormSpace n hn →L[ℝ] GinibreFullGradientL2 n :=
  Real.sqrt (n : ℝ) •
    (WithLp.sndL 2 ℝ (GinibreFullValueL2 n) (GinibreFullGradientL2 n)).comp
      (ginibreFullFormSpace n hn).subtypeL

/-- The full weak-H¹ resolvent, constructed by the Riesz representation theorem. -/
def ginibreFullFormResolvent (n : ℕ) (hn : 0 < n) (f : GinibreFullValueL2 n) :
    ginibreFullFormSpace n hn :=
  (InnerProductSpace.toDual ℝ (ginibreFullFormSpace n hn)).symm
    ((innerSL ℝ f).comp (ginibreFullFormValue n hn))

theorem ginibreFullFormResolvent_riesz (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) (q : ginibreFullFormSpace n hn) :
    inner ℝ (ginibreFullFormResolvent n hn f) q =
      inner ℝ f (ginibreFullFormValue n hn q) :=
  InnerProductSpace.toDual_symm_apply

/-- Every point of the form Hilbert space is a genuine symmetric weak pair. -/
theorem ginibreFullFormSpace_weak (n : ℕ) (hn : 0 < n)
    (p : ginibreFullFormSpace n hn) :
    IsGinibreDistributionalGradient n (ginibreFullFormValue n hn p)
      (ginibreFullFormGradient n hn p) ∧
    IsGinibreSymmetricWeakPair (ginibreFullFormValue n hn p, ginibreFullFormGradient n hn p) :=
  p.property

/-- The Hilbert graph inner product is the value pairing plus the normalized
Dirichlet gradient pairing, with the paper's exact `1/n` factor. -/
theorem ginibreFullFormSpace_inner (n : ℕ) (hn : 0 < n)
    (p q : ginibreFullFormSpace n hn) :
    inner ℝ p q = inner ℝ (ginibreFullFormValue n hn p) (ginibreFullFormValue n hn q) +
      (1 / (n : ℝ)) * inner ℝ (ginibreFullFormGradient n hn p) (ginibreFullFormGradient n hn q) :=
        by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  change inner ℝ p.val q.val = _
  rw [WithLp.prod_inner_apply]
  simp only [ginibreFullFormValue, ginibreFullFormGradient, ContinuousLinearMap.comp_apply,
    smul_apply, Submodule.subtypeL_apply, WithLp.fstL_apply, WithLp.sndL_apply,
    real_inner_smul_left, real_inner_smul_right]
  have hc : 1 / (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = 1 := by
    rw [mul_assoc, hs]
    exact div_mul_cancel₀ 1 hnR
  simp only [← mul_assoc]
  rw [hc, one_mul]
  rfl


/-- Every actual symmetric weak pair has its normalized Hilbert graph point. -/
def ginibreFullFormOfWeak (n : ℕ) (hn : 0 < n) (p : ginibreFullWeakSpace n hn) :
    ginibreFullFormSpace n hn := by
  refine ⟨WithLp.toLp 2 (p.val.1, (Real.sqrt (n : ℝ))⁻¹ • p.val.2), ?_⟩
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  change (p.val.1, Real.sqrt (n : ℝ) • ((Real.sqrt (n : ℝ))⁻¹ • p.val.2)) ∈
    ginibreFullWeakSpace n hn
  simp only [smul_smul, mul_inv_cancel₀ hs, one_smul]
  exact p.property

@[simp] theorem ginibreFullFormOfWeak_value (n : ℕ) (hn : 0 < n)
    (p : ginibreFullWeakSpace n hn) :
    ginibreFullFormValue n hn (ginibreFullFormOfWeak n hn p) = p.val.1 := rfl

@[simp] theorem ginibreFullFormOfWeak_gradient (n : ℕ) (hn : 0 < n)
    (p : ginibreFullWeakSpace n hn) :
    ginibreFullFormGradient n hn (ginibreFullFormOfWeak n hn p) = p.val.2 := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  change Real.sqrt (n : ℝ) • ((Real.sqrt (n : ℝ))⁻¹ • p.val.2) = _
  simp [smul_smul, hs]

/-- The actual full symmetric weak-H¹ resolvent equation has a solution for
 every concrete Ginibre L² datum. All weak test pairs are included. -/
theorem ginibreFullGenerator_resolvent_exists (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) :
    ∃ u : GinibreFullValueL2 n, ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u g ∧ IsGinibreSymmetricWeakPair (u, g) ∧
      ∀ v : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n v h → IsGinibreSymmetricWeakPair (v, h) →
        inner ℝ u v + (1 / (n : ℝ)) * inner ℝ g h = inner ℝ f v := by
  let p := ginibreFullFormResolvent n hn f
  refine ⟨ginibreFullFormValue n hn p, ginibreFullFormGradient n hn p,
    (ginibreFullFormSpace_weak n hn p).1, (ginibreFullFormSpace_weak n hn p).2, ?_⟩
  intro v h hv hs
  let q : ginibreFullWeakSpace n hn := ⟨(v, h), hv, hs⟩
  have hr := ginibreFullFormResolvent_riesz n hn f (ginibreFullFormOfWeak n hn q)
  rw [ginibreFullFormSpace_inner, ginibreFullFormOfWeak_value,
    ginibreFullFormOfWeak_gradient] at hr
  exact hr

/-- The graph-norm resolvent is a contraction from the actual weighted L²
space into the full weak-H¹ Hilbert graph. -/
theorem ginibreFullFormResolvent_norm_le (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) : ‖ginibreFullFormResolvent n hn f‖ ≤ ‖f‖ := by
  let p := ginibreFullFormResolvent n hn f
  have hr := ginibreFullFormResolvent_riesz n hn f p
  rw [real_inner_self_eq_norm_sq] at hr
  have hvalue : ‖ginibreFullFormValue n hn p‖ ≤ ‖p‖ :=
    WithLp.norm_fst_le (α := GinibreFullValueL2 n) (β := GinibreFullGradientL2 n) p.val
  have hi := real_inner_le_norm f (ginibreFullFormValue n hn p)
  have hb : ‖p‖ ^ 2 ≤ ‖f‖ * ‖p‖ := by
    rw [hr]
    exact hi.trans (mul_le_mul_of_nonneg_left hvalue (norm_nonneg f))
  change ‖p‖ ≤ ‖f‖
  nlinarith [norm_nonneg p, norm_nonneg f]


/-- A full weak solution of the resolvent equation equals the concrete Riesz
solution in both value and physical gradient. -/
theorem ginibreFullGenerator_resolvent_unique (n : ℕ) (hn : 0 < n)
    (f u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g))
    (heq : ∀ v : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n v h → IsGinibreSymmetricWeakPair (v, h) →
      inner ℝ u v + (1 / (n : ℝ)) * inner ℝ g h = inner ℝ f v) :
    u = ginibreFullFormValue n hn (ginibreFullFormResolvent n hn f) ∧
      g = ginibreFullFormGradient n hn (ginibreFullFormResolvent n hn f) := by
  let p : ginibreFullWeakSpace n hn := ⟨(u, g), hu, hs⟩
  let r := ginibreFullFormOfWeak n hn p
  have hr : r = ginibreFullFormResolvent n hn f := by
    apply ext_inner_right ℝ
    intro q
    rw [ginibreFullFormResolvent_riesz, ginibreFullFormSpace_inner,
      ginibreFullFormOfWeak_value, ginibreFullFormOfWeak_gradient]
    exact heq _ _ (ginibreFullFormSpace_weak n hn q).1
      (ginibreFullFormSpace_weak n hn q).2
  constructor
  · have h := congrArg (ginibreFullFormValue n hn) hr
    exact h
  · have h := congrArg (ginibreFullFormGradient n hn) hr
    simpa [r, ginibreFullFormOfWeak_gradient] using h


/-- The full graph resolvent is linear in its concrete L² datum. -/
def ginibreFullFormResolventLinear (n : ℕ) (hn : 0 < n) :
    GinibreFullValueL2 n →ₗ[ℝ] ginibreFullFormSpace n hn where
  toFun := ginibreFullFormResolvent n hn
  map_add' := by
    intro f g
    unfold ginibreFullFormResolvent
    rw [← map_add]
    congr 1
    ext q
    simp
  map_smul' := by
    intro c f
    unfold ginibreFullFormResolvent
    rw [← map_smul]
    congr 1
    ext q
    simp

/-- The normalized full weak resolvent as a bounded linear map. -/
def ginibreFullFormResolventCLM (n : ℕ) (hn : 0 < n) :
    GinibreFullValueL2 n →L[ℝ] ginibreFullFormSpace n hn :=
  (ginibreFullFormResolventLinear n hn).mkContinuous 1 (by
    intro f
    simpa [ginibreFullFormResolventLinear] using ginibreFullFormResolvent_norm_le n hn f)

/-- The value resolvent on the original concrete weighted L² space. -/
def ginibreFullValueResolvent (n : ℕ) (hn : 0 < n) :
    GinibreFullValueL2 n →L[ℝ] GinibreFullValueL2 n :=
  (ginibreFullFormValue n hn).comp (ginibreFullFormResolventCLM n hn)

/-- The concrete full weak value resolvent is self-adjoint. -/
theorem ginibreFullValueResolvent_symmetric (n : ℕ) (hn : 0 < n)
    (f h : GinibreFullValueL2 n) :
    inner ℝ (ginibreFullValueResolvent n hn f) h =
      inner ℝ f (ginibreFullValueResolvent n hn h) := by
  have hf := ginibreFullFormResolvent_riesz n hn f (ginibreFullFormResolvent n hn h)
  have hh := ginibreFullFormResolvent_riesz n hn h (ginibreFullFormResolvent n hn f)
  change inner ℝ (ginibreFullFormValue n hn (ginibreFullFormResolvent n hn f)) h =
    inner ℝ f (ginibreFullFormValue n hn (ginibreFullFormResolvent n hn h))
  calc
    _ = inner ℝ h (ginibreFullFormValue n hn (ginibreFullFormResolvent n hn f)) :=
      real_inner_comm _ _
    _ = inner ℝ (ginibreFullFormResolvent n hn h) (ginibreFullFormResolvent n hn f) := hh.symm
    _ = inner ℝ (ginibreFullFormResolvent n hn f) (ginibreFullFormResolvent n hn h) :=
      real_inner_comm _ _
    _ = _ := hf

/-- Positivity of the full weak value resolvent, as an exact graph-norm identity. -/
theorem ginibreFullValueResolvent_positive (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) :
    inner ℝ f (ginibreFullValueResolvent n hn f) =
      ‖ginibreFullFormResolvent n hn f‖ ^ 2 := by
  exact (ginibreFullFormResolvent_riesz n hn f (ginibreFullFormResolvent n hn f)).symm.trans
    (real_inner_self_eq_norm_sq _)

end
end GinibrePoincare
