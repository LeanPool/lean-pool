/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorResolvent.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorDensity
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Correspondence operator resolvent

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorGenerator_resolvent_exists`,
`correspondenceOperatorGenerator_resolvent_unique`,
`correspondenceOperatorValueResolvent_injective`,
`correspondenceOperatorValueResolvent_denseRange`.
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped Topology ContDiff

/-- Ordinary unrestricted Ginibre H¹, bundled as its value-gradient graph. -/
def correspondenceOperatorWeakSpace (n : ℕ) (hn : 0 < n) :
    Submodule ℝ (GinibreFullValueL2 n × GinibreFullGradientL2 n) where
  carrier := {p | IsGinibreDistributionalGradient n p.1 p.2}
  zero_mem' := ginibre_weak_gradient_distributional n hn 0 0 (ginibre_zero_weak_gradient n)
  add_mem' := by
    intro p q hp hq
    exact ginibreFullGradient_add hn p.1 q.1 p.2 q.2 hp hq
  smul_mem' := by
    intro c p hp
    exact ginibreFullGradient_smul hn p.1 p.2 hp c

theorem correspondenceOperatorWeakSpace_isClosed (n : ℕ) (hn : 0 < n) :
    IsClosed (correspondenceOperatorWeakSpace n hn : Set (GinibreFullValueL2 n ×
        GinibreFullGradientL2 n)) :=
  isClosed_ginibre_distributional_gradient_pairs n hn

/-- Convert the Hilbert graph coordinate to the physical weak gradient. -/
def correspondenceOperatorFormCoordinates (n : ℕ) :
    GinibreFullFormAmbient n →L[ℝ] (GinibreFullValueL2 n × GinibreFullGradientL2 n) :=
  (WithLp.fstL 2 ℝ (GinibreFullValueL2 n) (GinibreFullGradientL2 n)).prod
    (Real.sqrt (n : ℝ) • WithLp.sndL 2 ℝ (GinibreFullValueL2 n) (GinibreFullGradientL2 n))

/-- The unrestricted H¹ graph in the Hilbert normalization
`‖u‖² + (1/n) ‖grad u‖²`. -/
def correspondenceOperatorFormSpace (n : ℕ) (hn : 0 < n) : Submodule ℝ (GinibreFullFormAmbient n) :=
  (correspondenceOperatorWeakSpace n hn).comap (correspondenceOperatorFormCoordinates n).toLinearMap

theorem correspondenceOperatorFormSpace_isClosed (n : ℕ) (hn : 0 < n) :
    IsClosed (correspondenceOperatorFormSpace n hn : Set (GinibreFullFormAmbient n)) :=
  (correspondenceOperatorWeakSpace_isClosed n hn).preimage (correspondenceOperatorFormCoordinates
      n).continuous

instance correspondenceOperatorFormSpace_complete (n : ℕ) (hn : 0 < n) :
    CompleteSpace (correspondenceOperatorFormSpace n hn) :=
  (correspondenceOperatorFormSpace_isClosed n hn).completeSpace_coe

/-- Value projection from the full Hilbert graph. -/
def correspondenceOperatorFormValue (n : ℕ) (hn : 0 < n) :
    correspondenceOperatorFormSpace n hn →L[ℝ] GinibreFullValueL2 n :=
  (WithLp.fstL 2 ℝ (GinibreFullValueL2 n) (GinibreFullGradientL2 n)).comp
    (correspondenceOperatorFormSpace n hn).subtypeL

/-- Physical gradient projection from the full Hilbert graph. -/
def correspondenceOperatorFormGradient (n : ℕ) (hn : 0 < n) :
    correspondenceOperatorFormSpace n hn →L[ℝ] GinibreFullGradientL2 n :=
  Real.sqrt (n : ℝ) •
    (WithLp.sndL 2 ℝ (GinibreFullValueL2 n) (GinibreFullGradientL2 n)).comp
      (correspondenceOperatorFormSpace n hn).subtypeL

/-- The full weak-H¹ resolvent, constructed by the Riesz representation theorem. -/
def correspondenceOperatorFormResolvent (n : ℕ) (hn : 0 < n) (f : GinibreFullValueL2 n) :
    correspondenceOperatorFormSpace n hn :=
  (InnerProductSpace.toDual ℝ (correspondenceOperatorFormSpace n hn)).symm
    ((innerSL ℝ f).comp (correspondenceOperatorFormValue n hn))

theorem correspondenceOperatorFormResolvent_riesz (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) (q : correspondenceOperatorFormSpace n hn) :
    inner ℝ (correspondenceOperatorFormResolvent n hn f) q =
      inner ℝ f (correspondenceOperatorFormValue n hn q) :=
  InnerProductSpace.toDual_symm_apply

/-- Every graph point has the genuine ordinary weak gradient. -/
theorem correspondenceOperatorFormSpace_weak (n : ℕ) (hn : 0 < n)
    (p : correspondenceOperatorFormSpace n hn) :
    IsGinibreDistributionalGradient n (correspondenceOperatorFormValue n hn p)
      (correspondenceOperatorFormGradient n hn p) := p.property

/-- The Hilbert graph inner product is the value pairing plus the normalized
Dirichlet gradient pairing, with the paper's exact `1/n` factor. -/
theorem correspondenceOperatorFormSpace_inner (n : ℕ) (hn : 0 < n)
    (p q : correspondenceOperatorFormSpace n hn) :
    inner ℝ p q = inner ℝ (correspondenceOperatorFormValue n hn p) (correspondenceOperatorFormValue
        n hn q) +
      (1 / (n : ℝ)) * inner ℝ (correspondenceOperatorFormGradient n hn p)
          (correspondenceOperatorFormGradient n hn q) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  change inner ℝ p.val q.val = _
  rw [WithLp.prod_inner_apply]
  simp only [correspondenceOperatorFormValue, correspondenceOperatorFormGradient,
      ContinuousLinearMap.comp_apply,
    smul_apply, Submodule.subtypeL_apply, WithLp.fstL_apply, WithLp.sndL_apply,
    real_inner_smul_left, real_inner_smul_right]
  have hc : 1 / (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = 1 := by
    rw [mul_assoc, hs]
    exact div_mul_cancel₀ 1 hnR
  simp only [← mul_assoc]
  rw [hc, one_mul]
  rfl

/-- Every actual unrestricted weak pair has its normalized Hilbert graph point. -/
def correspondenceOperatorFormOfWeak (n : ℕ) (hn : 0 < n) (p : correspondenceOperatorWeakSpace n hn)
    :
    correspondenceOperatorFormSpace n hn := by
  refine ⟨WithLp.toLp 2 (p.val.1, (Real.sqrt (n : ℝ))⁻¹ • p.val.2), ?_⟩
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  change (p.val.1, Real.sqrt (n : ℝ) • ((Real.sqrt (n : ℝ))⁻¹ • p.val.2)) ∈
    correspondenceOperatorWeakSpace n hn
  simp only [smul_smul, mul_inv_cancel₀ hs, one_smul]
  exact p.property

@[simp] theorem correspondenceOperatorFormOfWeak_value (n : ℕ) (hn : 0 < n)
    (p : correspondenceOperatorWeakSpace n hn) :
    correspondenceOperatorFormValue n hn (correspondenceOperatorFormOfWeak n hn p) = p.val.1 := rfl

@[simp] theorem correspondenceOperatorFormOfWeak_gradient (n : ℕ) (hn : 0 < n)
    (p : correspondenceOperatorWeakSpace n hn) :
    correspondenceOperatorFormGradient n hn (correspondenceOperatorFormOfWeak n hn p) = p.val.2 :=
        by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  change Real.sqrt (n : ℝ) • ((Real.sqrt (n : ℝ))⁻¹ • p.val.2) = _
  simp [smul_smul, hs]

/-- The actual unrestricted weak-H¹ resolvent equation has a solution for
 every concrete Ginibre L² datum. All weak test pairs are included. -/
theorem correspondenceOperatorGenerator_resolvent_exists (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) :
    ∃ u : GinibreFullValueL2 n, ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u g ∧
      ∀ v : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n v h →
        inner ℝ u v + (1 / (n : ℝ)) * inner ℝ g h = inner ℝ f v := by
  let p := correspondenceOperatorFormResolvent n hn f
  refine ⟨correspondenceOperatorFormValue n hn p, correspondenceOperatorFormGradient n hn p,
    correspondenceOperatorFormSpace_weak n hn p, ?_⟩
  intro v h hv
  let q : correspondenceOperatorWeakSpace n hn := ⟨(v, h), hv⟩
  have hr := correspondenceOperatorFormResolvent_riesz n hn f (correspondenceOperatorFormOfWeak n hn
      q)
  rw [correspondenceOperatorFormSpace_inner, correspondenceOperatorFormOfWeak_value,
    correspondenceOperatorFormOfWeak_gradient] at hr
  exact hr

/-- The graph-norm resolvent is a contraction from the actual weighted L²
space into the full weak-H¹ Hilbert graph. -/
theorem correspondenceOperatorFormResolvent_norm_le (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) : ‖correspondenceOperatorFormResolvent n hn f‖ ≤ ‖f‖ := by
  let p := correspondenceOperatorFormResolvent n hn f
  have hr := correspondenceOperatorFormResolvent_riesz n hn f p
  rw [real_inner_self_eq_norm_sq] at hr
  have hvalue : ‖correspondenceOperatorFormValue n hn p‖ ≤ ‖p‖ :=
    WithLp.norm_fst_le (α := GinibreFullValueL2 n) (β := GinibreFullGradientL2 n) p.val
  have hi := real_inner_le_norm f (correspondenceOperatorFormValue n hn p)
  have hb : ‖p‖ ^ 2 ≤ ‖f‖ * ‖p‖ := by
    rw [hr]
    exact hi.trans (mul_le_mul_of_nonneg_left hvalue (norm_nonneg f))
  change ‖p‖ ≤ ‖f‖
  nlinarith [norm_nonneg p, norm_nonneg f]

/-- A full weak solution of the resolvent equation equals the concrete Riesz
solution in both value and physical gradient. -/
theorem correspondenceOperatorGenerator_resolvent_unique (n : ℕ) (hn : 0 < n)
    (f u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (heq : ∀ v : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n v h →
      inner ℝ u v + (1 / (n : ℝ)) * inner ℝ g h = inner ℝ f v) :
    u = correspondenceOperatorFormValue n hn (correspondenceOperatorFormResolvent n hn f) ∧
      g = correspondenceOperatorFormGradient n hn (correspondenceOperatorFormResolvent n hn f) := by
  let p : correspondenceOperatorWeakSpace n hn := ⟨(u, g), hu⟩
  let r := correspondenceOperatorFormOfWeak n hn p
  have hr : r = correspondenceOperatorFormResolvent n hn f := by
    apply ext_inner_right ℝ
    intro q
    rw [correspondenceOperatorFormResolvent_riesz, correspondenceOperatorFormSpace_inner,
      correspondenceOperatorFormOfWeak_value, correspondenceOperatorFormOfWeak_gradient]
    exact heq _ _ (correspondenceOperatorFormSpace_weak n hn q)
  constructor
  · have h := congrArg (correspondenceOperatorFormValue n hn) hr
    exact h
  · have h := congrArg (correspondenceOperatorFormGradient n hn) hr
    simpa [r, correspondenceOperatorFormOfWeak_gradient] using h

/-- The full graph resolvent is linear in its concrete L² datum. -/
def correspondenceOperatorFormResolventLinear (n : ℕ) (hn : 0 < n) :
    GinibreFullValueL2 n →ₗ[ℝ] correspondenceOperatorFormSpace n hn where
  toFun := correspondenceOperatorFormResolvent n hn
  map_add' := by
    intro f g
    unfold correspondenceOperatorFormResolvent
    rw [← map_add]
    congr 1
    ext q
    simp
  map_smul' := by
    intro c f
    unfold correspondenceOperatorFormResolvent
    rw [← map_smul]
    congr 1
    ext q
    simp

/-- The normalized full weak resolvent as a bounded linear map. -/
def correspondenceOperatorFormResolventCLM (n : ℕ) (hn : 0 < n) :
    GinibreFullValueL2 n →L[ℝ] correspondenceOperatorFormSpace n hn :=
  (correspondenceOperatorFormResolventLinear n hn).mkContinuous 1 (by
    intro f
    simpa [correspondenceOperatorFormResolventLinear] using
        correspondenceOperatorFormResolvent_norm_le n hn f)

/-- The value resolvent on the original concrete weighted L² space. -/
def correspondenceOperatorValueResolvent (n : ℕ) (hn : 0 < n) :
    GinibreFullValueL2 n →L[ℝ] GinibreFullValueL2 n :=
  (correspondenceOperatorFormValue n hn).comp (correspondenceOperatorFormResolventCLM n hn)

/-- The concrete full weak value resolvent is self-adjoint. -/
theorem correspondenceOperatorValueResolvent_symmetric (n : ℕ) (hn : 0 < n)
    (f h : GinibreFullValueL2 n) :
    inner ℝ (correspondenceOperatorValueResolvent n hn f) h =
      inner ℝ f (correspondenceOperatorValueResolvent n hn h) := by
  have hf := correspondenceOperatorFormResolvent_riesz n hn f (correspondenceOperatorFormResolvent n
      hn h)
  have hh := correspondenceOperatorFormResolvent_riesz n hn h (correspondenceOperatorFormResolvent n
      hn f)
  change inner ℝ (correspondenceOperatorFormValue n hn (correspondenceOperatorFormResolvent n hn f))
      h =
    inner ℝ f (correspondenceOperatorFormValue n hn (correspondenceOperatorFormResolvent n hn h))
  calc
    _ = inner ℝ h (correspondenceOperatorFormValue n hn (correspondenceOperatorFormResolvent n hn
        f)) :=
      real_inner_comm _ _
    _ = inner ℝ (correspondenceOperatorFormResolvent n hn h) (correspondenceOperatorFormResolvent n
        hn f) := hh.symm
    _ = inner ℝ (correspondenceOperatorFormResolvent n hn f) (correspondenceOperatorFormResolvent n
        hn h) :=
      real_inner_comm _ _
    _ = _ := hf

/-- Positivity of the full weak value resolvent, as an exact graph-norm identity. -/
theorem correspondenceOperatorValueResolvent_positive (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) :
    inner ℝ f (correspondenceOperatorValueResolvent n hn f) =
      ‖correspondenceOperatorFormResolvent n hn f‖ ^ 2 := by
  exact (correspondenceOperatorFormResolvent_riesz n hn f (correspondenceOperatorFormResolvent n hn
      f)).symm.trans
    (real_inner_self_eq_norm_sq _)

/-- Smooth compact tests belong to the unrestricted weak graph. -/
theorem correspondenceOperator_smoothCompact_pair (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ p : correspondenceOperatorWeakSpace n hn,
      (p.val.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f := by
  obtain ⟨hmv, hmg⟩ := ginibreFull_smoothCompact_memLp n hn f hf hc
  exact ⟨⟨(hmv.toLp f, hmg.toLp (ginibreEuclideanGradient f)),
    ginibre_smooth_distributional_gradient n hn _ _ f hf hmv.coeFn_toLp hmg.coeFn_toLp⟩,
    hmv.coeFn_toLp⟩

/-- Testing against all ordinary weak values separates unrestricted L². -/
theorem correspondenceOperator_orthogonal_weak_eq_zero (n : ℕ) (hn : 0 < n)
    (a : GinibreFullValueL2 n)
    (ha : ∀ p : correspondenceOperatorWeakSpace n hn, inner ℝ a p.val.1 = 0) : a = 0 := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have htest (ψ : Configuration n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      (∫ z, ψ z • a z ∂ginibreMeasure n) = 0 := by
    obtain ⟨p, hp⟩ := correspondenceOperator_smoothCompact_pair n hn ψ hψ hc
    have hh := ha p
    rw [L2.inner_def] at hh
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [hp] with z hz
    change ψ z * a z = p.val.1 z*a z
    rw [hz]
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp a).integrable (by norm_num)).locallyIntegrable htest
  apply Lp.ext
  filter_upwards [hz] with z hz
  simpa using hz

theorem correspondenceOperatorValueResolvent_eq_zero_iff (n : ℕ) (hn : 0 < n)
    (f : GinibreFullValueL2 n) : correspondenceOperatorValueResolvent n hn f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    have hnorm := correspondenceOperatorValueResolvent_positive n hn f
    rw [hz, inner_zero_right] at hnorm
    have hR : correspondenceOperatorFormResolvent n hn f = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (correspondenceOperatorFormResolvent n hn f)]
    apply correspondenceOperator_orthogonal_weak_eq_zero n hn f
    intro p
    have hr := correspondenceOperatorFormResolvent_riesz n hn f (correspondenceOperatorFormOfWeak n
        hn p)
    rw [hR, inner_zero_left, correspondenceOperatorFormOfWeak_value] at hr
    exact hr.symm
  · intro hz
    simp [hz]

theorem correspondenceOperatorValueResolvent_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (correspondenceOperatorValueResolvent n hn) := by
  intro f h heq
  have hz : correspondenceOperatorValueResolvent n hn (f-h)=0 := by
    rw [map_sub, heq, sub_self]
  exact sub_eq_zero.mp ((correspondenceOperatorValueResolvent_eq_zero_iff n hn (f-h)).mp hz)

theorem correspondenceOperatorValueResolvent_denseRange (n : ℕ) (hn : 0 < n) :
    DenseRange (correspondenceOperatorValueResolvent n hn) := by
  let K := (correspondenceOperatorValueResolvent n hn).toLinearMap.range.topologicalClosure
  let : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    have hRa : correspondenceOperatorValueResolvent n hn a = 0 := by
      apply ext_inner_right ℝ
      intro f
      have hmem : correspondenceOperatorValueResolvent n hn f ∈ K :=
        Submodule.le_topologicalClosure _ ⟨f, rfl⟩
      have hzero := (Submodule.mem_orthogonal' K a).mp ha _ hmem
      rw [correspondenceOperatorValueResolvent_symmetric]
      simpa using hzero
    exact (correspondenceOperatorValueResolvent_eq_zero_iff n hn a).mp hRa
  have hK : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp horth
  change Dense (Set.range (correspondenceOperatorValueResolvent n hn))
  rw [dense_iff_closure_eq]
  change closure ((correspondenceOperatorValueResolvent n hn).toLinearMap.range : Set
      (GinibreFullValueL2 n)) = Set.univ
  rw [← Submodule.topologicalClosure_coe]
  change (K : Set (GinibreFullValueL2 n)) = Set.univ
  rw [hK]
  rfl

end
end GinibrePoincare
