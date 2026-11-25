/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# Functional calculus of positive contractions

The spectrum of a positive contraction lies in the unit interval. This
allows scalar identities on that interval to be lifted to bounded operators
on a real Hilbert space.
-/

public section

open scoped InnerProductSpace Pointwise

namespace CutoffRigidity.Riemann.Diff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A self-adjoint operator with quadratic form bounded below by zero and above by the identity. -/
structure UnitOp (R : H →L[ℝ] H) : Prop where
  selfAdjoint : IsSelfAdjoint R
  nonneg : ∀ x, 0 ≤ inner ℝ (R x) x
  le_one : ∀ x, inner ℝ (R x) x ≤ inner ℝ x x

theorem UnitOp.spectrum_subset {R : H →L[ℝ] H} (hR : UnitOp R) :
    spectrum ℝ R ⊆ Set.Icc 0 1 := by
  have hpositive : R.IsPositive :=
    ContinuousLinearMap.isPositive_def'.2 ⟨hR.selfAdjoint, hR.nonneg⟩
  have hcomplement : (1 - R).IsPositive := ContinuousLinearMap.isPositive_def'.2
    ⟨(IsSelfAdjoint.one _).sub hR.selfAdjoint, fun x => by
      change 0 ≤ inner ℝ ((1 - R) x) x
      simpa only [sub_apply, one_apply_eq_self, inner_sub_left,
        sub_nonneg] using hR.le_one x⟩
  have h0 := SpectrumRestricts.nnreal_iff.mp hpositive.spectrumRestricts
  have h1 := SpectrumRestricts.nnreal_iff.mp hcomplement.spectrumRestricts
  intro x hx
  refine ⟨h0 x hx, sub_nonneg.mp (h1 (1 - x) ?_)⟩
  have hmem : 1 - x ∈ ({1} : Set ℝ) - spectrum ℝ R := ⟨1, rfl, x, hx, rfl⟩
  rwa [spectrum.singleton_sub_eq, map_one] at hmem

variable {R : H →L[ℝ] H} (hR : UnitOp R)

include hR

lemma UnitOp.rcfc_id : cfc (id : ℝ → ℝ) R = R :=
  cfc_id ℝ R hR.selfAdjoint

lemma UnitOp.rcfc_id' : cfc (fun x : ℝ => x) R = R :=
  cfc_id' ℝ R hR.selfAdjoint

lemma UnitOp.rcfc_one : cfc (fun _ : ℝ => (1 : ℝ)) R = 1 :=
  cfc_const_one ℝ R (ha := hR.selfAdjoint)

lemma UnitOp.rcfc_add {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    cfc (fun x => f x + g x) R = cfc f R + cfc g R :=
  cfc_add R f g (hf.mono hR.spectrum_subset) (hg.mono hR.spectrum_subset)

lemma UnitOp.rcfc_mul {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    cfc (fun x => f x * g x) R = cfc f R * cfc g R :=
  cfc_mul f g R (hf.mono hR.spectrum_subset) (hg.mono hR.spectrum_subset)

lemma UnitOp.rcfc_smul (c : ℝ) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    cfc (fun x => c * f x) R = c • cfc f R :=
  cfc_const_mul c f R (hf.mono hR.spectrum_subset)

lemma UnitOp.rcfc_congr {f g : ℝ → ℝ} (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x) :
    cfc f R = cfc g R :=
  cfc_congr fun x hx => h x (hR.spectrum_subset hx)

lemma UnitOp.norm_rcfc_le {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ c) : ‖cfc f R‖ ≤ c :=
  norm_cfc_le hc fun x hx => by simpa only [Real.norm_eq_abs] using h x (hR.spectrum_subset hx)

lemma UnitOp.rcfc_inner_nonneg {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) (x : H) :
    0 ≤ inner ℝ (cfc f R x) x := by
  have h : 0 ≤ cfc f R := cfc_nonneg fun y hy => hf y (hR.spectrum_subset hy)
  have hp : (cfc f R).IsPositive := by simpa only [sub_zero] using ContinuousLinearMap.le_def.mp h
  exact hp.re_inner_nonneg_left x

lemma UnitOp.rcfc_sub {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    cfc (fun x => f x - g x) R = cfc f R - cfc g R :=
  cfc_sub f g R (hf.mono hR.spectrum_subset) (hg.mono hR.spectrum_subset)

lemma UnitOp.rcfc_pow {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) (n : ℕ) :
    cfc (fun x => f x ^ n) R = cfc f R ^ n :=
  cfc_pow f n R (hf.mono hR.spectrum_subset) hR.selfAdjoint

end CutoffRigidity.Riemann.Diff
