/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.CoefficientLocality
public import LeanPool.HighContrastHomogenization.Analytic.H1a0ToH10

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.PhysicalH1Realization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical Sobolev realization

The coefficient-weighted zero-trace pair is first realized as an exact
`H10Function`.  Adding a boundary datum gives a physical
`H1Function`; subtracting the comparison function's zero-trace witness gives
the final affine boundary relation.

On the bounded domain the coefficient agrees almost everywhere with a field
uniformly elliptic almost everywhere on all of `ℝ^d`, and `MemH1a0` reads the
field only there, so the realization is read at that companion field.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

/-- A coefficient-weighted zero-trace pair with boundary datum `g₀`
has an exact Sobolev representative in the affine boundary class of `h`. -/
theorem exists_h1Function_memAffineH10_of_memH1a0
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {a : Source.AKL.Field d} (ha : AEUniformlyEllipticField a)
    {aPhysical : CoeffField d}
    (hae : (⇑a : CoeffField d) =ᵐ[volume] aPhysical)
    (g₀ h : H1Function U)
    (hgh : MemAffineH10 U g₀ h)
    (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d)
    (hu0 : MemH1a0 aPhysical U
      (fun x ↦ uFun x - g₀.toFun x)
      (fun x ↦ uGrad x - g₀.grad x)) :
    ∃ u : H1Function U,
      u.toFun = uFun ∧ u.grad = uGrad ∧ MemAffineH10 U h u := by
  obtain ⟨lam, Lam, c, hlam, -, hellc, hac⟩ :=
    IsAELocallyUniformlyElliptic.exists_ae_isEllipticMatrix_ae_eq_restrict ha
      hU.isBoundedDomain.isBounded
  have haeU : (⇑a : CoeffField d) =ᵐ[volume.restrict U] aPhysical :=
    ae_restrict_of_ae hae
  have hPhysicalC : aPhysical =ᵐ[volume.restrict U] c := haeU.symm.trans hac
  obtain ⟨w, hwfun, hwgrad⟩ :=
    exists_h10Function_of_memH1a0 hU hlam hellc
      ((memH1a0_congr_coeff hPhysicalC _ _).1 hu0)
  let u : H1Function U := g₀ + w.toH1Function
  have hufun : u.toFun = uFun := by
    rw [show u.toFun = fun x ↦ g₀.toFun x + w.toH1Function.toFun x from rfl,
      hwfun]
    funext x
    ring
  have hugrad : u.grad = uGrad := by
    rw [show u.grad = fun x ↦ g₀.grad x + w.toH1Function.grad x from rfl,
      hwgrad]
    funext x i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  obtain ⟨z, hzfun, hzgrad⟩ := hgh
  have hsubfun : (w - z).toH1Function.toFun =
      fun x ↦ w.toH1Function.toFun x - z.toH1Function.toFun x := by
    funext x
    change w.toH1Function.toFun x + (-1) * z.toH1Function.toFun x = _
    ring
  have hsubgrad : (w - z).toH1Function.grad =
      fun x ↦ w.toH1Function.grad x - z.toH1Function.grad x := by
    funext x i
    change w.toH1Function.grad x i + (-1) * z.toH1Function.grad x i = _
    simp only [Pi.sub_apply]
    ring
  have hhu : MemAffineH10 U h u := by
    refine ⟨w - z, ?_, ?_⟩
    · rw [hsubfun]
      filter_upwards [hzfun] with x hx
      rw [show u.toFun x = g₀.toFun x + w.toH1Function.toFun x from rfl]
      rw [hx]
      ring
    · rw [hsubgrad]
      filter_upwards [hzgrad] with x hx
      rw [show u.grad x = g₀.grad x + w.toH1Function.grad x from rfl]
      rw [hx]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
  exact ⟨u, hufun, hugrad, hhu⟩

end

end HighContrast
end HCPolySupport
