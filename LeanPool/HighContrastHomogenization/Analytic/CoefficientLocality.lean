/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers

/-!
# High-contrast homogenization: Analytic.CoefficientLocality

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coefficient-weighted classes on a set read the field only on that set

The weighted energy `sEnergyOn`, the norm `h1sNormSqOn` of `s.introduction`,
the skew-flux dual norm `skewFluxDualNorm`
and the membership class `MemH1a0` are built from integrals over the set `V`
alone.  Two coefficient fields agreeing almost everywhere on `V` therefore give
the same weighted norm, the same skew-flux dual norm and the same membership
class: none of them reads the field outside `V`.

This is what makes a locally uniformly elliptic field usable in the estimates
stated for fields uniformly elliptic almost everywhere on all of `ℝ^d`.  On a
bounded domain the field agrees almost everywhere with such a field, and every
class in the display is unchanged by the replacement.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The weighted Dirichlet energy on `V` reads the field only on `V`. -/
theorem sEnergyOn_congr_coeff {b b' : CoeffField d} {V : Set (Vec d)}
    (h : b =ᵐ[volume.restrict V] b') (F : Vec d → Vec d) :
    sEnergyOn b V F = sEnergyOn b' V F := by
  simp only [sEnergyOn]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The `H¹_s(V)` norm square reads the field only on `V`. -/
theorem h1sNormSqOn_congr_coeff {b b' : CoeffField d} {V : Set (Vec d)}
    (h : b =ᵐ[volume.restrict V] b') (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    h1sNormSqOn b V u Du = h1sNormSqOn b' V u Du := by
  simp only [h1sNormSqOn, sEnergyOn_congr_coeff h]

/-- The skew-flux pairing on `V` reads the field only on `V`: the two integrands
agree almost everywhere there, so they are simultaneously absolutely convergent
and have the same integral. -/
theorem skewFluxPairing_congr_coeff {b b' : CoeffField d} {V : Set (Vec d)}
    (h : b =ᵐ[volume.restrict V] b') (F : Vec d → Vec d) (φ : Vec d → ℝ) :
    skewFluxPairing b V F φ = skewFluxPairing b' V F φ := by
  classical
  have hfun : (fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b x)) (F x)))
      =ᵐ[volume.restrict V]
        fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b' x)) (F x)) := by
    filter_upwards [h] with x hx
    rw [hx]
  simp only [skewFluxPairing]
  by_cases hint : IntegrableOn
      (fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b x)) (F x))) V volume
  · have hint' : IntegrableOn
        (fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b' x)) (F x))) V
        volume := hint.congr hfun
    rw [ite_eq_left hint, ite_eq_left hint']
    exact congrArg ENNReal.ofReal (integral_congr_ae hfun)
  · have hint' : ¬ IntegrableOn
        (fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b' x)) (F x))) V
        volume := fun hc => hint (hc.congr hfun.symm)
    rw [ite_eq_right hint, ite_eq_right hint']

/-- The skew-flux dual norm on `V` reads the field only on `V`: the test class
and the pairing it takes the supremum of are both unchanged. -/
theorem skewFluxDualNorm_congr_coeff {b b' : CoeffField d} {V : Set (Vec d)}
    (h : b =ᵐ[volume.restrict V] b') (F : Vec d → Vec d) :
    skewFluxDualNorm b V F = skewFluxDualNorm b' V F := by
  simp only [skewFluxDualNorm]
  refine le_antisymm (iSup_le fun φ => ?_) (iSup_le fun φ => ?_)
  · refine le_trans (le_of_eq (skewFluxPairing_congr_coeff h F φ.1)) ?_
    exact le_iSup (fun ψ : {ψ : Vec d → ℝ //
      IsLocalTest V ψ ∧ h1sNormSqOn b' V ψ (smoothGrad ψ) ≤ 1} =>
        skewFluxPairing b' V F ψ.1)
      ⟨φ.1, φ.2.1, by rw [← h1sNormSqOn_congr_coeff h]; exact φ.2.2⟩
  · refine le_trans (le_of_eq (skewFluxPairing_congr_coeff h.symm F φ.1)) ?_
    exact le_iSup (fun ψ : {ψ : Vec d → ℝ //
      IsLocalTest V ψ ∧ h1sNormSqOn b V ψ (smoothGrad ψ) ≤ 1} =>
        skewFluxPairing b V F ψ.1)
      ⟨φ.1, φ.2.1, by rw [h1sNormSqOn_congr_coeff h]; exact φ.2.2⟩

/-- **Membership in `H¹_a(V)` reads the field only on `V`.**  Both clauses that
see the coefficient field — the `H¹_s` approximation and the skew-flux dual
approximation — are unchanged when the field is replaced by one agreeing with it
almost everywhere on `V`. -/
theorem memH1a_congr_coeff {b b' : CoeffField d} {V : Set (Vec d)}
    (h : b =ᵐ[volume.restrict V] b') (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    MemH1a b V u Du ↔ MemH1a b' V u Du := by
  have h1 : ∀ v Dv, h1sNormSqOn b V v Dv = h1sNormSqOn b' V v Dv :=
    fun v Dv => h1sNormSqOn_congr_coeff h v Dv
  have h2 : ∀ G, skewFluxDualNorm b V G = skewFluxDualNorm b' V G :=
    fun G => skewFluxDualNorm_congr_coeff h G
  simp only [MemH1a, h1, h2]

/-- **Membership in `H¹_{a,0}(V)` reads the field only on `V`.**  Both clauses
that see the coefficient field — the `H¹_s` approximation and the skew-flux dual
approximation — are unchanged when the field is replaced by one agreeing with it
almost everywhere on `V`. -/
theorem memH1a0_congr_coeff {b b' : CoeffField d} {V : Set (Vec d)}
    (h : b =ᵐ[volume.restrict V] b') (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    MemH1a0 b V u Du ↔ MemH1a0 b' V u Du := by
  have h1 : ∀ v Dv, h1sNormSqOn b V v Dv = h1sNormSqOn b' V v Dv :=
    fun v Dv => h1sNormSqOn_congr_coeff h v Dv
  have h2 : ∀ G, skewFluxDualNorm b V G = skewFluxDualNorm b' V G :=
    fun G => skewFluxDualNorm_congr_coeff h G
  simp only [MemH1a0, h1, h2]

end

end HighContrast
end HCPolySupport
