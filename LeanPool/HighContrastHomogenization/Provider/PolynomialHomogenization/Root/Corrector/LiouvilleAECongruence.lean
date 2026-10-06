/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.LiouvilleGaugeInvariance
public import LeanPool.HighContrastHomogenization.Analytic.NormEquivalence

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.LiouvilleAECongruence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Almost-everywhere congruence for the Liouville class

The class is insensitive to changes of coefficient, value, and gradient
representatives on null sets.  The coefficient statement uses the unweighted
characterization of the local symmetric Sobolev closure.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

private theorem hasWeakGradientOn_congr_ae
    {U : Set (Vec d)} {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (huv : u =ᵐ[volume.restrict U] v)
    (hDuDv : Du =ᵐ[volume.restrict U] Dv)
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn U v Dv := by
  intro i φ hφsmooth hφcompact hφsub
  have hvalue :
      (fun x ↦ u x * (fderiv ℝ φ x) (basisVec i)) =ᵐ[volume.restrict U]
        fun x ↦ v x * (fderiv ℝ φ x) (basisVec i) := by
    filter_upwards [huv] with x hx
    rw [hx]
  have hgrad : (fun x ↦ Du x i * φ x) =ᵐ[volume.restrict U]
      fun x ↦ Dv x i * φ x := by
    filter_upwards [hDuDv] with x hx
    rw [hx]
  calc
    ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume :=
      integral_congr_ae hvalue.symm
    _ = -∫ x in U, Du x i * φ x ∂volume := h i φ hφsmooth hφcompact hφsub
    _ = -∫ x in U, Dv x i * φ x ∂volume := by
      rw [integral_congr_ae hgrad]

private theorem h1sNormSqOn_congr_ae
    (b : CoeffField d) (U : Set (Vec d))
    {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (huv : u =ᵐ[volume.restrict U] v)
    (hDuDv : Du =ᵐ[volume.restrict U] Dv) :
    h1sNormSqOn b U u Du = h1sNormSqOn b U v Dv := by
  have hvalue :
      (∫⁻ x in U, ENNReal.ofReal |u x| ∂volume) =
        ∫⁻ x in U, ENNReal.ofReal |v x| ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [huv] with x hx
    rw [hx]
  have henergy : sEnergyOn b U Du = sEnergyOn b U Dv := by
    unfold sEnergyOn
    apply lintegral_congr_ae
    filter_upwards [hDuDv] with x hx
    rw [hx]
  unfold h1sNormSqOn
  rw [hvalue, henergy]

private theorem normalizedL2Norm_congr_ae
    (U : Set (Vec d)) {u v : Vec d → ℝ}
    (huv : u =ᵐ[volume.restrict U] v) :
    normalizedL2Norm U u = normalizedL2Norm U v := by
  have hsq :
      (∫⁻ x in U, ENNReal.ofReal (u x ^ 2) ∂volume) =
        ∫⁻ x in U, ENNReal.ofReal (v x ^ 2) ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [huv] with x hx
    rw [hx]
  unfold normalizedL2Norm eVolumeAverage
  rw [hsq]

/-- Replacing the value and gradient representatives almost everywhere does
not change membership in the Liouville class. -/
theorem memLiouvilleClass_congr_representatives
    {b : CoeffField d} {theta : ℝ}
    {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (huv : u =ᵐ[volume] v) (hDuDv : Du =ᵐ[volume] Dv) :
    MemLiouvilleClass b theta u Du ↔ MemLiouvilleClass b theta v Dv := by
  have transfer : ∀ {f g : Vec d → ℝ} {Df Dg : Vec d → Vec d},
      f =ᵐ[volume] g → Df =ᵐ[volume] Dg →
      MemLiouvilleClass b theta f Df → MemLiouvilleClass b theta g Dg := by
    intro f g Df Dg hfg hDfDg hclass
    have hlocal : MemH1sLoc b g Dg := by
      refine ⟨⟨hclass.1.1.1.congr hfg, fun i ↦
        (hclass.1.1.2 i).congr (hDfDg.fun_comp fun z ↦ z i)⟩, ?_⟩
      intro R hR
      obtain ⟨hweak, w, hw, htend⟩ := hclass.1.2 R hR
      have hfgR := ae_restrict_of_ae (s := euclideanBall d R) hfg
      have hDfDgR := ae_restrict_of_ae (s := euclideanBall d R) hDfDg
      refine ⟨hasWeakGradientOn_congr_ae hfgR hDfDgR hweak, w, hw, ?_⟩
      apply htend.congr'
      filter_upwards [] with n
      apply h1sNormSqOn_congr_ae
      · filter_upwards [hfgR] with x hx
        rw [hx]
      · filter_upwards [hDfDgR] with x hx
        rw [hx]
    have hweak : IsWeakSolutionOn b Set.univ Dg :=
      hclass.2.1.congr_ae Filter.EventuallyEq.rfl (by
        simpa only [Measure.restrict_univ] using hDfDg)
    have hgrowth : Tendsto
        (fun r : ℝ ↦ ENNReal.ofReal (r ^ (-(1 + theta))) *
          normalizedL2Norm (euclideanBall d r) g) atTop (nhds 0) := by
      apply hclass.2.2.congr'
      filter_upwards [] with R
      rw [normalizedL2Norm_congr_ae _
        (ae_restrict_of_ae (s := euclideanBall d R) hfg)]
    exact ⟨hlocal, hweak, hgrowth⟩
  exact ⟨transfer huv hDuDv, transfer huv.symm hDuDv.symm⟩

/-- Almost-everywhere equal locally uniformly elliptic coefficient
representatives define the same Liouville class. -/
theorem memLiouvilleClass_congr_coefficient
    {a b : CoeffField d} {theta : ℝ} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d}
    (hab : a =ᵐ[volume] b)
    (ha : IsAELocallyUniformlyElliptic a)
    (hb : IsAELocallyUniformlyElliptic b) :
    MemLiouvilleClass a theta v Dv ↔ MemLiouvilleClass b theta v Dv := by
  have transfer : ∀ {c e : CoeffField d},
      c =ᵐ[volume] e → IsAELocallyUniformlyElliptic c →
      IsAELocallyUniformlyElliptic e →
      MemLiouvilleClass c theta v Dv → MemLiouvilleClass e theta v Dv := by
    intro c e hce hc he hclass
    have hlocal : MemH1sLoc e v Dv := by
      refine ⟨hclass.1.1, ?_⟩
      intro R hR
      obtain ⟨hweak, w, hw, htend⟩ := hclass.1.2 R hR
      obtain ⟨lc, Lc, hlc, -, hellc⟩ :=
        hc.exists_ae_isEllipticMatrix_euclideanBall hR
      obtain ⟨le2, Le2, hle2, -, helle⟩ :=
        he.exists_ae_isEllipticMatrix_euclideanBall hR
      refine ⟨hweak, w, hw, ?_⟩
      exact (tendsto_h1sNormSqOn_sub_zero_iff_restrict (Lam := Le2)
          hle2 helle v Dv w).mpr
        ((tendsto_h1sNormSqOn_sub_zero_iff_restrict (Lam := Lc)
          hlc hellc v Dv w).mp htend)
    have hweak := hclass.2.1.congr_ae
      (by simpa only [Measure.restrict_univ] using hce)
      Filter.EventuallyEq.rfl
    exact ⟨hlocal, hweak, hclass.2.2⟩
  exact ⟨transfer hab ha hb, transfer hab.symm hb ha⟩

end

end Root
end HighContrast
end HCPolySupport
