/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinMollifiedIdentity
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceFlux
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices

/-!
# The regularized cross identity in integrated-by-parts form

Combining the mollified cross identity with the fixed-time flux computation
gives, for every mollification radius and cutoff, an identity whose right side
involves only mollified velocities, gradients, convection terms and pressures.
The mollification and the cutoff are removed afterwards in
`lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The cross density: the tested flux of `w` against the mollified field `z`,
in integrated-by-parts form, at a space-time point `(y, τ)`. -/
@[expose] def serrinCrossDensity (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (pw : ParabolicPoint → ℝ) (z : ParabolicPoint → Vec3)
    (Dz : ParabolicPoint → Fin 3 → Vec3) (n : ℕ) (η : Vec3 → ℝ) (q : ParabolicPoint) : ℝ :=
  -(η q.1 * ∑ k : Fin 3, serrinSM (fun r => z r k) n q *
      serrinSM (fun r => ∑ j : Fin 3, w r j * Dw r k j) n q)
    - η q.1 * ∑ k : Fin 3, ∑ j : Fin 3,
      serrinSM (fun r => Dz r k j) n q * serrinSM (fun r => Dw r k j) n q
    - ∑ k : Fin 3, ∑ j : Fin 3, spatialDeriv η j q.1 *
      serrinSM (fun r => z r k) n q * serrinSM (fun r => Dw r k j) n q
    + ∑ k : Fin 3, spatialDeriv η k q.1 * serrinSM (fun r => z r k) n q *
      serrinSM pw n q

private theorem serrin_flux_continuous (n : ℕ) {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    {pw : Vec3 → ℝ}
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume)
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => w x i) (fun x => Dw x i))
    (htr : ∀ᵐ x ∂volume, ∑ j : Fin 3, Dw x j j = 0)
    (hpw : LocallyIntegrable pw volume) (k : Fin 3) :
    Continuous (fun y : Vec3 => ∫ x : Vec3,
      (-(∑ j : Fin 3, w x k * w x j * spatialDeriv (serrinKernel n) j (y - x))
        + (∑ j : Fin 3, Dw x k j * spatialDeriv (serrinKernel n) j (y - x))
        - pw x * spatialDeriv (serrinKernel n) k (y - x))) := by
  have hfun := funext fun y => serrin_slice_flux_integral n hw2 hDw2 hgrad htr hpw k y
  rw [hfun]
  have hε := serrinRadius_pos n
  have hN : LocallyIntegrable (fun x => ∑ j : Fin 3, w x j * Dw x k j) volume :=
    (integrable_finsetSum _ fun j _ =>
      (hw2.eval j).integrable_mul ((hDw2.eval k).eval j)).locallyIntegrable
  have hd {f : Vec3 → ℝ} (hf : LocallyIntegrable f volume) (j : Fin 3) :
      Continuous (spatialDeriv (CKN.mollify f (serrinRadius n) hε) j) :=
    ((CKN.mollify_contDiff hε hf (n := (⊤ : ℕ∞))).continuous_fderiv (by simp)).clm_apply
      continuous_const
  refine ((CKN.mollify_continuous hε hN).neg.add
    (continuous_finsetSum _ fun j _ => hd (((hDw2.eval k).eval j).locallyIntegrable
      (by norm_num)) j)).sub (hd hpw k)

/-- The regularized cross identity: for every mollification radius and cutoff,
the change of the cutoff-weighted mollified pairing equals the time integral
of the two cross densities. -/
theorem serrin_cross_regularized
    {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T b v Dv pv)
    (n : ℕ) {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ y, η y * ((∑ k : Fin 3, serrinMol v (serrinKernel n) k y t *
          serrinMol u (serrinKernel n) k y t) -
        ∑ k : Fin 3, serrinMol v (serrinKernel n) k y 0 * serrinMol u (serrinKernel n) k y 0)) =
      ∫ τ in (0 : ℝ)..t, ((∫ y, serrinCrossDensity v Dv pv u Du n η (y, τ)) +
        ∫ y, serrinCrossDensity u Du pu v Dv n η (y, τ)) := by
  have hρ : ContDiff ℝ (⊤ : ℕ∞) (serrinKernel n) :=
    CKN.mollifier_contDiff (d := 3) (serrinRadius_pos n)
  have hρc : HasCompactSupport (serrinKernel n) :=
    CKN.mollifier_hasCompactSupport (d := 3) (serrinRadius_pos n)
  rw [serrinMol_cross_identity hU hV hρ hρc hη.continuous hηc ht]
  apply intervalIntegral.integral_congr_ae
  have hgood := (ae_restrict_iff' measurableSet_Ioo).mp
    ((serrinWeak_slices_ae hU).and (serrinWeak_slices_ae hV))
  filter_upwards [hgood, Measure.ae_ne volume T] with τ hτ hτT hτI
  rw [uIoc_of_le ht.1] at hτI
  obtain ⟨⟨hu2, hDu2, hug, hutr, hpu⟩, ⟨hv2, hDv2, hvg, hvtr, hpv⟩⟩ :=
    hτ ⟨hτI.1, lt_of_le_of_ne (hτI.2.trans ht.2) hτT⟩
  -- continuity of the fluxes and mollified components in the mollification point
  have hfv (k : Fin 3) : Continuous (fun y => serrinMolFlux v Dv pv (serrinKernel n) k y τ) :=
    serrin_flux_continuous n hv2 hDv2 hvg hvtr hpv k
  have hfu (k : Fin 3) : Continuous (fun y => serrinMolFlux u Du pu (serrinKernel n) k y τ) :=
    serrin_flux_continuous n hu2 hDu2 hug hutr hpu k
  have hmu (k : Fin 3) : Continuous (fun y => serrinMol u (serrinKernel n) k y τ) := by
    have h := CKN.mollify_continuous (serrinRadius_pos n)
      ((hu2.eval k).locallyIntegrable (by norm_num))
    refine h.congr fun y => ?_
    exact serrin_mollify_eq_integral _ _ y
  have hmv (k : Fin 3) : Continuous (fun y => serrinMol v (serrinKernel n) k y τ) := by
    have h := CKN.mollify_continuous (serrinRadius_pos n)
      ((hv2.eval k).locallyIntegrable (by norm_num))
    refine h.congr fun y => ?_
    exact serrin_mollify_eq_integral _ _ y
  have hint1 : Integrable (fun y => η y * ∑ k : Fin 3,
      serrinMolFlux v Dv pv (serrinKernel n) k y τ * serrinMol u (serrinKernel n) k y τ)
      volume :=
    (hη.continuous.mul (continuous_finsetSum _ fun k _ => (hfv k).mul (hmu k))
      ).integrable_of_hasCompactSupport hηc.mul_right
  have hint2 : Integrable (fun y => η y * ∑ k : Fin 3,
      serrinMolFlux u Du pu (serrinKernel n) k y τ * serrinMol v (serrinKernel n) k y τ)
      volume :=
    (hη.continuous.mul (continuous_finsetSum _ fun k _ => (hfu k).mul (hmv k))
      ).integrable_of_hasCompactSupport hηc.mul_right
  have hsplit : (fun y => η y * ∑ k : Fin 3,
      (serrinMolFlux v Dv pv (serrinKernel n) k y τ * serrinMol u (serrinKernel n) k y τ +
        serrinMol v (serrinKernel n) k y τ * serrinMolFlux u Du pu (serrinKernel n) k y τ)) =
      fun y => (η y * ∑ k : Fin 3,
        serrinMolFlux v Dv pv (serrinKernel n) k y τ * serrinMol u (serrinKernel n) k y τ) +
        η y * ∑ k : Fin 3,
        serrinMolFlux u Du pu (serrinKernel n) k y τ * serrinMol v (serrinKernel n) k y τ := by
    funext y
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, integral_add hint1 hint2]
  congr 1
  · exact serrin_slice_flux_pairing n hv2 hDv2 hvg hvtr hpv hu2 hDu2 hug hutr hη hηc
  · exact serrin_slice_flux_pairing n hu2 hDu2 hug hutr hpu hv2 hDv2 hvg hvtr hη hηc

end ESS
