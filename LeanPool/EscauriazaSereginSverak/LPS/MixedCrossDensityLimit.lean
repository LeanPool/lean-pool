/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormPairingSlab
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossLimitTerms
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossRegularized
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossIdentity

/-!
# Mixed norm limits of the cross densities

As the mollification radius tends to zero and the cutoff radius to infinity,
the space-time integral of a cross density converges to minus the convection
pairing and the gradient pairing. This is the limit passage on the right side
of the cross-testing identity in `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Real exponents with `1/p + 1/q = 1` are Hölder conjugate. -/
theorem lps_real_holder_pair {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (h : p⁻¹ + q⁻¹ = 1) :
    p.HolderConjugate q :=
  ⟨by simpa using h, hp, hq⟩

/-- A coordinate of an almost everywhere strongly measurable vector field on a
slab is almost everywhere strongly measurable. -/
theorem lps_coordinate_aesm
    {T : ℝ} {F : ParabolicPoint → Vec3}
    (hF : AEStronglyMeasurable F
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T)))) (i : Fin 3) :
    AEStronglyMeasurable (fun z : ParabolicPoint => F z i)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
  (continuous_apply i).comp_aestronglyMeasurable hF

/-- An entry of an almost everywhere strongly measurable gradient field on a slab
is almost everywhere strongly measurable. -/
theorem lps_gradient_entry_aesm
    {T : ℝ} {F : ParabolicPoint → Fin 3 → Vec3}
    (hF : AEStronglyMeasurable F
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (i j : Fin 3) :
    AEStronglyMeasurable (fun z : ParabolicPoint => F z i j)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) :=
  (continuous_apply j).comp_aestronglyMeasurable
    ((continuous_apply i).comp_aestronglyMeasurable hF)

/-- The advective convection of measurable fields is almost everywhere strongly
measurable on a slab. -/
theorem lps_convection_aesm
    {T : ℝ} {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    (hw : AEStronglyMeasurable w
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))))
    (hDw : AEStronglyMeasurable Dw
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T)))) (k : Fin 3) :
    AEStronglyMeasurable
      (fun z : ParabolicPoint => ∑ j : Fin 3, w z j * Dw z k j)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) := by
  refine Finset.univ.aestronglyMeasurable_fun_sum ?_
  intro j _
  exact (lps_coordinate_aesm hw j).mul (lps_gradient_entry_aesm hDw k j)

/-- Integrability and the limit of the space-time integral of a cross density,
given the pairing limit of the convection term. The remaining terms are
controlled by the `L²` gradients, the `L^(5/2)` tested velocity and the
`L^(5/3)` pressure. -/
theorem lps_cross_density_limit_of_pairing {t T : ℝ} (ht : t ≤ T)
    {w z : ParabolicPoint → Vec3} {Dw Dz : ParabolicPoint → Fin 3 → Vec3}
    {pw : ParabolicPoint → ℝ}
    (hPairInt : ∀ k, ∀ᶠ n in atTop, Integrable
      (fun q : ParabolicPoint => serrinCutoff n q.1 * serrinSM (fun r => z r k) n q *
        serrinSM (fun r => ∑ j : Fin 3, w r j * Dw r k j) n q)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))))
    (hPairLim : ∀ k, Tendsto (fun n => ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      serrinCutoff n q.1 * serrinSM (fun r => z r k) n q *
        serrinSM (fun r => ∑ j : Fin 3, w r j * Dw r k j) n q) atTop
      (𝓝 (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        z q k * ∑ j : Fin 3, w q j * Dw q k j)))
    (hPairProd : ∀ k, Integrable
      (fun q : ParabolicPoint => z q k * ∑ j : Fin 3, w q j * Dw q k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))))
    (hDz : ∀ k j, MemLp (fun r => Dz r k j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDw : ∀ k j, MemLp (fun r => Dw r k j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hz2 : ∀ k, MemLp (fun r => z r k) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hz52 : ∀ k, MemLp (fun r => z r k) (ENNReal.ofReal (5 / 2))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hpw : MemLp pw (ENNReal.ofReal (5 / 3))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    (∀ᶠ n in atTop, Integrable (serrinCrossDensity w Dw pw z Dz n (serrinCutoff n))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) ∧
    Tendsto (fun n => ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) q) atTop
      (𝓝 (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, z q k * ∑ j : Fin 3, w q j * Dw q k j)
        - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Dz q k j * Dw q k j)) := by
  set μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))
  obtain ⟨C, hC0, hCb⟩ := serrinCutoff_deriv_bound
  have hη (n : ℕ) : Continuous (serrinCutoff n) := (serrinCutoff_contDiff n).continuous
  have hηb (n : ℕ) : ∃ B, ∀ y, |serrinCutoff n y| ≤ B := ⟨1, serrinCutoff_abs_le_one n⟩
  have hdη (n : ℕ) (j : Fin 3) : Continuous (spatialDeriv (serrinCutoff n) j) :=
    ((serrinCutoff_contDiff n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdηb (j : Fin 3) (n : ℕ) : ∃ B, ∀ y, |spatialDeriv (serrinCutoff n) j y| ≤ B :=
    ⟨C * (1 / ((n : ℝ) + 1)), fun y => hCb n j y⟩
  have hPressureHolder : ENNReal.HolderTriple (ENNReal.ofReal (5 / 2))
      (ENNReal.ofReal (5 / 3)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  -- the four families of terms
  let A1 : ℕ → Fin 3 → ParabolicPoint → ℝ := fun n k q =>
    serrinCutoff n q.1 * serrinSM (fun r => z r k) n q *
      serrinSM (fun r => ∑ j : Fin 3, w r j * Dw r k j) n q
  let A2 : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun n k j q =>
    serrinCutoff n q.1 * serrinSM (fun r => Dz r k j) n q * serrinSM (fun r => Dw r k j) n q
  let A3 : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun n k j q =>
    spatialDeriv (serrinCutoff n) j q.1 * serrinSM (fun r => z r k) n q *
      serrinSM (fun r => Dw r k j) n q
  let A4 : ℕ → Fin 3 → ParabolicPoint → ℝ := fun n k q =>
    spatialDeriv (serrinCutoff n) k q.1 * serrinSM (fun r => z r k) n q * serrinSM pw n q
  have hdens (n : ℕ) (q : ParabolicPoint) :
      serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) q =
        -(∑ k : Fin 3, A1 n k q) - (∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q)
          - (∑ k : Fin 3, ∑ j : Fin 3, A3 n k j q) + ∑ k : Fin 3, A4 n k q := by
    simp only [serrinCrossDensity, A1, A2, A3, A4, Finset.mul_sum, mul_assoc]
  -- eventual integrability of each term
  have hI1 : ∀ᶠ n in atTop, ∀ k, Integrable (A1 n k) μ := by
    rw [eventually_all]
    exact hPairInt
  have hI2 : ∀ᶠ n in atTop, ∀ k j, Integrable (A2 n k j) μ := by
    rw [eventually_all]
    intro k
    rw [eventually_all]
    exact fun j => serrin_weighted_term_integrable (p := 2) (q := 2) ht (by norm_num) (by simp)
      (by norm_num) (by simp) (hDz k j) (hDw k j) hη hηb
  have hI3 : ∀ᶠ n in atTop, ∀ k j, Integrable (A3 n k j) μ := by
    rw [eventually_all]
    intro k
    rw [eventually_all]
    exact fun j => serrin_weighted_term_integrable (p := 2) (q := 2) ht (by norm_num) (by simp)
      (by norm_num) (by simp) (hz2 k) (hDw k j) (fun n => hdη n j) (hdηb j)
  have hI4 : ∀ᶠ n in atTop, ∀ k, Integrable (A4 n k) μ := by
    rw [eventually_all]
    exact fun k => serrin_weighted_term_integrable ht (by norm_num) (by simp)
      (by norm_num) (by simp) (hz52 k) hpw
      (fun n => hdη n k) (hdηb k)
  have hdensf (n : ℕ) : serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) =
      fun q => -(∑ k : Fin 3, A1 n k q) - (∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q)
          - (∑ k : Fin 3, ∑ j : Fin 3, A3 n k j q) + ∑ k : Fin 3, A4 n k q :=
    funext (hdens n)
  have hIall : ∀ᶠ n in atTop, Integrable (serrinCrossDensity w Dw pw z Dz n (serrinCutoff n)) μ
      ∧ (∫ q, serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) q ∂μ) =
        -(∑ k : Fin 3, ∫ q, A1 n k q ∂μ) - (∑ k : Fin 3, ∑ j : Fin 3, ∫ q, A2 n k j q ∂μ)
          - (∑ k : Fin 3, ∑ j : Fin 3, ∫ q, A3 n k j q ∂μ) + ∑ k : Fin 3, ∫ q, A4 n k q ∂μ := by
    filter_upwards [hI1, hI2, hI3, hI4] with n h1 h2 h3 h4
    have i1 : Integrable (fun q => ∑ k : Fin 3, A1 n k q) μ :=
      integrable_finsetSum _ fun k _ => h1 k
    have i2 : Integrable (fun q => ∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q) μ :=
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h2 k j
    have i3 : Integrable (fun q => ∑ k : Fin 3, ∑ j : Fin 3, A3 n k j q) μ :=
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h3 k j
    have i4 : Integrable (fun q => ∑ k : Fin 3, A4 n k q) μ :=
      integrable_finsetSum _ fun k _ => h4 k
    have i1n : Integrable (fun q => -(∑ k : Fin 3, A1 n k q)) μ := i1.neg
    have i12 : Integrable (fun q => -(∑ k : Fin 3, A1 n k q) -
        ∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q) μ := i1n.sub i2
    have i123 : Integrable (fun q => -(∑ k : Fin 3, A1 n k q) -
        (∑ k : Fin 3, ∑ j : Fin 3, A2 n k j q) - ∑ k : Fin 3, ∑ j : Fin 3, A3 n k j q) μ :=
      i12.sub i3
    rw [hdensf n]
    refine ⟨i123.add i4, ?_⟩
    rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1n i2, integral_neg,
      integral_finsetSum _ fun k _ => h1 k, integral_finsetSum _ fun k _ => h4 k,
      integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h2 k j,
      integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h3 k j]
    simp only [integral_finsetSum _ fun j _ => h2 _ j, integral_finsetSum _ fun j _ => h3 _ j]
  refine ⟨hIall.mono fun n h => h.1, ?_⟩
  have hL1 (k : Fin 3) := hPairLim k
  have hL2 (k j : Fin 3) := serrin_cutoff_pairing_limit (p := 2) (q := 2) ht (by norm_num)
    (by simp) (by norm_num) (by simp) (hDz k j) (hDw k j)
  have hL3 (k j : Fin 3) := serrin_cutoff_deriv_pairing_limit (p := 2) (q := 2) ht
    (by norm_num) (by simp) (by norm_num) (by simp) (hz2 k) (hDw k j) j
  have hL4 (k : Fin 3) := serrin_cutoff_deriv_pairing_limit ht
    (p := ENNReal.ofReal (5 / 2)) (q := ENNReal.ofReal (5 / 3))
    (by norm_num) (by simp) (by norm_num) (by simp) (hz52 k) hpw k
  have hlim := (((tendsto_finsetSum Finset.univ fun k _ => hL1 k).neg.sub
    (tendsto_finsetSum Finset.univ fun k _ =>
      tendsto_finsetSum Finset.univ fun j _ => hL2 k j)).sub
    (tendsto_finsetSum Finset.univ fun k _ =>
      tendsto_finsetSum Finset.univ fun j _ => hL3 k j)).add
    (tendsto_finsetSum Finset.univ fun k _ => hL4 k)
  simp only [Finset.sum_const_zero, sub_zero, add_zero] at hlim
  have hint1 (k : Fin 3) : Integrable (fun q => z q k * ∑ j : Fin 3, w q j * Dw q k j) μ :=
    hPairProd k
  have hint2 (k j : Fin 3) : Integrable (fun q => Dz q k j * Dw q k j) μ :=
    memLp_one_iff_integrable.mp (((hDz k j).mono_measure (serrin_slab_restrict_le ht)).mul
      (r := 1) ((hDw k j).mono_measure (serrin_slab_restrict_le ht)))
  rw [integral_finsetSum _ fun k _ => hint1 k,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint2 k j]
  simp only [integral_finsetSum _ fun j _ => hint2 _ j]
  refine hlim.congr' ?_
  filter_upwards [hIall] with n hn
  exact hn.2.symm

/-- Integrability and the limit of the space-time integral of a cross density
when the tested velocity and the rival convection have conjugate finite mixed
norms. The pressure term retains the finite-energy exponents `5/2` and
`5/3`. -/
theorem lps_mixed_cross_density_limit {t T px qx pt qt : ℝ} (ht : t ≤ T)
    {w z : ParabolicPoint → Vec3} {Dw Dz : ParabolicPoint → Fin 3 → Vec3}
    {pw : ParabolicPoint → ℝ}
    (hpx1 : 1 ≤ px) (hqx1 : 1 ≤ qx) (hpt1 : 1 ≤ pt) (hqt1 : 1 ≤ qt)
    (hSpace : px.HolderConjugate qx) (hTime : pt.HolderConjugate qt)
    (hzMeas : ∀ k, AEStronglyMeasurable (fun r => z r k)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hNMeas : ∀ k, AEStronglyMeasurable
      (fun r => ∑ j : Fin 3, w r j * Dw r k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hzSlice : ∀ k, ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => z (x,τ) k) (ENNReal.ofReal px) volume)
    (hNSlice : ∀ k, ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => ∑ j : Fin 3, w (x,τ) j * Dw (x,τ) k j)
        (ENNReal.ofReal qx) volume)
    (hzMoment : ∀ k, (∫⁻ τ in Ioo 0 T,
      eLpNorm (fun x : Vec3 => z (x,τ) k) (ENNReal.ofReal px) volume ^ pt) < ⊤)
    (hNMoment : ∀ k, (∫⁻ τ in Ioo 0 T,
      eLpNorm (fun x : Vec3 => ∑ j : Fin 3, w (x,τ) j * Dw (x,τ) k j)
        (ENNReal.ofReal qx) volume ^ qt) < ⊤)
    (hDz : ∀ k j, MemLp (fun r => Dz r k j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDw : ∀ k j, MemLp (fun r => Dw r k j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hz2 : ∀ k, MemLp (fun r => z r k) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hz52 : ∀ k, MemLp (fun r => z r k) (ENNReal.ofReal (5 / 2))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hpw : MemLp pw (ENNReal.ofReal (5 / 3))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    (∀ᶠ n in atTop, Integrable (serrinCrossDensity w Dw pw z Dz n (serrinCutoff n))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) ∧
    Tendsto (fun n => ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        serrinCrossDensity w Dw pw z Dz n (serrinCutoff n) q) atTop
      (𝓝 (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, z q k * ∑ j : Fin 3, w q j * Dw q k j)
        - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Dz q k j * Dw q k j)) := by
  refine lps_cross_density_limit_of_pairing ht
    (fun k => (lps_mixed_cutoff_pairing_limit_slab ht hpx1 hqx1 hpt1 hqt1
      hSpace hTime (hzMeas k) (hNMeas k) (hzSlice k) (hNSlice k)
      (hzMoment k) (hNMoment k)).1)
    (fun k => (lps_mixed_cutoff_pairing_limit_slab ht hpx1 hqx1 hpt1 hqt1 hSpace hTime
      (hzMeas k) (hNMeas k) (hzSlice k) (hNSlice k) (hzMoment k) (hNMoment k)).2)
    (fun k => ((lps_mixed_product_integrable (by positivity) (by positivity) (by positivity)
      (by positivity) hSpace hTime (hzMeas k) (hNMeas k) (hzSlice k) (hNSlice k)
      (hzMoment k) (hNMoment k)).1).mono_measure (serrin_slab_restrict_le ht))
    hDz hDw hz2 hz52 hpw


end ESS
