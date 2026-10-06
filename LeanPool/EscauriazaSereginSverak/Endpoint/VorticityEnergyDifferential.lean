/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityEnergyComponent

/-!
# Smooth spatial energy inequality for vorticity

The component balance is combined with finite-dimensional estimates to
obtain the spatial differential inequality used in `lem:localized-vorticity-energy`.
-/

public section


open MeasureTheory Set
open scoped BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

private theorem vorticityEnergy_pointwise_pairing_bound
    (M : ℝ) (hM : 0 ≤ M) (v z g : Vec3)
    (F G : Fin 3 → Fin 3 → ℝ)
    (hvbound : vec3EuclideanNorm v ≤ M) :
    (∑ i : Fin 3, ∑ j : Fin 3, (v j * z i - z j * v i) * G j i) -
      ∑ i : Fin 3, ∑ j : Fin 3, F j i * G j i +
      ∑ i : Fin 3, g i * z i ≤
    (1 / 2 : ℝ) * (∑ j : Fin 3, ∑ i : Fin 3, (G j i) ^ 2) +
      36 * M ^ 2 * (∑ i : Fin 3, (z i) ^ 2) +
      ∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2 +
      (1 / 2 : ℝ) * (∑ i : Fin 3, (z i) ^ 2) +
      (1 / 2 : ℝ) * (∑ i : Fin 3, (g i) ^ 2) := by
  rw [Finset.sum_comm (f := fun i j => (v j * z i - z j * v i) * G j i),
    Finset.sum_comm (f := fun i j => F j i * G j i)]
  have hpair := vorticityFluxAndMatrixPairing_halfDissipation M v z F (fun i j => G j i) hM hvbound
  have hgpair := vorticityVectorPairing_young g z
  have hsumabs :
      (∑ j : Fin 3, ∑ i : Fin 3, (v j * z i - z j * v i) * G j i) -
        (∑ j : Fin 3, ∑ i : Fin 3, F j i * G j i) ≤
      |∑ j : Fin 3, ∑ i : Fin 3, (v j * z i - z j * v i) * G j i| +
        |∑ j : Fin 3, ∑ i : Fin 3, F j i * G j i| := by
    calc
      _ ≤ |(∑ j : Fin 3, ∑ i : Fin 3, (v j * z i - z j * v i) * G j i) -
          (∑ j : Fin 3, ∑ i : Fin 3, F j i * G j i)| := le_abs_self _
      _ ≤ _ := abs_sub _ _
  have hWbound :
      (∑ i : Fin 3, g i * z i) ≤
        (1 / 2 : ℝ) * (∑ i : Fin 3, (g i) ^ 2) +
          (1 / 2 : ℝ) * (∑ i : Fin 3, (z i) ^ 2) := by
    calc
      _ ≤ |∑ i : Fin 3, g i * z i| := le_abs_self _
      _ ≤ _ := hgpair
  have hnormsq : (vec3EuclideanNorm z) ^ 2 = ∑ i : Fin 3, (z i) ^ 2 := by
    rw [vec3EuclideanNorm, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hnormsq] at hpair
  linarith only [hpair, hWbound, hsumabs]

private theorem vorticityEnergy_integrate_pointwise_bound
    (M : ℝ) (Q D B C W S P R : Vec3 → ℝ)
    (hDint : Integrable D volume) (hSint : Integrable S volume)
    (hPint : Integrable P volume) (hRint : Integrable R volume)
    (hBint : Integrable B volume) (hCint : Integrable C volume)
    (hWint : Integrable W volume)
    (htotal : (∫ x : Vec3, Q x ∂volume) + ∫ x : Vec3, D x ∂volume =
      (∫ x : Vec3, B x ∂volume) - ∫ x : Vec3, C x ∂volume +
        ∫ x : Vec3, W x ∂volume)
    (hpoint : ∀ x, B x - C x + W x ≤
      (1 / 2 : ℝ) * D x + 36 * M ^ 2 * S x + P x +
        (1 / 2 : ℝ) * S x + (1 / 2 : ℝ) * R x) :
    2 * (∫ x : Vec3, Q x ∂volume) + ∫ x : Vec3, D x ∂volume ≤
      (72 * M ^ 2 + 1) * (∫ x : Vec3, S x ∂volume) +
        2 * (∫ x : Vec3, P x ∂volume) + ∫ x : Vec3, R x ∂volume := by
  have hpointAE : B - C + W ≤ᵐ[volume] fun x : Vec3 =>
      (1 / 2 : ℝ) * D x + (36 * M ^ 2 + 1 / 2) * S x + P x +
        (1 / 2 : ℝ) * R x := by
    filter_upwards [] with x
    have hx := hpoint x
    have harith : (1 / 2 : ℝ) * D x + 36 * M ^ 2 * S x + P x +
        (1 / 2 : ℝ) * S x + (1 / 2 : ℝ) * R x =
        (1 / 2 : ℝ) * D x + (36 * M ^ 2 + 1 / 2) * S x + P x +
          (1 / 2 : ℝ) * R x := by ring
    rw [harith] at hx
    exact hx
  have hRightInt : Integrable
      (fun x : Vec3 => (1 / 2 : ℝ) * D x +
        (36 * M ^ 2 + 1 / 2) * S x + P x + (1 / 2 : ℝ) * R x) volume := by
    exact (((hDint.const_mul _).add (hSint.const_mul _)).add hPint).add
      (hRint.const_mul _)
  have hLeftInt : Integrable (fun x : Vec3 => B x - C x + W x) volume :=
    (hBint.sub hCint).add hWint
  have hBounds := integral_mono_ae hLeftInt hRightInt hpointAE
  have hTbound :
      (∫ x : Vec3, Q x ∂volume) + ∫ x : Vec3, D x ∂volume ≤
        (1 / 2 : ℝ) * (∫ x : Vec3, D x ∂volume) +
          (36 * M ^ 2 + 1 / 2) * (∫ x : Vec3, S x ∂volume) +
          ∫ x : Vec3, P x ∂volume +
          (1 / 2 : ℝ) * (∫ x : Vec3, R x ∂volume) := by
    calc
      _ = ∫ x : Vec3, (B x - C x + W x) ∂volume := by
        have hint : (∫ x : Vec3, (B x - C x + W x) ∂volume) =
            (∫ x : Vec3, B x ∂volume) - ∫ x : Vec3, C x ∂volume +
              ∫ x : Vec3, W x ∂volume := by
          calc
            _ = (∫ x : Vec3, (B x - C x) ∂volume) +
                ∫ x : Vec3, W x ∂volume := integral_add (hBint.sub hCint) hWint
            _ = _ := by rw [integral_sub hBint hCint]
        rw [hint]
        exact htotal
      _ ≤ _ := hBounds
      _ = _ := by
        have hDS : (∫ x : Vec3,
            (1 / 2 : ℝ) * D x + (36 * M ^ 2 + 1 / 2) * S x ∂volume) =
            (∫ x : Vec3, (1 / 2 : ℝ) * D x ∂volume) +
              ∫ x : Vec3, (36 * M ^ 2 + 1 / 2) * S x ∂volume :=
          integral_add (hDint.const_mul _) (hSint.const_mul _)
        have hDSP : (∫ x : Vec3,
            ((1 / 2 : ℝ) * D x + (36 * M ^ 2 + 1 / 2) * S x) + P x ∂volume) =
            (∫ x : Vec3,
              (1 / 2 : ℝ) * D x + (36 * M ^ 2 + 1 / 2) * S x ∂volume) +
                ∫ x : Vec3, P x ∂volume :=
          integral_add ((hDint.const_mul _).add (hSint.const_mul _)) hPint
        have hDSPR : (∫ x : Vec3,
            (((1 / 2 : ℝ) * D x + (36 * M ^ 2 + 1 / 2) * S x) + P x) +
              (1 / 2 : ℝ) * R x ∂volume) =
            (∫ x : Vec3,
              ((1 / 2 : ℝ) * D x + (36 * M ^ 2 + 1 / 2) * S x) + P x ∂volume) +
              ∫ x : Vec3, (1 / 2 : ℝ) * R x ∂volume :=
          integral_add (((hDint.const_mul _).add (hSint.const_mul _)).add hPint)
            (hRint.const_mul _)
        calc
          _ = (∫ x : Vec3,
                ((1 / 2 : ℝ) * D x + (36 * M ^ 2 + 1 / 2) * S x) + P x ∂volume) +
                ∫ x : Vec3, (1 / 2 : ℝ) * R x ∂volume := hDSPR
          _ = ((∫ x : Vec3, (1 / 2 : ℝ) * D x ∂volume) +
                ∫ x : Vec3, (36 * M ^ 2 + 1 / 2) * S x ∂volume) +
                ∫ x : Vec3, P x ∂volume +
                ∫ x : Vec3, (1 / 2 : ℝ) * R x ∂volume := by rw [hDSP, hDS]
          _ = _ := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hTgrad :
      2 * (∫ x : Vec3, Q x ∂volume) + ∫ x : Vec3, D x ∂volume ≤
        (72 * M ^ 2 + 1) * (∫ x : Vec3, S x ∂volume) +
          2 * (∫ x : Vec3, P x ∂volume) + ∫ x : Vec3, R x ∂volume := by
    linarith only [hTbound]
  exact hTgrad

/-- A smooth compactly supported solution of the linear vorticity equation
satisfies the spatial differential energy inequality used in the smooth part
of `lem:localized-vorticity-energy`. Both matrix and vector forcing are measured in `L²` in this
smooth estimate. -/
theorem smoothVorticityEnergyDifferentialInequality
    {v z : Vec3 × ℝ → Vec3} {F : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {g : Vec3 × ℝ → Vec3}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hF : ∀ j i, ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => F w j i))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hzc : ∀ t : ℝ, HasCompactSupport (fun x : Vec3 => z (x, t)))
    (heq : ∀ (x : Vec3) (t : ℝ) (i : Fin 3),
      CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) -
        ∑ j : Fin 3, CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w => z w i) j j (x, t) =
      -(∑ j : Fin 3, CKN.spatialPartial
          (show ParabolicPoint → ℝ from fun w =>
            v w j * z w i - z w j * v w i) j (x, t)) +
        ∑ j : Fin 3, CKN.spatialPartial
          (show ParabolicPoint → ℝ from fun w => F w j i) j (x, t) +
        g (x, t) i)
    (M : ℝ) (hM : 0 ≤ M)
    (hvbound : ∀ x t, vec3EuclideanNorm (v (x, t)) ≤ M)
    (hF2 : ∀ t : ℝ, Integrable
      (fun x : Vec3 => ∑ j : Fin 3, ∑ i : Fin 3, (F (x, t) j i) ^ 2) volume)
    (hg2 : ∀ t : ℝ, Integrable
      (fun x : Vec3 => ∑ i : Fin 3, (g (x, t) i) ^ 2) volume) :
    ∀ t : ℝ,
      2 * (∫ x : Vec3, ∑ i : Fin 3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) +
        ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
          (CKN.spatialPartial (fun w : Vec3 × ℝ => z w i) j (x, t)) ^ 2 ≤
      (72 * M ^ 2 + 1) *
          (∫ x : Vec3, ∑ i : Fin 3, (z (x, t) i) ^ 2) +
        2 * (∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
          (F (x, t) j i) ^ 2) +
        ∫ x : Vec3, ∑ i : Fin 3, (g (x, t) i) ^ 2 := by
  intro t
  let Z : Fin 3 → Vec3 → ℝ := fun i x => z (x, t) i
  let T : Fin 3 → Vec3 → ℝ := fun i x =>
    CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t)
  let G : Fin 3 → Fin 3 → Vec3 → ℝ := fun j i x =>
    CKN.spatialDeriv (Z i) j x
  let A : Fin 3 → Fin 3 → Vec3 → ℝ := fun j i x =>
    v (x, t) j * z (x, t) i - z (x, t) j * v (x, t) i
  let H : Fin 3 → Fin 3 → Vec3 → ℝ := fun j i x => F (x, t) j i
  let Q : Vec3 → ℝ := fun x => ∑ i : Fin 3, T i x * Z i x
  let D : Vec3 → ℝ := fun x => ∑ j : Fin 3, ∑ i : Fin 3, (G j i x) ^ 2
  let P : Vec3 → ℝ := fun x => ∑ j : Fin 3, ∑ i : Fin 3, (H j i x) ^ 2
  let S : Vec3 → ℝ := fun x => ∑ i : Fin 3, (Z i x) ^ 2
  let R : Vec3 → ℝ := fun x => ∑ i : Fin 3, (g (x, t) i) ^ 2
  let B : Vec3 → ℝ := fun x =>
    ∑ i : Fin 3, ∑ j : Fin 3, A j i x * G j i x
  let C : Vec3 → ℝ := fun x =>
    ∑ i : Fin 3, ∑ j : Fin 3, H j i x * G j i x
  let W : Vec3 → ℝ := fun x => ∑ i : Fin 3, g (x, t) i * Z i x
  have hZsmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (Z i) := by
    exact vorticityEnergy_slice_contDiff
      (vorticityEnergy_fieldComponent_contDiff hz i) t
  have hZcompact (i : Fin 3) : HasCompactSupport (Z i) := by
    exact vorticityEnergy_component_hasCompactSupport (hzc t) i
  have hTsmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (T i) := by
    exact (CKN.contDiff_timePartial
      (vorticityEnergy_fieldComponent_contDiff hz i)).comp
        (contDiff_id.prodMk contDiff_const)
  have hGsmooth (j i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (G j i) := by
    exact CKN.contDiff_spatialDeriv_smooth (hZsmooth i) j
  have hGcompact (j i : Fin 3) : HasCompactSupport (G j i) := by
    change HasCompactSupport
      (CKN.spatialDeriv (fun x : Vec3 => z (x, t) i) j)
    let zi : Vec3 × ℝ → ℝ := fun w => z w i
    have hziCompact : HasCompactSupport (fun x : Vec3 => zi (x, t)) := by
      exact vorticityEnergy_component_hasCompactSupport (hzc t) i
    simpa only [zi] using
      (vorticityEnergy_first_slice_hasCompactSupport
        (f := zi) (t := t) hziCompact j)
  have hAsmooth (j i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (A j i) := by
    have hvj : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => v (x, t) j) :=
      vorticityEnergy_slice_contDiff ((contDiff_apply ℝ ℝ j).comp hv) t
    have hzi : ContDiff ℝ (⊤ : ℕ∞) (Z i) := hZsmooth i
    have hzj : ContDiff ℝ (⊤ : ℕ∞) (Z j) := hZsmooth j
    have hvi : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => v (x, t) i) :=
      vorticityEnergy_slice_contDiff ((contDiff_apply ℝ ℝ i).comp hv) t
    dsimp [A, Z]
    exact (hvj.mul hzi).sub (hzj.mul hvi)
  have hHsmooth (j i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (H j i) :=
    vorticityEnergy_slice_contDiff (hF j i) t
  have hQint : Integrable Q volume := by
    have hi (i : Fin 3) : Integrable (fun x : Vec3 => T i x * Z i x) volume :=
      vorticityEnergy_integrable_mul_compact (hTsmooth i).continuous
        (hZsmooth i).continuous (hZcompact i)
    change Integrable (fun x : Vec3 => ∑ i : Fin 3, T i x * Z i x) volume
    exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hDint : Integrable D volume := by
    have hi (i j : Fin 3) : Integrable (fun x : Vec3 => (G j i x) ^ 2) volume :=
      by
        simpa only [pow_two] using
          (vorticityEnergy_integrable_mul_compact (hGsmooth j i).continuous
            (hGsmooth j i).continuous (hGcompact j i))
    change Integrable (fun x : Vec3 => ∑ j : Fin 3, ∑ i : Fin 3,
      (G j i x) ^ 2) volume
    exact integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun i _ => hi i j))
  have hBint : Integrable B volume := by
    have hi (j i : Fin 3) : Integrable
        (fun x : Vec3 => A j i x * G j i x) volume :=
      vorticityEnergy_integrable_mul_compact (hAsmooth j i).continuous
        (hGsmooth j i).continuous (hGcompact j i)
    change Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      A j i x * G j i x) volume
    exact integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hi j i))
  have hCint : Integrable C volume := by
    have hi (j i : Fin 3) : Integrable
        (fun x : Vec3 => H j i x * G j i x) volume :=
      vorticityEnergy_integrable_mul_compact (hHsmooth j i).continuous
        (hGsmooth j i).continuous (hGcompact j i)
    change Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      H j i x * G j i x) volume
    exact integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hi j i))
  have hWint : Integrable W volume := by
    have hi (i : Fin 3) : Integrable
        (fun x : Vec3 => g (x, t) i * Z i x) volume :=
      vorticityEnergy_integrable_mul_compact
        (vorticityEnergy_slice_contDiff
          ((contDiff_apply ℝ ℝ i).comp hg) t).continuous
        (hZsmooth i).continuous (hZcompact i)
    change Integrable (fun x : Vec3 => ∑ i : Fin 3,
      g (x, t) i * Z i x) volume
    exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hSint : Integrable S volume := by
    have hi (i : Fin 3) : Integrable (fun x : Vec3 => (Z i x) ^ 2) volume :=
      by
        simpa only [pow_two] using
          (vorticityEnergy_integrable_mul_compact (hZsmooth i).continuous
            (hZsmooth i).continuous (hZcompact i))
    change Integrable (fun x : Vec3 => ∑ i : Fin 3, (Z i x) ^ 2) volume
    exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hPint : Integrable P volume := by simpa [P, H] using hF2 t
  have hRint : Integrable R volume := by simpa [R] using hg2 t
  have hcomponent (i : Fin 3) :=
    smoothVorticityComponentEnergyBalance hv hz hF hg hzc heq t i
  have htotal :
      (∫ x : Vec3, Q x ∂volume) + ∫ x : Vec3, D x ∂volume =
        (∫ x : Vec3, B x ∂volume) - ∫ x : Vec3, C x ∂volume +
          ∫ x : Vec3, W x ∂volume := by
    have hQ : (∑ i : Fin 3, ∫ x : Vec3, T i x * Z i x ∂volume) =
        ∫ x : Vec3, Q x ∂volume := by
      simpa [Q] using (vorticityEnergy_integral_finsetSum
        (fun i => by
          simpa [T, Z] using vorticityEnergy_integrable_mul_compact
            (hTsmooth i).continuous (hZsmooth i).continuous (hZcompact i))).symm
    have hD : (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : Vec3, (G j i x) ^ 2 ∂volume) = ∫ x : Vec3, D x ∂volume := by
      calc
        _ = ∑ j : Fin 3, ∑ i : Fin 3,
            ∫ x : Vec3, (G j i x) ^ 2 ∂volume := Finset.sum_comm
        _ = ∫ x : Vec3, D x ∂volume := by
          simpa [D] using (vorticityEnergy_integral_finsetSum2 (fun j i => by
            simpa [G, pow_two] using vorticityEnergy_integrable_mul_compact
              (hGsmooth j i).continuous (hGsmooth j i).continuous
              (hGcompact j i))).symm
    have hB : (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : Vec3, A j i x * G j i x ∂volume) = ∫ x : Vec3, B x ∂volume := by
      simpa [B] using (vorticityEnergy_integral_finsetSum2 (fun i j => by
        simpa [A, G] using vorticityEnergy_integrable_mul_compact
          (hAsmooth j i).continuous (hGsmooth j i).continuous (hGcompact j i))).symm
    have hC : (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : Vec3, H j i x * G j i x ∂volume) = ∫ x : Vec3, C x ∂volume := by
      simpa [C] using (vorticityEnergy_integral_finsetSum2 (fun i j => by
        simpa [H, G] using vorticityEnergy_integrable_mul_compact
          (hHsmooth j i).continuous (hGsmooth j i).continuous (hGcompact j i))).symm
    have hW : (∑ i : Fin 3, ∫ x : Vec3,
        g (x, t) i * Z i x ∂volume) = ∫ x : Vec3, W x ∂volume := by
      simpa [W] using (vorticityEnergy_integral_finsetSum (fun i => by
        simpa [Z] using vorticityEnergy_integrable_mul_compact
          (vorticityEnergy_slice_contDiff
            ((contDiff_apply ℝ ℝ i).comp hg) t).continuous
          (hZsmooth i).continuous (hZcompact i))).symm
    have hsum' :
        (∑ i : Fin 3, (∫ x : Vec3, T i x * Z i x ∂volume +
            ∑ j : Fin 3, ∫ x : Vec3, (G j i x) ^ 2 ∂volume)) =
          ∑ i : Fin 3, ((∑ j : Fin 3,
              ∫ x : Vec3, A j i x * G j i x ∂volume) -
            (∑ j : Fin 3, ∫ x : Vec3, H j i x * G j i x ∂volume) +
            ∫ x : Vec3, g (x, t) i * Z i x ∂volume) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [T, Z, A, H, G, CKN.spatialPartial, CKN.spatialDeriv] using hcomponent i
    have hsumrhs :
        (∑ i : Fin 3, ((∑ j : Fin 3,
            ∫ x : Vec3, A j i x * G j i x ∂volume) -
          (∑ j : Fin 3, ∫ x : Vec3, H j i x * G j i x ∂volume) +
          ∫ x : Vec3, g (x, t) i * Z i x ∂volume)) =
          (∑ i : Fin 3, ∑ j : Fin 3,
            ∫ x : Vec3, A j i x * G j i x ∂volume) -
          (∑ i : Fin 3, ∑ j : Fin 3,
            ∫ x : Vec3, H j i x * G j i x ∂volume) +
          ∑ i : Fin 3, ∫ x : Vec3, g (x, t) i * Z i x ∂volume := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hleftSum : (∑ i : Fin 3,
        (∫ x : Vec3, T i x * Z i x ∂volume +
          ∑ j : Fin 3, ∫ x : Vec3, (G j i x) ^ 2 ∂volume)) =
        (∫ x : Vec3, Q x ∂volume) + ∫ x : Vec3, D x ∂volume := by
      rw [Finset.sum_add_distrib, hQ, hD]
    have hrightSum : (∑ i : Fin 3, ((∑ j : Fin 3,
        ∫ x : Vec3, A j i x * G j i x ∂volume) -
      (∑ j : Fin 3, ∫ x : Vec3, H j i x * G j i x ∂volume) +
      ∫ x : Vec3, g (x, t) i * Z i x ∂volume)) =
        (∫ x : Vec3, B x ∂volume) - ∫ x : Vec3, C x ∂volume +
          ∫ x : Vec3, W x ∂volume := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hB, hC, hW]
    calc
      (∫ x : Vec3, Q x ∂volume) + ∫ x : Vec3, D x ∂volume =
          ∑ i : Fin 3, (∫ x : Vec3, T i x * Z i x ∂volume +
            ∑ j : Fin 3, ∫ x : Vec3, (G j i x) ^ 2 ∂volume) := hleftSum.symm
      _ = ∑ i : Fin 3, ((∑ j : Fin 3,
          ∫ x : Vec3, A j i x * G j i x ∂volume) -
        (∑ j : Fin 3, ∫ x : Vec3, H j i x * G j i x ∂volume) +
        ∫ x : Vec3, g (x, t) i * Z i x ∂volume) := hsum'
      _ = (∫ x : Vec3, B x ∂volume) - ∫ x : Vec3, C x ∂volume +
          ∫ x : Vec3, W x ∂volume := hrightSum
  have hpoint (x : Vec3) : B x - C x + W x ≤
      (1 / 2 : ℝ) * D x + 36 * M ^ 2 * S x + P x +
        (1 / 2 : ℝ) * S x + (1 / 2 : ℝ) * R x := by
    have hp := vorticityEnergy_pointwise_pairing_bound M hM
      (v (x, t)) (z (x, t)) (g (x, t))
      (fun j i => F (x, t) j i) (fun j i => G j i x) (hvbound x t)
    simpa only [B, C, W, D, P, S, R, A, H, Z] using hp
  have hTgrad := vorticityEnergy_integrate_pointwise_bound M Q D B C W S P R
    hDint hSint hPint hRint hBint hCint hWint htotal hpoint
  simpa [Q, D, P, S, R, T, Z, G, H,
    CKN.spatialPartial, CKN.spatialDeriv] using hTgrad

private theorem vorticityEnergy_integrable_smooth_compact
    {K : Set Vec3} (hK : IsCompact K)
    {f : Vec3 → ℝ} (hf : Continuous f)
    (hzero : ∀ x, x ∉ K → f x = 0) : Integrable f volume := by
  have hfc : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    change f x ≠ 0 at hx
    by_contra hxK
    exact hx (hzero x hxK)
  exact hf.integrable_of_hasCompactSupport hfc

/-- The smooth spatial energy inequality applies to fields with one common
compact spatial support, the support condition used in smooth approximation
for `lem:localized-vorticity-energy`. -/
theorem smoothVorticityEnergyDifferentialInequality_commonSupport
    {v z : Vec3 × ℝ → Vec3} {F : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {g : Vec3 × ℝ → Vec3}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hF : ∀ j i, ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => F w j i))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcommon : ∃ K : Set Vec3, IsCompact K ∧
      ∀ x, x ∉ K → ∀ t,
        z (x, t) = 0 ∧ (∀ j i, F (x, t) j i = 0) ∧ g (x, t) = 0)
    (heq : ∀ (x : Vec3) (t : ℝ) (i : Fin 3),
      CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) -
        ∑ j : Fin 3, CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w => z w i) j j (x, t) =
      -(∑ j : Fin 3, CKN.spatialPartial
          (show ParabolicPoint → ℝ from fun w =>
            v w j * z w i - z w j * v w i) j (x, t)) +
        ∑ j : Fin 3, CKN.spatialPartial
          (show ParabolicPoint → ℝ from fun w => F w j i) j (x, t) +
        g (x, t) i)
    (M : ℝ) (hM : 0 ≤ M)
    (hvbound : ∀ x t, vec3EuclideanNorm (v (x, t)) ≤ M) :
    ∀ t : ℝ,
      2 * (∫ x : Vec3, ∑ i : Fin 3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) +
        ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
          (CKN.spatialPartial (fun w : Vec3 × ℝ => z w i) j (x, t)) ^ 2 ≤
      (72 * M ^ 2 + 1) *
          (∫ x : Vec3, ∑ i : Fin 3, (z (x, t) i) ^ 2) +
        2 * (∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
          (F (x, t) j i) ^ 2) +
        ∫ x : Vec3, ∑ i : Fin 3, (g (x, t) i) ^ 2 := by
  rcases hcommon with ⟨K, hK, hzero⟩
  have hzc (t : ℝ) : HasCompactSupport (fun x : Vec3 => z (x, t)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    change z (x, t) ≠ 0 at hx
    by_contra hxK
    exact hx (hzero x hxK t).1
  have hF2 (t : ℝ) : Integrable
      (fun x : Vec3 => ∑ j : Fin 3, ∑ i : Fin 3, (F (x, t) j i) ^ 2) volume := by
    apply vorticityEnergy_integrable_smooth_compact hK
    · apply continuous_finsetSum
      intro j hj
      apply continuous_finsetSum
      intro i hi
      exact ((hF j i).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
    · intro x hx
      apply Finset.sum_eq_zero
      intro j hj
      apply Finset.sum_eq_zero
      intro i hi
      rw [(hzero x hx t).2.1 j i]
      simp
  have hg2 (t : ℝ) : Integrable
      (fun x : Vec3 => ∑ i : Fin 3, (g (x, t) i) ^ 2) volume := by
    apply vorticityEnergy_integrable_smooth_compact hK
    · apply continuous_finsetSum
      intro i hi
      exact ((contDiff_apply ℝ ℝ i).comp hg).continuous.comp
        (continuous_id.prodMk continuous_const) |>.pow 2
    · intro x hx
      apply Finset.sum_eq_zero
      intro i hi
      rw [congrFun (hzero x hx t).2.2 i]
      simp
  exact smoothVorticityEnergyDifferentialInequality hv hz hF hg hzc heq M hM
    hvbound hF2 hg2

end

end ESS
