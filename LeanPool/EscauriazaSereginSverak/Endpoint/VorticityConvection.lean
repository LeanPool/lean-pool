/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEq

/-!
# Convection pairing for weak vorticity

The weak product rule and the zero gradient trace reduce the convection term
to the cross product of velocity and vorticity.
-/

public section


open MeasureTheory
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

private theorem vorticityProductTestIntegrable
    {U : Set Vec3} (hUfinite : (volume.restrict U) Set.univ < ⊤)
    {a b φ : Vec3 → ℝ}
    (ha : MemLp a 2 (volume.restrict U)) (hb : MemLp b 2 (volume.restrict U))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    IntegrableOn (fun x => a x * b x * φ x) U volume := by
  let μ := volume.restrict U
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ENNReal.HolderConjugate.instTwoTwo
  let : IsFiniteMeasure μ := ⟨hUfinite⟩
  have hab : MemLp (fun x => a x * b x) 1 μ := ha.mul hb
  have hφtop : MemLp φ (⊤ : ℝ≥0∞) μ :=
    hφ.continuous.memLp_top_of_hasCompactSupport hφc μ
  have hprod : MemLp (fun x => a x * b x * φ x) 1 μ := hab.mul hφtop
  have hInt : Integrable (fun x => a x * b x * φ x) μ :=
    hprod.integrable (q := 1) (by norm_num)
  simpa [IntegrableOn, μ] using hInt

/-- The nonlinear term tested against a divergence-free field is the pairing
with the cross product of velocity and weak vorticity (manuscript
`lem:vorticity-weak-eq`). -/
theorem suitableWeakConvectionPairingDivergenceFree
    {U : Set Vec3} (hU : IsOpen U)
    (hUfinite : (volume.restrict U) Set.univ < ⊤)
    {v : Vec3 → Vec3} {Dv : Vec3 → Fin 3 → Vec3}
    (hv : ∀ i : Fin 3, MemLp (fun x => v x i) 2 (volume.restrict U))
    (hDv : MemLp Dv 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => v x i) (fun x => Dv x i))
    (htrace : (fun x => ∑ i : Fin 3, Dv x i i) =ᵐ[volume.restrict U] 0)
    {φ : Vec3 → Vec3}
    (hφ : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x i))
    (hφc : ∀ i : Fin 3, HasCompactSupport (fun x => φ x i))
    (hφU : ∀ i : Fin 3, tsupport (fun x => φ x i) ⊆ U)
    (hdivφ : ∀ x, ∑ i : Fin 3, CKN.spatialDeriv (fun y => φ y i) i x = 0) :
    (∑ i : Fin 3, ∫ x in U, ∑ j : Fin 3,
      v x i * v x j * CKN.spatialDeriv (fun y => φ y i) j x) =
    ∑ i : Fin 3, ∫ x in U,
      spatialCross (v x) (spatialWeakVorticity Dv x) i * φ x i := by
  let A (i j : Fin 3) (x : Vec3) := Dv x i j * v x j * φ x i
  let B (i j : Fin 3) (x : Vec3) := v x i * Dv x j j * φ x i
  let G (i j : Fin 3) (x : Vec3) := v x j * Dv x j i * φ x i
  let X (i : Fin 3) (x : Vec3) :=
    spatialCross (v x) (spatialWeakVorticity Dv x) i * φ x i
  have hDvVec (i : Fin 3) : MemLp (fun x => Dv x i) 2 (volume.restrict U) :=
    (memLp_pi_iff.mp hDv) i
  have hDvCoord (i j : Fin 3) : MemLp (fun x => Dv x i j) 2
      (volume.restrict U) := (memLp_pi_iff.mp (hDvVec i)) j
  have hAterm (i j : Fin 3) : IntegrableOn (A i j) U volume := by
    exact vorticityProductTestIntegrable hUfinite (hDvCoord i j) (hv j) (hφ i) (hφc i)
  have hBterm (i j : Fin 3) : IntegrableOn (B i j) U volume := by
    exact vorticityProductTestIntegrable hUfinite (hv i) (hDvCoord j j) (hφ i) (hφc i)
  have hGterm (i j : Fin 3) : IntegrableOn (G i j) U volume := by
    exact vorticityProductTestIntegrable hUfinite (hv j) (hDvCoord j i) (hφ i) (hφc i)
  have hAsum (i : Fin 3) : IntegrableOn (fun x => ∑ j : Fin 3, A i j x) U volume :=
    integrable_finsetSum _ (fun j _ => hAterm i j)
  have hBsum (i : Fin 3) : IntegrableOn (fun x => ∑ j : Fin 3, B i j x) U volume :=
    integrable_finsetSum _ (fun j _ => hBterm i j)
  have hGsum (i : Fin 3) : IntegrableOn (fun x => ∑ j : Fin 3, G i j x) U volume :=
    integrable_finsetSum _ (fun j _ => hGterm i j)
  have hpair := suitableWeakConvectionTensorPairing hU hUfinite hv
    (fun i => hDvVec i) hweak
    hφ hφc hφU
  have hABeq (i : Fin 3) : (fun x => ∑ j : Fin 3, (A i j x + B i j x)) =
      (fun x => (∑ j : Fin 3, A i j x) + ∑ j : Fin 3, B i j x) := by
    funext x
    simp only [Finset.sum_add_distrib]
  have hsplit (i : Fin 3) :
      (∫ x in U, (∑ j : Fin 3, (A i j x + B i j x))) =
        (∫ x in U, ∑ j : Fin 3, A i j x) +
          ∫ x in U, ∑ j : Fin 3, B i j x := by
    rw [hABeq i, integral_add (hAsum i) (hBsum i)]
  have htraceZero (i : Fin 3) : ∫ x in U, ∑ j : Fin 3, B i j x = 0 := by
    have heq : (fun x => ∑ j : Fin 3, B i j x) =ᵐ[volume.restrict U]
        (fun _ => 0) := by
      filter_upwards [htrace] with x hx
      have hfactor : (∑ j : Fin 3, B i j x) =
          (v x i * φ x i) * ∑ j : Fin 3, Dv x j j := by
        calc
          (∑ j : Fin 3, B i j x) =
              ∑ j : Fin 3, (v x i * φ x i) * Dv x j j := by
                apply Finset.sum_congr rfl
                intro j hj
                dsimp [B]
                ring
          _ = (v x i * φ x i) * ∑ j : Fin 3, Dv x j j :=
            (Finset.mul_sum _ _ _).symm
      rw [hfactor, hx]
      simp
    rw [integral_congr_ae heq]
    simp
  have hAeqG (i : Fin 3) (x : Vec3) :
      (∑ j : Fin 3, A i j x) = (∑ j : Fin 3, G i j x) - X i x := by
    have hc := spatialConvective_decomposition v Dv x i
    dsimp [A, G, X]
    calc
      (∑ j : Fin 3, Dv x i j * v x j * φ x i) =
          (∑ j : Fin 3, v x j * Dv x i j) * φ x i := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ((∑ j : Fin 3, v x j * Dv x j i) -
          spatialCross (v x) (spatialWeakVorticity Dv x) i) * φ x i := by rw [hc]
      _ = (∑ j : Fin 3, v x j * Dv x j i * φ x i) -
          spatialCross (v x) (spatialWeakVorticity Dv x) i * φ x i := by
            rw [sub_mul, Finset.sum_mul]
  have hXsum (i : Fin 3) : IntegrableOn (X i) U volume := by
    have heq : X i =ᵐ[volume.restrict U]
        (fun x => (∑ j : Fin 3, G i j x) - (∑ j : Fin 3, A i j x)) := by
      filter_upwards [] with x
      have h := hAeqG i x
      dsimp [A, G, X] at h ⊢
      linarith only [h]
    exact (hGsum i).sub (hAsum i) |>.congr heq.symm
  have hGzero := suitableWeakGradientPairingZero hU hUfinite hv hDv hweak
    hφ hφc hφU hdivφ
  have hGzero' : (∑ i : Fin 3, ∫ x in U, ∑ j : Fin 3, G i j x) = 0 := by
    calc
      (∑ i : Fin 3, ∫ x in U, ∑ j : Fin 3, G i j x) =
          ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in U, v x j * Dv x j i * φ x i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [integral_finsetSum _ (fun j _ => hGterm i j)]
      _ = 0 := hGzero
  calc
    (∑ i : Fin 3, ∫ x in U, (∑ j : Fin 3,
        v x i * v x j * CKN.spatialDeriv (fun y => φ y i) j x)) =
      -∑ i : Fin 3, ∫ x in U, (∑ j : Fin 3,
        (Dv x i j * v x j + v x i * Dv x j j) * φ x i) := hpair
    _ = -∑ i : Fin 3, ∫ x in U, (∑ j : Fin 3, (A i j x + B i j x)) := by
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro i hi
          apply integral_congr_ae
          filter_upwards [] with x
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [A, B]
          ring
    _ = -∑ i : Fin 3,
        ((∫ x in U, ∑ j : Fin 3, A i j x) +
          ∫ x in U, ∑ j : Fin 3, B i j x) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            exact hsplit i
    _ = -∑ i : Fin 3,
        ((∫ x in U, ∑ j : Fin 3, G i j x) - ∫ x in U, X i x) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            rw [htraceZero i]
            have hEq : (fun x => ∑ j : Fin 3, A i j x) =ᵐ[volume.restrict U]
                (fun x => (∑ j : Fin 3, G i j x) - X i x) := by
              filter_upwards [] with x
              exact hAeqG i x
            rw [integral_congr_ae hEq]
            rw [integral_sub (hGsum i) (hXsum i)]
            ring
    _ = ∑ i : Fin 3, ∫ x in U, X i x := by
          rw [Finset.sum_sub_distrib, hGzero']
          simp only [zero_sub, neg_neg]

end

end ESS
