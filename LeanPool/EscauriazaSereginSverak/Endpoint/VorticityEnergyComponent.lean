/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.SmoothIBP
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityEnergyAlgebra

/-!
# Smooth spatial energy identity for vorticity

The compactly supported smooth energy calculation is the first step in
`lem:localized-vorticity-energy`.
-/

public section


open MeasureTheory Set
open scoped BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

/-- A component of a compactly supported spatial slice remains compactly
supported (manuscript `lem:localized-vorticity-energy`). -/
theorem vorticityEnergy_component_hasCompactSupport
    {z : Vec3 × ℝ → Vec3}
    {t : ℝ} (hz : HasCompactSupport (fun x : Vec3 => z (x, t)))
    (i : Fin 3) :
    HasCompactSupport (fun x : Vec3 => z (x, t) i) := by
  have hc : HasCompactSupport ((fun y : Vec3 => y i) ∘ fun x => z (x, t)) :=
    hz.comp_left (g := fun y : Vec3 => y i) (by simp)
  convert hc using 1
  funext x
  rfl

/-- A smooth factor times a compactly supported smooth factor is integrable
(manuscript `lem:localized-vorticity-energy`). -/
theorem vorticityEnergy_integrable_mul_compact
    {f g : Vec3 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
  Integrable (fun x : Vec3 => f x * g x) volume := by
  exact (hf.mul hg).integrable_of_hasCompactSupport (hgc.mul_left (f := f))

private theorem vorticityEnergy_spatialPartial_eq_sliceDeriv
    {f : Vec3 × ℝ → ℝ} (j : Fin 3) (t : ℝ) (x : Vec3) :
    CKN.spatialPartial (show ParabolicPoint → ℝ from f) j (x, t) =
      CKN.spatialDeriv (fun y : Vec3 => f (y, t)) j x := rfl

private theorem vorticityEnergy_secondPartial_eq_sliceDeriv
    {f : Vec3 × ℝ → ℝ} (j : Fin 3) (t : ℝ) (x : Vec3) :
    CKN.spatialSecondPartial (show ParabolicPoint → ℝ from f) j j (x, t) =
      CKN.spatialDeriv (CKN.spatialDeriv (fun y : Vec3 => f (y, t)) j) j x := rfl

/-- Restricting a smooth space-time scalar field to a time slice preserves
smoothness (manuscript `lem:localized-vorticity-energy`). -/
theorem vorticityEnergy_slice_contDiff
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => f (x, t)) := by
  exact hf.comp (contDiff_id.prodMk contDiff_const)

private theorem vorticityEnergy_first_slice_contDiff
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : Fin 3) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialDeriv (fun x : Vec3 => f (x, t)) j) := by
  exact CKN.contDiff_spatialDeriv_smooth
    (vorticityEnergy_slice_contDiff hf t) j

private theorem vorticityEnergy_second_slice_contDiff
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : Fin 3) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialDeriv
        (CKN.spatialDeriv (fun x : Vec3 => f (x, t)) j) j) := by
  exact CKN.contDiff_spatialDeriv_smooth
    (vorticityEnergy_first_slice_contDiff hf j t) j

/-- Every first spatial derivative of a compactly supported smooth slice has
compact support (manuscript `lem:localized-vorticity-energy`). -/
theorem vorticityEnergy_first_slice_hasCompactSupport
    {f : Vec3 × ℝ → ℝ} {t : ℝ}
    (hfc : HasCompactSupport (fun x : Vec3 => f (x, t))) (j : Fin 3) :
    HasCompactSupport
      (CKN.spatialDeriv (fun x : Vec3 => f (x, t)) j) := by
  change HasCompactSupport
    (fun x : Vec3 => (fderiv ℝ (fun y : Vec3 => f (y, t)) x) (CKN.basisVec j))
  exact hfc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)

private theorem vorticityEnergy_first_slice_hasCompactSupport_of_compact
    {f : Vec3 × ℝ → ℝ} {t : ℝ}
    (hfc : HasCompactSupport (fun x : Vec3 => f (x, t))) (j : Fin 3) :
    HasCompactSupport
      (fun x : Vec3 => CKN.spatialDeriv (fun y : Vec3 => f (y, t)) j x) :=
  vorticityEnergy_first_slice_hasCompactSupport hfc j

/-- A component of a smooth vector-valued space-time field is smooth
(manuscript `lem:localized-vorticity-energy`). -/
theorem vorticityEnergy_fieldComponent_contDiff
    {z : Vec3 × ℝ → Vec3} (hz : ContDiff ℝ (⊤ : ℕ∞) z) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => z w i) :=
  (contDiff_apply ℝ ℝ i).comp hz

/-- Integrals commute with finite sums of integrable vorticity components
(manuscript `lem:localized-vorticity-energy`). -/
theorem vorticityEnergy_integral_finsetSum
    {f : Fin 3 → Vec3 → ℝ}
    (hf : ∀ i, Integrable (f i) (volume : Measure Vec3)) :
    (∫ x : Vec3, ∑ i : Fin 3, f i x ∂volume) =
      ∑ i : Fin 3, ∫ x : Vec3, f i x ∂volume := by
  exact integral_finsetSum (μ := (volume : Measure Vec3)) Finset.univ
    (fun i _ => hf i)

/-- Iterated finite sums commute with integration for integrable terms
(manuscript `lem:localized-vorticity-energy`). -/
theorem vorticityEnergy_integral_finsetSum2
    {f : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hf : ∀ i j, Integrable (f i j) (volume : Measure Vec3)) :
    (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, f i j x ∂volume) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, f i j x ∂volume := by
  rw [vorticityEnergy_integral_finsetSum (fun i =>
    integrable_finsetSum _ (fun j _ => hf i j))]
  apply Finset.sum_congr rfl
  intro i hi
  exact vorticityEnergy_integral_finsetSum (fun j => hf i j)

private theorem vorticityEnergy_integral_finsetSum3
    {f : Fin 3 → Fin 3 → Fin 3 → Vec3 → ℝ}
    (hf : ∀ i j k, Integrable (f i j k) (volume : Measure Vec3)) :
    (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        f i j k x ∂volume) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ∫ x : Vec3, f i j k x ∂volume := by
  rw [vorticityEnergy_integral_finsetSum2 (fun i j =>
    integrable_finsetSum _ (fun k _ => hf i j k))]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact vorticityEnergy_integral_finsetSum (fun k => hf i j k)

private theorem vorticityEnergy_integral_mul_comm
    {f g : Vec3 → ℝ} :
    (∫ x : Vec3, f x * g x ∂volume) = ∫ x, g x * f x ∂volume := by
  apply integral_congr_ae
  filter_upwards [] with x
  ring

private theorem vorticityEnergy_integrateComponentEquation
    {Z T G : Vec3 → ℝ} {S DA DH : Fin 3 → Vec3 → ℝ}
    (heq : ∀ x : Vec3,
      T x - ∑ j : Fin 3, S j x =
        -(∑ j : Fin 3, DA j x) + ∑ j : Fin 3, DH j x + G x)
    (hTI : Integrable (fun x : Vec3 => T x * Z x) volume)
    (hSI : ∀ j : Fin 3, Integrable (fun x : Vec3 => S j x * Z x) volume)
    (hDAI : ∀ j : Fin 3, Integrable (fun x : Vec3 => DA j x * Z x) volume)
    (hDHI : ∀ j : Fin 3, Integrable (fun x : Vec3 => DH j x * Z x) volume)
    (hGI : Integrable (fun x : Vec3 => G x * Z x) volume) :
    (∫ x : Vec3, T x * Z x ∂volume) -
        ∑ j : Fin 3, ∫ x : Vec3, S j x * Z x ∂volume =
      -(∑ j : Fin 3, ∫ x : Vec3, DA j x * Z x ∂volume) +
        ∑ j : Fin 3, ∫ x : Vec3, DH j x * Z x ∂volume +
        ∫ x : Vec3, G x * Z x ∂volume := by
  have hSI_sum : Integrable
      (fun x : Vec3 => (∑ j : Fin 3, S j x) * Z x) volume := by
    have heq' : (fun x : Vec3 => (∑ j : Fin 3, S j x) * Z x) =
        fun x => ∑ j : Fin 3, S j x * Z x := by
      funext x
      rw [Finset.sum_mul]
    rw [heq']
    exact integrable_finsetSum _ (fun j _ => hSI j)
  have hDAI_sum : Integrable
      (fun x : Vec3 => (∑ j : Fin 3, DA j x) * Z x) volume := by
    have heq' : (fun x : Vec3 => (∑ j : Fin 3, DA j x) * Z x) =
        fun x => ∑ j : Fin 3, DA j x * Z x := by
      funext x
      rw [Finset.sum_mul]
    rw [heq']
    exact integrable_finsetSum _ (fun j _ => hDAI j)
  have hDHI_sum : Integrable
      (fun x : Vec3 => (∑ j : Fin 3, DH j x) * Z x) volume := by
    have heq' : (fun x : Vec3 => (∑ j : Fin 3, DH j x) * Z x) =
        fun x => ∑ j : Fin 3, DH j x * Z x := by
      funext x
      rw [Finset.sum_mul]
    rw [heq']
    exact integrable_finsetSum _ (fun j _ => hDHI j)
  have hRaw :
      (∫ x : Vec3, (T x - ∑ j : Fin 3, S j x) * Z x ∂volume) =
        ∫ x : Vec3,
          (-(∑ j : Fin 3, DA j x) + ∑ j : Fin 3, DH j x + G x) * Z x ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      congrArg (fun y : ℝ => y * Z x) (heq x))
  have hLeft :
      (∫ x : Vec3, (T x - ∑ j : Fin 3, S j x) * Z x ∂volume) =
        (∫ x : Vec3, T x * Z x ∂volume) -
          ∑ j : Fin 3, ∫ x : Vec3, S j x * Z x ∂volume := by
    calc
      _ = ∫ x : Vec3, T x * Z x - (∑ j : Fin 3, S j x) * Z x ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x : Vec3, T x * Z x ∂volume) -
            ∫ x : Vec3, (∑ j : Fin 3, S j x) * Z x ∂volume :=
        integral_sub hTI hSI_sum
      _ = _ := by
        have hExpand :
            (∫ x : Vec3, (∑ j : Fin 3, S j x) * Z x ∂volume) =
              ∑ j : Fin 3, ∫ x : Vec3, S j x * Z x ∂volume := by
          rw [show (fun x : Vec3 => (∑ j : Fin 3, S j x) * Z x) =
              fun x => ∑ j : Fin 3, S j x * Z x by
                funext x
                rw [Finset.sum_mul]]
          exact vorticityEnergy_integral_finsetSum (fun j => hSI j)
        rw [hExpand]
  have hRight :
      (∫ x : Vec3,
        (-(∑ j : Fin 3, DA j x) + ∑ j : Fin 3, DH j x + G x) * Z x ∂volume) =
        -(∑ j : Fin 3, ∫ x : Vec3, DA j x * Z x ∂volume) +
          ∑ j : Fin 3, ∫ x : Vec3, DH j x * Z x ∂volume +
          ∫ x : Vec3, G x * Z x ∂volume := by
    calc
      _ = ∫ x : Vec3,
          (-( (∑ j : Fin 3, DA j x) * Z x) +
            (∑ j : Fin 3, DH j x) * Z x + G x * Z x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = -(∫ x : Vec3, (∑ j : Fin 3, DA j x) * Z x ∂volume) +
            ∫ x : Vec3, (∑ j : Fin 3, DH j x) * Z x ∂volume +
            ∫ x : Vec3, G x * Z x ∂volume := by
        calc
          _ = ∫ x : Vec3,
              -( (∑ j : Fin 3, DA j x) * Z x) +
                ((∑ j : Fin 3, DH j x) * Z x + G x * Z x) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
          _ = (∫ x : Vec3, -( (∑ j : Fin 3, DA j x) * Z x) ∂volume) +
                ∫ x : Vec3,
                  (∑ j : Fin 3, DH j x) * Z x + G x * Z x ∂volume :=
            integral_add hDAI_sum.neg (hDHI_sum.add hGI)
          _ = _ := by
            rw [integral_neg, integral_add hDHI_sum hGI]
            ring
      _ = _ := by
        have hExpandA :
            (∫ x : Vec3, (∑ j : Fin 3, DA j x) * Z x ∂volume) =
              ∑ j : Fin 3, ∫ x : Vec3, DA j x * Z x ∂volume := by
          rw [show (fun x : Vec3 => (∑ j : Fin 3, DA j x) * Z x) =
              fun x => ∑ j : Fin 3, DA j x * Z x by
                funext x
                rw [Finset.sum_mul]]
          exact vorticityEnergy_integral_finsetSum (fun j => hDAI j)
        have hExpandH :
            (∫ x : Vec3, (∑ j : Fin 3, DH j x) * Z x ∂volume) =
              ∑ j : Fin 3, ∫ x : Vec3, DH j x * Z x ∂volume := by
          rw [show (fun x : Vec3 => (∑ j : Fin 3, DH j x) * Z x) =
              fun x => ∑ j : Fin 3, DH j x * Z x by
                funext x
                rw [Finset.sum_mul]]
          exact vorticityEnergy_integral_finsetSum (fun j => hDHI j)
        rw [hExpandA, hExpandH]
  calc
    _ = ∫ x : Vec3, (T x - ∑ j : Fin 3, S j x) * Z x ∂volume := hLeft.symm
    _ = ∫ x : Vec3,
        (-(∑ j : Fin 3, DA j x) + ∑ j : Fin 3, DH j x + G x) * Z x ∂volume := hRaw
    _ = _ := hRight

private theorem vorticityEnergy_smoothIntegrationByPartsSums
    (Z : Vec3 → ℝ) (A H : Fin 3 → Vec3 → ℝ)
    (hZ : ContDiff ℝ (⊤ : ℕ∞) Z) (hZc : HasCompactSupport Z)
    (hA : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (A j))
    (hH : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (H j)) :
    (∑ j : Fin 3, ∫ x : Vec3,
        CKN.spatialDeriv (CKN.spatialDeriv Z j) j x * Z x ∂volume =
      -(∑ j : Fin 3, ∫ x : Vec3, (CKN.spatialDeriv Z j x) ^ 2 ∂volume)) ∧
    (∑ j : Fin 3, ∫ x : Vec3, CKN.spatialDeriv (A j) j x * Z x ∂volume =
      -(∑ j : Fin 3, ∫ x : Vec3, A j x * CKN.spatialDeriv Z j x ∂volume)) ∧
    (∑ j : Fin 3, ∫ x : Vec3, CKN.spatialDeriv (H j) j x * Z x ∂volume =
      -(∑ j : Fin 3, ∫ x : Vec3, H j x * CKN.spatialDeriv Z j x ∂volume)) := by
  have hZgradc (j : Fin 3) : HasCompactSupport (CKN.spatialDeriv Z j) := by
    change HasCompactSupport
      (fun x : Vec3 => (fderiv ℝ Z x) (CKN.basisVec j))
    exact hZc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  have hZgrad (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv Z j) :=
    CKN.contDiff_spatialDeriv_smooth hZ j
  have hSecond (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialDeriv (CKN.spatialDeriv Z j) j) :=
    CKN.contDiff_spatialDeriv_smooth (hZgrad j) j
  have hSecOne (j : Fin 3) :
      (∫ x : Vec3,
        CKN.spatialDeriv (CKN.spatialDeriv Z j) j x * Z x ∂volume) =
        -(∫ x : Vec3, (CKN.spatialDeriv Z j x) ^ 2 ∂volume) := by
    have h := CKN.integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
      (u := CKN.spatialDeriv Z j) (φ := Z) (hZgrad j) hZ hZc j
    have h' := congrArg Neg.neg h
    simpa only [neg_neg, pow_two] using h'.symm
  have hAOne (j : Fin 3) :
      (∫ x : Vec3, CKN.spatialDeriv (A j) j x * Z x ∂volume) =
        -(∫ x : Vec3, A j x * CKN.spatialDeriv Z j x ∂volume) := by
    have h := CKN.integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
      (u := A j) (φ := Z) (hA j) hZ hZc j
    have h' := congrArg Neg.neg h
    simpa only [neg_neg] using h'.symm
  have hHOne (j : Fin 3) :
      (∫ x : Vec3, CKN.spatialDeriv (H j) j x * Z x ∂volume) =
        -(∫ x : Vec3, H j x * CKN.spatialDeriv Z j x ∂volume) := by
    have h := CKN.integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
      (u := H j) (φ := Z) (hH j) hZ hZc j
    have h' := congrArg Neg.neg h
    simpa only [neg_neg] using h'.symm
  have hSecSum :
      ∑ j : Fin 3, ∫ x : Vec3,
        CKN.spatialDeriv (CKN.spatialDeriv Z j) j x * Z x ∂volume =
        -(∑ j : Fin 3, ∫ x : Vec3,
          (CKN.spatialDeriv Z j x) ^ 2 ∂volume) := by
    calc
      _ = ∑ j : Fin 3, -(∫ x : Vec3,
          (CKN.spatialDeriv Z j x) ^ 2 ∂volume) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hSecOne j
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hASum :
      ∑ j : Fin 3, ∫ x : Vec3, CKN.spatialDeriv (A j) j x * Z x ∂volume =
        -(∑ j : Fin 3, ∫ x : Vec3,
          A j x * CKN.spatialDeriv Z j x ∂volume) := by
    calc
      _ = ∑ j : Fin 3, -(∫ x : Vec3,
          A j x * CKN.spatialDeriv Z j x ∂volume) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hAOne j
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hHSum :
      ∑ j : Fin 3, ∫ x : Vec3, CKN.spatialDeriv (H j) j x * Z x ∂volume =
        -(∑ j : Fin 3, ∫ x : Vec3,
          H j x * CKN.spatialDeriv Z j x ∂volume) := by
    calc
      _ = ∑ j : Fin 3, -(∫ x : Vec3,
          H j x * CKN.spatialDeriv Z j x ∂volume) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hHOne j
      _ = _ := by rw [Finset.sum_neg_distrib]
  exact ⟨hSecSum, hASum, hHSum⟩

/-- A smooth solution of a linear vorticity equation satisfies its spatial
energy balance when paired with one component of the solution itself
(manuscript `lem:localized-vorticity-energy`). -/
theorem smoothVorticityComponentEnergyBalance
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
        g (x, t) i) :
    ∀ (t : ℝ) (i : Fin 3),
      (∫ x : Vec3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) +
        ∑ j : Fin 3, ∫ x : Vec3,
          CKN.spatialPartial (fun w : Vec3 × ℝ => z w i) j (x, t) ^ 2 =
      (∑ j : Fin 3, ∫ x : Vec3,
        (v (x, t) j * z (x, t) i - z (x, t) j * v (x, t) i) *
          CKN.spatialPartial (fun w : Vec3 × ℝ => z w i) j (x, t)) -
      (∑ j : Fin 3, ∫ x : Vec3,
        F (x, t) j i * CKN.spatialPartial
          (fun w : Vec3 × ℝ => z w i) j (x, t)) +
      ∫ x : Vec3, g (x, t) i * z (x, t) i := by
  intro t i
  let Z : Vec3 → ℝ := fun x => z (x, t) i
  let V : Fin 3 → Vec3 → ℝ := fun j x => v (x, t) j
  let A : Fin 3 → Vec3 → ℝ := fun j x =>
    V j x * Z x - z (x, t) j * V i x
  let H : Fin 3 → Vec3 → ℝ := fun j x => F (x, t) j i
  let T : Vec3 → ℝ := fun x => CKN.timePartial
    (fun w : Vec3 × ℝ => z w i) (x, t)
  let S : Fin 3 → Vec3 → ℝ := fun j x =>
    CKN.spatialDeriv (CKN.spatialDeriv Z j) j x
  let DA : Fin 3 → Vec3 → ℝ := fun j x => CKN.spatialDeriv (A j) j x
  let DH : Fin 3 → Vec3 → ℝ := fun j x => CKN.spatialDeriv (H j) j x
  let G : Vec3 → ℝ := fun x => g (x, t) i
  have hZc : HasCompactSupport Z := by
    simpa [Z] using vorticityEnergy_component_hasCompactSupport (hzc t) i
  have hZsmooth : ContDiff ℝ (⊤ : ℕ∞) Z := by
    simpa [Z] using vorticityEnergy_slice_contDiff
      (vorticityEnergy_fieldComponent_contDiff hz i) t
  have hZgrad (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => CKN.spatialDeriv Z j x) :=
    CKN.contDiff_spatialDeriv_smooth hZsmooth j
  have hZsecond (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (S j) := by
    exact CKN.contDiff_spatialDeriv_smooth (hZgrad j) j
  have hTime : ContDiff ℝ (⊤ : ℕ∞) T := by
    exact (CKN.contDiff_timePartial
      (vorticityEnergy_fieldComponent_contDiff hz i)).comp
        (contDiff_id.prodMk contDiff_const)
  have hVsmooth (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (V j) := by
    exact vorticityEnergy_slice_contDiff
      ((contDiff_apply ℝ ℝ j).comp hv) t
  have hZsmoothAll (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => z (x, t) k) := by
    exact vorticityEnergy_slice_contDiff
      ((contDiff_apply ℝ ℝ k).comp hz) t
  have hAsmooth (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (A j) := by
    dsimp [A, V, Z]
    exact ((hVsmooth j).mul hZsmooth).sub ((hZsmoothAll j).mul (hVsmooth i))
  have hHsmooth (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (H j) := by
    exact vorticityEnergy_slice_contDiff (hF j i) t
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) G := by
    exact vorticityEnergy_slice_contDiff
      ((contDiff_apply ℝ ℝ i).comp hg) t
  have hDAcont (j : Fin 3) : Continuous (DA j) :=
    (CKN.contDiff_spatialDeriv_smooth (hAsmooth j) j).continuous
  have hDHcont (j : Fin 3) : Continuous (DH j) :=
    (CKN.contDiff_spatialDeriv_smooth (hHsmooth j) j).continuous
  have hTimeInt : Integrable (fun x : Vec3 => T x * Z x) volume :=
    vorticityEnergy_integrable_mul_compact hTime.continuous hZsmooth.continuous hZc
  have hSecInt (j : Fin 3) : Integrable (fun x : Vec3 => S j x * Z x) volume :=
    vorticityEnergy_integrable_mul_compact (hZsecond j).continuous
      hZsmooth.continuous hZc
  have hDAInt (j : Fin 3) : Integrable (fun x : Vec3 => DA j x * Z x) volume :=
    vorticityEnergy_integrable_mul_compact (hDAcont j) hZsmooth.continuous hZc
  have hDHInt (j : Fin 3) : Integrable (fun x : Vec3 => DH j x * Z x) volume :=
    vorticityEnergy_integrable_mul_compact (hDHcont j) hZsmooth.continuous hZc
  have hGInt : Integrable (fun x : Vec3 => G x * Z x) volume :=
    vorticityEnergy_integrable_mul_compact hGsmooth.continuous hZsmooth.continuous hZc
  have hEqSlice (x : Vec3) :
      T x - ∑ j : Fin 3, S j x =
        -(∑ j : Fin 3, DA j x) + ∑ j : Fin 3, DH j x + G x := by
    have h := heq x t i
    change T x - ∑ j : Fin 3, S j x =
      -(∑ j : Fin 3, DA j x) + ∑ j : Fin 3, DH j x + G x at h
    exact h
  have hEqInt := vorticityEnergy_integrateComponentEquation
    hEqSlice hTimeInt hSecInt hDAInt hDHInt hGInt
  have hIBPSums := vorticityEnergy_smoothIntegrationByPartsSums
    Z A H hZsmooth hZc hAsmooth hHsmooth
  rw [hIBPSums.1, hIBPSums.2.1, hIBPSums.2.2] at hEqInt
  have hTimeOut :
      (∫ x : Vec3, T x * Z x ∂volume) +
        ∑ j : Fin 3, ∫ x : Vec3,
          (CKN.spatialDeriv Z j x) ^ 2 ∂volume =
        (∑ j : Fin 3, ∫ x : Vec3,
          A j x * CKN.spatialDeriv Z j x ∂volume) -
          (∑ j : Fin 3, ∫ x : Vec3,
            H j x * CKN.spatialDeriv Z j x ∂volume) +
          ∫ x : Vec3, G x * Z x ∂volume := by
    linear_combination hEqInt
  simpa [T, Z, A, H, G, V, CKN.spatialPartial, CKN.spatialDeriv] using hTimeOut

end

end ESS
