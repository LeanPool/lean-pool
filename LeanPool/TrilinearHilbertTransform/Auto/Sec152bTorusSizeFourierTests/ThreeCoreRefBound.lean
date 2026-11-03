/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec152bTorusSizeFourierTests.ThreeCoreNorefSide

/-!
# Trilinear Hilbert transform: three_core_ref_bound
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}
namespace SideInput
variable (D : fp.SideInput)

open scoped Classical in
private def ThreeCoreRefBoundHTailStatement : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (D : fp.SideInput)
    (I : ℤ × ℤ)
    (G : bf.Grp)
    (δ : ℝ)
    (Cm : ℝ)
    (Kt : ℕ)
    (J : ℕ)
    (h : ℕ)
    (l : Fin (4 : ℕ))
    (Fsel : (j : Fin (4 : ℕ)) → Finset ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart
      D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))))
    (n : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms j G).zc.dim → ℤ)
    (a : Fin (4 : ℕ) → ℝ)
    (xs : ℝ)
    (X : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (Aw : ℕ)
    (Iw : ℕ)
    (_ : (0 : ℝ) ≤ (D.S.Dstar ^ (100 : ℕ))⁻¹)
    (_ : (0 : ℝ) ≤ entryCU κ' J Aw)
    (_ : (dyadicGridLength A.G I.1)⁻¹ * √(dyadicGridLength A.G I.1 * ∫ (y : ℝ) in
      dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
      ‖augPhys X y‖ ^ (2 : ℕ)) = √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in
      dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
      ‖augPhys X y‖ ^ (2 : ℕ)))
    (_ : (0 : ℝ) ≤ √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in dyadicGridLeft A.G I.1
      I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ (2 :
      ℕ)))
    (_ : entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) ≤ entryCU κ' J Aw)
    (_ : (0 : ℝ) ≤ ((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0
      Cm Kt) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) * ∏ j ∈
      Finset.univ.erase l, (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) + cutTail
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt * D.coefSum G I j (Fsel j)))
    (_ : ((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm Kt) *
      ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) * ∏ j ∈
      Finset.univ.erase l, (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) + cutTail
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt * D.coefSum G I j (Fsel j)) ≤ (32 : ℝ) * ∏
      j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j))
    (_ : (0 : ℝ) ≤ ((2 : ℝ) ^ (Iw + (1 : ℕ)))⁻¹ ^ (Aw + (1 : ℕ)))
    (_ : ((2 : ℝ) ^ (Iw + (1 : ℕ)))⁻¹ ^ (Aw + (1 : ℕ)) ≤ (D.S.Dstar ^ (100 : ℕ))⁻¹),
  (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a)
    * (2 : ℝ) ^ (Aw + (4 : ℕ)) * ((2 : ℝ) * ((2 : ℝ) ^ (Iw + (1 : ℕ)))⁻¹ ^ (Aw + (1 :
    ℕ))) * ((((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ))
    D.S.Q0 Cm Kt) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) * ∏ j ∈
    Finset.univ.erase l, (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) + cutTail
    (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt * D.coefSum G I j (Fsel j))) *
    √(dyadicGridLength A.G I.1 * ∫ (y : ℝ) in dyadicGridLeft A.G I.1
    I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ (2 :
    ℕ))) ≤ ((64 : ℝ) * (2 : ℝ) ^ (Aw + (4 : ℕ)) * entryCU κ' J Aw * (D.S.Dstar ^ (100
    : ℕ))⁻¹ * ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
    √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in dyadicGridLeft A.G I.1
    I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ (2 :
    ℕ))


open scoped Classical in
private def ThreeCoreRefBoundStage1Statement : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (D : fp.SideInput)
    (Cj : ℕ)
    (CA : ℕ)
    (CT : ℕ)
    (CK : ℕ)
    (δs : ℝ)
    (W : ℝ)
    (_ : D.S.Valid Cj CA CT CK δs W)
    (_ : (4 : ℕ) ≤ CT)
    (_ : (2 : ℕ) ≤ D.S.dmax)
    (_ : (2 : ℝ) ≤ D.S.Dstar)
    (_ : (2 : ℝ) ≤ D.S.Bstar)
    (_ : (1 : ℕ) ≤ D.S.Q0)
    (_ : D.SP = D.S.sideParams δs)
    (I : ℤ × ℤ)
    (G : bf.Grp)
    (δ : ℝ)
    (Cm : ℝ)
    (Kt : ℕ)
    (_ : cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt ≤ (D.S.Dstar ^ (300 : ℕ))⁻¹)
    (_ : multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm Kt ≤ (D.S.Dstar ^
      (300 : ℕ))⁻¹)
    (_ : multNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm ≤ D.S.Dstar)
    (_ : cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ ≤ D.S.Dstar)
    (J : ℕ)
    (_ : (3 : ℕ) ≤ J)
    (h : ℕ)
    (l : Fin (4 : ℕ))
    (Fsel : (j : Fin (4 : ℕ)) → Finset ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart
      D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))))
    (n : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms j G).zc.dim → ℤ)
    (a : Fin (4 : ℕ) → ℝ)
    (xs : ℝ)
    (X : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (Aw : ℕ)
    (Iw : ℕ)
    (_ : (1 : ℕ) ≤ Aw)
    (_ : D.U0 ≤ (2 : ℝ) ^ (Iw + (1 : ℕ)))
    (_ : (0 : ℝ) < dyadicGridLength A.G I.1)
    (_ : IsAdmissibleLocalKernel κ' (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1)
      (A.w I))
    (_ : (1 : ℝ) ≤ D.S.Dstar)
    (_ : h - D.SP.Δ ≤ D.SP.Jst)
    (_ : (0 : ℝ) ≤ (D.S.Dstar ^ (100 : ℕ))⁻¹)
    (_ : (D.S.Dstar ^ (100 : ℕ))⁻¹ ≤ (1 : ℝ))
    (_ : ∀ (k : ℕ), (100 : ℕ) ≤ k → (D.S.Dstar ^ k)⁻¹ ≤ (D.S.Dstar ^ (100 : ℕ))⁻¹)
    (_ : (0 : ℝ) ≤ localKernelSupBound κ')
    (_ : (0 : ℝ) ≤ kerC κ' J)
    (_ : (0 : ℝ) ≤ entryCU κ' J Aw)
    (_ : (0 : ℝ) ≤ nearBC κ')
    (_ : (0 : ℝ) ≤ cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt)
    (_ : (0 : ℝ) ≤ multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm Kt)
    (_ : (0 : ℝ) ≤ cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ)
    (_ : (Finset.univ.erase l).card = (3 : ℕ))
    (_ : ∀ j ∈ Finset.univ.erase l, (0 : ℝ) ≤ D.coefSum G I j (Fsel j))
    (_ : (0 : ℝ) ≤ ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j))
    (_ : ∀ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) ≤
      D.coefSum G I j (Fsel j))
    (_ : ∏ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) ≤ ∏ j ∈
      Finset.univ.erase l, D.coefSum G I j (Fsel j))
    (_ : (dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in Set.Icc (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖ ≤
      √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in dyadicGridLeft A.G I.1
      I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ (2 :
      ℕ)) ∧ (dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in Set.Ico (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖ ≤
      √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in dyadicGridLeft A.G I.1
      I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ (2 :
      ℕ)))
    (_ : (dyadicGridLength A.G I.1)⁻¹ * √(dyadicGridLength A.G I.1 * ∫ (y : ℝ) in
      dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
      ‖augPhys X y‖ ^ (2 : ℕ)) = √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in
      dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
      ‖augPhys X y‖ ^ (2 : ℕ)))
    (_ : (0 : ℝ) ≤ √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in dyadicGridLeft A.G I.1
      I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ (2 :
      ℕ)))
    (_ : (0 : ℝ) ≤ (dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in Set.Icc (dyadicGridLeft A.G
      I.1 I.2) (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖)
    (_ : (0 : ℝ) ≤ (dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in Set.Ico (dyadicGridLeft A.G
      I.1 I.2) (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖)
    (_ : D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ) ≤ (D.S.Dstar ^ (999 : ℕ))⁻¹ ∧ D.S.Dstar ^
      (999 : ℕ) ≤ D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) - D.U0)
    (_ : ‖(fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ)
          (Function.update
            (fun (j : Fin (4 : ℕ)) =>
              D.compSub j G I (Finset.map { toFun := Subtype.val, inj' := Subtype.val_injective
                } (Fsel j)))
            l X)‖ ≤
      (2 : ℝ) *
        ((2 : ℝ) * localKernelSupBound κ' *
                  (((4 : ℝ) * (D.S.Dstar ^ (150 : ℕ))⁻¹ +
                      (gaugeErr (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ (δ / (2 : ℝ)) +
                          (4 : ℝ) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^
                            (3 : ℕ) *
                            cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt +
                        ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (4 : ℕ) *
                          multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm Kt)) *
                    ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
                ((dyadicGridLength A.G I.1)⁻¹ *
                  ∫ (y : ℝ) in Set.Icc (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2
                    + dyadicGridLength A.G I.1),
                    ‖augPhys X y‖) +
              (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) *
                    (2 : ℝ) ^ (Aw + (4 : ℕ)) *
                  ((2 : ℝ) * ((2 : ℝ) ^ (Iw + (1 : ℕ)))⁻¹ ^ (Aw + (1 : ℕ))) *
                ((((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm
                  Kt) *
                      ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) *
                    ∏ j ∈ Finset.univ.erase l,
                      (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) +
                        cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt * D.coefSum G I j (Fsel
                          j))) *
                  √(dyadicGridLength A.G I.1 *
                      ∫ (y : ℝ) in dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 +
                        dyadicGridLength A.G I.1,
                        ‖augPhys X y‖ ^ (2 : ℕ))) +
            multNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm *
                (cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ *
                  ∏ j ∈ Finset.univ.erase l, cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ *
                    D.coefSum G I j (Fsel j)) *
              (((dyadicGridLength A.G I.1)⁻¹ *
                  ∫ (y : ℝ) in Set.Ico (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2
                    + dyadicGridLength A.G I.1),
                    ‖augPhys X y‖) *
                (nearB κ' (D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ)) +
                  (12 : ℝ) * (kerC κ' J * ((4 : ℝ) / (D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) -
                    D.U0)) ^ (J - (2 : ℕ))))) +
          ∑ i ∈ Finset.range (Iw + (1 : ℕ)),
            (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a)
              * (2 : ℝ) ^ (Aw + (4 : ℕ)) *
                  ((2 : ℝ) ^ i)⁻¹ ^ (Aw + (1 : ℕ)) *
                (((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm Kt) *
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) *
                  ∏ j ∈ Finset.univ.erase l,
                    (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) +
                      cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt * D.coefSum G I j (Fsel j))) *
              √(∫ (ρ' : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ),
                  sideWinE (D.Ms (0 : Fin (4 : ℕ)) G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
                    (dyadicGridLength A.G I.1) (D.threeWin G I xs (h - D.SP.Δ) l a ((2 : ℝ) ^ i))
                    ρ' ∂offsetMeasure (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim)))
    (_ : (0 : ℝ) ≤ entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a))
    (_ : entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) ≤ entryCU κ' J Aw),
  ‖(fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ)
        (Function.update
          (fun (j : Fin (4 : ℕ)) =>
            D.compSub j G I (Finset.map { toFun := Subtype.val, inj' := Subtype.val_injective }
              (Fsel j)))
          l X)‖ ≤
    D.threePrin G I xs (h - D.SP.Δ) l a Fsel n X J Aw Iw +
      (((208 : ℝ) * localKernelSupBound κ' + (252 : ℝ) * (2 : ℝ) ^ (Aw + (4 : ℕ)) * entryCU κ' J
        Aw +
                (2 : ℝ) * nearBC κ' +
              (96 : ℝ) * kerC κ' J) *
            (D.S.Dstar ^ (100 : ℕ))⁻¹ *
          ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
        √((dyadicGridLength A.G I.1)⁻¹ *
            ∫ (y : ℝ) in dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 +
              dyadicGridLength A.G I.1,
              ‖augPhys X y‖ ^ (2 : ℕ))




private theorem three_core_ref_bound_hTail : ThreeCoreRefBoundHTailStatement := by
  classical
  intro κ' c₀ A bf fp D I G δ Cm Kt J h l Fsel n a xs X Aw Iw hu0 hEC hσ hσ0 heC hWf0 hWf32 hX0 hX
  have e : ((dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) *
    2 ^ (Aw + 4) * (2 * ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1)) *
    (((1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) *
      (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l,
      (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) +
        cutTail (D.Ms 0 G).zc.dim δ Kt * D.coefSum G I j (Fsel j))) *
    Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2))) = (entryC κ' J
          Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) * ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1)) *
      ((1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0 G).zc.dim δ
          Kt) * (∏ j ∈ Finset.univ.erase l, (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) +
    cutTail (D.Ms 0 G).zc.dim δ Kt * D.coefSum G I j (Fsel j)))) * (2 * 2 ^ (Aw + 4)) *
        ((dyadicGridLength A.G I.1)⁻¹ * (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in
            (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2))) := by ring
  rw [e, hσ]
  have h1 := mul_le_mul heC hX hX0 hEC
  have h2 := mul_le_mul h1 hWf32 hWf0 (mul_nonneg hEC hu0)
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2
    (by positivity : (0 : ℝ) ≤ 2 * 2 ^ (Aw + 4))) hσ0
  calc _ ≤ entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (32 * (∏ j ∈ Finset.univ.erase l, D.coefSum G
      I j (Fsel j))) * (2 * 2 ^ (Aw + 4)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in
          (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := h3
    _ = 64 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l,
        D.coefSum G I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in
            (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by ring
-- the coset replacement and tail errors



private theorem three_core_ref_bound_stage_1 : ThreeCoreRefBoundStage1Statement := by
  classical
  intro κ' c₀ A bf fp D Cj CA CT CK δs W hV hCT hd2 hD hB hQ hSP I G δ Cm Kt hτc hτm hMN hCN J hJ
    h l Fsel n a xs X Aw Iw hAw hIw hr hw hD1 hh' hu0 hu1 hpow hK hkJ hEC hNB hτc0 hτm0 hCN0 hcard
    hS0 hP0 haS hPaP hcs hσ hσ0 hL1 hL1' hTb key' heC0 heC
  have hWf := trunc_core_err3 (Finset.univ.erase l) hcard
    (a := fun j => D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j))
    (S := fun j => D.coefSum G I j (Fsel j)) (fun j _ => D.coreSize_nonneg G I xs _ j _ _) haS
    hτc0 hτm0 (hτc.trans (hpow 300 (by norm_num))) (hτm.trans (hpow 300 (by norm_num))) hu1
  have hQ0 : 0 ≤ (∏ j ∈ Finset.univ.erase l, (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) +
      cutTail (D.Ms 0 G).zc.dim δ Kt * D.coefSum G I j (Fsel j))) := Finset.prod_nonneg fun j hj =>
    add_nonneg (D.coreSize_nonneg G I xs _ j _ _) (mul_nonneg hτc0 (hS0 j hj))
  have hWf0 : 0 ≤ (1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0
      G).zc.dim δ Kt) * (∏ j ∈ Finset.univ.erase l, (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n
          j) +
      cutTail (D.Ms 0 G).zc.dim δ Kt * D.coefSum G I j (Fsel j))) :=
    mul_nonneg (mul_nonneg (by linarith only [hτm0]) (by linarith only [hτc0])) hQ0
  have hWf32 : (1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0
      G).zc.dim δ Kt) * (∏ j ∈ Finset.univ.erase l, (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n
          j) +
      cutTail (D.Ms 0 G).zc.dim δ Kt * D.coefSum G I j (Fsel j))) ≤ 32 * (∏ j ∈ Finset.univ.erase
          l, D.coefSum G I j (Fsel j)) := by
    have h1 : 31 * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) ≤ 31
        * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) := by
      have := mul_le_mul_of_nonneg_right hu1 hP0
      linarith only [this]
    exact hWf.trans (by linarith only [hPaP, h1])
  -- the torus-form and gauge errors
  have hT1 : (2 * localKernelSupBound κ' * ((4 * (D.S.Dstar ^ 150)⁻¹ +
      (gaugeErr (D.Ms 0 G).zc.dim δ (δ / 2) +
        4 * (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 3 * cutTail (D.Ms 0 G).zc.dim δ Kt +
        (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 4 *
          multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt)) *
      ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
      ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in Set.Icc (dyadicGridLeft A.G I.1 I.2)
        (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖)) ≤ 104 *
            localKernelSupBound κ' * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G
                I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft
                    A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
    have g := gauge_err_le (K := localKernelSupBound κ') (δ := δ) (P := (∏ j ∈ Finset.univ.erase l,
        D.coefSum G I j (Fsel j)))
      (D.Ms 0 G).zc.dim hD1 hK hP0 hτc0 hτm0 hτc hτm
    exact mul_le_mul g hcs.1 hL1 (by positivity)
  -- the shells above the windows
  have hX0 : 0 ≤ ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1) := by positivity
  have hX : ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1) ≤ (D.S.Dstar ^ 100)⁻¹ := by
    have hU0 : 0 < D.U0 := by unfold U0; positivity
    have h1 : ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1) ≤ ((2 : ℝ) ^ (Iw + 1))⁻¹ :=
      pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
        (by omega)
    have h2 : ((2 : ℝ) ^ (Iw + 1))⁻¹ ≤ D.U0⁻¹ := inv_anti₀ hU0 hIw
    have h3 : D.U0⁻¹ ≤ (D.S.Dstar ^ 100)⁻¹ := by unfold U0; exact hpow 250 (by norm_num)
    linarith only [h1, h2, h3]
  have hTail : ((dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a)
      *
      2 ^ (Aw + 4) * (2 * ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1)) *
      (((1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) *
        (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l,
        (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) +
          cutTail (D.Ms 0 G).zc.dim δ Kt * D.coefSum G I j (Fsel j))) *
      Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
        dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2))) ≤ 64 * 2 ^ (Aw
            + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G
                I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft
                    A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
    expose_names
    exact @three_core_ref_bound_hTail κ' c₀ A bf fp D I G δ Cm Kt J h l Fsel n a xs X Aw Iw hu0
      hEC hσ hσ0 heC hWf0 hWf32 hX0 hX
  have hCo : ((multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm * (cutNorm (D.Ms 0 G).zc.dim δ *
      ∏ j ∈ Finset.univ.erase l, (cutNorm (D.Ms 0 G).zc.dim δ *
        D.coefSum G I j (Fsel j)))) *
      ((dyadicGridLength A.G I.1)⁻¹ * (∫ y in Set.Ico (dyadicGridLeft A.G I.1 I.2)
        (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖) *
        (nearB κ' (D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ)) + 12 * (kerC κ' J *
          (4 / (D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) - D.U0)) ^ (J - 2))))) ≤ (nearBC κ' + 48 *
              kerC κ' J) * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel
                  j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1
                      I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
    have hε0 : 0 ≤ D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ) := by
      have hL : (0 : ℝ) < ModeSchedule.Lh (h - D.SP.Δ) := pow_pos (by norm_num) _
      have hT := D.Lh_mul_Ξ_le_Tt hV hCT hd2 hD hB hQ hSP hh'
      have hΞ : 0 < D.S.Ξ := by unfold ModeSchedule.Ξ; positivity
      have hT0 : 0 < D.SP.Tt := lt_of_lt_of_le (mul_pos hL hΞ) hT
      positivity
    have hε1 : D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ) ≤ 1 :=
      hTb.1.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hD1))
    have hnear0 : 0 ≤ nearB κ' (D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ)) := by
      unfold nearB
      have := kerC_nonneg hr hw 2
      have := kerC_nonneg hr hw 4
      have := kernelDerivBound_nonneg κ' 0
      positivity
    exact three_coset_err_le (Finset.univ.erase l) hcard (S := fun j => D.coefSum G I j (Fsel j))
      hJ hD hS0 hMN hCN0 hCN hNB hkJ hTb.1 hTb.2 hL1' hcs.2 hnear0
      (nearB_le hr hw hε0 hε1)
  -- the windows
  have hc : ∀ i : ℕ, 0 ≤ (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h -
      D.SP.Δ) l a) * 2 ^ (Aw + 4) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) := fun i => by
    have := inv_nonneg.mpr hr.le
    positivity
  have hW := window_split (I := Iw)
    (c := fun i => (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l
        a) * 2 ^ (Aw + 4) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1))
    (ω := fun i => Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l (augPhys X) (dyadicGridLeft A.G I.1
        I.2) (dyadicGridLength A.G I.1)
      (D.threeWin G I xs (h - D.SP.Δ) l a (2 ^ i)) ρ' ∂offsetMeasure (D.Ms 0 G).zc.dim))
    hc (fun i => Real.sqrt_nonneg _) (fun i => window_root_le _ l X I _) hWf hu0 hP0
  beta_reduce at hW
  have hcs2 : ∑ i ∈ Finset.range (Iw + 1), (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw
      (D.threeBeta G I xs (h - D.SP.Δ) l a) * 2 ^ (Aw + 4) *
      ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) ≤ (dyadicGridLength A.G I.1)⁻¹ * entryCU κ' J Aw * 2 ^ (Aw + 4) *
          2 := by
    rw [← Finset.mul_sum]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heC
      (inv_nonneg.mpr hr.le)) (by positivity)) (sum_range_inv_pow_le Aw Iw)
      (Finset.sum_nonneg fun i _ => by positivity)
      (mul_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) hEC) (by positivity))
  have hR : 31 * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
      (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) * ∑ i ∈
          Finset.range (Iw + 1), (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs
              (h - D.SP.Δ) l a) * 2 ^ (Aw + 4) *
      ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) ≤ 62 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j
          ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G
              I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
    calc _ ≤ 31 * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
        (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) *
          ((dyadicGridLength A.G I.1)⁻¹ * entryCU κ' J Aw * 2 ^ (Aw + 4) * 2) :=
          mul_le_mul_of_nonneg_left hcs2 (by positivity)
      _ = 62 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l,
          D.coefSum G I j (Fsel j)) * ((dyadicGridLength A.G I.1)⁻¹ * (Real.sqrt (dyadicGridLength
              A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2))) := by ring
      _ = _ := by rw [hσ]
  unfold threePrin
  linarith only [key', hT1, hTail, hCo, hW, hR]


open Classical in
/-- Blueprint `eq:core-numerical` (lines 2562-2567) for a three-core tuple with a reference on a
leaf cell of the side states (enlarged gauge cutoff `δ/2`, truncation tails at most `D_*^{-300}`,
full Fourier norms at most `D_*`, `J ≥ 3`, windows up to `2^{I_w} ≥ U₀/2`): the cell form with the
side `X` in slot `l` is at most the principal window quantity `threePrin` (true torus sizes) plus
`C D_*^{-100} Π_{j ≠ l} Σ_{F_j} |α| σ`, with `σ = (r⁻¹ ∫_I |S_phys|²)^{1/2}` the local side size.
The error collects the torus-form and gauge errors (`gauge_err_le`), the truncation parts of the
core sizes (`trunc_core_err3`, `window_split`), the shells above `2^{I_w}` (`2^{-(I_w+1)(A+1)} ≤
U₀⁻¹`), and the coset replacement and tails (`nearB_le`, `T⁻¹/L ≤ D_*^{-999}`). -/
theorem three_core_ref_bound {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) {I : ℤ × ℤ}
    (hI : I ∈ A.cells) (G : bf.Grp) (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc)
    (hdim : (D.Ms 0 G).zc.dim ≤ D.S.dmax) {δ : ℝ} (hδ : 0 < δ)
    (hdδ : 8 * (D.Ms 0 G).zc.dim * δ ≤ 1) (hδ8 : δ ≤ 1 / 8) (hδc : ∀ j, (D.Ms j G).δc = δ)
    (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j) (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm)
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar)
    (hτc : cutTail (D.Ms 0 G).zc.dim δ Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hτm : multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hMN : multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm ≤ D.S.Dstar)
    (hCN : cutNorm (D.Ms 0 G).zc.dim δ ≤ D.S.Dstar) {J : ℕ} (hJ : 3 ≤ J) {h : ℕ}
    (hh : h ≤ D.SP.Jst) (j₀ : Fin 4)
    {m₀ : (D.Ms j₀ G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    (hgood : ((D.Ms j₀ G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).Good D.SP.Δ
      ((D.Ms j₀ G).goodP D.S D.SP (A.blkStart D.S.K I.1)) h m₀) (l : Fin 4)
    (Fsel : ∀ j, Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ)
    (hn : ∀ j, j ≠ l → ∀ x ∈ Fsel j, ∀ i,
      |(n j x i : ℝ)| ≤ D.S.Dstar * D.S.Eh (h - D.SP.Δ))
    (a : Fin 4 → ℝ)
    {xs : ℝ} (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (hform : ∀ j, j ≠ l → ∀ y ∈ dyadicGridCell A.G I.1 I.2,
      ‖∑ x ∈ Fsel j, D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1 * (D.Ms j G).wave x.1 y -
        (Real.fourierChar (((D.Ms j G).cl : ℝ) * centerPhase (D.Ms j G).zc (D.Ms j G).ρ y) : ℂ) *
          (Real.fourierChar (a j * (y - xs)) : ℂ) *
          (D.Ms j G).torusG D.S (h - D.SP.Δ) xs (Fsel j)
            (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j)
            (fun i => (D.Ms j G).torusξ D.S (h - D.SP.Δ) i * (y - xs))‖ ≤
        (D.S.Dstar ^ 150)⁻¹ *
          ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖)
    (hne : (D.threeRefSet G I xs (h - D.SP.Δ) l a).Nonempty)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (Aw Iw : ℕ) (hAw : 1 ≤ Aw) (hIw : D.U0 ≤ 2 ^ (Iw + 1)) :
    ‖fp.Λc I (Function.update (fun j => D.compSub j G I
        ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩)) l X)‖ ≤
      D.threePrin G I xs (h - D.SP.Δ) l a Fsel n X J Aw Iw +
      (208 * localKernelSupBound κ' + 252 * 2 ^ (Aw + 4) * entryCU κ' J Aw + 2 * nearBC κ' +
        96 * kerC κ' J) * (D.S.Dstar ^ 100)⁻¹ *
        (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
        Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
          dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2) := by
  have hr : 0 < (dyadicGridLength A.G I.1) := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  have hDp : 0 < D.S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ D.S.Dstar := by linarith
  have hh' : h - D.SP.Δ ≤ D.SP.Jst := le_trans (Nat.sub_le _ _) hh
  have hu0 : (0 : ℝ) ≤ (D.S.Dstar ^ 100)⁻¹ := by positivity
  have hu1 : (D.S.Dstar ^ 100)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hD1)
  have hpow : ∀ k : ℕ, 100 ≤ k → (D.S.Dstar ^ k)⁻¹ ≤ (D.S.Dstar ^ 100)⁻¹ := fun k hk =>
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hD1 hk)
  have hK := localKernelSupBound_nonneg κ'
  have hkJ := kerC_nonneg hr hw J
  have hEC := entryCU_nonneg hr hw J Aw
  have hNB : 0 ≤ nearBC κ' := by
    unfold nearBC
    have := kerC_nonneg hr hw 2
    have := kerC_nonneg hr hw 4
    positivity
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hτc0 := cutTail_nonneg (D.Ms 0 G).zc.dim hδ Kt
  have hτm0 : 0 ≤ multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt := by
    unfold multTail
    have := profR_nonneg hδ2 ((D.Ms 0 G).zc.dim + (D.Ms 0 G).zc.dim + 1)
    positivity
  have hCN0 : 0 ≤ cutNorm (D.Ms 0 G).zc.dim δ := by
    unfold cutNorm; have := one_le_bumpConst; positivity
  have hcard : (Finset.univ.erase l).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ l)]; simp
  have hS0 : ∀ j ∈ Finset.univ.erase l, 0 ≤ D.coefSum G I j (Fsel j) :=
    fun j _ => D.coefSum_nonneg G I j (Fsel j)
  have hP0 : 0 ≤ (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) := Finset.prod_nonneg hS0
  have haS : ∀ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) ≤
      D.coefSum G I j (Fsel j) := fun j _ =>
    D.coreSize_le G I xs _ j (by rw [hδc j]; exact hδ) (Fsel j) (n j)
  have hPa0 : 0 ≤ (∏ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j)) :=
      Finset.prod_nonneg fun j _ => D.coreSize_nonneg G I xs _ j _ _
  have hPaP : (∏ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j)) ≤ (∏ j ∈
      Finset.univ.erase l, D.coefSum G I j (Fsel j)) :=
    Finset.prod_le_prod₀ (fun j _ => D.coreSize_nonneg G I xs _ j _ _) haS
  have hL2X : MemLp (augPhys X) 2 (volume.restrict (Set.Ioc (dyadicGridLeft A.G I.1 I.2)
      ((dyadicGridLeft A.G I.1 I.2) + (dyadicGridLength A.G I.1)))) :=
    (memLp_column_coord X none).restrict _
  have hcs := cell_l1_le_size hr hL2X
  have hσ : (dyadicGridLength A.G I.1)⁻¹ * (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in
      (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) = (Real.sqrt
          ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
          inv_mul_sqrt_mul hr
  have hσ0 : 0 ≤ (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
          Real.sqrt_nonneg _
  have hR20 : 0 ≤ (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
          Real.sqrt_nonneg _
  have hL1 : 0 ≤ (dyadicGridLength A.G I.1)⁻¹ * ∫ y in Set.Icc (dyadicGridLeft A.G I.1 I.2)
      ((dyadicGridLeft A.G I.1 I.2) + (dyadicGridLength A.G I.1)), ‖augPhys X y‖ :=
    mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => norm_nonneg _)
  have hL1' : 0 ≤ (dyadicGridLength A.G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft A.G I.1 I.2)
      ((dyadicGridLeft A.G I.1 I.2) + (dyadicGridLength A.G I.1)), ‖augPhys X y‖ :=
    mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => norm_nonneg _)
  have hTb := D.Tt_far_bounds hV hCT hd2 hD hB hQ hSP hh'
  have key := D.three_core_test hV hCA hCT hd2 hD hB hQ hSP hI G hz hdim hδ hdδ hδ8 hδc hcl hρ
    hQC hCm0 hCm hδ2 hQB (J := J) (by omega) hh j₀ hgood l Fsel n hn a hxs hform hne X Aw Iw hAw
  have key' :
    ‖fp.Λc I (Function.update (fun j => D.compSub j G I
        ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩)) l X)‖ ≤ 2 * (
      2 * localKernelSupBound κ' * ((4 * (D.S.Dstar ^ 150)⁻¹ +
          (gaugeErr (D.Ms 0 G).zc.dim δ (δ / 2) +
            4 * (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 3 * cutTail (D.Ms 0 G).zc.dim δ Kt +
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 4 *
              multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt)) *
        ∏ j ∈ Finset.univ.erase l,
          D.coefSum G I j (Fsel j)) *
        ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in Set.Icc (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖) +
      (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) *
          2 ^ (Aw + 4) * (2 * ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1)) *
        (((1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) *
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l,
            (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) +
              cutTail (D.Ms 0 G).zc.dim δ Kt *
                D.coefSum G I j (Fsel j))) *
          Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
            dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) +
      (multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm * (cutNorm (D.Ms 0 G).zc.dim δ *
          ∏ j ∈ Finset.univ.erase l, (cutNorm (D.Ms 0 G).zc.dim δ *
            D.coefSum G I j (Fsel j)))) *
        ((dyadicGridLength A.G I.1)⁻¹ * (∫ y in Set.Ico (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖) *
          (nearB κ' (D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ)) + 12 * (kerC κ' J *
            (4 / (D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) - D.U0)) ^ (J - 2)))) +
      ∑ i ∈ Finset.range (Iw + 1), ((dyadicGridLength A.G I.1)⁻¹ *
          entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) * 2 ^ (Aw + 4) *
          ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) * ((1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) *
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l,
            (D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) +
              cutTail (D.Ms 0 G).zc.dim δ Kt *
                D.coefSum G I j (Fsel j)))) *
        Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLength A.G I.1) (D.threeWin G I xs (h - D.SP.Δ) l a (2 ^ i)) ρ'
          ∂offsetMeasure (D.Ms 0 G).zc.dim)) := key
  have heC0 : 0 ≤ entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) := entryC_nonneg hr hw J Aw _
  have heC : entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) ≤ entryCU κ' J Aw :=
    (entryC_le_min hr hw J Aw _).trans (mul_le_of_le_one_right hEC (min_le_left _ _))
  -- the truncation parts of the core sizes
  expose_names
  exact @three_core_ref_bound_stage_1 κ' c₀ A bf fp D Cj CA CT CK δs W hV hCT hd2 hD hB hQ hSP I G
    δ Cm Kt hτc hτm hMN hCN J hJ h l Fsel n a xs X Aw Iw hAw hIw hr hw hD1 hh' hu0 hu1 hpow hK hkJ
    hEC hNB hτc0 hτm0 hCN0 hcard hS0 hP0 haS hPaP hcs hσ hσ0 hL1 hL1' hTb key' heC0 heC



end SideInput
end ActiveSetup.BasicFamilies.FamParams
end TrilinearHT.Auto
end
